/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2 -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Defs -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.CostedTables -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SmReachInvParty -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs
import Computational.Proofs.ReductionDsl.SpkLeakRed
import Computational.Proofs.E2E.Dsl.SpqrSim

/-!
# Relational Init, Transmit, and Challenge Proofs for `HaltedSpkLeakTier2`

Defines `SpkHaltedTier2SimRel` and proves relational simulation for initialization, transmit, and
challenge steps of `spkLeakRedHaltedTier2`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Step

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Env Ops Iface Expr Comp CostedReduction UniformSamplerTag bits
  bits_mono reductionSizeBudget atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfIface e2eSessionCodec BV256 BV512 PtT PK GhostStT PlainT B smQT smRT recvResultT
  recvResultEnc bind_congr_of_mem_support' handlerImpl smQenc partyToBool)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec evalQuery)
open CryptoGames.Ratchet (expandPRG)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (SimKemFailTrack SimBraidSt SimKemCoins simNextKemCoins simEkSideIsA simAuthNext simBe64
   simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver)
open CryptoGames.SM (Pos samIfNec posTy posSender posEpoch posIdx maxN maxOptE sendsInE orE boolEq
  isSomeE otherE pGet pSet Record RecvResult GameState transmitR transmitImpl challR challImpl
  corrR inWindow MakesAtMostQueries partyEnc posEnc orE_eval boolEq_eval isSomeE_eval)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey KeyPair SessionState
  GhostState currentVersion maxReceiverChains maxForwardJumps)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes SpkLeakRedProg spkTier2Budget paramsIdsWithSpqr
  sessionSchemeFixedSpk sessionSchemeU configRefuseEarlyBobCorr liftSpkGameM initAOracle
  receiveSpk deliverSpk injectSpk)
open CryptoVerification.E2E.Costed (e2eSig e2eOps gRedBounded_of_bounds
  liftM_unif_query_bind liftM_sample_prod_bind_bv256)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (kemBraidParty KemFailTrackState KemFailSessionTrack initKemFailTrack stepKemFailSend
   stepKemFailDeliver transmitRTrackHalted challRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs
  (SpkTrackHaltedM liftSpkGameTrackHaltedM liftSpkNoTrackM deliverSpkTrackHalted
   spkOracleImplTrackHalted spkLeakRedTrackHalted transmitRTrackHalted_support
   challRTrackHalted_support)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_cost drSendC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (zeroPqxdhPrims sessGroupOp eval_sessGroupOp cost_sessGroupOp sessCurveOp
   atomicDraw256 atomicDraw256_eval atomicDraw256_cost
   atomicDraw512 atomicDraw512_eval atomicDraw512_cost
   liftTy liftVal liftExpr liftEnv liftExpr_eval coinE2EIface liftCompCoins
   liftCompCoins_queries_zero liftCompCoins_eval wk1Expr wk1Expr_cost wk1Expr_eval
   wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval drRecvAtomicOutT)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (letE_eval comp_eval_ret comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt
   comp_eval_caseSum isQueryBoundP_of_makesAtMostQueries bits_succ_le
   liftExpr_size_le liftCompCoins_size_le wk1Expr_size wk1Comp_size
   session_cost_le_ratchetCostBudget dummyBoolSessionRed dummyBoolSessionRed_totalQueries
   dummyBoolSessionRed_totalCost_le dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys
  (spkMaxWireLen cost_spkWireKeyE_of_lt size_spkWireKeyE_of_lt)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (Tier2Gs Tier2GsRel)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase
  (tier2RecvRejE tier2RecvAccE tier2SmRWireE tier2SmRRecvE tier2SmRCorrE
   eval_tier2RecvRejE eval_tier2RecvAccE eval_tier2SmRWireE eval_tier2SmRRecvE eval_tier2SmRCorrE
   tier2RecTy tier2RecEnc tier2RecPos tier2RecCt tier2RecMk eval_tier2RecPos eval_tier2RecMk
   tier2SmRenc e2eSessionCodec_rdec_tier2SmRenc
   tier2GsTy tier2GsEnc gsStTier2E gsBTier2E gsWinTier2E gsEpochTier2E gsIdxTier2E
   initGsTier2E eval_initGsTier2E setWinTier2E eval_setWinTier2E
   safeChTier2E eval_safeChTier2E safeInjTier2E eval_safeInjTier2E
   epMgmtTier2E eval_epMgmtTier2E gsChallTier2E eval_gsChallTier2E
   trivialTier2E eval_trivialTier2E corrAllowedTier2E eval_corrAllowedTier2E
   afterCorrAllowedTier2E eval_afterCorrAllowedTier2E
   inWindowTier2E eval_inWindowTier2E sendOKTier2E eval_sendOKTier2E corrOKTier2E eval_corrOKTier2E)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping
  (acceptCiphertextTier2E eval_acceptCiphertextTier2E
   inTransitTier2E eval_inTransitTier2E
   recordCiphertextTier2E eval_recordCiphertextTier2E sessionSchemeU_send_wire_length_le
   spk_totalCost_le_spkTier2Budget)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs
  (tier2GsRel_init_pair tier2GsRel_record_preserves tier2GsRel_accept_preserves)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift
  (OracleCompRel eval_eq_simulateQ_of_rel)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2
  (kemTrackTier2T honestWiresTier2T kemSessionTrackTier2T
   kemTrackTier2Enc honestWiresTier2Enc kemSessionTrackTier2Enc
   KemTrackTier2Inv kemTrackTier2Inv_initSim kemTrackTier2Inv_stepSendSim
   kemTrackTier2Inv_stepDeliverSim
   initKemFailSessionTrackTier2E initKemFailSessionTrackTier2E_eval
   stepKemFailSendTier2C stepKemFailSendTier2C_eval
   recordHonestWireTier2E recordHonestWireTier2E_eval
   findRevHonestWireIdxTier2E findRevHonestWireIdxTier2E_eval
   kemOnDeliverPostTier2E kemOnDeliverPostTier2E_eval)
open Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
  (spkInitArgT spkInitGsE2EE eval_spkInitGsE2EE
   receiveSpkAtomicC receiveSpkAtomicC_eval_and_inv)

open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Defs
  (spkHaltedTier2StTy samIfNec512Tier2C ratchetKeyAdmissibleTier2E drSendCoinsTier2C
   spkInitHaltedTier2C spkInitHaltedTier2C_queries spkInitHaltedTier2C_cost spkInitHaltedTier2C_size
   spkTrArmHaltedTier2C spkChArmHaltedTier2C spkDlArmHaltedTier2C spkIjArmHaltedTier2C
   spkCrArmHaltedTier2C spkStepHaltedTier2C spkStepHaltedTier2C_queries spkStepHaltedTier2C_cost
   spkStepHaltedTier2C_size spkFinishTier2C spkFinishTier2C_cost spkFinishTier2C_size)

section HaltedTier2

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) (idA idB : IdentityKey)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "PrfI" => extractPtPrfIface ℓ Pt


/-! ## Relational state invariant -/

theorem extractPtPrfIface_liftP {α : Type} (p : ProbComp α) :
    (extractPtPrfIface ℓ Pt).liftP p =
      (liftM p : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [ReductionDsl.Iface.liftP]
  | query_bind t mx ih =>
    rw [ReductionDsl.Iface.liftP, simulateQ_query_bind, liftM_unif_query_bind]
    exact bind_congr ih

private theorem samIfNec512Tier2C_eval {Γ : List (Ty ASig)}
    (optR : Expr AOps Γ (.opt BV512)) (ρ : Env Γ) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).eval ρ =
      (extractPtPrfIface ℓ Pt).liftP (samIfNec (optR.eval ρ)) := by
  unfold samIfNec512Tier2C samIfNec
  rw [comp_eval_caseOpt]
  cases optR.eval ρ with
  | none =>
    dsimp only
    rw [comp_eval_bind, atomicDraw512_eval]
    simp [comp_eval_ret, Expr.eval, Expr.v0, Iface.liftP]
  | some r =>
    simp [comp_eval_ret, Expr.eval, Expr.v0, Iface.liftP]

private theorem drSendCoinsTier2C_eval {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) (ρ : Env Γ)
    (st_q : GhostState Bytes) (mSend : Plain ℓ) (rCoins : BitVec 512)
    (hinp : inpE.eval ρ = (st_q, (mSend, rCoins)))
    (hg : PartyReachInv C K st_q) :
    (drSendCoinsTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).eval ρ =
    pure ((sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ).send
      st_q mSend rCoins) := by
  rw [drSendCoinsTier2C, comp_eval_bind_ret, hinp, wk1Comp_eval]
  let tDr : Ty ESig := .prod CryptoVerification.E2E.Costed.GhostStT
    (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  have hl := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drSendC hooks (coinE2EIface (ℓ := ℓ) PrfI) (.v0 : Expr EOps [tDr] _))
    (.cons (t := tDr) (st_q, (mSend, rCoins)) .nil)
  have hsend := drSendC_eval hooks (coinE2EIface (ℓ := ℓ) PrfI) (.v0 : Expr EOps [tDr] _)
    (.cons (t := tDr) (st_q, (mSend, rCoins)) .nil) idA idB 0 hg
  change _ = pure ((sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ 0).send st_q mSend rCoins)
  rw [show Env.cons (t := .prod GhostStT (.prod PlainT BV512))
      (st_q, (mSend, rCoins)) .nil =
      liftEnv (Pt := Pt) (.cons (t := tDr) (st_q, (mSend, rCoins)) .nil) from rfl,
    hl, hsend, map_pure]
  rfl

@[expose] def kemCoinsEnc : CryptoVerification.SpqrV1Sync.Braid.Coins → SimKemCoins
  | .init => .init
  | .seed s => .seed s
  | .both s r => .both s r

@[expose] def kemTrackEnc {F : ShaCompress} (tr : KemFailTrackState F) : SimKemFailTrack F :=
  { e := tr.e, auth := tr.auth, c := kemCoinsEnc tr.c, st := tr.st,
    sentB := tr.sentB, sendCtr := tr.sendCtr, cand := tr.cand }

abbrev bridgeToRefTrack {F : ShaCompress} (tr : KemFailTrackState F) :
    KemFailTrackState F := tr

@[expose] def deliverPostTrack {Msg : Type} (F : ShaCompress) (K : MlKem)
    (trk : KemFailSessionTrack F Bytes) (x : Party × Bytes)
    (res : Option (RecvResult Msg)) : KemFailSessionTrack F Bytes :=
  match res, trk.2.reverse.findIdx? (fun wp => wp.1 == x.2 && wp.2 == x.1.other) with
  | some (.accepted _ _ _), some j => (stepKemFailDeliver F K trk.1 x.1 j, trk.2)
  | _, _ => trk

@[expose] def spkStepTrackRef (qep : ℕ) (s : BitVec 256)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (trk : KemFailSessionTrack C.F Bytes) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        GameState (GhostState Bytes) (Plain ℓ) Bytes) ×
       KemFailSessionTrack C.F Bytes) :=
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let cfg := configRefuseEarlyBobCorr decT encT
  match sq with
  | .inl (.inl (.inl (.inl x))) =>
    liftM (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x).run st).run trk)
  | .inl (.inl (.inl (.inr x))) =>
    liftM (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x).run st).run trk)
  | .inl (.inl (.inr x)) =>
    (fun rs => (rs, deliverPostTrack C.F K trk x rs.1)) <$>
      (deliverSpk P ℓ Dh encT decT s x).run st
  | .inl (.inr x) =>
    (fun rs => (rs, trk)) <$> (injectSpk P ℓ Dh encT decT qep s x).run st
  | .inr x =>
    (fun rs => (rs, trk)) <$> (liftSpkGameM (corrR cfg x)).run st

@[expose] def spkInitHaltedImpl (s : BitVec 256) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (Unit × (GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes)) := do
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool)
  let ck0 ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
  let rest ← (liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256))
  let stA ← initAOracle (Pt := Pt) P Dh ck0 s rest.1 rest.2
  let stB := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
  return ((), ({ st := fun Q => match Q with | .A => stA | .B => stB, b := b },
    (initKemFailTrack C.F rest.2, [])))

structure SpkHaltedTier2SimRel (s : BitVec 256) (_m : ℕ)
    (st₁ : (spkHaltedTier2StTy ℓ Pt).denote)
    (gst : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes) : Prop where
  exists_gs : ∃ d : Tier2Gs ℓ, st₁.1 = (s, tier2GsEnc Pt d) ∧ Tier2GsRel ℓ gst.1 d
  party_inv : ∀ Q : Party, PartyReachInv C K (gst.1.st Q)
  trk_enc : st₁.2 = kemSessionTrackTier2Enc ℓ (kemTrackEnc (bridgeToRefTrack gst.2.1), gst.2.2)
  kem_inv : KemTrackTier2Inv C.F K (kemTrackEnc (bridgeToRefTrack gst.2.1))
  hw_len : ∀ wp ∈ gst.2.2, wp.1.length ≤ spkMaxWireLen ℓ

private theorem bridgeToRefTrack_init_eq (F : ShaCompress) (k : BitVec 256) :
    kemTrackEnc (bridgeToRefTrack (initKemFailTrack F k)) = simInitKemFailTrack F k := rfl

theorem spkInitHaltedTier2C_rel (qAdv : ℕ) (s : BitVec 256) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s qAdv r₁.2 r₂.2)
      ((spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).eval (.cons s .nil))
      (spkInitHaltedImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let ρ₀ : Env (S := ASig) [BV256] := .cons s .nil
  have hsampBool :
      (Comp.sample (O := AOps) (I := PrfI) UniformSamplerTag.bool .unit).eval ρ₀ =
        (liftM ($ᵗ Bool : ProbComp Bool) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool) := by
    rw [show (Comp.sample (O := AOps) (I := PrfI) UniformSamplerTag.bool .unit).eval ρ₀ =
      (PrfI).liftP ($ᵗ Bool : ProbComp Bool) from rfl]
    exact extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt) ($ᵗ Bool)
  rw [spkInitHaltedTier2C, comp_eval_bind, hsampBool]
  unfold spkInitHaltedImpl
  refine OracleCompRel.bind_same _ _ _ fun b _ => ?_
  rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP]
  refine OracleCompRel.bind_same _ _ _ fun ck0 _ => ?_
  let tailC : Comp AOps PrfI [BV256, BV256, BV256, .bool, BV256]
      (.prod .unit (spkHaltedTier2StTy ℓ Pt)) :=
    .bind
      (Comp.query (I := PrfI) ()
        (sessGroupOp .ptDh
          (.pair .v4 (sessGroupOp .ptDh (.pair .v1 (sessGroupOp .ptBase .unit))))))
      (let sVar : Expr AOps _ BV256 := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
       let initArgE : Expr AOps _ (liftTy (Pt := Pt) (spkInitArgT ℓ)) :=
         .pair .v4 (.pair sVar (.pair (sessGroupOp .rootExpandPrg .v0)
           (.pair .v3 (.pair .v2 .v1))))
       let gsE2EE :=
         Expr.letE initArgE
           (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
             (encT := encT) (decT := decT) (lam := lam)
             (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K)
               (decT := decT) (encT := encT) idA idB)))
       let gs2E : Expr AOps _ (tier2GsTy ℓ Pt) :=
         .letE (.pair .v4 (.fst gsE2EE))
           (initGsTier2E (.fst (.snd .v0)) (.snd (.snd .v0)) (.fst .v0))
       .ret (.pair .unit
         (.pair (.pair sVar gs2E)
           (initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
             (encT := encT) (decT := decT) (lam := lam) .v1))))
  have htwo :
      (Comp.bind (atomicDraw256 (O := AOps) (I := PrfI) rfl)
        (.bind (atomicDraw256 (O := AOps) (I := PrfI) rfl) tailC)).eval
        (Env.cons (S := ASig) ck0 (.cons b (.cons s .nil))) =
      ((liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256)) >>=
        fun rest =>
          tailC.eval
            (Env.cons (S := ASig) rest.2 (.cons rest.1 (.cons ck0 (.cons b (.cons s .nil)))))) := by
    rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
    have hinner : ∀ v : BitVec 256,
        (Comp.bind (atomicDraw256 (O := AOps) (I := PrfI) rfl) tailC).eval
          (Env.cons (S := ASig) v (.cons ck0 (.cons b (.cons s .nil)))) =
        ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>=
          fun v_1 =>
            tailC.eval
              (Env.cons (S := ASig) v_1 (.cons v (.cons ck0 (.cons b (.cons s .nil)))))) := by
      intro v
      rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
    simp only [hinner]
    exact (liftM_sample_prod_bind_bv256 fun rest : BitVec 256 × BitVec 256 =>
      tailC.eval
        (Env.cons (S := ASig) rest.2 (.cons rest.1 (.cons ck0 (.cons b (.cons s .nil)))))).symm
  rw [htwo]
  refine OracleCompRel.bind_same _ _ _ fun rest _ => ?_
  let ρ₄ : Env (S := ASig) [BV256, BV256, BV256, .bool, BV256] :=
    .cons rest.2 (.cons rest.1 (.cons ck0 (.cons b (.cons s .nil))))
  have hq :
      (Comp.query (O := AOps) (I := PrfI) ()
        (sessGroupOp .ptDh
          (.pair .v4 (sessGroupOp .ptDh (.pair .v1 (sessGroupOp .ptBase .unit)))))).eval ρ₄ =
        evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh s (Dh.dh rest.1 Dh.base)) := by
    dsimp only [Comp.eval]
    simp only [Expr.eval, eval_sessGroupOp, Expr.v1, Expr.v4]
    rfl
  rw [comp_eval_bind, hq]
  dsimp only [initAOracle]
  rw [bind_assoc]
  refine OracleCompRel.bind_same _ _ _ fun prk _ => ?_
  rw [pure_bind, comp_eval_ret]
  let ρ₅ : Env (S := ASig) [BV256, BV256, BV256, BV256, .bool, BV256] := .cons prk ρ₄
  let rk1 := ((expandPRG C.F).gen prk).1
  let ck1 := ((expandPRG C.F).gen prk).2
  let initArgVal : (spkInitArgT ℓ).denote := (b, (s, ((rk1, ck1), (ck0, (rest.1, rest.2)))))
  let stA : GhostState Bytes :=
    ⟨.A, (((SessionState.new currentVersion idA idB rk1
      (spqrV1Init C.F K .a2b rest.2)).addReceiverChain
      (KeyPair.generate C s).publicKey ⟨ck0, 0⟩).setSenderChain
      (KeyPair.generate C rest.1) ⟨ck1, 0⟩).setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB : GhostState Bytes := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
  have hgs :
      (Expr.letE
        (.pair .v4 (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.pair (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .rootExpandPrg .v0)
            (.pair .v3 (.pair .v2 .v1)))))
        (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K)
            (decT := decT) (encT := encT) idA idB)))).eval ρ₅ =
      liftVal (Pt := Pt)
        (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsEnc
          ({ st := fun Q => match Q with | .A => stA | .B => stB, b := b } :
            GameState (GhostState Bytes) (Plain ℓ) Bytes)) := by
    rw [letE_eval, wk1Expr_eval]
    have harg : (Expr.pair .v4 (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.pair (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .rootExpandPrg .v0)
          (.pair .v3 (.pair .v2 .v1)))) :
        Expr AOps _ (liftTy (Pt := Pt) (spkInitArgT ℓ))).eval ρ₅ = initArgVal := by
      simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
      rfl
    rw [harg]
    have henv : (Env.cons initArgVal .nil : Env (S := ASig) [liftTy (Pt := Pt) (spkInitArgT ℓ)]) =
        liftEnv (Pt := Pt) (.cons initArgVal .nil : Env [spkInitArgT ℓ]) := rfl
    rw [henv, liftExpr_eval, eval_spkInitGsE2EE]
    rfl
  have htr2 := initKemFailSessionTrackTier2E_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (.v1 : Expr AOps _ BV256) ρ₅ rest.2 rfl
  refine OracleCompRel.pureP ⟨rfl, ?_⟩
  refine ⟨⟨Tier2Gs.init stA stB b, ?_, tier2GsRel_init_pair stA stB b⟩, ?_, ?_,
    by rw [bridgeToRefTrack_init_eq]; exact kemTrackTier2Inv_initSim C.F K rest.2,
    by simp⟩
  · have hb5 : (Expr.v4 (O := AOps)).eval ρ₅ = b := rfl
    have hs5 :
        (Expr.var (O := AOps) (.succ (.succ (.succ (.succ (.succ .zero)))))).eval ρ₅ = s := rfl
    let gsE2E5 :
        Expr AOps [BV256, BV256, BV256, BV256, .bool, BV256]
          (liftTy (Pt := Pt) (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsTy ℓ)) :=
      Expr.letE
        (.pair .v4 (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.pair (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .rootExpandPrg .v0)
            (.pair .v3 (.pair .v2 .v1)))))
        (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K)
            (decT := decT) (encT := encT) idA idB)))
    have hfst_gs : (Expr.fst gsE2E5).eval ρ₅ = (stA, stB) := by
      change (gsE2E5.eval ρ₅).1 = (stA, stB)
      rw [hgs]; rfl
    change ((Expr.var (O := AOps) (.succ (.succ (.succ (.succ (.succ .zero)))))).eval ρ₅,
      (Expr.letE (.pair .v4 (.fst gsE2E5))
        (initGsTier2E (.fst (.snd .v0)) (.snd (.snd .v0)) (.fst .v0))).eval ρ₅) =
      (s, tier2GsEnc Pt (Tier2Gs.init stA stB b))
    have hpair5 : (Expr.pair .v4 (.fst gsE2E5)).eval ρ₅ = (b, (stA, stB)) := by
      change ((Expr.v4 (O := AOps)).eval ρ₅, (Expr.fst gsE2E5).eval ρ₅) = (b, (stA, stB))
      rw [hb5, hfst_gs]
    rw [hs5, letE_eval, hpair5, eval_initGsTier2E]
    rfl
  · intro Q
    cases Q with
    | A =>
      have htop0 := topStateTight_init C.F K .a2b rest.2
      have hnot5 : ¬ (5 < 1) := by decide
      dsimp only [stA, SessionState.setUnacknowledgedPreKeyMessage, SessionState.setSenderChain,
        SessionState.addReceiverChain, SessionState.new]
      refine ⟨htop0, ?_, ?_, ?_, ?_⟩
      · simp [maxReceiverChains]
      · intro rc hrc
        simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
          List.mem_singleton] at hrc
        subst hrc
        simp
      · intro rc hrc mk hmk
        simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
          List.mem_singleton] at hrc
        subst hrc
        simp at hmk
      · simp [maxReceiverChains]
    | B =>
      exact Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_initB
        C K (P := P) rfl ⟨0, ck0, s, rest.1, rest.2⟩
  · exact htr2

/-! ## Step evaluation helpers -/

theorem pair_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (x : Expr O0 Γ a) (y : Expr O0 Γ b) (ρ : Env Γ) :
    (Expr.pair x y).eval ρ = (x.eval ρ, y.eval ρ) := rfl

theorem ite_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (c : Expr O0 Γ .bool) (t f : Expr O0 Γ a) (ρ : Env Γ) :
    (Expr.ite c t f).eval ρ = (if c.eval ρ then t.eval ρ else f.eval ρ) := rfl

theorem none_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig} (ρ : Env Γ) :
    (Expr.none : Expr O0 Γ (.opt a)).eval ρ = none := rfl

theorem some_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (x : Expr O0 Γ a) (ρ : Env Γ) :
    (Expr.some x).eval ρ = some (x.eval ρ) := rfl

theorem snd_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (x : Expr O0 Γ (.prod a b)) (ρ : Env Γ) :
    (Expr.snd x).eval ρ = (x.eval ρ).2 := rfl

theorem v0_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (v : a.denote) (ρ : Env Γ) :
    (Expr.v0 : Expr O0 (a :: Γ) a).eval (.cons v ρ) = v := rfl

theorem eval_pGet_gsStTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsStTier2E sE) pE).eval ρ = d.st p := by
  cases p <;> simp [pGet, gsStTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

theorem eval_gsBTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (hs : sE.eval ρ = tier2GsEnc Pt d) :
    (gsBTier2E sE).eval ρ = d.b := by
  simp [gsBTier2E, Expr.eval, hs, tier2GsEnc]

theorem eval_gsWinTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (hs : sE.eval ρ = tier2GsEnc Pt d) :
    (gsWinTier2E sE).eval ρ = d.win := by
  simp [gsWinTier2E, Expr.eval, hs, tier2GsEnc]

theorem eval_pGet_gsEpochTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsEpochTier2E sE) pE).eval ρ = d.epoch p := by
  cases p <;> simp [pGet, gsEpochTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

theorem eval_pGet_gsIdxTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsIdxTier2E sE) pE).eval ρ = d.idx p := by
  cases p <;> simp [pGet, gsIdxTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

theorem partyToBool_eq_partyEnc (p : Party) :
    partyToBool p = partyEnc p := by
  cases p <;> rfl

theorem otherE_eval_partyEnc {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (pE : Expr O0 Γ .bool) (ρ : Env Γ) (p : Party) (hp : pE.eval ρ = partyEnc p) :
    (otherE pE).eval ρ = partyEnc p.other := by
  cases p <;> simp [otherE, Expr.eval, hp, partyEnc, Party.other]

theorem epMgmt_st_eq
    {gs gs' : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {Δ qep : ℕ} {p : Party} {bad : Bool}
    (h : gs.epMgmt Δ qep p bad = some gs') :
    gs'.st = gs.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> cases h <;> rfl

theorem liftM_prob_pure {α : Type} (x : α) :
    (liftM (pure x : ProbComp α) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) = pure x := by
  rw [← extractPtPrfIface_liftP (ℓ := 0) (Pt := Pt)]
  simp [ReductionDsl.Iface.liftP]

theorem liftM_prob_bind {α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    (liftM (p >>= f) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) =
      (liftM p : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) >>=
        fun a => (liftM (f a) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) := by
  simp_rw [← extractPtPrfIface_liftP (ℓ := 0) (Pt := Pt)]
  simp [ReductionDsl.Iface.liftP]

private theorem stateT_lift_get_run2 {S₁ S₂ : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift get : StateT S₁ (StateT S₂ M) S₂).run s₁).run s₂) = pure ((s₂, s₁), s₂) := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]

private theorem stateT_lift_prob_run2 {S₁ S₂ α : Type} (p : ProbComp α) (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift (liftM p : StateT S₂ ProbComp α) :
        StateT S₁ (StateT S₂ ProbComp) α).run s₁).run s₂) =
      p >>= fun a => pure ((a, s₁), s₂) := by
  simp [monadLift]

private theorem kemCoinsEnc_nextCoins (F : ShaCompress)
    (c : CryptoVerification.SpqrV1Sync.Braid.Coins)
    (st : SimBraidSt F) (tape : List (BitVec 8)) :
    kemCoinsEnc (CryptoVerification.SpqrV1Sync.Braid.nextCoins F c st tape) =
      simNextKemCoins F (kemCoinsEnc c) st tape := by
  cases c <;> cases st <;>
    simp only [CryptoVerification.SpqrV1Sync.Braid.nextCoins, simNextKemCoins, kemCoinsEnc]
  all_goals split_ifs <;> rfl

private theorem simEkSideIsA_bne_eq (e : BitVec 64) (Q : Party) :
    (simEkSideIsA e != (Q == .A)) =
      (CryptoVerification.SpqrV1Sync.Braid.ekSide e !=
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.kemBraidParty Q) := by
  cases Q <;> by_cases h : e.toNat % 2 = 1 <;>
    simp only [simEkSideIsA, CryptoVerification.SpqrV1Sync.Braid.ekSide,
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.kemBraidParty, h, ↓reduceIte] <;>
    decide

private theorem simStepKemFailSend_kemTrackEnc (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    simStepKemFailSend F K (kemTrackEnc tr) Q r =
      kemTrackEnc (stepKemFailSend F K tr Q r) := by
  unfold simStepKemFailSend stepKemFailSend
  dsimp only [kemTrackEnc]
  rcases (tr.st Q).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with err | ⟨out, _⟩ <;>
    simp only [kemCoinsEnc_nextCoins, simEkSideIsA_bne_eq] <;>
    congr 1 <;> rcases tr.cand with _ | p <;> rcases tr.c with _ | s | ⟨s, r₀⟩ <;>
    rcases tr.st Q <;> rfl

private theorem bridgeToRefTrack_stepSend (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    bridgeToRefTrack (stepKemFailSend F K tr Q r) = stepKemFailSend F K (bridgeToRefTrack tr) Q r :=
  rfl

private theorem kemTrackEnc_cand_latch (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    { kemTrackEnc (bridgeToRefTrack tr) with
      cand := (simStepKemFailSend F K (kemTrackEnc (bridgeToRefTrack tr)) Q r).cand } =
    kemTrackEnc (bridgeToRefTrack { tr with cand := (stepKemFailSend F K tr Q r).cand }) := by
  rw [simStepKemFailSend_kemTrackEnc]
  rfl

private theorem partyReachInv_record
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hinv : ∀ Q, PartyReachInv C K (gs.st Q))
    (Δ : ℕ) (Q : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st')
    (r : Record (Plain ℓ) Bytes) (isChall : Bool) :
    ∀ Q', PartyReachInv C K ((gs.record Δ Q st' r isChall).st Q') := by
  intro Q'
  dsimp only [GameState.record]
  by_cases hQ : Q' = Q
  · subst hQ; rw [Function.update_self]; exact hst'
  · rw [Function.update_of_ne hQ]; exact hinv Q'


/-! ## Transmit and challenge relational proofs -/

theorem spkTrArmHaltedTier2C_rel (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (Q : Party) (msg : Plain ℓ) (optR : Option (BitVec 512))
    (st₁ : (spkHaltedTier2StTy ℓ Pt).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (hs : SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s (m + 1) st₁ (gs, (tr, hw))) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inl (Q, msg, optR))))) r₁.1 = r₂.1.1 ∧
          SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 (r₂.1.2, r₂.2))
      ((spkTrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval
        (Env.cons (S := ASig) (st₁, (partyEnc Q, (msg, optR))) .nil))
      (spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s
        (.inl (.inl (.inl (.inl (Q, msg, optR))))) gs (tr, hw)) := by
  rcases hs with ⟨⟨d, hst1, hrel⟩, hinv, htrk1, hkem, hhw⟩
  rcases st₁ with ⟨st₁_gs, st₁_trk⟩
  dsimp only at hst1 htrk1
  subst hst1; subst htrk1
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inl (Q, msg, optR))))
  let t0 : Ty ASig := .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))
  let st₁Val : (spkHaltedTier2StTy ℓ Pt).denote :=
    ((s, tier2GsEnc Pt d), kemSessionTrackTier2Enc ℓ (kemTrackEnc (bridgeToRefTrack tr), hw))
  let ρ₀ : Env (S := ASig) [t0] := .cons (st₁Val, (partyEnc Q, (msg, optR))) .nil
  have hpres : SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m st₁Val (gs, (tr, hw)) :=
    ⟨⟨d, rfl, hrel⟩, hinv, rfl, hkem, hhw⟩
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1.1 ∧
        SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 (r₂.1.2, r₂.2))
    ((spkTrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval ρ₀)
    (liftM (((transmitRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, msg, optR)).run gs).run (tr, hw)))
  have hguard :
      (orE (.not (sendOKTier2E (.snd (.fst (.fst .v0))) (.fst (.snd .v0))))
        (gsWinTier2E (.snd (.fst (.fst .v0)))) : Expr AOps [t0] .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.snd (.fst (.fst .v0))) (.fst (.snd .v0))) :
        Expr AOps [t0] .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]
      rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [spkTrArmHaltedTier2C, comp_eval_ite, hguard]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret,
      transmitRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind, hok,
      StateT.run_pure, liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, hpres⟩
    rw [pair_ev, eval_tier2SmRWireE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  | true =>
    cases hwin : gs.win with
    | true =>
      simp only [Bool.not_true, Bool.false_or, ↓reduceIte, comp_eval_ret,
        transmitRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind, hok, hwin]
      refine OracleCompRel.pureP ⟨?_, hpres⟩
      rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    | false =>
      simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      have hrhs :
          (liftM (((transmitRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep cfg
              (Q, msg, optR)).run gs).run (tr, hw)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _) =
          (liftM (samIfNec optR) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 512 × Bool)) >>=
            fun ⟨coins, bad⟩ =>
              (liftM ((match gs.epMgmt 3 qep Q bad with
                | none => pure ((none, gs), (tr, hw))
                | some gs₁ =>
                  let tr' := stepKemFailSend C.F K tr Q coins
                  if tr'.cand.isSome then
                    pure ((none, gs), ({ tr with cand := tr'.cand }, hw))
                  else
                    let out := (sessionSchemeU P ℓ).send (gs₁.st Q) msg coins
                    pure ((some out.2,
                      gs₁.record 3 Q out.1 ⟨⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩, msg, out.2⟩ false),
                      (tr', (out.2, Q) :: hw))) : ProbComp _) :
                OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _) := by
        simp only [transmitRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind,
          hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwin,
          stateT_lift_prob_run2, bind_assoc, liftM_prob_bind]
        refine bind_congr fun ⟨coins, bad⟩ => ?_
        cases hep : gs.epMgmt 3 qep Q bad with
        | none => rfl
        | some gs₁ =>
          dsimp only
          simp only [StateT.run_bind, stateT_lift_get_run2, pure_bind]
          split_ifs <;> simp_all [StateT.run_set, StateT.run_lift]
      rw [hrhs, comp_eval_bind, samIfNec512Tier2C_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
      have hoptR : (Expr.snd (.snd (.snd (Expr.v0 (O := AOps)))) :
          Expr AOps [t0] (.opt BV512)).eval ρ₀ = optR := rfl
      rw [hoptR]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      dsimp only
      let ρ₁ : Env (S := ASig) [.prod BV512 .bool, t0] := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) : Expr AOps [.prod BV512 .bool, t0] .bool).eval ρ₁ =
          bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, hpres⟩
          rw [pair_ev, eval_tier2SmRWireE, none_ev]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
        | some d₁ =>
          simp [hep_gs, hep_d] at hep_none
      | some gs₁ =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp [hep_gs, hep_d] at hep_none
        | some d₁ =>
          have hrel₁ : Tier2GsRel ℓ gs₁ d₁ := hep_rel gs₁ d₁ hep_gs hep_d
          have hinv₁ : ∀ Q', PartyReachInv C K (gs₁.st Q') := by
            intro Q'; rw [epMgmt_st_eq hep_gs]; exact hinv Q'
          simp only [Option.map_some]
          let ρ₂ : Env (S := ASig) [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
            .cons (tier2GsEnc Pt d₁) ρ₁
          have hkf := stepKemFailSendTier2C_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (I := PrfI)
            (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.fst .v1) ρ₂
            (kemTrackEnc (bridgeToRefTrack tr)) Q coins rfl
            (partyToBool_eq_partyEnc Q).symm rfl (hkem.bOk Q)
          rw [comp_eval_bind, hkf, pure_bind]
          let trS' := simStepKemFailSend C.F K (kemTrackEnc (bridgeToRefTrack tr)) Q coins
          let outKf : (Ty.prod (S := ASig) .bool (kemTrackTier2T ℓ Pt)).denote :=
            (trS'.cand.isSome,
             if trS'.cand.isSome then
               kemTrackTier2Enc { kemTrackEnc (bridgeToRefTrack tr) with cand := trS'.cand }
             else kemTrackTier2Enc trS')
          let ρ₃ : Env (S := ASig)
              [.prod .bool (kemTrackTier2T ℓ Pt), tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
            .cons outKf ρ₂
          have hcand_eq : trS'.cand.isSome = (stepKemFailSend C.F K tr Q coins).cand.isSome := by
            dsimp only [trS']
            rw [simStepKemFailSend_kemTrackEnc, ← bridgeToRefTrack_stepSend]
            rfl
          have hfst3 : (Expr.fst (Expr.v0 (O := AOps)) : Expr AOps _ .bool).eval ρ₃ =
              (stepKemFailSend C.F K tr Q coins).cand.isSome := hcand_eq
          rw [comp_eval_ite, hfst3]
          cases hcand : (stepKemFailSend C.F K tr Q coins).cand.isSome with
          | true =>
            simp only [↓reduceIte, comp_eval_ret, liftM_prob_pure]
            refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, ?_, ?_, hhw⟩
            · rw [pair_ev, eval_tier2SmRWireE, none_ev]
              exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
            · rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev]
              have hv0s : (Expr.snd (Expr.v0 (O := AOps))).eval ρ₃ =
                  kemTrackTier2Enc (Pt := Pt)
                    (kemTrackEnc (bridgeToRefTrack
                      { tr with cand := (stepKemFailSend C.F K tr Q coins).cand })) := by
                change outKf.2 = _
                dsimp only [outKf]
                rw [hcand_eq, hcand]
                simp only [↓reduceIte]
                rw [kemTrackEnc_cand_latch]
              rw [hv0s]
              rfl
            · rw [← kemTrackEnc_cand_latch]
              exact hkem.withCand _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, liftM_prob_pure]
            have hinp :
                (Expr.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3)))
                  (.pair (.fst (.snd (.snd .v3))) (.fst .v2)) :
                  Expr AOps _ (.prod GhostStT (.prod PlainT BV512))).eval ρ₃ =
                (gs₁.st Q, (msg, coins)) := by
              rw [pair_ev, eval_pGet_gsStTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_st, pair_ev]
              rfl
            rw [comp_eval_bind,
              drSendCoinsTier2C_eval C K Dh encPt encT decT lam idA idB _ ρ₃
                (gs₁.st Q) msg coins hinp (hinv₁ Q),
              pure_bind, comp_eval_ret]
            let out := (sessionSchemeU P ℓ).send (gs₁.st Q) msg coins
            let ρ₄ : Env (S := ASig)
                [.prod GhostStT (B 32), .prod .bool (kemTrackTier2T ℓ Pt),
                 tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
              .cons out ρ₃
            let p0 : Pos := ⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩
            have hposE :
                (Expr.pair (.fst (.snd .v4))
                  (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
                    (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))) :
                  Expr AOps _ posTy).eval ρ₄ = posEnc p0 := by
              rw [pair_ev, pair_ev, eval_pGet_gsEpochTier2E _ _ ρ₄ d₁ Q rfl rfl, hrel₁.h_epoch]
              change (partyEnc Q, (gs₁.epoch Q,
                (pGet (gsIdxTier2E .v2) (.fst (.snd .v4)) : Expr AOps _ .nat).eval ρ₄ + 1)) =
                posEnc p0
              rw [eval_pGet_gsIdxTier2E _ _ ρ₄ d₁ Q rfl rfl, hrel₁.h_idx]
              rfl
            have hrecE :
                (tier2RecMk
                  (.pair (.fst (.snd .v4))
                    (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
                      (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))))
                  (.fst (.snd (.snd .v4))) (.snd .v0) :
                  Expr AOps _ (tier2RecTy ℓ Pt)).eval ρ₄ =
                tier2RecEnc ⟨p0, msg, out.2⟩ :=
              eval_tier2RecMk _ _ _ ρ₄ p0 hposE
            have hrecGs := eval_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) 3
              .v2 (.fst (.snd .v4)) (.fst .v0)
              (tier2RecMk
                (.pair (.fst (.snd .v4))
                  (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
                    (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))))
                (.fst (.snd (.snd .v4))) (.snd .v0))
              (.bool false) ρ₄ d₁ Q ⟨p0, msg, out.2⟩ rfl rfl hrecE
            have hhw2 := recordHonestWireTier2E_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.snd (.snd (.fst .v4))) (.snd .v0) (.fst (.snd .v4)) ρ₄ hw out.2 Q
              rfl rfl (partyToBool_eq_partyEnc Q).symm
            have hlen_out := sessionSchemeU_send_wire_length_le C K idA idB (gs₁.st Q) msg coins
            refine OracleCompRel.pureP ⟨?_,
              ⟨d₁.record 3 Q out.1 ⟨p0, msg, out.2⟩ false, ?_,
                tier2GsRel_record_preserves hrel₁ 3 Q out.1 ⟨p0, msg, out.2⟩ false rfl hlen_out⟩,
              partyReachInv_record C K hinv₁ 3 Q
                (Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_send
                  C K (P := P) rfl (hinv₁ Q) msg.toList coins) ⟨p0, msg, out.2⟩ false,
              ?_, ?_, ?_⟩
            · rw [pair_ev, eval_tier2SmRWireE, some_ev]
              exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some out.2)
            · rw [pair_ev]; dsimp only; rw [pair_ev, pair_ev, hrecGs]
              rfl
            · rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev, hhw2]
              have hv1s : (Expr.snd (Expr.v1 (O := AOps))).eval ρ₄ =
                  kemTrackTier2Enc (Pt := Pt)
                    (kemTrackEnc (bridgeToRefTrack (stepKemFailSend C.F K tr Q coins))) := by
                change outKf.2 = _
                dsimp only [outKf]
                rw [hcand_eq, hcand]
                simp only [Bool.false_eq_true, ↓reduceIte]
                dsimp only [trS']
                rw [simStepKemFailSend_kemTrackEnc, ← bridgeToRefTrack_stepSend]
              rw [hv1s]
              rfl
            · rw [bridgeToRefTrack_stepSend, ← simStepKemFailSend_kemTrackEnc]
              exact kemTrackTier2Inv_stepSendSim C.F K _ Q coins hkem
            · intro wp hwp
              rcases List.mem_cons.mp hwp with rfl | hwp'
              · exact hlen_out
              · exact hhw wp hwp'

theorem spkChArmHaltedTier2C_rel (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (optR : Option (BitVec 512))
    (st₁ : (spkHaltedTier2StTy ℓ Pt).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (hs : SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s (m + 1) st₁ (gs, (tr, hw))) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) r₁.1 = r₂.1.1 ∧
          SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 (r₂.1.2, r₂.2))
      ((spkChArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval
        (Env.cons (S := ASig) (st₁, (partyEnc Q, (m₀, (m₁, optR)))) .nil))
      (spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s
        (.inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) gs (tr, hw)) := by
  rcases hs with ⟨⟨d, hst1, hrel⟩, hinv, htrk1, hkem, hhw⟩
  rcases st₁ with ⟨st₁_gs, st₁_trk⟩
  dsimp only at hst1 htrk1
  subst hst1; subst htrk1
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))
  let t0 : Ty ASig :=
    .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let st₁Val : (spkHaltedTier2StTy ℓ Pt).denote :=
    ((s, tier2GsEnc Pt d), kemSessionTrackTier2Enc ℓ (kemTrackEnc (bridgeToRefTrack tr), hw))
  let ρ₀ : Env (S := ASig) [t0] := .cons (st₁Val, (partyEnc Q, (m₀, (m₁, optR)))) .nil
  have hpres : SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m st₁Val (gs, (tr, hw)) :=
    ⟨⟨d, rfl, hrel⟩, hinv, rfl, hkem, hhw⟩
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1.1 ∧
        SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 (r₂.1.2, r₂.2))
    ((spkChArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval ρ₀)
    (liftM (((challRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, m₀, m₁, optR)).run gs).run (tr, hw)))
  have hguard :
      (orE (.not (sendOKTier2E (.snd (.fst (.fst .v0))) (.fst (.snd .v0))))
        (gsWinTier2E (.snd (.fst (.fst .v0)))) : Expr AOps [t0] .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.snd (.fst (.fst .v0))) (.fst (.snd .v0))) :
        Expr AOps [t0] .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]
      rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [spkChArmHaltedTier2C, comp_eval_ite, hguard]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret,
      challRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind, hok,
      StateT.run_pure, liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, hpres⟩
    rw [pair_ev, eval_tier2SmRWireE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  | true =>
    cases hwin : gs.win with
    | true =>
      simp only [Bool.not_true, Bool.false_or, ↓reduceIte, comp_eval_ret,
        challRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind, hok, hwin]
      refine OracleCompRel.pureP ⟨?_, hpres⟩
      rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    | false =>
      simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      have hcallow : ∀ t, cfg.base.challAllowedIn t = true := by rw [← hcfg]; intro _; rfl
      have hcmsg : ∀ t, cfg.base.challMsg t = none := by rw [← hcfg]; intro _; rfl
      have hrhs :
          (liftM (((challRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep cfg
              (Q, m₀, m₁, optR)).run gs).run (tr, hw)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _) =
          (liftM (samIfNec optR) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 512 × Bool)) >>=
            fun ⟨coins, bad⟩ =>
              (liftM ((match gs.epMgmt 3 qep Q bad with
                | none => pure ((none, gs), (tr, hw))
                | some gs₁ =>
                  if !(gs₁.safeCh 3 Q) then
                    pure ((none, gs), (tr, hw))
                  else
                    let tr' := stepKemFailSend C.F K tr Q coins
                    if tr'.cand.isSome then
                      pure ((none, gs), ({ tr with cand := tr'.cand }, hw))
                    else
                      let mCh := if gs.b then m₁ else m₀
                      let out := (sessionSchemeU P ℓ).send (gs₁.st Q) mCh coins
                      pure ((some out.2,
                        gs₁.record 3 Q out.1 ⟨⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩, mCh, out.2⟩ true),
                        (tr', (out.2, Q) :: hw))) : ProbComp _) :
                OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _) := by
        simp only [challRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind,
          hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwin,
          stateT_lift_prob_run2, bind_assoc, liftM_prob_bind]
        refine bind_congr fun ⟨coins, bad⟩ => ?_
        cases hep : gs.epMgmt 3 qep Q bad with
        | none => rfl
        | some gs₁ =>
          dsimp only
          simp only [hcallow, Bool.not_true, Bool.or_false, hcmsg, Option.getD_none]
          by_cases hsc' : gs₁.safeCh 3 Q
          · simp only [hsc', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, stateT_lift_get_run2, pure_bind]
            split_ifs <;> simp_all [StateT.run_set, StateT.run_lift]
          · simp [hsc']
      rw [hrhs, comp_eval_bind, samIfNec512Tier2C_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
      have hoptR : (Expr.snd (.snd (.snd (.snd (Expr.v0 (O := AOps))))) :
          Expr AOps [t0] (.opt BV512)).eval ρ₀ = optR := rfl
      rw [hoptR]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      dsimp only
      let ρ₁ : Env (S := ASig) [.prod BV512 .bool, t0] := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) : Expr AOps [.prod BV512 .bool, t0] .bool).eval ρ₁ =
          bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, hpres⟩
          rw [pair_ev, eval_tier2SmRWireE, none_ev]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
        | some d₁ =>
          simp [hep_gs, hep_d] at hep_none
      | some gs₁ =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp [hep_gs, hep_d] at hep_none
        | some d₁ =>
          have hrel₁ : Tier2GsRel ℓ gs₁ d₁ := hep_rel gs₁ d₁ hep_gs hep_d
          have hinv₁ : ∀ Q', PartyReachInv C K (gs₁.st Q') := by
            intro Q'; rw [epMgmt_st_eq hep_gs]; exact hinv Q'
          simp only [Option.map_some]
          let ρ₂ : Env (S := ASig) [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
            .cons (tier2GsEnc Pt d₁) ρ₁
          have hsafe :
              (Expr.not (safeChTier2E 3 .v0 (.fst (.snd .v2))) :
                Expr AOps _ .bool).eval ρ₂ = !(gs₁.safeCh 3 Q) := by
            dsimp only [Expr.eval]
            rw [eval_safeChTier2E 3 _ _ ρ₂ d₁ Q rfl rfl, hrel₁.safeCh_eq 3 Q]
          rw [comp_eval_ite, hsafe]
          cases hsc : gs₁.safeCh 3 Q with
          | false =>
            simp only [Bool.not_false, ↓reduceIte, liftM_prob_pure, comp_eval_ret]
            refine OracleCompRel.pureP ⟨?_, hpres⟩
            rw [pair_ev, eval_tier2SmRWireE, none_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            have hkf := stepKemFailSendTier2C_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (I := PrfI)
              (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.fst .v1) ρ₂
              (kemTrackEnc (bridgeToRefTrack tr)) Q coins rfl
              (partyToBool_eq_partyEnc Q).symm rfl (hkem.bOk Q)
            rw [comp_eval_bind, hkf, pure_bind]
            let trS' := simStepKemFailSend C.F K (kemTrackEnc (bridgeToRefTrack tr)) Q coins
            let outKf : (Ty.prod (S := ASig) .bool (kemTrackTier2T ℓ Pt)).denote :=
              (trS'.cand.isSome,
               if trS'.cand.isSome then
                 kemTrackTier2Enc { kemTrackEnc (bridgeToRefTrack tr) with cand := trS'.cand }
               else kemTrackTier2Enc trS')
            let ρ₃ : Env (S := ASig)
                [.prod .bool (kemTrackTier2T ℓ Pt), tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
              .cons outKf ρ₂
            have hcand_eq : trS'.cand.isSome = (stepKemFailSend C.F K tr Q coins).cand.isSome := by
              dsimp only [trS']
              rw [simStepKemFailSend_kemTrackEnc, ← bridgeToRefTrack_stepSend]
              rfl
            have hfst3 : (Expr.fst (Expr.v0 (O := AOps)) : Expr AOps _ .bool).eval ρ₃ =
                (stepKemFailSend C.F K tr Q coins).cand.isSome := hcand_eq
            rw [comp_eval_ite, hfst3]
            cases hcand : (stepKemFailSend C.F K tr Q coins).cand.isSome with
            | true =>
              simp only [↓reduceIte, comp_eval_ret, liftM_prob_pure]
              refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv, ?_, ?_, hhw⟩
              · rw [pair_ev, eval_tier2SmRWireE, none_ev]
                exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
              · rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev]
                have hv0s : (Expr.snd (Expr.v0 (O := AOps))).eval ρ₃ =
                    kemTrackTier2Enc (Pt := Pt)
                      (kemTrackEnc (bridgeToRefTrack
                        { tr with cand := (stepKemFailSend C.F K tr Q coins).cand })) := by
                  change outKf.2 = _
                  dsimp only [outKf]
                  rw [hcand_eq, hcand]
                  simp only [↓reduceIte]
                  rw [kemTrackEnc_cand_latch]
                rw [hv0s]
                rfl
              · rw [← kemTrackEnc_cand_latch]
                exact hkem.withCand _
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, liftM_prob_pure]
              let mCh := if gs.b then m₁ else m₀
              have hmCh3 :
                  (Expr.ite (gsBTier2E (.snd (.fst (.fst .v3))))
                    (.fst (.snd (.snd (.snd .v3))))
                    (.fst (.snd (.snd .v3))) : Expr AOps _ PlainT).eval ρ₃ = mCh := by
                rw [ite_ev, eval_gsBTier2E _ ρ₃ d rfl, hrel.h_b]
                rfl
              have hinp :
                  (Expr.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3)))
                    (.pair
                      (.ite (gsBTier2E (.snd (.fst (.fst .v3))))
                        (.fst (.snd (.snd (.snd .v3))))
                        (.fst (.snd (.snd .v3))))
                      (.fst .v2)) :
                    Expr AOps _ (.prod GhostStT (.prod PlainT BV512))).eval ρ₃ =
                  (gs₁.st Q, (mCh, coins)) := by
                rw [pair_ev, eval_pGet_gsStTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_st, pair_ev, hmCh3]
                rfl
              rw [comp_eval_bind,
                drSendCoinsTier2C_eval C K Dh encPt encT decT lam idA idB _ ρ₃
                  (gs₁.st Q) mCh coins hinp (hinv₁ Q),
                pure_bind, comp_eval_ret]
              let out := (sessionSchemeU P ℓ).send (gs₁.st Q) mCh coins
              let ρ₄ : Env (S := ASig)
                  [.prod GhostStT (B 32), .prod .bool (kemTrackTier2T ℓ Pt),
                   tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
                .cons out ρ₃
              let p0 : Pos := ⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩
              have hmCh4 :
                  (Expr.ite (gsBTier2E (.snd (.fst (.fst .v4))))
                    (.fst (.snd (.snd (.snd .v4))))
                    (.fst (.snd (.snd .v4))) : Expr AOps _ PlainT).eval ρ₄ = mCh := by
                rw [ite_ev, eval_gsBTier2E _ ρ₄ d rfl, hrel.h_b]
                rfl
              have hposE :
                  (Expr.pair (.fst (.snd .v4))
                    (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
                      (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))) :
                    Expr AOps _ posTy).eval ρ₄ = posEnc p0 := by
                rw [pair_ev, pair_ev, eval_pGet_gsEpochTier2E _ _ ρ₄ d₁ Q rfl rfl, hrel₁.h_epoch]
                change (partyEnc Q, (gs₁.epoch Q,
                  (pGet (gsIdxTier2E .v2) (.fst (.snd .v4)) : Expr AOps _ .nat).eval ρ₄ + 1)) =
                  posEnc p0
                rw [eval_pGet_gsIdxTier2E _ _ ρ₄ d₁ Q rfl rfl, hrel₁.h_idx]
                rfl
              have hrecE :
                  (tier2RecMk
                    (.pair (.fst (.snd .v4))
                      (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
                        (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))))
                    (.ite (gsBTier2E (.snd (.fst (.fst .v4))))
                      (.fst (.snd (.snd (.snd .v4))))
                      (.fst (.snd (.snd .v4))))
                    (.snd .v0) :
                    Expr AOps _ (tier2RecTy ℓ Pt)).eval ρ₄ =
                  tier2RecEnc ⟨p0, mCh, out.2⟩ := by
                rw [eval_tier2RecMk _ _ _ ρ₄ p0 hposE, hmCh4]
                rfl
              have hrecGs := eval_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh)
                (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) 3
                .v2 (.fst (.snd .v4)) (.fst .v0)
                (tier2RecMk
                  (.pair (.fst (.snd .v4))
                    (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
                      (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))))
                  (.ite (gsBTier2E (.snd (.fst (.fst .v4))))
                    (.fst (.snd (.snd (.snd .v4))))
                    (.fst (.snd (.snd .v4))))
                  (.snd .v0))
                (.bool true) ρ₄ d₁ Q ⟨p0, mCh, out.2⟩ rfl rfl hrecE
              have hhw2 := recordHonestWireTier2E_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (.snd (.snd (.fst .v4))) (.snd .v0) (.fst (.snd .v4)) ρ₄ hw out.2 Q
                rfl rfl (partyToBool_eq_partyEnc Q).symm
              have hlen_out := sessionSchemeU_send_wire_length_le C K idA idB (gs₁.st Q) mCh coins
              refine OracleCompRel.pureP ⟨?_,
                ⟨d₁.record 3 Q out.1 ⟨p0, mCh, out.2⟩ true, ?_,
                  tier2GsRel_record_preserves hrel₁ 3 Q out.1 ⟨p0, mCh, out.2⟩ true rfl hlen_out⟩,
                partyReachInv_record C K hinv₁ 3 Q
                  (Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_send
                    C K (P := P) rfl (hinv₁ Q) mCh.toList coins) ⟨p0, mCh, out.2⟩ true,
                ?_, ?_, ?_⟩
              · rw [pair_ev, eval_tier2SmRWireE, some_ev]
                exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some out.2)
              · rw [pair_ev]; dsimp only; rw [pair_ev, pair_ev, hrecGs]
                rfl
              · rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev]; dsimp only [Prod.snd]; rw [pair_ev, hhw2]
                have hv1s : (Expr.snd (Expr.v1 (O := AOps))).eval ρ₄ =
                    kemTrackTier2Enc (Pt := Pt)
                      (kemTrackEnc (bridgeToRefTrack (stepKemFailSend C.F K tr Q coins))) := by
                  change outKf.2 = _
                  dsimp only [outKf]
                  rw [hcand_eq, hcand]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  dsimp only [trS']
                  rw [simStepKemFailSend_kemTrackEnc, ← bridgeToRefTrack_stepSend]
                rw [hv1s]
                rfl
              · rw [bridgeToRefTrack_stepSend, ← simStepKemFailSend_kemTrackEnc]
                exact kemTrackTier2Inv_stepSendSim C.F K _ Q coins hkem
              · intro wp hwp
                rcases List.mem_cons.mp hwp with rfl | hwp'
                · exact hlen_out
                · exact hhw wp hwp'

end HaltedTier2

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Step
