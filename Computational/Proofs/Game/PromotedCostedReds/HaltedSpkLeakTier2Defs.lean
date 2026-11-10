/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2 -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.E2E.Dsl.SmReachInvParty
public import Computational.Proofs.E2E.Dsl.SpqrSim -- proof-setup: allow-public-import

/-!
# Tier-2 Tracker-Halted `spkLeakRed` Step Definitions and Bounds

Defines the table-backed state `spkHaltedTier2StTy`, initializer `spkInitHaltedTier2C`, and
5-arm handler `spkStepHaltedTier2C` for `spkLeakRedHaltedTier2`, together with query, cost, and
size bounds.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Defs

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Env Ops Iface Expr Comp CostedReduction UniformSamplerTag bits
  bits_mono reductionSizeBudget atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfIface e2eSessionCodec BV256 BV512 PtT PK GhostStT PlainT B smQT smRT recvResultT
  bind_congr_of_mem_support')
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec)
open CryptoGames.Ratchet (expandPRG)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Pos samIfNec posTy posSender posEpoch posIdx maxN maxOptE sendsInE orE boolEq
  isSomeE otherE pGet pSet Record RecvResult GameState MakesAtMostQueries partyEnc posEnc
  orE_eval boolEq_eval isSomeE_eval)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey GhostState maxForwardJumps)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes SpkLeakRedProg spkTier2Budget paramsIdsWithSpqr
  sessionSchemeFixedSpk sessionSchemeU configRefuseEarlyBobCorr liftSpkGameM initAOracle
  deliverSpk injectSpk)
open CryptoVerification.E2E.Costed (e2eSig e2eOps gRedBounded_of_bounds recvResultEnc)
open Computational.Proofs.E2E.HaltedSpkDefs (spkLeakRedTrackHalted)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_cost drSendC_eval)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (drSendC_spqr_size_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (zeroPqxdhPrims sessGroupOp eval_sessGroupOp cost_sessGroupOp sessCurveOp
   atomicDraw256 atomicDraw256_eval atomicDraw256_cost
   atomicDraw512 atomicDraw512_eval atomicDraw512_cost
   liftTy liftExpr liftEnv liftExpr_eval coinE2EIface liftCompCoins liftCompCoins_queries_zero
   liftCompCoins_eval wk1Expr wk1Expr_cost wk1Expr_eval wk1Comp wk1Comp_queries wk1Comp_cost
   wk1Comp_eval drRecvAtomicOutT)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (letE_eval comp_eval_ret comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt
   comp_eval_caseSum isQueryBoundP_of_makesAtMostQueries bits_succ_le
   liftExpr_size_le liftCompCoins_size_le wk1Expr_size wk1Comp_size
   session_cost_le_ratchetCostBudget dummyBoolSessionRed dummyBoolSessionRed_totalQueries
   dummyBoolSessionRed_totalCost_le dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys
  (cost_spkWireKeyE_of_lt size_spkWireKeyE_of_lt)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (Tier2Gs Tier2GsRel)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase
  (tier2RecvRejE tier2RecvAccE tier2SmRWireE tier2SmRRecvE tier2SmRCorrE
   cost_tier2RecvRejE cost_tier2RecvAccE cost_tier2SmRWireE cost_tier2SmRRecvE cost_tier2SmRCorrE
   tier2RecTy tier2RecPos tier2RecCt tier2RecMk cost_tier2RecMk
   tier2GsTy gsStTier2E gsBTier2E gsWinTier2E gsEpochTier2E gsIdxTier2E gsTLTier2E gsMaxAccTier2E
   gsNextIdTier2E gsHeadTblTier2E gsNodeRecTier2E gsNodeKeyTier2E gsNodePrevTier2E gsNodeNextTier2E
   gsPosNodeTier2E gsChallTblTier2E gsChallCountTier2E gsCompTblTier2E gsUncompCountTier2E
   tbl1GetE cost_tbl1GetE tbl1SetE cost_tbl1SetE posTblGetE posTblSetE cost_posTblSetE leakTier2E
   initGsTier2E cost_initGsTier2E setWinTier2E cost_setWinTier2E
   safeChTier2E cost_safeChTier2E safeInjTier2E cost_safeInjTier2E
   epMgmtTier2E cost_epMgmtTier2E gsChallTier2E cost_gsChallTier2E
   trivialTier2E cost_trivialTier2E corrAllowedTier2E cost_corrAllowedTier2E
   afterCorrAllowedTier2E cost_afterCorrAllowedTier2E
   inWindowTier2E cost_inWindowTier2E sendOKTier2E cost_sendOKTier2E corrOKTier2E cost_corrOKTier2E)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping
  (deleteCiphertextTier2E acceptCiphertextTier2E cost_acceptCiphertextTier2E
   inTransitTier2E cost_inTransitTier2E recordCiphertextTier2E spk_totalCost_le_spkTier2Budget)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2
  (kemTrackTier2T honestWiresTier2T kemSessionTrackTier2T
   initKemFailSessionTrackTier2E initKemFailSessionTrackTier2E_cost_le initKemFailSessionTrackTier2E_size_le
   stepKemFailSendTier2C stepKemFailSendTier2C_queries_zero stepKemFailSendTier2C_cost_le stepKemFailSendTier2C_size_le
   recordHonestWireTier2E recordHonestWireTier2E_cost_le recordHonestWireTier2E_size_le
   findRevHonestWireIdxTier2E findRevHonestWireIdxTier2E_cost_le findRevHonestWireIdxTier2E_size_le
   kemOnDeliverPostTier2E kemOnDeliverPostTier2E_cost_le kemOnDeliverPostTier2E_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
  (spkInitArgT spkInitGsE2EE cost_spkInitGsE2EE size_spkInitGsE2EE
   receiveSpkAtomicC receiveSpkAtomicC_queries receiveSpkAtomicC_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
  (liftExpr_cost_exact liftCompCoins_cost_exact drReceiveAtomicC_cost_exact)

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

abbrev spkHaltedTier2StTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod BV256 (tier2GsTy ℓ Pt)) (kemSessionTrackTier2T ℓ Pt)

@[expose] def samIfNec512Tier2C {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) :
    Comp AOps PrfI Γ (.prod BV512 .bool) :=
  .caseOpt optR
    (.bind (atomicDraw512 (I := PrfI) rfl) (.ret (.pair .v0 (.bool false))))
    (.ret (.pair .v0 (.bool true)))

private theorem samIfNec512Tier2C_queries {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [samIfNec512Tier2C, Comp.queries]

private theorem samIfNec512Tier2C_cost {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).cost ≤ optR.cost + 12 := by
  simp only [samIfNec512Tier2C, Comp.cost, Expr.cost, Expr.v0, atomicDraw512_cost]; omega

private theorem atomicDraw256_size {O0 : Ops (atomicSig ℓ Pt)} {ι : Type}
    {T : OracleSpec ι} {I0 : Iface (atomicSig ℓ Pt) T} (h : I0.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw256 (O := O0) (I := I0) h (Γ := Γ)).size = 2 := by
  rcases I0 with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h; subst h; rfl

private theorem atomicDraw512_size {O0 : Ops (atomicSig ℓ Pt)} {ι : Type}
    {T : OracleSpec ι} {I0 : Iface (atomicSig ℓ Pt) T} (h : I0.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw512 (O := O0) (I := I0) h (Γ := Γ)).size = 2 := by
  rcases I0 with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h; subst h; rfl

private theorem samIfNec512Tier2C_size {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).size ≤ optR.size + 12 := by
  simp only [samIfNec512Tier2C, Comp.size, Expr.size, Expr.v0, atomicDraw512_size]; omega

@[expose] def ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    Expr AOps Γ .bool :=
  sessCurveOp .checkRatchetKeyOnCurve cE

private theorem cost_ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (ratchetKeyAdmissibleTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost = cE.cost + (ℓ / 32 + 24) := rfl

private theorem size_ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (ratchetKeyAdmissibleTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).size = cE.size + 1 := rfl

@[expose] def drSendCoinsTier2C {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    Comp AOps PrfI Γ (.prod GhostStT (B 32)) :=
  .bind (.ret inpE)
    (wk1Comp (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
      (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
        (Γ := [.prod CryptoVerification.E2E.Costed.GhostStT
          (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)]) .v0)))

private theorem drSendCoinsTier2C_queries {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendCoinsTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [drSendCoinsTier2C, wk1Comp_queries, liftCompCoins_queries_zero, Comp.queries]

private theorem noKemKeyGenComp_drSendC_v0 :
    SpkHop2RInProg.NoKemKeyGenComp
      (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
        (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
          (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
            Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0) =
      true := by
  dsimp only [drSendC, spqrDslHooks,
    Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE]
  cases CryptoVerification.E2E.serializedPartyAddresses
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A <;>
  cases CryptoVerification.E2E.serializedPartyAddresses
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B <;>
  rfl

private theorem drSendCoinsTier2C_cost {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendCoinsTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).cost ≤ inpE.cost + 67815 + 10 * (ℓ / 32 + 1) := by
  have h1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0)
    (noKemKeyGenComp_drSendC_v0 (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (encT := encT) (decT := decT))
  have h2 := drSendC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
    (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0
  have h12 : (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
      (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
        (Γ := [.prod CryptoVerification.E2E.Costed.GhostStT
          (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)])
        .v0)).cost ≤ 67810 + 10 * (ℓ / 32 + 1) :=
    (h1.trans h2).trans (by simp [Expr.v0, Expr.cost])
  simp only [drSendCoinsTier2C, wk1Comp_cost, Comp.cost]; omega

private theorem drSendCoinsTier2C_size {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendCoinsTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).size ≤ inpE.size + 620010 := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)
  let cE2E := drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
    (Γ := [tInp]) .v0
  have h1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl cE2E
  have h2 := drSendC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (coinE2EIface (ℓ := ℓ) PrfI) (.v0 : Expr EOps [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.size, Expr.v0] at h2
  simp only [drSendCoinsTier2C, wk1Comp_size, Comp.size, Expr.v0] at h1 h2 ⊢; omega

private theorem receiveSpkAtomicC_cost_tier2 {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 5105000 + 9 * (ℓ / 32 + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  have hsk := SpkLeakRedRInProg.cost_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.fst (.snd (.snd .v0)) : Expr AOps (t0 :: Γ) (B 32))
  have hprep := SpkLeakRedRInProg.cost_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)) :
      Expr AOps (BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod PK (.prod BV256 BV256))))
  have hdr1 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
      Expr AOps (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hdr2 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
      Expr AOps (t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hb0 : bits 0 = 1 := by decide
  dsimp only [receiveSpkAtomicC]
  simp only [SpkLeakRedRInProg.cost_sPureOp, SpkLeakRedRInProg.cost_sGroupOp,
    extractPtPrfIface, atomicPrfIface, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    _root_.ReductionDsl.AtomicPureOp.cost, _root_.ReductionDsl.AtomicGroupOp.cost, hb0]
    at hsk hprep hdr1 hdr2 ⊢
  omega

@[expose] def spkInitHaltedTier2C :
    Comp AOps PrfI [BV256] (.prod .unit (spkHaltedTier2StTy ℓ Pt)) :=
  .bind (Comp.sample (I := PrfI) UniformSamplerTag.bool .unit)
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind (atomicDraw256 (I := PrfI) rfl)
        (.bind (atomicDraw256 (I := PrfI) rfl)
          (.bind
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
                   (encT := encT) (decT := decT) (lam := lam) .v1))))))))

theorem spkInitHaltedTier2C_queries :
    (spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkInitHaltedTier2C, atomicDraw256, Comp.queries]

theorem spkInitHaltedTier2C_cost :
    (spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).cost ≤ 75000 := by
  let Γ₅ : List (Ty ASig) := [BV256, BV256, BV256, BV256, .bool, BV256]
  let Γ₆ : List (Ty ASig) := .prod .bool (.prod GhostStT GhostStT) :: Γ₅
  let eGs := liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) rfl
  have hwk : (wk1Expr (Γ := Γ₅) eGs).cost = eGs.cost := wk1Expr_cost eGs
  have hgsE := cost_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  have hgs2 := cost_initGsTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₆)
    (.fst (.snd .v0)) (.snd (.snd .v0)) (.fst .v0)
  have htrk := initKemFailSessionTrackTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps Γ₅ BV256)
  dsimp only [spkInitHaltedTier2C, sessGroupOp]
  dsimp only [eGs] at hwk
  simp only [extractPtPrfIface, atomicPrfIface,
    atomicSamplers, _root_.ReductionDsl.unifSamplers, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    atomicDraw256_cost] at hl hgs2 htrk ⊢
  change _ ≤ 75000
  have hd : (AOps).cost (.inl (.inl (.inr .ptBase))) =
      _root_.ReductionDsl.AtomicGroupOp.cost .ptBase := rfl
  have he : (AOps).cost (.inl (.inl (.inr .ptDh))) =
      _root_.ReductionDsl.AtomicGroupOp.cost .ptDh := rfl
  have hf : (AOps).cost (.inl (.inl (.inr .rootExpandPrg))) =
      _root_.ReductionDsl.AtomicGroupOp.cost .rootExpandPrg := rfl
  dsimp only [_root_.ReductionDsl.AtomicGroupOp.cost] at hd he hf
  omega

theorem spkInitHaltedTier2C_size :
    (spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).size ≤ 6500 := by
  let Γ₅ : List (Ty ASig) := [BV256, BV256, BV256, BV256, .bool, BV256]
  let eGs := liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hwk : (wk1Expr (Γ := Γ₅) eGs).size = eGs.size := wk1Expr_size eGs
  have hgsE := size_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  have htrk := initKemFailSessionTrackTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps Γ₅ BV256)
  dsimp only [spkInitHaltedTier2C, initGsTier2E]
  dsimp only [eGs] at hwk
  have hd : (AOps).opSize (.inl (.inl (.inr .ptBase))) = 0 := rfl
  have he : (AOps).opSize (.inl (.inl (.inr .ptDh))) = 0 := rfl
  have hf : (AOps).opSize (.inl (.inl (.inr .rootExpandPrg))) = 0 := rfl
  simp only [Comp.size, Expr.size, atomicDraw256_size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    show bits 0 = 1 from rfl, show bits 1 = 1 from rfl] at hl htrk ⊢
  generalize (initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.var (.succ .zero) : Expr AOps Γ₅ BV256)).size = szT at htrk ⊢
  omega

@[expose] def spkTrArmHaltedTier2C (qep : ℕ) :
    Comp AOps PrfI
      [.prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))]
      (.prod (smRT GhostStT) (spkHaltedTier2StTy ℓ Pt)) :=
  let stH0 := Expr.fst .v0
  let gs0 := Expr.snd (.fst stH0)
  let p0 := Expr.fst (.snd .v0)
  let optR0 := Expr.snd (.snd (.snd .v0))
  .ite (orE (.not (sendOKTier2E gs0 p0)) (gsWinTier2E gs0))
    (.ret (.pair (tier2SmRWireE .none) stH0))
    (.bind (samIfNec512Tier2C C K Dh encPt encT decT lam optR0)
      (.caseOpt (epMgmtTier2E 3 qep (.snd (.fst (.fst .v1))) (.fst (.snd .v1)) (.snd .v0))
        (.ret (.pair (tier2SmRWireE .none) (.fst .v1)))
        (.bind
          (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (I := PrfI)
            (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.fst .v1))
          (.ite (.fst .v0)
            (.ret (.pair (tier2SmRWireE .none)
              (.pair (.fst (.fst .v3)) (.pair (.snd .v0) (.snd (.snd (.fst .v3)))))))
            (.bind
              (drSendCoinsTier2C C K Dh encPt encT decT lam
                (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3)))
                  (.pair (.fst (.snd (.snd .v3))) (.fst .v2))))
              (let st' : Expr AOps _ GhostStT := .fst .v0
               let ct' : Expr AOps _ (B 32) := .snd .v0
               let trOut : Expr AOps _ (kemTrackTier2T ℓ Pt) := .snd .v1
               let gs1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v2
               let stH4 : Expr AOps _ (spkHaltedTier2StTy ℓ Pt) := .fst .v4
               let s4 : Expr AOps _ BV256 := .fst (.fst stH4)
               let hw4 : Expr AOps _ (honestWiresTier2T ℓ Pt) := .snd (.snd stH4)
               let p4 : Expr AOps _ .bool := .fst (.snd .v4)
               let m4 : Expr AOps _ PlainT := .fst (.snd (.snd .v4))
               let posE : Expr AOps _ posTy :=
                 .pair p4 (.pair (pGet (gsEpochTier2E gs1) p4)
                   (.add (pGet (gsIdxTier2E gs1) p4) (.nat 1)))
               let gs2 : Expr AOps _ (tier2GsTy ℓ Pt) :=
                 recordCiphertextTier2E 3 gs1 p4 st' (tier2RecMk posE m4 ct') (.bool false)
               let hw2 : Expr AOps _ (honestWiresTier2T ℓ Pt) :=
                 recordHonestWireTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam) hw4 ct' p4
               .ret (.pair (tier2SmRWireE (.some ct'))
                 (.pair (.pair s4 gs2) (.pair trOut hw2)))))))))

@[expose] def spkChArmHaltedTier2C (qep : ℕ) :
    Comp AOps PrfI
      [.prod (spkHaltedTier2StTy ℓ Pt)
        (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))]
      (.prod (smRT GhostStT) (spkHaltedTier2StTy ℓ Pt)) :=
  let stH0 := Expr.fst .v0
  let gs0 := Expr.snd (.fst stH0)
  let p0 := Expr.fst (.snd .v0)
  let optR0 := Expr.snd (.snd (.snd (.snd .v0)))
  .ite (orE (.not (sendOKTier2E gs0 p0)) (gsWinTier2E gs0))
    (.ret (.pair (tier2SmRWireE .none) stH0))
    (.bind (samIfNec512Tier2C C K Dh encPt encT decT lam optR0)
      (.caseOpt (epMgmtTier2E 3 qep (.snd (.fst (.fst .v1))) (.fst (.snd .v1)) (.snd .v0))
        (.ret (.pair (tier2SmRWireE .none) (.fst .v1)))
        (.ite (.not (safeChTier2E 3 .v0 (.fst (.snd .v2))))
          (.ret (.pair (tier2SmRWireE .none) (.fst .v2)))
          (.bind
            (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (I := PrfI)
              (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.fst .v1))
            (.ite (.fst .v0)
              (.ret (.pair (tier2SmRWireE .none)
                (.pair (.fst (.fst .v3)) (.pair (.snd .v0) (.snd (.snd (.fst .v3)))))))
              (let mCh3 : Expr AOps _ PlainT :=
                 .ite (gsBTier2E (.snd (.fst (.fst .v3))))
                   (.fst (.snd (.snd (.snd .v3))))
                   (.fst (.snd (.snd .v3)))
               .bind
                 (drSendCoinsTier2C C K Dh encPt encT decT lam
                   (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3))) (.pair mCh3 (.fst .v2))))
                 (let st' : Expr AOps _ GhostStT := .fst .v0
                  let ct' : Expr AOps _ (B 32) := .snd .v0
                  let trOut : Expr AOps _ (kemTrackTier2T ℓ Pt) := .snd .v1
                  let gs1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v2
                  let stH4 : Expr AOps _ (spkHaltedTier2StTy ℓ Pt) := .fst .v4
                  let s4 : Expr AOps _ BV256 := .fst (.fst stH4)
                  let gsOrig4 : Expr AOps _ (tier2GsTy ℓ Pt) := .snd (.fst stH4)
                  let hw4 : Expr AOps _ (honestWiresTier2T ℓ Pt) := .snd (.snd stH4)
                  let p4 : Expr AOps _ .bool := .fst (.snd .v4)
                  let mCh4 : Expr AOps _ PlainT :=
                    .ite (gsBTier2E gsOrig4)
                      (.fst (.snd (.snd (.snd .v4))))
                      (.fst (.snd (.snd .v4)))
                  let posE : Expr AOps _ posTy :=
                    .pair p4 (.pair (pGet (gsEpochTier2E gs1) p4)
                      (.add (pGet (gsIdxTier2E gs1) p4) (.nat 1)))
                  let gs2 : Expr AOps _ (tier2GsTy ℓ Pt) :=
                    recordCiphertextTier2E 3 gs1 p4 st' (tier2RecMk posE mCh4 ct') (.bool true)
                  let hw2 : Expr AOps _ (honestWiresTier2T ℓ Pt) :=
                    recordHonestWireTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                      (encT := encT) (decT := decT) (lam := lam) hw4 ct' p4
                  .ret (.pair (tier2SmRWireE (.some ct'))
                    (.pair (.pair s4 gs2) (.pair trOut hw2))))))))))

@[expose] def spkDlArmHaltedTier2C :
    Comp AOps PrfI
      [.prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (B 32))]
      (.prod (smRT GhostStT) (spkHaltedTier2StTy ℓ Pt)) :=
  let stH0 := Expr.fst .v0
  let gs0 := Expr.snd (.fst stH0)
  let p0 := Expr.fst (.snd .v0)
  let c0 := Expr.snd (.snd .v0)
  .ite (gsWinTier2E gs0)
    (.ret (.pair (tier2SmRRecvE .none) stH0))
    (.caseOpt (inTransitTier2E gs0 (otherE p0) c0)
      (.ret (.pair (tier2SmRRecvE .none) (.fst .v0)))
      (.bind (atomicDraw256 (I := PrfI) rfl)
        (.bind
          (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam)
            (.fst (.fst (.fst .v2)))
            (pGet (gsStTier2E (.snd (.fst (.fst .v2)))) (.fst (.snd .v2)))
            (.snd (.snd .v2)) .v0)
          (.caseOpt .v0
            (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE)) (.fst .v3)))
            (let st' : Expr AOps _ GhostStT := .fst .v0
             let t' : Expr AOps _ .nat := .fst (.snd .v0)
             let i' : Expr AOps _ .nat := .fst (.snd (.snd .v0))
             let m' : Expr AOps _ PlainT := .snd (.snd (.snd .v0))
             let rPos : Expr AOps _ posTy := tier2RecPos .v3
             let stH4 : Expr AOps _ (spkHaltedTier2StTy ℓ Pt) := .fst .v4
             let s4 : Expr AOps _ BV256 := .fst (.fst stH4)
             let gs4 : Expr AOps _ (tier2GsTy ℓ Pt) := .snd (.fst stH4)
             let tr4 : Expr AOps _ (kemTrackTier2T ℓ Pt) := .fst (.snd stH4)
             let hw4 : Expr AOps _ (honestWiresTier2T ℓ Pt) := .snd (.snd stH4)
             let p4 : Expr AOps _ .bool := .fst (.snd .v4)
             let c4 : Expr AOps _ (B 32) := .snd (.snd .v4)
             let mOut : Expr AOps _ (.opt PlainT) :=
               .ite (gsChallTier2E gs4 rPos) .none (.some m')
             let rrAcc : Expr AOps _ (recvResultT (ℓ := ℓ) (Pt := Pt)) :=
               tier2RecvAccE t' i' mOut
             let jOpt : Expr AOps _ (.opt .nat) :=
               findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam) hw4 p4 c4
             let trOut : Expr AOps _ (kemTrackTier2T ℓ Pt) :=
               kemOnDeliverPostTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam) p4 jOpt (.some rrAcc) tr4
             .ret (.pair (tier2SmRRecvE (.some rrAcc))
               (.pair (.pair s4 (acceptCiphertextTier2E gs4 p4 st' rPos))
                 (.pair trOut hw4))))))))

@[expose] def spkIjArmHaltedTier2C (qep : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))]
      (.prod (smRT GhostStT) (.prod BV256 (tier2GsTy ℓ Pt))) :=
  let s0 : Expr AOps _ BV256 := .fst .v0
  let gs0 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst (.snd .v0)
  let p0 : Expr AOps _ .bool := .fst (.snd (.snd .v0))
  let c0 : Expr AOps _ (B 32) := .snd (.snd (.snd .v0))
  let refuseCond : Expr AOps _ .bool :=
    orE (gsWinTier2E gs0)
      (orE (isSomeE (inTransitTier2E gs0 (otherE p0) c0))
        (orE (.not (safeInjTier2E 3 gs0))
          (.not (ratchetKeyAdmissibleTier2E C K Dh encPt encT decT lam c0))))
  .ite refuseCond
    (.ret (.pair (tier2SmRRecvE .none) (.pair s0 gs0)))
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind
        (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam)
          (.fst .v1) (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1))))
          (.snd (.snd (.snd .v1))) .v0)
        (.caseOpt .v0
          (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
            (.pair (.fst .v2) (.fst (.snd .v2)))))
          (let st' : Expr AOps _ GhostStT := .fst .v0
           let t' : Expr AOps _ .nat := .fst (.snd .v0)
           let i' : Expr AOps _ .nat := .fst (.snd (.snd .v0))
           let m' : Expr AOps _ PlainT := .snd (.snd (.snd .v0))
           let s3 : Expr AOps _ BV256 := .fst .v3
           let gs3 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst (.snd .v3)
           let p3 : Expr AOps _ .bool := .fst (.snd (.snd .v3))
           .ite (.lt (.nat (qep + 1)) t')
             (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE)) (.pair s3 gs3)))
             (let posE : Expr AOps _ posTy := .pair (otherE p3) (.pair t' i')
              .ite (trivialTier2E 3 gs3 posE)
                (.ret (.pair (tier2SmRRecvE (.some (tier2RecvAccE t' i' (.some m'))))
                  (.pair s3 (acceptCiphertextTier2E gs3 p3 st' posE))))
                (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
                  (.pair s3 (setWinTier2E gs3 (.bool true))))))))))

@[expose] def spkCrArmHaltedTier2C :
    Comp AOps PrfI
      [.prod (tier2GsTy ℓ Pt) .bool]
      (.prod (smRT GhostStT) (tier2GsTy ℓ Pt)) :=
  let gs0 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst .v0
  let p0 : Expr AOps _ .bool := .snd .v0
  let refuseCond : Expr AOps _ .bool :=
    orE (gsWinTier2E gs0)
      (orE (.not (corrAllowedTier2E gs0 p0))
        (orE (inWindowTier2E gs0 p0) (.not (corrOKTier2E gs0 p0))))
  .ite refuseCond
    (.ret (.pair (tier2SmRCorrE .none) gs0))
    (.ret (.pair (tier2SmRCorrE (.some (pGet (gsStTier2E gs0) p0)))
      (afterCorrAllowedTier2E gs0 p0)))

/-- Combined 5-arm Tier-2 handler for `spkOracleImplTrackHalted`. -/
@[expose] def spkStepHaltedTier2C (qep : ℕ) :
    Comp AOps PrfI
      [spkHaltedTier2StTy ℓ Pt, smQT]
      (.prod (smRT GhostStT) (spkHaltedTier2StTy ℓ Pt)) :=
  .caseSum .v1
    (.bind (.ret (.pair .v1 .v0))
      (wk1Comp (spkTrArmHaltedTier2C C K Dh encPt encT decT lam qep)))
    (.caseSum .v0
      (.bind (.ret (.pair .v2 .v0))
        (wk1Comp (spkChArmHaltedTier2C C K Dh encPt encT decT lam qep)))
      (.caseSum .v0
        (.bind (.ret (.pair .v3 .v0))
          (wk1Comp (spkDlArmHaltedTier2C C K Dh encPt encT decT lam)))
        (.caseSum .v0
          (.bind (.ret (.pair (.fst (.fst .v4)) (.pair (.snd (.fst .v4)) .v0)))
            (.bind (wk1Comp (spkIjArmHaltedTier2C C K Dh encPt encT decT lam qep))
              (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v6))))))
          (.bind (.ret (.pair (.snd (.fst .v4)) .v0))
            (.bind (wk1Comp (spkCrArmHaltedTier2C C K Dh encPt encT decT lam))
              (.ret (.pair (.fst .v0) (.pair (.pair (.fst (.fst .v6)) (.snd .v0)) (.snd .v6)))))))))

theorem spkStepHaltedTier2C_queries (qep : ℕ) :
    (spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  unfold spkStepHaltedTier2C spkTrArmHaltedTier2C spkChArmHaltedTier2C
    spkDlArmHaltedTier2C spkIjArmHaltedTier2C spkCrArmHaltedTier2C
  simp [Comp.queries, wk1Comp_queries, samIfNec512Tier2C_queries,
    stepKemFailSendTier2C_queries_zero, drSendCoinsTier2C_queries, receiveSpkAtomicC_queries]

private theorem cost_recordCiphertextTier2E_three {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (sE : Expr AOps Γ (tier2GsTy ℓ Pt)) (pE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ GhostStT) (rE : Expr AOps Γ (tier2RecTy ℓ Pt)) (isChallE : Expr AOps Γ .bool) :
    (recordCiphertextTier2E 3 sE pE stE rE isChallE).cost ≤
      sE.cost + pE.cost + stE.cost + rE.cost + isChallE.cost + 30 * ℓ + 18500 := by
  let tIn : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT (.prod (tier2RecTy ℓ Pt) .bool)))
  let c0 : List (Ty ASig) := tIn :: Γ; let c1 : List (Ty ASig) := .nat :: c0
  have hwk := cost_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := c0) hℓ (tier2RecCt (.fst (.snd (.snd (.snd .v0)))))
  have hsc := cost_safeChTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := c1) 3 (.fst .v1) (.fst (.snd .v1))
  have htg := cost_tbl1GetE (O := AOps) (Γ := c1) (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0
  have hts := cost_tbl1SetE (O := AOps) (Γ := c1) (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0
    (gsNextIdTier2E (.fst .v1))
  have hp0 := cost_posTblSetE (O := AOps) (Γ := c1) (gsPosNodeTier2E (.fst .v1))
    (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (gsNextIdTier2E (.fst .v1))
  have hp1 := cost_posTblSetE (O := AOps) (Γ := c1) (gsChallTblTier2E (.fst .v1))
    (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
  have hp2 := cost_posTblSetE (O := AOps) (Γ := c1) (gsCompTblTier2E (.fst .v1))
    (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
  simp only [recordCiphertextTier2E, pSet, pGet, posIdx, tier2RecPos, tier2RecCt, gsStTier2E,
    gsEpochTier2E, gsIdxTier2E, gsNextIdTier2E, gsHeadTblTier2E, gsNodeRecTier2E, gsNodeKeyTier2E,
    gsNodePrevTier2E, gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E,
    gsCompTblTier2E, gsUncompCountTier2E, Expr.cost, Expr.v0, Expr.v1,
    show bits 0 = 1 from rfl, show bits 1 = 1 from rfl, show bits 3 = 2 from rfl]
    at hwk hsc htg hts hp0 hp1 hp2 ⊢
  omega

private theorem spkTrArmHaltedTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkTrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      1260000 + 61 * ℓ + 2 * bits qep := by
  let tRoot : Ty ASig := .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))
  let Γ₀ : List (Ty ASig) := [tRoot]; let Γ₁ : List (Ty ASig) := .prod BV512 .bool :: Γ₀
  let Γ₂ : List (Ty ASig) := tier2GsTy ℓ Pt :: Γ₁; let Γ₃ : List (Ty ASig) := .prod .bool (kemTrackTier2T ℓ Pt) :: Γ₂
  let Γ₄ : List (Ty ASig) := .prod GhostStT (B 32) :: Γ₃
  have hsok := cost_sendOKTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.snd (.fst (.fst .v0))) (.fst (.snd .v0))
  have hr0 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hsam := samIfNec512Tier2C_cost C K Dh encPt encT decT lam
    (.snd (.snd (.snd .v0)) : Expr AOps Γ₀ (.opt BV512))
  have hepm := cost_epMgmtTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) 3 qep
    (.snd (.fst (.fst .v1))) (.fst (.snd .v1)) (.snd .v0)
  have hr1 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) .none
  have hkf := stepKemFailSendTier2C_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := PrfI) (Γ := Γ₂)
    (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.fst .v1)
  have hr3 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) .none
  have hdr := drSendCoinsTier2C_cost C K Dh encPt encT decT lam
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3)))
      (.pair (.fst (.snd (.snd .v3))) (.fst .v2)) :
        Expr AOps Γ₃ (.prod GhostStT (.prod PlainT BV512)))
  let p4 : Expr AOps Γ₄ .bool := .fst (.snd .v4)
  let posE : Expr AOps Γ₄ posTy :=
    .pair p4 (.pair (pGet (gsEpochTier2E .v2) p4) (.add (pGet (gsIdxTier2E .v2) p4) (.nat 1)))
  have hrmk := cost_tier2RecMk (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄)
    posE (.fst (.snd (.snd .v4))) (.snd .v0)
  have hrec := cost_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ
    .v2 p4 (.fst .v0) (tier2RecMk posE (.fst (.snd (.snd .v4))) (.snd .v0)) (.bool false)
  have hhw := recordHonestWireTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₄) hℓ
    (.snd (.snd (.fst .v4))) (.snd .v0) p4
  have hr4 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) (.some (.snd .v0))
  have hb3 : bits 3 = 2 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [p4, posE] at hrmk hrec hhw
  simp only [spkTrArmHaltedTier2C, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    orE, pGet, gsWinTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E, hb3, hb1]
    at hsok hr0 hsam hepm hr1 hkf hr3 hdr hrmk hrec hhw hr4 ⊢
  rw [hrmk] at hrec
  rw [hr0, hr1, hr3, hr4]
  generalize (sendOKTier2E _ _).cost = csok at hsok ⊢
  generalize (samIfNec512Tier2C C K Dh encPt encT decT lam _).cost = csam at hsam ⊢
  generalize (epMgmtTier2E _ _ _ _ _).cost = cepm at hepm ⊢
  generalize (stepKemFailSendTier2C (Pt := Pt) (lam := lam) _ _ _).cost = ckf at hkf ⊢
  generalize (drSendCoinsTier2C C K Dh encPt encT decT lam _).cost = cdr at hdr ⊢
  generalize (recordCiphertextTier2E (Pt := Pt) (lam := lam) _ _ _ _ _ _).cost = crec at hrec ⊢
  generalize (recordHonestWireTier2E (Pt := Pt) (lam := lam) _ _ _).cost = chw at hhw ⊢
  omega

private theorem spkChArmHaltedTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkChArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      1260000 + 61 * ℓ + 2 * bits qep := by
  let tRoot : Ty ASig := .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let Γ₀ : List (Ty ASig) := [tRoot]; let Γ₁ : List (Ty ASig) := .prod BV512 .bool :: Γ₀
  let Γ₂ : List (Ty ASig) := tier2GsTy ℓ Pt :: Γ₁; let Γ₃ : List (Ty ASig) := .prod .bool (kemTrackTier2T ℓ Pt) :: Γ₂
  let Γ₄ : List (Ty ASig) := .prod GhostStT (B 32) :: Γ₃
  have hsok := cost_sendOKTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.snd (.fst (.fst .v0))) (.fst (.snd .v0))
  have hr0 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hsam := samIfNec512Tier2C_cost C K Dh encPt encT decT lam
    (.snd (.snd (.snd (.snd .v0))) : Expr AOps Γ₀ (.opt BV512))
  have hepm := cost_epMgmtTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) 3 qep
    (.snd (.fst (.fst .v1))) (.fst (.snd .v1)) (.snd .v0)
  have hr1 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) .none
  have hsch := cost_safeChTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₂) 3 .v0 (.fst (.snd .v2))
  have hr2 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₂) .none
  have hkf := stepKemFailSendTier2C_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := PrfI) (Γ := Γ₂)
    (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.fst .v1)
  have hr3 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) .none
  let mCh3 : Expr AOps Γ₃ PlainT :=
    .ite (gsBTier2E (.snd (.fst (.fst .v3)))) (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3)))
  have hdr := drSendCoinsTier2C_cost C K Dh encPt encT decT lam
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3))) (.pair mCh3 (.fst .v2)) :
      Expr AOps Γ₃ (.prod GhostStT (.prod PlainT BV512)))
  let p4 : Expr AOps Γ₄ .bool := .fst (.snd .v4)
  let mCh4 : Expr AOps Γ₄ PlainT :=
    .ite (gsBTier2E (.snd (.fst (.fst .v4)))) (.fst (.snd (.snd (.snd .v4)))) (.fst (.snd (.snd .v4)))
  let posE : Expr AOps Γ₄ posTy :=
    .pair p4 (.pair (pGet (gsEpochTier2E .v2) p4) (.add (pGet (gsIdxTier2E .v2) p4) (.nat 1)))
  have hrmk := cost_tier2RecMk (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) posE mCh4 (.snd .v0)
  have hrec := cost_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ
    .v2 p4 (.fst .v0) (tier2RecMk posE mCh4 (.snd .v0)) (.bool true)
  have hhw := recordHonestWireTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₄) hℓ
    (.snd (.snd (.fst .v4))) (.snd .v0) p4
  have hr4 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) (.some (.snd .v0))
  have hb3 : bits 3 = 2 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [mCh3, p4, mCh4, posE] at hdr hrmk hrec hhw
  simp only [spkChArmHaltedTier2C, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    orE, pGet, gsBTier2E, gsWinTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E, hb3, hb1]
    at hsok hr0 hsam hepm hr1 hsch hr2 hkf hr3 hdr hrmk hrec hhw hr4 ⊢
  rw [hrmk] at hrec
  rw [hr0, hr1, hr2, hr3, hr4]
  generalize (sendOKTier2E _ _).cost = csok at hsok ⊢
  generalize (samIfNec512Tier2C C K Dh encPt encT decT lam _).cost = csam at hsam ⊢
  generalize (epMgmtTier2E _ _ _ _ _).cost = cepm at hepm ⊢
  generalize (safeChTier2E _ _ _).cost = csch at hsch ⊢
  generalize (stepKemFailSendTier2C (Pt := Pt) (lam := lam) _ _ _).cost = ckf at hkf ⊢
  generalize (drSendCoinsTier2C C K Dh encPt encT decT lam _).cost = cdr at hdr ⊢
  generalize (recordCiphertextTier2E (Pt := Pt) (lam := lam) _ _ _ _ _ _).cost = crec at hrec ⊢
  generalize (recordHonestWireTier2E (Pt := Pt) (lam := lam) _ _ _).cost = chw at hhw ⊢
  omega

private theorem spkDlArmHaltedTier2C_cost (hℓ : ℓ < 10 ^ 6) :
    (spkDlArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤
      5150000 + 61 * ℓ := by
  let t0 : Ty ASig := .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (B 32))
  let Γ₀ : List (Ty ASig) := [t0]; let Γ₁ : List (Ty ASig) := tier2RecTy ℓ Pt :: Γ₀
  let Γ₂ : List (Ty ASig) := BV256 :: Γ₁; let Γ₃ : List (Ty ASig) := drRecvAtomicOutT ℓ Pt :: Γ₂
  let Γ₄ : List (Ty ASig) := .prod GhostStT (.prod .nat (.prod .nat PlainT)) :: Γ₃
  have hit := cost_inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) hℓ (.snd (.fst (.fst .v0))) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hr0 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hrcv := receiveSpkAtomicC_cost_tier2 C K Dh encPt encT decT lam
    (.fst (.fst (.fst .v2)) : Expr AOps Γ₂ BV256) (pGet (gsStTier2E (.snd (.fst (.fst .v2)))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0
  have hr3 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) (.some tier2RecvRejE)
  let t' : Expr AOps Γ₄ .nat := .fst (.snd .v0); let i' : Expr AOps Γ₄ .nat := .fst (.snd (.snd .v0))
  let m' : Expr AOps Γ₄ PlainT := .snd (.snd (.snd .v0)); let rPos : Expr AOps Γ₄ posTy := tier2RecPos .v3
  let gs4 : Expr AOps Γ₄ (tier2GsTy ℓ Pt) := .snd (.fst (.fst .v4)); let p4 : Expr AOps Γ₄ .bool := .fst (.snd .v4)
  let mOut : Expr AOps Γ₄ (.opt PlainT) := .ite (gsChallTier2E gs4 rPos) .none (.some m')
  let rrAcc : Expr AOps Γ₄ (recvResultT (ℓ := ℓ) (Pt := Pt)) := tier2RecvAccE t' i' mOut
  let jOpt : Expr AOps Γ₄ (.opt .nat) :=
    findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (.snd (.snd (.fst .v4))) p4 (.snd (.snd .v4))
  have hch := cost_gsChallTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) gs4 rPos
  have hacc := cost_acceptCiphertextTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄)
    gs4 p4 (.fst .v0) rPos
  have hra4 := cost_tier2RecvAccE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) t' i' mOut
  have hr4 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) (.some rrAcc)
  have hj := findRevHonestWireIdxTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₄) hℓ
    (.snd (.snd (.fst .v4))) p4 (.snd (.snd .v4))
  have hpost := kemOnDeliverPostTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₄)
    p4 jOpt (.some rrAcc) (.fst (.snd (.fst .v4)))
  dsimp only [t', i', m', rPos, gs4, p4, mOut, rrAcc, jOpt] at hch hacc hra4 hr4 hj hpost
  simp only [spkDlArmHaltedTier2C, Comp.cost, Expr.cost,
    Expr.v0, Expr.v2, Expr.v3, Expr.v4,
    otherE, pGet, gsWinTier2E, gsStTier2E, tier2RecPos, atomicDraw256_cost,
    cost_tier2RecvRejE] at hit hr0 hrcv hr3 hch hacc hra4 hr4 hj hpost ⊢
  rw [hr0, hr3, hr4]
  rw [hra4] at hpost ⊢
  generalize (inTransitTier2E (Pt := Pt) (lam := lam) _ _ _).cost = cit at hit ⊢
  generalize (receiveSpkAtomicC (Pt := Pt) (lam := lam) _ _ _ _).cost = crcv at hrcv ⊢
  generalize (gsChallTier2E _ _).cost = cch at hch hpost ⊢
  generalize (acceptCiphertextTier2E _ _ _ _).cost = cacc at hacc ⊢
  generalize (findRevHonestWireIdxTier2E (Pt := Pt) (lam := lam) _ _ _).cost = cj at hj hpost ⊢
  generalize (kemOnDeliverPostTier2E (Pt := Pt) (lam := lam) _ _ _ _).cost = cp at hpost ⊢
  omega

private theorem spkIjArmHaltedTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkIjArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      5125000 + 31 * ℓ + 2 * bits qep := by
  let t0 : Ty ASig := .prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))
  let Γ₀ : List (Ty ASig) := [t0]
  let Γ₁ : List (Ty ASig) := BV256 :: Γ₀
  let Γ₂ : List (Ty ASig) := drRecvAtomicOutT ℓ Pt :: Γ₁
  let Γ₃ : List (Ty ASig) := .prod GhostStT (.prod .nat (.prod .nat PlainT)) :: Γ₂
  have hit := cost_inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) hℓ
    (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hsi := cost_safeInjTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) 3 (.fst (.snd .v0))
  have hrka := cost_ratchetKeyAdmissibleTier2E C K Dh encPt encT decT lam
    (.snd (.snd (.snd .v0)) : Expr AOps Γ₀ (B 32))
  have hr0 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hrcv := receiveSpkAtomicC_cost_tier2 C K Dh encPt encT decT lam
    (.fst .v1 : Expr AOps Γ₁ BV256)
    (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1))))
    (.snd (.snd (.snd .v1))) .v0
  have hr2 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₂) (.some tier2RecvRejE)
  let t' : Expr AOps Γ₃ .nat := .fst (.snd .v0)
  let i' : Expr AOps Γ₃ .nat := .fst (.snd (.snd .v0))
  let m' : Expr AOps Γ₃ PlainT := .snd (.snd (.snd .v0))
  let gs3 : Expr AOps Γ₃ (tier2GsTy ℓ Pt) := .fst (.snd .v3)
  let p3 : Expr AOps Γ₃ .bool := .fst (.snd (.snd .v3))
  let posE : Expr AOps Γ₃ posTy := .pair (otherE p3) (.pair t' i')
  have hr3 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) (.some tier2RecvRejE)
  have htriv := cost_trivialTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) 3 gs3 posE
  have hacc := cost_acceptCiphertextTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃)
    gs3 p3 (.fst .v0) posE
  have hsw := cost_setWinTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) gs3 (.bool true)
  have hra3 := cost_tier2RecvAccE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) t' i' (.some m')
  have hr3a := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃)
    (.some (tier2RecvAccE t' i' (.some m')))
  have hbs := bits_succ_le qep
  have hb3 : bits 3 = 2 := by decide
  dsimp only [t', i', m', gs3, p3, posE] at htriv hacc hsw hra3 hr3a
  simp only [spkIjArmHaltedTier2C, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    orE, isSomeE, otherE, pGet, gsWinTier2E, gsStTier2E, atomicDraw256_cost,
    cost_tier2RecvRejE] at hit hsi hrka hr0 hrcv hr2 hr3 htriv hacc hsw hra3 hr3a ⊢
  rw [hrka, hr0, hr2, hr3, hr3a, hra3]
  generalize (inTransitTier2E (Pt := Pt) (lam := lam) _ _ _).cost = cit at hit ⊢
  generalize (safeInjTier2E _ _).cost = csi at hsi ⊢
  generalize (receiveSpkAtomicC (Pt := Pt) (lam := lam) _ _ _ _).cost = crcv at hrcv ⊢
  generalize (trivialTier2E _ _ _).cost = ctriv at htriv ⊢
  generalize (acceptCiphertextTier2E _ _ _ _).cost = cacc at hacc ⊢
  generalize (setWinTier2E _ _).cost = csw at hsw ⊢
  omega

private theorem spkCrArmHaltedTier2C_cost :
    (spkCrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 500 := by
  let Γ₀ : List (Ty ASig) := [.prod (tier2GsTy ℓ Pt) .bool]
  have hca := cost_corrAllowedTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) (.fst .v0) (.snd .v0)
  have hiw := cost_inWindowTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) (.fst .v0) (.snd .v0)
  have hcok := cost_corrOKTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) (.fst .v0) (.snd .v0)
  have haca := cost_afterCorrAllowedTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.fst .v0) (.snd .v0)
  have hc0 := cost_tier2SmRCorrE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hc1 := cost_tier2SmRCorrE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.some (pGet (gsStTier2E (.fst .v0)) (.snd .v0)))
  simp only [spkCrArmHaltedTier2C, Comp.cost, Expr.cost, Expr.v0, orE, pGet, gsWinTier2E,
    gsStTier2E] at hca hiw hcok haca hc0 hc1 ⊢
  omega

theorem spkStepHaltedTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      5160000 + 61 * ℓ + 2 * bits qep := by
  have htr := spkTrArmHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hch := spkChArmHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hdl := spkDlArmHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ
  have hij := spkIjArmHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hcr := spkCrArmHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
  dsimp only [spkStepHaltedTier2C]
  rw [Comp.cost]
  simp only [Comp.cost, wk1Comp_cost]
  generalize (spkTrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = ctr
    at htr ⊢
  generalize (spkChArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = cch
    at hch ⊢
  generalize (spkDlArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost = cdl
    at hdl ⊢
  generalize (spkIjArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = cij
    at hij ⊢
  generalize (spkCrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost = ccr
    at hcr ⊢
  simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

private theorem size_inTransitTier2E {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (sE : Expr AOps Γ (tier2GsTy ℓ Pt)) (pE : Expr AOps Γ .bool) (cE : Expr AOps Γ (B 32)) :
    (inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) sE pE cE).size ≤ sE.size + pE.size + cE.size + 900 := by
  have hwk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) hℓ cE
  simp only [inTransitTier2E, tbl1GetE, pGet, gsNodeRecTier2E, gsHeadTblTier2E,
    Expr.size, Expr.v0, Expr.v1] at hwk ⊢; omega

private theorem size_acceptCiphertextTier2E {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (tier2GsTy ℓ Pt)) (pE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ GhostStT) (posE : Expr AOps Γ posTy) :
    (acceptCiphertextTier2E (O := AOps) sE pE stE posE).size ≤
      2 * sE.size + pE.size + stE.size + 3 * posE.size + 1500 := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 := by decide
  simp only [acceptCiphertextTier2E, deleteCiphertextTier2E, tbl1GetE, tbl1SetE, posTblGetE, posTblSetE,
    maxN, _root_.CryptoGames.SM.leN, pSet, pGet, posSender, posEpoch, posIdx, gsStTier2E, gsEpochTier2E,
    gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E, gsNextIdTier2E, gsHeadTblTier2E, gsNodeKeyTier2E,
    gsNodePrevTier2E, gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E,
    gsCompTblTier2E, gsUncompCountTier2E, Expr.size, Expr.v0, Expr.v1, Expr.v2, hb.1, hb.2]
  omega

private theorem size_recordCiphertextTier2E_three {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (sE : Expr AOps Γ (tier2GsTy ℓ Pt)) (pE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ GhostStT) (rE : Expr AOps Γ (tier2RecTy ℓ Pt)) (isChallE : Expr AOps Γ .bool) :
    (recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) 3 sE pE stE rE isChallE).size ≤
      sE.size + pE.size + stE.size + rE.size + isChallE.size + 1800 := by
  let tIn : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT (.prod (tier2RecTy ℓ Pt) .bool)))
  have hwk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := tIn :: Γ) hℓ
    (tier2RecCt (.fst (.snd (.snd (.snd .v0)))))
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 3 = 2 := by decide
  dsimp only [recordCiphertextTier2E, safeChTier2E, leakTier2E, sendsInE,
    _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.otherE, tbl1GetE, tbl1SetE, posTblSetE, orE, maxN, isSomeE, pSet, pGet,
    posSender, posEpoch, posIdx, tier2RecPos, tier2RecCt, gsStTier2E, gsEpochTier2E, gsIdxTier2E,
    gsTLTier2E, gsMaxAccTier2E, gsNextIdTier2E, gsHeadTblTier2E, gsNodeRecTier2E, gsNodeKeyTier2E,
    gsNodePrevTier2E, gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E,
    gsCompTblTier2E, gsUncompCountTier2E, Expr.size, Expr.v0, Expr.v1] at hwk ⊢
  simp only [hb.1, hb.2.1, hb.2.2]; omega

private theorem size_epMgmtTier2E_three {Γ : List (Ty ASig)} (qep : ℕ)
    (sE : Expr AOps Γ (tier2GsTy ℓ Pt)) (pE : Expr AOps Γ .bool) (badE : Expr AOps Γ .bool) :
    (epMgmtTier2E (O := AOps) 3 qep sE pE badE).size ≤
      sE.size + pE.size + badE.size + 2 * bits qep + 350 := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 3 = 2 := by decide
  dsimp only [epMgmtTier2E, safeChTier2E, leakTier2E, sendsInE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.otherE,
    orE, maxN, isSomeE, pSet, pGet, gsEpochTier2E, gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E,
    Expr.size, Expr.v0, Expr.v1]
  simp only [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]; omega

theorem spkStepHaltedTier2C_size (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size ≤
      3900000 + 6 * bits qep := by
  let tTr : Ty ASig := .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))
  let tCh : Ty ASig :=
    .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let tDl : Ty ASig := .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (B 32))
  let tIj : Ty ASig := .prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))
  have htr_sam := samIfNec512Tier2C_size C K Dh encPt encT decT lam
    (.snd (.snd (.snd .v0)) : Expr AOps [tTr] (.opt BV512))
  have htr_ep := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep
    (.snd (.fst (.fst .v1)) : Expr AOps [.prod BV512 .bool, tTr] _) (.fst (.snd .v1)) (.snd .v0)
  have htr_kf := stepKemFailSendTier2C_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := PrfI)
    (.fst (.snd (.fst .v2)) : Expr AOps [tier2GsTy ℓ Pt, .prod BV512 .bool, tTr] _)
    (.fst (.snd .v2)) (.fst .v1)
  have htr_dr := drSendCoinsTier2C_size C K Dh encPt encT decT lam
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3))) (.pair (.fst (.snd (.snd .v3))) (.fst .v2)) :
      Expr AOps [.prod .bool (kemTrackTier2T ℓ Pt), tier2GsTy ℓ Pt, .prod BV512 .bool, tTr] _)
  let Γtr4 : List (Ty ASig) :=
    [.prod GhostStT (B 32), .prod .bool (kemTrackTier2T ℓ Pt), tier2GsTy ℓ Pt,
     .prod BV512 .bool, tTr]
  have htr_rec := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam (Γ := Γtr4) hℓ
    .v2 (.fst (.snd .v4)) (.fst .v0)
    (tier2RecMk (.pair (.fst (.snd .v4)) (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
      (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))))
      (.fst (.snd (.snd .v4))) (.snd .v0)) (.bool false)
  have htr_hw := recordHonestWireTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γtr4) hℓ
    (.snd (.snd (.fst .v4))) (.snd .v0) (.fst (.snd .v4))
  have hch_sam := samIfNec512Tier2C_size C K Dh encPt encT decT lam
    (.snd (.snd (.snd (.snd .v0))) : Expr AOps [tCh] (.opt BV512))
  have hch_ep := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep
    (.snd (.fst (.fst .v1)) : Expr AOps [.prod BV512 .bool, tCh] _) (.fst (.snd .v1)) (.snd .v0)
  have hch_kf := stepKemFailSendTier2C_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := PrfI)
    (.fst (.snd (.fst .v2)) : Expr AOps [tier2GsTy ℓ Pt, .prod BV512 .bool, tCh] _)
    (.fst (.snd .v2)) (.fst .v1)
  have hch_dr := drSendCoinsTier2C_size C K Dh encPt encT decT lam
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3)))
      (.pair (.ite (gsBTier2E (.snd (.fst (.fst .v3))))
        (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3)))) (.fst .v2)) :
      Expr AOps [.prod .bool (kemTrackTier2T ℓ Pt), tier2GsTy ℓ Pt, .prod BV512 .bool, tCh] _)
  let Γch4 : List (Ty ASig) :=
    [.prod GhostStT (B 32), .prod .bool (kemTrackTier2T ℓ Pt), tier2GsTy ℓ Pt,
     .prod BV512 .bool, tCh]
  have hch_rec := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam (Γ := Γch4) hℓ
    .v2 (.fst (.snd .v4)) (.fst .v0)
    (tier2RecMk (.pair (.fst (.snd .v4)) (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd .v4)))
      (.add (pGet (gsIdxTier2E .v2) (.fst (.snd .v4))) (.nat 1))))
      (.ite (gsBTier2E (.snd (.fst (.fst .v4))))
        (.fst (.snd (.snd (.snd .v4)))) (.fst (.snd (.snd .v4)))) (.snd .v0)) (.bool true)
  have hch_hw := recordHonestWireTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γch4) hℓ
    (.snd (.snd (.fst .v4))) (.snd .v0) (.fst (.snd .v4))
  have hdl_it := size_inTransitTier2E C K Dh encPt encT decT lam (Γ := [tDl]) hℓ
    (.snd (.fst (.fst .v0))) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hdl_rcv := receiveSpkAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.fst (.fst .v2)) : Expr AOps [BV256, tier2RecTy ℓ Pt, tDl] BV256)
    (pGet (gsStTier2E (.snd (.fst (.fst .v2)))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0
  let Γdl4 : List (Ty ASig) :=
    [.prod GhostStT (.prod .nat (.prod .nat PlainT)), drRecvAtomicOutT ℓ Pt, BV256,
     tier2RecTy ℓ Pt, tDl]
  have hdl_acc := size_acceptCiphertextTier2E C K Dh encPt encT decT lam (Γ := Γdl4)
    (.snd (.fst (.fst .v4))) (.fst (.snd .v4)) (.fst .v0) (tier2RecPos .v3)
  have hdl_j := findRevHonestWireIdxTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γdl4) hℓ
    (.snd (.snd (.fst .v4))) (.fst (.snd .v4)) (.snd (.snd .v4))
  have hdl_p := kemOnDeliverPostTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γdl4)
    (.fst (.snd .v4))
    (findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (.snd (.snd (.fst .v4)))
      (.fst (.snd .v4)) (.snd (.snd .v4)))
    (.some (tier2RecvAccE (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
      (.ite (gsChallTier2E (.snd (.fst (.fst .v4))) (tier2RecPos .v3))
        .none (.some (.snd (.snd (.snd .v0)))))))
    (.fst (.snd (.fst .v4)))
  have hij_it := size_inTransitTier2E C K Dh encPt encT decT lam (Γ := [tIj]) hℓ
    (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hij_rcv := receiveSpkAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst .v1 : Expr AOps [BV256, tIj] BV256)
    (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd .v1))) .v0
  let Γij3 : List (Ty ASig) :=
    [.prod GhostStT (.prod .nat (.prod .nat PlainT)), drRecvAtomicOutT ℓ Pt, BV256, tIj]
  have hij_acc := size_acceptCiphertextTier2E C K Dh encPt encT decT lam (Γ := Γij3)
    (.fst (.snd .v3)) (.fst (.snd (.snd .v3))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.snd .v3)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hbs := bits_succ_le qep
  dsimp only [spkStepHaltedTier2C, spkTrArmHaltedTier2C, spkChArmHaltedTier2C,
    spkDlArmHaltedTier2C, spkIjArmHaltedTier2C, spkCrArmHaltedTier2C,
    tier2SmRWireE, tier2SmRRecvE, tier2SmRCorrE, isSomeE, orE, otherE] at hij_it hdl_it hij_acc ⊢
  simp only [Comp.size, wk1Comp_size, atomicDraw256_size, Expr.size]
  generalize (samIfNec512Tier2C C K Dh encPt encT decT lam (.snd (.snd (.snd .v0)) : Expr AOps [tTr] _)).size = s1 at htr_sam ⊢
  generalize (epMgmtTier2E 3 qep (.snd (.fst (.fst .v1)) : Expr AOps [.prod BV512 .bool, tTr] _) (.fst (.snd .v1)) (.snd .v0)).size = s2 at htr_ep ⊢
  generalize (stepKemFailSendTier2C (I := PrfI) (.fst (.snd (.fst .v2)) : Expr AOps [tier2GsTy ℓ Pt, .prod BV512 .bool, tTr] _) (.fst (.snd .v2)) (.fst .v1)).size = s3 at htr_kf ⊢
  generalize (drSendCoinsTier2C C K Dh encPt encT decT lam (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3))) (.pair (.fst (.snd (.snd .v3))) (.fst .v2)) : Expr AOps [_, _, _, tTr] _)).size = s4 at htr_dr ⊢
  generalize (recordCiphertextTier2E 3 (.v2 : Expr AOps Γtr4 _) _ _ _ _).size = s5 at htr_rec ⊢
  generalize (recordHonestWireTier2E (.snd (.snd (.fst .v4)) : Expr AOps Γtr4 _) _ _).size = s6 at htr_hw ⊢
  generalize (samIfNec512Tier2C C K Dh encPt encT decT lam (.snd (.snd (.snd (.snd .v0))) : Expr AOps [tCh] _)).size = s7 at hch_sam ⊢
  generalize (epMgmtTier2E 3 qep (.snd (.fst (.fst .v1)) : Expr AOps [.prod BV512 .bool, tCh] _) (.fst (.snd .v1)) (.snd .v0)).size = s8 at hch_ep ⊢
  generalize (stepKemFailSendTier2C (I := PrfI) (.fst (.snd (.fst .v2)) : Expr AOps [tier2GsTy ℓ Pt, .prod BV512 .bool, tCh] _) (.fst (.snd .v2)) (.fst .v1)).size = s9 at hch_kf ⊢
  generalize (drSendCoinsTier2C C K Dh encPt encT decT lam (.pair (pGet (gsStTier2E .v1) (.fst (.snd .v3))) _ : Expr AOps [_, _, _, tCh] _)).size = s10 at hch_dr ⊢
  generalize (recordCiphertextTier2E 3 (.v2 : Expr AOps Γch4 _) _ _ _ _).size = s11 at hch_rec ⊢
  generalize (recordHonestWireTier2E (.snd (.snd (.fst .v4)) : Expr AOps Γch4 _) _ _).size = s12 at hch_hw ⊢
  generalize (inTransitTier2E (.snd (.fst (.fst .v0)) : Expr AOps [tDl] _) _ _).size = s13 at hdl_it ⊢
  generalize (receiveSpkAtomicC (Pt := Pt) (lam := lam) (.fst (.fst (.fst .v2)) : Expr AOps [BV256, tier2RecTy ℓ Pt, tDl] _) _ _ _).size = s14 at hdl_rcv ⊢
  generalize (acceptCiphertextTier2E (.snd (.fst (.fst .v4)) : Expr AOps Γdl4 _) _ _ _).size = s15 at hdl_acc ⊢
  generalize (kemOnDeliverPostTier2E (.fst (.snd .v4) : Expr AOps Γdl4 _) _ _ _).size = s16 at hdl_p ⊢
  generalize (findRevHonestWireIdxTier2E (.snd (.snd (.fst .v4)) : Expr AOps Γdl4 _) _ _).size = s17 at hdl_j hdl_p
  generalize (inTransitTier2E (.fst (.snd .v0) : Expr AOps [tIj] _) _ _).size = s18 at hij_it ⊢
  generalize (receiveSpkAtomicC (Pt := Pt) (lam := lam) (.fst .v1 : Expr AOps [BV256, tIj] _) _ _ _).size = s19 at hij_rcv ⊢
  generalize (acceptCiphertextTier2E (.fst (.snd .v3) : Expr AOps Γij3 _) _ _ _).size = s20 at hij_acc ⊢
  dsimp only [orE, isSomeE, otherE, pGet, pSet, sendOKTier2E, gsWinTier2E, gsBTier2E, gsStTier2E,
    gsEpochTier2E, gsIdxTier2E, gsChallTier2E, SpkTier2BookkeepingBase.gsCompTier2E,
    safeChTier2E, safeInjTier2E, leakTier2E, trivialTier2E,
    setWinTier2E, corrAllowedTier2E, afterCorrAllowedTier2E, inWindowTier2E, corrOKTier2E,
    tier2RecvRejE, tier2RecvAccE, tier2RecPos, tier2RecMk, gsTLTier2E, gsMaxAccTier2E, gsNextIdTier2E,
    gsHeadTblTier2E, gsNodeRecTier2E, gsNodeKeyTier2E, gsNodePrevTier2E, gsNodeNextTier2E,
    gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E,
    posTblGetE, tbl1GetE, tbl1SetE, sendsInE, posSender, posEpoch, posIdx, maxN,
    _root_.CryptoGames.SM.minN, _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.maxOptE,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.otherE,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
    at htr_sam htr_ep htr_kf htr_dr htr_rec htr_hw hch_sam hch_ep hch_kf hch_dr hch_rec hch_hw
       hdl_it hdl_rcv hdl_acc hdl_j hdl_p hij_it hij_rcv hij_acc ⊢
  simp only [size_ratchetKeyAdmissibleTier2E, Expr.size,
    show bits 0 = 1 from rfl, show bits 1 = 1 from rfl, show bits 2 = 2 from rfl,
    show bits 3 = 2 from rfl, show bits 10 = 4 from rfl]
    at htr_sam htr_ep htr_kf htr_dr htr_rec htr_hw hch_sam hch_ep hch_kf hch_dr hch_rec hch_hw
       hdl_it hdl_rcv hdl_acc hdl_j hdl_p hij_it hij_rcv hij_acc ⊢
  omega

@[expose] def spkFinishTier2C : Comp AOps PrfI [spkHaltedTier2StTy ℓ Pt, .bool] .bool :=
  .ret (orE (boolEq (gsBTier2E (.snd (.fst .v0))) .v1) (gsWinTier2E (.snd (.fst .v0))))

theorem spkFinishTier2C_cost :
    (spkFinishTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 30 := by
  simp only [spkFinishTier2C, orE, boolEq, gsBTier2E, gsWinTier2E, Comp.cost, Expr.cost, Expr.v0, Expr.v1]; omega

theorem spkFinishTier2C_size :
    (spkFinishTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 30 := by
  simp only [spkFinishTier2C, orE, boolEq, gsBTier2E, gsWinTier2E, Comp.size, Expr.size, Expr.v0, Expr.v1]; omega


end HaltedTier2

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Defs
