/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.DrSessionSimRecv
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost

/-!
# Tight Tier-1 Cost Bounds for Tracker-Halted Hop 2

Proves tight static `.cost` bounds for `hop2InitBodyTrackC`, `hop2InitPrfTrackC`,
`hop2SendAfterPreTrackC`, and `hop2StepTrackC` within `spkTier1Budget`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier1Tight

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp CostedReduction
  bits bits_mono atomicSig atomicSessionOps coinOnlyIface
  BV256 BV512 PK PtT GhostStT PlainT B smQT smRT)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (posTy posSender orE isSomeE otherE pGet boolEq)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes spkTier1Budget)
open CryptoVerification.E2E.Costed (e2eSig e2eOps)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsSt e2eGsWin
  e2eGsTrans e2eRecPos e2eRecCt e2eInTransitE
  cost_e2eSafeInjE_le cost_e2eTrivialE_le cost_e2eAcceptE_le cost_e2eGsSetWin_le
  cost_ratchetKeyAdmissibleE cost_bytesEqE cost_smRRecvE cost_recvResultRejE cost_recvResultAccE)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drCrArmC drCrArmC_cost)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  liftTy renExpr renExpr_cost wk1Expr wk1Comp wk1Expr_cost wk1Comp_cost
  coinE2EIface liftExpr liftCompCoins liftCompCoins_cost)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (bits_succ_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (initKemTrackAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost (initKemTrackAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub (trE_cand)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub (
  kemOnDeliverPostAtomicE kemOnDeliverPostAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg (
  compCoinToPrf cost_compCoinToPrf Hop2Mode
  drawBoolCoin_cost draw256Coin draw256Coin_cost
  sPureOp sGroupOp cost_sPureOp cost_sGroupOp
  hop2ChallTy hop2EntryTy hop2UpdTy hop2SendHalfResTy hop2AuxTy hop2RecvResTy hop2FullStTy
  auxLazy auxMade auxIdx auxCoins auxBad auxMk auxSetBad cost_auxConsLazy cost_auxSetBad
  stS stGs stAux stChall stMk
  hop2LookupE hop2CommitE cost_hop2CommitE
  dhTargetPtAtomicE cost_dhTargetPtAtomicE
  cost_finishHop2DHAtomicC_tight hop2FinishNoneC hop2LazyC
  cost_hop2SendHalfSomeC hop2DHC hop2RecvC hop2DlArmC hop2IjArmC
  hop2InitGsE2EE cost_hop2InitGsE2EE noKemKeyGenExpr_hop2InitGsE2EE
  dlPreE2EE cost_dlPreE2EE noKemKeyGenExpr_dlPreE2EE
  dlPostE2EE cost_dlPostE2EE noKemKeyGenExpr_dlPostE2EE
  ijPreE2EE noKemKeyGenExpr_ijPreE2EE
  ijPostHop2E2EE noKemKeyGenExpr_ijPostHop2E2EE
  hop2BadAtE2EE cost_hop2BadAtE2EE noKemKeyGenExpr_hop2BadAtE2EE
  needsDHE2EE cost_needsDHE2EE noKemKeyGenExpr_needsDHE2EE
  hasSenderChainE2EE cost_hasSenderChainE2EE noKemKeyGenExpr_hasSenderChainE2EE
  sendHalfRealE2EE cost_sendHalfRealE2EE noKemKeyGenExpr_sendHalfRealE2EE
  liftExpr_cost_exact liftCompCoins_cost_exact drReceiveAtomicC_cost_exact)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step (
  hop2HaltedStTy hstBase hstSessionTr hstTr hstWires hstMk
  hop2InitBodyTrackC hop2InitPrfTrackC
  findHonestWireIdxE cost_findHonestWireIdxE
  trPreE2EC chPreE2EC sendPostE2EC cost_trPreE2EC cost_chPreE2EC cost_sendPostE2EC
  hop2SendAfterPreTrackC hop2StepTrackC)

theorem session_cost_le_spkTier1Budget
    (q qep cInit cFin cStepBase cStepQ cStepQep : ℕ)
    (hInit : cInit ≤ 1000000)
    (hFin : cFin ≤ 1000000)
    (hBase : cStepBase ≤ 12800000)
    (hQ : cStepQ ≤ 1024)
    (hQep : cStepQep ≤ 256) :
    cInit + q * (cStepBase + cStepQ * q + cStepQep * bits qep) + cFin ≤
      spkTier1Budget q qep := by
  have h1 : q * cStepBase ≤ q * 12800000 := Nat.mul_le_mul_left q hBase
  have h2 : q * (cStepQ * q) ≤ q * (1024 * q) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right q hQ)
  have h3 : q * (cStepQep * bits qep) ≤ q * (256 * bits qep) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right (bits qep) hQep)
  have hlhs : q * (cStepBase + cStepQ * q + cStepQep * bits qep) =
      q * cStepBase + q * (cStepQ * q) + q * (cStepQep * bits qep) := by ring
  have hmfj : CryptoGames.LibsignalSession.maxForwardJumps = 25000 := rfl
  simp only [spkTier1Budget, hmfj]
  have hrhs : 2 ^ 10 * (q + 1) ^ 2 + 2 ^ 9 * 25000 * (q + 1) + 2 ^ 8 * (q + 1) * bits qep =
      12801024 + 12802048 * q + 1024 * (q * q) + 256 * bits qep + 256 * (q * bits qep) := by ring
  have hm1 : q * 12800000 = 12800000 * q := by ring
  have hm2 : q * (1024 * q) = 1024 * (q * q) := by ring
  have hm3 : q * (256 * bits qep) = 256 * (q * bits qep) := by ring
  rw [hlhs, hrhs]
  rw [hm1] at h1
  rw [hm2] at h2
  rw [hm3] at h3
  omega

theorem q_add_eleven_le_spkTier1Budget (q' qep' : ℕ) :
    q' + 11 ≤ spkTier1Budget q' qep' := by
  have h := session_cost_le_spkTier1Budget q' qep' 11 0 1 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem spkTier1Budget_mono_qep (q : ℕ) {qep₁ qep₂ : ℕ} (h : qep₁ ≤ qep₂) :
    spkTier1Budget q qep₁ ≤ spkTier1Budget q qep₂ := by
  have hm := Nat.mul_le_mul_left (2 ^ 8 * (q + 1)) (bits_mono h)
  dsimp only [spkTier1Budget]
  omega

theorem spkTier1Budget_le_ratchetCostBudget (q qep : ℕ) :
    spkTier1Budget q qep ≤ CryptoVerification.LibsignalSession.ratchetCostBudget q qep := by
  have hmfj : CryptoGames.LibsignalSession.maxForwardJumps = 25000 := rfl
  simp only [spkTier1Budget, CryptoVerification.LibsignalSession.ratchetCostBudget, hmfj]
  have hq1 : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  have h1 : 2 ^ 10 * (q + 1) ^ 2 + 2 ^ 9 * 25000 * (q + 1) ≤ 2 ^ 12 * (q + 1) ^ 2 * 25000 := by
    nlinarith
  have h2 : 2 ^ 8 * (q + 1) * bits qep ≤ 2 ^ 12 * (q + 1) ^ 2 * bits qep :=
    Nat.mul_le_mul_right (bits qep) (by nlinarith)
  nlinarith

section Tier1Tight

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem cost_ijPreE2EE_tight (q Δ : ℕ) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).cost ≤
      400 + (ℓ / 32 + 1) + 85 * q + bits Δ := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  have hsinj := cost_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ))
  simp only [ijPreE2EE, e2eInTransitE, e2eGsTrans, e2eRecPos, e2eRecCt, posSender, boolEq,
    cost_bytesEqE, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    cost_ratchetKeyAdmissibleE, cost_smRRecvE, Expr.cost, Expr.v0, Expr.v1, hm34] at hsinj ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem cost_ijPostHop2E2EE_tight (q Δ qep : ℕ) :
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).cost ≤
      1020 + 290 * q + bits Δ + bits (qep + 1) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have htriv := cost_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hwin := cost_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.bool true)
  simp only [ijPostHop2E2EE, otherE, cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE,
    Expr.cost, Expr.v0, Expr.v1] at htriv hacc hwin ⊢
  omega

private theorem cost_hop2LookupE_tight {Γ : List (Ty ASig)} (L : ℕ)
    (lE : Expr AOps Γ (.list (hop2EntryTy ℓ Pt)))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L lE tE qE).cost ≤
      lE.cost + tE.cost + qE.cost + 26 * L + 20 := by
  have hmax3 : max 3 1 = 3 := rfl
  simp only [hop2LookupE, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    cost_sGroupOp, _root_.ReductionDsl.AtomicGroupOp.cost, Nat.reduceAdd, hmax3]; omega

private theorem cost_hop2FinishNoneC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    (hop2FinishNoneC M gE srkE cE rcE rkME ckRE auxE).cost ≤
      gE.cost + 2 * srkE.cost + cE.cost + 2 * rcE.cost + rkME.cost + ckRE.cost + auxE.cost +
        5104015 + 8 * (ℓ / 32 + 1) + 950 := by
  have hs1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hs2 := cost_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let tOuter : Ty ASig :=
    .prod (.opt (.prod BV256 BV256))
      (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2AuxTy ℓ Pt))))))
  have hf := cost_finishHop2DHAtomicC_tight M
    (Γ := [.prod BV256 BV256, tOuter] ++ Γ)
    (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst .v0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) (.snd .v0)
    (.pair .none (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) .none))
  simp only [hop2FinishNoneC, Comp.cost, wk1Expr_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hf ⊢
  omega

private theorem cost_hop2LazyC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyC M L auxE tE qE).cost ≤ auxE.cost + tE.cost + qE.cost + 26 * L + 100 := by
  let tOuter : Ty ASig := .prod (hop2AuxTy ℓ Pt) (.prod .nat PtT)
  have hlk := cost_hop2LookupE_tight C K Dh encPt encT decT lam L
    (Γ := [tOuter] ++ Γ) (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hcl := cost_auxConsLazy (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := [BV256, tOuter] ++ Γ)
    (.fst .v1) (.pair (.pair (.fst (.snd .v1)) (.snd (.snd .v1))) .v0)
  simp only [hop2LazyC, auxLazy, Comp.cost, M.embedCoin_cost, draw256Coin_cost,
    Expr.cost, Expr.v0, Expr.v1] at hlk hcl ⊢
  omega

private theorem cost_hop2DHC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHC M q k challE auxE tE coinsE gE srkE cE rcE).cost ≤
      challE.cost + auxE.cost + tE.cost + coinsE.cost + 2 * gE.cost + 2 * srkE.cost +
        cE.cost + rcE.cost + 5104015 + 8 * (ℓ / 32 + 1) + 52 * q + 3 * bits k + 3000 := by
  have hsc1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsc2 := cost_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hdt := cost_dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) srkE
  have hbkp1 : bits (k + 1) ≤ bits k + 1 := bits_succ_le k
  have hb1 : bits 1 = 1 := by decide
  let t0 : Ty ASig :=
    .prod (.opt PtT)
      (.prod .bool
        (.prod (hop2ChallTy ℓ Pt)
          (.prod (hop2AuxTy ℓ Pt)
            (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let p1 : Expr AOps ([PtT, t0] ++ Γ) _ := .snd (.snd .v1)
  let qPt : Expr AOps ([PtT, t0] ++ Γ) PtT :=
    sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd p1)))) .v0)
  have hlk := cost_hop2LookupE_tight C K Dh encPt encT decT lam (q + 1)
    (auxMade (.fst (.snd p1))) (.fst (.snd (.snd p1))) qPt
  have hlz := cost_hop2LazyC_tight C K Dh encPt encT decT lam M q
    (.fst (.snd p1)) (.fst (.snd (.snd p1))) qPt
  let p3a : Expr AOps ([.prod BV256 BV256, .prod BV256 (hop2AuxTy ℓ Pt), PtT, t0] ++ Γ) _ :=
    .snd (.snd .v3)
  have hfn1 := cost_hop2FinishNoneC_tight C K Dh encPt encT decT lam M
    (.fst (.snd (.snd (.snd (.snd p3a)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3a))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.fst .v0) (.snd .v0) (.snd .v1)
  let p2 : Expr AOps ([BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v2)
  have hsh := cost_hop2SendHalfSomeC M k
    (.fst p2) (.add (.fst (.snd (.snd p2))) (.nat 1))
    (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))) .v1))
  let tShInner : Ty ASig :=
    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
  let p4 : Expr AOps ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v4)
  have hfd := cost_finishHop2DHAtomicC_tight M
    (.fst (.snd (.snd (.snd (.snd p4)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p4))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
    (.pair (.fst .v0) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
      (.snd (.snd (.snd .v0)))))
  have hst := M.stepC_cost (.fst (.fst p1)) qPt
  let p3b : Expr AOps ([.prod BV256 BV256, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn2 := cost_hop2FinishNoneC_tight C K Dh encPt encT decT lam M
    (.fst (.snd (.snd (.snd (.snd p3b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.fst .v0) (.snd .v0) (.fst (.snd p3b))
  simp only [hop2DHC, p1, qPt, p3a, p2, p4, p3b, auxMade,
    Comp.cost, wk1Expr_cost, cost_sGroupOp, _root_.ReductionDsl.AtomicGroupOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, hb1]
    at hdt hlk hlz hfn1 hsh hfd hst hfn2 ⊢
  omega

private theorem cost_hop2RecvC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvC M q k challE auxE gE cE rcE).cost ≤
      challE.cost + auxE.cost + gE.cost + cE.cost + rcE.cost +
        5104015 + 10 * (ℓ / 32 + 1) + 52 * q + 3 * bits k + 3500 := by
  have hnd1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hnd2 := cost_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt)
      (.prod (hop2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let tAuxU : Ty ASig := .prod (hop2AuxTy ℓ Pt) .unit
  have hdr1 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, _root_.ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v1))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v1)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v1)))))))
  have hdr2 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, .nat, _root_.ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v2))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v2)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v2)))))))
  have hdh := cost_hop2DHC_tight C K Dh encPt encT decT lam M q k
    (Γ := [.nat, _root_.ReductionDsl.signalParsedT, t0] ++ Γ)
    (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoins (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
    (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
    (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvC, auxIdx, auxCoins, pGet,
    Comp.cost, M.embedCoin_cost, wk1Expr_cost, renExpr_cost,
    cost_sPureOp, _root_.ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hdr1 hdr2 hdh ⊢
  omega

private theorem cost_hop2DlArmC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) :
    (hop2DlArmC C K Dh encPt encT decT lam M q k).cost ≤
      5112000 + 12 * (ℓ / 32 + 1) + 790 * q + 3 * bits k := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tInr : Ty ASig := .prod GhostStT (liftTy (Pt := Pt) posTy)
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (noKemKeyGenExpr_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpre2 := cost_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (noKemKeyGenExpr_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost2 := cost_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hbad1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hrecv := cost_hop2RecvC_tight C K Dh encPt encT decT lam M q k
    (Γ := [BV256, tInr, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    (.fst .v1) (.snd (.snd .v2)) .v0
  have hcomm := cost_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (.snd .v1) (.fst (.snd .v4)) (.snd .v0)
  have hsbad := cost_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (hop2CommitE (.snd .v1) (.fst (.snd .v4)) (.snd .v0))
    (orE (auxBad (.snd .v1))
      (.letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
          (.pair (.fst .v3) (.snd (.snd .v4))))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))))
  simp only [hop2DlArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE,
    Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hrecv hcomm hsbad ⊢
  omega

private theorem cost_hop2IjArmC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2IjArmC C K Dh encPt encT decT lam M q qep k).cost ≤
      5113000 + 14 * (ℓ / 32 + 1) + 1010 * q + 3 * bits (qep + 1) + 3 * bits k := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
    (noKemKeyGenExpr_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
  have hpre2 := cost_ijPreE2EE_tight (Pt := Pt) (ℓ := ℓ) C K encT decT q (2 + 1)
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
    (noKemKeyGenExpr_ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      q (2 + 1) qep)
  have hpost2 := cost_ijPostHop2E2EE_tight (Pt := Pt) (ℓ := ℓ) C K encT decT q (2 + 1) qep
  have hbad1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hrecv := cost_hop2RecvC_tight C K Dh encPt encT decT lam M q k
    (Γ := [BV256, GhostStT, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    .v1 (.snd (.snd .v2)) .v0
  let badAtB : Expr AOps [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0] .bool :=
    .letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4)) (.pair .v3 (.snd (.snd .v4))))
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  let aux1E := auxSetBad (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hsbad := cost_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hcomm := cost_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    aux1E (.fst (.snd .v4)) (.snd .v0)
  have hb3 : bits (2 + 1) = 2 := by decide
  dsimp only [aux1E, badAtB] at hsbad hcomm
  simp only [hop2IjArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE, hb3,
    Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hpre2 hpost2 hrecv hsbad hcomm ⊢
  omega

theorem cost_hop2SendAfterPreTrackC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q : ℕ) (isChall : Bool) :
    (hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q isChall).cost ≤
      1225000 + 10 * (ℓ / 32 + 1) + 251 * q := by
  let CoinI := coinOnlyIface ℓ Pt
  let tIn : Ty ASig := .prod (hop2HaltedStTy ℓ Pt)
    (.prod .bool (.opt (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512))))
  let tSome : Ty ASig := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512)
  let sEmb := Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.sessionEmbed
    ℓ Pt C K Dh encPt encT decT lam
  have hstep :=
    Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.stepKemFailSendPairC_cost_le
      sEmb q (I := CoinI)
      (hstTr C K Dh encPt encT decT lam (.fst (.v1 : Expr AOps [tSome, tIn] tIn)))
      (.fst (.snd .v1)) (.snd (.snd .v0))
  have hpost1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall)
    (by
      dsimp only [sendPostE2EC,
        Computational.Proofs.E2E.Dsl.DrSessionSim.drSendC,
        Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks,
        Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE,
        Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE]
      cases isChall <;>
      cases CryptoVerification.E2E.serializedPartyAddresses
        CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A <;>
      cases CryptoVerification.E2E.serializedPartyAddresses
        CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B <;>
      rfl)
  have hpost2 := cost_sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall
  have hpost := hpost1.trans hpost2
  clear hpost1 hpost2
  dsimp only [hop2SendAfterPreTrackC, sEmb, tSome, tIn, CoinI] at hstep hpost ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall) = postC at hpost ⊢
  simp only [hstBase, hstTr, hstWires, hstMk, stS, stAux, stChall, stMk, trE_cand,
    M.embedCoin_cost, wk1Comp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hstep hpost ⊢
  generalize (Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.stepKemFailSendPairC
    _ q _ _ _).cost = ckf at hstep ⊢
  omega

/-- Tight Tier-1 static cost bound for `hop2StepTrackC`. -/
theorem cost_hop2StepTrackC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepTrackC C K Dh encPt encT decT lam M q qep k).cost ≤
      5121000 + 14 * (ℓ / 32 + 1) + 1010 * q +
        32 * bits qep + 32 * bits (qep + 1) + 3 * bits k := by
  let CoinI := coinOnlyIface ℓ Pt
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)
  have htr2 := cost_trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep
  have htr := htr1.trans (Nat.mul_le_mul_left 32 htr2)
  clear htr1 htr2
  have hch1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)
  have hch2 := cost_chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep
  have hch := hch1.trans (Nat.mul_le_mul_left 32 hch2)
  clear hch1 hch2
  have hcr1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
    rfl
  have hcr2 := drCrArmC_cost (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  simp only [Expr.cost, Expr.v0] at hcr2
  have hcr := hcr1.trans hcr2
  clear hcr1 hcr2
  have hsndF := cost_hop2SendAfterPreTrackC_tight C K Dh encPt encT decT lam M q false
  have hsndT := cost_hop2SendAfterPreTrackC_tight C K Dh encPt encT decT lam M q true
  let tG : List (Ty ASig) := [hop2HaltedStTy ℓ Pt, smQT]
  let tDlArg : Ty ASig := .prod .bool (B 32)
  let tDlIn : Ty ASig := .prod (hop2FullStTy ℓ Pt) tDlArg
  let tDlOut : Ty ASig := .prod (smRT GhostStT) (hop2FullStTy ℓ Pt)
  have hfind := cost_findHonestWireIdxE C K Dh encPt encT decT lam q
    (hstWires C K Dh encPt encT decT lam
      (.v3 : Expr AOps (tDlArg :: .sum tDlArg (.sum (.prod .bool (B 32)) .bool) ::
        .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
          (.sum tDlArg (.sum (.prod .bool (B 32)) .bool)) :: tG) (hop2HaltedStTy ℓ Pt)))
    (.fst .v0) (.snd .v0)
  have hdl := cost_hop2DlArmC_tight C K Dh encPt encT decT lam M q k
  have hkemDl := kemOnDeliverPostAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q
    (.fst (.v3 : Expr AOps (tDlOut :: tDlIn :: .opt .nat :: tDlArg ::
      .sum tDlArg (.sum (.prod .bool (B 32)) .bool) ::
      .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
        (.sum tDlArg (.sum (.prod .bool (B 32)) .bool)) :: tG) tDlArg))
    .v2 (.fst (.snd (.fst .v0)))
    (hstTr C K Dh encPt encT decT lam .v6)
  have hij := cost_hop2IjArmC_tight C K Dh encPt encT decT lam M q qep k
  dsimp only [hop2StepTrackC, CoinI, tCr] at htr hch hcr ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (trPreE2EC C K encT decT qep) = trPreC at htr ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (chPreE2EC C K encT decT qep) = chPreC at hch ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (drCrArmC q (.fst .v0) (.snd .v0)) = crArmC at hcr ⊢
  generalize hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q false = sndFC at hsndF ⊢
  generalize hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q true = sndTC at hsndT ⊢
  generalize findHonestWireIdxE C K Dh encPt encT decT lam q _ _ _ = findE at hfind ⊢
  generalize hop2DlArmC C K Dh encPt encT decT lam M q k = dlC at hdl ⊢
  generalize kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ _ = kemDlE at hkemDl ⊢
  generalize hop2IjArmC C K Dh encPt encT decT lam M q qep k = ijC at hij ⊢
  simp only [hstBase, hstSessionTr, hstTr, hstWires, hstMk, stS, stGs, stAux, stChall, stMk,
    M.embedCoin_cost, wk1Comp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
    at hfind hkemDl ⊢
  omega

theorem max_hop2StepTrackC_cost_le_tier1 {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') (hℓ : ℓ < 10 ^ 6) (hk : k < 16) :
    max 1 ((hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k).cost + 16) ≤
      5560000 + 1010 * q + 64 * bits qep' := by
  have hstep := cost_hop2StepTrackC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k
  have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
  have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
    (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
  have hbk : bits k ≤ 4 := (bits_mono (by omega : k ≤ 15)).trans (by decide : bits 15 ≤ 4)
  have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
  generalize (hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k).cost = cStep
    at hstep ⊢
  omega

theorem cost_hop2InitBodyTrackC_tight (k : ℕ) :
    (hop2InitBodyTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤
      70000 := by
  have hgs1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
    (noKemKeyGenExpr_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := cost_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
    (encT := encT) idA idB
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  have htr0 := initKemTrackAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ6) .v1
  have hck1 :
      ((if k = 0 then .snd (.snd .v6) else .v0) : Expr AOps Γ6 BV256).cost ≤ 3 := by
    split_ifs <;> simp [Expr.cost, Expr.v0, Expr.v6]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2InitBodyTrackC]
  generalize initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps Γ6 BV256) = tr0 at htr0 ⊢
  simp only [hstMk, stMk, auxMk, Comp.cost, drawBoolCoin_cost, draw256Coin_cost, wk1Expr_cost,
    cost_sGroupOp, _root_.ReductionDsl.AtomicGroupOp.cost,
    cost_sPureOp, _root_.ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    hb0, hb1] at hck1 htr0 ⊢
  omega

theorem cost_hop2InitPrfTrackC_tight (k : ℕ) :
    (hop2InitPrfTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤
      70100 := by
  have hb := cost_hop2InitBodyTrackC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  dsimp only [hop2InitPrfTrackC]
  rw [cost_compCoinToPrf]
  simp only [Comp.cost, draw256Coin_cost, wk1Comp_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

end Tier1Tight

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier1Tight
