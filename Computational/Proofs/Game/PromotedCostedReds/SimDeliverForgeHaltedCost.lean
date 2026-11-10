/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Static Cost, Size, Query, and `GRedBounded` Proofs for `SimDeliverForgeHalted`

Proves total query, execution cost, syntactic size, and `GRedBounded` bounds for
`simDeliverForgeRedProgHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCost

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ops Iface Ty Expr Comp Var CostedReduction bits
  reductionSizeBudget isGameQuery atomicSig atomicSessionOps fig8SmIfaceDF e2eSessionCodec
  PlainT BV256 BV512 U32 B smQT lpubT fig8CtT)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (pGet pSet sendsInE)
open CryptoGames.SM.Construction.DeliverForge (MakesAtMostQueriesDF specDF)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (GRedBounded ratchetCostBudget ratchetCostBudget_pos)
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_mul_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSamplers_sizeHonest atomicSessionOps_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (sessPureOp sessSpqrKemOp atomicDraw256 atomicDraw256_cost atomicDraw256_queries_zero)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
   dummyBoolSessionRed_size_le session_cost_le_ratchetCostBudget)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simMirT simBaseT keptT initSimCE cost_initSimCE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (mWin mEpoch mIdx mSafeChE mEpMgmtE mRecordE mNoBobEpoch0E
   ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk
   scBase scKept scSent scSnaps scMk)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
  (optBytesLitE mkPubAtomicC mkPubAtomicC_queries toWireAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (f8Id f8VS f8Tcur keptSendAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle (dfFullT)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorrCost
  (dfOrE dfIsSomeE dfNatNeE dfSmRNoneE dfSmRSendSomeE dfIdxPredU32E dfPostSendArgT dfPostSendStateE)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr
  (simDeliverForgeSendCorrSpec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost (dfRecvOutT)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd
  (dfRecvHookC dfRecvHookC_queries dfRecvHookC_cost dfRecvHookC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeBase
  (two_mul_expr_size_le_atomicExprDescBits two_mul_comp_size_le_atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
  (kemTrackT initKemTrackAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
  (initKemTrackAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
  (boolEqE trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand trMk
   ekSideIsAE isKeysUnsampledV1E isHeaderReceivedV1E encRandBvAtomicE
   nextKemCoinsAtomicE stepPostKemSendE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (findRevHonestIdxE kemOnDeliverPostAtomicE findRevHonestIdxE_cost
   findRevHonestIdxE_descBits_le kemOnDeliverPostAtomicE_cost kemOnDeliverPostAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailBadHalted
  (honestExchangeFailsPolyC honestExchangeFailsPolyC_queries_zero
   honestExchangeFailsPolyC_cost_le honestExchangeFailsPolyC_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
  (dfHaltedT nextKemCandPolyC stepKemFailSendPolyC dfDrawRqC dfDrawRcOptC
   dfSendHaltedInpT dfSendStepHaltedC wkTop1CompH smRRecvPackEH
   dfSendArgTH dfRecvArgTH classifySmQEH dfStepHaltedC
   simDeliverForgeInitHaltedC simDeliverForgeFinishHaltedC simDeliverForgeRedProgHalted)

private theorem hopAOps {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (o : (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op) :
    2 * (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).opSize o ≤
      atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o := by
  rcases o with (((o | (_ | _)) | _) | (_ | _)) | _
  · cases o <;>
      dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
        _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
        Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize,
        atomicSessionOpDescBits, KemFailRedLoopAndCost.atomicPureOpDescBits] <;> omega
  · change 2 * 0 ≤ 8 + 5; omega
  · change 2 * 0 ≤ KemFailRedLoopAndCost.atomicSymOpDescBits _ + 5; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 1; omega

noncomputable section
set_option linter.unusedSectionVars false

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "DFIface" => fig8SmIfaceDF ℓ Pt

private theorem hb0_bits : bits 0 = 1 := by decide
private theorem hb1_bits : bits 1 = 1 := by decide
private theorem hb2_bits : bits 2 = 2 := by decide

private theorem nextKemCandPolyC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (nextKemCandPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) trE qBE rqE).queries w ws = 0 := by
  simp [nextKemCandPolyC, Comp.queries, honestExchangeFailsPolyC_queries_zero]

private theorem stepKemFailSendPolyC_queries_zero (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (stepKemFailSendPolyC q (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) trE qBE rqE).queries w ws = 0 := by
  simp [stepKemFailSendPolyC, Comp.queries, nextKemCandPolyC_queries_zero]

private theorem dfDrawRqC_queries_zero {Γ : List (Ty ASig)}
    (rE : Expr AOps Γ (.opt BV512)) (w : (fig8SmIfaceDF ℓ Pt).Tag → ℕ) :
    (dfDrawRqC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) rE).queries w (fun _ => 0) = 0 := by
  simp [dfDrawRqC, Comp.queries]

private theorem dfDrawRcOptC_queries_zero {Γ : List (Ty ASig)}
    (rE : Expr AOps Γ (.opt BV512)) (w : (fig8SmIfaceDF ℓ Pt).Tag → ℕ) :
    (dfDrawRcOptC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) rE).queries w (fun _ => 0) = 0 := by
  simp [dfDrawRcOptC, Comp.queries]

private theorem dfSendStepHaltedC_queries (idA idB : IdentityKey) (qep q : ℕ)
    {Γ : List (Ty ASig)}
    (stHaltedE : Expr AOps Γ (dfHaltedT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (dfSendStepHaltedC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      idA idB qep q stHaltedE qE m0E chalE rE).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp only [dfSendStepHaltedC, Comp.queries, dfDrawRqC_queries_zero,
    stepKemFailSendPolyC_queries_zero, dfDrawRcOptC_queries_zero, mkPubAtomicC_queries]
  omega

private theorem dfStepHaltedC_queries (idA idB : IdentityKey) (qep q : ℕ) :
    (dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  let Γs : List (Ty ASig) := [dfSendArgTH ℓ Pt, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty ASig) :=
    [.bool, .sum (dfRecvArgTH ℓ Pt) .bool, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hs := dfSendStepHaltedC_queries (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γs)
    (.var (.succ .zero)) (.fst (.var .zero)) (.fst (.snd (.var .zero)))
    (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  have hr :
      Comp.queries (O := AOps) (I := DFIface) (fun _ => 1) (fun _ => 0)
        (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤ 1 :=
    dfRecvHookC_queries (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q
  have hc := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hcorr_q
    (Γ := Γc) (.fst (.var (.succ (.succ .zero)))) (.var .zero)
  simp only [dfStepHaltedC, wkTop1CompH, Comp.queries, Comp.renameM_queries] at hs hr hc ⊢
  omega

theorem simDeliverForgeInitHaltedC_queries_zero
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (w : (fig8SmIfaceDF ℓ Pt).Tag → ℕ) :
    (simDeliverForgeInitHaltedC (ℓ := ℓ) (Pt := Pt)
      C K Dh encPt encT decT lam).queries w (fun _ => 0) = 0 := by
  simp [simDeliverForgeInitHaltedC, Comp.queries, atomicDraw256_queries_zero]

theorem simDeliverForgeFinishHaltedC_queries_zero
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (w : (fig8SmIfaceDF ℓ Pt).Tag → ℕ) :
    (simDeliverForgeFinishHaltedC (ℓ := ℓ) (Pt := Pt)
      C K Dh encPt encT decT lam).queries w (fun _ => 0) = 0 :=
  rfl

theorem simDeliverForgeRedProgHalted_totalQueries_le
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    (simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  unfold simDeliverForgeRedProgHalted
  split_ifs with hℓ
  · simp only [CostedReduction.totalQueries, simDeliverForgeInitHaltedC_queries_zero,
      simDeliverForgeFinishHaltedC_queries_zero, zero_add, add_zero]
    have hs := dfStepHaltedC_queries (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q
    exact le_trans (Nat.mul_le_mul_left q hs) (by omega)
  · rw [dummyBoolSessionRed_totalQueries]
    exact Nat.zero_le q

theorem simDeliverForgeRedProgHalted_makesAtMostQueriesDF
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    MakesAtMostQueriesDF
      ((simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) q := by
  rw [CryptoGames.Ratchet.LibsignalSim.makesAtMostQueriesDF_iff_isGameQuery]
  have hA' := SessionProgCommon.isQueryBoundP_of_makesAtMostQueries hq
  have h := CostedReduction.queryBound_eval
    (simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q)
    (isGameQuery (G := specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [isGameQuery, OracleComp.isQueryBoundP_query_iff])
    (fun _ => A) q (fun _ => hA') ()
  exact h.mono
    (simDeliverForgeRedProgHalted_totalQueries_le C K idA idB Dh encPt encT decT lam qep q)

private theorem stepKemFailSendPolyC_cost_le (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendPolyC q (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) trE qBE rqE).cost ≤
      trE.cost + qBE.cost + rqE.cost + 4 * q + 1160000 := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γc := BV512 :: Ty.sum BV512 (.prod BV512 BV256) ::
    Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ0
  have hhon := honestExchangeFailsPolyC_cost_le (I := I) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γc) .v0
    (encRandBvAtomicE (.snd (.snd .v2)))
  dsimp only [stepKemFailSendPolyC, nextKemCandPolyC, stepPostKemSendE, nextKemCoinsAtomicE,
    encRandBvAtomicE, isKeysUnsampledV1E, isHeaderReceivedV1E, ekSideIsAE, boolEqE,
    trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, trE_cand, trMk, pGet, pSet] at hhon ⊢
  generalize honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) .v0 _ = cHon at hhon ⊢
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  simp only [SimFig8State.cost_eLet, SimFig8State.cost_sOpSpqr, SimFig8State.cost_sOpPure,
    _root_.ReductionDsl.AtomicSpqrKemOp.cost, _root_.ReductionDsl.AtomicPureOp.cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, List.length_singleton,
    hb1_bits, hb2_bits, hp1, hp32, hp64] at hhon ⊢
  omega

private theorem dfIdxPredU32E_cost_local {Γ : List (Ty ASig)} (idxE : Expr AOps Γ .nat) :
    (dfIdxPredU32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idxE).cost ≤ idxE.cost + 50 := by
  simp only [dfIdxPredU32E, SimFig8State.cost_eLet, SimFig8State.cost_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.cost, Expr.v0, Expr.cost, hb1_bits]
  omega

private theorem dfDrawRqC_cost {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512)) :
    (dfDrawRqC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rE).cost ≤ rE.cost + 50 := by
  dsimp only [dfDrawRqC, fig8SmIfaceDF, _root_.ReductionDsl.atomicSamplers,
    _root_.ReductionDsl.unifSamplers, _root_.ReductionDsl.AtomicUnifBase.cost,
    Expr.v0, Comp.cost, Expr.cost]
  omega

private theorem dfDrawRcOptC_cost {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512)) :
    (dfDrawRcOptC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rE).cost ≤ rE.cost + 50 := by
  dsimp only [dfDrawRcOptC, fig8SmIfaceDF, _root_.ReductionDsl.atomicSamplers,
    _root_.ReductionDsl.unifSamplers, _root_.ReductionDsl.AtomicUnifBase.cost,
    Expr.v0, Comp.cost, Expr.cost]
  omega

private theorem dfPostSendStateE_cost_local (idA idB : IdentityKey) (hℓ : ℓ < 10 ^ 6)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (isChallE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (dfPostSendStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB stE s1E qE m0E isChallE pq'E pnE cE).cost ≤
      stE.cost + s1E.cost + qE.cost + m0E.cost + isChallE.cost + pq'E.cost + pnE.cost +
        cE.cost + 700000 := by
  let _ := hℓ
  let Γ1 := dfPostSendArgT ℓ Pt :: Γ
  let Γ2 := B (ℓ := ℓ) (Pt := Pt) 32 :: Γ1
  have hw := SimFig8WireSnap.toWireAtomicE_cost
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := Γ1) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  let s1' : Expr AOps Γ2 (simMirT ℓ Pt) := .fst (.snd .v1)
  let q1 : Expr AOps Γ2 .bool := .fst (.snd (.snd .v1))
  let recE : Expr AOps Γ2 (SimFig8LoopAndCost.simRecT ℓ Pt) :=
    .pair (.pair q1 (.pair (pGet (mEpoch s1') q1) (.add (pGet (mIdx s1') q1) (.nat 1))))
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)
  have hmr := SimFig8State.cost_mRecordE s1' q1 recE (.fst (.snd (.snd (.snd (.snd .v1)))))
  have hks := SimFig8Kept.keptSendAtomicE_cost
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ2) (pGet (scKept (.fst (.fst .v1))) q1)
  dsimp only [Γ1, Γ2, s1', q1, recE, pGet, mEpoch, mIdx, scKept,
    Expr.v0, Expr.v1, Expr.cost] at hw hmr hks
  simp only [hb1_bits] at hmr
  dsimp only [dfPostSendStateE, dfSmRSendSomeE, pGet, pSet, sendsInE,
    scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, ssMk,
    mEpoch, mIdx, f8Id, f8VS, f8Tcur, Expr.v0, Expr.v1, Expr.v2]
  generalize toWireAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = ew at hw ⊢
  generalize mRecordE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emr at hmr ⊢
  generalize keptSendAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ = eks at hks ⊢
  simp only [SimFig8State.cost_eLet, Expr.cost, hb0_bits, hb1_bits, hb2_bits]
  omega

private theorem dfSendStepHaltedC_cost (idA idB : IdentityKey) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    {Γ : List (Ty ASig)}
    (stHaltedE : Expr AOps Γ (dfHaltedT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (dfSendStepHaltedC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      idA idB qep q stHaltedE qE m0E chalE rE).cost ≤
      stHaltedE.cost + qE.cost + m0E.cost + chalE.cost + rE.cost +
        10000000 + 100 * q + 512 * bits (qep + 1) := by
  have hbqep : bits qep ≤ bits (qep + 1) := bits_mono (Nat.le_succ qep)
  let inpT := dfSendHaltedInpT ℓ Pt
  let trPairT : Ty ASig := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)
  let pubPairT : Ty ASig := .prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))
  let Γ0 := inpT :: Γ
  let Γ1 := simMirT ℓ Pt :: Γ0
  let Γ2 := BV512 (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := trPairT :: Γ2
  let Γ4 := Ty.opt (BV256 (ℓ := ℓ) (Pt := Pt)) :: Γ3
  let Γ5 := U32 (ℓ := ℓ) (Pt := Pt) :: Γ4
  let Γ6 := Ty.opt pubPairT :: Γ5
  let Γ7 := pubPairT :: Γ6
  let Γ8 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ7
  let Γ9 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ8
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst (.fst (.fst .v0))))
  let q0 : Expr AOps Γ0 .bool := .fst (.snd .v0)
  have hmnb := SimFig8State.cost_mNoBobEpoch0E mir0 q0
  have hmep := SimFig8State.cost_mEpMgmtE
    qep mir0 q0 (dfIsSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hmsc := SimFig8State.cost_mSafeChE (O' := AOps) (Γ := Γ1) .v0 (.fst (.snd .v1))
  have hdrq := dfDrawRqC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.snd (.snd (.snd .v1))))
  have htrk := stepKemFailSendPolyC_cost_le q (I := DFIface) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    (.snd (.fst .v2)) (.fst (.snd .v2)) .v0
  have hdrc := dfDrawRcOptC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) (.snd (.snd (.snd (.snd .v3))))
  let inp4 : Expr AOps Γ4 inpT := .var (.succ (.succ (.succ (.succ .zero))))
  let mir4 : Expr AOps Γ4 (simMirT ℓ Pt) := ssMir (scBase (.fst (.fst (.fst inp4))))
  let q4 : Expr AOps Γ4 .bool := .fst (.snd inp4)
  let pn4 : Expr AOps Γ4 U32 :=
    .ite (dfNatNeE (pGet (mEpoch .v3) q4) (pGet (mEpoch mir4) q4))
      (dfIdxPredU32E (pGet (mIdx mir4) q4))
      (pGet (ssPn (scBase (.fst (.fst (.fst inp4))))) q4)
  have hpn4 : pn4.cost ≤ 150 := by
    have hidx := dfIdxPredU32E_cost_local (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ4) (pGet (mIdx mir4) q4)
    dsimp only [inpT, trPairT, Γ0, Γ1, Γ2, Γ3, Γ4, inp4, mir4, q4, pn4, dfNatNeE, dfOrE,
      pGet, mEpoch, mIdx, ssPn, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
      Expr.cost] at hidx ⊢
    generalize dfIdxPredU32E (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ = eidx at hidx ⊢
    simp only [SimFig8State.cost_eLet, Expr.cost]
    omega
  let inp5 : Expr AOps Γ5 inpT := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
  let base5 : Expr AOps Γ5 (simBaseT ℓ Pt) := scBase (.fst (.fst (.fst inp5)))
  let q5 : Expr AOps Γ5 .bool := .fst (.snd inp5)
  let addr5 : Expr AOps Γ5 (.opt (B 32)) :=
    .ite (.and (.not q5) (ssUnackA base5)) (optBytesLitE (paramsV1 C K idA idB).addrAB) .none
  have hpub : (mkPubAtomicC DFIface
      (.pair (pGet (ssPq base5) q5) (.pair .v3 (.pair .v0 addr5)))).cost ≤ 2144300 := by
    have hm := SimFig8WireSnap.mkPubAtomicC_cost
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      DFIface (Γ := Γ5) (.pair (pGet (ssPq base5) q5) (.pair .v3 (.pair .v0 addr5)))
    have hab := SimFig8WireSnap.optBytesLitE_cost
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := Γ5) (paramsV1 C K idA idB).addrAB 36
      (SimFig8Crypto.serializedPartyAddresses_len_le_36 .A .B)
    dsimp only [inpT, trPairT, Γ0, Γ1, Γ2, Γ3, Γ4, Γ5, inp5, base5, q5, addr5,
      pGet, ssPq, ssUnackA, scBase, Expr.v0, Expr.v3] at hm hab ⊢
    generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ = eab at hab hm ⊢
    simp only [Expr.cost] at hm ⊢
    omega
  let inp9 : Expr AOps Γ9 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
  have hpost := dfPostSendStateE_cost_local (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB hℓ (Γ := Γ9)
    (.fst (.fst inp9))
    (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
    (.fst (.snd inp9)) (.fst (.snd (.snd inp9)))
    (dfIsSomeE (.fst (.snd (.snd (.snd inp9)))))
    (.fst .v2) (.var (.succ (.succ (.succ (.succ .zero))))) .v0
  dsimp only [inpT, trPairT, pubPairT, Γ0, Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7, Γ8, Γ9,
    mir0, q0, inp4, mir4, q4, pn4, inp5, base5, q5, addr5, inp9,
    dfSendStepHaltedC, dfOrE, dfIsSomeE, dfSmRNoneE, trE_cand,
    ssStopped, mWin, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    at hmnb hmep hmsc hdrq htrk hdrc hpn4 hpub hpost ⊢
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) _ _ = emnb at hmnb ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emep at hmep ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) _ _ = emsc at hmsc ⊢
  generalize dfDrawRqC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = cdrq at hdrq ⊢
  generalize stepKemFailSendPolyC q (I := DFIface) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ = ctrk at htrk ⊢
  generalize dfDrawRcOptC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = cdrc at hdrc ⊢
  generalize (Expr.ite (dfNatNeE _ _) _ _ : Expr AOps _ _) = epn4 at hpn4 ⊢
  generalize mkPubAtomicC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ = cpub at hpub ⊢
  generalize dfPostSendStateE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ _ _ _ _ = epost at hpost ⊢
  simp only [SimFig8State.cost_eLet, Comp.cost, Expr.cost]
    at hmnb hmep hmsc hdrq htrk hdrc hpn4 hpub hpost ⊢
  omega

private theorem dfStepHaltedC_cost (idA idB : IdentityKey) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q).cost ≤
      199000000 + 100000000 * q + 4096 * bits (qep + 1) := by
  let Γs : List (Ty ASig) := [dfSendArgTH ℓ Pt, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γr0 : List (Ty ASig) :=
    [dfRecvArgTH ℓ Pt, .sum (dfRecvArgTH ℓ Pt) .bool, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γr2 : List (Ty ASig) :=
    [dfRecvOutT ℓ Pt, .opt .nat, dfRecvArgTH ℓ Pt, .sum (dfRecvArgTH ℓ Pt) .bool,
      dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty ASig) :=
    [.bool, .sum (dfRecvArgTH ℓ Pt) .bool, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hs := dfSendStepHaltedC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q hℓ (Γ := Γs)
    (.var (.succ .zero)) (.fst (.var .zero)) (.fst (.snd (.var .zero)))
    (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  have hfnd := findRevHonestIdxE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr0)
    (ssHonest (scBase (.fst (.fst (.var (.succ (.succ .zero)))))))
    (.fst (.var .zero)) (.fst (.snd (.var .zero)))
  have hr :
      Comp.cost (O := AOps) (I := DFIface)
        (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤
        185000000 + 40000000 * q + 512 * bits (qep + 1) :=
    dfRecvHookC_cost (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hℓ
  have hdel := kemOnDeliverPostAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr2)
    (.fst (.var (.succ (.succ .zero))))
    (.var (.succ .zero))
    (.fst (.var .zero))
    (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
  let sc := simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q
  have hc := sc.hcorr_c hℓ (Γ := Γc) (.fst (.var (.succ (.succ .zero)))) (.var .zero)
  dsimp only [dfStepHaltedC, classifySmQEH, smRRecvPackEH, wkTop1CompH]
  generalize dfSendStepHaltedC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q _ _ _ _ _ = cSend at hs ⊢
  generalize findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ = eFnd at hfnd ⊢
  generalize dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q = cRecv
    at hr ⊢
  generalize kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ _ = eDel at hdel ⊢
  generalize sc.corrC (Γ := Γc) (.fst (.var (.succ (.succ .zero)))) (.var .zero) = cCorr at hc ⊢
  dsimp only [ssHonest, scBase] at hfnd ⊢
  simp only [Comp.cost, Expr.cost, Comp.renameM_cost] at hs hfnd hr hdel hc ⊢
  omega

theorem simDeliverForgeInitHaltedC_cost_le
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 5000 := by
  let pqA : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [BV256, .unit] (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero))
  let pqB : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [BV256, .unit] (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))
  have hc := cost_initSimCE pqA pqB
  have hcA : pqA.cost = 213 := rfl
  have hcB : pqB.cost = 213 := rfl
  have htr := initKemTrackAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := [BV256, .unit]) (.var .zero)
  have hdraw := atomicDraw256_cost (ℓ := ℓ) (Pt := Pt)
    (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (I := fig8SmIfaceDF ℓ Pt)
    (Γ := [.unit]) rfl
  dsimp only [simDeliverForgeInitHaltedC]
  generalize initKemTrackAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.var .zero) = etr at htr ⊢
  dsimp only [Comp.cost, Expr.cost] at htr ⊢
  dsimp only [pqA, pqB] at hc hcA hcB
  rw [hdraw]
  omega

theorem simDeliverForgeFinishHaltedC_cost_le
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeFinishHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 4 := by
  simp [simDeliverForgeFinishHaltedC, Comp.cost, Expr.cost]

theorem simDeliverForgeRedProgHalted_totalCost_le
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    (simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).totalCost q ≤
      ratchetCostBudget q (qep + 1) := by
  unfold simDeliverForgeRedProgHalted
  split_ifs with hℓ
  · have hi := simDeliverForgeInitHaltedC_cost_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hf := simDeliverForgeFinishHaltedC_cost_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hs := dfStepHaltedC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q hℓ
    have hmax : max 1 ((dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q).cost + 16) ≤
        199000020 + 100000000 * q + 4096 * bits (qep + 1) := by
      omega
    have htot :
        ({ σ := dfHaltedT ℓ Pt
           init := simDeliverForgeInitHaltedC C K Dh encPt encT decT lam
           handle := dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q
           finish := simDeliverForgeFinishHaltedC C K Dh encPt encT decT lam } :
          CostedReduction _ _ _ (e2eSessionCodec ℓ Pt) _ _ _ _).totalCost q ≤
        5000 + q * (199000020 + 100000000 * q + 4096 * bits (qep + 1)) + 4 := by
      dsimp only [CostedReduction.totalCost]
      have hmul := Nat.mul_le_mul_left q hmax
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q (qep + 1)
      5000 4 199000020 100000000 4096
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le (fig8SmIfaceDF ℓ Pt) rfl .unit q (qep + 1)

private theorem stepKemFailSendPolyC_size_le (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendPolyC q (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + bits (q + 1) + 920 := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γc := BV512 :: Ty.sum BV512 (.prod BV512 BV256) ::
    Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ0
  have hhon := honestExchangeFailsPolyC_size_le (I := I) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γc) .v0
    (encRandBvAtomicE (.snd (.snd .v2)))
  dsimp only [stepKemFailSendPolyC, nextKemCandPolyC, stepPostKemSendE, nextKemCoinsAtomicE,
    encRandBvAtomicE, isKeysUnsampledV1E, isHeaderReceivedV1E, ekSideIsAE, boolEqE,
    trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, trE_cand, trMk, pGet, pSet,
    SimFig8State.eLet] at hhon ⊢
  generalize honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) .v0 _ = cHon at hhon ⊢
  dsimp only [SimFig8State.sOpPure, SimFig8State.sOpSpqr, sessPureOp, sessSpqrKemOp,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hhon ⊢
  simp only [Comp.size, Expr.size, hb1_bits, hb2_bits] at hhon ⊢
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize,
    List.length_cons, List.length_nil] at trE qBE rqE cHon hhon ⊢
  omega

private theorem dfPostSendStateE_size_le_local (idA idB : IdentityKey)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (isChallE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (dfPostSendStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB stE s1E qE m0E isChallE pq'E pnE cE).size ≤
      stE.size + s1E.size + qE.size + m0E.size + isChallE.size + pq'E.size + pnE.size +
        cE.size + 850000 := by
  let Γ1 := dfPostSendArgT ℓ Pt :: Γ
  let Γ2 := B (ℓ := ℓ) (Pt := Pt) 32 :: Γ1
  let ewExpr : Expr AOps Γ1 (B 32) :=
    toWireAtomicE (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  have hw2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits ewExpr hopAOps).trans
    (SimFig8WireSnap.toWireAtomicE_descBits_le
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := Γ1) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have hw0 : atomicExprDescBits atomicSessionOpDescBits
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.v0 : Expr AOps Γ1 _))))))) :
        Expr AOps Γ1 (fig8CtT (ℓ := ℓ) (Pt := Pt))) ≤ 200 := by
    simp only [Expr.v0, KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  let s1' : Expr AOps Γ2 (simMirT ℓ Pt) := .fst (.snd .v1)
  let q1 : Expr AOps Γ2 .bool := .fst (.snd (.snd .v1))
  let recE : Expr AOps Γ2 (SimFig8LoopAndCost.simRecT ℓ Pt) :=
    .pair (.pair q1 (.pair (pGet (mEpoch s1') q1) (.add (pGet (mIdx s1') q1) (.nat 1))))
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)
  have hmr2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits
      (mRecordE s1' q1 recE (.fst (.snd (.snd (.snd (.snd .v1)))))) hopAOps).trans
    (SimFig8State.mRecordE_descBits_le atomicSessionOpDescBits
      s1' q1 recE (.fst (.snd (.snd (.snd (.snd .v1))))))
  have hmr_args :
      atomicExprDescBits atomicSessionOpDescBits s1' +
      atomicExprDescBits atomicSessionOpDescBits q1 +
      atomicExprDescBits atomicSessionOpDescBits recE +
      atomicExprDescBits atomicSessionOpDescBits
        (.fst (.snd (.snd (.snd (.snd (.v1 : Expr AOps Γ2 _))))) : Expr AOps Γ2 .bool) ≤ 1000 := by
    simp only [s1', q1, recE, pGet, mEpoch, mIdx, Expr.v0, Expr.v1,
      KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  let eksExpr : Expr AOps Γ2 (keptT ℓ Pt) :=
    keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB (pGet (scKept (.fst (.fst .v1))) q1)
  have hks2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits eksExpr hopAOps).trans
    (SimFig8Kept.keptSendAtomicE_descBits_le
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB (Γ := Γ2) (pGet (scKept (.fst (.fst .v1))) q1))
  have hks_arg : atomicExprDescBits atomicSessionOpDescBits
      (pGet (scKept (.fst (.fst (.v1 : Expr AOps Γ2 _)))) q1) ≤ 500 := by
    simp only [q1, pGet, scKept, Expr.v0, Expr.v1, KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  dsimp only [ewExpr, eksExpr, s1', q1, recE] at hw2 hmr2 hmr_args hks2 hks_arg
  dsimp only [dfPostSendStateE, dfSmRSendSomeE, pGet, pSet, sendsInE,
    scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, ssMk,
    mEpoch, mIdx, f8Id, f8VS, f8Tcur, SimFig8State.eLet, Expr.v0, Expr.v1, Expr.v2]
    at hw2 hw0 hmr2 hmr_args hks2 hks_arg ⊢
  generalize toWireAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = ew at hw2 ⊢
  generalize mRecordE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emr at hmr2 ⊢
  generalize keptSendAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ = eks at hks2 ⊢
  simp only [Expr.size, hb0_bits, hb1_bits, hb2_bits]
  omega

private theorem dfSendStepHaltedC_size_le (idA idB : IdentityKey) (qep q : ℕ)
    {Γ : List (Ty ASig)}
    (stHaltedE : Expr AOps Γ (dfHaltedT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (dfSendStepHaltedC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      idA idB qep q stHaltedE qE m0E chalE rE).size ≤
      stHaltedE.size + qE.size + m0E.size + chalE.size + rE.size +
        890000 + 8 * bits (q + 1) + 8 * bits (qep + 1) := by
  have hbqep : bits qep ≤ bits (qep + 1) := bits_mono (Nat.le_succ qep)
  let inpT := dfSendHaltedInpT ℓ Pt
  let trPairT : Ty ASig := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)
  let pubPairT : Ty ASig := .prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))
  let Γ0 := inpT :: Γ
  let Γ1 := simMirT ℓ Pt :: Γ0
  let Γ2 := BV512 (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := trPairT :: Γ2
  let Γ4 := Ty.opt (BV256 (ℓ := ℓ) (Pt := Pt)) :: Γ3
  let Γ5 := U32 (ℓ := ℓ) (Pt := Pt) :: Γ4
  let Γ6 := Ty.opt pubPairT :: Γ5
  let Γ7 := pubPairT :: Γ6
  let Γ8 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ7
  let Γ9 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ8
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst (.fst (.fst .v0))))
  let q0 : Expr AOps Γ0 .bool := .fst (.snd .v0)
  have hmnb2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits
      (mNoBobEpoch0E mir0 q0) hopAOps).trans
    (SimFig8State.mNoBobEpoch0E_descBits_le atomicSessionOpDescBits mir0 q0)
  have hmnb_args :
      atomicExprDescBits atomicSessionOpDescBits mir0 +
      atomicExprDescBits atomicSessionOpDescBits q0 ≤ 500 := by
    simp only [mir0, q0, ssMir, scBase, Expr.v0, KemFailRedLoopAndCost.varIdx,
      atomicExprDescBits]
    decide
  have hmep2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits
      (mEpMgmtE qep mir0 q0 (dfIsSomeE (.snd (.snd (.snd (.snd .v0)))))) hopAOps).trans
    (SimFig8State.mEpMgmtE_descBits_le atomicSessionOpDescBits
      qep mir0 q0 (dfIsSomeE (.snd (.snd (.snd (.snd .v0))))))
  have hmep_arg : atomicExprDescBits atomicSessionOpDescBits
      (dfIsSomeE (.snd (.snd (.snd (.snd (.v0 : Expr AOps Γ0 _)))))) ≤ 300 := by
    simp only [dfIsSomeE, Expr.v0, KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  have hmsc2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits
      (mSafeChE (O' := AOps) (Γ := Γ1) .v0 (.fst (.snd .v1))) hopAOps).trans
    (SimFig8State.mSafeChE_descBits_le atomicSessionOpDescBits
      (Γ := Γ1) (.v0 : Expr AOps Γ1 _) (.fst (.snd .v1)))
  have hmsc_args :
      atomicExprDescBits atomicSessionOpDescBits (.v0 : Expr AOps Γ1 (simMirT ℓ Pt)) +
      atomicExprDescBits atomicSessionOpDescBits (.fst (.snd (.v1 : Expr AOps Γ1 inpT))) ≤ 300 := by
    simp only [Expr.v0, Expr.v1, KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  have htrk := stepKemFailSendPolyC_size_le q (I := DFIface) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    (.snd (.fst .v2)) (.fst (.snd .v2)) .v0
  let inp5 : Expr AOps Γ5 inpT := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
  let base5 : Expr AOps Γ5 (simBaseT ℓ Pt) := scBase (.fst (.fst (.fst inp5)))
  let q5 : Expr AOps Γ5 .bool := .fst (.snd inp5)
  let addr5 : Expr AOps Γ5 (.opt (B 32)) :=
    .ite (.and (.not q5) (ssUnackA base5)) (optBytesLitE (paramsV1 C K idA idB).addrAB) .none
  have hpub : (mkPubAtomicC DFIface
      (.pair (pGet (ssPq base5) q5) (.pair .v3 (.pair .v0 addr5)))).size ≤ 15000 := by
    have hm2 := (two_mul_comp_size_le_atomicCompDescBits
        atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (mkPubAtomicC DFIface (.pair (pGet (ssPq base5) q5) (.pair .v3 (.pair .v0 addr5))))
        hopAOps).trans
      (SimFig8WireSnap.mkPubAtomicC_descBits_le
        (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        DFIface (fun _ => 8) (fun _ => 8) (Γ := Γ5)
        (.pair (pGet (ssPq base5) q5) (.pair .v3 (.pair .v0 addr5))))
    have hab := SimFig8WireSnap.optBytesLitE_descBits_le
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := Γ5) (paramsV1 C K idA idB).addrAB
      (fun v hv => Nat.le_trans
        (SimFig8Crypto.serializedPartyAddresses_len_le_36 .A .B v hv) (by omega))
    have hp32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
    have hb5 : bits 5 = 3 := by decide
    have hb3 : bits 3 = 2 := by decide
    dsimp only [inpT, trPairT, Γ0, Γ1, Γ2, Γ3, Γ4, Γ5, inp5, base5, q5, addr5,
      pGet, ssPq, ssUnackA, scBase, Expr.v0, Expr.v3] at hm2 hab ⊢
    generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ = eab at hab hm2 ⊢
    simp only [B, KemFailRedLoopAndCost.varIdx, atomicExprDescBits,
      KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits,
      Nat.reduceAdd, hb0_bits, hb3, hb5, hp32] at hm2 ⊢
    omega
  let inp9 : Expr AOps Γ9 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
  have hpost := dfPostSendStateE_size_le_local (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ9)
    (.fst (.fst inp9))
    (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
    (.fst (.snd inp9)) (.fst (.snd (.snd inp9)))
    (dfIsSomeE (.fst (.snd (.snd (.snd inp9)))))
    (.fst .v2) (.var (.succ (.succ (.succ (.succ .zero))))) .v0
  dsimp only [inpT, trPairT, pubPairT, Γ0, Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7, Γ8, Γ9,
    mir0, q0, inp5, base5, q5, addr5, inp9,
    dfSendStepHaltedC, dfDrawRqC, dfDrawRcOptC, dfIdxPredU32E,
    dfOrE, dfIsSomeE, dfNatNeE, dfSmRNoneE, trE_cand, SimFig8State.eLet,
    SimFig8State.sOpPure, sessPureOp, pGet, mEpoch, mIdx, ssPn, ssStopped, mWin, ssMir, scBase,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    at hmnb2 hmnb_args hmep2 hmep_arg hmsc2 hmsc_args htrk hpub hpost ⊢
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) _ _ = emnb at hmnb2 ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emep at hmep2 ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) _ _ = emsc at hmsc2 ⊢
  generalize stepKemFailSendPolyC q (I := DFIface) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ = ctrk at htrk ⊢
  generalize mkPubAtomicC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ = cpub at hpub ⊢
  generalize dfPostSendStateE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ _ _ _ _ = epost at hpost ⊢
  simp only [Comp.size, Expr.size, hb1_bits]
    at hmnb2 hmnb_args hmep2 hmep_arg hmsc2 hmsc_args htrk hpub hpost ⊢
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize]
    at stHaltedE qE m0E chalE rE emnb emep emsc ctrk cpub epost
       hmnb2 hmnb_args hmep2 hmep_arg hmsc2 hmsc_args htrk hpub hpost ⊢
  omega

private theorem renameM_size_eq {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (c : Comp O I Γ t) :
    (Comp.renameM f c).size = c.size :=
  Comp.renameM_size f c

private theorem dfStepHaltedC_size_le (idA idB : IdentityKey) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q).size ≤
      2 ^ 21 + 3800 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have hbqep : bits (qep + 1) ≤ bits (ratchetCostBudget q (qep + 1) + (qep + 1)) :=
    bits_mono (Nat.le_add_left _ _)
  have hbq1 : bits (q + 1) ≤ bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
    have hpos := ratchetCostBudget_pos q (qep + 1)
    exact bits_mono (by omega)
  have hbq : bits q ≤ bits (q + 1) := bits_mono (Nat.le_succ q)
  let Γs : List (Ty ASig) := [dfSendArgTH ℓ Pt, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γr0 : List (Ty ASig) :=
    [dfRecvArgTH ℓ Pt, .sum (dfRecvArgTH ℓ Pt) .bool, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γr2 : List (Ty ASig) :=
    [dfRecvOutT ℓ Pt, .opt .nat, dfRecvArgTH ℓ Pt, .sum (dfRecvArgTH ℓ Pt) .bool,
      dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty ASig) :=
    [.bool, .sum (dfRecvArgTH ℓ Pt) .bool, dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hs := dfSendStepHaltedC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γs)
    (.var (.succ .zero)) (.fst (.var .zero)) (.fst (.snd (.var .zero)))
    (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  have hfnd2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits
      (findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr0)
        (ssHonest (scBase (.fst (.fst (.var (.succ (.succ .zero)))))))
        (.fst (.var .zero)) (.fst (.snd (.var .zero))))
      hopAOps).trans
    (findRevHonestIdxE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr0)
      (ssHonest (scBase (.fst (.fst (.var (.succ (.succ .zero)))))))
      (.fst (.var .zero)) (.fst (.snd (.var .zero))))
  have hfnd_args :
      atomicExprDescBits atomicSessionOpDescBits
        (ssHonest (scBase (.fst (.fst (.var (.succ (.succ .zero)) : Expr AOps Γr0 _))))) +
      atomicExprDescBits atomicSessionOpDescBits (.fst (.var .zero : Expr AOps Γr0 _)) +
      atomicExprDescBits atomicSessionOpDescBits (.fst (.snd (.var .zero : Expr AOps Γr0 _))) ≤
      500 := by
    simp only [ssHonest, scBase, KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  have hr2 := (two_mul_comp_size_le_atomicCompDescBits
      atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q)
      hopAOps).trans
    (dfRecvHookC_descBits_le (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hℓ)
  have hdel2 := (two_mul_expr_size_le_atomicExprDescBits atomicSessionOpDescBits
      (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr2)
        (.fst (.var (.succ (.succ .zero))))
        (.var (.succ .zero))
        (.fst (.var .zero))
        (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
      hopAOps).trans
    (kemOnDeliverPostAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr2)
      (.fst (.var (.succ (.succ .zero))))
      (.var (.succ .zero))
      (.fst (.var .zero))
      (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
  have hdel_args :
      atomicExprDescBits atomicSessionOpDescBits
        (.fst (.var (.succ (.succ .zero)) : Expr AOps Γr2 _)) +
      atomicExprDescBits atomicSessionOpDescBits (.var (.succ .zero) : Expr AOps Γr2 _) +
      atomicExprDescBits atomicSessionOpDescBits (.fst (.var .zero : Expr AOps Γr2 _)) +
      atomicExprDescBits atomicSessionOpDescBits
        (.snd (.var (.succ (.succ (.succ (.succ .zero)))) : Expr AOps Γr2 _)) ≤ 500 := by
    simp only [KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  let sc := simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q
  have hc2 := (two_mul_comp_size_le_atomicCompDescBits
      atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (sc.corrC (Γ := Γc) (.fst (.var (.succ (.succ .zero)))) (.var .zero))
      hopAOps).trans
    (sc.hcorr_d hℓ (Γ := Γc) (.fst (.var (.succ (.succ .zero)))) (.var .zero))
  have hc_args :
      atomicExprDescBits atomicSessionOpDescBits
        (.fst (.var (.succ (.succ .zero)) : Expr AOps Γc _)) +
      atomicExprDescBits atomicSessionOpDescBits (.var .zero : Expr AOps Γc _) ≤ 200 := by
    simp only [KemFailRedLoopAndCost.varIdx, atomicExprDescBits]
    decide
  dsimp only [dfStepHaltedC, classifySmQEH, smRRecvPackEH, wkTop1CompH]
  generalize dfSendStepHaltedC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q _ _ _ _ _ = cSend at hs ⊢
  generalize findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ = eFnd at hfnd2 ⊢
  generalize dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q = cRecv
    at hr2 ⊢
  generalize kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ _ = eDel at hdel2 ⊢
  generalize sc.corrC (Γ := Γc) (.fst (.var (.succ (.succ .zero)))) (.var .zero) = cCorr at hc2 ⊢
  simp only [Comp.size, Expr.size, renameM_size_eq] at hs hfnd2 hr2 hdel2 hc2 ⊢
  omega

theorem simDeliverForgeInitHaltedC_size_le
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 2000 := by
  dsimp only [simDeliverForgeInitHaltedC, atomicDraw256, initSimCE, SimFig8LoopAndCost.initSimMirE,
    SimFig8LoopAndCost.keptUnknownE, initKemTrackAtomicE, KemFailRedInit.initV1BraidStAtomicE,
    SimFig8State.eLet, sessPureOp, sessSpqrKemOp]
  simp only [Comp.size, Expr.size, hb0_bits]
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize,
    List.length_cons, List.length_nil]
  omega

theorem simDeliverForgeFinishHaltedC_size_le
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeFinishHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 10 := by
  simp [simDeliverForgeFinishHaltedC, Comp.size, Expr.size]

theorem simDeliverForgeRedProgHalted_size_le
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 10) :
    (simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q (qep + 1)) := by
  unfold simDeliverForgeRedProgHalted
  split_ifs with hℓ
  · set B := ratchetCostBudget q (qep + 1)
    have hBpos : 16777216 * (q + 1) ≤ B := ratchetCostBudget_pos q (qep + 1)
    have hsum : B + (qep + 1) ≤ 2 * B := by omega
    have hbits : bits (B + (qep + 1)) ≤ 2 + bits B := by
      have hm1 := bits_mono hsum
      have hm2 := bits_mul_le 2 B
      rw [hb2_bits] at hm2
      exact hm1.trans hm2
    have hi := simDeliverForgeInitHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hf := simDeliverForgeFinishHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hs := dfStepHaltedC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q hℓ
    change (dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q).size ≤
      2 ^ 21 + 3800 * bits (B + (qep + 1)) at hs
    have hred : 2 ^ 21 + 2000 + 10 + 3800 * 2 ≤ reductionSizeBudget := by decide
    dsimp only [CostedReduction.size]
    omega
  · have hd := dummyBoolSessionRed_size_le
      (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt) .unit
    omega

/-- Proves `GRedBounded` for `simDeliverForgeRedProgHalted` under `hqep : qep ≤ q + 10`. -/
theorem simDeliverForgeRedProgHalted_gRedBounded
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    (simDeliverForgeRedProgHalted_totalCost_le C K idA idB Dh encPt encT decT lam qep q)
    (simDeliverForgeRedProgHalted_size_le C K idA idB Dh encPt encT decT lam qep q hqep)
    (simDeliverForgeRedProgHalted_totalQueries_le C K idA idB Dh encPt encT decT lam qep q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCost
