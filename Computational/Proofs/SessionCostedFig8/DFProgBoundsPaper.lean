/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8WeightedParts
public import Computational.Proofs.SessionCostedFig8.Bundles
public import Computational.Proofs.SessionCostedFig8.ProgBounds
public import Computational.Proofs.SessionCostedFig8.DFProgSizeBounds
public import Computational.Proofs.SessionCostedFig8.DFProgBoundsShifted
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2
import Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded cInTransitE_excessUB commitEC_excessUB_le compCostW_le_cost_add_excessUB compExcessUB compExcessUB_bind compExcessUB_caseOpt compExcessUB_caseSum compExcessUB_ite compExcessUB_query compExcessUB_ret compExcessUB_sample exprExcessUB exprExcessUB_add exprExcessUB_and exprExcessUB_anyB exprExcessUB_bool exprExcessUB_caseOpt exprExcessUB_cons exprExcessUB_eqN exprExcessUB_findB exprExcessUB_foldrB exprExcessUB_fst exprExcessUB_inl exprExcessUB_inr exprExcessUB_ite exprExcessUB_letE exprExcessUB_lt exprExcessUB_modK exprExcessUB_nat exprExcessUB_nil exprExcessUB_none exprExcessUB_not exprExcessUB_op exprExcessUB_pair exprExcessUB_snd exprExcessUB_some exprExcessUB_tget exprExcessUB_tset exprExcessUB_unit exprExcessUB_v0 exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4 exprExcessUB_v5 hooksCKAC_excessBounded hooksFSC_excessBounded hooksPRNGC_excessBounded implEC_excessUB_le initCKAEStateC_excessUB_le initFSEStateC_excessUB_le initPRNGEStateC_excessUB_le modeCfgEC_injectFullE_excessUB pureEngineExprs_excessUB vRecvC_excessUB_le)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded authOutE_cost_le bits_le_bits_qep_add bits_succ_le cCompContainsE_cost_le cGsSetWin_cost cGsSt_cost cInTransitE_cost_le cRecPos_cost cTrivialE_cost_le commitEC_cost_le esAbort_cost esG_cost esH_cost esSetG_cost esSetH_cost hooksCKAC_costBounded hooksFSC_costBounded hooksFSC_costBounded_linear hooksPRNGC_costBounded implEC_cost_le initCKAEStateC_cost_le initFSEStateC_cost_le initPRNGEStateC_cost_le isSomeE_cost mAcceptE_cost_le mAfterCorrE_cost_le mB_cost mChallContainsE_cost_le mEpMgmtE_cost_le mEpoch_cost mIdx_cost mInTransitE_cost_le mRecordE_cost_le mSafeChE_cost_le modeCfgEC_injectFullE_cost_le otherE_cost pGet_cost recPos_cost v0_cost v1_cost v2_cost v3_cost v4_cost v5_cost vRecvC_cost_le)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (bits_le_add_one compCostW_le_of_parts)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW)
open Computational.Proofs.SessionCostedFig8.DFProgBoundsShifted (compileCkaDFAtomic_gRedBounded_df compileFsDFAtomic_gRedBounded_df compilePrngDFAtomic_gRedBounded_df redCKAAuthDFShiftedDir2PaperAtomicProg_gRedBounded redCKAAuthDFShiftedPaperAtomicProg_gRedBounded redFSAuthDFShiftedDir2PaperAtomicProg_gRedBounded redFSAuthDFShiftedPaperAtomicProg_gRedBounded redPRNGAuthDFShiftedDir2PaperAtomicProg_gRedBounded redPRNGAuthDFShiftedPaperAtomicProg_gRedBounded)
open Computational.Proofs.SessionCostedFig8.ProgBounds (const_le_fig8AtomicStepBound linear_le_fig8AtomicStepBound)
open CryptoGames.SM.Construction (Header healEpoch)
open ReductionDsl (Comp CostedReduction Expr Iface Ops Sig Ty atomicFig8Ops atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest bits ckaTargetIface fig8SmCodecDF fig8SmIfaceDF fsaeadHeaderIface prngTargetIface)

@[expose] public section

namespace Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper

set_option autoImplicit false


open OracleSpec OracleComp
open _root_.ReductionDsl (Expr Comp CostedReduction atomicFig8Ops
  atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest fig8SmIfaceDF fig8SmCodecDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface bits reductionSizeBudget)
open _root_.CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey maxForwardJumps)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (smOpC smSampC smQueryC ckaOpC ckaSampC
  ckaQueryC prngQueryC fsQueryC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (compCostW
  compilePureAuxRed_totalCost_le compilePureAuxRed_totalQueries_le)
open Computational.Proofs.ReductionDsl.MacroLift (guardRed_gRedBounded)
open Computational.Proofs.SessionCostedFig8.ProgBounds (compiled_le_ratchetCostBudget
  dummy_le_ratchetCostBudget)
open Computational.Proofs.SessionCostedFig8.DFProgSizeBounds
  (challSimDF'PaperProg_size_le redCKAAuthDFPaperProg_size_le
   redPRNGAuthDFPaperProg_size_le redFSAuthDFPaperProg_size_le)

section GenericDFWrappers

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
  (idOf : Party → IdentityKey) (lam : Pt)

set_option maxRecDepth 100000 in
theorem compileSmDFAtomic_gRedBounded_df
    (R : CostedReduction (Bundles.fig8SmOpsShallow ℓ Pt)
      (CryptoGames.SM.smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.SM.smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW smOpC smSampC smQueryC R.init + compCostW smOpC smSampC smQueryC R.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.finish + 600 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileSmDFAtomic ℓ Pt C Dh encPt encT idOf lam R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileSmDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R smOpC smSampC smQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · intro o
      have h1 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqMExpr_cost ℓ Pt C Dh encPt encT lam
      have h2 := Computational.Proofs.ReductionDsl.Fig8Atomic.smEqCtExpr_cost ℓ Pt C Dh encPt encT lam
      have h3 := Computational.Proofs.ReductionDsl.Fig8Atomic.smBlankExpr_cost ℓ Pt C Dh encPt encT lam
      cases o <;> simp only [Bundles.smDFPureAuxBundle, Bundles.smOpMacro, smOpC, Expr.cost] <;> omega
    · intro s; cases s <;> simp [Bundles.smDFPureAuxBundle, Bundles.smDFSampMacro, smSampC, Comp.cost, Expr.cost]
    · intro g; cases g <;> simp [smQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · simp
    · have h1 := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R Bundles.smOpS Bundles.smSampS Bundles.smQueryS
      (Bundles.smOpMacro_size_le ℓ Pt C Dh encPt encT lam) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.smDFPureAuxBundle, Bundles.smDFSampMacro, Bundles.smSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.smQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.smDFPureAuxBundle, Bundles.smDFSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

end GenericDFWrappers

section ChallSimDFPaperParts

open Computational.Proofs.ReductionDsl.Fig8WeightedParts (compCostW_le_of_parts)
open Computational.Proofs.SessionCostedFig8.ProgBounds (const_le_fig8AtomicStepBound
  linear_le_fig8AtomicStepBound)

variable
  {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St}
  {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool}
  {eqCt : C → C → Bool}
  {blank : Msg → Msg}
  {injOK : C → Bool}
  {stOK : Party → St → Bool}
  {φ : St → Option St₂}
  {stSort : CryptoGames.SM.SMSort}
  {sampKey : ProbComp (Option Key)}
  {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

local notation "S_sm" => CryptoGames.SM.smSig Key St St₂ Msg Coins RCoins C
local notation "OO_sm" => CryptoGames.SM.smOps init send receive eqMsg eqCt blank injOK stOK φ
local notation "SQ_df" => CryptoGames.SM.smQDF Key St St₂ Msg Coins RCoins C

private lemma mCorrAllowedPaperE_cost_le' {O' : _root_.ReductionDsl.Ops S_sm} (K : ℕ) {Γ}
    (s : _root_.ReductionDsl.Expr O' Γ CryptoGames.SM.mirrorTy)
    (p : _root_.ReductionDsl.Expr O' Γ .bool) :
    (CryptoGames.SM.mCorrAllowedPaperE K s p).cost ≤ s.cost + p.cost + 20 * K + 20 := by
  have hmax34 : max 3 4 = 4 := rfl
  simp only [CryptoGames.SM.mCorrAllowedPaperE, CryptoGames.SM.mChall, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.otherE, _root_.ReductionDsl.Expr.cost,
    v0_cost, v1_cost, hmax34, Nat.reduceAdd]
  omega

private lemma simTransmitC'DFPaper_cost_le' (qep : ℕ) {Γ}
    (s : _root_.ReductionDsl.Expr OO_sm Γ CryptoGames.SM.mirrorTy)
    (arg : _root_.ReductionDsl.Expr OO_sm Γ
      (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    (CryptoGames.SM.simTransmitC'DFPaper (stSort := stSort) (sampKey := sampKey)
      (sampCoins := sampCoins) (sampRCoins := sampRCoins) 3 qep s arg).cost ≤
      s.cost + arg.cost + 5 * _root_.ReductionDsl.bits qep + 1205 := by
  have hb1 : _root_.ReductionDsl.bits 1 = 1 := rfl
  let Γ0 : List (_root_.ReductionDsl.Ty S_sm) :=
    .prod CryptoGames.SM.mirrorTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ
  let Γ1 : List (_root_.ReductionDsl.Ty S_sm) := .base .ct :: .opt (.base .ct) :: Γ0
  let Γ2 : List (_root_.ReductionDsl.Ty S_sm) := CryptoGames.SM.mirrorTy :: Γ1
  have hep := mEpMgmtE_cost_le (O' := OO_sm) qep (Γ := Γ1)
    (.fst .v2) (.fst (.snd .v2)) (.bool false)
  have hrec := mRecordE_cost_le (O' := OO_sm) (Γ := Γ2)
    .v0 (.fst (.snd .v3))
    (.pair (.pair (.fst (.snd .v3))
      (.pair (CryptoGames.SM.pGet (CryptoGames.SM.mEpoch .v0) (.fst (.snd .v3)))
        (.add (CryptoGames.SM.pGet (CryptoGames.SM.mIdx .v0) (.fst (.snd .v3))) (.nat 1))))
      (.pair (.fst (.snd (.snd .v3))) .v1))
    (.bool false)
  simp only [pGet_cost, mEpoch_cost, mIdx_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, _root_.ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hep hrec
  simp only [CryptoGames.SM.simTransmitC'DFPaper, _root_.ReductionDsl.Comp.cost,
    _root_.ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, CryptoGames.SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simChallC'DFPaper_cost_le' (qep : ℕ) {Γ}
    (s : _root_.ReductionDsl.Expr OO_sm Γ CryptoGames.SM.mirrorTy)
    (arg : _root_.ReductionDsl.Expr OO_sm Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    (CryptoGames.SM.simChallC'DFPaper (stSort := stSort) (sampKey := sampKey)
      (sampCoins := sampCoins) (sampRCoins := sampRCoins) 3 qep s arg).cost ≤
      s.cost + arg.cost + 5 * _root_.ReductionDsl.bits qep + 1405 := by
  have hb1 : _root_.ReductionDsl.bits 1 = 1 := rfl
  let Γ0 : List (_root_.ReductionDsl.Ty S_sm) :=
    .prod CryptoGames.SM.mirrorTy
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ
  let Γ1 : List (_root_.ReductionDsl.Ty S_sm) := CryptoGames.SM.mirrorTy :: Γ0
  let Γ2 : List (_root_.ReductionDsl.Ty S_sm) := .base .ct :: .opt (.base .ct) :: Γ1
  have hep := mEpMgmtE_cost_le (O' := OO_sm) qep (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.bool false)
  have hsc := mSafeChE_cost_le (O' := OO_sm) (Γ := Γ1) .v0 (.fst (.snd .v1))
  have hrec := mRecordE_cost_le (O' := OO_sm) (Γ := Γ2)
    .v2 (.fst (.snd .v3))
    (.pair (.pair (.fst (.snd .v3))
      (.pair (CryptoGames.SM.pGet (CryptoGames.SM.mEpoch .v2) (.fst (.snd .v3)))
        (.add (CryptoGames.SM.pGet (CryptoGames.SM.mIdx .v2) (.fst (.snd .v3))) (.nat 1))))
      (.pair (.ite (CryptoGames.SM.mB (.fst .v3)) (.fst (.snd (.snd (.snd .v3))))
        (.fst (.snd (.snd .v3)))) .v0))
    (.bool true)
  simp only [pGet_cost, mEpoch_cost, mIdx_cost, mB_cost, v0_cost, v1_cost, v2_cost, v3_cost,
    _root_.ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hep hsc hrec
  simp only [CryptoGames.SM.simChallC'DFPaper, mB_cost, _root_.ReductionDsl.Comp.cost,
    _root_.ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, CryptoGames.SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simDeliverCDF_cost_le' (K : ℕ) {Γ}
    (s : _root_.ReductionDsl.Expr OO_sm Γ CryptoGames.SM.mirrorTy)
    (arg : _root_.ReductionDsl.Expr OO_sm Γ (.prod .bool (.base .ct))) :
    (CryptoGames.SM.simDeliverCDF (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s arg).cost ≤ s.cost + arg.cost + 400 * K + 1000 := by
  let Γ0 : List (_root_.ReductionDsl.Ty S_sm) :=
    .prod CryptoGames.SM.mirrorTy (.prod .bool (.base .ct)) :: Γ
  let Γ1 : List (_root_.ReductionDsl.Ty S_sm) := .prod .nat (.prod .nat (.opt (.base .msg))) ::
    CryptoGames.SM.smRrTy Key St St₂ Msg Coins RCoins C ::
    .opt (CryptoGames.SM.smRrTy Key St St₂ Msg Coins RCoins C) :: Γ0
  let Γ2 : List (_root_.ReductionDsl.Ty S_sm) := CryptoGames.SM.recTy :: Γ1
  have hit := mInTransitE_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    K (Γ := Γ1) (.fst .v3) (CryptoGames.SM.otherE (.fst (.snd .v3))) (.snd (.snd .v3))
  have hcc := mChallContainsE_cost_le (O' := OO_sm) K (Γ := Γ2) (.fst .v4) (CryptoGames.SM.recPos .v0)
  have hacc := mAcceptE_cost_le (O' := OO_sm) K (Γ := Γ2)
    (.fst .v4) (.fst (.snd .v4)) (CryptoGames.SM.recPos .v0)
  simp only [otherE_cost, recPos_cost, v0_cost, v3_cost, v4_cost,
    _root_.ReductionDsl.Expr.cost, Nat.reduceAdd] at hit hcc hacc
  simp only [CryptoGames.SM.simDeliverCDF, _root_.ReductionDsl.Comp.cost,
    _root_.ReductionDsl.Expr.cost, v0_cost, v1_cost, v3_cost, CryptoGames.SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simInjectCDF_cost_le' (K : ℕ) {Γ}
    (s : _root_.ReductionDsl.Expr OO_sm Γ CryptoGames.SM.mirrorTy)
    (arg : _root_.ReductionDsl.Expr OO_sm Γ (.prod .bool (.base .ct))) :
    (CryptoGames.SM.simInjectCDF (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s arg).cost ≤ s.cost + arg.cost + 250 * K + 900 := by
  let Γ0 : List (_root_.ReductionDsl.Ty S_sm) :=
    .prod CryptoGames.SM.mirrorTy (.prod .bool (.base .ct)) :: Γ
  let Γ1 : List (_root_.ReductionDsl.Ty S_sm) := .prod .nat (.prod .nat (.opt (.base .msg))) ::
    CryptoGames.SM.smRrTy Key St St₂ Msg Coins RCoins C ::
    .opt (CryptoGames.SM.smRrTy Key St St₂ Msg Coins RCoins C) :: Γ0
  have hacc := mAcceptE_cost_le (O' := OO_sm) K (Γ := Γ1) (.fst .v3) (.fst (.snd .v3))
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst .v0) (.fst (.snd .v0))))
  simp only [otherE_cost, v0_cost, v3_cost, _root_.ReductionDsl.Expr.cost, Nat.reduceAdd] at hacc
  simp only [CryptoGames.SM.simInjectCDF, _root_.ReductionDsl.Comp.cost,
    _root_.ReductionDsl.Expr.cost, v0_cost, v1_cost, v3_cost, CryptoGames.SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simCorrCDFPaper_cost_le' (K : ℕ) {Γ}
    (s : _root_.ReductionDsl.Expr OO_sm Γ CryptoGames.SM.mirrorTy)
    (p : _root_.ReductionDsl.Expr OO_sm Γ .bool) :
    (CryptoGames.SM.simCorrCDFPaper (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s p).cost ≤ s.cost + p.cost + 420 * K + 4100 := by
  let Γ0 : List (_root_.ReductionDsl.Ty S_sm) := .prod CryptoGames.SM.mirrorTy .bool :: Γ
  let Γ1 : List (_root_.ReductionDsl.Ty S_sm) := .opt (.base stSort) :: Γ0
  have hca := mCorrAllowedPaperE_cost_le' (O' := OO_sm) K (Γ := Γ0) (.fst .v0) (.snd .v0)
  have hac := mAfterCorrE_cost_le (O' := OO_sm) K (Γ := Γ1) (.fst .v1) (.snd .v1)
  simp only [v0_cost, v1_cost, _root_.ReductionDsl.Expr.cost, Nat.reduceAdd] at hca hac
  simp only [CryptoGames.SM.simCorrCDFPaper, isSomeE_cost, _root_.ReductionDsl.Comp.cost,
    _root_.ReductionDsl.Expr.cost, v0_cost, v1_cost, CryptoGames.SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simDeliverForgeCDF_cost_le' (K : ℕ) {Γ}
    (s : _root_.ReductionDsl.Expr OO_sm Γ CryptoGames.SM.mirrorTy)
    (arg : _root_.ReductionDsl.Expr OO_sm Γ (.prod .bool (.prod (.base .ct) (.base .ct)))) :
    (CryptoGames.SM.simDeliverForgeCDF (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s arg).cost ≤ s.cost + arg.cost + 250 * K + 900 := by
  let Γ0 : List (_root_.ReductionDsl.Ty S_sm) :=
    .prod CryptoGames.SM.mirrorTy (.prod .bool (.prod (.base .ct) (.base .ct))) :: Γ
  let Γ1 : List (_root_.ReductionDsl.Ty S_sm) := .prod .nat (.prod .nat (.opt (.base .msg))) ::
    CryptoGames.SM.smRrTy Key St St₂ Msg Coins RCoins C ::
    .opt (CryptoGames.SM.smRrTy Key St St₂ Msg Coins RCoins C) :: Γ0
  have hacc := mAcceptE_cost_le (O' := OO_sm) K (Γ := Γ1) (.fst .v3) (.fst (.snd .v3))
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst .v0) (.fst (.snd .v0))))
  simp only [otherE_cost, v0_cost, v3_cost, _root_.ReductionDsl.Expr.cost, Nat.reduceAdd] at hacc
  simp only [CryptoGames.SM.simDeliverForgeCDF, _root_.ReductionDsl.Comp.cost,
    _root_.ReductionDsl.Expr.cost, v0_cost, v1_cost, v3_cost, CryptoGames.SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simHandleC'DFPaper_cost_le' (K qep : ℕ) :
    (CryptoGames.SM.simHandleC'DFPaper (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K 3 qep).cost ≤ 5 * _root_.ReductionDsl.bits qep + 420 * K + 4205 := by
  let trQ : _root_.ReductionDsl.Ty S_sm := .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
  let chQ : _root_.ReductionDsl.Ty S_sm :=
    .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
  let dlQ : _root_.ReductionDsl.Ty S_sm := .prod .bool (.base .ct)
  let dfQ : _root_.ReductionDsl.Ty S_sm := .prod .bool (.prod (.base .ct) (.base .ct))
  let s1 : _root_.ReductionDsl.Ty S_sm := .sum (.sum (.sum (.sum trQ chQ) dlQ) dlQ) .bool
  let s2 : _root_.ReductionDsl.Ty S_sm := .sum (.sum (.sum trQ chQ) dlQ) dlQ
  let s3 : _root_.ReductionDsl.Ty S_sm := .sum (.sum trQ chQ) dlQ
  let s4 : _root_.ReductionDsl.Ty S_sm := .sum trQ chQ
  have hb_tr := simTransmitC'DFPaper_cost_le' (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    qep (Γ := trQ :: s4 :: s3 :: s2 :: s1 :: [CryptoGames.SM.mirrorTy, SQ_df]) .v5 .v0
  have hb_ch := simChallC'DFPaper_cost_le' (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    qep (Γ := chQ :: s4 :: s3 :: s2 :: s1 :: [CryptoGames.SM.mirrorTy, SQ_df]) .v5 .v0
  have hb_dl := simDeliverCDF_cost_le' (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := dlQ :: s3 :: s2 :: s1 :: [CryptoGames.SM.mirrorTy, SQ_df]) .v4 .v0
  have hb_ij := simInjectCDF_cost_le' (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := dlQ :: s2 :: s1 :: [CryptoGames.SM.mirrorTy, SQ_df]) .v3 .v0
  have hb_cr := simCorrCDFPaper_cost_le' (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := .bool :: s1 :: [CryptoGames.SM.mirrorTy, SQ_df]) .v2 .v0
  have hb_df := simDeliverForgeCDF_cost_le' (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := dfQ :: [CryptoGames.SM.mirrorTy, SQ_df]) .v1 .v0
  simp only [v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost]
    at hb_tr hb_ch hb_dl hb_ij hb_cr hb_df
  simp only [CryptoGames.SM.simHandleC'DFPaper, _root_.ReductionDsl.Comp.cost,
    _root_.ReductionDsl.Expr.cost, v0_cost, v1_cost, Nat.reduceAdd]
  omega

private lemma simHandleC'DFPaper_excessUB_le' (K qep : ℕ) :
    compExcessUB smOpC smSampC smQueryC
      (CryptoGames.SM.simHandleC'DFPaper (init := init) (send := send) (receive := receive)
        (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
        (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K 3 qep) ≤ 400 * K + 1000000 := by
  simp only [CryptoGames.SM.simHandleC'DFPaper, CryptoGames.SM.simTransmitC'DFPaper,
    CryptoGames.SM.simChallC'DFPaper, CryptoGames.SM.simDeliverCDF, CryptoGames.SM.simInjectCDF,
    CryptoGames.SM.simCorrCDFPaper, CryptoGames.SM.simDeliverForgeCDF,
    CryptoGames.SM.mCorrAllowedPaperE, CryptoGames.SM.mEpMgmtE, CryptoGames.SM.mSafeChE,
    CryptoGames.SM.mLeakE, CryptoGames.SM.mRecordE, CryptoGames.SM.mInTransitE,
    CryptoGames.SM.mDeleteE, CryptoGames.SM.mAcceptE, CryptoGames.SM.mChallContainsE,
    CryptoGames.SM.mAfterCorrE, CryptoGames.SM.mMk, CryptoGames.SM.mSt, CryptoGames.SM.mB,
    CryptoGames.SM.mWin, CryptoGames.SM.mEpoch, CryptoGames.SM.mIdx, CryptoGames.SM.mTL,
    CryptoGames.SM.mTrans, CryptoGames.SM.mChall, CryptoGames.SM.mComp, CryptoGames.SM.mMaxAcc,
    CryptoGames.SM.mLeaks, CryptoGames.SM.mCorrs, CryptoGames.SM.recPos, CryptoGames.SM.recCt,
    CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
    CryptoGames.SM.maxOptE, CryptoGames.SM.maxAccSet, CryptoGames.SM.maxAccGet,
    CryptoGames.SM.posEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    CryptoGames.SM.boolEq, smOpC, smQueryC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
    exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add,
    exprExcessUB_modK, exprExcessUB_lt,
    exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
    exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_letE, exprExcessUB_op, exprExcessUB_cons,
    exprExcessUB_findB, exprExcessUB_anyB,
    exprExcessUB_foldrB, exprExcessUB_tget,
    exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
    compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_query,
    Nat.reduceAdd, Nat.zero_add, Nat.add_zero, Nat.mul_zero]
  omega

private theorem challSimDF'PaperProg_parts_le (q qep : ℕ) :
    let P := CryptoGames.SM.challSimDF'PaperProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep
    compCostW smOpC smSampC smQueryC P.init + compCostW smOpC smSampC smQueryC P.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro P
  have hi : compCostW smOpC smSampC smQueryC P.init ≤ 700 := by
    dsimp only [P, CryptoGames.SM.challSimDF'PaperProg]
    refine compCostW_le_of_parts (a := 200) (b := 500) ?_ ?_ (by omega)
    · rw [CryptoGames.SM.simInitCDF_cost]; decide
    · simp [CryptoGames.SM.simInitCDF, CryptoGames.SM.mMk, smSampC]
  have hf : compCostW smOpC smSampC smQueryC P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.challSimDF'PaperProg]
    exact compCostW_le_of_parts (a := 10) (b := 0)
      (by simp only [ReductionDsl.Comp.cost, v1_cost]; decide)
      (by simp only [compExcessUB_ret, exprExcessUB_v1]; decide) (by omega)
  have hh : compCostW smOpC smSampC smQueryC P.handle ≤
      5 * _root_.ReductionDsl.bits qep + 820 * (q + 1) + 1004205 := by
    dsimp only [P, CryptoGames.SM.challSimDF'PaperProg]
    exact compCostW_le_of_parts (simHandleC'DFPaper_cost_le' q qep)
      (simHandleC'DFPaper_excessUB_le' q qep) (by omega)
  refine ⟨(Nat.add_le_add_right (Nat.add_le_add hi hf) 100000).trans
    (const_le_fig8AtomicStepBound (by decide)), ?_⟩
  refine (Nat.add_le_add_right hh 200000).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound (k := 5) (a := 820)
    (b := 1204205) (q := q) (qep := qep) (by decide) (by decide) (by decide))
  ring

end ChallSimDFPaperParts

section DFEnginePaperParts

open _root_.ReductionDsl (Sig Ty Ops Iface bits)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (compCostW_le_of_parts bits_le_add_one)

private theorem healEpoch_le_of_getD_le_dfp {t : ℕ} {tL : Option ℕ} (h : tL.getD 0 ≤ t) :
    healEpoch tL ≤ t + 2 := by
  rcases tL with _ | l <;>
    simp only [Option.getD_none, Option.getD_some, healEpoch] at h ⊢ <;> omega

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

private theorem hdrEqE_cost_le_dfp {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (CryptoGames.SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]
  omega

private theorem deliverForgeEC_cost_le_dfp {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
      (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L + bits qep + bits mo.tStar + 5010 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) :=
    .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod hdrCtT hdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le_dfp (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2) (CryptoGames.SM.Engine.esG (.fst .v4))
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd]
    at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.posEpoch, cRecPos_cost, esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]
  omega

private theorem hdrEqE_excessUB_dfp (B0 : ℕ) {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprExcessUB (ckaOpC B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      exprExcessUB (ckaOpC B0) c₁ + exprExcessUB (ckaOpC B0) c₂ + 20 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, ckaOpC, exprExcessUB_v0, exprExcessUB_v1,
    exprExcessUB_bool, exprExcessUB_eqN, exprExcessUB_and, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
    Nat.add_zero, Nat.zero_add]
  omega

private theorem deliverForgeEC_excessUB_le_dfp {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy
        (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ'
      (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      60 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) +
        2 * Ho + Hr + 300 * L + 1000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) :=
    .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod hdrCtT hdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0))
    (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ1) (CryptoGames.SM.Engine.esG (.fst .v1))
    (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hhe1 := hdrEqE_excessUB_dfp (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) B0 (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_excessUB_le hk Ho Hs Hr L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_excessUB (O' := OO_cka) (ckaOpC B0) mo
    (Γ' := Γ2) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_v4, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_none, exprExcessUB_letE, Nat.add_zero, Nat.zero_add,
    Nat.mul_zero] at hit0 hit1 hhe1 hvr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cTrivialE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG,
    CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks,
    CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_tget,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

private theorem exprCostW_v0_dfp {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ) {t : Ty S'}
    {Γ' : List (Ty S')} : exprCostW opC (.v0 : Expr O' (t :: Γ') t) = 1 := rfl

private theorem exprCostW_v1_dfp {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ) {a t : Ty S'}
    {Γ' : List (Ty S')} : exprCostW opC (.v1 : Expr O' (a :: t :: Γ') t) = 1 := rfl

set_option maxRecDepth 100000 in
private theorem implECDF_compCostW_le_fig8AtomicStepBound_dfp {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S_cka (unifSpec + TSpec)} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hhkC : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * bits qep + B + 2500))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (300 * (q + 1) + 250000) 2000000
      (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
        6 * bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (CryptoGames.SM.Engine.implECDF
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) + 200000 ≤
      fig8AtomicStepBound q qep := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  let H := 320 * L + 10 * bits qep + B + 2500
  let Ho := 300 * L + 250000
  let Hs := 2000000
  let Hr := 500 * L + 40 * B + 6 * bits B + 5700000
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let dfqT : Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let smqDFT := CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod esT smqDFT :: [esT, smqDFT]
  let Γ_sm : List (Ty S_cka) := smqT :: Γ0
  let Γ_df : List (Ty S_cka) := dfqT :: Γ0
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have hbB := bits_le_add_one B
  have hC_sm := implEC_cost_le hk H L qep maxForwardJumps mo hhkC (Γ' := Γ_sm) (.fst .v1) .v0
  have hE_sm := implEC_excessUB_le hk Ho Hs Hr L qep maxForwardJumps mo hhkE
    (Γ' := Γ_sm) (.fst .v1) .v0
  have hW_sm := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC qC
    (CryptoGames.SM.Engine.implEC hk L 3 qep maxForwardJumps (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
      (Γ' := Γ_sm) (.fst .v1) .v0)
  have hC_df := deliverForgeEC_cost_le_dfp hk H L qep mo hhkC (Γ' := Γ_df) (.fst .v1) .v0
  have hE_df := deliverForgeEC_excessUB_le_dfp hk Ho Hs Hr L qep mo hhkE (Γ' := Γ_df) (.fst .v1) .v0
  have hW_df := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC qC
    (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo)
      (Γ' := Γ_df) (.fst .v1) .v0)
  simp only [ReductionDsl.Expr.cost, v0_cost, v1_cost] at hC_sm hC_df
  simp only [exprExcessUB_fst, exprExcessUB_v0, exprExcessUB_v1] at hE_sm hE_df
  have hmul :
      L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) ≤ L * (3 * bits qep + 60) :=
    Nat.mul_le_mul_left L (by omega)
  simp only [CryptoGames.SM.Engine.implECDF, compCostW, exprCostW, exprCostW_v0_dfp, exprCostW_v1_dfp,
    Nat.reduceAdd]
  unfold fig8AtomicStepBound
  dsimp only [L, B, H, Ho, Hs, Hr] at hC_sm hE_sm hW_sm hC_df hE_df hW_df hmul hbB ⊢
  generalize bits ((q + 1) * (maxForwardJumps + 1)) = bB at hE_sm hE_df hbB
  generalize (q + 1) * (maxForwardJumps + 1) = Bv at hC_sm hE_sm hW_sm hC_df hE_df hW_df hbB ⊢
  generalize (q + 1) * (3 * bits qep + 60) = Lbq at hmul ⊢
  omega

private theorem cCorrAllowedPaperE_costW_le_dfp {O' : Ops S_cka} {vpT : Ty S_cka}
    (opC : O'.Op → ℕ) {Γ'} (L : ℕ)
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprCostW opC (CryptoGames.SM.Engine.cCorrAllowedPaperE L s p) ≤
      exprCostW opC (CryptoGames.SM.Engine.cCorrAllowedE L s p) := by
  unfold CryptoGames.SM.Engine.cCorrAllowedPaperE CryptoGames.SM.Engine.cCorrAllowedE
  dsimp only [exprCostW]
  omega

private theorem corrECPaper_costW_le_dfp {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opC : (OO_cka).Op → ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (L : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy
        (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    compCostW opC sC qC (CryptoGames.SM.Engine.corrECPaper hk L π es p) ≤
      compCostW opC sC qC (CryptoGames.SM.Engine.corrEC hk L π es p) := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  unfold CryptoGames.SM.Engine.corrECPaper CryptoGames.SM.Engine.corrEC
  have h := cCorrAllowedPaperE_costW_le_dfp opC (vpT := vpT)
    (Γ' := .prod (CryptoGames.SM.Engine.esTy vpT hsT) .bool :: Γ') L (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  dsimp only [compCostW, exprCostW, CryptoGames.SM.orE]
  omega

private theorem implECDFPaper_costW_le_dfp {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opC : (OO_cka).Op → ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy
        (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    compCostW opC sC qC (CryptoGames.SM.Engine.implECDFPaper hk L Δ qep maxSkip cfg π es q) ≤
      compCostW opC sC qC (CryptoGames.SM.Engine.implECDF hk L Δ qep maxSkip cfg π es q) := by
  let esT := CryptoGames.SM.Engine.esTy
    (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT
  let smQ := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smQDF := CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  unfold CryptoGames.SM.Engine.implECDFPaper CryptoGames.SM.Engine.implECDF CryptoGames.SM.Engine.implECPaper CryptoGames.SM.Engine.implEC
  have h := corrECPaper_costW_le_dfp opC sC qC hk L π
    (Γ' := .bool :: .prod esT smQ :: smQ :: .prod esT smQDF :: Γ') (.fst .v1) .v0
  dsimp only [compCostW, exprCostW]
  omega

private theorem implECDFPaper_compCostW_le_fig8AtomicStepBound_dfp {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S_cka (unifSpec + TSpec)} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hhkC : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * bits qep + B + 2500))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (300 * (q + 1) + 250000) 2000000
      (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
        6 * bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (CryptoGames.SM.Engine.implECDFPaper
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) + 200000 ≤
      fig8AtomicStepBound q qep :=
  (Nat.add_le_add_right
    (implECDFPaper_costW_le_dfp (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      hk (q + 1) (2 + 1) qep maxForwardJumps (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1)
    200000).trans
    (implECDF_compCostW_le_fig8AtomicStepBound_dfp hk q qep mo htStar htL hhkC hhkE)

private theorem init_finish_le_step_dfp {q qep k1 k2 a1 a2 b1 b2 x y : ℕ}
    (hx : x ≤ k1 * bits qep + a1 * (q + 1) + b1)
    (hy : y ≤ k2 * bits qep + a2 * (q + 1) + b2)
    (hk : k1 + k2 ≤ 200) (ha : a1 + a2 ≤ 15000) (hb : b1 + b2 + 100000 ≤ 25000000) :
    x + y + 100000 ≤ fig8AtomicStepBound q qep := by
  refine (Nat.add_le_add (Nat.add_le_add hx hy) le_rfl).trans ?_
  refine (le_of_eq ?_).trans (ProgBounds.linear_le_fig8AtomicStepBound hk ha hb)
  ring

private theorem hooksCKA_mono_arith_dfp {L B bq bt btH : ℕ}
    (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    3 * btH + bt + (B + 1) + 1010 ≤ 320 * L + 10 * bq + B + 2500 := by omega

private theorem hooksPRNG_mono_arith_dfp {L B bq bt btH : ℕ}
    (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    2 * bt + 3 * btH + (B + 1) + 910 ≤ 320 * L + 10 * bq + B + 2500 := by omega

private theorem hooksFS_mono_arith_dfp {L B j bq bt btH : ℕ}
    (hj : j + 1 ≤ L) (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    300 * L + 20 * (j + 1) + 2 * bt + 2 * btH + (B + 1) + 2110 ≤
      320 * L + 10 * bq + B + 2500 := by omega

private theorem authOut_hm_dfp {L bq bt btL c : ℕ}
    (ht : bt ≤ bq + 4) (htL : btL ≤ bq + 4) (hc : c ≤ (btL + 3) + bt + 100 * L + 260) :
    c + 0 ≤ 2 * bq + 100 * L + 500 := by omega

private theorem initPRNG_hm_dfp {bq bt btH c e : ℕ}
    (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4)
    (hc : c ≤ 2 * bt + 3 * btH + 930) (he : e ≤ 3300) :
    c + e ≤ 5 * bq + 0 * 1 + 5000 := by omega

private theorem initFS_hm_dfp {L j bq bt btH c e : ℕ}
    (hj : j + 1 ≤ L) (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4)
    (hc : c ≤ 200 * L + 12 * (j + 1) + 2 * bt + 2 * btH + 2030) (he : e ≤ 200 * L + 5100) :
    c + e ≤ 4 * bq + 500 * L + 8000 := by omega

private theorem bind_ret_pair_unit_cost_le_dfp {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {σ : Ty S'}
    {c : Comp O' I' Γ' σ} {K M : ℕ} (hc : c.cost ≤ K) (hK : K + 5 ≤ M) :
    (ReductionDsl.Comp.bind c (ReductionDsl.Comp.ret (.pair .unit .v0))).cost ≤ M := by
  simp only [ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost]; omega

private theorem bind_ret_pair_unit_excess_le_dfp {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} (opC : O'.Op → ℕ) (sampC : I'.smp.Samp → ℕ)
    (qC : I'.Tag → ℕ) {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : compExcessUB opC sampC qC c ≤ K) (hK : K ≤ M) :
    compExcessUB opC sampC qC (ReductionDsl.Comp.bind c (ReductionDsl.Comp.ret (.pair .unit .v0))) ≤ M := by
  simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
    exprExcessUB_v0]; omega

private theorem comp_ret_cost_le_dfp {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {τ : Ty S'}
    {e : Expr O' Γ' τ} {K M : ℕ} (he : e.cost ≤ K) (hM : K + 1 ≤ M) :
    (ReductionDsl.Comp.ret (I := I') e).cost ≤ M := by
  simp only [ReductionDsl.Comp.cost]; omega

private theorem redCKAAuthDFPaperProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init +
        compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  have htL2 := healEpoch_le_of_getD_le_dfp htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * bits qep + B + 2500)
    (hooksCKA_mono_arith_dfp ht_bits htH_bits)
  have hhkE := (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000)
    (Hr' := 500 * L + 40 * B + 6 * bits B + 5700000)
    (by omega) (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC ckaQueryC P.init ≤
        0 * bits qep + 0 * (q + 1) + 2100 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFPaperProg]
      have hiC0 := initCKAEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
      have hiE0 := initCKAEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts (a := 520) (b := 1510) ?_ ?_ (by simp)
      · exact bind_ret_pair_unit_cost_le_dfp hiC0 (by simp only [ReductionDsl.Expr.cost]; decide)
      · exact bind_ret_pair_unit_excess_le_dfp _ _ _ hiE0 (by simp only [exprExcessUB_bool]; decide)
    have hf : compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish ≤
        2 * bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFPaperProg]
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [CryptoGames.SM.Construction.ckaEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [CryptoGames.SM.Construction.ckaEsTy, .bool])
        (ReductionDsl.Expr.v0 (O := OO_cka) (t := CryptoGames.SM.Construction.ckaEsTy))).1
      dsimp only [mo] at hfE0
      refine compCostW_le_of_parts
        (a := (bits (tL.getD 0) + 3) + bits t + 100 * L + 260)
        (b := 0) ?_ ?_ (authOut_hm_dfp ht_bits htL_bits le_rfl)
      · exact comp_ret_cost_le_dfp hfC0 (by
          simp only [v0_cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.policy]; omega)
      · simp only [compExcessUB_ret, hfE0, exprExcessUB_v0]; exact le_rfl
    exact init_finish_le_step_dfp hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redCKAAuthDFPaperProg]
    exact implECDFPaper_compCostW_le_fig8AtomicStepBound_dfp _ q qep mo ht htL hhkC hhkE

private theorem redPRNGAuthDFPaperProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC prngQueryC P.init +
        compCostW (ckaOpC B) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  have htL2 := healEpoch_le_of_getD_le_dfp htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * bits qep + B + 2500)
    (hooksPRNG_mono_arith_dfp ht_bits htH_bits)
  have hhkE := (hooksPRNGC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000)
    (Hr' := 500 * L + 40 * B + 6 * bits B + 5700000)
    (by omega) (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC prngQueryC P.init ≤
        5 * bits qep + 0 * (q + 1) + 5000 := by
      dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperProg]
      have hiC0 := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
      have hiE0 := initPRNGEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts
        (a := 2 * bits t + 3 * bits (healEpoch tL) + 930) (b := 3300) ?_ ?_
        ((initPRNG_hm_dfp ht_bits htH_bits le_rfl le_rfl).trans (by simp))
      · exact bind_ret_pair_unit_cost_le_dfp hiC0 (by
          simp only [ReductionDsl.Expr.cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.tH]; omega)
      · exact bind_ret_pair_unit_excess_le_dfp _ _ _ hiE0 (by simp only [exprExcessUB_bool]; decide)
    have hf : compCostW (ckaOpC B) ckaSampC prngQueryC P.finish ≤
        2 * bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperProg]
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @CryptoGames.SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool])
        (ReductionDsl.Expr.v0 (O := OO_cka) (t := CryptoGames.SM.Construction.prngEsTy))).1
      dsimp only [mo] at hfE0
      refine compCostW_le_of_parts
        (a := (bits (tL.getD 0) + 3) + bits t + 100 * L + 260)
        (b := 0) ?_ ?_ (authOut_hm_dfp ht_bits htL_bits le_rfl)
      · exact comp_ret_cost_le_dfp hfC0 (by
          simp only [v0_cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.policy]; omega)
      · simp only [compExcessUB_ret, hfE0, exprExcessUB_v0]; exact le_rfl
    exact init_finish_le_step_dfp hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redPRNGAuthDFPaperProg]
    exact implECDFPaper_compCostW_le_fig8AtomicStepBound_dfp _ q qep mo ht htL hhkC hhkE

private theorem redFSAuthDFPaperProg_parts_le (q qep j t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps j tL t
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init +
        compCostW (ckaOpC B) ckaSampC fsQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  have htL2 := healEpoch_le_of_getD_le_dfp htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hjL : j + 1 ≤ L := by omega
  have hhkC := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo j).mono
    (H' := 320 * L + 10 * bits qep + B + 2500)
    (hooksFS_mono_arith_dfp hjL ht_bits htH_bits)
  have hhkE := hooksFSC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B L B mo j
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC fsQueryC P.init ≤
        4 * bits qep + 500 * (q + 1) + 8000 := by
      dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFPaperProg]
      have hiC0 := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j (Γ' := [.unit]) (.bool false)
      have hiE0 := initFSEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B L mo j (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts
        (a := 200 * L + 12 * (j + 1) + 2 * bits t + 2 * bits (healEpoch tL) + 2030)
        (b := 200 * L + 5100) ?_ ?_ (initFS_hm_dfp hjL ht_bits htH_bits le_rfl le_rfl)
      · exact bind_ret_pair_unit_cost_le_dfp hiC0 (by
          simp only [ReductionDsl.Expr.cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.tH]; omega)
      · exact bind_ret_pair_unit_excess_le_dfp _ _ _ hiE0 (by simp only [exprExcessUB_bool]; omega)
    have hf : compCostW (ckaOpC B) ckaSampC fsQueryC P.finish ≤
        0 * bits qep + 0 * (q + 1) + 300 := by
      dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFPaperProg]
      exact compCostW_le_of_parts (a := 10) (b := 210)
        (by simp only [ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]; decide)
        (by simp only [compExcessUB_sample, exprExcessUB_unit, ckaSampC]; decide)
        (by simp)
    exact init_finish_le_step_dfp hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redFSAuthDFPaperProg]
    exact implECDFPaper_compCostW_le_fig8AtomicStepBound_dfp _ q qep mo ht htL hhkC hhkE

end DFEnginePaperParts

section ConcretePaperAtomicProgs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

def challSimDF'PaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  Bundles.compileSmDFAtomic ℓ Pt C Dh encPt encT idOf lam
    (CryptoGames.SM.challSimDF'PaperProg q (2 + 1) qep)

def redCKAAuthDFPaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redCKAAuthDFPaperProg (q + 1) B0 1 qep maxForwardJumps tL t)

def redCKAAuthDFCasePaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (if 2 ≤ t ∧ tL = some (t - 2) then
      CryptoGames.SM.Construction.redCKAAuthDFShiftedDir2PaperProg
        (q + 1) B0 qep maxForwardJumps (t - 1) t
    else if 3 ≤ t ∧ tL = some (t - 3) then
      CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperProg
        (q + 1) B0 1 qep maxForwardJumps (t - 2) t
    else
      CryptoGames.SM.Construction.redCKAAuthDFPaperProg
        (q + 1) B0 1 qep maxForwardJumps tL t)

def redPRNGAuthDFPaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redPRNGAuthDFPaperProg (q + 1) B0 1 qep maxForwardJumps tL t)

def redPRNGAuthDFCasePaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (if 2 ≤ t ∧ tL = some (t - 2) then
      CryptoGames.SM.Construction.redPRNGAuthDFShiftedDir2PaperProg
        (q + 1) B0 qep maxForwardJumps (t - 1) t
    else if 3 ≤ t ∧ tL = some (t - 3) then
      CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperProg
        (q + 1) B0 1 qep maxForwardJumps (t - 2) t
    else
      CryptoGames.SM.Construction.redPRNGAuthDFPaperProg
        (q + 1) B0 1 qep maxForwardJumps tL t)

def redFSAuthDFPaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redFSAuthDFPaperProg (q + 1) B0 1 qep maxForwardJumps j tL t)

def redFSAuthDFCasePaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (if 2 ≤ t ∧ tL = some (t - 2) then
      CryptoGames.SM.Construction.redFSAuthDFShiftedDir2PaperProg
        (q + 1) B0 qep maxForwardJumps j (t - 1) t
    else if 3 ≤ t ∧ tL = some (t - 3) then
      CryptoGames.SM.Construction.redFSAuthDFShiftedPaperProg
        (q + 1) B0 1 qep maxForwardJumps j (t - 2) t
    else
      CryptoGames.SM.Construction.redFSAuthDFPaperProg
        (q + 1) B0 1 qep maxForwardJumps j tL t)

theorem challSimDF'PaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (challSimDF'PaperAtomicProg Dh encPt C ℓ encT idOf lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) :=
  compileSmDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam
    (CryptoGames.SM.challSimDF'PaperProg q (2 + 1) qep) q qep q
    (challSimDF'PaperProg_parts_le q qep)
    (challSimDF'PaperProg_size_le q qep hqep)
    (CryptoGames.SM.challSimDF'PaperProg_totalQueries q (2 + 1) qep q).le

theorem redCKAAuthDFPaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redCKAAuthDFPaperAtomicProg Dh encPt C ℓ encT idOf lam qep q tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redCKAAuthDFPaperAtomicProg]
  exact compileCkaDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redCKAAuthDFPaperProg_parts_le q qep t tL ht htL)
    (redCKAAuthDFPaperProg_size_le q qep t tL ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redCKAAuthDFPaperProg_totalQueries]; omega)

theorem redCKAAuthDFCasePaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redCKAAuthDFCasePaperAtomicProg Dh encPt C ℓ encT idOf lam qep q tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  unfold redCKAAuthDFCasePaperAtomicProg; split_ifs
  · exact redCKAAuthDFShiftedDir2PaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q
      (t - 1) t ht (Nat.sub_le t 1) hqep
  · exact redCKAAuthDFShiftedPaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q
      (t - 2) t ht (Nat.sub_le t 2) hqep
  · exact redCKAAuthDFPaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q t tL ht htL hqep

theorem redPRNGAuthDFPaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFPaperAtomicProg Dh encPt C ℓ encT idOf lam qep q tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redPRNGAuthDFPaperAtomicProg]
  exact compilePrngDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redPRNGAuthDFPaperProg_parts_le q qep t tL ht htL)
    (redPRNGAuthDFPaperProg_size_le q qep t tL ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGAuthDFPaperProg_totalQueries]; omega)

theorem redPRNGAuthDFCasePaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFCasePaperAtomicProg Dh encPt C ℓ encT idOf lam qep q tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  unfold redPRNGAuthDFCasePaperAtomicProg; split_ifs
  · exact redPRNGAuthDFShiftedDir2PaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q
      (t - 1) t ht (Nat.sub_le t 1) hqep
  · exact redPRNGAuthDFShiftedPaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q
      (t - 2) t ht (Nat.sub_le t 2) hqep
  · exact redPRNGAuthDFPaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q t tL ht htL hqep

theorem redFSAuthDFPaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q j : ℕ)
    (t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redFSAuthDFPaperAtomicProg Dh encPt C ℓ encT idOf lam qep q j tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redFSAuthDFPaperAtomicProg]
  exact compileFsDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 * q)
    (redFSAuthDFPaperProg_parts_le q qep j t tL ht htL hj)
    (redFSAuthDFPaperProg_size_le q qep j t tL ht htL hj hqep)
    (by rw [CryptoGames.SM.Construction.redFSAuthDFPaperProg_totalQueries]; omega)

theorem redFSAuthDFCasePaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q j : ℕ)
    (t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redFSAuthDFCasePaperAtomicProg Dh encPt C ℓ encT idOf lam qep q j tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFCasePaperAtomicProg; split_ifs
  · exact redFSAuthDFShiftedDir2PaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q j
      (t - 1) t ht (Nat.sub_le t 1) hj hqep
  · exact redFSAuthDFShiftedPaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q j
      (t - 2) t ht (Nat.sub_le t 2) hj hqep
  · exact redFSAuthDFPaperAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q j t tL ht htL hj hqep

end ConcretePaperAtomicProgs

end Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper
