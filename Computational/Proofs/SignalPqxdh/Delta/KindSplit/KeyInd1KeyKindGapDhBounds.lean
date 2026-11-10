/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBoundsArms
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhWire
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost
import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem
public import Computational.Specifications.Pqxdh.Bound
public import Computational.Specifications.Pqxdh.Security.Headline

/-!
# Syntactic Cost, Query, Size, and Block Bounds for `fgKeyInd1KeyGapDhKindAtomicProg`

Proves the syntactic total step-cost, oracle-query (`sig`, `ddh`, `prim`), program-size,
block-size, and per-query-kind step-cost bounds for `fgKeyInd1KeyGapDhKindAtomicProg` required by
`KeyIndCostedReductionBounds`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBounds

public section

set_option autoImplicit false

open OracleSpec
open _root_.ReductionDsl (Expr Comp Var Ty Env Iface CostedReduction
  pqAtomicSig pqAtomicOps pqAtomicSamplers pqSigAndDdhIface pqKeyIndCodec
  B PB drKeyT bits bits_mono bits_mul bits_le_succ reductionSizeBudget
  pqAtomicSamplers_sizeHonest)
open _root_.SignalPqxdh (Setup QueryBudget keyIndSpec KeyIndQuery
  activeIdCount activeSpkCount activeOpkCount activeSendCount activeSendOpkCount)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit primQueryBudget
  GRedBlockBounded keyIndQueryKind keyIndKindCounts
  chalIfaceSigQueryWeight chalIfaceDdhQueryWeight chalIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps sigAndDdhOracle)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT v letV bindV caseOptV caseSumV findMV anyMV
  isSomeE eCaseOpt eAny eFind eMap litB rNone
  keyIndRespTy initQTy accQTy keyIndStateTy simTy paramsTy params2Ty gdhStateTy gdhState2Ty
  emptySimE emptyStE smMk smUpd stMk stUpd smBase paMk pa2Mk
  paU paV paUp paOpkMode
  wrapBase2 wrapSim2 corruptB testB revealB registerGdhB revealSpkB
  finishAcceptGdhC chooseArm2C bernoulliRatioGdhC
  sBool sIndex sBytes32 sRandom64 sDrKey96
  qX25519 qX25519Base qPow8 qIsCanonical qSigPkGen qSigSign qSigVerify
  qKemKeyGen qKemEncaps qKemDecaps
  fgPosTy fgPatchEntryTy drKeyTy bits_0 bits_1 bits_2 bits_3 bits_eq_log2_succ)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (
  letV_costUB bindV_costUB sIndex_costUB sBool_costUB v_costUB gPrim_costUB
  bindV_queries letV_queries caseOptV_queries findMV_queries foldMV_queries
  letV_queriesUB bindV_queriesUB caseOptV_queriesUB caseSumV_queriesUB findMV_queriesUB
  wDdhGdh wPrimGdh wsZero
  gPrim_queries_wDdhGdh gPrim_queries_wPrimGdh gPrim_queriesUB_wPrimGdh
  mkSecretPosC_chal computePosC_chal computeOptPosInitC_chal
  entryMatchesC_chal chooseInitRandC_chal
  koskBundleOkPowsC_primUB koskSenderOkPowsC_primUB
  isGameSpkC_primUB isGameOpkC_primUB partnerC_primUB
  resolveSigPkC_primUB lookupSpkSkC_primUB honestPeerC_primUB checkProvC_primUB
  findHonestC_primUB chooseInitRandC_primUB chooseRespRandC_primUB
  computePosC_primUB computeOptPosInitC_primUB mkSecretPosC_primUB mkPairPosC_primUB
  ddhEqC_primUB ddhEqOptC_primUB entryMatchesC_primUB
  sIndex_queriesUB sBool_queriesUB sBytes32_queriesUB sRandom64_queriesUB sDrKey96_queriesUB
  qX25519_queriesUB qX25519Base_queriesUB qIsCanonical_queriesUB qPow8_queriesUB
  qSigPkGen_queriesUB qSigSign_queriesUB qSigVerify_queriesUB
  qKemKeyGen_queriesUB qKemEncaps_queriesUB qKemDecaps_queriesUB)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  liftGdhComp liftGdhComp_cost
  liftGdhComp_queries_sig liftGdhComp_queries_ddh liftGdhComp_queries_prim
  sigChalQ_dsl)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  activeSigBudget fgActiveTotalIndexCount optNatMatchesE gdh1KeyActiveStateTy
  initPrin1KeyActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB genOpkActiveGdhB)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  TagLift mapExpr mapComp tlSigDdhKeyInd embedTy embedCtx
  compRename exprRename exprRename_cost compRename_cost
  mapComp_cost_eleven_mul_le mapComp_cost_two_mul_le
  mapComp_queries_le samplerZeroQueryWeight_eq
  tlSigDdhKeyInd_sigW tlSigDdhKeyInd_ddhW tlSigDdhKeyInd_primW
  compLitSize exprLitSize pqOpLitSize mapComp_size_le tlSigDdhKeyInd_sizeLe
  bits_le_bits_stepCostBudget
  gredBlockBounded_atomic_of_totalCost_le
  one_le_pqSigAndDdhIface_qCost one_le_pqAtomicSamplers_sCost)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  fgKeyInd1KeyGapDhKindAtomicProg gdh1KeyKindInitC gdh1KeyKindHandleC gdh1KeyKindFinishC
  gdh1KeyKindBaseInit initParams1KeyKindC gdhKindRoArm
  gdhKindInitPrinLeg gdhKindGenSpkLeg gdhKindGenOpkLeg gdhWrapDelegNoFgLeg
  gdhKindInitiateSessLeg gdhKindAcceptOpkSessLeg gdhKindAcceptNoOpkSessLeg
  liftSigDdhNoFgArm liftSigDdhSessArm gdh1KeyActiveKindStateTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  keyIndSentinel dispatchKeyIndQ atomicRNoneE runAt2 runAt3 runAt4)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost (
  dispatchKeyIndQ_ro_costAt_le dispatchKeyIndQ_online_costAt_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget gdhLift1Key liftGdhAtomic seqFgEntryTy fgSessCtrTy
  fgSessScanPackC fgPatchShadowC sessScanMinPredC
  roParsedPrePos160C roParsedPrePos192C roRawFallbackShadowAtomicC
  roParsedPostPosShadowAtomicC roParsedShadowAtomicC sampleDrKey96LiftC
  initiateGdhActiveShadowInnerB acceptOpkGdh2ShadowB acceptNoOpkGdhShadowB
  gdhFinishK extractMode0KC emptyFgShadowE runAt1)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost (
  roParsedShadowAtomicC_cost_le gdhFinishK_atomic_cost_le
  genSpkGdhActiveKB_atomic_cost_le initiateGdhActiveShadowInnerB_atomic_cost_le
  acceptOpkGdh2ShadowB_atomic_cost_le acceptNoOpkGdhShadowB_atomic_cost_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (
  avlSearchB192C_cost_le avlInsertAtPathC_cost_le
  avlSearchB192C_queries avlInsertAtPathC_queries
  avlSearchB192C_size_le avlInsertAtPathC_size_le)
open Computational.Proofs.ReductionDsl.KindedDispatch (costBoundedByKind_fin2_of_armCosts)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBoundsArms (
  gdhOnlineArmBudget gdhKindRoArm_cost_le gdh1KeyKindHandleC_cost_le
  gdh1KeyKindHandleC_costAt_online_le gdh1KeyKindHandleC_costAt_ro_le
  fgKeyInd1KeyGapDhKindAtomicProg_size_le_aux)

private theorem compRename_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (wQ : I.Tag → Nat) (wS : I.smp.Samp → Nat) :
    ∀ {Γ Δ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
      (ρ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp pqAtomicOps I Γ t),
      (compRename ρ c).queries wQ wS = c.queries wQ wS
  | _, _, _, _, .ret _ => rfl
  | _, _, _, _, .sample _ _ => rfl
  | _, _, _, _, .query _ _ => rfl
  | _, _, _, ρ, .bind c k => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS ρ c,
      compRename_queries wQ wS _ k]
  | _, _, _, ρ, .ite _ c d => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS ρ c,
      compRename_queries wQ wS ρ d]
  | _, _, _, ρ, .caseOpt _ c d => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS ρ c,
      compRename_queries wQ wS _ d]
  | _, _, _, ρ, .caseSum _ c d => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS _ c,
      compRename_queries wQ wS _ d]
  | _, _, _, ρ, .iter _ _ body => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS _ body]
  | _, _, _, ρ, .findM _ _ body => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS _ body]
  | _, _, _, ρ, .anyM _ _ body => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS _ body]
  | _, _, _, ρ, .mapM _ _ body => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS _ body]
  | _, _, _, ρ, .consumeFirstM _ _ body _ => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS _ body]
  | _, _, _, ρ, .foldM _ _ _ body => by
    simp only [compRename, Comp.queries, compRename_queries wQ wS _ body]

private theorem dispatchKeyIndQ_queries_le {ι : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} (S : Setup) {Γ : List (Ty pqAtomicSig)} {τ : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q))
    (wQ : I.Tag → Nat) (wS : I.smp.Samp → Nat) (M : Nat)
    (c1 c2 : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) τ)
    (c3 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) τ)
    (c4 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: Γ) τ)
    (c5 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_opk)) _root_.ReductionDsl.bundleT) :: Γ) τ)
    (c6 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_no_opk)) _root_.ReductionDsl.bundleT) :: Γ) τ)
    (c7 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_opk)) _root_.ReductionDsl.hdrT)) :: Γ) τ)
    (c8 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_no_opk)) _root_.ReductionDsl.hdrT)) :: Γ) τ)
    (c9 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT S :: Γ) τ)
    (c10 : Comp pqAtomicOps I (PB 192 :: Γ) τ)
    (c11 : Comp pqAtomicOps I (.unit :: Γ) τ)
    (c12 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT S :: Γ) τ)
    (c13 : Comp pqAtomicOps I (PB 32 :: Γ) τ)
    (c14 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) τ)
    (h1 : c1.queries wQ wS ≤ M) (h2 : c2.queries wQ wS ≤ M)
    (h3 : c3.queries wQ wS ≤ M) (h4 : c4.queries wQ wS ≤ M)
    (h5 : c5.queries wQ wS ≤ M) (h6 : c6.queries wQ wS ≤ M)
    (h7 : c7.queries wQ wS ≤ M) (h8 : c8.queries wQ wS ≤ M)
    (h9 : c9.queries wQ wS ≤ M) (h10 : c10.queries wQ wS ≤ M)
    (h11 : c11.queries wQ wS ≤ M) (h12 : c12.queries wQ wS ≤ M)
    (h13 : c13.queries wQ wS ≤ M) (h14 : c14.queries wQ wS ≤ M) :
    (dispatchKeyIndQ S qE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14).queries wQ wS ≤ M := by
  simp only [dispatchKeyIndQ, Comp.queries, compRename_queries]
  omega

private abbrev lcSigW := _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.wSig1Key
private abbrev lcDdhW := _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.wDdh1Key
private abbrev lcPrimW := _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.wPrim1Key
private abbrev lcZeroWS := _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.wsZero1Key

private theorem liftSigDdhNoFgArm_queries_le (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy))
    (w : _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag → Nat)
    (w' : pqSigAndDdhIface.Tag → Nat)
    (hw : ∀ {Γ} (g : _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
      (e : Expr pqAtomicOps Γ (embedTy (_root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))),
      (tlSigDdhKeyInd.mapQuery g e).queries w' (fun _ => 0) ≤ w g) :
    (liftSigDdhNoFgArm S payE arm).queries w' samplerZeroQueryWeight ≤
      arm.queries w lcZeroWS := by
  unfold liftSigDdhNoFgArm runAt2
  simp only [Comp.queries, compRename_queries, Nat.zero_add, Nat.add_zero,
    samplerZeroQueryWeight_eq]
  exact mapComp_queries_le tlSigDdhKeyInd w lcZeroWS w' hw arm

private theorem liftSigDdhSessArm_queries_le (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [.prod stTy fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy fgSessCtrTy)))
    (w : _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag → Nat)
    (w' : pqSigAndDdhIface.Tag → Nat)
    (hw : ∀ {Γ} (g : _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
      (e : Expr pqAtomicOps Γ (embedTy (_root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))),
      (tlSigDdhKeyInd.mapQuery g e).queries w' (fun _ => 0) ≤ w g) :
    (liftSigDdhSessArm S payE arm).queries w' samplerZeroQueryWeight ≤
      arm.queries w lcZeroWS := by
  unfold liftSigDdhSessArm runAt2
  simp only [Comp.queries, compRename_queries, Nat.zero_add, Nat.add_zero,
    samplerZeroQueryWeight_eq]
  exact mapComp_queries_le tlSigDdhKeyInd w lcZeroWS w' hw arm

private theorem bits_le_log_dh_succ {n : Nat} {S : Setup} (h : n ≤ S.N_dh) :
    bits n ≤ Nat.log 2 S.N_dh + 1 := by
  rw [bits_eq_log2_succ]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem bits_le_two_log_dh_succ {n : Nat} {S : Setup} (h : n ≤ S.N_dh * S.N_dh) :
    bits n ≤ 2 * Nat.log 2 S.N_dh + 2 := by
  have h1 : bits n ≤ bits (S.N_dh * S.N_dh) := bits_mono h
  have h2 := bits_mul S.N_dh S.N_dh
  have h3 : bits S.N_dh = Nat.log 2 S.N_dh + 1 := bits_eq_log2_succ S.N_dh
  omega

private theorem bits_keyIndSentinel_le_split (S : Setup) (b : QueryBudget) :
    bits (keyIndSentinel S b) ≤ Nat.log 2 S.N_dh + bits (min b.q_on b.q_total + 1) + 3 := by
  have hle : keyIndSentinel S b ≤ S.N_dh + (min b.q_on b.q_total + 1) := by
    unfold keyIndSentinel
    exact Nat.le_trans (Nat.min_le_right _ _) (by omega)
  by_cases hdh : S.N_dh = 0
  · have hb := bits_mono (by omega : keyIndSentinel S b ≤ min b.q_on b.q_total + 1)
    omega
  · have hpos : 1 ≤ S.N_dh := Nat.pos_of_ne_zero hdh
    have hprod1 : S.N_dh ≤ S.N_dh * (min b.q_on b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hprod2 : min b.q_on b.q_total + 1 ≤ S.N_dh * (min b.q_on b.q_total + 1) :=
      Nat.le_mul_of_pos_left _ hpos
    have hprod : S.N_dh + (min b.q_on b.q_total + 1) ≤
        2 * S.N_dh * (min b.q_on b.q_total + 1) := by linarith
    have hb1 := bits_mono (Nat.le_trans hle hprod)
    have hb2 := bits_mul (2 * S.N_dh) (min b.q_on b.q_total + 1)
    have hb3 := bits_mul 2 S.N_dh
    have hb2_val : bits 2 = 2 := by decide
    have hb_dh : bits S.N_dh = Nat.log 2 S.N_dh + 1 := bits_eq_log2_succ S.N_dh
    omega

private theorem act_bernoulliRatioGdhC_cost_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).cost ≤ 3 * bits (A + B) + 25 := by
  refine (bernoulliRatioGdhC (Δ := Δ) A B).cost_le_costUB.trans ?_
  unfold bernoulliRatioGdhC
  split_ifs with hA hB hAB
  · simp [Comp.costUB, Expr.costUB]
  · simp [Comp.costUB, Expr.costUB]
  · have hb : bits A ≤ bits (A + B) := bits_mono (Nat.le_add_right A B)
    simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    omega
  · have hb : bits B ≤ bits (A + B) := bits_mono (Nat.le_add_left B A)
    simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    omega

private theorem act_chooseArm2C_cost_le {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Δ' τ)
    (B : Nat)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).cost ≤ B)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).cost ≤ B) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).cost ≤ 3 * bits (w1 + w2) + B + 30 := by
  unfold chooseArm2C
  split_ifs with hw1 hw2
  · exact (hc2 (Δ' := Δ)).trans (by omega)
  · exact (hc1 (Δ' := Δ)).trans (by omega)
  · have hb := act_bernoulliRatioGdhC_cost_le (Δ := Δ) w1 w2
    have h1 := hc1 (Δ' := .bool :: Δ)
    have h2 := hc2 (Δ' := .bool :: Δ)
    simp only [bindV, v, Comp.cost, Expr.cost]
    omega

private theorem initParams1KeyKindC_cost_le_split (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32))) :
    (initParams1KeyKindC S b (Δ := Δ) uv).cost ≤
      20 * Nat.log 2 S.N_dh + 4 * bits (min b.q_on b.q_total + 1) + 200 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hd2 : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hId : activeIdCount S b.q_on ≤ S.N_id := Nat.min_le_right _ _
  have hSpk : activeSpkCount S b.q_on ≤ S.N_spk_tot := Nat.min_le_right _ _
  have hOpk : activeOpkCount S b.q_on ≤ S.N_opk_tot := Nat.min_le_right _ _
  have hSend : activeSendCount S b.q_on ≤ S.N_send_tot := Nat.min_le_right _ _
  have hSendO : activeSendOpkCount S b.q_on ≤ S.N_send_opk_tot := Nat.min_le_right _ _
  have bId := bits_le_log_dh_succ (S := S) (by omega : activeIdCount S b.q_on ≤ S.N_dh)
  have bSpk := bits_le_log_dh_succ (S := S) (by omega : activeSpkCount S b.q_on ≤ S.N_dh)
  have bOpk := bits_le_log_dh_succ (S := S) (by omega : activeOpkCount S b.q_on ≤ S.N_dh)
  have bSend := bits_le_log_dh_succ (S := S) (by omega : activeSendCount S b.q_on ≤ S.N_dh)
  have bSendO := bits_le_log_dh_succ (S := S) (by omega : activeSendOpkCount S b.q_on ≤ S.N_dh)
  have bUnr := bits_keyIndSentinel_le_split S b
  have hmA := Nat.mul_le_mul hId hSpk; have hmC := Nat.mul_le_mul hSend hSpk
  have hmB := Nat.mul_le_mul hSend hId; have hmD := Nat.mul_le_mul hSendO hOpk
  have hSumSq : S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot ≤ S.N_dh * S.N_dh := by nlinarith
  have bAC := bits_le_two_log_dh_succ (S := S) (by omega :
    activeIdCount S b.q_on * activeSpkCount S b.q_on + activeSendCount S b.q_on * activeSpkCount S b.q_on ≤ S.N_dh * S.N_dh)
  have bBD := bits_le_two_log_dh_succ (S := S) (by omega :
    activeSendCount S b.q_on * activeIdCount S b.q_on + activeSendOpkCount S b.q_on * activeOpkCount S b.q_on ≤ S.N_dh * S.N_dh)
  have bAll := bits_le_two_log_dh_succ (S := S) (by omega :
    (activeIdCount S b.q_on * activeSpkCount S b.q_on + activeSendCount S b.q_on * activeSpkCount S b.q_on) +
    (activeSendCount S b.q_on * activeIdCount S b.q_on + activeSendOpkCount S b.q_on * activeOpkCount S b.q_on) ≤ S.N_dh * S.N_dh)
  let Bleaf := 4 * Nat.log 2 S.N_dh + 2 * bits (min b.q_on b.q_total + 1) + 80
  unfold initParams1KeyKindC; dsimp only
  by_cases h0 : fgActiveTotalIndexCount S b.q_on = 0
  · simp only [h0, ↓reduceIte]
    refine (Comp.cost_le_costUB _).trans ?_
    simp only [paMk, v_costUB, Comp.costUB, Expr.costUB, bits_0]; omega
  · simp only [h0, ↓reduceIte]
    let Bmid := 10 * Nat.log 2 S.N_dh + 2 * bits (min b.q_on b.q_total + 1) + 116
    refine (act_chooseArm2C_cost_le (Γ₁ := Γ₁) (Δ := Δ) _ _ _ _ Bmid ?_ ?_).trans
      (by dsimp [Bmid]; omega)
    · intro Δ' _
      refine (act_chooseArm2C_cost_le (Γ₁ := Γ₁) (Δ := Δ') _ _ _ _ Bleaf ?_ ?_).trans
        (by dsimp [Bleaf, Bmid]; omega)
      · intro Δ'' _
        refine (Comp.cost_le_costUB _).trans ?_
        split_ifs <;> (simp only [paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB,
          Comp.costUB, Expr.costUB, bits_0]; dsimp [Bleaf]; omega)
      · intro Δ'' _
        refine (Comp.cost_le_costUB _).trans ?_
        split_ifs <;> (simp only [paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB,
          Comp.costUB, Expr.costUB, bits_0, bits_1]; dsimp [Bleaf]; omega)
    · intro Δ' _
      refine (act_chooseArm2C_cost_le (Γ₁ := Γ₁) (Δ := Δ') _ _ _ _ Bleaf ?_ ?_).trans
        (by dsimp [Bleaf, Bmid]; omega)
      · intro Δ'' _
        refine (Comp.cost_le_costUB _).trans ?_
        split_ifs <;> (simp only [paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB,
          Comp.costUB, Expr.costUB, bits_0, bits_2]; dsimp [Bleaf]; omega)
      · intro Δ'' _
        refine (Comp.cost_le_costUB _).trans ?_
        split_ifs <;> (simp only [paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB,
          Comp.costUB, Expr.costUB, bits_0, bits_3]; dsimp [Bleaf]; omega)

private theorem gdh1KeyKindBaseInit_cost_le_split (S : Setup) (b : QueryBudget) :
    (gdh1KeyKindBaseInit S b).cost ≤
      21 * Nat.log 2 S.N_dh + 4 * bits (min b.q_on b.q_total + 1) + 260 := by
  have hP := initParams1KeyKindC_cost_le_split S b
    (Γ₁ := .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32) ::
           [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)])
    (Δ := .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32) ::
          [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)]) .zero
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hsb : activeSigBudget S b ≤ S.N_dh :=
    Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_left _ _) (by omega))
  have bSb := bits_le_log_dh_succ hsb
  have hsB : (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim
      (sBool (Γ := paramsTy :: .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32) ::
        [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)]))).cost ≤ 4 :=
    (Comp.cost_le_costUB _).trans (by simp [sBool_costUB])
  unfold gdh1KeyKindBaseInit
  simp only [letV, bindV, liftGdhComp_cost, emptySimE, smMk, emptyStE, stMk,
    v, Comp.cost, Expr.cost, bits_0]
  omega

private theorem gdh1KeyKindInitC_cost_le_split (S : Setup) (b : QueryBudget) :
    (gdh1KeyKindInitC S b).cost ≤
      63 * Nat.log 2 S.N_dh + 12 * bits (min b.q_on b.q_total + 1) + 2000 := by
  have hBase := gdh1KeyKindBaseInit_cost_le_split S b
  have hMap := mapComp_cost_eleven_mul_le tlSigDdhKeyInd (gdh1KeyKindBaseInit S b)
  have hTail : (Expr.pair (Expr.fst (Expr.var
      (Γ := [embedTy (.prod .unit gdh1KeyActiveStateTy), .prod (PB 32) (PB 32)]) .zero))
      (Expr.pair (Expr.snd (Expr.var .zero)) emptyFgShadowE)).cost ≤ 1200 := by
    decide
  unfold gdh1KeyKindInitC
  simp only [Comp.cost]
  omega

private theorem gdh1KeyKindFinishC_cost_le (S : Setup) (b : QueryBudget) :
    (gdh1KeyKindFinishC S b).cost ≤
      207 * (min (keyIndKFuelsOfBudget S b).kOn S.N_dh) ^ 2 +
        207 * (keyIndKFuelsOfBudget S b).kOn * min (keyIndKFuelsOfBudget S b).kOn S.N_dh +
        198 * min (keyIndKFuelsOfBudget S b).kOn S.N_dh *
          min (keyIndKFuelsOfBudget S b).kOn S.N_sess_tot +
        1269 * min (keyIndKFuelsOfBudget S b).kOn S.N_dh +
        789 * min (keyIndKFuelsOfBudget S b).kOn S.N_sess_tot +
        6396 * (keyIndKFuelsOfBudget S b).kOff + 1255 := by
  have hF := gdhFinishK_atomic_cost_le gdhLift1Key S (keyIndKFuelsOfBudget S b)
  unfold gdh1KeyKindFinishC runAt2
  simp only [Comp.cost, compRename_cost, exprRename_cost, Expr.cost, Expr.v0, Expr.v1]
  omega

section QueryBounds
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.pqSamplers

private theorem act_bernoulliRatioGdhC_queries_zero {Δ : List PT}
    (w : _root_.SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → ℕ) (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries w wsZero = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [bindV, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, sIndex, wsZero, Comp.queries]

private theorem act_chooseArm2C_queries_zero {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w : _root_.SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → ℕ) (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Δ' τ)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries w wsZero = 0)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries w wsZero = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries w wsZero = 0 := by
  unfold chooseArm2C
  split_ifs
  · exact hc2
  · exact hc1
  · simp [bindV, act_bernoulliRatioGdhC_queries_zero, hc1, hc2, Comp.queries]

private theorem initParams1KeyKindC_queries_zero (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)))
    (w : _root_.SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → ℕ) :
    (initParams1KeyKindC S b (Δ := Δ) uv).queries w wsZero = 0 := by
  unfold initParams1KeyKindC; dsimp only
  by_cases h0 : fgActiveTotalIndexCount S b.q_on = 0
  · simp only [h0, ↓reduceIte]; rfl
  · simp only [h0, ↓reduceIte]
    refine act_chooseArm2C_queries_zero w _ _ _ _
      (fun {Δ'} [_] => act_chooseArm2C_queries_zero w _ _ _ _
        (fun {Δ''} [_] => by
          by_cases hA : activeIdCount S b.q_on * activeSpkCount S b.q_on = 0 <;>
            simp [hA, bindV, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, sIndex, wsZero, Comp.queries])
        (fun {Δ''} [_] => by
          by_cases hC : activeSendCount S b.q_on * activeSpkCount S b.q_on = 0 <;>
            simp [hC, bindV, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, sIndex, wsZero, Comp.queries]))
      (fun {Δ'} [_] => act_chooseArm2C_queries_zero w _ _ _ _
        (fun {Δ''} [_] => by
          by_cases hB : activeSendCount S b.q_on * activeIdCount S b.q_on = 0 <;>
            simp [hB, bindV, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, sIndex, wsZero, Comp.queries])
        (fun {Δ''} [_] => by
          by_cases hD : activeSendOpkCount S b.q_on * activeOpkCount S b.q_on = 0 <;>
            simp [hD, bindV, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, sIndex, wsZero, Comp.queries]))

@[local simp] private theorem gPrim_sBool_queries_wsZero {Δ : List PT}
    (w : _root_.SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → ℕ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim (Γ := Δ) sBool).queries w wsZero = 0 := rfl

private theorem liftGdhAtomic_sig_zero {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhAtomic gdhLift1Key c).queries chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  refine Nat.eq_zero_of_le_zero ?_
  unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
  refine (mapComp_queries_le tlSigDdhKeyInd lcSigW lcZeroWS
    chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW (liftGdhComp c)).trans ?_
  rw [liftGdhComp_queries_sig]

private theorem gdhKindRoArm_sigQueries (S : Setup) (f : KeyIndKFuels) :
    (gdhKindRoArm S f).queries chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  have hDr : (liftGdhAtomic gdhLift1Key
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim (sDrKey96 (Γ := [])))).queries
      chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := rfl
  have hPre160 := liftGdhAtomic_sig_zero
    (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)
  have hPre192 := liftGdhAtomic_sig_zero
    (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)
  have hScan := liftGdhAtomic_sig_zero (fgSessScanPackC f.kOn)
  unfold gdhKindRoArm roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
    sampleDrKey96LiftC
  simp only [runAt1, runAt2, runAt3, runAt4, Comp.queries, compRename_queries,
    avlSearchB192C_queries, avlInsertAtPathC_queries, hDr, hPre160, hPre192, hScan]
  omega

theorem fgKeyInd1KeyGapDhKindAtomicProg_q_sig (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).totalQueries
      chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  have hInit : (gdh1KeyKindInitC S b).queries chalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold gdh1KeyKindInitC
    simp only [Comp.queries, Nat.add_zero, samplerZeroQueryWeight_eq]
    refine (mapComp_queries_le tlSigDdhKeyInd lcSigW lcZeroWS
      chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW (gdh1KeyKindBaseInit S b)).trans ?_
    simp [gdh1KeyKindBaseInit, letV_queries, bindV_queries,
      liftGdhComp_queries_sig, Comp.queries]
  have hFin : (gdh1KeyKindFinishC S b).queries chalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold gdh1KeyKindFinishC runAt2
    simp only [Comp.queries, compRename_queries, Nat.zero_add]
    exact (liftGdhAtomic_sig_zero (gdhFinishK S (keyIndKFuelsOfBudget S b))).le
  have hH : (gdh1KeyKindHandleC S b).queries chalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := by
    unfold gdh1KeyKindHandleC; dsimp only
    apply dispatchKeyIndQ_queries_le
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhKindInitPrinLeg, initPrin1KeyActiveGdhB, letV_queries, bindV_queries,
        liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhWrapDelegNoFgLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB, letV_queries, bindV_queries, caseOptV_queries,
        liftGdhComp_queries_sig,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.sigChalQ_dsl_queries_sig,
        Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhKindGenOpkLeg, genOpkActiveGdhB, letV_queries, bindV_queries,
        liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhSessArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhKindInitiateSessLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhSessArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhKindInitiateSessLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhSessArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhKindAcceptOpkSessLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhSessArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhKindAcceptNoOpkSessLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhWrapDelegNoFgLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · rw [gdhKindRoArm_sigQueries]; omega
    · simp [Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhWrapDelegNoFgLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhWrapDelegNoFgLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcSigW _ tlSigDdhKeyInd_sigW).trans ?_
      simp [gdhWrapDelegNoFgLeg, letV_queries, bindV_queries, liftGdhComp_queries_sig, Comp.queries]
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDhKindAtomicProg]
  omega

private theorem liftGdhAtomic_ddh_le {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhAtomic gdhLift1Key c).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      c.queries wDdhGdh wsZero := by
  unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
  refine (mapComp_queries_le tlSigDdhKeyInd lcDdhW lcZeroWS
    chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW (liftGdhComp c)).trans ?_
  rw [liftGdhComp_queries_ddh]

private theorem gdhKindRoArm_ddhQueries_le (S : Setup) (f : KeyIndKFuels) :
    (gdhKindRoArm S f).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * f.kOn := by
  have hPre160 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 :=
    Nat.eq_zero_of_le_zero ((liftGdhAtomic_ddh_le _).trans
      (by simp [roParsedPrePos160C, bindV_queries, letV_queries, mkSecretPosC_chal, Comp.queries]))
  have hPre192 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 :=
    Nat.eq_zero_of_le_zero ((liftGdhAtomic_ddh_le _).trans
      (by simp [roParsedPrePos192C, bindV_queries, letV_queries, mkSecretPosC_chal, Comp.queries]))
  have hScan : (liftGdhAtomic gdhLift1Key (fgSessScanPackC f.kOn)).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * f.kOn :=
    (liftGdhAtomic_ddh_le _).trans (by
      simp [fgSessScanPackC,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessScanC,
        sessScanMinPredC, letV_queries, findMV_queries, entryMatchesC_chal, Comp.queries]; omega)
  have hDr : (liftGdhAtomic gdhLift1Key
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim (sDrKey96 (Γ := [])))).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := rfl
  unfold gdhKindRoArm roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
    sampleDrKey96LiftC
  simp only [runAt1, runAt2, runAt3, runAt4, Comp.queries, compRename_queries,
    avlSearchB192C_queries, avlInsertAtPathC_queries, hDr, hPre160, hPre192]
  omega

@[local simp] private theorem fgPatchShadowC_chal (kFg : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy))
    (ctr : Expr pqxdhOps Δ .nat) :
    (fgPatchShadowC kFg pos1 pos2 pos3 pos4? ss fgL fgSess ctr).queries wDdhGdh wsZero =
      4 * kFg := by
  simp [fgPatchShadowC, letV_queries, bindV_queries, findMV_queries, caseOptV_queries,
    entryMatchesC_chal, gPrim_queries_wDdhGdh, Comp.queries]
  omega

theorem fgKeyInd1KeyGapDhKindAtomicProg_q_ddh (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).totalQueries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  have hInit : (gdh1KeyKindInitC S b).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold gdh1KeyKindInitC
    simp only [Comp.queries, Nat.add_zero, samplerZeroQueryWeight_eq]
    refine (mapComp_queries_le tlSigDdhKeyInd lcDdhW lcZeroWS
      chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW (gdh1KeyKindBaseInit S b)).trans ?_
    simp [gdh1KeyKindBaseInit, letV_queries, bindV_queries,
      liftGdhComp_queries_ddh, initParams1KeyKindC_queries_zero, Comp.queries]
  have hfOn : (keyIndKFuelsOfBudget S b).kOn ≤ b.q_total := Nat.min_le_right _ _
  have hfOff : (keyIndKFuelsOfBudget S b).kOff ≤ b.q_total := Nat.min_le_right _ _
  have hfFg : (keyIndKFuelsOfBudget S b).kFg ≤ b.q_total := Nat.min_le_left _ _
  have hfOnD : min (keyIndKFuelsOfBudget S b).kOn S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hfOnS : min (keyIndKFuelsOfBudget S b).kOn S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hFin : (gdh1KeyKindFinishC S b).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      b.q_total + S.N_dh + S.N_sess_tot := by
    unfold gdh1KeyKindFinishC runAt2
    simp only [Comp.queries, compRename_queries, Nat.zero_add]
    refine (liftGdhAtomic_ddh_le (gdhFinishK S (keyIndKFuelsOfBudget S b))).trans ?_
    simp only [gdhFinishK, extractMode0KC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.logFindC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.spkPowsC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMapStepC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initDh1CandC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.respDh1CandC,
      letV_queries, bindV_queries, caseOptV_queries, findMV_queries,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.mapMV_queries, foldMV_queries,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.ddhQ_queries_wDdhGdh,
      gPrim_queries_wDdhGdh, Comp.queries, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.max_zero, max_self]
    omega
  have hH : (gdh1KeyKindHandleC S b).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      4 * b.q_total := by
    unfold gdh1KeyKindHandleC; dsimp only
    apply dispatchKeyIndQ_queries_le
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhKindInitPrinLeg, initPrin1KeyActiveGdhB, letV_queries, bindV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhWrapDelegNoFgLeg, wrapBase2, letV_queries, bindV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB, genSpkGdhActiveB,
        letV_queries, bindV_queries, caseOptV_queries,
        liftGdhComp_queries_ddh,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.sigChalQ_dsl_queries_ddh,
        gPrim_queries_wDdhGdh, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhKindGenOpkLeg, genOpkActiveGdhB, letV_queries, bindV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, Comp.queries]
    · refine (liftSigDdhSessArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp only [gdhKindInitiateSessLeg, initiateGdhActiveShadowInnerB,
        letV_queries, bindV_queries, caseOptV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh,
        computePosC_chal, computeOptPosInitC_chal, fgPatchShadowC_chal,
        chooseInitRandC_chal, Comp.queries]; omega
    · refine (liftSigDdhSessArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp only [gdhKindInitiateSessLeg, initiateGdhActiveShadowInnerB,
        letV_queries, bindV_queries, caseOptV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh,
        computePosC_chal, computeOptPosInitC_chal, fgPatchShadowC_chal,
        chooseInitRandC_chal, Comp.queries]; omega
    · refine (liftSigDdhSessArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp only [gdhKindAcceptOpkSessLeg, acceptOpkGdh2ShadowB,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.acceptOpkGdhCoreShadowB,
        finishAcceptGdhC, letV_queries, bindV_queries, caseOptV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, computePosC_chal, mkSecretPosC_chal,
        fgPatchShadowC_chal,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.chooseRespRandC_chal,
        Comp.queries]; omega
    · refine (liftSigDdhSessArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp only [gdhKindAcceptNoOpkSessLeg, acceptNoOpkGdhShadowB, finishAcceptGdhC,
        letV_queries, bindV_queries, caseOptV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, computePosC_chal, fgPatchShadowC_chal,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.chooseRespRandC_chal,
        Comp.queries]; omega
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhWrapDelegNoFgLeg, wrapBase2, letV_queries, bindV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, Comp.queries]
    · exact (gdhKindRoArm_ddhQueries_le S _).trans (by omega)
    · simp [Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhWrapDelegNoFgLeg, wrapBase2, letV_queries, bindV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhWrapDelegNoFgLeg, wrapSim2, registerGdhB, letV_queries, bindV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, Comp.queries]
    · refine (liftSigDdhNoFgArm_queries_le S _ _ lcDdhW _ tlSigDdhKeyInd_ddhW).trans ?_
      simp [gdhWrapDelegNoFgLeg, wrapBase2, letV_queries, bindV_queries,
        liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, Comp.queries]
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDhKindAtomicProg]
  nlinarith

@[local simp] private theorem liftGdhComp_primUB :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t),
      (liftGdhComp c).queriesUB lcPrimW lcZeroWS = c.queriesUB wPrimGdh wsZero := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queriesUB]

@[local simp] private theorem sigChalQ_dsl_primUB (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B m)) :
    (sigChalQ_dsl m msg).queriesUB lcPrimW lcZeroWS = 0 := rfl

@[local simp] private theorem loc_wrapBase2_primUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queriesUB wPrimGdh wsZero =
      c.queriesUB _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wPrimBase
        _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZeroBase := by
  simp [wrapBase2, bindV_queriesUB, gPrim_queriesUB_wPrimGdh, Comp.queriesUB]

@[local simp] private theorem loc_wrapSim2_primUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queriesUB wPrimGdh wsZero = c.queriesUB wPrimGdh wsZero := by
  simp [wrapSim2, bindV_queriesUB, Comp.queriesUB]

@[local simp] private theorem fgPatchShadowC_primUB (kFg : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy))
    (ctr : Expr pqxdhOps Δ .nat) :
    (fgPatchShadowC kFg pos1 pos2 pos3 pos4? ss fgL fgSess ctr).queriesUB wPrimGdh wsZero = 0 := by
  simp [fgPatchShadowC, letV_queriesUB, bindV_queriesUB, findMV_queriesUB, caseOptV_queriesUB,
    entryMatchesC_primUB, gPrim_queriesUB_wPrimGdh, sDrKey96_queriesUB, Comp.queriesUB]

private theorem liftGdhAtomic_primUB_le {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhAtomic gdhLift1Key c).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      c.queriesUB wPrimGdh wsZero := by
  unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
  refine (mapComp_queries_le tlSigDdhKeyInd lcPrimW lcZeroWS
    chalIfacePrimQueryWeight tlSigDdhKeyInd_primW (liftGdhComp c)).trans ?_
  exact (liftGdhComp_queries_prim c).le.trans (Comp.queries_le_queriesUB wPrimGdh wsZero c)

private theorem gdhKindRoArm_primQueries_le (S : Setup) (f : KeyIndKFuels) :
    (gdhKindRoArm S f).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 := by
  have hPre160 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 3 :=
    (liftGdhAtomic_primUB_le _).trans (by
      simp [roParsedPrePos160C, letV_queriesUB, bindV_queriesUB, mkSecretPosC_primUB,
        Comp.queriesUB])
  have hPre192 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 :=
    (liftGdhAtomic_primUB_le _).trans (by
      simp [roParsedPrePos192C, letV_queriesUB, bindV_queriesUB, mkSecretPosC_primUB,
        Comp.queriesUB])
  have hScan : (liftGdhAtomic gdhLift1Key (fgSessScanPackC f.kOn)).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 0 :=
    (liftGdhAtomic_primUB_le _).trans (by
      simp [fgSessScanPackC,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessScanC,
        sessScanMinPredC, letV_queriesUB, findMV_queriesUB, entryMatchesC_primUB, Comp.queriesUB])
  have hDr : (liftGdhAtomic gdhLift1Key
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim (sDrKey96 (Γ := [])))).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := rfl
  unfold gdhKindRoArm roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
    sampleDrKey96LiftC
  simp only [runAt1, runAt2, runAt3, runAt4, Comp.queries, compRename_queries,
    avlSearchB192C_queries, avlInsertAtPathC_queries, hDr]
  omega

private theorem liftSigDdhNoFgArm_primUB_le (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy)) :
    (liftSigDdhNoFgArm S payE arm).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      arm.queriesUB lcPrimW lcZeroWS :=
  (liftSigDdhNoFgArm_queries_le S payE arm lcPrimW chalIfacePrimQueryWeight tlSigDdhKeyInd_primW).trans
    (Comp.queries_le_queriesUB lcPrimW lcZeroWS arm)

private theorem liftSigDdhSessArm_primUB_le (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [.prod stTy fgSessCtrTy, qPayTy] (.prod keyIndRespTy (.prod stTy fgSessCtrTy))) :
    (liftSigDdhSessArm S payE arm).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      arm.queriesUB lcPrimW lcZeroWS :=
  (liftSigDdhSessArm_queries_le S payE arm lcPrimW chalIfacePrimQueryWeight tlSigDdhKeyInd_primW).trans
    (Comp.queries_le_queriesUB lcPrimW lcZeroWS arm)

set_option linter.unusedSimpArgs false in
theorem fgKeyInd1KeyGapDhKindAtomicProg_q_prim (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).totalQueries
      chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  have hInit : (gdh1KeyKindInitC S b).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold gdh1KeyKindInitC
    simp only [Comp.queries, Nat.add_zero, samplerZeroQueryWeight_eq]
    refine (mapComp_queries_le tlSigDdhKeyInd lcPrimW lcZeroWS
      chalIfacePrimQueryWeight tlSigDdhKeyInd_primW (gdh1KeyKindBaseInit S b)).trans ?_
    simp [gdh1KeyKindBaseInit, letV_queries, bindV_queries,
      liftGdhComp_queries_prim, initParams1KeyKindC_queries_zero, Comp.queries]
  have hfOnD : min (keyIndKFuelsOfBudget S b).kOn S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hfOnS : min (keyIndKFuelsOfBudget S b).kOn S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hFin : (gdh1KeyKindFinishC S b).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      3 * S.N_dh + S.N_sess_tot := by
    unfold gdh1KeyKindFinishC runAt2
    simp only [Comp.queries, compRename_queries, Nat.zero_add]
    refine (liftGdhAtomic_primUB_le (gdhFinishK S (keyIndKFuelsOfBudget S b))).trans ?_
    simp only [gdhFinishK, extractMode0KC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.logFindC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.spkPowsC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMapStepC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initDh1CandC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.respDh1CandC,
      letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, findMV_queriesUB,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.mapMV_queriesUB,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.foldMV_queriesUB,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.ddhQ_queriesUB_wPrimGdh,
      gPrim_queriesUB_wPrimGdh, qPow8_queriesUB, qX25519_queriesUB, Comp.queriesUB]
    linarith
  have hH : (gdh1KeyKindHandleC S b).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      160 + 76 * S.N_dh + 16 * S.N_sess_tot := by
    unfold gdh1KeyKindHandleC; dsimp only
    apply dispatchKeyIndQ_queries_le
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhKindInitPrinLeg, initPrin1KeyActiveGdhB, letV_queriesUB, bindV_queriesUB,
        liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh, sBytes32_queriesUB, qX25519Base_queriesUB,
        Comp.queriesUB]; omega
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhWrapDelegNoFgLeg, corruptB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhComp_primUB, Comp.queriesUB]; omega
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB, genSpkGdhActiveB,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB,
        liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh, sigChalQ_dsl_primUB,
        sBytes32_queriesUB, sRandom64_queriesUB, qX25519Base_queriesUB, qSigSign_queriesUB,
        qKemKeyGen_queriesUB, Comp.queriesUB]; omega
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhKindGenOpkLeg, genOpkActiveGdhB, letV_queriesUB, bindV_queriesUB,
        liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh, sBytes32_queriesUB, qX25519Base_queriesUB,
        Comp.queriesUB]; omega
    · refine (liftSigDdhSessArm_primUB_le S _ _).trans ?_
      simp only [gdhKindInitiateSessLeg, initiateGdhActiveShadowInnerB,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, findMV_queriesUB,
        liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh,
        isGameSpkC_primUB, isGameOpkC_primUB, partnerC_primUB,
        honestPeerC_primUB, koskBundleOkPowsC_primUB, resolveSigPkC_primUB,
        lookupSpkSkC_primUB, checkProvC_primUB, findHonestC_primUB, chooseInitRandC_primUB,
        computePosC_primUB, computeOptPosInitC_primUB, mkSecretPosC_primUB, mkPairPosC_primUB,
        ddhEqC_primUB, ddhEqOptC_primUB, fgPatchShadowC_primUB,
        sBytes32_queriesUB, sDrKey96_queriesUB, qX25519_queriesUB, qX25519Base_queriesUB,
        qIsCanonical_queriesUB, qSigVerify_queriesUB, qKemEncaps_queriesUB, Comp.queriesUB]; linarith
    · refine (liftSigDdhSessArm_primUB_le S _ _).trans ?_
      simp only [gdhKindInitiateSessLeg, initiateGdhActiveShadowInnerB,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, findMV_queriesUB,
        liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh,
        isGameSpkC_primUB, isGameOpkC_primUB, partnerC_primUB,
        honestPeerC_primUB, koskBundleOkPowsC_primUB, resolveSigPkC_primUB,
        lookupSpkSkC_primUB, checkProvC_primUB, findHonestC_primUB, chooseInitRandC_primUB,
        computePosC_primUB, computeOptPosInitC_primUB, mkSecretPosC_primUB, mkPairPosC_primUB,
        ddhEqC_primUB, ddhEqOptC_primUB, fgPatchShadowC_primUB,
        sBytes32_queriesUB, sDrKey96_queriesUB, qX25519_queriesUB, qX25519Base_queriesUB,
        qIsCanonical_queriesUB, qSigVerify_queriesUB, qKemEncaps_queriesUB, Comp.queriesUB]; linarith
    · refine (liftSigDdhSessArm_primUB_le S _ _).trans ?_
      simp only [gdhKindAcceptOpkSessLeg, acceptOpkGdh2ShadowB,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.acceptOpkGdhCoreShadowB,
        finishAcceptGdhC, letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, findMV_queriesUB,
        liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh,
        koskSenderOkPowsC_primUB, findHonestC_primUB, chooseRespRandC_primUB, partnerC_primUB,
        computePosC_primUB, mkSecretPosC_primUB, mkPairPosC_primUB,
        ddhEqC_primUB, ddhEqOptC_primUB, fgPatchShadowC_primUB,
        sDrKey96_queriesUB, qX25519_queriesUB, qIsCanonical_queriesUB, qKemDecaps_queriesUB,
        Comp.queriesUB]; linarith
    · refine (liftSigDdhSessArm_primUB_le S _ _).trans ?_
      simp only [gdhKindAcceptNoOpkSessLeg, acceptNoOpkGdhShadowB, finishAcceptGdhC,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, findMV_queriesUB,
        liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh,
        koskSenderOkPowsC_primUB, findHonestC_primUB, chooseRespRandC_primUB, partnerC_primUB,
        computePosC_primUB, mkSecretPosC_primUB, mkPairPosC_primUB,
        ddhEqC_primUB, ddhEqOptC_primUB, fgPatchShadowC_primUB,
        sDrKey96_queriesUB, qX25519_queriesUB, qIsCanonical_queriesUB, qKemDecaps_queriesUB,
        Comp.queriesUB]; linarith
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhWrapDelegNoFgLeg, testB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhComp_primUB, Comp.queriesUB]; omega
    · exact (gdhKindRoArm_primQueries_le S (keyIndKFuelsOfBudget S b)).trans (by omega)
    · simp [Comp.queries]
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhWrapDelegNoFgLeg, revealB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhComp_primUB, Comp.queriesUB]; omega
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhWrapDelegNoFgLeg, registerGdhB, loc_wrapSim2_primUB, letV_queriesUB,
        bindV_queriesUB, liftGdhComp_primUB, gPrim_queriesUB_wPrimGdh,
        qX25519Base_queriesUB, qPow8_queriesUB, Comp.queriesUB]; omega
    · refine (liftSigDdhNoFgArm_primUB_le S _ _).trans ?_
      simp only [gdhWrapDelegNoFgLeg, revealSpkB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhComp_primUB, Comp.queriesUB]; omega
  have hMul := Nat.mul_le_mul_left b.q_total hH
  have hTot : (fgKeyInd1KeyGapDhKindAtomicProg S b).totalQueries
      chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      b.q_total * (160 + 76 * S.N_dh + 16 * S.N_sess_tot) + (3 * S.N_dh + S.N_sess_tot) := by
    dsimp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDhKindAtomicProg]; omega
  unfold primQueryBudget; nlinarith

end QueryBounds

private theorem bits_le_succ_self (n : Nat) : bits n ≤ n + 1 := by
  unfold bits; have := Nat.log_le_self 2 n; omega

theorem fgKeyInd1KeyGapDhKindAtomicProg_size_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) :=
  fgKeyInd1KeyGapDhKindAtomicProg_size_le_aux S b

theorem fgKeyInd1KeyGapDhKindAtomicProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  let q := b.q_total
  let M_dh := min q S.N_dh
  let M_sess := min q S.N_sess_tot
  let logDh := Nat.log 2 S.N_dh
  let logSess := Nat.log 2 S.N_sess_tot
  let f := keyIndKFuelsOfBudget S b
  let B := 15000 * q + 25500 * M_dh + 23500 * M_sess + 102000
  have hkOn : f.kOn ≤ q := Nat.min_le_right _ _
  have hkOff : f.kOff ≤ q := Nat.min_le_right _ _
  have hkFg : f.kFg ≤ q := Nat.min_le_left _ _
  have hmDh : min f.kOn S.N_dh ≤ M_dh :=
    le_min ((Nat.min_le_left _ _).trans hkOn) (Nat.min_le_right _ _)
  have hmSess : min f.kOn S.N_sess_tot ≤ M_sess :=
    le_min ((Nat.min_le_left _ _).trans hkOn) (Nat.min_le_right _ _)
  have hbAvl : bits f.kAvl ≤ 3 * q + 2 := by
    have hkAvl : f.kAvl ≤ 3 * q + 1 := by
      dsimp only [f, keyIndKFuelsOfBudget]
      linarith [Nat.min_le_right b.q_ro q, Nat.min_le_right b.q_on q]
    exact (bits_le_succ_self f.kAvl).trans (by linarith)
  have hbOn1 : bits (min b.q_on q + 1) ≤ q + 2 :=
    (bits_le_succ_self _).trans (by linarith [Nat.min_le_right b.q_on q])
  have hOnB : gdhOnlineArmBudget S f ≤ B := by
    unfold gdhOnlineArmBudget; dsimp only [B]
    linarith [Nat.zero_le q, Nat.zero_le M_dh, Nat.zero_le M_sess]
  have hRoB : (gdhKindRoArm S f).cost ≤ B :=
    (gdhKindRoArm_cost_le S f).trans
      (by dsimp only [B]; linarith [Nat.zero_le q, Nat.zero_le M_dh, Nat.zero_le M_sess])
  have hHdl : (gdh1KeyKindHandleC S b).cost ≤ B + 27 :=
    gdh1KeyKindHandleC_cost_le S b hOnB hRoB
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  have hUCost : pqSigAndDdhIface.uCost ≤ 91 := by decide
  have hMax : max pqSigAndDdhIface.uCost
      ((gdh1KeyKindHandleC S b).cost + (pqKeyIndCodec S).codecCost) ≤ B + 91 :=
    max_le (hUCost.trans (by linarith [Nat.zero_le B])) (by rw [hCodec]; linarith)
  have hInit : (gdh1KeyKindInitC S b).cost ≤ 63 * logDh + 12 * q + 2024 :=
    (gdh1KeyKindInitC_cost_le_split S b).trans (by dsimp only [q, logDh]; linarith)
  have hFin : (gdh1KeyKindFinishC S b).cost ≤
      207 * M_dh ^ 2 + 207 * q * M_dh + 198 * M_dh * M_sess +
        1269 * M_dh + 789 * M_sess + 6396 * q + 1255 := by
    have h0 := gdh1KeyKindFinishC_cost_le S b
    have hEq : f = keyIndKFuelsOfBudget S b := rfl
    rw [← hEq] at h0
    have hSq : (min f.kOn S.N_dh) ^ 2 ≤ M_dh ^ 2 := Nat.pow_le_pow_left hmDh 2
    have hQM : f.kOn * min f.kOn S.N_dh ≤ q * M_dh := Nat.mul_le_mul hkOn hmDh
    have hDS : min f.kOn S.N_dh * min f.kOn S.N_sess_tot ≤ M_dh * M_sess :=
      Nat.mul_le_mul hmDh hmSess
    linarith
  have hTot : (fgKeyInd1KeyGapDhKindAtomicProg S b).totalCost q ≤
      (63 * logDh + 12 * q + 2024) + q * (B + 91) +
        (207 * M_dh ^ 2 + 207 * q * M_dh + 198 * M_dh * M_sess +
          1269 * M_dh + 789 * M_sess + 6396 * q + 1255) := by
    dsimp only [CostedReduction.totalCost, fgKeyInd1KeyGapDhKindAtomicProg]
    exact Nat.add_le_add (Nat.add_le_add hInit (Nat.mul_le_mul_left q hMax)) hFin
  refine hTot.trans ?_
  unfold stepCostBudget; dsimp only [q, M_dh, M_sess, logDh, logSess, B]
  exact Nat.le.intro (k :=
    50536 * q ^ 2 + 22573 * q + 62257 +
    7061 * q * M_dh + 31499 * M_dh +
    9268 * q * M_sess + 31979 * M_sess +
    1024 * q * logDh + 961 * logDh +
    1024 * q * logSess + 1024 * logSess +
    1841 * M_dh ^ 2 + 58 * M_dh * M_sess) (by ring)

private theorem gredBlockBounded_of_cost {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} {G : OracleSpec κ}
    {C : _root_.ReductionDsl.GameCodec pqAtomicSig G}
    {rIn out : Ty pqAtomicSig}
    (hqCost : ∀ g, 1 ≤ I.qCost g) (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : CostedReduction pqAtomicOps I G C rIn .unit .bool out)
    (hsmp : I.smp = pqAtomicSamplers)
    (hCost : R.totalCost b.q_total ≤ stepCostBudget S b)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b)) :
    GRedBlockBounded S b ℓ R :=
  gredBlockBounded_atomic_of_totalCost_le (hsmp ▸ pqAtomicSamplers_sizeHonest) hqCost
    (hsmp ▸ one_le_pqAtomicSamplers_sCost) S b ℓ R hCost hSize

theorem fgKeyInd1KeyGapDhKindAtomicProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ (fgKeyInd1KeyGapDhKindAtomicProg S b) :=
  gredBlockBounded_of_cost one_le_pqSigAndDdhIface_qCost S b ℓ
    (fgKeyInd1KeyGapDhKindAtomicProg S b) rfl
    (fgKeyInd1KeyGapDhKindAtomicProg_totalCost_le S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_size_le S b)

theorem fgKeyInd1KeyGapDhKindAtomicProg_costByKind (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).CostBoundedByKind keyIndQueryKind (keyIndKindCounts b)
      (stepCostBudgetSplit S b b.q_ro) := by
  let M_on := min b.q_on b.q_total
  let M_off := min b.q_ro b.q_total
  let M_dh := min M_on S.N_dh
  let M_sess := min M_on S.N_sess_tot
  let bAvl := bits (M_off + 2 * M_on + 1)
  let logDh := Nat.log 2 S.N_dh
  let logSess := Nat.log 2 S.N_sess_tot
  let f := keyIndKFuelsOfBudget S b
  let c0 := 1336 * M_off + 13836 * M_on + 25500 * M_dh + 23500 * M_sess + 102026
  let c1 := 4420 * bAvl + 1345 * M_on + 8726
  refine costBoundedByKind_fin2_of_armCosts (fgKeyInd1KeyGapDhKindAtomicProg S b)
    keyIndQueryKind (keyIndKindCounts b) (c0 := c0) (c1 := c1) ?_ ?_ ?_
  · intro s t ht
    dsimp only [fgKeyInd1KeyGapDhKindAtomicProg]
    refine (gdh1KeyKindHandleC_costAt_online_le S b s t ht).trans ?_
    have hkFg : f.kFg ≤ M_on + M_off := Nat.min_le_right _ _
    have hEq : f = keyIndKFuelsOfBudget S b := rfl
    rw [← hEq]; unfold gdhOnlineArmBudget
    dsimp only [f, keyIndKFuelsOfBudget, M_on, M_off, M_dh, M_sess, c0] at hkFg ⊢
    linarith [Nat.zero_le M_on, Nat.zero_le M_off, Nat.zero_le M_dh, Nat.zero_le M_sess]
  · intro s t ht
    match t, ht with
    | .roQuery sec, _ =>
      dsimp only [fgKeyInd1KeyGapDhKindAtomicProg]
      refine (gdh1KeyKindHandleC_costAt_ro_le S b s sec).trans ?_
      refine (Nat.add_le_add_right (gdhKindRoArm_cost_le S (keyIndKFuelsOfBudget S b)) 26).trans ?_
      dsimp only [keyIndKFuelsOfBudget, c1, bAvl, M_off, M_on]; omega
  · have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
    have hUCost : pqSigAndDdhIface.uCost ≤ 90 := by decide
    have hMax0 : max pqSigAndDdhIface.uCost (c0 + (pqKeyIndCodec S).codecCost) ≤ c0 + 64 :=
      max_le (hUCost.trans (by dsimp only [c0]; linarith [Nat.zero_le M_off, Nat.zero_le M_on, Nat.zero_le M_dh, Nat.zero_le M_sess])) (by rw [hCodec])
    have hMax1 : max pqSigAndDdhIface.uCost (c1 + (pqKeyIndCodec S).codecCost) ≤ c1 + 64 :=
      max_le (hUCost.trans (by dsimp only [c1]; linarith [Nat.zero_le bAvl, Nat.zero_le M_on])) (by rw [hCodec])
    have hbOn1 : bits (M_on + 1) ≤ M_on + 2 :=
      (bits_le_succ_self (M_on + 1)).trans (by linarith)
    have hInit : (gdh1KeyKindInitC S b).cost ≤ 63 * logDh + 12 * M_on + 2024 :=
      (gdh1KeyKindInitC_cost_le_split S b).trans (by dsimp only [M_on, logDh] at hbOn1 ⊢; linarith)
    have hFin : (gdh1KeyKindFinishC S b).cost ≤
        207 * M_dh ^ 2 + 207 * M_on * M_dh + 198 * M_dh * M_sess +
          1269 * M_dh + 789 * M_sess + 6396 * M_off + 1255 :=
      gdh1KeyKindFinishC_cost_le S b
    have hK0 : keyIndKindCounts b 0 = M_on := rfl
    have hK1 : keyIndKindCounts b 1 = M_off := rfl
    dsimp only [fgKeyInd1KeyGapDhKindAtomicProg]
    rw [hK0, hK1]
    refine (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add hInit (Nat.mul_le_mul_left M_on hMax0))
        (Nat.mul_le_mul_left M_off hMax1))
      hFin).trans ?_
    unfold stepCostBudgetSplit
    dsimp only [M_on, M_off, M_dh, M_sess, bAvl, logDh, logSess, c0, c1]
    exact Nat.le.intro (k :=
      51700 * M_on ^ 2 + 61738 * M_on + 62257 +
      7061 * M_on * M_dh + 31499 * M_dh +
      9268 * M_on * M_sess + 31979 * M_sess +
      1024 * M_on * logDh + 1024 * M_off * logDh + 961 * logDh +
      1024 * M_on * logSess + 1024 * M_off * logSess + 1024 * logSess +
      3772 * M_off * bAvl + 8192 * M_on * bAvl +
      17582 * M_off + 5511 * M_off * M_on +
      1841 * M_dh ^ 2 + 58 * M_dh * M_sess) (by ring)

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBounds
