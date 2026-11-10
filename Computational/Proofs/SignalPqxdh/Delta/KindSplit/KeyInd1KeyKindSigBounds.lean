/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.ReductionDsl.AtomicSizeHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.SignalPqxdh.AtomicLift
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBoundsCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigWire
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost
import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem
public import Computational.Specifications.Pqxdh.Bound
public import Computational.Specifications.Pqxdh.Security.Headline

/-!
# Cost, Query, Size, and Block Bounds for `sigKeyInd1KeyKindAtomicProg`

Proves total and per-query-kind step-cost bounds, syntactic signature/DDH/primitive query
bounds, program size bounds, and block-size bounds (`GRedBlockBounded`) for
`sigKeyInd1KeyKindAtomicProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBounds

public section

set_option autoImplicit false

open OracleSpec
open _root_.ReductionDsl (Expr Comp Var Ty Env Iface CostedReduction
  pqAtomicSig pqAtomicOps pqAtomicSamplers pqSigAndDdhIface pqKeyIndCodec
  B PB drKeyT bits bits_mono bits_mul bits_le_succ reductionSizeBudget)
open _root_.SignalPqxdh (Setup QueryBudget keyIndSpec KeyIndQuery activeIdCount)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit primQueryBudget
  GRedBlockBounded keyIndQueryKind keyIndKindCounts
  chalIfaceSigQueryWeight chalIfaceDdhQueryWeight chalIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.Computational.Proofs.ReductionDsl.AtomicSizeHonest (pqAtomicSamplers_sizeHonest)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps sigAndDdhOracle)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT v letV bindV caseOptV caseSumV findMV anyMV
  isSomeE eCaseOpt eAny eFind eMap litB rNone
  keyIndRespTy initQTy accQTy s1Prim s1Forgery s1Fg s1Pk s1Upd s1Mk s1Base s1Target s1Budget
  emptySimE emptyStE smMk smUpd stMk stUpd
  sig1KeyStTy sig1KeyTargetGenSpkB liftGdhToSigDdh keyIndStateTy simTy params2Ty gdhState2Ty
  smBase pa2Mk wrapBase2 wrapSim2 genSpkGdh2B genOpkGdh2B
  corruptB testB revealB registerGdhB revealSpkB
  initiateGdh2B acceptOpkGdh2B acceptNoOpkGdhB finishAcceptGdhC
  preKeyBundleTy sBool sIndex sBytes32 sRandom64 sDrKey96
  qX25519 qX25519Base qPow8 qIsCanonical qSigPkGen qSigSign qSigVerify
  qKemKeyGen qKemEncaps qKemDecaps qHkdfDerive96
  fgPosTy fgPatchEntryTy drKeyTy bits_0 bits_1 bits_eq_log2_succ
  s1Prim_costUB s1Prim_primUB qSigDdhSign_primUB liftGdhToSigDdh_primUB)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (
  bindV_costUB sIndex_costUB sBool_costUB v_costUB
  bindV_queries letV_queries caseOptV_queries findMV_queries
  letV_queriesUB bindV_queriesUB caseOptV_queriesUB caseSumV_queriesUB findMV_queriesUB
  wDdhGdh wPrimGdh wPrimBase wsZero wsZeroBase
  gPrim_queries_wDdhGdh gPrim_queries_wPrimGdh gPrim_queriesUB_wPrimGdh
  mkSecretPosC_chal computePosC_chal computeOptPosInitC_chal
  entryMatchesC_chal chooseInitRandC_chal
  koskBundleOkPowsC_primUB koskSenderOkPowsC_primUB
  resolveSigPkC_primUB lookupSpkSkC_primUB honestPeerC_primUB checkProvC_primUB
  findHonestC_primUB chooseInitRandC_primUB chooseRespRandC_primUB
  computePosC_primUB computeOptPosInitC_primUB mkSecretPosC_primUB entryMatchesC_primUB
  sBytes32_queriesUB sRandom64_queriesUB sDrKey96_queriesUB
  qX25519_queriesUB qX25519Base_queriesUB qIsCanonical_queriesUB qPow8_queriesUB
  qSigPkGen_queriesUB qSigSign_queriesUB qSigVerify_queriesUB
  qKemKeyGen_queriesUB qKemEncaps_queriesUB qKemDecaps_queriesUB)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  liftGdhComp liftGdhComp_queries_sig liftGdhComp_queries_ddh liftGdhComp_queries_prim)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  activeSigBudget optNatMatchesE sig1KeyActiveStTy S1ARS saTP saInner
  extract1KeyActiveC sig1KeyActiveInitPrinB)
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
  sigKeyInd1KeyKindAtomicProg sig1KeyKindInitC sig1KeyKindHandleC sig1KeyKindFinishC
  sig1KeyKindBaseInit sig1KeyKindBaseFinish sigKindRoArm
  sigKindInitPrinLeg sigKindGenSpkLeg sigWrapGdh2NoFgLeg
  sigKindInitiateSessLeg sigKindAcceptOpkSessLeg sigKindAcceptNoOpkSessLeg
  liftSigDdhNoFgArm liftSigDdhSessArm
  sigHasForgeryAtomicE sigGetFgAtomicE sigSetFgAtomicE)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  keyIndSentinel dispatchKeyIndQ atomicRNoneE runAt2 runAt3 runAt4)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost (
  dispatchKeyIndQ_ro_costAt_le dispatchKeyIndQ_online_costAt_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget gdhLift1Key liftGdhAtomic seqFgEntryTy
  fgSessScanPackC fgPatchShadowC sessScanMinPredC
  roParsedPrePos160C roParsedPrePos192C roRawFallbackShadowAtomicC
  roParsedPostPosShadowAtomicC roParsedShadowAtomicC sampleDrKey96LiftC
  initiateGdh2ShadowB acceptOpkGdh2ShadowB acceptNoOpkGdhShadowB emptyFgShadowE runAt1)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (
  avlSearchB192C_cost_le avlInsertAtPathC_cost_le
  avlSearchB192C_queries avlInsertAtPathC_queries
  avlSearchB192C_size_le avlInsertAtPathC_size_le)

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

private abbrev lcSigW := _root_.SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
private abbrev lcDdhW := _root_.SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
private abbrev lcPrimW :=
  _root_.SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight (C := sigAndDdhOracle)
private abbrev lcZeroWS := _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight

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
      [.prod stTy Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy)))
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

private theorem bits_keyIndSentinel_le_split (S : Setup) (b : QueryBudget) :
    bits (keyIndSentinel S b) ≤ Nat.log 2 S.N_dh + bits (min b.q_on b.q_total + 1) + 3 := by
  have hle : keyIndSentinel S b ≤ S.N_dh + (min b.q_on b.q_total + 1) := by
    unfold keyIndSentinel
    exact Nat.le_trans (Nat.min_le_right _ _) (by omega)
  by_cases hdh : S.N_dh = 0
  · have hle' : keyIndSentinel S b ≤ min b.q_on b.q_total + 1 := by omega
    have hb := bits_mono hle'
    omega
  · have hpos : 1 ≤ S.N_dh := Nat.pos_of_ne_zero hdh
    have hm1 : S.N_dh ≤ S.N_dh * (min b.q_on b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hm2 : min b.q_on b.q_total + 1 ≤ S.N_dh * (min b.q_on b.q_total + 1) :=
      Nat.le_mul_of_pos_left _ hpos
    have hprod : S.N_dh + (min b.q_on b.q_total + 1) ≤
        2 * S.N_dh * (min b.q_on b.q_total + 1) := by
      rw [Nat.mul_assoc]; omega
    have hb1 : bits (keyIndSentinel S b) ≤ bits (2 * S.N_dh * (min b.q_on b.q_total + 1)) :=
      bits_mono (Nat.le_trans hle hprod)
    have hb2 := bits_mul (2 * S.N_dh) (min b.q_on b.q_total + 1)
    have hb3 := bits_mul 2 S.N_dh
    have hb2_val : bits 2 = 2 := by decide
    have hb_dh : bits S.N_dh = Nat.log 2 S.N_dh + 1 := bits_eq_log2_succ S.N_dh
    omega

private theorem sig1KeyKindBaseInit_cost_le_split (S : Setup) (b : QueryBudget) :
    (sig1KeyKindBaseInit S b).cost ≤
      2 * Nat.log 2 S.N_dh + bits (min b.q_on b.q_total + 1) + 80 := by
  refine Nat.le_trans (sig1KeyKindBaseInit S b).cost_le_costUB ?_
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hn : activeIdCount S b.q_on ≤ S.N_dh :=
    Nat.le_trans (Nat.min_le_right _ _) (by omega)
  have b1 := bits_le_log_dh_succ hn
  have hsb : activeSigBudget S b ≤ S.N_dh :=
    Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_left _ _) (by omega))
  have b2 := bits_le_log_dh_succ hsb
  have b3 := bits_keyIndSentinel_le_split S b
  unfold sig1KeyKindBaseInit
  by_cases h0 : activeIdCount S b.q_on = 0 <;>
    (simp only [h0, ↓reduceIte, s1Mk, emptySimE, smMk, emptyStE, stMk,
      bindV_costUB, s1Prim_costUB, sIndex_costUB, sBool_costUB, v_costUB,
      Comp.costUB, Expr.costUB, bits_0]
     omega)

private theorem sig1KeyKindInitC_cost_le_split (S : Setup) (b : QueryBudget) :
    (sig1KeyKindInitC S b).cost ≤
      22 * Nat.log 2 S.N_dh + 11 * bits (min b.q_on b.q_total + 1) + 2900 := by
  have hBase := sig1KeyKindBaseInit_cost_le_split S b
  have hMap := mapComp_cost_eleven_mul_le tlSigDdhKeyInd (sig1KeyKindBaseInit S b)
  have hTail : (Expr.pair (Expr.fst (Expr.var (Γ := [embedTy (.prod .unit sig1KeyActiveStTy), PB 32]) .zero))
      (Expr.pair (Expr.snd (Expr.var .zero)) emptyFgShadowE)).cost ≤ 2000 := by
    decide
  unfold sig1KeyKindInitC
  simp only [Comp.cost]
  omega

private theorem sig1KeyKindFinishC_cost_le :
    sig1KeyKindFinishC.cost ≤ 10000 := by
  decide

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.pqSamplers

private theorem sigKindRoArm_sigQueries (S : Setup) (f : KeyIndKFuels) :
    (sigKindRoArm S f).queries chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  have hPre160 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
    refine Nat.eq_zero_of_le_zero ((?_) : _ ≤ 0)
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcSigW lcZeroWS
      chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW _) ?_
    exact (liftGdhComp_queries_sig _).le
  have hPre192 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
    refine Nat.eq_zero_of_le_zero ((?_) : _ ≤ 0)
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcSigW lcZeroWS
      chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW _) ?_
    exact (liftGdhComp_queries_sig _).le
  have hScan : (liftGdhAtomic gdhLift1Key (fgSessScanPackC f.kOn)).queries
      chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
    refine Nat.eq_zero_of_le_zero ((?_) : _ ≤ 0)
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcSigW lcZeroWS
      chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW _) ?_
    exact (liftGdhComp_queries_sig _).le
  have hSmp : (liftGdhAtomic gdhLift1Key (Γ := [])
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim sDrKey96)).queries
      chalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := rfl
  unfold sigKindRoArm roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
    sampleDrKey96LiftC
  simp only [runAt1, runAt2, runAt3, runAt4, Comp.queries, compRename_queries,
    avlSearchB192C_queries, avlInsertAtPathC_queries, hSmp,
    hPre160, hPre192, hScan]
  omega

private theorem sigKindRoArm_ddhQueries_le (S : Setup) (f : KeyIndKFuels) :
    (sigKindRoArm S f).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * f.kOn := by
  have hPre160 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
    refine Nat.eq_zero_of_le_zero ((?_) : _ ≤ 0)
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcDdhW lcZeroWS
      chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW _) ?_
    refine (liftGdhComp_queries_ddh _).le.trans ?_
    simp [roParsedPrePos160C, bindV_queries, letV_queries, mkSecretPosC_chal, Comp.queries]
  have hPre192 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
    refine Nat.eq_zero_of_le_zero ((?_) : _ ≤ 0)
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcDdhW lcZeroWS
      chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW _) ?_
    refine (liftGdhComp_queries_ddh _).le.trans ?_
    simp [roParsedPrePos192C, bindV_queries, letV_queries, mkSecretPosC_chal, Comp.queries]
  have hScan : (liftGdhAtomic gdhLift1Key (fgSessScanPackC f.kOn)).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * f.kOn := by
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcDdhW lcZeroWS
      chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW _) ?_
    refine (liftGdhComp_queries_ddh _).le.trans ?_
    simp [fgSessScanPackC,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessScanC,
      sessScanMinPredC, letV_queries, findMV_queries, entryMatchesC_chal, Comp.queries]
    omega
  have hSmp : (liftGdhAtomic gdhLift1Key (Γ := [])
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim sDrKey96)).queries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := rfl
  unfold sigKindRoArm roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
    sampleDrKey96LiftC
  simp only [runAt1, runAt2, runAt3, runAt4, Comp.queries, compRename_queries,
    avlSearchB192C_queries, avlInsertAtPathC_queries, hSmp,
    hPre160, hPre192]
  omega

theorem sigKeyInd1KeyKindAtomicProg_q_sig (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyKindAtomicProg S b).totalQueries
      chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  have hInit : (sig1KeyKindInitC S b).queries chalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold sig1KeyKindInitC
    simp only [Comp.queries, Nat.add_zero, samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcSigW lcZeroWS
      chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW _) ?_
    simp [sig1KeyKindBaseInit, bindV_queries,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_sigQueries, Comp.queries]
  have hFin : sig1KeyKindFinishC.queries chalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold sig1KeyKindFinishC runAt2
    simp only [Comp.queries, compRename_queries, Nat.zero_add, samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcSigW lcZeroWS
      chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW _) ?_
    rfl
  have hH : (sig1KeyKindHandleC S b).queries chalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := by
    unfold sig1KeyKindHandleC
    dsimp only
    apply dispatchKeyIndQ_queries_le
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigKindInitPrinLeg, sig1KeyActiveInitPrinB, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigWrapGdh2NoFgLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigKindGenSpkLeg, sig1KeyTargetGenSpkB, letV_queries, bindV_queries, caseOptV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_sigQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigDdhSign, Comp.queries,
        _root_.SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigWrapGdh2NoFgLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigKindInitiateSessLeg, extract1KeyActiveC, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_sigQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigKindInitiateSessLeg, extract1KeyActiveC, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_sigQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigKindAcceptOpkSessLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigKindAcceptNoOpkSessLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigWrapGdh2NoFgLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · rw [sigKindRoArm_sigQueries]; omega
    · simp [Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigWrapGdh2NoFgLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigWrapGdh2NoFgLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_sigW) ?_
      simp [sigWrapGdh2NoFgLeg, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, Comp.queries]
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, sigKeyInd1KeyKindAtomicProg]
  omega

private theorem fgPatchShadowC_chal (kFg : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
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

theorem sigKeyInd1KeyKindAtomicProg_q_ddh (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyKindAtomicProg S b).totalQueries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
        4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  have hInit : (sig1KeyKindInitC S b).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold sig1KeyKindInitC
    simp only [Comp.queries, Nat.add_zero, samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcDdhW lcZeroWS
      chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW _) ?_
    simp [sig1KeyKindBaseInit, bindV_queries,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_ddhQueries, Comp.queries]
  have hFin : sig1KeyKindFinishC.queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold sig1KeyKindFinishC runAt2
    simp only [Comp.queries, compRename_queries, Nat.zero_add, samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcDdhW lcZeroWS
      chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW _) ?_
    rfl
  have hfOn : (keyIndKFuelsOfBudget S b).kOn ≤ b.q_total := Nat.min_le_right _ _
  have hfFg : (keyIndKFuelsOfBudget S b).kFg ≤ b.q_total := Nat.min_le_left _ _
  have hH : (sig1KeyKindHandleC S b).queries chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      4 * b.q_total := by
    unfold sig1KeyKindHandleC
    dsimp only
    apply dispatchKeyIndQ_queries_le
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigKindInitPrinLeg, sig1KeyActiveInitPrinB, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_ddhQueries, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigWrapGdh2NoFgLeg, wrapBase2, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigKindGenSpkLeg, sig1KeyTargetGenSpkB, wrapSim2, genSpkGdh2B,
        letV_queries, bindV_queries, caseOptV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_ddhQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigDdhSign,
        gPrim_queries_wDdhGdh, Comp.queries,
        _root_.SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigWrapGdh2NoFgLeg, wrapSim2, genOpkGdh2B, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, Comp.queries]
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp only [sigKindInitiateSessLeg, extract1KeyActiveC, initiateGdh2ShadowB,
        letV_queries, bindV_queries, caseOptV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_ddhQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, computePosC_chal, computeOptPosInitC_chal,
        fgPatchShadowC_chal, chooseInitRandC_chal, Comp.queries]
      omega
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp only [sigKindInitiateSessLeg, extract1KeyActiveC, initiateGdh2ShadowB,
        letV_queries, bindV_queries, caseOptV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim_ddhQueries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, computePosC_chal, computeOptPosInitC_chal,
        fgPatchShadowC_chal, chooseInitRandC_chal, Comp.queries]
      omega
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp only [sigKindAcceptOpkSessLeg, acceptOpkGdh2ShadowB,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.acceptOpkGdhCoreShadowB,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.finishAcceptGdhC,
        letV_queries, bindV_queries, caseOptV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, computePosC_chal, mkSecretPosC_chal, fgPatchShadowC_chal,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.chooseRespRandC_chal, Comp.queries]
      omega
    · refine Nat.le_trans (liftSigDdhSessArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp only [sigKindAcceptNoOpkSessLeg, acceptNoOpkGdhShadowB,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.finishAcceptGdhC,
        letV_queries, bindV_queries, caseOptV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, computePosC_chal, fgPatchShadowC_chal,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.chooseRespRandC_chal, Comp.queries]
      omega
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigWrapGdh2NoFgLeg, wrapBase2, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, Comp.queries]
    · exact Nat.le_trans (sigKindRoArm_ddhQueries_le S _) (by omega)
    · simp [Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigWrapGdh2NoFgLeg, wrapBase2, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigWrapGdh2NoFgLeg, wrapSim2, registerGdhB, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_queries_le S _ _ _ _ tlSigDdhKeyInd_ddhW) ?_
      simp [sigWrapGdh2NoFgLeg, wrapBase2, letV_queries, bindV_queries,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
        gPrim_queries_wDdhGdh, Comp.queries]
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, sigKeyInd1KeyKindAtomicProg]
  nlinarith

@[local simp] private theorem loc_wrapBase2_primUB
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queriesUB wPrimGdh wsZero =
      c.queriesUB wPrimBase wsZeroBase := by
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

private theorem sigKindRoArm_primQueries_le (S : Setup) (f : KeyIndKFuels) :
    (sigKindRoArm S f).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 := by
  have hPre160 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 3 := by
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcPrimW lcZeroWS
      chalIfacePrimQueryWeight tlSigDdhKeyInd_primW _) ?_
    refine (liftGdhComp_queries_prim _).le.trans ?_
    refine Nat.le_trans (Comp.queries_le_queriesUB wPrimGdh wsZero _) ?_
    simp [roParsedPrePos160C, bindV_queriesUB, letV_queriesUB, mkSecretPosC_primUB, Comp.queriesUB]
  have hPre192 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 := by
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcPrimW lcZeroWS
      chalIfacePrimQueryWeight tlSigDdhKeyInd_primW _) ?_
    refine (liftGdhComp_queries_prim _).le.trans ?_
    refine Nat.le_trans (Comp.queries_le_queriesUB wPrimGdh wsZero _) ?_
    simp [roParsedPrePos192C, bindV_queriesUB, letV_queriesUB, mkSecretPosC_primUB, Comp.queriesUB]
  have hScan : (liftGdhAtomic gdhLift1Key (fgSessScanPackC f.kOn)).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold liftGdhAtomic; rw [samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcPrimW lcZeroWS
      chalIfacePrimQueryWeight tlSigDdhKeyInd_primW _) ?_
    refine (liftGdhComp_queries_prim _).le.trans ?_
    refine Nat.le_trans (Comp.queries_le_queriesUB wPrimGdh wsZero _) ?_
    simp [fgSessScanPackC,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessScanC,
      sessScanMinPredC, letV_queriesUB, findMV_queriesUB, entryMatchesC_primUB, Comp.queriesUB]
  have hSmp : (liftGdhAtomic gdhLift1Key (Γ := [])
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim sDrKey96)).queries
      chalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := rfl
  unfold sigKindRoArm roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
    sampleDrKey96LiftC
  simp only [runAt1, runAt2, runAt3, runAt4, Comp.queries, compRename_queries,
    avlSearchB192C_queries, avlInsertAtPathC_queries, hSmp]
  omega

private theorem liftSigDdhNoFgArm_primUB_le (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy)) :
    (liftSigDdhNoFgArm S payE arm).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      arm.queriesUB lcPrimW lcZeroWS :=
  Nat.le_trans (liftSigDdhNoFgArm_queries_le S payE arm lcPrimW chalIfacePrimQueryWeight tlSigDdhKeyInd_primW)
    (Comp.queries_le_queriesUB lcPrimW lcZeroWS arm)

private theorem liftSigDdhSessArm_primUB_le (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [.prod stTy Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy))) :
    (liftSigDdhSessArm S payE arm).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      arm.queriesUB lcPrimW lcZeroWS :=
  Nat.le_trans (liftSigDdhSessArm_queries_le S payE arm lcPrimW chalIfacePrimQueryWeight tlSigDdhKeyInd_primW)
    (Comp.queries_le_queriesUB lcPrimW lcZeroWS arm)

theorem sigKeyInd1KeyKindAtomicProg_q_prim (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyKindAtomicProg S b).totalQueries
      chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  have hInit : (sig1KeyKindInitC S b).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold sig1KeyKindInitC
    simp only [Comp.queries, Nat.add_zero, samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcPrimW lcZeroWS
      chalIfacePrimQueryWeight tlSigDdhKeyInd_primW _)
      (Nat.le_trans (Comp.queries_le_queriesUB lcPrimW lcZeroWS (sig1KeyKindBaseInit S b)) ?_)
    simp [sig1KeyKindBaseInit, bindV_queriesUB, s1Prim_primUB,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.sIndex_queriesUB,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.sBool_queriesUB, Comp.queriesUB]
  have hFin : sig1KeyKindFinishC.queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 0 := by
    unfold sig1KeyKindFinishC runAt2
    simp only [Comp.queries, compRename_queries, Nat.zero_add, samplerZeroQueryWeight_eq]
    refine Nat.le_trans (mapComp_queries_le tlSigDdhKeyInd lcPrimW lcZeroWS
      chalIfacePrimQueryWeight tlSigDdhKeyInd_primW _) ?_
    rfl
  have hfOnD : min (keyIndKFuelsOfBudget S b).kOn S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hfOnS : min (keyIndKFuelsOfBudget S b).kOn S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hH : (sig1KeyKindHandleC S b).queries chalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      160 + 76 * S.N_dh + 16 * S.N_sess_tot := by
    unfold sig1KeyKindHandleC
    dsimp only
    apply dispatchKeyIndQ_queries_le
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigKindInitPrinLeg, sig1KeyActiveInitPrinB, letV_queriesUB, bindV_queriesUB,
        s1Prim_primUB, sBytes32_queriesUB, qX25519Base_queriesUB, Comp.queriesUB]; omega
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigWrapGdh2NoFgLeg, corruptB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhToSigDdh_primUB, Comp.queriesUB]; omega
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigKindGenSpkLeg, sig1KeyTargetGenSpkB, genSpkGdh2B, loc_wrapSim2_primUB,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, s1Prim_primUB,
        liftGdhToSigDdh_primUB, gPrim_queriesUB_wPrimGdh, qSigDdhSign_primUB,
        sBytes32_queriesUB, sRandom64_queriesUB, qX25519Base_queriesUB, qSigSign_queriesUB,
        qKemKeyGen_queriesUB, Comp.queriesUB]; omega
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigWrapGdh2NoFgLeg, genOpkGdh2B, loc_wrapSim2_primUB, letV_queriesUB,
        bindV_queriesUB, liftGdhToSigDdh_primUB, gPrim_queriesUB_wPrimGdh,
        sBytes32_queriesUB, qX25519Base_queriesUB, Comp.queriesUB]; omega
    · refine Nat.le_trans (liftSigDdhSessArm_primUB_le S _ _) ?_
      simp only [sigKindInitiateSessLeg, extract1KeyActiveC, initiateGdh2ShadowB,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, s1Prim_primUB,
        liftGdhToSigDdh_primUB, gPrim_queriesUB_wPrimGdh,
        honestPeerC_primUB, koskBundleOkPowsC_primUB, resolveSigPkC_primUB,
        lookupSpkSkC_primUB, checkProvC_primUB, findHonestC_primUB, chooseInitRandC_primUB,
        computePosC_primUB, computeOptPosInitC_primUB, fgPatchShadowC_primUB,
        sBytes32_queriesUB, qX25519Base_queriesUB,
        qSigVerify_queriesUB, qKemEncaps_queriesUB, Comp.queriesUB]; linarith
    · refine Nat.le_trans (liftSigDdhSessArm_primUB_le S _ _) ?_
      simp only [sigKindInitiateSessLeg, extract1KeyActiveC, initiateGdh2ShadowB,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, s1Prim_primUB,
        liftGdhToSigDdh_primUB, gPrim_queriesUB_wPrimGdh,
        honestPeerC_primUB, koskBundleOkPowsC_primUB, resolveSigPkC_primUB,
        lookupSpkSkC_primUB, checkProvC_primUB, findHonestC_primUB, chooseInitRandC_primUB,
        computePosC_primUB, computeOptPosInitC_primUB, fgPatchShadowC_primUB,
        sBytes32_queriesUB, qX25519Base_queriesUB,
        qSigVerify_queriesUB, qKemEncaps_queriesUB, Comp.queriesUB]; linarith
    · refine Nat.le_trans (liftSigDdhSessArm_primUB_le S _ _) ?_
      simp only [sigKindAcceptOpkSessLeg, acceptOpkGdh2ShadowB,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.acceptOpkGdhCoreShadowB,
        finishAcceptGdhC, letV_queriesUB, bindV_queriesUB,
        caseOptV_queriesUB, liftGdhToSigDdh_primUB, gPrim_queriesUB_wPrimGdh,
        koskSenderOkPowsC_primUB, findHonestC_primUB, chooseRespRandC_primUB,
        computePosC_primUB, mkSecretPosC_primUB, fgPatchShadowC_primUB,
        qX25519_queriesUB, qIsCanonical_queriesUB, qKemDecaps_queriesUB,
        Comp.queriesUB]; linarith
    · refine Nat.le_trans (liftSigDdhSessArm_primUB_le S _ _) ?_
      simp only [sigKindAcceptNoOpkSessLeg, acceptNoOpkGdhShadowB, finishAcceptGdhC,
        letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, liftGdhToSigDdh_primUB,
        gPrim_queriesUB_wPrimGdh,
        koskSenderOkPowsC_primUB, findHonestC_primUB, chooseRespRandC_primUB,
        computePosC_primUB, fgPatchShadowC_primUB,
        qX25519_queriesUB, qIsCanonical_queriesUB, qKemDecaps_queriesUB,
        Comp.queriesUB]; linarith
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigWrapGdh2NoFgLeg, testB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhToSigDdh_primUB, Comp.queriesUB]; omega
    · exact Nat.le_trans (sigKindRoArm_primQueries_le S (keyIndKFuelsOfBudget S b)) (by omega)
    · simp [Comp.queries]
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigWrapGdh2NoFgLeg, revealB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhToSigDdh_primUB, Comp.queriesUB]; omega
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigWrapGdh2NoFgLeg, registerGdhB, loc_wrapSim2_primUB, letV_queriesUB,
        bindV_queriesUB, liftGdhToSigDdh_primUB, gPrim_queriesUB_wPrimGdh,
        qX25519Base_queriesUB, qPow8_queriesUB, Comp.queriesUB]; omega
    · refine Nat.le_trans (liftSigDdhNoFgArm_primUB_le S _ _) ?_
      simp only [sigWrapGdh2NoFgLeg, revealSpkB, loc_wrapBase2_primUB, letV_queriesUB,
        bindV_queriesUB, caseOptV_queriesUB, liftGdhToSigDdh_primUB, Comp.queriesUB]; omega
  have hMul := Nat.mul_le_mul_left b.q_total hH
  have hTot : (sigKeyInd1KeyKindAtomicProg S b).totalQueries
      chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      b.q_total * (160 + 76 * S.N_dh + 16 * S.N_sess_tot) := by
    dsimp only [CostedReduction.totalQueries, sigKeyInd1KeyKindAtomicProg]; omega
  unfold primQueryBudget; nlinarith

end

section SizeBounds

open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (avlHeightCap)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBoundsCost (
  sigInitFinish_size_le sig1KeyKindHandleC_size_le)

theorem sigKeyInd1KeyKindAtomicProg_size_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyKindAtomicProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  let f := keyIndKFuelsOfBudget S b
  rcases sigInitFinish_size_le S b with ⟨hInit, hFin⟩
  have hHdl := sig1KeyKindHandleC_size_le S b
  have hbQ : bits b.q_total ≤ bits (stepCostBudget S b) :=
    bits_le_bits_stepCostBudget S b (by omega)
  have hbQ1 : bits (b.q_total + 1) ≤ bits (stepCostBudget S b) :=
    bits_le_bits_stepCostBudget S b (by omega)
  have hbSent : bits (keyIndSentinel S b) ≤ bits (stepCostBudget S b) :=
    le_trans (_root_.ReductionDsl.bits_mono
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.keyIndSentinel_le S b)) hbQ1
  have hbSig : bits (activeSigBudget S b) ≤ bits (stepCostBudget S b) :=
    le_trans (_root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)) hbQ
  have hbOn : bits f.kOn ≤ bits (stepCostBudget S b) :=
    le_trans (_root_.ReductionDsl.bits_mono (show f.kOn ≤ b.q_total from Nat.min_le_right _ _)) hbQ
  have hbDh : bits (min f.kOn S.N_dh) ≤ bits (stepCostBudget S b) :=
    le_trans (_root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)) hbOn
  have hbSess : bits (min f.kOn S.N_sess_tot) ≤ bits (stepCostBudget S b) :=
    le_trans (_root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)) hbOn
  have hbFg : bits f.kFg ≤ bits (stepCostBudget S b) :=
    le_trans (_root_.ReductionDsl.bits_mono (show f.kFg ≤ b.q_total from Nat.min_le_left _ _)) hbQ
  have hbAvl : bits (avlHeightCap f.kAvl) ≤ bits (stepCostBudget S b) := by
    apply _root_.ReductionDsl.bits_mono
    have hkAvl : f.kAvl ≤ 3 * b.q_total + 1 := by
      dsimp only [f, keyIndKFuelsOfBudget]
      have := Nat.min_le_right b.q_on b.q_total
      have := Nat.min_le_right b.q_ro b.q_total
      omega
    have hLog : bits f.kAvl ≤ f.kAvl + 1 := by
      rw [bits_eq_log2_succ]
      exact Nat.succ_le_succ (Nat.log_le_self 2 f.kAvl)
    have hCap : avlHeightCap f.kAvl ≤ 6 * b.q_total + 4 := by
      unfold avlHeightCap; omega
    unfold stepCostBudget; dsimp only
    have hMul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  have hRedB : 256000 ≤ reductionSizeBudget := by decide
  have hMulB : 1788 * bits (stepCostBudget S b) ≤ 2 ^ 12 * bits (stepCostBudget S b) :=
    Nat.mul_le_mul_right _ (by decide)
  unfold CostedReduction.size sigKeyInd1KeyKindAtomicProg
  dsimp only [f] at *
  omega

end SizeBounds

section CostByKindAndTotal

open Computational.Proofs.ReductionDsl.KindedDispatch (costBoundedByKind_fin2_of_armCosts)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (sig1KeyActiveKindStTy)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBoundsCost (
  sigKindRoArm_cost_le dispatchKeyIndQ_cost_le sigOnlineArmBudget sigOnlineArms_all_cost_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost (
  keyInd_gpair_sum_eq)

private theorem total_budget_arith (q M_dh M_sess logDh logSess : Nat) :
    (22 * logDh + 11 * q + 2922) +
      q * (22536 * q + 25100 * M_dh + 23100 * M_sess + 102291) + 10000 ≤
      2 ^ 16 * (q + 1) * (q + 1) +
        2 ^ 15 * (q + 1) * (M_dh + M_sess) +
        2 ^ 10 * (q + 1) * (logDh + logSess) +
        2 ^ 11 * M_dh ^ 2 + 2 ^ 8 * M_dh * M_sess :=
  Nat.le.intro (k := 43000 * q ^ 2 + 28770 * q + 52614 + 7668 * q * M_dh + 32768 * M_dh +
    9668 * q * M_sess + 32768 * M_sess + 1024 * q * logDh + 1002 * logDh +
    1024 * q * logSess + 1024 * logSess + 2048 * M_dh ^ 2 + 256 * M_dh * M_sess) (by ring)

private theorem max_uCost_codecCost_le (S : Setup) {x y : Nat} (h : x ≤ y) :
    max pqSigAndDdhIface.uCost (x + (pqKeyIndCodec S).codecCost) ≤ y + 64 := by
  have hU : pqSigAndDdhIface.uCost ≤ 64 := by decide
  have hC : (pqKeyIndCodec S).codecCost = 64 := rfl
  omega

theorem sigKeyInd1KeyKindAtomicProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyKindAtomicProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  let f := keyIndKFuelsOfBudget S b
  let q := b.q_total
  let M_dh := min q S.N_dh
  let M_sess := min q S.N_sess_tot
  let B := 22536 * q + 25100 * M_dh + 23100 * M_sess + 102200
  have hkOn : f.kOn ≤ q := Nat.min_le_right _ _
  have hkFg : f.kFg ≤ q := Nat.min_le_left _ _
  have hmDh : min f.kOn S.N_dh ≤ M_dh := by
    dsimp only [M_dh]; have := Nat.min_le_left f.kOn S.N_dh; have := Nat.min_le_right f.kOn S.N_dh; omega
  have hmSess : min f.kOn S.N_sess_tot ≤ M_sess := by
    dsimp only [M_sess]
    have := Nat.min_le_left f.kOn S.N_sess_tot
    have := Nat.min_le_right f.kOn S.N_sess_tot
    omega
  have hOnLeB : sigOnlineArmBudget S f ≤ B := by
    dsimp only [sigOnlineArmBudget, B]; omega
  have hAvlLe : bits f.kAvl ≤ 3 * q + 2 := by
    have hkAvl : f.kAvl ≤ 3 * q + 1 := by
      dsimp only [f, keyIndKFuelsOfBudget, q]
      have := Nat.min_le_right b.q_on b.q_total
      have := Nat.min_le_right b.q_ro b.q_total
      omega
    have hLog : bits f.kAvl ≤ f.kAvl + 1 := by
      rw [bits_eq_log2_succ]; exact Nat.succ_le_succ (Nat.log_le_self 2 f.kAvl)
    omega
  have hRoLeB : (sigKindRoArm S f).cost ≤ B := by
    have hRo := sigKindRoArm_cost_le S f
    dsimp only [B]; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12, h13, h14⟩ := sigOnlineArms_all_cost_le S f
  have hHandle : (sig1KeyKindHandleC S b).cost ≤ B + 27 := by
    unfold sig1KeyKindHandleC; dsimp only
    refine (dispatchKeyIndQ_cost_le S .v1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (h1.trans hOnLeB) (h2.trans hOnLeB) (h3.trans hOnLeB) (h4.trans hOnLeB)
      (h5.trans hOnLeB) (h6.trans hOnLeB) (h7.trans hOnLeB) (h8.trans hOnLeB)
      (h9.trans hOnLeB) hRoLeB (h11.trans hOnLeB) (h12.trans hOnLeB)
      (h13.trans hOnLeB) (h14.trans hOnLeB)).trans ?_
    have hv1 : (.v1 : Expr pqAtomicOps [sig1KeyActiveKindStTy, (pqKeyIndCodec S).Q] _).cost = 1 := rfl
    omega
  have hInit : (sig1KeyKindInitC S b).cost ≤ 22 * Nat.log 2 S.N_dh + 11 * q + 2922 := by
    have hI := sig1KeyKindInitC_cost_le_split S b
    have hbOn : bits (min b.q_on b.q_total + 1) ≤ q + 2 := by
      rw [bits_eq_log2_succ]
      have := Nat.log_le_self 2 (min b.q_on b.q_total + 1)
      have := Nat.min_le_right b.q_on b.q_total
      omega
    omega
  have hFin := sig1KeyKindFinishC_cost_le
  have hMax : max pqSigAndDdhIface.uCost ((sig1KeyKindHandleC S b).cost + (pqKeyIndCodec S).codecCost) ≤
      B + 91 := max_uCost_codecCost_le S hHandle
  unfold CostedReduction.totalCost sigKeyInd1KeyKindAtomicProg; dsimp only
  exact (Nat.add_le_add (Nat.add_le_add hInit (Nat.mul_le_mul_left q hMax)) hFin).trans
    (total_budget_arith q M_dh M_sess (Nat.log 2 S.N_dh) (Nat.log 2 S.N_sess_tot))

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

theorem sigKeyInd1KeyKindAtomicProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ (sigKeyInd1KeyKindAtomicProg S b) :=
  gredBlockBounded_of_cost one_le_pqSigAndDdhIface_qCost S b ℓ
    (sigKeyInd1KeyKindAtomicProg S b) rfl
    (sigKeyInd1KeyKindAtomicProg_totalCost_le S b)
    (sigKeyInd1KeyKindAtomicProg_size_le S b)

private theorem split_budget_arith (M_on M_off M_dh M_sess logDh logSess bAvl : Nat) :
    (22 * logDh + 11 * M_on + 2922) +
      M_on * (1336 * M_off + 22536 * M_on + 25100 * M_dh + 23100 * M_sess + 102290) +
      M_off * (4420 * bAvl + 1345 * M_on + 8884) + 10000 ≤
      2 ^ 16 * (M_on + 1) * (M_on + 1) +
        2 ^ 15 * (M_on + 1) * (M_dh + M_sess) +
        2 ^ 10 * (M_on + M_off + 1) * (logDh + logSess) +
        2 ^ 13 * (M_off + M_on) * (bAvl + 4) +
        2 ^ 13 * M_off * M_on +
        2 ^ 11 * M_dh ^ 2 + 2 ^ 8 * M_dh * M_sess := by
  have _hGpair := keyInd_gpair_sum_eq (A := Computational.Proofs.SignalPqxdh.AtomicLift.aiSigDdh)
  exact Nat.le.intro (k := 43000 * M_on ^ 2 + 61539 * M_on + 52614 +
    7668 * M_on * M_dh + 32768 * M_dh + 9668 * M_on * M_sess + 32768 * M_sess +
    1024 * M_on * logDh + 1024 * M_off * logDh + 1002 * logDh +
    1024 * M_on * logSess + 1024 * M_off * logSess + 1024 * logSess +
    3772 * M_off * bAvl + 8192 * M_on * bAvl + 23884 * M_off +
    5511 * M_off * M_on + 2048 * M_dh ^ 2 + 256 * M_dh * M_sess) (by ring)

theorem sigKeyInd1KeyKindAtomicProg_costByKind (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyKindAtomicProg S b).CostBoundedByKind keyIndQueryKind (keyIndKindCounts b)
      (stepCostBudgetSplit S b b.q_ro) := by
  let f := keyIndKFuelsOfBudget S b
  let M_on := min b.q_on b.q_total
  let M_off := min b.q_ro b.q_total
  let M_dh := min M_on S.N_dh
  let M_sess := min M_on S.N_sess_tot
  let bAvl := bits (M_off + 2 * M_on + 1)
  let c0 := 1336 * M_off + 22536 * M_on + 25100 * M_dh + 23100 * M_sess + 102226
  let c1 := 4420 * bAvl + 1345 * M_on + 8820
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12, h13, h14⟩ := sigOnlineArms_all_cost_le S f
  refine costBoundedByKind_fin2_of_armCosts (sigKeyInd1KeyKindAtomicProg S b)
    keyIndQueryKind (keyIndKindCounts b) (c0 := c0) (c1 := c1) (fun s q hq => ?_) (fun s q hq => ?_) ?_
  · dsimp only [sigKeyInd1KeyKindAtomicProg]
    unfold sig1KeyKindHandleC; dsimp only
    refine (dispatchKeyIndQ_online_costAt_le S (sigOnlineArmBudget S f) s q hq
      _ _ _ _ _ _ _ _ _ (sigKindRoArm S f) _ _ _ _
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14).trans ?_
    have hkFg : f.kFg ≤ M_on + M_off := Nat.min_le_right _ _
    dsimp only [sigOnlineArmBudget, c0, f, keyIndKFuelsOfBudget, M_on, M_off, M_dh, M_sess] at hkFg ⊢
    omega
  · cases q with
    | roQuery sec =>
      dsimp only [sigKeyInd1KeyKindAtomicProg]
      unfold sig1KeyKindHandleC; dsimp only
      refine (dispatchKeyIndQ_ro_costAt_le S s sec _ _ _ _ _ _ _ _ _
        (sigKindRoArm S (keyIndKFuelsOfBudget S b)) _ _ _ _).trans ?_
      refine (Nat.add_le_add_right (sigKindRoArm_cost_le S (keyIndKFuelsOfBudget S b)) 20).trans ?_
      dsimp only [c1, bAvl, M_on, M_off, keyIndKFuelsOfBudget]
      omega
    | _ => simp [keyIndQueryKind] at hq
  · dsimp only [sigKeyInd1KeyKindAtomicProg]
    have hInit : (sig1KeyKindInitC S b).cost ≤ 22 * Nat.log 2 S.N_dh + 11 * M_on + 2922 := by
      have hI := sig1KeyKindInitC_cost_le_split S b
      have hbOn : bits (M_on + 1) ≤ M_on + 2 := by
        rw [bits_eq_log2_succ]; exact Nat.succ_le_succ (Nat.log_le_self 2 (M_on + 1))
      dsimp only [M_on] at hbOn ⊢; omega
    have hFin := sig1KeyKindFinishC_cost_le
    have hK0 : keyIndKindCounts b 0 = M_on := rfl
    have hK1 : keyIndKindCounts b 1 = M_off := rfl
    have hM0 : max pqSigAndDdhIface.uCost (c0 + (pqKeyIndCodec S).codecCost) ≤ c0 + 64 :=
      max_uCost_codecCost_le S le_rfl
    have hM1 : max pqSigAndDdhIface.uCost (c1 + (pqKeyIndCodec S).codecCost) ≤ c1 + 64 :=
      max_uCost_codecCost_le S le_rfl
    rw [hK0, hK1]
    exact (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add hInit (Nat.mul_le_mul_left M_on hM0))
          (Nat.mul_le_mul_left M_off hM1)) hFin).trans
      (split_budget_arith M_on M_off M_dh M_sess (Nat.log 2 S.N_dh) (Nat.log 2 S.N_sess_tot) bAvl)

end CostByKindAndTotal

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBounds
