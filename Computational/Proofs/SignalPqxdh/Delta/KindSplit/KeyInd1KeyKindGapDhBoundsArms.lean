/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
# Arm-Level Cost and Program-Size Bounds for `fgKeyInd1KeyGapDhKindAtomicProg`

Proves per-arm `pqAtomicOps` step-cost bounds (`Comp.cost` and `Comp.costAt` by query kind) and
syntactic `Comp.size` bounds for the 14-way query handler of `fgKeyInd1KeyGapDhKindAtomicProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBoundsArms

public section

set_option autoImplicit false

open OracleSpec
open _root_.ReductionDsl (Expr Comp Var Ty Env Iface CostedReduction
  pqAtomicSig pqAtomicOps pqAtomicSamplers pqSigAndDdhIface pqKeyIndCodec
  B PB drKeyT bits bits_mono reductionSizeBudget atomicPureOps AtomicPureOp)
open _root_.SignalPqxdh (Setup QueryBudget keyIndSpec KeyIndQuery
  activeIdCount activeSpkCount activeOpkCount activeSendCount activeSendOpkCount)
open _root_.SignalPqxdh.Security (stepCostBudget keyIndQueryKind)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps sigAndDdhOracle ChallengerOracle U32)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT v letV bindV caseOptV caseSumV findMV mapMV foldMV anyMV
  isSomeE eCaseOpt eCaseSum eAny eFind eMap eLet eLet2 litB rNone
  keyIndRespTy initQTy accQTy keyIndStateTy simTy paramsTy params2Ty gdhStateTy gdhState2Ty
  emptySimE emptyStE smMk smUpd stMk stUpd smBase paMk pa2Mk
  paU paV paUp paPrinFlag paPrinIdx paSpkIdx paOpkMode paOpkIdx paMode
  pa2U pa2V pa2Up pa2OpkMode
  wrapBase2 wrapSim2 corruptB testB revealB registerGdhB revealSpkB
  finishAcceptGdhC chooseArm2C bernoulliRatioGdhC
  sBool sIndex sBytes32 sRandom64 sDrKey96
  qX25519 qX25519Base qPow8 qIsCanonical qSigPkGen qSigSign qSigVerify
  qKemKeyGen qKemEncaps qKemDecaps
  fgPosTy fgPatchEntryTy drKeyTy bits_0 bits_1 bits_2 bits_3 bits_32 bits_eq_log2_succ)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  activeSigBudget fgActiveTotalIndexCount optNatMatchesE gdh1KeyActiveStateTy
  initPrin1KeyActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB genOpkActiveGdhB)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  TagLift mapExpr mapComp tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe embedTy embedCtx
  compRename exprRename exprRename_cost compRename_cost exprRename_size compRename_size
  mapExpr_size mapComp_size_le compLitSize exprLitSize pqOpLitSize pqxdhOps_opSize
  mapComp_cost_eleven_mul_le mapComp_cost_two_mul_le
  finSidToNatExpr bits_le_bits_stepCostBudget)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlHeightCap aop)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (
  avlSearchB192C_size_le avlInsertAtPathC_size_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  keyIndSentinel keyIndSentinel_le dispatchKeyIndQ
  finPairToNatE finTripleToNatE initPayToNatE accPayToNatE atomicRNoneE
  runAt2 runAt3 runAt4 ren1)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost (
  dispatchKeyIndQ_online_costAt_le dispatchKeyIndQ_ro_costAt_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget
  fgShadowAtomicTy fgSessCtrTy seqFgEntryTy gdhLift1Key liftGdhAtomic runAt1
  roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
  roParsedPrePos160C roParsedPrePos192C fgSessScanPackC sessScanMinPredC sampleDrKey96LiftC
  fgPatchShadowC initiateGdhActiveShadowInnerB acceptOpkGdh2ShadowB acceptNoOpkGdhShadowB
  gdhFinishK extractMode0KC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost (
  roParsedShadowAtomicC_cost_le
  initiateGdhActiveShadowInnerB_atomic_cost_le
  acceptOpkGdh2ShadowB_atomic_cost_le
  acceptNoOpkGdhShadowB_atomic_cost_le)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  initParams1KeyKindC gdhKindInitPrinLeg gdhKindGenSpkLeg gdhKindGenOpkLeg gdhWrapDelegNoFgLeg
  gdhKindInitiateSessLeg gdhKindAcceptOpkSessLeg gdhKindAcceptNoOpkSessLeg
  gdh1KeyActiveKindStateTy liftSigDdhNoFgArm liftSigDdhSessArm gdhKindRoArm
  gdh1KeyKindBaseInit gdh1KeyKindInitC gdh1KeyKindHandleC gdh1KeyKindFinishC
  fgKeyInd1KeyGapDhKindAtomicProg)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  liftGdhComp liftGdhComp_cost liftGdhComp_costUB liftGdhComp_size
  sigChalQ_dsl sigChalQ_dsl_costUB sigChalQ_dsl_size)

/-- Uniform per-step `pqAtomicOps` cost budget across the 13 online arms of `gdh1KeyKindHandleC`. -/
@[expose] def gdhOnlineArmBudget (S : Setup) (f : KeyIndKFuels) : Nat :=
  1336 * f.kFg + 12500 * f.kOn + 25500 * min f.kOn S.N_dh +
    23500 * min f.kOn S.N_sess_tot + 102000

section ArmCosts

open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  natEq nat2Eq nat3Eq sidEq
  stPrin stSpks stOpks peIkAPk peSecIKAsign peUpd peMk sbSpkPk sbPqspkPk sbUpd sbMk
  buIkB buSpkB buSpkSig buPqspkB buPqspkSig buMk
  rInitPrin rBundle rPk rCorr rDrKey rSpkSk oeMk seMk seUpd reMk reUpd rs freshE
  encEC encKEM widenEC consB widenB)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (
  letV_costUB bindV_costUB caseOptV_costUB eLet_costUB eCaseOpt_costUB eCaseSum_costUB
  eFind_costUB eAny_costUB eMap_costUB
  litB_costUB lenB_costUB eqB_costUB u32OfNat_costUB
  sBytes32_costUB sRandom64_costUB qX25519Base_costUB qPow8_costUB
  qSigPkGen_costUB qSigSign_costUB qSigVerify_costUB qKemKeyGen_costUB
  gPrim_costUB v_costUB encEC_costUB encKEM_costUB
  rNone_costUB rInitPrin_costUB rPk_costUB rCorr_costUB rBundle_costUB rDrKey_costUB rSpkSk_costUB
  smBase_costUB smFgL_costUB smRaw_costUB smLog_costUB smPows_costUB)
open Computational.Proofs.SignalPqxdh.AtomicLift (expr_cost_two_mul_le)

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.pqSamplers

private theorem expr_cost_le_costUB_loc {Γ : List PT} {τ : PT} (e : Expr pqxdhOps Γ τ) :
    e.cost ≤ e.costUB := by
  have h := (Comp.ret (I := _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface) e).cost_le_costUB
  simp only [Comp.cost, Comp.costUB] at h; omega

private theorem mapExpr_cost_le_two_costUB_loc {Γ : List PT} {τ : PT} (e : Expr pqxdhOps Γ τ) :
    (mapExpr e).cost ≤ 2 * e.costUB := by
  have h1 := expr_cost_two_mul_le e
  have h2 := expr_cost_le_costUB_loc e
  omega

private theorem mapComp_sigDdh_cost_le_eleven_costUB {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface Γ τ) :
    (mapComp tlSigDdhKeyInd c).cost ≤ 11 * c.costUB := by
  have h1 := mapComp_cost_eleven_mul_le tlSigDdhKeyInd c
  have h2 := c.cost_le_costUB
  omega

private theorem mapComp_liftGdhComp_cost_le_three_costUB {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ τ) :
    (mapComp tlSigDdhKeyInd (liftGdhComp c)).cost ≤ 3 * c.costUB := by
  have heq : (mapComp tlSigDdhKeyInd (liftGdhComp c)).cost =
      (liftGdhAtomic gdhLift1Key c).cost := rfl
  rw [heq,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost.liftGdhAtomic_gdhLift1Key_cost_eq]
  have h11 := mapComp_cost_eleven_mul_le Computational.Proofs.SignalPqxdh.AtomicLift.tlGapDhKeyInd c
  have hUB := c.cost_le_costUB
  dsimp only [liftGdhAtomic,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.gdhLift2Key]
  omega

private theorem letV_sigDdh_cost_le {Γ : List PT} {τ₁ τ₂ : PT}
    (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface (τ₁ :: Γ) τ₂)
    {Bk : Nat} (hk : (mapComp tlSigDdhKeyInd (k .zero)).cost ≤ Bk) :
    (mapComp tlSigDdhKeyInd (letV e k)).cost ≤ 2 * e.costUB + Bk + 2 := by
  have he := mapExpr_cost_le_two_costUB_loc e
  simp only [letV, mapComp, Comp.cost] at hk ⊢; omega

private theorem bindV_sigDdh_cost_le {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface (τ₁ :: Γ) τ₂)
    {Bm Bk : Nat} (hm : (mapComp tlSigDdhKeyInd m).cost ≤ Bm)
    (hk : (mapComp tlSigDdhKeyInd (k .zero)).cost ≤ Bk) :
    (mapComp tlSigDdhKeyInd (bindV m k)).cost ≤ Bm + Bk + 1 := by
  simp only [bindV, mapComp, Comp.cost] at hm hk ⊢; omega

private theorem ite_sigDdh_cost_le {Γ : List PT} {τ : PT}
    (b : Expr pqxdhOps Γ .bool)
    (t e : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface Γ τ)
    {Bt Be : Nat} (ht : (mapComp tlSigDdhKeyInd t).cost ≤ Bt)
    (he : (mapComp tlSigDdhKeyInd e).cost ≤ Be) :
    (mapComp tlSigDdhKeyInd (.ite b t e)).cost ≤ 2 * b.costUB + max Bt Be + 1 := by
  have hb := mapExpr_cost_le_two_costUB_loc b
  simp only [mapComp, Comp.cost] at ht he ⊢; omega

private theorem ret_sigDdh_cost_le {Γ : List PT} {τ : PT} (e : Expr pqxdhOps Γ τ) :
    (mapComp tlSigDdhKeyInd (I := _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface) (.ret e)).cost ≤
      2 * e.costUB + 1 := by
  have h := mapExpr_cost_le_two_costUB_loc e
  dsimp only [mapComp, Comp.cost]; omega

theorem gdhKindRoArm_cost_le (S : Setup) (f : KeyIndKFuels) :
    (gdhKindRoArm S f).cost ≤ 4420 * bits f.kAvl + 1345 * f.kOn + 8700 := by
  have hRo := roParsedShadowAtomicC_cost_le gdhLift1Key f
  unfold gdhKindRoArm runAt2
  simp only [Comp.cost, compRename_cost, exprRename_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

set_option linter.unusedSimpArgs false in
private theorem gdhPayExprs_cost_le (S : Setup) {A : Ty pqAtomicSig} (N_s N_o : Nat) :
    (aop (.finVal S.N_id) (.v0 : Expr pqAtomicOps [.base (.fin S.N_id), A, (pqKeyIndCodec S).Q] _)).cost ≤ 60 ∧
    (finPairToNatE S.N_id S.N_recv
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)), A, (pqKeyIndCodec S).Q] _)).cost ≤ 60 ∧
    (finTripleToNatE S.N_id S.N_recv S.N_opk
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))),
        A, (pqKeyIndCodec S).Q] _)).cost ≤ 60 ∧
    (finSidToNatExpr S (.v0 : Expr pqAtomicOps (_root_.ReductionDsl.sidT S :: [A, (pqKeyIndCodec S).Q]) _)).cost ≤ 60 ∧
    (initPayToNatE N_s S
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s))
        (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))), A, (pqKeyIndCodec S).Q] _)).cost ≤ 60 ∧
    (accPayToNatE N_o S
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv))
        (.prod (.base (.fin N_o)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))),
        A, (pqKeyIndCodec S).Q] _)).cost ≤ 60 ∧
    (.v0 : Expr pqAtomicOps [PB 32, A, (pqKeyIndCodec S).Q] (PB 32)).cost ≤ 60 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [finPairToNatE, finTripleToNatE, finSidToNatExpr, initPayToNatE, accPayToNatE,
      aop, Expr.cost, Expr.v0, pqAtomicOps, atomicPureOps, AtomicPureOp.cost]; omega)

private theorem liftSigDdhNoFgArm_cost_le (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy)) :
    (liftSigDdhNoFgArm S payE arm).cost ≤ payE.cost + (mapComp tlSigDdhKeyInd arm).cost + 20 := by
  unfold liftSigDdhNoFgArm runAt2
  simp only [Comp.cost, compRename_cost, exprRename_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem liftSigDdhSessArm_cost_le (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [.prod stTy fgSessCtrTy, qPayTy] (.prod keyIndRespTy (.prod stTy fgSessCtrTy))) :
    (liftSigDdhSessArm S payE arm).cost ≤ payE.cost + (mapComp tlSigDdhKeyInd arm).cost + 40 := by
  unfold liftSigDdhSessArm runAt2
  simp only [Comp.cost, compRename_cost, exprRename_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

set_option linter.unusedSimpArgs false in
private theorem gdhWrapDelegNoFgLeg_atomic_cost_le {qPayTy : PT}
    (gdhBody : Var [params2Ty, paramsTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.gdh1KeyStateTy,
        gdh1KeyActiveStateTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, paramsTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.gdh1KeyStateTy,
        gdh1KeyActiveStateTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, paramsTy,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.gdh1KeyStateTy,
        gdh1KeyActiveStateTy, qPayTy] keyIndStateTy →
      Var [gdh1KeyActiveStateTy, qPayTy] qPayTy →
      Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
        [keyIndStateTy, simTy, params2Ty, paramsTy,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.gdh1KeyStateTy,
          gdh1KeyActiveStateTy, qPayTy]
        (.prod keyIndRespTy gdhState2Ty)) :
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg gdhBody)).cost ≤
      3 * (gdhBody .zero .zero .zero (.succ .zero)).costUB + 200 := by
  apply Nat.le_trans
  · dsimp only [gdhWrapDelegNoFgLeg]
    apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
    apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
    apply bindV_sigDdh_cost_le
    · exact mapComp_liftGdhComp_cost_le_three_costUB _
    · exact ret_sigDdh_cost_le _
  · simp only [pa2Mk, paU, paV, paUp, paOpkMode, smBase_costUB, v_costUB, Expr.costUB, bits_1]
    omega

set_option linter.unusedSimpArgs false in
private theorem gdhSessLegs_atomic_cost_le (S : Setup) (f : KeyIndKFuels) :
    (∀ hasOpk, (mapComp tlSigDdhKeyInd (gdhKindInitiateSessLeg S f hasOpk)).cost ≤
      1336 * f.kFg + 12000 * f.kOn + 7000 * min f.kOn S.N_dh +
        23000 * min f.kOn S.N_sess_tot + 55300) ∧
    (mapComp tlSigDdhKeyInd (gdhKindAcceptOpkSessLeg S f)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35400 ∧
    (mapComp tlSigDdhKeyInd (gdhKindAcceptNoOpkSessLeg S f)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35400 := by
  refine ⟨fun hasOpk => ?_, ?_, ?_⟩
  · apply Nat.le_trans
    · dsimp only [gdhKindInitiateSessLeg]
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le
      apply bindV_sigDdh_cost_le
      · simpa only [liftGdhAtomic, gdhLift1Key] using
          initiateGdhActiveShadowInnerB_atomic_cost_le gdhLift1Key S f
            .zero .zero .zero .zero .zero hasOpk (.succ .zero)
      · exact ret_sigDdh_cost_le _
    · simp only [smBase_costUB, v_costUB, Expr.costUB]
      linarith
  · apply Nat.le_trans
    · dsimp only [gdhKindAcceptOpkSessLeg]
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le
      apply bindV_sigDdh_cost_le
      · simpa only [liftGdhAtomic, gdhLift1Key] using
          acceptOpkGdh2ShadowB_atomic_cost_le gdhLift1Key S f
            .zero .zero .zero .zero (.succ .zero)
      · exact ret_sigDdh_cost_le _
    · simp only [pa2Mk, paU, paV, paUp, paOpkMode, smBase_costUB, v_costUB, Expr.costUB, bits_1]
      linarith
  · apply Nat.le_trans
    · dsimp only [gdhKindAcceptNoOpkSessLeg]
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply bindV_sigDdh_cost_le
      · simpa only [liftGdhAtomic, gdhLift1Key] using
          acceptNoOpkGdhShadowB_atomic_cost_le gdhLift1Key S f
            .zero .zero .zero (.succ .zero)
      · exact ret_sigDdh_cost_le _
    · simp only [smBase_costUB, v_costUB, Expr.costUB]
      linarith

set_option linter.unusedSimpArgs false in
private theorem gdhNoFgLegs_atomic_cost_le (K : Nat) :
    (mapComp tlSigDdhKeyInd (gdhKindInitPrinLeg K)).cost ≤ 12000 * K + 20000 ∧
    (mapComp tlSigDdhKeyInd (gdhKindGenSpkLeg K)).cost ≤ 12000 * K + 101000 ∧
    (mapComp tlSigDdhKeyInd (gdhKindGenOpkLeg K)).cost ≤ 12000 * K + 20000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt u =>
      wrapBase2 pa sm (corruptB K bSt u))).cost ≤ 12000 * K + 20000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt sid =>
      wrapBase2 pa sm (testB K bSt sid))).cost ≤ 12000 * K + 20000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt sid =>
      wrapBase2 pa sm (revealB K bSt sid))).cost ≤ 12000 * K + 20000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt sk =>
      wrapSim2 pa (registerGdhB sm bSt sk))).cost ≤ 12000 * K + 20000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt x =>
      wrapBase2 pa sm (revealSpkB K bSt x))).cost ≤ 12000 * K + 20000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mapComp_sigDdh_cost_le_eleven_costUB _).trans ?_
    simp only [gdhKindInitPrinLeg, initPrin1KeyActiveGdhB,
      paPrinFlag, paPrinIdx, paUp, smUpd, smMk,
      smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      stPrin, stUpd, stMk, peMk, rNone_costUB, rInitPrin_costUB, natEq,
      letV_costUB, bindV_costUB, liftGdhComp_costUB, gPrim_costUB,
      sBytes32_costUB, qX25519Base_costUB, eAny_costUB, litB_costUB,
      v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
    omega
  · apply Nat.le_trans
    · dsimp only [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB]
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply ite_sigDdh_cost_le
      · exact mapComp_sigDdh_cost_le_eleven_costUB _
      · apply bindV_sigDdh_cost_le
        · exact mapComp_liftGdhComp_cost_le_three_costUB _
        · exact ret_sigDdh_cost_le _
    · simp only [genSpkGdhActiveB, optNatMatchesE, eLet2,
        paSpkIdx, paV, smUpd, smMk,
        smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        stPrin, stSpks, stUpd, stMk, peIkAPk, peSecIKAsign, sbMk, buMk,
        rNone_costUB, rBundle_costUB, nat2Eq, natEq,
        letV_costUB, bindV_costUB, caseOptV_costUB, liftGdhComp_costUB, gPrim_costUB,
        sigChalQ_dsl_costUB, sBytes32_costUB, sRandom64_costUB,
        qX25519Base_costUB, qKemKeyGen_costUB, qSigSign_costUB,
        encEC_costUB, encKEM_costUB, eLet_costUB, eCaseOpt_costUB, eAny_costUB, eFind_costUB,
        u32OfNat_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
        List.length_nil, PNat.val_ofNat, bits_0, bits_1]
      omega
  · refine (mapComp_sigDdh_cost_le_eleven_costUB _).trans ?_
    simp only [gdhKindGenOpkLeg, genOpkActiveGdhB,
      paOpkMode, paOpkIdx, paV, smUpd, smMk,
      smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      stOpks, stUpd, stMk, oeMk, rNone_costUB, rPk_costUB, nat3Eq, nat2Eq, natEq,
      letV_costUB, bindV_costUB, liftGdhComp_costUB, gPrim_costUB,
      sBytes32_costUB, qX25519Base_costUB, eAny_costUB, litB_costUB,
      v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
    omega
  · refine (gdhWrapDelegNoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, corruptB, rs, peUpd, peMk, stUpd, stMk, smUpd, smMk,
      gPrim_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      rNone_costUB, rCorr_costUB, bindV_costUB, caseOptV_costUB, eFind_costUB, eMap_costUB,
      natEq, v_costUB, Comp.costUB, Expr.costUB]; omega
  · refine (gdhWrapDelegNoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, testB, freshE, rs, seUpd, seMk, reUpd, reMk, stUpd, stMk, smUpd, smMk,
      gPrim_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      rNone_costUB, rDrKey_costUB, bindV_costUB, caseOptV_costUB,
      eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eMap_costUB,
      sidEq, eLet2, nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]; omega
  · refine (gdhWrapDelegNoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, revealB, rs, seUpd, seMk, reUpd, reMk, stUpd, stMk, smUpd, smMk,
      gPrim_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      rNone_costUB, rDrKey_costUB, bindV_costUB, caseOptV_costUB,
      eLet_costUB, eCaseSum_costUB, eFind_costUB, eMap_costUB,
      sidEq, eLet2, nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]; omega
  · refine (gdhWrapDelegNoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapSim2, registerGdhB, stUpd, stMk, smUpd, smMk,
      gPrim_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      rNone_costUB, rPk_costUB, bindV_costUB, qX25519Base_costUB, qPow8_costUB, lenB_costUB,
      natEq, v_costUB, Comp.costUB, Expr.costUB, PNat.val_ofNat, bits_32]; omega
  · refine (gdhWrapDelegNoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, revealSpkB, rs, sbUpd, sbMk, stUpd, stMk, smUpd, smMk,
      gPrim_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      rNone_costUB, rSpkSk_costUB, bindV_costUB, caseOptV_costUB, eFind_costUB, eMap_costUB,
      nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]; omega

set_option linter.unusedSimpArgs false in
private theorem dispatchKeyIndQ_cost_le {ι : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} (S : Setup) {Γ : List (Ty pqAtomicSig)} {τ : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q)) (B : Nat)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)
    (h1 : c1.cost ≤ B) (h2 : c2.cost ≤ B) (h3 : c3.cost ≤ B) (h4 : c4.cost ≤ B)
    (h5 : c5.cost ≤ B) (h6 : c6.cost ≤ B) (h7 : c7.cost ≤ B) (h8 : c8.cost ≤ B)
    (h9 : c9.cost ≤ B) (h10 : c10.cost ≤ B) (h11 : c11.cost ≤ B) (h12 : c12.cost ≤ B)
    (h13 : c13.cost ≤ B) (h14 : c14.cost ≤ B) :
    (dispatchKeyIndQ S qE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 :
      Comp pqAtomicOps I Γ τ).cost ≤ qE.cost + B + 26 := by
  simp only [dispatchKeyIndQ, Comp.cost, compRename_cost, Expr.cost, Expr.v0]; omega

private theorem gdhOnlineArms_all_cost_le (S : Setup) (f : KeyIndKFuels) :
    let A := gdh1KeyActiveKindStateTy
    let B := gdhOnlineArmBudget S f
    (liftSigDdhNoFgArm S (PayAtomic := .base (.fin S.N_id)) (aop (.finVal S.N_id) .v0)
      (gdhKindInitPrinLeg f.kOn)).cost ≤ B ∧
    (liftSigDdhNoFgArm S (PayAtomic := .base (.fin S.N_id)) (aop (.finVal S.N_id) .v0)
      (gdhWrapDelegNoFgLeg fun pa sm bSt u => wrapBase2 pa sm (corruptB f.kOn bSt u))).cost ≤ B ∧
    (liftSigDdhNoFgArm S (PayAtomic := .prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)))
      (finPairToNatE S.N_id S.N_recv .v0) (gdhKindGenSpkLeg f.kOn)).cost ≤ B ∧
    (liftSigDdhNoFgArm S
      (PayAtomic := .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (gdhKindGenOpkLeg f.kOn)).cost ≤ B ∧
    (liftSigDdhSessArm S (PayAtomic := .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_opk))
        (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))))
      (initPayToNatE S.N_send_opk S .v0) (gdhKindInitiateSessLeg S f true)).cost ≤ B ∧
    (liftSigDdhSessArm S (PayAtomic := .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_no_opk))
        (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))))
      (initPayToNatE S.N_send_no_opk S .v0) (gdhKindInitiateSessLeg S f false)).cost ≤ B ∧
    (liftSigDdhSessArm S (PayAtomic := .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv))
        (.prod (.base (.fin S.N_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))))
      (accPayToNatE S.N_opk S .v0) (gdhKindAcceptOpkSessLeg S f)).cost ≤ B ∧
    (liftSigDdhSessArm S (PayAtomic := .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv))
        (.prod (.base (.fin S.N_no_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))))
      (accPayToNatE S.N_no_opk S .v0) (gdhKindAcceptNoOpkSessLeg S f)).cost ≤ B ∧
    (liftSigDdhNoFgArm S (PayAtomic := _root_.ReductionDsl.sidT S) (finSidToNatExpr S .v0)
      (gdhWrapDelegNoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (testB f.kOn bSt sid))).cost ≤ B ∧
    (Comp.ret (I := pqSigAndDdhIface) (Γ := .unit :: [A, (pqKeyIndCodec S).Q])
      (.pair (atomicRNoneE (S := S)) .v1)).cost ≤ B ∧
    (liftSigDdhNoFgArm S (PayAtomic := _root_.ReductionDsl.sidT S) (finSidToNatExpr S .v0)
      (gdhWrapDelegNoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (revealB f.kOn bSt sid))).cost ≤ B ∧
    (liftSigDdhNoFgArm S (PayAtomic := PB 32) .v0
      (gdhWrapDelegNoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk))).cost ≤ B ∧
    (liftSigDdhNoFgArm S (PayAtomic := .prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)))
      (finPairToNatE S.N_id S.N_recv .v0)
      (gdhWrapDelegNoFgLeg fun pa sm bSt x => wrapBase2 pa sm (revealSpkB f.kOn bSt x))).cost ≤ B := by
  intro A B
  obtain ⟨hN1, hN3, hN4, hN2, hN9, hN12, hN13, hN14⟩ := gdhNoFgLegs_atomic_cost_le f.kOn
  obtain ⟨hSi, hSaO, hSaN⟩ := gdhSessLegs_atomic_cost_le S f
  have hS5 := hSi true; have hS6 := hSi false
  obtain ⟨hP1, hPP, hPT, hPS, hP5b, hP7b, hPV0⟩ :=
    gdhPayExprs_cost_le S (A := .prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy) S.N_send_opk S.N_opk
  obtain ⟨_, _, _, _, hP6b, hP8b, _⟩ :=
    gdhPayExprs_cost_le S (A := .prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy) S.N_send_no_opk S.N_no_opk
  have hB : gdhOnlineArmBudget S f = B := rfl
  rw [← hB]; unfold gdhOnlineArmBudget
  have := Nat.zero_le f.kFg
  have := Nat.zero_le f.kOn
  have := Nat.zero_le (min f.kOn S.N_dh)
  have := Nat.zero_le (min f.kOn S.N_sess_tot)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hP1 hN1; linarith
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hP1 hN2; linarith
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hPP hN3; linarith
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hPT hN4; linarith
  · refine (liftSigDdhSessArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hP5b hS5; linarith
  · refine (liftSigDdhSessArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hP6b hS6; linarith
  · refine (liftSigDdhSessArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hP7b hSaO; linarith
  · refine (liftSigDdhSessArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hP8b hSaN; linarith
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hPS hN9; linarith
  · simp only [atomicRNoneE, Comp.cost, Expr.cost, Expr.v1,
      pqAtomicOps, atomicPureOps]; linarith
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hPS hN12; linarith
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hPV0 hN13; linarith
  · refine (liftSigDdhNoFgArm_cost_le S _ _).trans ?_; have := Nat.add_le_add hPP hN14; linarith

theorem gdh1KeyKindHandleC_cost_le (S : Setup) (b : QueryBudget) {B : Nat}
    (hOn : gdhOnlineArmBudget S (keyIndKFuelsOfBudget S b) ≤ B)
    (hRo : (gdhKindRoArm S (keyIndKFuelsOfBudget S b)).cost ≤ B) :
    (gdh1KeyKindHandleC S b).cost ≤ B + 27 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12, h13, h14⟩ :=
    gdhOnlineArms_all_cost_le S (keyIndKFuelsOfBudget S b)
  unfold gdh1KeyKindHandleC; dsimp only
  refine (dispatchKeyIndQ_cost_le S .v1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (h1.trans hOn) (h2.trans hOn) (h3.trans hOn) (h4.trans hOn)
    (h5.trans hOn) (h6.trans hOn) (h7.trans hOn) (h8.trans hOn)
    (h9.trans hOn) hRo (h11.trans hOn) (h12.trans hOn)
    (h13.trans hOn) (h14.trans hOn)).trans ?_
  have hv1 : (.v1 : Expr pqAtomicOps [gdh1KeyActiveKindStateTy, (pqKeyIndCodec S).Q] _).cost = 1 := rfl
  omega

theorem gdh1KeyKindHandleC_costAt_online_le (S : Setup) (b : QueryBudget)
    (s : gdh1KeyActiveKindStateTy.denote) (q : KeyIndQuery S)
    (hq : keyIndQueryKind q = ⟨0, by decide⟩) :
    (gdh1KeyKindHandleC S b).costAt (.cons s (.cons ((pqKeyIndCodec S).qenc q) .nil)) ≤
      gdhOnlineArmBudget S (keyIndKFuelsOfBudget S b) + 26 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12, h13, h14⟩ :=
    gdhOnlineArms_all_cost_le S (keyIndKFuelsOfBudget S b)
  unfold gdh1KeyKindHandleC; dsimp only
  refine (dispatchKeyIndQ_online_costAt_le S (gdhOnlineArmBudget S (keyIndKFuelsOfBudget S b)) s q hq
    _ _ _ _ _ _ _ _ _ (gdhKindRoArm S (keyIndKFuelsOfBudget S b)) _ _ _ _
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14).trans ?_
  linarith

theorem gdh1KeyKindHandleC_costAt_ro_le (S : Setup) (b : QueryBudget)
    (s : gdh1KeyActiveKindStateTy.denote) (sec : List UInt8) :
    (gdh1KeyKindHandleC S b).costAt (.cons s (.cons ((pqKeyIndCodec S).qenc (.roQuery sec)) .nil)) ≤
      (gdhKindRoArm S (keyIndKFuelsOfBudget S b)).cost + 26 := by
  unfold gdh1KeyKindHandleC; dsimp only
  refine (dispatchKeyIndQ_ro_costAt_le S s sec
    _ _ _ _ _ _ _ _ _ (gdhKindRoArm S (keyIndKFuelsOfBudget S b)) _ _ _ _).trans ?_
  omega

end ArmCosts

section SizeBounds

open _root_.SignalPqxdh (F_X25519)
open _root_.SignalPqxdh.LegacyCosted (gapDhDdhOracle pqChalIface pqPrimIface pqGapDhIface pqSamplers)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  liftBase gPrim peMk peUpd peSecIKA0 peSecIKAsign peIkAPk peIkSignPk peCorrupted
  sbMk sbUpd sbSpkSk sbSpkPk sbSpkSig sbPqspkSk sbPqspkPk sbPqspkSig sbRevealed
  oeMk oeOpkSk oeOpkPk oeConsumed oeUpd
  buMk buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig
  hdMk hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt
  seMk seUpd seSid seHonestPeer sePeerIk sePeerSpk sePeerOpk sePeerPqspk
  seSpkHon seOpkHon sePqspkHon seEkASk seFresh seDrReal seDrRand seHdr seTested seRevealed
  reMk reUpd reSid reRespIk reSpk reOpk rePqspk reHdr reSenderHonest reDrReal reDrRand reTested reRevealed
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stRo stAdv stSecb
  smFgL smRaw smLog smPows feMk feDk fePos1 fePos2 fePos3 fePos4 feSs
  rs rCorr rAccFresh rDh rInitPrin rBundle rPk rHdr rInitUnfresh rDrKey rSpkSk
  qK qJ qO qHdr qKJO paDhFlag paEphIdx freshE buildSecretsE catB consB eqU32
  isAdvPowsE isAdvRegC chooseRespRandC recordRespC hkdfOrRoC acceptKeysC ephSidMatchesE
  natEq nat2Eq nat3Eq sidEq orE mulRight optBytesEq optU32Eq kyberEq kyberCheckE nonZero32
  isSomeE optFst optSnd initSidE getDBytes u32OfNat encEC encKEM widenEC widenB eqB lenB
  slice32 takeKB dropB ddhQ qHkdfDerive96
  koskBundleOkPowsC koskSenderOkPowsC resolveSigPkC lookupSpkSkC honestPeerC checkProvC
  isGameSpkC isGameOpkC findHonestC chooseInitRandC partnerC
  computePosC computeOptPosInitC mkSecretPosC mkPairPosC entryMatchesC ddhEqC ddhEqOptC
  logFindC spkPowsC findMapStepC initDh1CandC respDh1CandC lookupFromPowsE respBundleKeyE)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (
  bits_64 bits_96 bits_128 bits_160 bits_192)
open Computational.Proofs.SignalPqxdh.AtomicLift (atomicSize_le_budget)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  emptyFgShadowE wkSndVar roNotPrefixE roLenEqE seqFgEntryDkE
  roHitRespSimE rawMissRespSimE parsedMissRespSimE fgSessScanC
  fgPatchShadowC initiateGdhActiveShadowInnerB acceptOpkGdhCoreShadowB
  acceptOpkGdh2ShadowB acceptNoOpkGdhShadowB)

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle
  pqChalIface pqPrimIface pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface pqSamplers

private theorem act_liftBase_size_aux {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [liftBase, Comp.size, pqChalIface, pqPrimIface]

private theorem act_liftGdhComp_size_aux {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhComp c).size = c.size := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.size]

private theorem act_liftBase_litSize_aux {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (liftBase (C := C) c) = compLitSize c := by
  induction c <;> simp_all [liftBase, compLitSize, pqChalIface, pqPrimIface]

private theorem act_liftGdhComp_litSize_aux {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhComp c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, compLitSize]

@[local simp] private theorem act_liftBase_size {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := act_liftBase_size_aux c

@[local simp] private theorem act_gPrim_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).size = c.size := act_liftBase_size c

@[local simp] private theorem act_liftGdhComp_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhComp c).size = c.size := act_liftGdhComp_size_aux c

@[local simp] private theorem act_liftBase_litSize {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (liftBase (C := C) c) = compLitSize c := act_liftBase_litSize_aux c

@[local simp] private theorem act_gPrim_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (gPrim c) = compLitSize c := act_liftBase_litSize c

@[local simp] private theorem act_liftGdhComp_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhComp c) = compLitSize c := act_liftGdhComp_litSize_aux c

@[local simp] private theorem act_F_X25519_length : F_X25519.length = 32 := rfl

set_option linter.unusedSimpArgs false in
private theorem act_bernoulliRatioGdhC_size_and_lit {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).size ≤ 25 ∧
    compLitSize (bernoulliRatioGdhC (Δ := Δ) A B) = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;>
    simp [bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
      Comp.size, Expr.size, compLitSize, exprLitSize, bits_1]

private theorem act_chooseArm2C_size_and_lit {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (B1 B2 L1 L2 : Nat)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      (c1 (Δ' := Δ')).size ≤ B1 ∧ compLitSize (c1 (Δ' := Δ')) ≤ L1)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      (c2 (Δ' := Δ')).size ≤ B2 ∧ compLitSize (c2 (Δ' := Δ')) ≤ L2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).size ≤ B1 + B2 + 30 ∧
    compLitSize (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2) ≤ L1 + L2 := by
  unfold chooseArm2C
  split_ifs with hw1 hw2
  · exact ⟨le_trans hc2.1 (by omega), le_trans hc2.2 (by omega)⟩
  · exact ⟨le_trans hc1.1 (by omega), le_trans hc1.2 (by omega)⟩
  · obtain ⟨hbSz, hbLit⟩ := act_bernoulliRatioGdhC_size_and_lit (Δ := Δ) w1 w2
    obtain ⟨hSz1, hLit1⟩ := hc1 (Δ' := .bool :: Δ)
    obtain ⟨hSz2, hLit2⟩ := hc2 (Δ' := .bool :: Δ)
    simp only [bindV, v, Comp.size, Expr.size, compLitSize, exprLitSize]
    exact ⟨by omega, by omega⟩

set_option linter.unusedSimpArgs false in
private theorem initParams1KeyKindC_size_and_lit (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 32))) :
    (initParams1KeyKindC S b (Δ := Δ) uv).size ≤ 16 * bits (keyIndSentinel S b) + 400 ∧
    compLitSize (initParams1KeyKindC S b (Δ := Δ) uv) ≤ 10 := by
  let unreach := keyIndSentinel S b
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_send_opk := activeSendOpkCount S b.q_on
  let nA := n_id * n_spk
  let nC := n_send * n_spk
  let nB := n_send * n_id
  let nD := n_send_opk * n_opk
  have hA : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (fun c : Comp pqxdhOps pqGapDhIface Δ' paramsTy =>
      c.size ≤ 4 * bits unreach + 60 ∧ compLitSize c ≤ 0)
      (if nA = 0 then
        .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool true)
          (.nat unreach) (.nat 0) (.bool false) (.nat unreach) (.nat 0))
       else
        bindV (gPrim (sIndex n_id)) fun pOrd => bindV (gPrim (sIndex n_spk)) fun spkOrd =>
        .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool true)
          (.nat unreach) (v spkOrd) (.bool false) (.nat unreach) (.nat 0))) := by
    intro Δ' _; split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0]
      exact ⟨by omega, by omega⟩ }
  have hC : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (fun c : Comp pqxdhOps pqGapDhIface Δ' paramsTy =>
      c.size ≤ 4 * bits unreach + 60 ∧ compLitSize c ≤ 0)
      (if nC = 0 then
        .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
          (.bool false) (.nat 0) (.nat 0) (.bool false) (.nat unreach) (.nat 1))
       else
        bindV (gPrim (sIndex n_send)) fun ephOrd => bindV (gPrim (sIndex n_spk)) fun spkOrd =>
        .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
          (.bool false) (v ephOrd) (v spkOrd) (.bool false) (.nat unreach) (.nat 1))) := by
    intro Δ' _; split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0, bits_1]
      exact ⟨by omega, by omega⟩ }
  have hB : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (fun c : Comp pqxdhOps pqGapDhIface Δ' paramsTy =>
      c.size ≤ 4 * bits unreach + 60 ∧ compLitSize c ≤ 0)
      (if nB = 0 then
        .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool false)
          (.nat 0) (.nat unreach) (.bool false) (.nat unreach) (.nat 2))
       else
        bindV (gPrim (sIndex n_send)) fun ephOrd => bindV (gPrim (sIndex n_id)) fun pOrd =>
        .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool false)
          (v ephOrd) (.nat unreach) (.bool false) (.nat unreach) (.nat 2))) := by
    intro Δ' _; split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0, bits_2]
      exact ⟨by omega, by omega⟩ }
  have hD : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (fun c : Comp pqxdhOps pqGapDhIface Δ' paramsTy =>
      c.size ≤ 4 * bits unreach + 60 ∧ compLitSize c ≤ 0)
      (if nD = 0 then
        .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
          (.bool false) (.nat 0) (.nat unreach) (.bool true) (.nat 0) (.nat 3))
       else
        bindV (gPrim (sIndex n_send_opk)) fun ephOrd => bindV (gPrim (sIndex n_opk)) fun opkOrd =>
        .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
          (.bool false) (v ephOrd) (.nat unreach) (.bool true) (v opkOrd) (.nat 3))) := by
    intro Δ' _; split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0, bits_3]
      exact ⟨by omega, by omega⟩ }
  unfold initParams1KeyKindC; dsimp only
  by_cases h0 : fgActiveTotalIndexCount S b.q_on = 0
  · simp only [h0, ↓reduceIte, paMk, v, Comp.size, Expr.size, compLitSize, exprLitSize, bits_0]
    exact ⟨by omega, by omega⟩
  · simp only [h0, ↓reduceIte]
    have hTree := act_chooseArm2C_size_and_lit (Γ₁ := Γ₁) (Δ := Δ)
      (activeIdCount S b.q_on * activeSpkCount S b.q_on +
        activeSendCount S b.q_on * activeSpkCount S b.q_on)
      (activeSendCount S b.q_on * activeIdCount S b.q_on +
        activeSendOpkCount S b.q_on * activeOpkCount S b.q_on)
      _ _ ((4 * bits unreach + 60) + (4 * bits unreach + 60) + 30)
      ((4 * bits unreach + 60) + (4 * bits unreach + 60) + 30) 0 0
      (fun {Δ'} [_] => act_chooseArm2C_size_and_lit (Γ₁ := Γ₁) (Δ := Δ')
        (activeIdCount S b.q_on * activeSpkCount S b.q_on)
        (activeSendCount S b.q_on * activeSpkCount S b.q_on) _ _
        (4 * bits unreach + 60) (4 * bits unreach + 60) 0 0
        (fun {Δ''} [_] => hA (Δ' := Δ'')) (fun {Δ''} [_] => hC (Δ' := Δ'')))
      (fun {Δ'} [_] => act_chooseArm2C_size_and_lit (Γ₁ := Γ₁) (Δ := Δ')
        (activeSendCount S b.q_on * activeIdCount S b.q_on)
        (activeSendOpkCount S b.q_on * activeOpkCount S b.q_on) _ _
        (4 * bits unreach + 60) (4 * bits unreach + 60) 0 0
        (fun {Δ''} [_] => hB (Δ' := Δ'')) (fun {Δ''} [_] => hD (Δ' := Δ'')))
    exact ⟨hTree.1.trans (by dsimp only [unreach]; omega), hTree.2.trans (by omega)⟩

set_option linter.unusedSimpArgs false in
private theorem gdh1KeyKindInitC_size_le (S : Setup) (b : QueryBudget) :
    (gdh1KeyKindInitC S b).size ≤
      160 * bits (keyIndSentinel S b) + 10 * bits (activeSigBudget S b) + 5500 := by
  obtain ⟨hP_sz, hP_lit⟩ := initParams1KeyKindC_size_and_lit S b
    (Γ₁ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
            .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)])
    (Δ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
           .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)]) .zero
  have hBaseSz : (gdh1KeyKindBaseInit S b).size ≤
      16 * bits (keyIndSentinel S b) + bits (activeSigBudget S b) + 500 := by
    simp only [gdh1KeyKindBaseInit, emptySimE, smMk, emptyStE, stMk,
      letV, bindV, act_liftGdhComp_size, act_gPrim_size, sBool, v,
      Comp.size, Expr.size, bits_0]
    omega
  have hBaseLit : compLitSize (gdh1KeyKindBaseInit S b) ≤ 100 := by
    simp only [gdh1KeyKindBaseInit, emptySimE, smMk, emptyStE, stMk,
      letV, bindV, act_liftGdhComp_litSize, act_gPrim_litSize, sBool, v,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  have hMap := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe (gdh1KeyKindBaseInit S b)
  have hEmp : (emptyFgShadowE (Γ := [.prod .unit (embedTy gdh1KeyActiveStateTy),
      .prod (PB 32) (PB 32)])).size ≤ 200 := by
    simp only [emptyFgShadowE,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlEmptyE,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.dfltB192E,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.dfltDrKeyE,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.dfltFgRoValE,
      aop, Expr.size, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, bits_0, List.length_nil]
    omega
  unfold gdh1KeyKindInitC
  simp only [Comp.size, Expr.size]
  omega

set_option linter.unusedSimpArgs false in
private theorem gdh1KeyKindFinishC_size_le (S : Setup) (b : QueryBudget) :
    let f := keyIndKFuelsOfBudget S b
    (gdh1KeyKindFinishC S b).size ≤ 200 * bits f.kOff + 250 * bits f.kOn + 21000 := by
  intro f
  have hFinSz : (gdhFinishK S f).size ≤ 20 * bits f.kOff + 25 * bits f.kOn + 2000 := by
    simp (config := { maxSteps := 1000000 }) only [
      gdhFinishK, extractMode0KC, logFindC, spkPowsC, findMapStepC,
      initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
      smBase, smLog, smPows, paU, paV, paMode,
      stSpks, stSess, stResps, sbSpkSk, sbSpkPk, sePeerSpk, seHdr,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr, hdIkAPk,
      natEq, nat2Eq, orE, mulRight, optBytesEq,
      letV, bindV, caseOptV, findMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eMap,
      act_gPrim_size, gPrim, liftBase, ddhQ, qPow8, qX25519,
      litB, takeKB, dropB, eqB, v, Comp.size, Expr.size,
      bits_0, bits_1, bits_2, bits_3, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
      ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
    have h1 : bits (min f.kOn S.N_dh) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h2 : bits (f.kOn.min S.N_dh) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h3 : bits (min f.kOn S.N_sess_tot) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h4 : bits (f.kOn.min S.N_sess_tot) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    linarith
  have hFinLit : compLitSize (gdhFinishK S f) ≤ 500 := by
    simp (config := { maxSteps := 1000000 }) only [
      gdhFinishK, extractMode0KC, logFindC, spkPowsC, findMapStepC,
      initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
      smBase, smLog, smPows, paU, paV, paMode,
      stSpks, stSess, stResps, sbSpkSk, sbSpkPk, sePeerSpk, seHdr,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr, hdIkAPk,
      natEq, nat2Eq, orE, mulRight, optBytesEq,
      letV, bindV, caseOptV, findMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eMap,
      act_gPrim_litSize, gPrim, liftBase, ddhQ, qPow8, qX25519,
      litB, takeKB, dropB, eqB, v, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_replicate, Nat.add_zero, Nat.zero_add]
    linarith
  have hMap := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe
    (liftGdhComp (gdhFinishK S f))
  rw [act_liftGdhComp_size, act_liftGdhComp_litSize] at hMap
  have hEq : f = keyIndKFuelsOfBudget S b := rfl
  unfold gdh1KeyKindFinishC
  simp only [← hEq, runAt2, liftGdhAtomic, gdhLift1Key,
    Comp.size, compRename_size, exprRename_size, Expr.size, Expr.v0, Expr.v1]
  linarith

private theorem bind_atomic_size_le {Γ : List (Ty pqAtomicSig)} {τ σ : Ty pqAtomicSig}
    (c₁ : Comp pqAtomicOps pqSigAndDdhIface Γ τ)
    (c₂ : Comp pqAtomicOps pqSigAndDdhIface (τ :: Γ) σ) {n₁ n₂ n : Nat}
    (h₁ : c₁.size ≤ n₁) (h₂ : c₂.size ≤ n₂) (h : n₁ + n₂ + 1 ≤ n) :
    (Comp.bind c₁ c₂).size ≤ n := by
  simp only [Comp.size]; omega

private theorem caseOpt_atomic_size_le {Γ : List (Ty pqAtomicSig)} {α σ : Ty pqAtomicSig}
    (e : Expr pqAtomicOps Γ (.opt α))
    (c₁ : Comp pqAtomicOps pqSigAndDdhIface Γ σ)
    (c₂ : Comp pqAtomicOps pqSigAndDdhIface (α :: Γ) σ) {ne n₁ n₂ n : Nat}
    (he : e.size ≤ ne) (h₁ : c₁.size ≤ n₁) (h₂ : c₂.size ≤ n₂) (h : ne + n₁ + n₂ + 1 ≤ n) :
    (Comp.caseOpt e c₁ c₂).size ≤ n := by
  simp only [Comp.size]; omega

set_option linter.unusedSimpArgs false in
private theorem gdhKindRoArm_size_le (S : Setup) (f : KeyIndKFuels) :
    (gdhKindRoArm S f).size ≤ 8 * bits (avlHeightCap f.kAvl) + 100 * bits f.kOn + 45000 := by
  have hPre160 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).size ≤ 5000 := by
    dsimp only [liftGdhAtomic, gdhLift1Key]
    refine (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _).trans ?_
    rw [act_liftGdhComp_size, act_liftGdhComp_litSize]
    simp only [roParsedPrePos160C, mkSecretPosC, slice32, takeKB, dropB, letV, bindV, eCaseOpt,
      act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, qIsCanonical, ddhQ,
      litB, eqB, v, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
      List.length_nil, List.length_replicate, Nat.add_zero, Nat.zero_add]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      ReductionDsl.Ops.sum, Sum.elim_inl]
    omega
  have hPre192 : (liftGdhAtomic gdhLift1Key
      (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).size ≤ 6500 := by
    dsimp only [liftGdhAtomic, gdhLift1Key]
    refine (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _).trans ?_
    rw [act_liftGdhComp_size, act_liftGdhComp_litSize]
    simp only [roParsedPrePos192C, mkSecretPosC, slice32, takeKB, dropB, letV, bindV, eCaseOpt,
      act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, qIsCanonical, ddhQ,
      litB, eqB, v, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
      List.length_nil, List.length_replicate, Nat.add_zero, Nat.zero_add]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      ReductionDsl.Ops.sum, Sum.elim_inl]
    omega
  have hScan : (liftGdhAtomic gdhLift1Key (fgSessScanPackC f.kOn)).size ≤
      40 * bits f.kOn + 8000 := by
    dsimp only [liftGdhAtomic, gdhLift1Key]
    refine (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _).trans ?_
    rw [act_liftGdhComp_size, act_liftGdhComp_litSize]
    simp (config := { maxSteps := 500000 }) only [
      fgSessScanPackC, fgSessScanC, sessScanMinPredC, entryMatchesC, ddhEqC, ddhEqOptC, orE,
      fePos1, fePos2, fePos3, fePos4, feSs,
      letV, bindV, caseOptV, caseSumV, findMV, ddhQ, eqB, v,
      Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      ReductionDsl.Ops.sum, Sum.elim_inl]
    omega
  have hDr : ∀ {Γ}, (sampleDrKey96LiftC gdhLift1Key (Γ := Γ)).size ≤ 50 := by
    intro Γ; simp only [sampleDrKey96LiftC, compRename_size]; dsimp only [liftGdhAtomic, gdhLift1Key]
    refine (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _).trans ?_
    rw [act_liftGdhComp_size, act_liftGdhComp_litSize]
    simp [act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sDrKey96,
      Comp.size, Expr.size, compLitSize, exprLitSize]
  have hPure :
      roNotPrefixE.size + exprLitSize roNotPrefixE ≤ 200 ∧
      (roLenEqE 160).size + exprLitSize (roLenEqE 160) ≤ 50 ∧
      (roLenEqE 192).size + exprLitSize (roLenEqE 192) ≤ 50 ∧
      seqFgEntryDkE.size + exprLitSize seqFgEntryDkE ≤ 50 ∧
      roHitRespSimE.size + exprLitSize roHitRespSimE ≤ 100 ∧
      rawMissRespSimE.size + exprLitSize rawMissRespSimE ≤ 100 ∧
      parsedMissRespSimE.size + exprLitSize parsedMissRespSimE ≤ 200 := by
    simp only [roNotPrefixE, roLenEqE, seqFgEntryDkE, roHitRespSimE, rawMissRespSimE,
      parsedMissRespSimE, feDk, feMk, rDrKey, smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows,
      natEq, lenB, takeKB, eqB, litB, act_F_X25519_length, v,
      Expr.size, exprLitSize, pqOpLitSize, bits_32, bits_160, bits_192, Nat.add_zero, Nat.zero_add]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      ReductionDsl.Ops.sum, Sum.elim_inl]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨hNP, hL160, hL192, hDk, hHit, hRawM, hParM⟩ := hPure
  have hRaw : (roRawFallbackShadowAtomicC gdhLift1Key f).size ≤
      2 * bits (avlHeightCap f.kAvl) + 3200 := by
    unfold roRawFallbackShadowAtomicC
    refine bind_atomic_size_le _ _ (avlSearchB192C_size_le _ _ _) ?_ (n₂ := bits (avlHeightCap f.kAvl) + 2800) ?_
    · refine caseOpt_atomic_size_le _ _ _ (ne := 5) (by simp [Expr.size, Expr.v0])
        (n₁ := bits (avlHeightCap f.kAvl) + 2400) ?_ (n₂ := 300) ?_ (by omega)
      · refine bind_atomic_size_le _ _ hDr ?_ (n₂ := bits (avlHeightCap f.kAvl) + 2300) (by omega)
        refine bind_atomic_size_le _ _ (avlInsertAtPathC_size_le _ _ _ _ _) ?_ (n₂ := 500) ?_
        · simp only [runAt3, Comp.size, compRename_size, exprRename_size, mapExpr_size,
            Expr.size, Expr.v0, Expr.v1, Expr.v3]; omega
        · simp only [aop, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
            pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, bits_192]; omega
      · simp only [runAt3, Comp.size, compRename_size, exprRename_size, mapExpr_size,
          Expr.size, Expr.v0, Expr.v2, Expr.v3]; omega
    · simp only [aop, Expr.size, Expr.v0, Expr.v1, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, bits_192]; omega
  have hPost : (roParsedPostPosShadowAtomicC gdhLift1Key f).size ≤
      2 * bits (avlHeightCap f.kAvl) + 40 * bits f.kOn + 12000 := by
    unfold roParsedPostPosShadowAtomicC
    refine bind_atomic_size_le _ _ (avlSearchB192C_size_le _ _ _) ?_
      (n₂ := bits (avlHeightCap f.kAvl) + 40 * bits f.kOn + 11700) ?_
    · refine bind_atomic_size_le _ _ (n₁ := 40 * bits f.kOn + 8100)
        (by simp only [runAt3, Comp.size, compRename_size, exprRename_size, Expr.size,
              Expr.v0, Expr.v1, Expr.v2, bits_0, bits_1]; omega)
        ?_ (n₂ := bits (avlHeightCap f.kAvl) + 3500) (by omega)
      refine caseOpt_atomic_size_le _ _ _ (ne := 5) (by simp [Expr.size, Expr.v0])
        (n₁ := bits (avlHeightCap f.kAvl) + 3150) ?_ (n₂ := 300) ?_ (by omega)
      · refine caseOpt_atomic_size_le _ _ _ (ne := 5) (by simp [Expr.size, Expr.v1])
          (n₁ := bits (avlHeightCap f.kAvl) + 2900) ?_ (n₂ := 200) ?_ (by omega)
        · refine bind_atomic_size_le _ _ hDr ?_ (n₂ := bits (avlHeightCap f.kAvl) + 2800) (by omega)
          refine bind_atomic_size_le _ _ (avlInsertAtPathC_size_le _ _ _ _ _) ?_ (n₂ := 1000) ?_
          · simp only [runAt4, Comp.size, compRename_size, exprRename_size, mapExpr_size,
              Expr.size, Expr.v0, Expr.v1, bits_1]; omega
          · simp only [aop, Expr.size, Expr.v0, Expr.v2, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, bits_192]; omega
        · simp only [runAt3, Comp.size, compRename_size, exprRename_size, mapExpr_size,
            Expr.size, Expr.v0]; omega
      · simp only [runAt3, Comp.size, compRename_size, exprRename_size, mapExpr_size,
          Expr.size, Expr.v0]; omega
    · simp only [aop, Expr.size, Expr.v1, Expr.v2, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, bits_192]; omega
  unfold gdhKindRoArm roParsedShadowAtomicC
  simp only [runAt1, runAt2, runAt3, Comp.size, compRename_size, exprRename_size, mapExpr_size,
    Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

set_option linter.unusedSimpArgs false in
private theorem gdhPayExprs_size_le (S : Setup) {A : Ty pqAtomicSig} (N_s N_o : Nat) :
    (aop (.finVal S.N_id) (.v0 : Expr pqAtomicOps [.base (.fin S.N_id), A, (pqKeyIndCodec S).Q] _)).size ≤ 60 ∧
    (finPairToNatE S.N_id S.N_recv
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)), A, (pqKeyIndCodec S).Q] _)).size ≤ 60 ∧
    (finTripleToNatE S.N_id S.N_recv S.N_opk
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))),
        A, (pqKeyIndCodec S).Q] _)).size ≤ 60 ∧
    (finSidToNatExpr S (.v0 : Expr pqAtomicOps (_root_.ReductionDsl.sidT S :: [A, (pqKeyIndCodec S).Q]) _)).size ≤ 60 ∧
    (initPayToNatE N_s S
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s))
        (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))), A, (pqKeyIndCodec S).Q] _)).size ≤ 60 ∧
    (accPayToNatE N_o S
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv))
        (.prod (.base (.fin N_o)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))),
        A, (pqKeyIndCodec S).Q] _)).size ≤ 60 ∧
    (.v0 : Expr pqAtomicOps [PB 32, A, (pqKeyIndCodec S).Q] (PB 32)).size ≤ 60 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [finPairToNatE, finTripleToNatE, finSidToNatExpr, initPayToNatE, accPayToNatE,
      aop, Expr.size, Expr.v0, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize]; omega)

private theorem liftSigDdhNoFgArm_size_le (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy))
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy)) :
    (liftSigDdhNoFgArm S payE arm).size ≤ (mapComp tlSigDdhKeyInd arm).size + payE.size + 25 := by
  unfold liftSigDdhNoFgArm runAt2
  simp only [Comp.size, compRename_size, exprRename_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem liftSigDdhSessArm_size_le (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [.prod stTy fgSessCtrTy, qPayTy] (.prod keyIndRespTy (.prod stTy fgSessCtrTy)))
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy)) :
    (liftSigDdhSessArm S payE arm).size ≤ (mapComp tlSigDdhKeyInd arm).size + payE.size + 45 := by
  unfold liftSigDdhSessArm runAt2
  simp only [Comp.size, compRename_size, exprRename_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

set_option linter.unusedSimpArgs false in
private theorem gdhNoFgLegs_size_le (K : Nat) :
    (mapComp tlSigDdhKeyInd (gdhKindInitPrinLeg K)).size ≤ 120 * bits K + 16000 ∧
    (mapComp tlSigDdhKeyInd (gdhKindGenSpkLeg K)).size ≤ 120 * bits K + 16000 ∧
    (mapComp tlSigDdhKeyInd (gdhKindGenOpkLeg K)).size ≤ 120 * bits K + 16000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt u =>
      wrapBase2 pa sm (corruptB K bSt u))).size ≤ 120 * bits K + 16000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt sid =>
      wrapBase2 pa sm (testB K bSt sid))).size ≤ 120 * bits K + 16000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt sid =>
      wrapBase2 pa sm (revealB K bSt sid))).size ≤ 120 * bits K + 16000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt sk =>
      wrapSim2 pa (registerGdhB sm bSt sk))).size ≤ 120 * bits K + 16000 ∧
    (mapComp tlSigDdhKeyInd (gdhWrapDelegNoFgLeg fun pa sm bSt x =>
      wrapBase2 pa sm (revealSpkB K bSt x))).size ≤ 120 * bits K + 16000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
    refine (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _).trans ?_
    simp (config := { maxSteps := 1000000 }) only [
      gdhKindInitPrinLeg, gdhKindGenSpkLeg, gdhKindGenOpkLeg, gdhWrapDelegNoFgLeg,
      initPrin1KeyActiveGdhB, genSpk1KeyActiveGdhB, genSpkGdhActiveB, genOpkActiveGdhB,
      optNatMatchesE, sigChalQ_dsl, wrapBase2, wrapSim2,
      corruptB, testB, revealB, registerGdhB, revealSpkB, freshE, rs, rCorr,
      peUpd, sbUpd, reSid, reDrReal, reDrRand, reTested, reRevealed, reMk, reUpd,
      seHonestPeer, sePeerIk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seFresh, seDrReal, seDrRand, seTested, seRevealed, consB,
      pa2Mk, paU, paV, paUp, paPrinFlag, paPrinIdx, paSpkIdx, paOpkMode, paOpkIdx,
      smBase, smUpd, smMk, smFgL, smRaw, smLog, smPows,
      stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
      stMk, stUpd, peMk, peIkAPk, peSecIKA0, peSecIKAsign, sbMk, sbSpkSk, buMk, oeMk,
      seMk, seUpd, seSid, sePeerSpk, seHdr, rNone, rInitPrin, rBundle, rPk, rDrKey, rSpkSk,
      natEq, nat2Eq, nat3Eq, sidEq, lenB, u32OfNat, encEC, encKEM, widenEC, widenB, eLet2,
      letV, bindV, caseOptV, eLet, eCaseOpt, eCaseSum, eAny, eFind, eMap,
      act_liftGdhComp_size, act_liftGdhComp_litSize, act_gPrim_size, act_gPrim_litSize,
      liftGdhComp, gPrim, liftBase, sBytes32, sRandom64, qX25519Base, qPow8, qKemKeyGen, qSigSign,
      litB, v, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      bits_0, bits_1, bits_32, List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
    try simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      _root_.SignalPqxdh.LegacyCosted.pqU32Ops, ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
    omega }

set_option linter.unusedSimpArgs false in
private theorem gdhInitSessLeg_size_le (S : Setup) (f : KeyIndKFuels) (hasOpk : Bool) :
    (mapComp tlSigDdhKeyInd (gdhKindInitiateSessLeg S f hasOpk)).size ≤
      80 * bits f.kFg + 400 * bits f.kOn + 45000 := by
  cases hasOpk <;> refine (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _).trans ?_
  all_goals
    simp (config := { maxSteps := 2000000 }) only [
      gdhKindInitiateSessLeg, initiateGdhActiveShadowInnerB, fgPatchShadowC,
      koskBundleOkPowsC, isAdvPowsE, resolveSigPkC, lookupSpkSkC, honestPeerC, checkProvC,
      isGameSpkC, isGameOpkC, findHonestC, chooseInitRandC, partnerC, computePosC,
      computeOptPosInitC, mkSecretPosC, mkPairPosC, entryMatchesC, ddhEqC, ddhEqOptC,
      fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk, buildSecretsE, rs,
      qK, qJ, qO, qHdr, qKJO, reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr,
      catB, consB, eqU32, paDhFlag, paEphIdx, paOpkMode, paU,
      seHonestPeer, sePeerIk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seFresh, seDrReal, seDrRand, seTested, seRevealed, seSid, sePeerSpk, seHdr, seMk, seUpd,
      smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
      stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkPk,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig,
      oeOpkPk, oeConsumed, hdMk, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
      rNone, rHdr, rInitUnfresh, initSidE, isSomeE, optFst, optSnd, natEq, nat2Eq, nat3Eq, sidEq,
      optU32Eq, kyberEq, orE, eLet2, encEC, encKEM, u32OfNat, lenB,
      letV, bindV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eAny, eFind,
      act_liftGdhComp_size, act_liftGdhComp_litSize, act_gPrim_size, act_gPrim_litSize,
      liftGdhComp, gPrim, liftBase, getDBytes, optBytesEq, ddhQ,
      sBytes32, sDrKey96, qX25519, qX25519Base, qIsCanonical, qPow8, qSigVerify, qKemEncaps, qHkdfDerive96,
      litB, widenB, eqB, act_F_X25519_length, v, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      bits_0, bits_1, bits_2, bits_3, bits_32, ↓reduceIte, Bool.false_eq_true,
      List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      _root_.SignalPqxdh.LegacyCosted.pqU32Ops, ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
    have h1 : bits (min f.kOn S.N_dh) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h2 : bits (f.kOn.min S.N_dh) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h3 : bits (min f.kOn S.N_sess_tot) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h4 : bits (f.kOn.min S.N_sess_tot) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have := Nat.zero_le (bits f.kFg); have := Nat.zero_le (bits f.kOn); linarith

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem gdhAcceptSessLegs_size_le (S : Setup) (f : KeyIndKFuels) :
    (mapComp tlSigDdhKeyInd (gdhKindAcceptOpkSessLeg S f)).size ≤
      80 * bits f.kFg + 400 * bits f.kOn + 45000 ∧
    (mapComp tlSigDdhKeyInd (gdhKindAcceptNoOpkSessLeg S f)).size ≤
      80 * bits f.kFg + 400 * bits f.kOn + 45000 := by
  refine ⟨?_, ?_⟩
  all_goals
    refine (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _).trans ?_
    simp (config := { maxSteps := 2000000 }) only [
      gdhKindAcceptOpkSessLeg, gdhKindAcceptNoOpkSessLeg,
      acceptOpkGdh2ShadowB, acceptOpkGdhCoreShadowB, acceptNoOpkGdhShadowB,
      finishAcceptGdhC, fgPatchShadowC, koskSenderOkPowsC,
      isAdvPowsE, isAdvRegC, chooseRespRandC, recordRespC, hkdfOrRoC, acceptKeysC, ephSidMatchesE,
      rAccFresh, rDh, fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk, buildSecretsE, rs,
      qK, qJ, qO, qHdr, qKJO, reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr,
      reSenderHonest, reDrReal, reDrRand, reTested, reRevealed, reMk, reUpd,
      seHonestPeer, sePeerIk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seFresh, seDrReal, seDrRand, seTested, seRevealed, seSid, sePeerSpk, seHdr, seMk, seUpd,
      catB, consB, eqU32, findHonestC, isGameSpkC, isGameOpkC, resolveSigPkC, honestPeerC,
      checkProvC, partnerC, computePosC, mkSecretPosC, mkPairPosC, entryMatchesC, ddhEqC, ddhEqOptC,
      pa2Mk, paU, paV, paUp, paOpkMode, pa2OpkMode,
      smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
      stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
      oeOpkSk, oeOpkPk, oeConsumed, oeUpd, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
      rNone, rDrKey, initSidE, isSomeE, optFst, optSnd, natEq, nat2Eq, nat3Eq, sidEq,
      optU32Eq, kyberEq, kyberCheckE, nonZero32, orE, mulRight, optBytesEq, getDBytes,
      encEC, encKEM, u32OfNat, lenB, slice32, takeKB, dropB, eLet2,
      letV, bindV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eAny, eFind, eMap,
      act_liftGdhComp_size, act_liftGdhComp_litSize, act_gPrim_size, act_gPrim_litSize,
      liftGdhComp, gPrim, liftBase, ddhQ,
      sBytes32, sDrKey96, qX25519, qX25519Base, qIsCanonical, qPow8, qSigVerify, qKemDecaps, qHkdfDerive96,
      litB, widenB, eqB, act_F_X25519_length, v, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      _root_.SignalPqxdh.TAG_EC_DJB, _root_.SignalPqxdh.TAG_KYBER_1024,
      bits_0, bits_1, bits_2, bits_3, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
      ↓reduceIte, Bool.false_eq_true,
      List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      _root_.SignalPqxdh.LegacyCosted.pqU32Ops, ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
    have h1 : bits (min f.kOn S.N_dh) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h2 : bits (f.kOn.min S.N_dh) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h3 : bits (min f.kOn S.N_sess_tot) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have h4 : bits (f.kOn.min S.N_sess_tot) ≤ bits f.kOn := bits_mono (Nat.min_le_left _ _)
    have := Nat.zero_le (bits f.kFg); have := Nat.zero_le (bits f.kOn); linarith

private theorem dispatchKeyIndQ_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (S : Setup) {Γ : List (Ty pqAtomicSig)} {τ : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q)) {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14}
    {n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 : Nat}
    (h1 : c1.size ≤ n1) (h2 : c2.size ≤ n2) (h3 : c3.size ≤ n3) (h4 : c4.size ≤ n4) (h5 : c5.size ≤ n5)
    (h6 : c6.size ≤ n6) (h7 : c7.size ≤ n7) (h8 : c8.size ≤ n8) (h9 : c9.size ≤ n9) (h10 : c10.size ≤ n10)
    (h11 : c11.size ≤ n11) (h12 : c12.size ≤ n12) (h13 : c13.size ≤ n13) (h14 : c14.size ≤ n14) :
    (dispatchKeyIndQ S qE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Comp pqAtomicOps I Γ τ).size ≤
      qE.size + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + 40 := by
  simp only [dispatchKeyIndQ, Comp.size, compRename_size, Expr.size, Expr.v0]; omega

theorem fgKeyInd1KeyGapDhKindAtomicProg_size_le_aux (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  let f := keyIndKFuelsOfBudget S b
  have hInit := gdh1KeyKindInitC_size_le S b; have hRo := gdhKindRoArm_size_le S f
  have hFin : (gdh1KeyKindFinishC S b).size ≤ 200 * bits f.kOff + 250 * bits f.kOn + 21000 := gdh1KeyKindFinishC_size_le S b
  obtain ⟨hN1, hN3, hN4, hN2, hN9, hN12, hN13, hN14⟩ := gdhNoFgLegs_size_le f.kOn
  have hS5 := gdhInitSessLeg_size_le S f true; have hS6 := gdhInitSessLeg_size_le S f false
  obtain ⟨hSaO, hSaN⟩ := gdhAcceptSessLegs_size_le S f
  obtain ⟨hP1, hPP, hPT, hPS, hP5b, hP7b, hPV0⟩ :=
    gdhPayExprs_size_le S (A := .prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy) S.N_send_opk S.N_opk
  obtain ⟨_, _, _, _, hP6b, hP8b, _⟩ :=
    gdhPayExprs_size_le S (A := .prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy) S.N_send_no_opk S.N_no_opk
  have hA1 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN1 hP1) 25)
  have hA2 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN2 hP1) 25)
  have hA3 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN3 hPP) 25)
  have hA4 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN4 hPT) 25)
  have hA5 := (liftSigDdhSessArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hS5 hP5b) 45)
  have hA6 := (liftSigDdhSessArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hS6 hP6b) 45)
  have hA7 := (liftSigDdhSessArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hSaO hP7b) 45)
  have hA8 := (liftSigDdhSessArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hSaN hP8b) 45)
  have hA9 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN9 hPS) 25)
  have hA11 : (Comp.ret (I := pqSigAndDdhIface) (Γ := .unit :: [gdh1KeyActiveKindStateTy, (pqKeyIndCodec S).Q])
      (.pair (atomicRNoneE (S := S)) .v1)).size ≤ 20 := by
    simp only [atomicRNoneE, Comp.size, Expr.size, Expr.v1, pqAtomicOps, atomicPureOps]; omega
  have hA12 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN12 hPS) 25)
  have hA13 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN13 hPV0) 25)
  have hA14 := (liftSigDdhNoFgArm_size_le S _ _).trans (Nat.add_le_add_right (Nat.add_le_add hN14 hPP) 25)
  have hHdl : (gdh1KeyKindHandleC S b).size ≤
      8 * bits (avlHeightCap f.kAvl) + 320 * bits f.kFg + 2660 * bits f.kOn + 355000 := by
    unfold gdh1KeyKindHandleC; dsimp only
    refine (dispatchKeyIndQ_size_le S .v1 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9 hRo hA11 hA12 hA13 hA14).trans ?_
    have hv1 : (.v1 : Expr pqAtomicOps [gdh1KeyActiveKindStateTy, (pqKeyIndCodec S).Q] _).size = 1 := rfl
    rw [hv1]; omega
  have hCostGe : 6 * b.q_total + 4 ≤ stepCostBudget S b := by
    have h1 : 6 * b.q_total + 4 ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le.intro (k := 65536 * b.q_total ^ 2 + 131066 * b.q_total + 65532) (by ring)
    unfold stepCostBudget; dsimp only
    exact h1.trans (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _ |>.trans
      (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))))
  have hbSent : bits (keyIndSentinel S b) ≤ bits (stepCostBudget S b) :=
    bits_mono ((keyIndSentinel_le S b).trans ((by omega : _ ≤ 6 * b.q_total + 4).trans hCostGe))
  have hbSig : bits (activeSigBudget S b) ≤ bits (stepCostBudget S b) := bits_mono ((Nat.min_le_left _ _).trans
    ((by have := Nat.min_le_right b.q_on b.q_total; omega : _ ≤ 6 * b.q_total + 4).trans hCostGe))
  have hbOn := bits_mono ((show f.kOn ≤ b.q_total from Nat.min_le_right _ _).trans ((by omega : _ ≤ 6 * b.q_total + 4).trans hCostGe))
  have hbOff := bits_mono ((show f.kOff ≤ b.q_total from Nat.min_le_right _ _).trans ((by omega : _ ≤ 6 * b.q_total + 4).trans hCostGe))
  have hbFg := bits_mono ((show f.kFg ≤ b.q_total from Nat.min_le_left _ _).trans ((by omega : _ ≤ 6 * b.q_total + 4).trans hCostGe))
  have hbAvl : bits (avlHeightCap f.kAvl) ≤ bits (stepCostBudget S b) := by
    have hkAvl : f.kAvl ≤ 3 * b.q_total + 1 := by
      dsimp only [f, keyIndKFuelsOfBudget]
      have := Nat.min_le_right b.q_ro b.q_total; have := Nat.min_le_right b.q_on b.q_total; omega
    have hCap : avlHeightCap f.kAvl ≤ 6 * b.q_total + 4 := by
      unfold avlHeightCap bits; have := Nat.log_le_self 2 f.kAvl; omega
    exact bits_mono (hCap.trans hCostGe)
  have hBud : 390000 ≤ reductionSizeBudget := by decide
  dsimp only [CostedReduction.size, fgKeyInd1KeyGapDhKindAtomicProg]
  generalize bits (stepCostBudget S b) = bSB at hbSent hbSig hbOn hbOff hbFg hbAvl ⊢
  linarith only [hInit, hHdl, hFin, hbSent, hbSig, hbOn, hbOff, hbFg, hbAvl, hBud, Nat.zero_le bSB]

end SizeBounds

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBoundsArms
