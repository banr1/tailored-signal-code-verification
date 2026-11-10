/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.KindedDispatch -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost

/-!
# Cost Bounds for Shadow-Indexed `KeyInd` Gap-DH Handlers

Proves closed-form `Comp.cost` and per-arm `costAt` upper bounds for the shadow-indexed `KeyInd`
Gap-DH random-oracle arm, online session arms, 14-way handlers (`gdhShadowHandleAtomic`,
`gdhShadowHandle2Atomic`), and clamped finishers (`gdhShadowFinishAtomic`, `gdhShadowFinish2Atomic`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost

open OracleSpec
open _root_.SignalPqxdh (Setup Bytes F_X25519 QueryBudget KeyIndQuery)
open _root_.SignalPqxdh.Security (stepCostBudgetSplit keyIndQueryKind)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface
  pqAtomicSig pqAtomicOps pqAtomicSamplers pqKeyIndCodec
  AtomicPureOp atomicPureOps atomicBaseSamplers unifSamplers AtomicBaseUnif
  PB drKeyT bits bits_mono
)
open _root_.SignalPqxdh.Costed (PTag)
open _root_.SignalPqxdh.LegacyCosted (B pqSig pqxdhOps pqGapDhIface pqSamplers)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  PT Ext v letV bindV caseOptV caseSumV findMV anyMV mapMV foldMV
  eLet eCaseOpt eCaseSum eFind eAny eMap eqB orE eLet2
  fgPosTy fgPatchEntryTy drKeyTy simTy keyIndStateTy keyIndRespTy
  paramsTy params2Ty gdhStateTy gdhState2Ty initQTy accQTy
  fePos1 fePos2 fePos3 fePos4 feSs feDk feMk ddhQ ddhEqC ddhEqOptC
  gPrim sBytes32 sRandom64 sDrKey96
  qX25519 qX25519Base qIsCanonical qPow8 qSigPkGen qSigSign qSigVerify
  qKemKeyGen qKemEncaps qKemDecaps
  mkSecretPosC computePosC computeOptPosInitC chooseInitRandC chooseRespRandC
  koskBundleOkPowsC koskSenderOkPowsC resolveSigPkC lookupSpkSkC
  honestPeerC checkProvC findHonestC finishAcceptGdhC
  slice32 litB takeKB lenB natEq nat2Eq nat3Eq sidEq kyberEq kyberCheckE
  u32OfNat eqU32 optU32Eq isSomeE optFst optSnd nonZero32 encEC encKEM
  initSidE initSlotIdxE ephSidMatchesE spkFlatIdxE opkFlatIdxE
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb
  peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peMk peUpd
  sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk sbMk sbUpd
  oeOpkSk oeOpkPk oeConsumed oeMk oeUpd
  buIkB buSpkB buSpkId buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig buMk
  hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt hdMk
  seSid seMk seUpd reMk reUpd stMk stUpd
  qK qJ qO qHdr qKJO
  rNone rInitPrin rPk rCorr rBundle rHdr rInitUnfresh rAccFresh rDrKey rSpkSk
  paU paV paUp paPrinFlag paPrinIdx paDhFlag paEphIdx paSpkIdx paOpkMode paOpkIdx paMode
  pa2U pa2V pa2Up pa2PrinTarget pa2DhFlag pa2EphTarget pa2SpkTarget pa2OpkMode pa2OpkTarget pa2Mode
  smBase smFgL smRaw smLog smPows smMk smUpd
  wrapBase wrapSim wrapBase2 wrapSim2
  initPrinGdhB initPrinGdh2B corruptB genSpkGdhB genSpkGdh2B genOpkGdhB genOpkGdh2B
  testB revealB registerGdhB revealSpkB
  logFindC logFind2C spkPowsC initDh1CandC respDh1CandC findMapStepC findMapStep2C
  entryMatchesC mulRight rs freshE
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (
  isSecEntry
  letV_costUB bindV_costUB caseOptV_costUB caseSumV_costUB
  findMV_costUB anyMV_costUB mapMV_costUB foldMV_costUB
  eLet_costUB eCaseOpt_costUB eCaseSum_costUB eFind_costUB eAny_costUB eMap_costUB
  litB_costUB takeKB_costUB lenB_costUB eqB_costUB u32OfNat_costUB eqU32_costUB
  sBool_costUB sBytes32_costUB sRandom64_costUB sDrKey96_costUB sIndex_costUB
  qX25519_costUB qX25519Base_costUB qIsCanonical_costUB qPow8_costUB
  qSigPkGen_costUB qSigSign_costUB qSigVerify_costUB
  qKemKeyGen_costUB qKemEncaps_costUB qKemDecaps_costUB ddhQ_costUB
  gPrim_costUB v_costUB mkSecretPosC_costUB computePosC_costUB computeOptPosInitC_costUB
  koskBundleOkPowsC_costUB koskSenderOkPowsC_costUB resolveSigPkC_costUB lookupSpkSkC_costUB
  honestPeerC_costUB checkProvC_costUB findHonestC_costUB chooseInitRandC_costUB
  finishAcceptGdhC_costUB encEC_costUB encKEM_costUB slice32_costUB
  rNone_costUB rInitPrin_costUB rPk_costUB rCorr_costUB rBundle_costUB rHdr_costUB
  rInitUnfresh_costUB rAccFresh_costUB rDrKey_costUB rSpkSk_costUB
  qK_costUB qJ_costUB qO_costUB qHdr_costUB
  smBase_costUB smFgL_costUB smRaw_costUB smLog_costUB smPows_costUB
  paU_costUB paV_costUB paUp_costUB paPrinFlag_costUB paPrinIdx_costUB
  paDhFlag_costUB paEphIdx_costUB paSpkIdx_costUB paOpkMode_costUB paOpkIdx_costUB paMode_costUB
  wrapBase_costUB wrapSim_costUB
  logFindC_costUB spkPowsC_costUB initDh1CandC_costUB respDh1CandC_costUB findMapStepC_costUB
  bits_0 bits_1 bits_2 bits_32 bits_64 bits_96 bits_128 bits_160 bits_192
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlSearchResTy avlSearchB192C avlInsertAtPathC
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (
  avlSearchB192C_cost_le avlInsertAtPathC_cost_le
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp)
open Computational.Proofs.ReductionDsl.KindedDispatch (
  DispatchesTo costAt_eq_of_dispatchesTo costAt_le_arm_cost_of_dispatchesTo
)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface aiOfIface aiGapDh aiSigDdh
  embedSort embedTy embedCtx embedVar
  exprRename exprRename_cost compRename compRename_cost
  aop mapOpExpr mapExpr expr_cost_two_mul_le mapSamp mapSampH mapSampCast mapKeyIndPrimTag
  mapComp mapComp_cost_two_mul_le mapComp_cost_eleven_mul_le sampR64W
  tlGapDhKeyInd tlSigDdhKeyInd finSidToNatExpr
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget (
  roTableKappa roTableStepCost
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost (
  dispatchKeyIndQ_ro_costAt_le dispatchKeyIndQ_online_costAt_le
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  wkRen1 dispatchKeyIndQ
  finPairToNatE finTripleToNatE initPayToNatE accPayToNatE atomicRNoneE emptyVarRen
  ren2 ren3 ren4 runAt2 runAt3 runAt4
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget
  seqFgEntryTy fgSessCtrTy fgListAndShadowTy roPosPackTy
  fgPatchShadowC sessScanMinPredC fgSessScanC fgSessScanPackC
  roParsedPrePos160C roParsedPrePos192C
  extractMode0KC gdhFinishK extractMode0_2KC gdhFinish2K
  fgRoValAtomicTy rawRoValAtomicTy fgShadowAtomicTy simShadowAtomicTy
  gdhShadowStateAtomicTy gdhShadowState2AtomicTy
  genSpkGdhActiveKB initiateGdhShadowB initiateGdh2ShadowB initiateGdhActiveShadowInnerB
  acceptOpkGdhCoreShadowB acceptOpkGdhShadowB acceptOpkGdh2ShadowB acceptNoOpkGdhShadowB
  GdhAtomicLift gdhLift2Key gdhLift1Key liftGdhAtomic
  ren1 wkSndVar runAt1 sampleDrKey96LiftC
  roNotPrefixE roLenEqE seqFgEntryDkE roHitRespSimE rawMissRespSimE parsedMissRespSimE
  roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC roParsedShadowAtomicC
  liftKind0NoFgArm liftKind0SessArm liftKind1RoArm wrapSimSessArm wrapNoFgArm
  gdhShadowHandle2Atomic gdhShadowHandleAtomic gdhShadowFinish2Atomic gdhShadowFinishAtomic
)

theorem liftGdhAtomic_gdhLift1Key_cost_eq {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    (liftGdhAtomic gdhLift1Key c).cost = (liftGdhAtomic gdhLift2Key c).cost := by
  simp only [liftGdhAtomic, gdhLift1Key, gdhLift2Key]
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 => simp only [liftGdhComp, mapComp, Comp.cost, ih1, ih2]
  | ite _ _ _ ih1 ih2 => simp only [liftGdhComp, mapComp, Comp.cost, ih1, ih2]
  | caseOpt _ _ _ ih1 ih2 => simp only [liftGdhComp, mapComp, Comp.cost, ih1, ih2]
  | caseSum _ _ _ ih1 ih2 => simp only [liftGdhComp, mapComp, Comp.cost, ih1, ih2]
  | sample s _ => change (mapSamp aiSigDdh s).cost = (mapSamp aiGapDh s).cost; cases s <;> rfl
  | query g _ => cases g with | inl t => cases t <;> rfl | inr u => cases u; rfl
  | iter _ _ _ ih => simp only [liftGdhComp, mapComp, Comp.cost, ih]
  | findM _ _ _ ih => simp only [liftGdhComp, mapComp, Comp.cost, ih]
  | anyM _ _ _ ih => simp only [liftGdhComp, mapComp, Comp.cost, ih]
  | mapM _ _ _ ih => simp only [liftGdhComp, mapComp, Comp.cost, ih]
  | consumeFirstM _ _ _ _ ih => simp only [liftGdhComp, mapComp, Comp.cost, ih]
  | foldM _ _ _ _ ih => simp only [liftGdhComp, mapComp, Comp.cost, ih]

/-- Typeclass witnessing that `gl : GdhAtomicLift A` has the same syntactic `Comp.cost` as `gdhLift2Key`. -/
class StdGdhLift {ι : Type} {T : OracleSpec ι} {A : AtomicIface T} (gl : GdhAtomicLift A) : Prop where
  cost_eq_twoKey : ∀ {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqGapDhIface Γ τ),
    (liftGdhAtomic gl c).cost = (liftGdhAtomic gdhLift2Key c).cost

instance instStdGdhLift2Key : StdGdhLift gdhLift2Key := ⟨fun _ => rfl⟩
instance instStdGdhLift1Key : StdGdhLift gdhLift1Key := ⟨liftGdhAtomic_gdhLift1Key_cost_eq⟩

@[local simp] private theorem runAt1_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (c : Comp pqAtomicOps I [A] R) :
    (runAt1 aE c).cost = aE.cost + c.cost + 2 := by
  simp only [runAt1, Comp.cost, compRename_cost]; omega
@[local simp] private theorem runAt2_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (c : Comp pqAtomicOps I [A, B] R) :
    (runAt2 aE bE c).cost = aE.cost + bE.cost + c.cost + 4 := by
  simp only [runAt2, Comp.cost, exprRename_cost, compRename_cost]; omega
@[local simp] private theorem runAt3_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (m : Comp pqAtomicOps I [A, B, C] R) :
    (runAt3 aE bE cE m).cost = aE.cost + bE.cost + cE.cost + m.cost + 6 := by
  simp only [runAt3, Comp.cost, exprRename_cost, compRename_cost]; omega
@[local simp] private theorem runAt4_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (cE : Expr pqAtomicOps Γ C) (dE : Expr pqAtomicOps Γ D) (m : Comp pqAtomicOps I [A, B, C, D] R) :
    (runAt4 aE bE cE dE m).cost = aE.cost + bE.cost + cE.cost + dE.cost + m.cost + 8 := by
  simp only [runAt4, Comp.cost, exprRename_cost, compRename_cost]; omega

@[local simp] private theorem mapExpr_v_cost {Γ Δ : List PT} {τ : PT} [Ext Γ Δ] (x : Var Γ τ) :
    (mapExpr (v (Δ := Δ) x)).cost = 1 := rfl

theorem ddhEqC_atomic_cost_eq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT}
    (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (liftGdhAtomic gl (ddhEqC p1 p2)).cost = (mapExpr p1).cost + (mapExpr p2).cost + 305 := by
  rw [StdGdhLift.cost_eq_twoKey]
  simp only [liftGdhAtomic, gdhLift2Key, ddhEqC, orE, letV, caseSumV, eqB, ddhQ, v,
    mapComp, mapExpr, mapOpExpr, tlGapDhKeyInd, aop,
    Comp.cost, Expr.cost, aiGapDh, aiOfIface,
    _root_.SignalPqxdh.Costed.pqGapDhIface, _root_.SignalPqxdh.Costed.pqChalIface,
    _root_.SignalPqxdh.Costed.gapDhDdhOracle,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, PNat.val_ofNat]
  norm_num [Nat.max_def]

theorem ddhEqOptC_atomic_cost_eq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT}
    (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (liftGdhAtomic gl (ddhEqOptC p1? p2?)).cost =
      (mapExpr p1?).cost + (mapExpr p2?).cost + 316 := by
  rw [StdGdhLift.cost_eq_twoKey]
  have hDdh := fun {Δ : List PT} (x y : Expr pqxdhOps Δ fgPosTy) =>
    ddhEqC_atomic_cost_eq gdhLift2Key x y
  simp only [liftGdhAtomic, gdhLift2Key] at hDdh ⊢
  simp only [ddhEqOptC, letV, caseOptV, v, mapComp, mapExpr, Comp.cost, Expr.cost, hDdh]
  norm_num [Nat.max_def]

theorem entryMatchesC_atomic_cost_eq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) :
    (liftGdhAtomic gl (entryMatchesC pos1 pos2 pos3 pos4? ss e)).cost = 1335 := by
  rw [StdGdhLift.cost_eq_twoKey]
  have hDdh := fun {Δ' : List PT} (x y : Expr pqxdhOps Δ' fgPosTy) => ddhEqC_atomic_cost_eq gdhLift2Key x y
  have hDdhOpt := fun {Δ' : List PT} (x y : Expr pqxdhOps Δ' (.opt fgPosTy)) =>
    ddhEqOptC_atomic_cost_eq gdhLift2Key x y
  simp only [liftGdhAtomic, gdhLift2Key] at hDdh hDdhOpt ⊢
  simp only [entryMatchesC, bindV, fePos1, fePos2, fePos3, fePos4, feSs, eqB,
    mapComp, mapExpr, mapOpExpr, aop, hDdh, hDdhOpt, mapExpr_v_cost,
    Comp.cost, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost, PNat.val_ofNat]
  norm_num [Nat.max_def]

theorem sessScanMinPredC_atomic_cost_eq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (minIdx : Var Γ₀ .nat) (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (se : Var Δ seqFgEntryTy) :
    (liftGdhAtomic gl (sessScanMinPredC minIdx pos1 pos2 pos3 pos4? ss se)).cost = 1344 := by
  rw [StdGdhLift.cost_eq_twoKey]
  have hEm := entryMatchesC_atomic_cost_eq gdhLift2Key pos1 pos2 pos3 pos4? ss (Δ := fgPatchEntryTy :: Δ) .zero
  simp only [liftGdhAtomic, gdhLift2Key] at hEm ⊢
  simp only [sessScanMinPredC, letV, mapComp, mapExpr, mapExpr_v_cost, Comp.cost, Expr.cost, hEm]
  norm_num [Nat.max_def]

theorem keyInd_gpair_sum_eq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (minIdx : Var Γ₀ .nat) (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (se : Var Δ seqFgEntryTy) (e : Var Δ fgPatchEntryTy) :
    ((liftGdhAtomic gl (sessScanMinPredC minIdx pos1 pos2 pos3 pos4? ss se)).cost + 1) +
    ((liftGdhAtomic gl (entryMatchesC pos1 pos2 pos3 pos4? ss e)).cost + 1) = 2681 := by
  rw [sessScanMinPredC_atomic_cost_eq, entryMatchesC_atomic_cost_eq]

theorem fgSessScanPackC_atomic_cost_eq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (kOn : ℕ) :
    (liftGdhAtomic gl (fgSessScanPackC kOn)).cost = 1345 * kOn + 31 := by
  rw [StdGdhLift.cost_eq_twoKey]
  have hPred := fun {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
      [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
      (m : Var Γ₀ .nat) (p1 : Var Γ₁ fgPosTy) (p2 : Var Γ₂ fgPosTy) (p3 : Var Γ₃ fgPosTy)
      (p4 : Var Γ₄ (.opt fgPosTy)) (s : Var Γ₅ (B 32)) (se : Var Δ seqFgEntryTy) =>
    sessScanMinPredC_atomic_cost_eq gdhLift2Key m p1 p2 p3 p4 s se
  simp only [liftGdhAtomic, gdhLift2Key] at hPred ⊢
  simp only [fgSessScanPackC, fgSessScanC, letV, findMV,
    mapComp, mapExpr, mapExpr_v_cost, Comp.cost, Expr.cost, hPred]
  omega

theorem sessScanMinPredAtomic_per_entry_cost_le
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (minIdx : Var Γ₀ .nat)
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (se : Var Δ seqFgEntryTy) :
    (mapComp tlSigDdhKeyInd (liftGdhComp (sessScanMinPredC minIdx pos1 pos2 pos3 pos4? ss se))).cost + 1 ≤
      3811 := by
  have h := sessScanMinPredC_atomic_cost_eq gdhLift1Key minIdx pos1 pos2 pos3 pos4? ss se
  simp only [liftGdhAtomic, gdhLift1Key] at h
  omega

theorem fgPatchShadowAtomic_per_entry_cost_le
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (e : Var Δ fgPatchEntryTy) :
    (mapComp tlSigDdhKeyInd (liftGdhComp (entryMatchesC pos1 pos2 pos3 pos4? ss e))).cost + 1 ≤
      3796 := by
  have h := entryMatchesC_atomic_cost_eq gdhLift1Key pos1 pos2 pos3 pos4? ss e
  simp only [liftGdhAtomic, gdhLift1Key] at h
  omega

/-- Bounds the combined per-entry scan cost of `sessScanMinPredC` and `entryMatchesC` by `2 ^ 13`. -/
theorem keyInd_gpair_sum_le_8192
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (minIdx : Var Γ₀ .nat)
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (se : Var Δ seqFgEntryTy) (e : Var Δ fgPatchEntryTy) :
    ((mapComp tlSigDdhKeyInd (liftGdhComp (sessScanMinPredC minIdx pos1 pos2 pos3 pos4? ss se))).cost + 1) +
    ((mapComp tlSigDdhKeyInd (liftGdhComp (entryMatchesC pos1 pos2 pos3 pos4? ss e))).cost + 1) ≤
      2 ^ 13 := by
  have ha := sessScanMinPredAtomic_per_entry_cost_le minIdx pos1 pos2 pos3 pos4? ss se
  have hb := fgPatchShadowAtomic_per_entry_cost_le pos1 pos2 pos3 pos4? ss e
  omega

/-- `CryptoVerification.E2E.ofU8` preserves `BEq` on byte lists, preventing cross-length collisions
    in `B 192` AVL keys. -/
theorem avlKey_ofU8_beq_eq (sec sec' : Bytes) :
    (CryptoVerification.E2E.ofU8 sec == CryptoVerification.E2E.ofU8 sec') = (sec == sec') :=
  Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec.ofU8_beq_eq sec sec'

theorem sampleDrKey96LiftC_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List (Ty pqAtomicSig)} :
    (sampleDrKey96LiftC gl (Γ := Γ)).cost ≤ 200 := by
  rw [sampleDrKey96LiftC, compRename_cost, StdGdhLift.cost_eq_twoKey]
  decide

theorem roParsedPrePos160C_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] :
    (liftGdhAtomic gl (roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero)).cost ≤ 5000 := by
  rw [StdGdhLift.cost_eq_twoKey]
  have h11 := mapComp_cost_eleven_mul_le tlGapDhKeyInd
    (roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero)
  have hUB := (roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero).cost_le_costUB
  have hCalc : (roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero).costUB ≤ 2350 := by
    simp only [roParsedPrePos160C, bindV_costUB, letV_costUB, mkSecretPosC_costUB, slice32_costUB,
      v_costUB, Comp.costUB, Expr.costUB, bits_32, bits_64, bits_96, bits_128]
    omega
  simp only [liftGdhAtomic, gdhLift2Key]
  omega

theorem roParsedPrePos192C_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] :
    (liftGdhAtomic gl (roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero)).cost ≤ 6000 := by
  rw [StdGdhLift.cost_eq_twoKey]
  have h11 := mapComp_cost_eleven_mul_le tlGapDhKeyInd
    (roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero)
  have hUB := (roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero).cost_le_costUB
  have hCalc : (roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero).costUB ≤ 2800 := by
    simp only [roParsedPrePos192C, bindV_costUB, letV_costUB, mkSecretPosC_costUB, slice32_costUB,
      v_costUB, Comp.costUB, Expr.costUB, bits_32, bits_64, bits_96, bits_128, bits_160]
    omega
  simp only [liftGdhAtomic, gdhLift2Key]
  omega

theorem roRawFallbackShadowAtomicC_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (f : KeyIndKFuels) :
    (roRawFallbackShadowAtomicC gl f).cost ≤ 4420 * bits f.kAvl + 1600 := by
  have hSmp := sampleDrKey96LiftC_cost_le gl
    (Γ := avlSearchResTy rawRoValAtomicTy :: [simShadowAtomicTy, PB 192])
  have hSrch := avlSearchB192C_cost_le (I := A.toIface) f.kAvl
    (Γ := [simShadowAtomicTy, PB 192]) (V := rawRoValAtomicTy)
    (.snd (.snd (.snd (.snd .v0)))) (aop (.pbytesToBytes 192) .v1)
  have hIns := avlInsertAtPathC_cost_le (I := A.toIface) f.kAvl
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) :: avlSearchResTy rawRoValAtomicTy ::
      [simShadowAtomicTy, PB 192])
    (.snd (.snd (.snd (.snd .v2)))) (.snd .v1) (aop (.pbytesToBytes 192) .v3) .v0
  simp only [roRawFallbackShadowAtomicC, rawMissRespSimE, roHitRespSimE,
    smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows, rDrKey, v,
    mapExpr, runAt3_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    aop, Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.aop,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, PNat.val_ofNat] at hSrch hIns ⊢
  omega

theorem roParsedPostPosShadowAtomicC_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (f : KeyIndKFuels) :
    (roParsedPostPosShadowAtomicC gl f).cost ≤ 4420 * bits f.kAvl + 1345 * f.kOn + 2100 := by
  have hScan := fgSessScanPackC_atomic_cost_eq gl f.kOn
  have hSmp := sampleDrKey96LiftC_cost_le gl
    (Γ := .opt (embedTy seqFgEntryTy) :: avlSearchResTy fgRoValAtomicTy ::
      [embedTy roPosPackTy, simShadowAtomicTy, PB 192])
  have hSrch := avlSearchB192C_cost_le (I := A.toIface) f.kAvl
    (Γ := [embedTy roPosPackTy, simShadowAtomicTy, PB 192]) (V := fgRoValAtomicTy)
    (.fst (.snd (.snd (.snd .v1)))) (aop (.pbytesToBytes 192) .v2)
  have hIns := avlInsertAtPathC_cost_le (I := A.toIface) f.kAvl
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) :: .opt (embedTy seqFgEntryTy) ::
      avlSearchResTy fgRoValAtomicTy :: [embedTy roPosPackTy, simShadowAtomicTy, PB 192])
    (.fst (.snd (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))
    (.snd .v2)
    (aop (.pbytesToBytes 192) (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (.pair .v0 (.fst (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))
  simp only [roParsedPostPosShadowAtomicC, parsedMissRespSimE, roHitRespSimE, seqFgEntryDkE,
    feMk, feDk, smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows, rDrKey, v,
    mapExpr, exprRename_cost, runAt3_cost, runAt4_cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    aop, Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.aop,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, PNat.val_ofNat, bits_0, bits_1,
    hScan] at hSrch hIns ⊢
  omega

theorem roParsedShadowAtomicC_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (f : KeyIndKFuels) :
    (roParsedShadowAtomicC gl f).cost ≤ 4420 * bits f.kAvl + 1345 * f.kOn + 8600 := by
  have hRaw := roRawFallbackShadowAtomicC_cost_le gl f
  have hPost := roParsedPostPosShadowAtomicC_cost_le gl f
  have h160 := roParsedPrePos160C_atomic_cost_le gl
  have h192 := roParsedPrePos192C_atomic_cost_le gl
  have hF : F_X25519.length = 32 := rfl
  simp only [roParsedShadowAtomicC, roNotPrefixE, roLenEqE, eqB, takeKB, litB, lenB, natEq, v,
    mapExpr, mapOpExpr, exprRename_cost, runAt1_cost, runAt3_cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    aop, pqAtomicOps, atomicPureOps, AtomicPureOp.cost, PNat.val_ofNat, hF, bits_160, bits_192]
  omega

theorem liftKind1RoArm_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels) {paTy : PT} :
    (liftKind1RoArm gl S f (paTy := paTy)).cost ≤
      4420 * bits f.kAvl + 1345 * f.kOn + 8630 := by
  have hRo := roParsedShadowAtomicC_cost_le gl f
  simp only [liftKind1RoArm, runAt2_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

/-- Bounds `roParsedShadowAtomicC` cost by `roTableStepCost roTableKappa f.kAvl + 1345 * f.kOn`. -/
theorem roParsedShadowAtomicC_cost_le_budget {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (f : KeyIndKFuels) :
    (roParsedShadowAtomicC gl f).cost ≤
      roTableStepCost roTableKappa f.kAvl + 1345 * f.kOn := by
  have h := roParsedShadowAtomicC_cost_le gl f
  simp only [roTableStepCost, roTableKappa]
  omega

private theorem expr_cost_le_costUB {Γ : List PT} {τ : PT} (e : Expr pqxdhOps Γ τ) :
    e.cost ≤ e.costUB := by
  have h := (Comp.ret (I := pqGapDhIface) e).cost_le_costUB
  simp only [Comp.cost, Comp.costUB] at h
  omega

private theorem mapExpr_cost_le_two_costUB {Γ : List PT} {τ : PT} (e : Expr pqxdhOps Γ τ) :
    (mapExpr e).cost ≤ 2 * e.costUB := by
  have h2 := expr_cost_two_mul_le e
  have hUB := expr_cost_le_costUB e
  omega

private theorem liftGdhAtomic_cost_le_three_costUB {ι : Type} {T : OracleSpec ι}
    {A : AtomicIface T} (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    (liftGdhAtomic gl c).cost ≤ 3 * c.costUB := by
  rw [StdGdhLift.cost_eq_twoKey]
  have h11 := mapComp_cost_eleven_mul_le tlGapDhKeyInd c
  have hUB := c.cost_le_costUB
  simp only [liftGdhAtomic, gdhLift2Key]
  omega

theorem fgPatchShadowC_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (kFg : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy))
    (ctr : Expr pqxdhOps Δ .nat) :
    (liftGdhAtomic gl (fgPatchShadowC kFg pos1 pos2 pos3 pos4? ss fgL fgSess ctr)).cost ≤
      1336 * kFg + (mapExpr fgL).cost + (mapExpr fgSess).cost + (mapExpr ctr).cost + 350 := by
  rw [StdGdhLift.cost_eq_twoKey]
  have hEm := entryMatchesC_atomic_cost_eq gdhLift2Key pos1 pos2 pos3 pos4? ss
    (Δ := fgPatchEntryTy :: fgListAndShadowTy :: Δ) .zero
  have hSmp : (liftGdhAtomic gdhLift2Key
      (gPrim (Γ := .opt fgPatchEntryTy :: fgListAndShadowTy :: Δ) sDrKey96)).cost ≤ 295 := by
    apply Nat.le_trans (liftGdhAtomic_cost_le_three_costUB gdhLift2Key
      (gPrim (Γ := .opt fgPatchEntryTy :: fgListAndShadowTy :: Δ) sDrKey96))
    simp only [gPrim_costUB, sDrKey96_costUB]
    omega
  simp only [liftGdhAtomic, gdhLift2Key] at hEm hSmp ⊢
  have hMul : kFg * ((mapComp tlGapDhKeyInd (entryMatchesC pos1 pos2 pos3 pos4? ss
      (Δ := fgPatchEntryTy :: fgListAndShadowTy :: Δ) .zero)).cost + 1) = 1336 * kFg := by
    rw [hEm]; ring
  simp only [fgPatchShadowC, letV, bindV, caseOptV, findMV, feMk, feDk, v,
    mapComp, mapExpr, Comp.cost, Expr.cost, bits_1]
  omega

private theorem le_atomic_letV {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT} {τ₁ τ₂ : PT}
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    {Bk : ℕ} (hk : (liftGdhAtomic gl (k .zero)).cost ≤ Bk) :
    (liftGdhAtomic gl (letV e k)).cost ≤ 2 * e.costUB + Bk + 2 := by
  rw [StdGdhLift.cost_eq_twoKey] at hk ⊢
  have he := mapExpr_cost_le_two_costUB e
  simp only [liftGdhAtomic, gdhLift2Key, letV, mapComp, Comp.cost] at hk ⊢
  omega

private theorem le_atomic_bindV {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps pqGapDhIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    {Bm Bk : ℕ} (hm : (liftGdhAtomic gl m).cost ≤ Bm)
    (hk : (liftGdhAtomic gl (k .zero)).cost ≤ Bk) :
    (liftGdhAtomic gl (bindV m k)).cost ≤ Bm + Bk + 1 := by
  rw [StdGdhLift.cost_eq_twoKey] at hm hk ⊢
  simp only [liftGdhAtomic, gdhLift2Key, bindV, mapComp, Comp.cost] at hm hk ⊢
  omega

private theorem le_atomic_bindV_ub {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps pqGapDhIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    {Bk : ℕ} (hk : (liftGdhAtomic gl (k .zero)).cost ≤ Bk) :
    (liftGdhAtomic gl (bindV m k)).cost ≤ 3 * m.costUB + Bk + 1 :=
  le_atomic_bindV gl m k (liftGdhAtomic_cost_le_three_costUB gl m) hk

private theorem le_atomic_ite {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT} {τ : PT}
    (b : Expr pqxdhOps Γ .bool) (t e : Comp pqxdhOps pqGapDhIface Γ τ)
    {Bt Be : ℕ} (ht : (liftGdhAtomic gl t).cost ≤ Bt) (he : (liftGdhAtomic gl e).cost ≤ Be) :
    (liftGdhAtomic gl (.ite b t e)).cost ≤ 2 * b.costUB + max Bt Be + 1 := by
  rw [StdGdhLift.cost_eq_twoKey] at ht he ⊢
  have hb := mapExpr_cost_le_two_costUB b
  simp only [liftGdhAtomic, gdhLift2Key, mapComp, Comp.cost] at ht he ⊢
  omega

private theorem le_atomic_caseOptV {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] {Γ : List PT} {τ₁ τ₂ : PT}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps pqGapDhIface Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    {Bn Bs : ℕ} (hn : (liftGdhAtomic gl kn).cost ≤ Bn)
    (hs : (liftGdhAtomic gl (ks .zero)).cost ≤ Bs) :
    (liftGdhAtomic gl (caseOptV o kn ks)).cost ≤ 2 * o.costUB + max Bn (Bs + 1) + 2 := by
  rw [StdGdhLift.cost_eq_twoKey] at hn hs ⊢
  have ho := mapExpr_cost_le_two_costUB o
  simp only [liftGdhAtomic, gdhLift2Key, caseOptV, mapComp, Comp.cost] at hn hs ⊢
  omega

private theorem fgPatchShadowC_atomic_cost_le_ub {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (kFg : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy))
    (ctr : Expr pqxdhOps Δ .nat) :
    (liftGdhAtomic gl (fgPatchShadowC kFg pos1 pos2 pos3 pos4? ss fgL fgSess ctr)).cost ≤
      1336 * kFg + 2 * fgL.costUB + 2 * fgSess.costUB + 2 * ctr.costUB + 350 := by
  have h := fgPatchShadowC_atomic_cost_le gl kFg pos1 pos2 pos3 pos4? ss fgL fgSess ctr
  have h1 := mapExpr_cost_le_two_costUB fgL
  have h2 := mapExpr_cost_le_two_costUB fgSess
  have h3 := mapExpr_cost_le_two_costUB ctr
  omega

local macro "peel_atomic_cost" : tactic => `(tactic|
  repeat (first
    | (apply le_atomic_bindV; · exact fgPatchShadowC_atomic_cost_le_ub _ _ _ _ _ _ _ _ _ _)
    | apply le_atomic_letV
    | apply le_atomic_bindV_ub
    | apply le_atomic_ite
    | apply le_atomic_caseOptV
    | exact liftGdhAtomic_cost_le_three_costUB _ _))

theorem genSpkGdhActiveKB_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (kOn : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    (liftGdhAtomic gl (genSpkGdhActiveKB (Δ := Δ) kOn pa sm bSt x)).cost ≤ 200 * kOn + 30000 := by
  apply Nat.le_trans (liftGdhAtomic_cost_le_three_costUB gl
    (genSpkGdhActiveKB (Δ := Δ) kOn pa sm bSt x))
  simp only [genSpkGdhActiveKB, sbMk, buMk, stUpd, stMk, smUpd, smMk, nat2Eq, natEq,
    letV_costUB, bindV_costUB, caseOptV_costUB, eAny_costUB, eFind_costUB,
    gPrim_costUB, sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB,
    qSigSign_costUB, qKemKeyGen_costUB, encEC_costUB, encKEM_costUB,
    litB_costUB, u32OfNat_costUB, rNone_costUB, rBundle_costUB,
    paV_costUB, paSpkIdx_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
    v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  omega

theorem initiateGdh2ShadowB_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    (liftGdhAtomic gl (initiateGdh2ShadowB S f (Δ := Δ) pa sm bSt fgSh hasOpk x)).cost ≤
      1336 * f.kFg + 12000 * f.kOn + 7000 * min f.kOn S.N_dh +
        23000 * min f.kOn S.N_sess_tot + 55000 := by
  cases hasOpk <;> (
    apply Nat.le_trans
    · dsimp only [initiateGdh2ShadowB]; peel_atomic_cost
    · simp only [ephSidMatchesE, pa2U, pa2DhFlag, pa2EphTarget, initSidE,
        sidEq, eLet2, nat3Eq, nat2Eq, natEq, isSomeE, optFst, optSnd,
        buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
        peSecIKA0, peIkAPk, seSid, stSess, stPrin,
        seMk, seUpd, stUpd, stMk, smUpd, smMk,
        eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eAny_costUB, eFind_costUB,
        gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, qSigVerify_costUB, qKemEncaps_costUB,
        koskBundleOkPowsC_costUB, resolveSigPkC_costUB, lookupSpkSkC_costUB,
        computePosC_costUB, computeOptPosInitC_costUB,
        honestPeerC_costUB, checkProvC_costUB, chooseInitRandC_costUB, findHonestC_costUB,
        encEC_costUB, encKEM_costUB, litB_costUB,
        rNone_costUB, rHdr_costUB, rInitUnfresh_costUB,
        smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat,
        ↓reduceIte, Bool.false_eq_true]
      omega)

theorem initiateGdhShadowB_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    (liftGdhAtomic gl (initiateGdhShadowB S f (Δ := Δ) pa sm bSt fgSh hasOpk x)).cost ≤
      1336 * f.kFg + 12000 * f.kOn + 7000 * min f.kOn S.N_dh +
        27000 * min f.kOn S.N_sess_tot + 10 * bits S.N_dh + 55000 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have c3 := bits_mono (show S.N_send_opk.min S.N_send_opk_tot ≤ S.N_dh from
    le_trans (Nat.min_le_right _ _) (by omega))
  have c4 := bits_mono (show S.N_send_opk_tot ≤ S.N_dh by omega)
  have c5 := bits_mono (show S.N_send_no_opk.min S.N_send_no_opk_tot ≤ S.N_dh from
    le_trans (Nat.min_le_right _ _) (by omega))
  have c6 := bits_mono (show S.N_send_tot ≤ S.N_dh by omega)
  cases hasOpk <;> (
    apply Nat.le_trans
    · dsimp only [initiateGdhShadowB]; peel_atomic_cost
    · simp only [initSlotIdxE, initSidE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mulRight,
        sidEq, eLet2, nat3Eq, nat2Eq, natEq, isSomeE, optFst, optSnd,
        buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
        peSecIKA0, peIkAPk, seSid, stSess, stPrin,
        seMk, seUpd, stUpd, stMk, smUpd, smMk,
        eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eAny_costUB, eFind_costUB,
        gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, qSigVerify_costUB, qKemEncaps_costUB,
        koskBundleOkPowsC_costUB, resolveSigPkC_costUB, lookupSpkSkC_costUB,
        computePosC_costUB, computeOptPosInitC_costUB,
        honestPeerC_costUB, checkProvC_costUB, chooseInitRandC_costUB, findHonestC_costUB,
        encEC_costUB, encKEM_costUB, litB_costUB,
        rNone_costUB, rHdr_costUB, rInitUnfresh_costUB,
        paU_costUB, paDhFlag_costUB, paEphIdx_costUB,
        smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat,
        ↓reduceIte, Bool.false_eq_true]
      omega)

theorem initiateGdhActiveShadowInnerB_atomic_cost_le {ι : Type} {T : OracleSpec ι}
    {A : AtomicIface T} (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₆ fgSessCtrTy) (sendOpkCnt : Var Γ₅ .nat)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    (liftGdhAtomic gl (initiateGdhActiveShadowInnerB S f (Δ := Δ)
        pa sm bSt fgSh sendOpkCnt hasOpk x)).cost ≤
      1336 * f.kFg + 12000 * f.kOn + 7000 * min f.kOn S.N_dh +
        23000 * min f.kOn S.N_sess_tot + 55000 := by
  cases hasOpk <;> (
    apply Nat.le_trans
    · dsimp only [initiateGdhActiveShadowInnerB]; peel_atomic_cost
    · simp only [initSidE, sidEq, eLet2, nat3Eq, nat2Eq, natEq, isSomeE, optFst, optSnd,
        buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
        peSecIKA0, peIkAPk, seSid, stSess, stPrin,
        seMk, seUpd, stUpd, stMk, smUpd, smMk,
        eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eAny_costUB, eFind_costUB,
        gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, qSigVerify_costUB, qKemEncaps_costUB,
        koskBundleOkPowsC_costUB, resolveSigPkC_costUB, lookupSpkSkC_costUB,
        computePosC_costUB, computeOptPosInitC_costUB,
        honestPeerC_costUB, checkProvC_costUB, chooseInitRandC_costUB, findHonestC_costUB,
        encEC_costUB, encKEM_costUB, litB_costUB,
        rNone_costUB, rHdr_costUB, rInitUnfresh_costUB,
        paU_costUB, paDhFlag_costUB, paEphIdx_costUB, paOpkMode_costUB,
        smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_1,
        ↓reduceIte, Bool.false_eq_true]
      omega)

theorem acceptOpkGdhCoreShadowB_atomic_cost_le {ι : Type} {T : OracleSpec ι}
    {A : AtomicIface T} (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (opkModeB : Var Γ₁ .bool) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    (liftGdhAtomic gl (acceptOpkGdhCoreShadowB S f (Δ := Δ) opkModeB sm bSt fgSh x)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35000 := by
  apply Nat.le_trans
  · dsimp only [acceptOpkGdhCoreShadowB]; peel_atomic_cost
  · simp only [kyberCheckE, kyberEq, qKJO, optU32Eq, nonZero32, eLet2,
      nat3Eq, nat2Eq, natEq,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
      peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk, oeOpkSk, oeOpkPk, oeUpd, oeMk,
      stUsedO, stUsedN, stPrin, stSpks, stOpks, stKyb,
      qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
      eLet_costUB, eCaseOpt_costUB, eAny_costUB, eFind_costUB, eMap_costUB,
      gPrim_costUB, qIsCanonical_costUB, qX25519_costUB, qKemDecaps_costUB,
      koskSenderOkPowsC_costUB, computePosC_costUB, mkSecretPosC_costUB, finishAcceptGdhC_costUB,
      litB_costUB, lenB_costUB, eqB_costUB, u32OfNat_costUB, eqU32_costUB,
      rNone_costUB, smFgL_costUB, smPows_costUB,
      v_costUB, Comp.costUB, Expr.costUB, List.length_nil, List.length_replicate,
      PNat.val_ofNat, bits_32]
    omega

theorem acceptOpkGdhShadowB_atomic_cost_le {ι : Type} {T : OracleSpec ι}
    {A : AtomicIface T} (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    (liftGdhAtomic gl (acceptOpkGdhShadowB S f (Δ := Δ) pa sm bSt fgSh x)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35050 := by
  apply Nat.le_trans (le_atomic_letV gl _ _
    (acceptOpkGdhCoreShadowB_atomic_cost_le gl S f .zero sm bSt fgSh x))
  simp only [paOpkMode_costUB, v_costUB]; omega

theorem acceptOpkGdh2ShadowB_atomic_cost_le {ι : Type} {T : OracleSpec ι}
    {A : AtomicIface T} (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    (liftGdhAtomic gl (acceptOpkGdh2ShadowB S f (Δ := Δ) pa sm bSt fgSh x)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35050 := by
  apply Nat.le_trans (le_atomic_letV gl _ _
    (acceptOpkGdhCoreShadowB_atomic_cost_le gl S f .zero sm bSt fgSh x))
  simp only [pa2OpkMode, v_costUB, Expr.costUB]; omega

theorem acceptNoOpkGdhShadowB_atomic_cost_le {ι : Type} {T : OracleSpec ι}
    {A : AtomicIface T} (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    {Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    (liftGdhAtomic gl (acceptNoOpkGdhShadowB S f (Δ := Δ) sm bSt fgSh x)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35000 := by
  apply Nat.le_trans
  · dsimp only [acceptNoOpkGdhShadowB]; peel_atomic_cost
  · simp only [kyberCheckE, kyberEq, qKJO, optU32Eq, nonZero32, eLet2,
      nat3Eq, nat2Eq, natEq,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
      peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk,
      stUsedO, stUsedN, stPrin, stSpks, stOpks, stKyb,
      qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
      eLet_costUB, eCaseOpt_costUB, eAny_costUB, eFind_costUB,
      gPrim_costUB, qIsCanonical_costUB, qX25519_costUB, qKemDecaps_costUB,
      koskSenderOkPowsC_costUB, computePosC_costUB, finishAcceptGdhC_costUB,
      litB_costUB, lenB_costUB, eqB_costUB, u32OfNat_costUB, eqU32_costUB,
      rNone_costUB, smFgL_costUB, smPows_costUB,
      v_costUB, Comp.costUB, Expr.costUB, List.length_nil, List.length_replicate,
      PNat.val_ofNat, bits_32]
    omega

private theorem wrapBase2_costUB' {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, bindV_costUB, gPrim_costUB, smUpd, smMk,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

private theorem wrapSim2_costUB' {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := by
  simp only [wrapSim2, bindV_costUB, v_costUB, Comp.costUB, Expr.costUB]

private theorem liftKind0NoFgArm_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup)
    {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps pqGapDhIface [stTy, qPayTy] (.prod keyIndRespTy stTy)) :
    (liftKind0NoFgArm gl S payE arm).cost ≤ payE.cost + 3 * arm.costUB + 20 := by
  have hArm := liftGdhAtomic_cost_le_three_costUB gl arm
  simp only [liftKind0NoFgArm, runAt2_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem liftKind0SessArm_wrap_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup)
    {paTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy (.prod paTy simTy)) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (body : Var [paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] paTy →
      Var [simTy, paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] keyIndStateTy →
      Var [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] fgSessCtrTy →
      Var [.prod (.prod paTy simTy) fgSessCtrTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
          .prod (.prod paTy simTy) fgSessCtrTy, qPayTy]
        (.prod keyIndRespTy (.prod simTy fgSessCtrTy)))
    {Bb : ℕ}
    (hb : (liftGdhAtomic gl (body .zero .zero .zero .zero (.succ .zero))).cost ≤ Bb) :
    (liftKind0SessArm gl S payE (wrapSimSessArm body)).cost ≤ payE.cost + Bb + 130 := by
  have hWrap : (liftGdhAtomic gl (wrapSimSessArm body)).cost ≤ Bb + 85 := by
    apply Nat.le_trans
    · dsimp only [wrapSimSessArm]
      apply le_atomic_letV; apply le_atomic_letV; apply le_atomic_letV
      apply le_atomic_letV; apply le_atomic_letV
      refine le_atomic_bindV gl _ _ hb (Bk := 45) ?_
      rw [StdGdhLift.cost_eq_twoKey]
      simp only [liftGdhAtomic, gdhLift2Key, mapComp, mapExpr, v, Comp.cost, Expr.cost]
      omega
    · simp only [smBase_costUB, v_costUB, Expr.costUB]; omega
  simp only [liftKind0SessArm, runAt2_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

/-- Random-oracle `costAt` bound for tuple-keyed `gdhShadowHandle2Atomic`. -/
theorem gdhShadowHandle2Atomic_costAt_ro_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    (st : gdhShadowState2AtomicTy.denote) (sec : List UInt8) :
    (gdhShadowHandle2Atomic gl S f).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc (.roQuery sec)) .nil)) ≤
      4420 * bits f.kAvl + 1345 * f.kOn + 8650 := by
  have hRo := liftKind1RoArm_cost_le gl S f (paTy := params2Ty)
  dsimp only [gdhShadowHandle2Atomic]
  refine Nat.le_trans (dispatchKeyIndQ_ro_costAt_le S st sec
    _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  omega

/-- Random-oracle `costAt` bound for stage-1 `gdhShadowHandleAtomic`. -/
theorem gdhShadowHandleAtomic_costAt_ro_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    (st : gdhShadowStateAtomicTy.denote) (sec : List UInt8) :
    (gdhShadowHandleAtomic gl S f).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc (.roQuery sec)) .nil)) ≤
      4420 * bits f.kAvl + 1345 * f.kOn + 8650 := by
  have hRo := liftKind1RoArm_cost_le gl S f (paTy := paramsTy)
  dsimp only [gdhShadowHandleAtomic]
  refine Nat.le_trans (dispatchKeyIndQ_ro_costAt_le S st sec
    _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  omega

private theorem payExprs_cost_le (S : Setup) {A : Ty pqAtomicSig} (N_s N_o : ℕ) :
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

private theorem sharedNoFgArms_costUB_le {paTy : PT} (K : ℕ) :
    (corruptB (Δ := [keyIndStateTy, simTy, paTy, .prod paTy simTy, .nat]) K
      (Var.zero : Var [keyIndStateTy, simTy, paTy, .prod paTy simTy, .nat] _)
      (Var.succ Var.zero : Var [.prod paTy simTy, .nat] _)).costUB ≤ 3900 * K + 17000 ∧
    (testB (Δ := [keyIndStateTy, simTy, paTy, .prod paTy simTy, _root_.SignalPqxdh.LegacyCosted.sidT]) K
      (Var.zero : Var [keyIndStateTy, simTy, paTy, .prod paTy simTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)
      (Var.succ Var.zero : Var [.prod paTy simTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)).costUB ≤
      3900 * K + 17000 ∧
    (revealB (Δ := [keyIndStateTy, simTy, paTy, .prod paTy simTy, _root_.SignalPqxdh.LegacyCosted.sidT]) K
      (Var.zero : Var [keyIndStateTy, simTy, paTy, .prod paTy simTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)
      (Var.succ Var.zero : Var [.prod paTy simTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)).costUB ≤
      3900 * K + 17000 ∧
    (registerGdhB (Δ := [keyIndStateTy, simTy, paTy, .prod paTy simTy, B 32])
      (Var.zero : Var [simTy, paTy, .prod paTy simTy, B 32] simTy)
      (Var.zero : Var [keyIndStateTy, simTy, paTy, .prod paTy simTy, B 32] _)
      (Var.succ Var.zero : Var [.prod paTy simTy, B 32] _)).costUB ≤ 3900 * K + 17000 ∧
    (revealSpkB (Δ := [keyIndStateTy, simTy, paTy, .prod paTy simTy, .prod .nat .nat]) K
      (Var.zero : Var [keyIndStateTy, simTy, paTy, .prod paTy simTy, .prod .nat .nat] _)
      (Var.succ Var.zero : Var [.prod paTy simTy, .prod .nat .nat] _)).costUB ≤
      3900 * K + 17000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [corruptB, rs, peUpd, peMk, stUpd, stMk, rNone_costUB, rCorr_costUB,
      caseOptV_costUB, eFind_costUB, eMap_costUB, natEq, v_costUB, Comp.costUB, Expr.costUB]; omega
  · simp only [testB, freshE, rs, seUpd, seMk, reUpd, reMk, stUpd, stMk, rNone_costUB, rDrKey_costUB,
      caseOptV_costUB, eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eMap_costUB,
      sidEq, eLet2, nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]; omega
  · simp only [revealB, rs, seUpd, seMk, reUpd, reMk, stUpd, stMk, rNone_costUB, rDrKey_costUB,
      caseOptV_costUB, eLet_costUB, eCaseSum_costUB, eFind_costUB, eMap_costUB,
      sidEq, eLet2, nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]; omega
  · simp only [registerGdhB, stUpd, stMk, smUpd, smMk,
      smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, rNone_costUB, rPk_costUB,
      bindV_costUB, gPrim_costUB, qX25519Base_costUB, qPow8_costUB, lenB_costUB,
      natEq, v_costUB, Comp.costUB, Expr.costUB, PNat.val_ofNat, bits_32]; omega
  · simp only [revealSpkB, rs, sbUpd, sbMk, stUpd, stMk, rNone_costUB, rSpkSk_costUB,
      caseOptV_costUB, eFind_costUB, eMap_costUB, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]
    omega

/-- Online-query `costAt` bound for tuple-keyed `gdhShadowHandle2Atomic`. -/
theorem gdhShadowHandle2Atomic_costAt_online_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    (st : gdhShadowState2AtomicTy.denote) (q : KeyIndQuery S)
    (hq : keyIndQueryKind q = ⟨0, by decide⟩) :
    (gdhShadowHandle2Atomic gl S f).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc q) .nil)) +
      (pqKeyIndCodec S).codecCost ≤
      1336 * f.kFg + 12500 * f.kOn + 25500 * min f.kOn S.N_dh +
        23500 * min f.kOn S.N_sess_tot + 56000 := by
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  rcases sharedNoFgArms_costUB_le (paTy := params2Ty) f.kOn with ⟨hCor, hTst, hRev, hReg, hRSpk⟩
  rcases payExprs_cost_le S (A := gdhShadowState2AtomicTy) S.N_send_opk S.N_opk with
    ⟨hP1, hPP, hPT, hPS, hPI1, hPA1, hPV0⟩
  rcases payExprs_cost_le S (A := gdhShadowState2AtomicTy) S.N_send_no_opk S.N_no_opk with
    ⟨_, _, _, _, hPI2, hPA2, _⟩
  have hS5 := liftKind0SessArm_wrap_cost_le gl S (initPayToNatE S.N_send_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdh2ShadowB S f pa sm bSt fgSh true x)
    (initiateGdh2ShadowB_atomic_cost_le gl S f .zero .zero .zero .zero true (.succ .zero))
  have hS6 := liftKind0SessArm_wrap_cost_le gl S (initPayToNatE S.N_send_no_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdh2ShadowB S f pa sm bSt fgSh false x)
    (initiateGdh2ShadowB_atomic_cost_le gl S f .zero .zero .zero .zero false (.succ .zero))
  have hS7 := liftKind0SessArm_wrap_cost_le gl S (accPayToNatE S.N_opk S .v0)
    (fun pa sm bSt fgSh x => acceptOpkGdh2ShadowB S f pa sm bSt fgSh x)
    (acceptOpkGdh2ShadowB_atomic_cost_le gl S f .zero .zero .zero .zero (.succ .zero))
  have hS8 := liftKind0SessArm_wrap_cost_le gl S (paTy := params2Ty) (accPayToNatE S.N_no_opk S .v0)
    (fun _ sm bSt fgSh x => acceptNoOpkGdhShadowB S f sm bSt fgSh x)
    (acceptNoOpkGdhShadowB_atomic_cost_le gl S f .zero .zero .zero (.succ .zero))
  let B := 1336 * f.kFg + 12500 * f.kOn + 25500 * min f.kOn S.N_dh +
    23500 * min f.kOn S.N_sess_tot + 55900
  have hNoFg : ∀ {qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
      (payE : Expr pqAtomicOps (PayAtomic :: [gdhShadowState2AtomicTy, (pqKeyIndCodec S).Q])
        (embedTy qPayTy))
      (arm : Comp pqxdhOps pqGapDhIface [gdhState2Ty, qPayTy] (.prod keyIndRespTy gdhState2Ty)),
      payE.cost ≤ 60 → arm.costUB ≤ 4000 * f.kOn + 18000 →
      (liftKind0NoFgArm gl S payE arm).cost ≤ B := by
    intro _ _ payE arm hp ha; have hL := liftKind0NoFgArm_cost_le gl S payE arm; dsimp only [B]; omega
  dsimp only [gdhShadowHandle2Atomic]
  refine Nat.le_trans (Nat.add_le_add_right (dispatchKeyIndQ_online_costAt_le S B st q hq
    _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hNoFg _ _ hP1 (by
      simp only [wrapNoFgArm, wrapSim2_costUB', initPrinGdh2B, peMk, stUpd, stMk, smUpd, smMk,
        pa2PrinTarget, pa2Up, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        rNone_costUB, rInitPrin_costUB, letV_costUB, bindV_costUB, eCaseOpt_costUB, eAny_costUB,
        gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, qSigPkGen_costUB, litB_costUB,
        natEq, v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]; omega))
    (hNoFg _ _ hP1 (by simp only [wrapNoFgArm, wrapBase2_costUB', smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (hNoFg _ _ hPP (by
      simp only [wrapNoFgArm, wrapSim2_costUB', genSpkGdh2B, sbMk, buMk, stUpd, stMk, smUpd, smMk,
        pa2SpkTarget, pa2V, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        rNone_costUB, rBundle_costUB, letV_costUB, bindV_costUB, caseOptV_costUB,
        eCaseOpt_costUB, eAny_costUB, eFind_costUB, gPrim_costUB,
        sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB, qSigSign_costUB, qKemKeyGen_costUB,
        encEC_costUB, encKEM_costUB, u32OfNat_costUB, litB_costUB,
        nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]; omega))
    (hNoFg _ _ hPT (by
      simp only [wrapNoFgArm, wrapSim2_costUB', genOpkGdh2B, oeMk, stUpd, stMk, smUpd, smMk,
        pa2OpkMode, pa2OpkTarget, pa2V, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB,
        smPows_costUB, rNone_costUB, rPk_costUB, letV_costUB, bindV_costUB,
        eCaseOpt_costUB, eAny_costUB, gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, litB_costUB,
        nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
      omega))
    (Nat.le_trans hS5 (by dsimp only [B]; omega))
    (Nat.le_trans hS6 (by dsimp only [B]; omega))
    (Nat.le_trans hS7 (by dsimp only [B]; omega))
    (Nat.le_trans hS8 (by dsimp only [B]; omega))
    (hNoFg _ _ hPS (by simp only [wrapNoFgArm, wrapBase2_costUB', smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (by simp only [atomicRNoneE, Comp.cost, Expr.cost, Expr.v1, B]; omega)
    (hNoFg _ _ hPS (by simp only [wrapNoFgArm, wrapBase2_costUB', smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (hNoFg _ _ hPV0 (by simp only [wrapNoFgArm, wrapSim2_costUB', smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (hNoFg _ _ hPP (by simp only [wrapNoFgArm, wrapBase2_costUB', smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))) _) ?_
  dsimp only [B]; omega

/-- Online-query `costAt` bound for stage-1 `gdhShadowHandleAtomic`. -/
theorem gdhShadowHandleAtomic_costAt_online_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels)
    (st : gdhShadowStateAtomicTy.denote) (q : KeyIndQuery S)
    (hq : keyIndQueryKind q = ⟨0, by decide⟩) :
    (gdhShadowHandleAtomic gl S f).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc q) .nil)) +
      (pqKeyIndCodec S).codecCost ≤
      1336 * f.kFg + 12500 * f.kOn + 25500 * min f.kOn S.N_dh +
        27500 * min f.kOn S.N_sess_tot + 10 * bits S.N_dh + 56000 := by
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have cSpk := bits_mono (show S.N_recv.min S.N_spk_tot ≤ S.N_dh from
    le_trans (Nat.min_le_right _ _) (by omega))
  have cOpk := bits_mono (show S.N_opk.min S.N_opk_tot ≤ S.N_dh from
    le_trans (Nat.min_le_right _ _) (by omega))
  rcases sharedNoFgArms_costUB_le (paTy := paramsTy) f.kOn with ⟨hCor, hTst, hRev, hReg, hRSpk⟩
  rcases payExprs_cost_le S (A := gdhShadowStateAtomicTy) S.N_send_opk S.N_opk with
    ⟨hP1, hPP, hPT, hPS, hPI1, hPA1, hPV0⟩
  rcases payExprs_cost_le S (A := gdhShadowStateAtomicTy) S.N_send_no_opk S.N_no_opk with
    ⟨_, _, _, _, hPI2, hPA2, _⟩
  have hS5 := liftKind0SessArm_wrap_cost_le gl S (initPayToNatE S.N_send_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdhShadowB S f pa sm bSt fgSh true x)
    (initiateGdhShadowB_atomic_cost_le gl S f .zero .zero .zero .zero true (.succ .zero))
  have hS6 := liftKind0SessArm_wrap_cost_le gl S (initPayToNatE S.N_send_no_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdhShadowB S f pa sm bSt fgSh false x)
    (initiateGdhShadowB_atomic_cost_le gl S f .zero .zero .zero .zero false (.succ .zero))
  have hS7 := liftKind0SessArm_wrap_cost_le gl S (accPayToNatE S.N_opk S .v0)
    (fun pa sm bSt fgSh x => acceptOpkGdhShadowB S f pa sm bSt fgSh x)
    (acceptOpkGdhShadowB_atomic_cost_le gl S f .zero .zero .zero .zero (.succ .zero))
  have hS8 := liftKind0SessArm_wrap_cost_le gl S (paTy := paramsTy) (accPayToNatE S.N_no_opk S .v0)
    (fun _ sm bSt fgSh x => acceptNoOpkGdhShadowB S f sm bSt fgSh x)
    (acceptNoOpkGdhShadowB_atomic_cost_le gl S f .zero .zero .zero (.succ .zero))
  let B := 1336 * f.kFg + 12500 * f.kOn + 25500 * min f.kOn S.N_dh +
    27500 * min f.kOn S.N_sess_tot + 10 * bits S.N_dh + 55900
  have hNoFg : ∀ {qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
      (payE : Expr pqAtomicOps (PayAtomic :: [gdhShadowStateAtomicTy, (pqKeyIndCodec S).Q])
        (embedTy qPayTy))
      (arm : Comp pqxdhOps pqGapDhIface [gdhStateTy, qPayTy] (.prod keyIndRespTy gdhStateTy)),
      payE.cost ≤ 60 → arm.costUB ≤ 4000 * f.kOn + 3 * bits S.N_dh + 18000 →
      (liftKind0NoFgArm gl S payE arm).cost ≤ B := by
    intro _ _ payE arm hp ha; have hL := liftKind0NoFgArm_cost_le gl S payE arm; dsimp only [B]; omega
  dsimp only [gdhShadowHandleAtomic]
  refine Nat.le_trans (Nat.add_le_add_right (dispatchKeyIndQ_online_costAt_le S B st q hq
    _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hNoFg _ _ hP1 (by
      simp only [wrapNoFgArm, wrapSim_costUB, initPrinGdhB, peMk, stUpd, stMk, smUpd, smMk,
        paPrinFlag_costUB, paPrinIdx_costUB, paUp_costUB,
        smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        rNone_costUB, rInitPrin_costUB, letV_costUB, bindV_costUB, eAny_costUB,
        gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, qSigPkGen_costUB, litB_costUB,
        natEq, v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]; omega))
    (hNoFg _ _ hP1 (by simp only [wrapNoFgArm, wrapBase_costUB, smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (hNoFg _ _ hPP (by
      simp only [wrapNoFgArm, wrapSim_costUB, genSpkGdhB, spkFlatIdxE, mulRight,
        sbMk, buMk, stUpd, stMk, smUpd, smMk, paSpkIdx_costUB, paV_costUB,
        smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        rNone_costUB, rBundle_costUB, letV_costUB, bindV_costUB, caseOptV_costUB,
        eAny_costUB, eFind_costUB, gPrim_costUB,
        sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB, qSigSign_costUB, qKemKeyGen_costUB,
        encEC_costUB, encKEM_costUB, u32OfNat_costUB, litB_costUB,
        nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]; omega))
    (hNoFg _ _ hPT (by
      simp only [wrapNoFgArm, wrapSim_costUB, genOpkGdhB, opkFlatIdxE, spkFlatIdxE, mulRight,
        oeMk, stUpd, stMk, smUpd, smMk, paOpkMode_costUB, paOpkIdx_costUB, paV_costUB,
        smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB,
        smPows_costUB, rNone_costUB, rPk_costUB, letV_costUB, bindV_costUB,
        eAny_costUB, gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, litB_costUB,
        nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
      omega))
    (Nat.le_trans hS5 (by dsimp only [B]; omega))
    (Nat.le_trans hS6 (by dsimp only [B]; omega))
    (Nat.le_trans hS7 (by dsimp only [B]; omega))
    (Nat.le_trans hS8 (by dsimp only [B]; omega))
    (hNoFg _ _ hPS (by simp only [wrapNoFgArm, wrapBase_costUB, smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (by simp only [atomicRNoneE, Comp.cost, Expr.cost, Expr.v1, B]; omega)
    (hNoFg _ _ hPS (by simp only [wrapNoFgArm, wrapBase_costUB, smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (hNoFg _ _ hPV0 (by simp only [wrapNoFgArm, wrapSim_costUB, smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))
    (hNoFg _ _ hPP (by simp only [wrapNoFgArm, wrapBase_costUB, smBase_costUB, letV_costUB, v_costUB, Expr.costUB]; omega))) _) ?_
  dsimp only [B]; omega

private theorem logFind2C_costUB' (K off : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) :
    (logFind2C (Δ := Δ) K off pa sm).costUB = K * (bits off + 526) + 77 := by
  simp only [logFind2C, slice32_costUB, smLog_costUB, pa2U, pa2V,
    bindV_costUB, findMV_costUB, eMap_costUB, eCaseOpt_costUB, ddhQ_costUB, litB_costUB,
    v_costUB, Comp.costUB, Expr.costUB, List.length_replicate, PNat.val_ofNat]
  ring

private theorem findMapStep2C_costUB' {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (acc : Var Γ₂ (.opt (B 32)))
    (cand : Comp pqxdhOps pqGapDhIface Δ (B 32)) :
    (findMapStep2C pa acc cand).costUB = cand.costUB + 117 := by
  simp only [findMapStep2C, caseOptV_costUB, bindV_costUB, ddhQ_costUB,
    pa2U, pa2V, v_costUB, Comp.costUB, Expr.costUB]
  ring

theorem gdhFinishK_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels) :
    (liftGdhAtomic gl (gdhFinishK S f)).cost ≤
      207 * (min f.kOn S.N_dh) ^ 2 + 207 * f.kOn * min f.kOn S.N_dh +
        198 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        1269 * min f.kOn S.N_dh + 789 * min f.kOn S.N_sess_tot + 6396 * f.kOff + 1230 := by
  have h3 := liftGdhAtomic_cost_le_three_costUB gl (gdhFinishK S f)
  have hUB : (gdhFinishK S f).costUB =
      69 * (min f.kOn S.N_dh) ^ 2 + 69 * f.kOn * min f.kOn S.N_dh +
        66 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        423 * min f.kOn S.N_dh + 263 * min f.kOn S.N_sess_tot + 2132 * f.kOff + 409 := by
    simp only [gdhFinishK, extractMode0KC, logFindC_costUB, spkPowsC_costUB, findMapStepC_costUB,
      initDh1CandC_costUB, respDh1CandC_costUB, slice32_costUB,
      smBase_costUB, smLog_costUB, smPows_costUB, paU_costUB, paV_costUB, paMode_costUB, natEq,
      letV_costUB, bindV_costUB, caseOptV_costUB, findMV_costUB, foldMV_costUB,
      eCaseOpt_costUB, eMap_costUB, ddhQ_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
      List.length_replicate, PNat.val_ofNat, bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
    ring
  have h3' : 3 * (gdhFinishK S f).costUB =
      207 * (min f.kOn S.N_dh) ^ 2 + 207 * f.kOn * min f.kOn S.N_dh +
        198 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        1269 * min f.kOn S.N_dh + 789 * min f.kOn S.N_sess_tot + 6396 * f.kOff + 1227 := by
    rw [hUB]; ring
  omega

theorem gdhFinish2K_atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels) :
    (liftGdhAtomic gl (gdhFinish2K S f)).cost ≤
      207 * (min f.kOn S.N_dh) ^ 2 + 207 * f.kOn * min f.kOn S.N_dh +
        198 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        1269 * min f.kOn S.N_dh + 789 * min f.kOn S.N_sess_tot + 6396 * f.kOff + 1230 := by
  have h3 := liftGdhAtomic_cost_le_three_costUB gl (gdhFinish2K S f)
  have hUB : (gdhFinish2K S f).costUB =
      69 * (min f.kOn S.N_dh) ^ 2 + 69 * f.kOn * min f.kOn S.N_dh +
        66 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        423 * min f.kOn S.N_dh + 263 * min f.kOn S.N_sess_tot + 2132 * f.kOff + 406 := by
    simp only [gdhFinish2K, extractMode0_2KC, logFind2C_costUB', spkPowsC_costUB, findMapStep2C_costUB',
      initDh1CandC_costUB, respDh1CandC_costUB, slice32_costUB,
      smBase_costUB, smLog_costUB, smPows_costUB, pa2U, pa2V, pa2Mode, natEq,
      letV_costUB, bindV_costUB, caseOptV_costUB, findMV_costUB, foldMV_costUB,
      eCaseOpt_costUB, eMap_costUB, ddhQ_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
      List.length_replicate, PNat.val_ofNat, bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
    ring
  have h3' : 3 * (gdhFinish2K S f).costUB =
      207 * (min f.kOn S.N_dh) ^ 2 + 207 * f.kOn * min f.kOn S.N_dh +
        198 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        1269 * min f.kOn S.N_dh + 789 * min f.kOn S.N_sess_tot + 6396 * f.kOff + 1218 := by
    rw [hUB]; ring
  omega

/-- Syntactic `Comp.cost` bound for stage-1 `gdhShadowFinishAtomic`. -/
theorem gdhShadowFinishAtomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels) :
    (gdhShadowFinishAtomic gl S f).cost ≤
      207 * (min f.kOn S.N_dh) ^ 2 + 207 * f.kOn * min f.kOn S.N_dh +
        198 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        1269 * min f.kOn S.N_dh + 789 * min f.kOn S.N_sess_tot + 6396 * f.kOff + 1245 := by
  have hF := gdhFinishK_atomic_cost_le gl S f
  simp only [gdhShadowFinishAtomic, runAt2_cost, Expr.cost, Expr.v0, Expr.v1]
  omega

/-- Syntactic `Comp.cost` bound for tuple-keyed `gdhShadowFinish2Atomic`. -/
theorem gdhShadowFinish2Atomic_cost_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) [StdGdhLift gl] (S : Setup) (f : KeyIndKFuels) :
    (gdhShadowFinish2Atomic gl S f).cost ≤
      207 * (min f.kOn S.N_dh) ^ 2 + 207 * f.kOn * min f.kOn S.N_dh +
        198 * min f.kOn S.N_dh * min f.kOn S.N_sess_tot +
        1269 * min f.kOn S.N_dh + 789 * min f.kOn S.N_sess_tot + 6396 * f.kOff + 1245 := by
  have hF := gdhFinish2K_atomic_cost_le gl S f
  simp only [gdhShadowFinish2Atomic, runAt2_cost, Expr.cost, Expr.v0, Expr.v1]
  omega

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost
