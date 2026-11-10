/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.SignalPqxdh.AtomicLift
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigWire
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost
import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem

/-!
# Size and Step-Cost Helpers for `sigKeyInd1KeyKindAtomicProg`

Establishes AST size bounds and per-arm static step-cost bounds for
`sigKeyInd1KeyKindAtomicProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBoundsCost

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
  bindV_costUB sIndex_costUB sBool_costUB v_costUB)
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

section SizeBounds

open _root_.SignalPqxdh.LegacyCosted (ChallengerOracle U32)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  letV_size bindV_size caseOptV_size caseSumV_size findMV_size anyMV_size
  eLet_size eCaseOpt_size eCaseSum_size eFind_size eAny_size eMap_size
  liftBase_size gPrim_size litB_size takeKB_size dropB_size lenB_size eqB_size u32OfNat_size eqU32_size
  encEC_size encKEM_size ddhQ_size v_size
  sIndex_size sBool_size sBytes32_size sRandom64_size sDrKey96_size
  qX25519_size qX25519Base_size qIsCanonical_size qPow8_size
  qSigPkGen_size qSigSign_size qSigVerify_size
  qKemKeyGen_size qKemEncaps_size qKemDecaps_size)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (
  bits_64 bits_96 bits_128 bits_160 bits_192)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  bits_32
  partnerC chooseRespRandC chooseInitRandC entryMatchesC ddhEqC ddhEqOptC
  mkSecretPosC mkPairPosC computePosC computeOptPosInitC
  findHonestC isGameSpkC isGameOpkC koskSenderOkPowsC koskBundleOkPowsC
  lookupSpkSkC resolveSigPkC honestPeerC checkProvC
  keyIndSessionEntryTy keyIndRespEntryTy principalEntryTy spkBundleEntryTy opkEntryTy
  pa2U pa2V pa2Up pa2PrinTarget pa2DhFlag pa2EphTarget pa2SpkTarget pa2OpkMode pa2OpkTarget pa2Mode
  ephSidMatchesE isAdvPowsE smFgL smRaw smLog smPows
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stRo stAdv stSecb
  peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted peMk peUpd
  sbSpkSk sbSpkPk sbSpkSig sbPqspkSk sbPqspkPk sbPqspkSig sbRevealed sbMk sbUpd
  buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig buMk
  oeOpkSk oeOpkPk oeConsumed oeMk oeUpd
  seSid seHdr sePeerSpk seTested seRevealed seMk seUpd
  reSid reHdr reMk reUpd hdMk
  hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt
  qKJO qK qJ qO qHdr rs slice32 freshE
  rPk rCorr rBundle rHdr rInitPrin rInitUnfresh rDrKey rAccFresh rSpkSk
  initSidE natEq nat2Eq nat3Eq sidEq kyberEq kyberCheckE
  optU32Eq optBytesEq getDBytes optFst optSnd nonZero32 orE eLet eLet2 eCaseSum
  fePos1 fePos2 fePos3 fePos4 feSs feDk feMk
  encEC encKEM widenEC qSigDdhSign ddhQ sIndex sBool
  takeKB dropB lenB eqB u32OfNat eqU32 consB widenB catB)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  exprRename_size compRename_size mapExpr_size finSidToNatExpr
  pqxdhOps_opSize bits_le_bits_stepCostBudget)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  finPairToNatE finTripleToNatE initPayToNatE accPayToNatE ren1)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlHeightCap aop)
open _root_.ReductionDsl (atomicPureOps AtomicPureOp)

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.pqSamplers

@[local simp] private theorem sz_liftBase {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.size]

@[local simp] private theorem sz_s1Prim {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (s1Prim c).size = c.size := sz_liftBase c

@[local simp] private theorem sz_liftGdhToSigDdh {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).size = c.size := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.size]

@[local simp] private theorem sz_liftGdhComp {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhComp c).size = c.size := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.size]

@[local simp] private theorem lit_liftBase {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c) =
      compLitSize c := by
  induction c <;> simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, compLitSize]

@[local simp] private theorem lit_s1Prim {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    compLitSize (s1Prim c) = compLitSize c := lit_liftBase c

@[local simp] private theorem lit_gPrim {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim c) = compLitSize c :=
  lit_liftBase c

@[local simp] private theorem lit_liftGdhToSigDdh {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    compLitSize (liftGdhToSigDdh c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, compLitSize]

@[local simp] private theorem lit_liftGdhComp {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    compLitSize (liftGdhComp c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, compLitSize]

@[local simp] private theorem sz_F_X25519_length :
    _root_.SignalPqxdh.F_X25519.length = 32 := by decide

private theorem dispatchKeyIndQ_size_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} (S : Setup) {Γ : List (Ty pqAtomicSig)} {τ : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q))
    (c1 : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) τ)
    (c2 : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) τ)
    (c3 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) τ)
    (c4 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: Γ) τ)
    (c5 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_opk))
          (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) τ)
    (c6 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_no_opk))
          (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) τ)
    (c7 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_opk))
            (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) τ)
    (c8 : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_no_opk))
            (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) τ)
    (c9 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) τ)
    (c10 : Comp pqAtomicOps I (_root_.SignalPqxdh.Costed.PB 192 :: Γ) τ)
    (c11 : Comp pqAtomicOps I (.unit :: Γ) τ)
    (c12 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) τ)
    (c13 : Comp pqAtomicOps I (_root_.SignalPqxdh.Costed.PB 32 :: Γ) τ)
    (c14 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) τ) :
    (dispatchKeyIndQ S qE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14).size =
      qE.size + 25 + c1.size + c2.size + c3.size + c4.size + c5.size + c6.size + c7.size +
        c8.size + c9.size + c10.size + c11.size + c12.size + c13.size + c14.size := by
  simp only [dispatchKeyIndQ, Comp.size, compRename_size, Expr.size, Expr.v0]
  omega

private theorem liftSigDdhNoFgArm_size_le (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy)) :
    (liftSigDdhNoFgArm S payE arm).size ≤
      payE.size + 10 * arm.size + compLitSize arm + 20 := by
  have hMap := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe arm
  unfold liftSigDdhNoFgArm runAt2
  simp only [Comp.size, compRename_size, exprRename_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem liftSigDdhSessArm_size_le (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy)
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgShadowAtomicTy,
        (pqKeyIndCodec S).Q]) (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [.prod stTy Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy))) :
    (liftSigDdhSessArm S payE arm).size ≤
      payE.size + 10 * arm.size + compLitSize arm + 40 := by
  have hMap := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe arm
  unfold liftSigDdhSessArm runAt2
  simp only [Comp.size, compRename_size, exprRename_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

set_option linter.unusedSimpArgs false in
private theorem roParsedPrePos_size_lit_le :
    10 * (gdhLift1Key.liftI (roParsedPrePos160C
      (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).size +
      compLitSize (gdhLift1Key.liftI (roParsedPrePos160C
        (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)) ≤ 2000 ∧
    10 * (gdhLift1Key.liftI (roParsedPrePos192C
      (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)).size +
      compLitSize (gdhLift1Key.liftI (roParsedPrePos192C
        (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero)) ≤ 2500 := by
  dsimp [gdhLift1Key]
  constructor
  · rw [sz_liftGdhComp, lit_liftGdhComp]
    simp only [roParsedPrePos160C, mkSecretPosC, slice32,
      letV_size, bindV_size, liftBase_size, gPrim_size, takeKB_size, dropB_size,
      qPow8_size, qIsCanonical_size, v_size, Comp.size, Expr.size]
    simp only [letV, bindV, lit_liftBase, lit_gPrim, takeKB, dropB,
      qPow8, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qIsCanonical, v,
      bits_32, bits_64, bits_96, bits_128, bits_160,
      compLitSize, exprLitSize, pqOpLitSize]
    omega
  · rw [sz_liftGdhComp, lit_liftGdhComp]
    simp only [roParsedPrePos192C, mkSecretPosC, slice32,
      letV_size, bindV_size, liftBase_size, gPrim_size, takeKB_size, dropB_size,
      qPow8_size, qIsCanonical_size, v_size, Comp.size, Expr.size]
    simp only [letV, bindV, lit_liftBase, lit_gPrim, takeKB, dropB,
      qPow8, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qIsCanonical, v,
      bits_32, bits_64, bits_96, bits_128, bits_160,
      compLitSize, exprLitSize, pqOpLitSize]
    omega

set_option linter.unusedSimpArgs false in
private theorem fgSessScanPackC_size_lit_le (kOn : Nat) :
    10 * (gdhLift1Key.liftI (fgSessScanPackC kOn)).size +
      compLitSize (gdhLift1Key.liftI (fgSessScanPackC kOn)) ≤ 20 * bits kOn + 6000 := by
  dsimp [gdhLift1Key]
  rw [sz_liftGdhComp, lit_liftGdhComp]
  simp only [fgSessScanPackC,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessScanC,
    sessScanMinPredC, entryMatchesC, ddhEqOptC, ddhEqC,
    fePos1, fePos2, fePos3, fePos4, feSs, feDk, orE,
    letV_size, bindV_size, findMV_size, caseOptV_size, caseSumV_size,
    ddhQ_size, eqB_size, v_size, Comp.size, Expr.size]
  simp only [letV, bindV, findMV, caseOptV, caseSumV, ddhQ, eqB, v,
    compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
  omega

private theorem sampleDrKey96LiftC_size_le {Γ : List (Ty pqAtomicSig)} :
    (sampleDrKey96LiftC gdhLift1Key (Γ := Γ)).size ≤ 30 := by
  unfold sampleDrKey96LiftC
  rw [compRename_size]
  exact le_trans (mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe _) (by decide)

set_option linter.unusedSimpArgs false in
private theorem sigKindRoArm_size_le (S : Setup) (f : KeyIndKFuels) :
    (sigKindRoArm S f).size ≤
      8 * bits (avlHeightCap f.kAvl) + 40 * bits f.kOn + 35000 := by
  have hS1 := avlSearchB192C_size_le (I := pqSigAndDdhIface) f.kAvl
    (Γ := [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.simShadowAtomicTy,
           _root_.SignalPqxdh.Costed.PB 192])
    (V := _root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty))
    (.snd (.snd (.snd (.snd .v0)))) (aop (.pbytesToBytes 192) .v1)
  have hI1 := avlInsertAtPathC_size_le (I := pqSigAndDdhIface) f.kAvl
    (Γ := _root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty) ::
          Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlSearchResTy
            (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)) ::
          [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.simShadowAtomicTy,
           _root_.SignalPqxdh.Costed.PB 192])
    (.snd (.snd (.snd (.snd .v2)))) (.snd .v1) (aop (.pbytesToBytes 192) .v3) .v0
  have hS2 := avlSearchB192C_size_le (I := pqSigAndDdhIface) f.kAvl
    (Γ := [embedTy Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.roPosPackTy,
           Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.simShadowAtomicTy,
           _root_.SignalPqxdh.Costed.PB 192])
    (V := .prod (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)) .nat)
    (.fst (.snd (.snd (.snd .v1)))) (aop (.pbytesToBytes 192) .v2)
  have hI2 := avlInsertAtPathC_size_le (I := pqSigAndDdhIface) f.kAvl
    (Γ := _root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty) ::
          .opt (embedTy seqFgEntryTy) ::
          Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlSearchResTy
            (.prod (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)) .nat) ::
          [embedTy Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.roPosPackTy,
           Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.simShadowAtomicTy,
           _root_.SignalPqxdh.Costed.PB 192])
    (.fst (.snd (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))
    (.snd .v2)
    (aop (.pbytesToBytes 192) (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (.pair .v0 (.fst (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))
  have hM160 := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe
    (gdhLift1Key.liftI (roParsedPrePos160C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero))
  have hM192 := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe
    (gdhLift1Key.liftI (roParsedPrePos192C (Γ := [_root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [_root_.SignalPqxdh.LegacyCosted.B 192]) .zero))
  have hMScan := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe
    (gdhLift1Key.liftI (fgSessScanPackC f.kOn))
  have ⟨hPre160, hPre192⟩ := roParsedPrePos_size_lit_le
  have hScan := fgSessScanPackC_size_lit_le f.kOn
  have hSmp1 := sampleDrKey96LiftC_size_le
    (Γ := Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlSearchResTy
      (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)) ::
      [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.simShadowAtomicTy,
       _root_.SignalPqxdh.Costed.PB 192])
  have hSmp2 := sampleDrKey96LiftC_size_le
    (Γ := .opt (embedTy seqFgEntryTy) ::
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlSearchResTy
        (.prod (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)) .nat) ::
      [embedTy Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.roPosPackTy,
       Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.simShadowAtomicTy,
       _root_.SignalPqxdh.Costed.PB 192])
  unfold sigKindRoArm roParsedShadowAtomicC roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC
  simp only [sigHasForgeryAtomicE, sigGetFgAtomicE, sigSetFgAtomicE, atomicRNoneE,
    runAt1, runAt2, runAt3, runAt4, liftGdhAtomic,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.roNotPrefixE,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.roLenEqE,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.seqFgEntryDkE,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.roHitRespSimE,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.rawMissRespSimE,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.parsedMissRespSimE,
    isSomeE, s1Forgery, saInner, saTP, s1Fg, s1Upd, s1Mk, s1Target, s1Pk, s1Budget, s1Base,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd, feMk, feDk, rDrKey, natEq,
    compRename_size, exprRename_size, mapExpr_size,
    takeKB_size, lenB_size, eqB_size, litB_size, v_size,
    Comp.size, Expr.size, aop,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    bits_0, bits_1, bits_160, bits_192] at hS1 hI1 hS2 hI2 ⊢
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.takeKB,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.lenB,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eqB, litB, v,
    exprLitSize, pqOpLitSize, sz_F_X25519_length, Nat.add_zero, Nat.zero_add]
  dsimp only [gdhLift1Key] at hM160 hM192 hMScan hPre160 hPre192 hScan hSmp1 hSmp2 ⊢
  omega

@[local simp] private theorem s1_partnerC_size {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).size = 211 := by
  simp only [partnerC, bindV_size, qPow8_size, getDBytes, optBytesEq, eLet2,
    eLet_size, eCaseOpt_size, eqB_size, litB_size, v_size, Comp.size, Expr.size]

@[local simp] private theorem s1_chooseRespRandC_size (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndStateTy)
    (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K (Δ := Δ) st r).size = bits (min K S.N_dh) + 238 := by
  simp only [chooseRespRandC, bindV_size, gPrim_size, findMV_size, s1_partnerC_size,
    caseOptV_size, sDrKey96_size, v_size, Comp.size, Expr.size]; omega

@[local simp] private theorem s1_chooseInitRandC_size (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndStateTy)
    (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K (Δ := Δ) st s).size = bits (min K S.N_sess_tot) + 235 := by
  simp only [chooseInitRandC, bindV_size, gPrim_size, findMV_size, s1_partnerC_size,
    caseOptV_size, sDrKey96_size, v_size, Comp.size, Expr.size]; omega

private theorem s1_fgPatchShadowC_size (kFg : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.fgPosTy)
    (pos2 : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.fgPosTy)
    (pos3 : Var Γ₃ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.fgPosTy)
    (pos4? : Var Γ₄ (.opt _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.fgPosTy))
    (ss : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (fgL : Expr pqxdhOps Δ (.list _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy))
    (ctr : Expr pqxdhOps Δ .nat) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgPatchShadowC
        kFg pos1 pos2 pos3 pos4? ss fgL fgSess ctr).size ≤
      fgL.size + fgSess.size + ctr.size + bits kFg + 600 := by
  simp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgPatchShadowC,
    entryMatchesC, ddhEqOptC, ddhEqC, fePos1, fePos2, fePos3, fePos4,
    feSs, feDk, feMk, orE, letV_size, bindV_size, findMV_size, caseOptV_size, caseSumV_size,
    liftBase_size, sDrKey96_size, ddhQ_size, eqB_size, v_size, Comp.size, Expr.size, bits_1]
  omega

@[local simp] private theorem s1_finishAcceptGdhC_size (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.simTy)
    (bSt : Var Γ₃ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (_root_.SignalPqxdh.LegacyCosted.B 32))))))
    (patchR : Var Γ₇ (.prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.drKeyTy
      (.list _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.fgPatchEntryTy))) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.finishAcceptGdhC
        S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).size =
      opkPkOpt.size + opks'.size + usedN'.size + usedO'.size + kyb'.size +
        2 * bits (min K S.N_dh) + 530 := by
  cases hasOpk <;> {
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.finishAcceptGdhC,
      findHonestC, s1_chooseRespRandC_size, isSomeE, qHdr, qKJO, qK, qJ, qO,
      smRaw, smLog, smPows, smMk, smUpd, rDrKey, rAccFresh, eqB_size,
      letV_size, bindV_size, findMV_size, eCaseOpt_size, liftBase_size, qPow8_size,
      v_size, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]; omega }

@[local simp] private theorem s1_widenEC_size {Γ : List PT}
    (e : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B 33)) :
    (widenEC e).size = e.size + 1 := rfl

@[local simp] private theorem s1_qSigDdhSign_size (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B m)) :
    (qSigDdhSign m msg).size = msg.size + 1 := rfl

set_option linter.unusedSimpArgs false in
private theorem sigNoFgLegs_size_lit_le (K : Nat) :
    10 * (sigKindInitPrinLeg K).size + compLitSize (sigKindInitPrinLeg K) +
    (10 * (sigWrapGdh2NoFgLeg fun pa sm bSt u => wrapBase2 pa sm (corruptB K bSt u)).size +
      compLitSize (sigWrapGdh2NoFgLeg fun pa sm bSt u => wrapBase2 pa sm (corruptB K bSt u))) +
    (10 * (sigKindGenSpkLeg K).size + compLitSize (sigKindGenSpkLeg K)) +
    (10 * (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x)).size +
      compLitSize (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x))) +
    (10 * (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (testB K bSt sid)).size +
      compLitSize (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (testB K bSt sid))) +
    (10 * (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (revealB K bSt sid)).size +
      compLitSize (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (revealB K bSt sid))) +
    (10 * (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)).size +
      compLitSize (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk))) +
    (10 * (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (revealSpkB K bSt x)).size +
      compLitSize (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (revealSpkB K bSt x))) ≤
      400 * bits K + 60000 := by
  simp (config := { maxSteps := 500000 }) only [
    sigKindInitPrinLeg, sigKindGenSpkLeg, sigWrapGdh2NoFgLeg,
    sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
    wrapBase2, wrapSim2, corruptB, genSpkGdh2B, genOpkGdh2B, testB, revealB, registerGdhB, revealSpkB,
    saTP, saInner, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    pa2Mk, pa2U, pa2V, pa2Up, pa2PrinTarget, pa2SpkTarget, pa2OpkMode, pa2OpkTarget, optNatMatchesE,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
    oeMk, buMk, seSid, seHdr, sePeerSpk, seTested, seRevealed, seMk, seUpd,
    reSid, reHdr, reMk, reUpd, rs, freshE,
    rNone, rInitPrin, rPk, rCorr, rBundle, rDrKey, rSpkSk,
    isSomeE, natEq, nat2Eq, nat3Eq, sidEq, eLet2,
    encEC_size, encKEM_size, s1_widenEC_size, s1_qSigDdhSign_size,
    letV_size, bindV_size, caseOptV_size,
    eLet_size, eCaseOpt_size, eCaseSum_size, eFind_size, eAny_size, eMap_size,
    sz_s1Prim, sz_liftGdhToSigDdh, gPrim_size, litB_size, lenB_size, u32OfNat_size,
    sBytes32_size, sRandom64_size, qX25519Base_size, qPow8_size, qSigSign_size, qKemKeyGen_size,
    v_size, Comp.size, Expr.size, bits_0, bits_1, bits_32, pqxdhOps_opSize]
  simp (config := { maxSteps := 500000 }) only [
    letV, bindV, caseOptV, eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    lit_s1Prim, lit_gPrim, lit_liftGdhToSigDdh,
    encEC, encKEM, widenEC, consB, widenB, qSigDdhSign,
    sBytes32, sRandom64, qX25519Base, qPow8, qSigSign, qKemKeyGen,
    litB, lenB, u32OfNat, v, compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem sigSessLegs_size_lit_le (S : Setup) (f : KeyIndKFuels) :
    10 * (sigKindInitiateSessLeg S f true).size + compLitSize (sigKindInitiateSessLeg S f true) +
    (10 * (sigKindInitiateSessLeg S f false).size + compLitSize (sigKindInitiateSessLeg S f false)) +
    (10 * (sigKindAcceptOpkSessLeg S f).size + compLitSize (sigKindAcceptOpkSessLeg S f)) +
    (10 * (sigKindAcceptNoOpkSessLeg S f).size + compLitSize (sigKindAcceptNoOpkSessLeg S f)) ≤
      600 * bits f.kOn + 600 * bits (min f.kOn S.N_dh) +
        60 * bits (min f.kOn S.N_sess_tot) + 60 * bits f.kFg + 150000 := by
  simp (config := { maxSteps := 1000000 }) only [
    sigKindInitiateSessLeg, sigKindAcceptOpkSessLeg, sigKindAcceptNoOpkSessLeg,
    extract1KeyActiveC, initiateGdh2ShadowB, acceptOpkGdh2ShadowB,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.acceptOpkGdhCoreShadowB,
    acceptNoOpkGdhShadowB,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgPatchShadowC,
    s1_finishAcceptGdhC_size, s1_chooseInitRandC_size,
    saTP, saInner, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    pa2Mk, pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget, pa2SpkTarget,
    pa2OpkMode, pa2OpkTarget, ephSidMatchesE, optNatMatchesE,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    seSid, seHdr, sePeerSpk, seTested, seRevealed, seMk, seUpd,
    reSid, reHdr, reMk, reUpd, qKJO, qK, qJ, qO, qHdr, rs, slice32, freshE,
    rNone, rHdr, rInitUnfresh, rDrKey, initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, optU32Eq, isSomeE, optFst, optSnd, nonZero32,
    orE, eLet2, isAdvPowsE, fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC, entryMatchesC, ddhEqOptC, ddhEqC,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC,
    encEC_size, encKEM_size, s1_widenEC_size,
    letV_size, bindV_size, caseOptV_size, caseSumV_size, findMV_size, anyMV_size,
    eLet_size, eCaseOpt_size, eCaseSum_size, eAny_size, eFind_size, eMap_size,
    sz_s1Prim, sz_liftGdhToSigDdh, liftBase_size, gPrim_size,
    litB_size, takeKB_size, dropB_size, lenB_size, eqB_size, u32OfNat_size, eqU32_size,
    sBytes32_size, sDrKey96_size, ddhQ_size,
    qX25519_size, qX25519Base_size, qIsCanonical_size, qPow8_size,
    qSigVerify_size, qKemEncaps_size, qKemDecaps_size,
    v_size, Comp.size, Expr.size,
    bits_0, bits_1, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true, pqxdhOps_opSize]
  simp (config := { maxSteps := 1000000 }) only [
    letV, bindV, caseOptV, caseSumV, findMV, anyMV, eLet, eLet2, eCaseOpt, eCaseSum, eAny, eFind, eMap,
    lit_s1Prim, lit_gPrim, lit_liftBase, lit_liftGdhToSigDdh,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.finishAcceptGdhC,
    findHonestC, chooseInitRandC, chooseRespRandC, partnerC,
    qKJO, qK, qJ, qO, qHdr, isSomeE, natEq,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
    peIkAPk, sbSpkPk, sbPqspkPk, seSid, seHdr, reSid, reHdr, reMk, reUpd, hdIkAPk,
    optBytesEq, getDBytes, rDrKey, rAccFresh,
    encEC, encKEM, widenEC, consB, widenB,
    sBytes32, sDrKey96, ddhQ, qX25519, qX25519Base, qIsCanonical, qPow8,
    qSigVerify, qKemEncaps, qKemDecaps,
    litB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32, v, compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, sz_F_X25519_length,
    Nat.add_zero, Nat.zero_add, ↓reduceIte, Bool.false_eq_true]
  have : f.kOn.min S.N_dh = min f.kOn S.N_dh := rfl
  have : f.kOn.min S.N_sess_tot = min f.kOn S.N_sess_tot := rfl
  omega

set_option linter.unusedSimpArgs false in
theorem sigInitFinish_size_le (S : Setup) (b : QueryBudget) :
    (sig1KeyKindInitC S b).size ≤
      10 * bits (keyIndSentinel S b) + 10 * bits (activeSigBudget S b) + 2000 ∧
    sig1KeyKindFinishC.size ≤ 4000 := by
  constructor
  · have hM := mapComp_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe (sig1KeyKindBaseInit S b)
    have hE : (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.emptyFgShadowE
        (Γ := [.prod .unit (embedTy sig1KeyActiveStTy), _root_.SignalPqxdh.Costed.PB 32])).size ≤ 200 := by
      decide
    have hBSz : (sig1KeyKindBaseInit S b).size ≤
        bits (keyIndSentinel S b) + bits (activeSigBudget S b) + 100 := by
      unfold sig1KeyKindBaseInit; dsimp only; split <;> {
        simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
          bindV_size, sz_s1Prim, sIndex_size, sBool_size, v_size, Comp.size, Expr.size, bits_0]
        omega }
    have hBLit : compLitSize (sig1KeyKindBaseInit S b) ≤ 100 := by
      unfold sig1KeyKindBaseInit; dsimp only; split <;> {
        simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
          bindV, lit_s1Prim, sIndex, sBool, v, compLitSize, exprLitSize, pqOpLitSize,
          Nat.add_zero, Nat.zero_add]
        omega }
    unfold sig1KeyKindInitC
    simp only [Comp.size, Expr.size]
    omega
  · decide

set_option linter.unusedSimpArgs false in
private theorem sigPayExprs_size_le (S : Setup) {A : Ty pqAtomicSig} (N_s N_o : ℕ) :
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
    (.v0 : Expr pqAtomicOps [_root_.SignalPqxdh.Costed.PB 32, A, (pqKeyIndCodec S).Q]
      (_root_.SignalPqxdh.Costed.PB 32)).size ≤ 60 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [finPairToNatE, finTripleToNatE, finSidToNatExpr, initPayToNatE, accPayToNatE,
      aop, Computational.Proofs.SignalPqxdh.AtomicLift.aop,
      Expr.size, Expr.v0, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize]; omega)


theorem sig1KeyKindHandleC_size_le (S : Setup) (b : QueryBudget) :
    let f := keyIndKFuelsOfBudget S b
    (sig1KeyKindHandleC S b).size ≤
      8 * bits (avlHeightCap f.kAvl) + 1040 * bits f.kOn + 600 * bits (min f.kOn S.N_dh) +
        60 * bits (min f.kOn S.N_sess_tot) + 60 * bits f.kFg + 250000 := by
  let f := keyIndKFuelsOfBudget S b
  let A := Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs.sig1KeyActiveKindStTy
  rcases sigPayExprs_size_le S (A := A) S.N_send_opk S.N_opk with
    ⟨hP1, hPP, hPT, hPS, hPI1, hPA1, hPV0⟩
  rcases sigPayExprs_size_le S (A := A) S.N_send_no_opk S.N_no_opk with
    ⟨_, _, _, _, hPI2, hPA2, _⟩
  have hNoFg := sigNoFgLegs_size_lit_le f.kOn
  have hSess := sigSessLegs_size_lit_le S f
  have hRo := sigKindRoArm_size_le S f
  have hA1 := liftSigDdhNoFgArm_size_le S (aop (.finVal S.N_id) .v0) (sigKindInitPrinLeg f.kOn)
  have hA2 := liftSigDdhNoFgArm_size_le S (aop (.finVal S.N_id) .v0)
    (sigWrapGdh2NoFgLeg fun pa sm bSt u => wrapBase2 pa sm (corruptB f.kOn bSt u))
  have hA3 := liftSigDdhNoFgArm_size_le S (finPairToNatE S.N_id S.N_recv .v0) (sigKindGenSpkLeg f.kOn)
  have hA4 := liftSigDdhNoFgArm_size_le S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
    (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B f.kOn pa sm bSt x))
  have hA5 := liftSigDdhSessArm_size_le S (initPayToNatE S.N_send_opk S .v0)
    (sigKindInitiateSessLeg S f true)
  have hA6 := liftSigDdhSessArm_size_le S (initPayToNatE S.N_send_no_opk S .v0)
    (sigKindInitiateSessLeg S f false)
  have hA7 := liftSigDdhSessArm_size_le S (accPayToNatE S.N_opk S .v0)
    (sigKindAcceptOpkSessLeg S f)
  have hA8 := liftSigDdhSessArm_size_le S (accPayToNatE S.N_no_opk S .v0)
    (sigKindAcceptNoOpkSessLeg S f)
  have hA9 := liftSigDdhNoFgArm_size_le S (finSidToNatExpr S .v0)
    (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (testB f.kOn bSt sid))
  have hA12 := liftSigDdhNoFgArm_size_le S (finSidToNatExpr S .v0)
    (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (revealB f.kOn bSt sid))
  have hA13 := liftSigDdhNoFgArm_size_le S .v0
    (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk))
  have hA14 := liftSigDdhNoFgArm_size_le S (finPairToNatE S.N_id S.N_recv .v0)
    (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (revealSpkB f.kOn bSt x))
  have hC11 : ((.ret (.pair atomicRNoneE .v1) :
      Comp pqAtomicOps pqSigAndDdhIface (.unit :: [A, (pqKeyIndCodec S).Q])
        (.prod ((pqKeyIndCodec S).R) A))).size ≤ 20 := by
    simp only [atomicRNoneE, Comp.size, Expr.size, Expr.v1]; omega
  have hV1 : ((.v1 : Expr pqAtomicOps [A, (pqKeyIndCodec S).Q] ((pqKeyIndCodec S).Q))).size = 1 := rfl
  unfold sig1KeyKindHandleC; dsimp only
  rw [dispatchKeyIndQ_size_eq]
  dsimp only [f, A] at *
  omega

end SizeBounds

section CostByKindAndTotal

open _root_.ReductionDsl (atomicPureOps AtomicPureOp)
open Computational.Proofs.ReductionDsl.KindedDispatch (costBoundedByKind_fin2_of_armCosts)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  widenEC widenEC_costUB qSigDdhSign_costUB encEC encKEM eqB honestPeerC
  natEq nat2Eq nat3Eq sidEq eLet2
  stPrin stSpks peIkAPk peUpd peMk sbSpkPk sbPqspkPk sbUpd sbMk
  buIkB buSpkB buSpkSig buPqspkB buPqspkSig buMk
  rInitPrin rBundle rPk rCorr rDrKey rSpkSk oeMk seMk seUpd reMk reUpd rs freshE
  pa2OpkMode pa2OpkTarget pa2SpkTarget pa2PrinTarget pa2Up pa2V)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (
  letV_costUB caseOptV_costUB eLet_costUB eCaseOpt_costUB eCaseSum_costUB
  eFind_costUB eAny_costUB eMap_costUB
  litB_costUB lenB_costUB eqB_costUB u32OfNat_costUB
  sBytes32_costUB sRandom64_costUB qX25519Base_costUB qPow8_costUB
  qSigPkGen_costUB qSigSign_costUB qSigVerify_costUB qKemKeyGen_costUB
  honestPeerC_costUB encEC_costUB encKEM_costUB
  rNone_costUB rInitPrin_costUB rPk_costUB rCorr_costUB rBundle_costUB rDrKey_costUB rSpkSk_costUB
  smBase_costUB smFgL_costUB smRaw_costUB smLog_costUB smPows_costUB bits_32)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  aop expr_cost_two_mul_le finSidToNatExpr)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  sig1KeyActiveKindStTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  finPairToNatE finTripleToNatE initPayToNatE accPayToNatE)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost (
  dispatchKeyIndQ_ro_costAt_le dispatchKeyIndQ_online_costAt_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  fgShadowAtomicTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost (
  keyInd_gpair_sum_eq roParsedShadowAtomicC_cost_le
  initiateGdh2ShadowB_atomic_cost_le acceptOpkGdh2ShadowB_atomic_cost_le
  acceptNoOpkGdhShadowB_atomic_cost_le)

private theorem mapComp_liftGdhToSigDdh_eq {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ τ) :
    mapComp tlSigDdhKeyInd (liftGdhToSigDdh c) = liftGdhAtomic gdhLift1Key c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, liftGdhAtomic, gdhLift1Key, liftGdhComp, mapComp]

theorem sigKindRoArm_cost_le (S : Setup) (f : KeyIndKFuels) :
    (sigKindRoArm S f).cost ≤ 4420 * bits f.kAvl + 1345 * f.kOn + 8800 := by
  have hRo := roParsedShadowAtomicC_cost_le gdhLift1Key f
  have hHas : (mapExpr (isSomeE (s1Forgery (saInner (Γ := [sig1KeyActiveStTy]) (.var .zero))))).cost ≤ 30 := by
    decide
  have hGet : (mapExpr (s1Fg (saInner (Γ := [sig1KeyActiveStTy]) (.var .zero)))).cost ≤ 30 := by
    decide
  have hSet : (mapExpr (Γ := [.prod sig1KeyActiveStTy simTy])
      (.pair (saTP (.fst (.var .zero)))
        (s1Upd (saInner (.fst (.var .zero))) (fg := .snd (.var .zero))))).cost ≤ 60 := by
    decide
  unfold sigKindRoArm sigHasForgeryAtomicE sigGetFgAtomicE sigSetFgAtomicE runAt2 atomicRNoneE
  simp only [Comp.cost, compRename_cost, exprRename_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem sigPayExprs_cost_le (S : Setup) {A : Ty pqAtomicSig} (N_s N_o : Nat) :
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

private theorem bindV_sigDdh_ub {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface (τ₁ :: Γ) τ₂)
    {Bk : Nat} (hk : (mapComp tlSigDdhKeyInd (k .zero)).cost ≤ Bk) :
    (mapComp tlSigDdhKeyInd (bindV m k)).cost ≤ 11 * m.costUB + Bk + 1 :=
  bindV_sigDdh_cost_le m k (mapComp_sigDdh_cost_le_eleven_costUB m) hk

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

private theorem extract1KeyActiveC_atomic_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (bu : Var Γ₂ preKeyBundleTy) :
    (mapComp tlSigDdhKeyInd (extract1KeyActiveC S K (Δ := Δ) st bu)).cost ≤
      9000 * K + 45000 := by
  apply Nat.le_trans
  · dsimp only [extract1KeyActiveC]
    apply letV_sigDdh_cost_le
    apply bindV_sigDdh_ub; apply bindV_sigDdh_ub; apply bindV_sigDdh_ub
    exact ret_sigDdh_cost_le _
  · simp only [saTP, optNatMatchesE, eLet2, s1Forgery, s1Base, s1Fg, smBase, s1Pk,
      stSpks, sbSpkPk, sbPqspkPk, buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig, natEq,
      s1Prim_costUB, letV_costUB, honestPeerC_costUB, qSigVerify_costUB,
      eLet_costUB, eCaseOpt_costUB, eAny_costUB, eqB_costUB, encEC_costUB, encKEM_costUB, widenEC_costUB,
      v_costUB, Expr.costUB, PNat.val_ofNat]
    omega

set_option linter.unusedSimpArgs false in
private theorem sigSessLegs_atomic_cost_le (S : Setup) (f : KeyIndKFuels) :
    (∀ hasOpk, (mapComp tlSigDdhKeyInd (sigKindInitiateSessLeg S f hasOpk)).cost ≤
      1336 * f.kFg + 21100 * f.kOn + 7000 * min f.kOn S.N_dh +
        23000 * min f.kOn S.N_sess_tot + 102000) ∧
    (mapComp tlSigDdhKeyInd (sigKindAcceptOpkSessLeg S f)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35600 ∧
    (mapComp tlSigDdhKeyInd (sigKindAcceptNoOpkSessLeg S f)).cost ≤
      1336 * f.kFg + 3000 * f.kOn + 25000 * min f.kOn S.N_dh + 35600 := by
  refine ⟨fun hasOpk => ?_, ?_, ?_⟩
  · apply Nat.le_trans
    · dsimp only [sigKindInitiateSessLeg]
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply ite_sigDdh_cost_le; · exact ret_sigDdh_cost_le _
      apply letV_sigDdh_cost_le
      apply bindV_sigDdh_cost_le; · exact extract1KeyActiveC_atomic_cost_le S f.kOn _ _
      apply ite_sigDdh_cost_le; · exact ret_sigDdh_cost_le _
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply bindV_sigDdh_cost_le
      · exact (congrArg Comp.cost (mapComp_liftGdhToSigDdh_eq _)).le.trans
          (initiateGdh2ShadowB_atomic_cost_le gdhLift1Key S f _ _ _ _ hasOpk _)
      · exact ret_sigDdh_cost_le _
    · simp only [saTP, saInner, isSomeE, s1Forgery, s1Pk, s1Fg, s1Upd, s1Mk,
        s1Target, s1Budget, smBase_costUB, pa2Mk, rNone_costUB, eCaseOpt_costUB,
        litB_costUB, v_costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_1]
      omega
  · apply Nat.le_trans
    · dsimp only [sigKindAcceptOpkSessLeg]
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply ite_sigDdh_cost_le; · exact ret_sigDdh_cost_le _
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply bindV_sigDdh_cost_le
      · exact (congrArg Comp.cost (mapComp_liftGdhToSigDdh_eq _)).le.trans
          (acceptOpkGdh2ShadowB_atomic_cost_le gdhLift1Key S f _ _ _ _ _)
      · exact ret_sigDdh_cost_le _
    · simp only [saTP, saInner, isSomeE, s1Forgery, s1Pk, s1Fg, s1Upd, s1Mk,
        s1Target, s1Budget, smBase_costUB, pa2Mk, rNone_costUB, eCaseOpt_costUB,
        litB_costUB, v_costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_1]
      omega
  · apply Nat.le_trans
    · dsimp only [sigKindAcceptNoOpkSessLeg]
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply ite_sigDdh_cost_le; · exact ret_sigDdh_cost_le _
      apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
      apply bindV_sigDdh_cost_le
      · exact (congrArg Comp.cost (mapComp_liftGdhToSigDdh_eq _)).le.trans
          (acceptNoOpkGdhShadowB_atomic_cost_le gdhLift1Key S f _ _ _ _)
      · exact ret_sigDdh_cost_le _
    · simp only [saTP, saInner, isSomeE, s1Forgery, s1Fg, s1Upd, s1Mk,
        s1Pk, s1Target, s1Budget, smBase_costUB, rNone_costUB, eCaseOpt_costUB,
        v_costUB, Expr.costUB]
      omega

private theorem mapComp_liftGdhToSigDdh_cost_le {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface Γ τ) :
    (mapComp tlSigDdhKeyInd (liftGdhToSigDdh c)).cost ≤ 11 * c.costUB := by
  rw [mapComp_liftGdhToSigDdh_eq,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKCost.liftGdhAtomic_gdhLift1Key_cost_eq]
  have h11 := mapComp_cost_eleven_mul_le Computational.Proofs.SignalPqxdh.AtomicLift.tlGapDhKeyInd c
  have hUB := c.cost_le_costUB
  dsimp only [liftGdhAtomic,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.gdhLift2Key]
  omega

set_option linter.unusedSimpArgs false in
private theorem sigWrapGdh2NoFgLeg_atomic_cost_le {qPayTy : PT}
    (gdhBody : Var [params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] keyIndStateTy →
      Var [sig1KeyActiveStTy, qPayTy] qPayTy →
      Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
        [keyIndStateTy, simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy]
        (.prod keyIndRespTy gdhState2Ty)) :
    (mapComp tlSigDdhKeyInd (sigWrapGdh2NoFgLeg gdhBody)).cost ≤
      11 * (gdhBody .zero .zero .zero (.succ .zero)).costUB + 300 := by
  apply Nat.le_trans
  · dsimp only [sigWrapGdh2NoFgLeg]
    apply ite_sigDdh_cost_le; · exact ret_sigDdh_cost_le _
    apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
    apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
    apply bindV_sigDdh_cost_le
    · exact mapComp_liftGdhToSigDdh_cost_le _
    · exact ret_sigDdh_cost_le _
  · simp only [saTP, saInner, isSomeE, s1Forgery, s1Pk, s1Fg, s1Upd, s1Mk,
      s1Target, s1Budget, smBase_costUB, pa2Mk, rNone_costUB, eCaseOpt_costUB,
      litB_costUB, v_costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_1]
    omega

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
      [.prod stTy Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.fgSessCtrTy))) :
    (liftSigDdhSessArm S payE arm).cost ≤ payE.cost + (mapComp tlSigDdhKeyInd arm).cost + 40 := by
  unfold liftSigDdhSessArm runAt2
  simp only [Comp.cost, compRename_cost, exprRename_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

set_option linter.unusedSimpArgs false in
private theorem sigNoFgLegs_atomic_cost_le (K : Nat) :
    (mapComp tlSigDdhKeyInd (sigKindInitPrinLeg K)).cost ≤ 15000 * K + 15000 ∧
    (mapComp tlSigDdhKeyInd (sigKindGenSpkLeg K)).cost ≤ 15000 * K + 102000 ∧
    (mapComp tlSigDdhKeyInd (sigWrapGdh2NoFgLeg fun pa sm bSt u =>
      wrapBase2 pa sm (corruptB K bSt u))).cost ≤ 15000 * K + 15000 ∧
    (mapComp tlSigDdhKeyInd (sigWrapGdh2NoFgLeg fun pa sm bSt x =>
      wrapSim2 pa (genOpkGdh2B K pa sm bSt x))).cost ≤ 15000 * K + 15000 ∧
    (mapComp tlSigDdhKeyInd (sigWrapGdh2NoFgLeg fun pa sm bSt sid =>
      wrapBase2 pa sm (testB K bSt sid))).cost ≤ 15000 * K + 15000 ∧
    (mapComp tlSigDdhKeyInd (sigWrapGdh2NoFgLeg fun pa sm bSt sid =>
      wrapBase2 pa sm (revealB K bSt sid))).cost ≤ 15000 * K + 15000 ∧
    (mapComp tlSigDdhKeyInd (sigWrapGdh2NoFgLeg fun pa sm bSt sk =>
      wrapSim2 pa (registerGdhB sm bSt sk))).cost ≤ 15000 * K + 15000 ∧
    (mapComp tlSigDdhKeyInd (sigWrapGdh2NoFgLeg fun pa sm bSt x =>
      wrapBase2 pa sm (revealSpkB K bSt x))).cost ≤ 15000 * K + 15000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mapComp_sigDdh_cost_le_eleven_costUB _).trans ?_
    simp only [sigKindInitPrinLeg, sig1KeyActiveInitPrinB, saTP, saInner, isSomeE,
      s1Forgery, s1Base, s1Fg, s1Target, s1Pk, s1Budget, s1Upd, s1Mk,
      smUpd, smMk, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      stPrin, stUpd, stMk, peMk, rNone_costUB, rInitPrin_costUB, natEq,
      letV_costUB, bindV_costUB, s1Prim_costUB, sBytes32_costUB, qX25519Base_costUB,
      eCaseOpt_costUB, eAny_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
      List.length_nil, PNat.val_ofNat]
    omega
  · apply Nat.le_trans
    · dsimp only [sigKindGenSpkLeg]
      apply ite_sigDdh_cost_le; · exact ret_sigDdh_cost_le _
      apply ite_sigDdh_cost_le
      · apply letV_sigDdh_cost_le
        apply bindV_sigDdh_ub; exact ret_sigDdh_cost_le _
      · apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
        apply letV_sigDdh_cost_le; apply letV_sigDdh_cost_le
        apply bindV_sigDdh_cost_le
        · exact mapComp_liftGdhToSigDdh_cost_le _
        · exact ret_sigDdh_cost_le _
    · simp only [sig1KeyTargetGenSpkB, genSpkGdh2B, wrapSim2, saTP, saInner, optNatMatchesE, eLet2,
        isSomeE, s1Forgery, s1Base, s1Fg, s1Target, s1Pk, s1Budget, s1Upd, s1Mk,
        pa2Mk, pa2SpkTarget, pa2V, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        smUpd, smMk, stPrin, stSpks, stUpd, stMk, peIkAPk, sbMk, buMk,
        rNone_costUB, rBundle_costUB, nat2Eq, natEq,
        letV_costUB, bindV_costUB, caseOptV_costUB, s1Prim_costUB,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gPrim_costUB,
        sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB, qKemKeyGen_costUB,
        qSigSign_costUB, qSigDdhSign_costUB, encEC_costUB, encKEM_costUB, widenEC_costUB,
        eLet_costUB, eCaseOpt_costUB, eAny_costUB, eFind_costUB,
        u32OfNat_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
        List.length_nil, PNat.val_ofNat, bits_0, bits_1]
      omega
  · refine (sigWrapGdh2NoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, corruptB, rs, peUpd, peMk, stUpd, stMk, smUpd, smMk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gPrim_costUB,
      smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, rNone_costUB, rCorr_costUB,
      bindV_costUB, caseOptV_costUB, eFind_costUB, eMap_costUB, natEq, v_costUB, Comp.costUB, Expr.costUB]
    omega
  · refine (sigWrapGdh2NoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapSim2, genOpkGdh2B, oeMk, stUpd, stMk, smUpd, smMk, pa2OpkMode, pa2OpkTarget, pa2V,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gPrim_costUB,
      smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, rNone_costUB, rPk_costUB,
      letV_costUB, bindV_costUB, eCaseOpt_costUB, eAny_costUB,
      sBytes32_costUB, qX25519Base_costUB, litB_costUB, nat3Eq, nat2Eq, natEq,
      v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
    omega
  · refine (sigWrapGdh2NoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, testB, freshE, rs, seUpd, seMk, reUpd, reMk, stUpd, stMk, smUpd, smMk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gPrim_costUB,
      smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, rNone_costUB, rDrKey_costUB,
      bindV_costUB, caseOptV_costUB, eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eMap_costUB,
      sidEq, eLet2, nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]
    omega
  · refine (sigWrapGdh2NoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, revealB, rs, seUpd, seMk, reUpd, reMk, stUpd, stMk, smUpd, smMk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gPrim_costUB,
      smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, rNone_costUB, rDrKey_costUB,
      bindV_costUB, caseOptV_costUB, eLet_costUB, eCaseSum_costUB, eFind_costUB, eMap_costUB,
      sidEq, eLet2, nat3Eq, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]
    omega
  · refine (sigWrapGdh2NoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapSim2, registerGdhB, stUpd, stMk, smUpd, smMk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gPrim_costUB,
      smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, rNone_costUB, rPk_costUB,
      bindV_costUB, qX25519Base_costUB, qPow8_costUB, lenB_costUB,
      natEq, v_costUB, Comp.costUB, Expr.costUB, PNat.val_ofNat, bits_32]
    omega
  · refine (sigWrapGdh2NoFgLeg_atomic_cost_le _).trans ?_
    simp only [wrapBase2, revealSpkB, rs, sbUpd, sbMk, stUpd, stMk, smUpd, smMk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gPrim_costUB,
      smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, rNone_costUB, rSpkSk_costUB,
      bindV_costUB, caseOptV_costUB, eFind_costUB, eMap_costUB, nat2Eq, natEq, v_costUB, Comp.costUB, Expr.costUB]
    omega

theorem dispatchKeyIndQ_cost_le {ι : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} (S : Setup) {Γ : List (Ty pqAtomicSig)} {τ : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q)) (B : Nat)
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
    (h1 : c1.cost ≤ B) (h2 : c2.cost ≤ B) (h3 : c3.cost ≤ B) (h4 : c4.cost ≤ B)
    (h5 : c5.cost ≤ B) (h6 : c6.cost ≤ B) (h7 : c7.cost ≤ B) (h8 : c8.cost ≤ B)
    (h9 : c9.cost ≤ B) (h10 : c10.cost ≤ B) (h11 : c11.cost ≤ B) (h12 : c12.cost ≤ B)
    (h13 : c13.cost ≤ B) (h14 : c14.cost ≤ B) :
    (dispatchKeyIndQ S qE c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14).cost ≤
      qE.cost + B + 26 := by
  simp only [dispatchKeyIndQ, Comp.cost, compRename_cost, Expr.cost, Expr.v0]
  omega

@[expose] def sigOnlineArmBudget (S : Setup) (f : KeyIndKFuels) : Nat :=
  1336 * f.kFg + 21200 * f.kOn + 25100 * min f.kOn S.N_dh +
    23100 * min f.kOn S.N_sess_tot + 102200

theorem sigOnlineArms_all_cost_le (S : Setup) (f : KeyIndKFuels) :
    let B := sigOnlineArmBudget S f
    (liftSigDdhNoFgArm S (aop (.finVal S.N_id) .v0) (sigKindInitPrinLeg f.kOn)).cost ≤ B ∧
    (liftSigDdhNoFgArm S (aop (.finVal S.N_id) .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt u => wrapBase2 pa sm (corruptB f.kOn bSt u))).cost ≤ B ∧
    (liftSigDdhNoFgArm S (finPairToNatE S.N_id S.N_recv .v0) (sigKindGenSpkLeg f.kOn)).cost ≤ B ∧
    (liftSigDdhNoFgArm S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B f.kOn pa sm bSt x))).cost ≤ B ∧
    (liftSigDdhSessArm S (initPayToNatE S.N_send_opk S .v0)
      (sigKindInitiateSessLeg S f true)).cost ≤ B ∧
    (liftSigDdhSessArm S (initPayToNatE S.N_send_no_opk S .v0)
      (sigKindInitiateSessLeg S f false)).cost ≤ B ∧
    (liftSigDdhSessArm S (accPayToNatE S.N_opk S .v0)
      (sigKindAcceptOpkSessLeg S f)).cost ≤ B ∧
    (liftSigDdhSessArm S (accPayToNatE S.N_no_opk S .v0)
      (sigKindAcceptNoOpkSessLeg S f)).cost ≤ B ∧
    (liftSigDdhNoFgArm S (finSidToNatExpr S .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (testB f.kOn bSt sid))).cost ≤ B ∧
    (.ret (.pair atomicRNoneE .v1) :
      Comp pqAtomicOps pqSigAndDdhIface
        (.unit :: [sig1KeyActiveKindStTy, (pqKeyIndCodec S).Q])
        (.prod ((pqKeyIndCodec S).R) sig1KeyActiveKindStTy)).cost ≤ B ∧
    (liftSigDdhNoFgArm S (finSidToNatExpr S .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (revealB f.kOn bSt sid))).cost ≤ B ∧
    (liftSigDdhNoFgArm S .v0
      (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk))).cost ≤ B ∧
    (liftSigDdhNoFgArm S (finPairToNatE S.N_id S.N_recv .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (revealSpkB f.kOn bSt x))).cost ≤ B := by
  dsimp only [sigOnlineArmBudget]
  obtain ⟨hL1, hL3, hL2, hL4, hL9, hL12, hL13, hL14⟩ := sigNoFgLegs_atomic_cost_le f.kOn
  obtain ⟨hSInit, hS7, hS8⟩ := sigSessLegs_atomic_cost_le S f
  have hS5 := hSInit true
  have hS6 := hSInit false
  obtain ⟨hP1a, hP3a, hP4a, hP9a, _, _, hP13a⟩ :=
    sigPayExprs_cost_le S (A := sig1KeyActiveKindStTy) S.N_send_opk S.N_opk
  obtain ⟨_, _, _, _, hP5b, hP7b, _⟩ :=
    sigPayExprs_cost_le S (A := sig1KeyActiveKindStTy) S.N_send_opk S.N_opk
  obtain ⟨_, _, _, _, hP6b, hP8b, _⟩ :=
    sigPayExprs_cost_le S (A := sig1KeyActiveKindStTy) S.N_send_no_opk S.N_no_opk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hW := liftSigDdhNoFgArm_cost_le S (aop (.finVal S.N_id) .v0) (sigKindInitPrinLeg f.kOn); omega
  · have hW := liftSigDdhNoFgArm_cost_le S (aop (.finVal S.N_id) .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt u => wrapBase2 pa sm (corruptB f.kOn bSt u)); omega
  · have hW := liftSigDdhNoFgArm_cost_le S (finPairToNatE S.N_id S.N_recv .v0) (sigKindGenSpkLeg f.kOn); omega
  · have hW := liftSigDdhNoFgArm_cost_le S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B f.kOn pa sm bSt x)); omega
  · have hW := liftSigDdhSessArm_cost_le S (initPayToNatE S.N_send_opk S .v0) (sigKindInitiateSessLeg S f true); omega
  · have hW := liftSigDdhSessArm_cost_le S (initPayToNatE S.N_send_no_opk S .v0) (sigKindInitiateSessLeg S f false); omega
  · have hW := liftSigDdhSessArm_cost_le S (accPayToNatE S.N_opk S .v0) (sigKindAcceptOpkSessLeg S f); omega
  · have hW := liftSigDdhSessArm_cost_le S (accPayToNatE S.N_no_opk S .v0) (sigKindAcceptNoOpkSessLeg S f); omega
  · have hW := liftSigDdhNoFgArm_cost_le S (finSidToNatExpr S .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (testB f.kOn bSt sid)); omega
  · simp only [atomicRNoneE, Comp.cost, Expr.cost, Expr.v1]; omega
  · have hW := liftSigDdhNoFgArm_cost_le S (finSidToNatExpr S .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (revealB f.kOn bSt sid)); omega
  · have hW := liftSigDdhNoFgArm_cost_le S .v0
      (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)); omega
  · have hW := liftSigDdhNoFgArm_cost_le S (finPairToNatE S.N_id S.N_recv .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (revealSpkB f.kOn bSt x)); omega


end CostByKindAndTotal

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBoundsCost
