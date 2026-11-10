/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.HeadlineDelta -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.CostedTablesCompat
import Computational.Proofs.ReductionDsl.AtomicSizeHonest
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigSessionSplit -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigWire
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhWire
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhSessionSplit

/-!
# Active Creation-Order Reduction Bounds for One-Key PQXDH `KeyInd`

Proves semantic query compliance (`pqxdhKeyInd1KeyActiveCostedSims_simBounds`), unsupported-query
vanishing, and atomic evaluation equivalences for the active creation-order one-key `KeyInd`
reduction family `pqxdhKeyInd1KeyActiveCostedSims`. The `sig` and `gdh` primitive-query bounds split
session queries from non-session queries to establish `gdhPrimQueryBudget`.
-/

set_option autoImplicit false

open OracleSpec OracleComp
open Computational.Proofs.GameHop.ReductionDsl.SupportWP (potC_bind potOK_simulateQ_handlerImpl)
open Computational.Proofs.SignalPqxdh.AtomicLift (embedMid embedMid_projMid embedVal kemShCrAdv_bounded_of_state_retract keyIndUnsupportedPrimW liftKeyInd1Stage_eval liftKeyInd1Stage_totalCost_eleven_mul_le liftKeyInd1Stage_totalCost_two_mul_le liftKeyInd1Stage_totalQueries_le liftKeyInd2Stage_eval1 liftKeyInd2Stage_eval2 liftKeyInd2Stage_totalCost_eleven_mul_le liftKeyInd2Stage_totalQueries_le one_le_pqPrimIface_qCost one_le_pqSigAndDdhIface_qCost projMid r64W sampR64W tlGapDhKeyInd tlPrimKeyInd tlPrimKeyInd_primW tlSigDdhKeyInd tlSigDdhKeyInd_ddhW tlSigDdhKeyInd_primW tlSigDdhKeyInd_sigW)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (S1ARS activeSigBudget callGdhActiveHandle extract1KeyActiveC fgActiveTotalIndexCount fgKeyInd1KeyGapDhActiveAtomicProg fgKeyInd1KeyGapDhActiveDslProg gdh1KeyActiveFinish gdh1KeyActiveHandle gdh1KeyActiveStateTy genOpkActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB initParams1KeyActiveFlat initPrin1KeyActiveGdhB initiateActiveGdhB initiateGdhActiveInnerB optNatMatchesE pqxdhKeyInd1KeyActiveCostedSims saInner saTP shcr1KeyActivePostC shcr1KeyActivePreC shcrActiveGenSpkB shcrActivePostTailC shcrKeyInd1KeyActiveAtomicProg shcrKeyInd1KeyActiveDslProg sig1KeyActiveHandleC sig1KeyActiveInitPrinB sig1KeyActiveInitiateCheckC sig1KeyActivePreDispatchC sig1KeyActiveStTy sigKeyInd1KeyActiveAtomicProg sigKeyInd1KeyActiveDslProg)
open ReductionDsl (Comp CostedReduction Env Expr Mid PotOK TwoStageCostedReduction Ty Var bits bits_le_succ bits_mono bits_mul isGameQuery)
open SignalPqxdh (BoundedAdv Bytes KemShCrAdv KeyIndAdversary PrimBaseSpec QueryBudget Setup activeIdCount activeOpkCount activeSendCount activeSendOpkCount activeSpkCount isDdhChalQuery isPrimQuery isPrimQuery₀ isSigChalQuery keyIndSpec sigAndDdhSpec)
open SignalPqxdh.LegacyCosted (B PSamp bundleT gapDhDdhOracle hdrT keyIndCodec pqChalIface pqGapDhIface pqPrimIface pqSamplers pqSig pqSigAndDdhIface pqxdhOps samplerZeroQueryWeight sidT sigAndDdhOracle)
open SignalPqxdh.Security (KeyIndCostedReductionBounds KeyIndCostedReductionFamily KeyIndReductionQueryBounds chalIfaceDdhQueryWeight chalIfacePrimQueryWeight chalIfaceSigQueryWeight fgTotalIndexCount gdhQueryBudget primIfacePrimQueryWeight primQueryBudget stepCostBudget)
open SignalPqxdh.Security.ReductionDsl.KeyInd (Ext PT S1RS accQTy acceptNoOpkGdhB acceptOpkGdhB anyMV bindV RS accInpTy acceptKeysC acceptNoOpkB acceptOpkB bits_0 bits_eq_log2_succ checkSigsC extractMode0C findMapStepC hkdfOrRoC initDh1CandC initFinishC koskBundleOkC koskSenderOkC logFindC mapMV foldMV preCheckC recordRespC respDh1CandC spkPowsC bits_1 bits_2 bits_3 bits_nRecv_le buIkB buMk buOpkB buPqspkB buPqspkId buPqspkSig buSpkB buSpkId buSpkSig caseOptV caseSumV checkProvC checkSigsC_queries chooseInitRandC chooseRespRandC computeOptPosInitC computePosC corruptB corruptB_cost corruptB_queries cost_encEC cost_encKEM cost_qSigSign cost_qX25519Base cost_sBytes32 cost_sRandom64 cost_u32OfNat cost_v ddhEqC ddhEqOptC ddhQ delegateFgC delegateFgC_cost_le delegateFgC_ddhQueries delegateFgC_potOK delegateFgC_primUB delegateFgC_sigQueries drKeyTy eAny eFind eLet eLet2 emptySimE emptyStE entryMatchesC extract1KeyC fgPatchC fgPatchEntryTy fgPosTy findHonestC findMV finishAcceptGdhC gPrim gdhFinish gdhHandle gdhStateTy genOpkB_cost genOpkB_queries genOpkGdhB genSpkB genSpkB_cost genSpkGdhB hUSigChal1Key hdMk honestPeerC hwSigChal1Key initPrin1KeyB initPrin1KeyB_cost_le initPrinB_cost initPrinGdhB initQTy initSidE initiateGdhB isAdvRegC isGameOpkC isGameSpkC isSigChal1KeyQ isSomeE keyIndLoopBound keyIndQueryRestTy keyIndQueryTy keyIndRespEntryTy keyIndRespTy keyIndSessionEntryTy keyIndStateTy koskBundleOkPowsC koskSenderOkPowsC letV liftBase liftGdhToSigDdh lookupSpkSkC mkPairPosC mkSecretPosC nRecv nat2Eq nat3Eq natEq oeMk onBase onBase_cost onBase_queries opkEntryTy optFst optSnd paMk paramsTy partnerC pauseCheckC pauseCheckC_cost pauseTy peIkAPk peMk peSecIKA0 peSecIKAsign potC_s1_bind0 potC_s1_caseOpt potC_s1_caseSum potC_s1_ite potC_s1_ret preCheckC_queries preKeyBundleTy primW primWS principalEntryTy qHkdfDerive96 qIsCanonical qKemDecaps qKemEncaps qKemKeyGen qPow8 qSigDdhSign qSigDdhSign_costUB qSigDdhSign_primUB qSigPkGen qSigSign qSigVerify qX25519 qX25519Base rBundle rInitPrin rNone registerB_cost registerB_queries registerGdhB resolveSigPkC revealB revealB_cost revealB_queries revealDhB_queries revealDhB_true_cost revealSpkB revealSpkB_cost revealSpkB_queries roB_queries roB_true_cost roParsedC roRawFallbackC s1Base s1Budget s1Fg s1Forgery s1Mk s1Pk s1Prim s1Prim_costUB s1Prim_ddhQueries s1Prim_primUB s1Prim_sigQueries s1Target s1Upd sBool sBytes32 sDrKey96 sIndex sRandom64 sbMk sbPqspkPk sbSpkPk scBase scChosen scCnt scIR scMk scRR scSIdx scTB scTPk scTSk scUpd seMk seSid seUpd shcrAcceptB_false_cost shcrAcceptB_false_queries shcrAcceptB_true_cost shcrAcceptB_true_queries shcrGenSpkB shcrInitiateC_false_cost shcrInitiateC_queries shcrInitiateC_true_cost shcrKeyIndProg shcrKeyIndProg_chDone_cost shcrKeyIndProg_finish_cost shcrKeyIndProg_finish_primQueries shcrKeyIndProg_resume_cost shcrKeyIndProg_resume_primQueries_le shcrPostC shcrPostC_eq_tail shcrPostTailC shcrPreC shcrStTy sidEq sig1KeyHandleC sig1KeyInitPrinB sig1KeyInitiateCheckC sig1KeyPreDispatchC sig1KeyStTy sig1KeyTargetGenSpkB sig1KeyTargetGenSpkB_potOK sigKeyInd1KeyProg sigPot1Key simTy smMk smUpd spkBundleEntryTy stAdv stKyb stMk stOpks stPrin stResps stRo stSecb stSess stSpks stUpd stUsedN stUsedO testB testB_cost testB_queries tryPauseC v widenEC_costUB wrapBase wrapSim)
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (callGdhHandle callGdhHandle_cost gdh1KeyStateTy liftGdhComp liftGdhComp_cost liftGdhComp_costUB liftGdhComp_queries_ddh liftGdhComp_queries_prim liftGdhComp_queries_sig qKemKeyGen_queries qX25519Base_queries renameComp renameComp_cost renameComp_queries sigChalQ_dsl sigChalQ_dsl_costUB sigChalQ_dsl_queries_prim twoVarRen wDdh1Key wPrim1Key wSig1Key wsZero1Key)
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (bindV_costUB anyMV_queries bindV_queries bindV_queriesUB caseOptV_costUB caseOptV_queries caseOptV_queriesUB caseSumV_costUB caseSumV_queries caseSumV_queriesUB checkProvC_costUB checkProvC_primUB chooseInitRandC_chal chooseInitRandC_costUB chooseInitRandC_primUB computeOptPosInitC_chal computeOptPosInitC_costUB computeOptPosInitC_primUB computePosC_chal computePosC_costUB computePosC_primUB eAny_costUB eCaseOpt_costUB eCaseSum_costUB eFind_costUB eLet_costUB encEC_costUB encKEM_costUB eqB_costUB fgKeyIndGapDhProg_totalChalQueries_eq fgKeyIndGapDhProg_totalChalQueries_le fgPatchC_chal fgPatchC_costUB fgPatchC_primUB findHonestC_costUB findHonestC_primUB gPrim_costUB gPrim_queriesUB_wPrimGdh gPrim_queries_wDdhGdh gPrim_queries_wPrimGdh gdhFinish_chalQueries gdhFinish_cost_le gdhFinish_primQueries_le gdhHandle_cost_le gdhHandle_primQueries_le honestPeerC_costUB honestPeerC_primUB koskBundleOkPowsC_costUB koskBundleOkPowsC_primUB letV_costUB findMV_queries foldMV_queries letV_queries mapMV_queries letV_queriesUB litB_costUB lookupSpkSkC_costUB lookupSpkSkC_primUB paDhFlag_costUB paEphIdx_costUB paOpkIdx_costUB paOpkMode_costUB paPrinFlag_costUB paPrinIdx_costUB paSpkIdx_costUB paU_costUB paUp_costUB paV_costUB qKemEncaps_costUB qKemEncaps_queriesUB qKemKeyGen_costUB qKemKeyGen_queriesUB qSigSign_costUB qSigSign_queriesUB qSigVerify_costUB qSigVerify_queriesUB qX25519Base_costUB qX25519Base_queriesUB rBundle_costUB rHdr_costUB rInitPrin_costUB rInitUnfresh_costUB rNone_costUB rPk_costUB resolveSigPkC_costUB resolveSigPkC_primUB sBool_costUB sBytes32_costUB sBytes32_queries sBytes32_queriesUB sIndex_costUB sRandom64_costUB sRandom64_queries sRandom64_queriesUB smBase_costUB smFgL_costUB smLog_costUB smPows_costUB smRaw_costUB u32OfNat_costUB v_costUB wPrimGdh wsZero)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveBounds

public section
private abbrev lcSigW := SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
private abbrev lcDdhW := SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
private abbrev lcPrimW := SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight (C := sigAndDdhOracle)
private abbrev lcPrimIfaceW := SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
private abbrev lcZeroWS := SignalPqxdh.LegacyCosted.samplerZeroQueryWeight

section LocalHeadlineShim
open _root_.ReductionDsl (pqAtomicOps pqAtomicSamplers pqAtomicSig)
open _root_.SignalPqxdh.Security (GRed2BlockBounded GRedBlockBounded PqOpsSizeHonest PqSampSizeHonest)
open _root_.Computational.Proofs.ReductionDsl.AtomicSizeHonest (pqAtomicOps_sizeHonest pqAtomicSamplers_sizeHonest)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (gred2BlockBounded_atomic_of_totalCost_le gredBlockBounded_atomic_of_totalCost_le one_le_pqAtomicSamplers_sCost)

private def zPrimWS : SignalPqxdh.LegacyCosted.pqPrimIface.smp.Samp → Nat := fun _ => 0
private def zGapDhW : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → Nat := tlGapDhKeyInd.unsupportedW
private def zGapDhWS : SignalPqxdh.LegacyCosted.pqGapDhIface.smp.Samp → Nat := fun _ => 0

private theorem pqOpsSizeHonest : PqOpsSizeHonest pqAtomicOps :=
  pqAtomicOps_sizeHonest

private theorem pqSampSizeHonest : PqSampSizeHonest pqAtomicSamplers :=
  pqAtomicSamplers_sizeHonest

private theorem gredBlockBounded_of_cost {ι κ : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqAtomicSig T} {G : OracleSpec κ}
    {C : _root_.ReductionDsl.GameCodec pqAtomicSig G}
    {rIn out : _root_.ReductionDsl.Ty pqAtomicSig}
    (hqCost : ∀ g, 1 ≤ I.qCost g) (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : CostedReduction pqAtomicOps I G C rIn .unit .bool out)
    (hsmp : I.smp = pqAtomicSamplers)
    (hCost : R.totalCost b.q_total ≤ _root_.SignalPqxdh.Security.stepCostBudget S b)
    (hSize : R.size ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b)) :
    GRedBlockBounded S b ℓ R :=
  gredBlockBounded_atomic_of_totalCost_le (hsmp ▸ pqAtomicSamplers_sizeHonest) hqCost
    (hsmp ▸ one_le_pqAtomicSamplers_sCost) S b ℓ R hCost hSize

private theorem gred2BlockBounded_of_cost {ι κ : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqAtomicSig T} {G : OracleSpec κ}
    {C : _root_.ReductionDsl.GameCodec pqAtomicSig G}
    {rIn ch rIn2 out : _root_.ReductionDsl.Ty pqAtomicSig}
    (hqCost : ∀ g, 1 ≤ I.qCost g) (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : TwoStageCostedReduction pqAtomicOps I G C rIn .unit .bool ch rIn2 out)
    (hsmp : I.smp = pqAtomicSamplers)
    (hCost : R.totalCost b.q_total ≤ _root_.SignalPqxdh.Security.stepCostBudget S b)
    (hSize : R.size ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b)) :
    GRed2BlockBounded S b ℓ R :=
  gred2BlockBounded_atomic_of_totalCost_le (hsmp ▸ pqAtomicSamplers_sizeHonest) hqCost
    (hsmp ▸ one_le_pqAtomicSamplers_sCost) S b ℓ R hCost hSize

end LocalHeadlineShim

section LocalUnsupHelpers
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (genOpkB initPrinB registerB revealDhB roB shcrAcceptB shcrExtractC shcrInitiateC shcrResumeC)
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle sigAndDdhOracle pqSamplers
attribute [local simp] letV_queries bindV_queries caseOptV_queries caseSumV_queries findMV_queries anyMV_queries mapMV_queries foldMV_queries
@[simp] private theorem sBool_unsup {Γ : List PT} : (sBool (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem sBytes32_unsup {Γ : List PT} : (sBytes32 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem sRandom64_unsup {Γ : List PT} : (sRandom64 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem sDrKey96_unsup {Γ : List PT} : (sDrKey96 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} : (sIndex N (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qX25519_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) : (qX25519 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qX25519Base_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qX25519Base e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qPow8_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qPow8 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qIsCanonical_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qIsCanonical e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qSigPkGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qSigPkGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qSigSign_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigSign m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qSigVerify_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigVerify m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qKemKeyGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) : (qKemKeyGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qKemEncaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) : (qKemEncaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qKemDecaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) : (qKemDecaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem qHkdfDerive96_unsup (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) : (qHkdfDerive96 w e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem gPrim_unsup {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries zGapDhW zGapDhWS = c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold gPrim; induction c with | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]
@[simp] private theorem ddhQ_unsup {Γ : List PT} (x y z : Expr pqxdhOps Γ (B 32)) : (ddhQ x y z).queries zGapDhW zGapDhWS = 0 := rfl
@[simp] private theorem findHonestC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [findHonestC, Comp.queries]
@[simp] private theorem isAdvRegC_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isAdvRegC, Comp.queries]
@[simp] private theorem isGameSpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameSpkC, Comp.queries]
@[simp] private theorem isGameOpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameOpkC, Comp.queries]
@[simp] private theorem koskBundleOkC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskBundleOkC, Comp.queries]
@[simp] private theorem koskSenderOkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskSenderOkC, Comp.queries]
@[simp] private theorem resolveSigPkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [resolveSigPkC, Comp.queries]
@[simp] private theorem honestPeerC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [honestPeerC, Comp.queries]
@[simp] private theorem checkProvC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [checkProvC, Comp.queries]
@[simp] private theorem partnerC_unsup {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem recordRespC_unsup (S : Setup) (K : Nat) {Δ : List PT} (p : Expr pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) :
    (recordRespC S K p).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [recordRespC, Comp.queries]
@[simp] private theorem hkdfOrRoC_true_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K true st sec).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [hkdfOrRoC, Comp.queries]
@[simp] private theorem hkdfOrRoC_false_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K false st sec).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [hkdfOrRoC, Comp.queries]
@[simp] private theorem acceptKeysC_unsup {Δ : List PT} (inp : Expr pqxdhOps Δ accInpTy) :
    (acceptKeysC inp).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] private theorem initFinishC_true_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (bu : Var Γ₃ bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (B 32)) (sc : Var Γ₆ (.prod (B 32) (B 1568))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [initFinishC, Comp.queries]
@[simp] private theorem preCheckC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (u : Var Γ₃ .nat) (bu : Var Γ₄ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [preCheckC, Comp.queries]
@[simp] private theorem checkSigsC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [checkSigsC, Comp.queries]
@[simp] private theorem onBase_unsup {Γ₁ Δ : List PT} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) → Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    (onBase (Δ := Δ) s br).queries keyIndUnsupportedPrimW zPrimWS = (br .zero).queries keyIndUnsupportedPrimW zPrimWS := by simp [onBase, Comp.queries]
@[simp] private theorem koskSenderOkPowsC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32)))) (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskSenderOkPowsC, Comp.queries]
@[simp] private theorem koskBundleOkPowsC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32)))) (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskBundleOkPowsC, Comp.queries]
@[simp] private theorem lookupSpkSkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32)))) (spkPk : Expr pqxdhOps Δ (B 32)) :
    (lookupSpkSkC S K st pows spkPk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [lookupSpkSkC, Comp.queries]
@[simp] private theorem chooseRespRandC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queries zGapDhW zGapDhWS = 0 := by simp [chooseRespRandC, Comp.queries]
@[simp] private theorem chooseInitRandC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queries zGapDhW zGapDhWS = 0 := by simp [chooseInitRandC, Comp.queries]
@[simp] private theorem mkSecretPosC_unsup {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) : (mkSecretPosC z).queries zGapDhW zGapDhWS = 0 := by simp [mkSecretPosC, Comp.queries]
@[simp] private theorem mkPairPosC_unsup {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) : (mkPairPosC pk1 pk2).queries zGapDhW zGapDhWS = 0 := by simp [mkPairPosC, Comp.queries]
@[simp] private theorem computePosC_unsup {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) : (computePosC sk1 sk2 pk1 pk2).queries zGapDhW zGapDhWS = 0 := by simp [computePosC, Comp.queries]
@[simp] private theorem computeOptPosInitC_unsup {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32)) (opkB? : Expr pqxdhOps Γ (.opt (.prod SignalPqxdh.LegacyCosted.U32 (B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queries zGapDhW zGapDhWS = 0 := by simp [computeOptPosInitC, Comp.queries]
@[simp] private theorem ddhEqC_unsup {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) : (ddhEqC p1 p2).queries zGapDhW zGapDhWS = 0 := by simp [ddhEqC, Comp.queries]
@[simp] private theorem ddhEqOptC_unsup {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) : (ddhEqOptC p1? p2?).queries zGapDhW zGapDhWS = 0 := by simp [ddhEqOptC, Comp.queries]
@[simp] private theorem entryMatchesC_unsup {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy) (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queries zGapDhW zGapDhWS = 0 := by simp [entryMatchesC, Comp.queries]
@[simp] private theorem fgPatchC_unsup (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy) (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queries zGapDhW zGapDhWS = 0 := by simp [fgPatchC, Comp.queries]

private theorem shcrKeyIndProg_resume_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).resume.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyIndProg S Q K).resume.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrKeyIndProg, shcrResumeC, letV, bindV, initFinishC_true_unsup, Comp.queries]

private theorem shcrKeyIndProg_finish_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).finish.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyIndProg S Q K).finish.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrKeyIndProg, shcrExtractC, Comp.queries]

private theorem shcrPostC_unsupported (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, shcrPostC, shcrGenSpkB, shcrInitiateC, shcrAcceptB,
    initPrinB, corruptB, genSpkB, genOpkB, acceptOpkB, acceptNoOpkB, testB, revealB, roB,
    revealDhB, registerB, revealSpkB, Comp.queries]

private theorem shcrKeyIndProg_handlePost_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcrPostC_unsupported S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

private theorem shcrKeyIndProg_handlePre_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePre.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrPreC, pauseCheckC, tryPauseC, shcrPostC_unsupported, Comp.queries]

private theorem gdhFinish_unsupported (S : Setup) (K : Nat) :
    (gdhFinish S K).queries zGapDhW zGapDhWS = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, gdhFinish, extractMode0C, logFindC, spkPowsC,
    findMapStepC, initDh1CandC, respDh1CandC, Comp.queries]

end LocalUnsupHelpers

section InitParamsHelpers
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle sigAndDdhOracle pqSamplers
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (initParams1KeyActiveC)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (bernoulliRatioGdhC chooseArm2C)

private theorem act_bernoulliRatioGdhC_queries_zero {Δ : List PT}
    (w : pqGapDhIface.Tag → ℕ) (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries w (fun _ => 0) = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [bindV, gPrim, liftBase, sIndex, Comp.queries]

private theorem act_chooseArm2C_queries_zero {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w : pqGapDhIface.Tag → ℕ) (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries w (fun _ => 0) = 0)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries w (fun _ => 0) = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries w (fun _ => 0) = 0 := by
  unfold chooseArm2C
  split_ifs
  · exact hc2
  · exact hc1
  · simp [bindV, act_bernoulliRatioGdhC_queries_zero, hc1, hc2, Comp.queries]

private theorem initParams1KeyActiveC_queries_zero (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32)))
    (w : pqGapDhIface.Tag → ℕ) :
    (initParams1KeyActiveC S b (Δ := Δ) uv).queries w (fun _ => 0) = 0 := by
  unfold initParams1KeyActiveC
  dsimp only
  by_cases h0 : fgActiveTotalIndexCount S b.q_on = 0
  · simp only [h0, ↓reduceIte]; rfl
  · simp only [h0, ↓reduceIte]
    refine act_chooseArm2C_queries_zero w _ _ _ _
      (fun {Δ'} [_] => act_chooseArm2C_queries_zero w _ _ _ _
        (fun {Δ''} [_] => by
          by_cases hA : activeIdCount S b.q_on * activeSpkCount S b.q_on = 0 <;>
            simp [hA, bindV, gPrim, liftBase, sIndex, Comp.queries])
        (fun {Δ''} [_] => by
          by_cases hC : activeSendCount S b.q_on * activeSpkCount S b.q_on = 0 <;>
            simp [hC, bindV, gPrim, liftBase, sIndex, Comp.queries]))
      (fun {Δ'} [_] => act_chooseArm2C_queries_zero w _ _ _ _
        (fun {Δ''} [_] => by
          by_cases hB : activeSendCount S b.q_on * activeIdCount S b.q_on = 0 <;>
            simp [hB, bindV, gPrim, liftBase, sIndex, Comp.queries])
        (fun {Δ''} [_] => by
          by_cases hD : activeSendOpkCount S b.q_on * activeOpkCount S b.q_on = 0 <;>
            simp [hD, bindV, gPrim, liftBase, sIndex, Comp.queries]))

private theorem act_bernoulliRatioGdhC_cost_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).cost ≤ 3 * bits (A + B) + 25 := by
  refine (bernoulliRatioGdhC (Δ := Δ) A B).cost_le_costUB.trans ?_
  unfold bernoulliRatioGdhC
  split_ifs with hA hB hAB
  · simp [Comp.costUB, Expr.costUB]
  · simp [Comp.costUB, Expr.costUB]
  · have hb : bits A ≤ bits (A + B) := _root_.ReductionDsl.bits_mono (Nat.le_add_right A B)
    simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    omega
  · have hb : bits B ≤ bits (A + B) := _root_.ReductionDsl.bits_mono (Nat.le_add_left B A)
    simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    omega

private theorem act_chooseArm2C_cost_le {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
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

end InitParamsHelpers

section Unsupported
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle sigAndDdhOracle pqSamplers
private def zSigDdhW : pqSigAndDdhIface.Tag → ℕ := tlSigDdhKeyInd.unsupportedW
private def zSigDdhWS : pqSigAndDdhIface.smp.Samp → ℕ := fun _ => 0

@[simp] private theorem s1Prim_unsupported {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) : (s1Prim
  c).queries zSigDdhW zSigDdhWS = c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold s1Prim; induction c with
  | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]

@[simp] private theorem qSigDdhSign_unsupported (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) : (qSigDdhSign m
  msg).queries zSigDdhW zSigDdhWS = 0 := rfl

@[simp] private theorem sigChalQ_dsl_unsupported (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) : (sigChalQ_dsl m
  msg).queries zSigDdhW zSigDdhWS = 0 := rfl

@[simp] private theorem liftGdhToSigDdh_unsupported {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t) :
  (liftGdhToSigDdh c).queries zSigDdhW zSigDdhWS = c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[simp] private theorem liftGdhComp_unsupported {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t) :
  (liftGdhComp c).queries zSigDdhW zSigDdhWS = c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl | _ => simp_all [liftGdhComp, Comp.queries]

@[local simp] private theorem wrapBase2_unsupported {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.wrapBase2 pa sm c).queries zGapDhW zGapDhWS =
      c.queries keyIndUnsupportedPrimW zPrimWS := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.wrapBase2, bindV, Comp.queries]

@[local simp] private theorem wrapSim2_unsupported {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2 pa c).queries zGapDhW zGapDhWS =
      c.queries zGapDhW zGapDhWS := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2, bindV, Comp.queries]

private theorem gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).queries zGapDhW zGapDhWS = 0 := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2,
    SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.genSpkGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.genOpkGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdh2B,
    acceptNoOpkGdhB, finishAcceptGdhC, corruptB, testB, roParsedC, roRawFallbackC,
    revealB, registerGdhB, revealSpkB, letV, bindV, caseOptV, caseSumV, Comp.queries]

theorem sigActive_init_unsupported (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S b).init.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sigKeyInd1KeyActiveDslProg S b).init.queries zSigDdhW zSigDdhWS = 0
  simp [sigKeyInd1KeyActiveDslProg, bindV, Comp.queries]

theorem sigActive_finish_unsupported (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S b).finish.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

theorem sigActive_handle_unsupported (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S b).handle.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyActiveHandleC S b.q_total).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S b.q_total).queries zGapDhW zGapDhWS = 0 :=
    gdhHandle2_unsupported S b.q_total
  simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyActiveInitiateCheckC, extract1KeyActiveC, ReductionDsl.Comp.rename_queries, hGdh,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

theorem sigActive_unsupported (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S b).init.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) + (sigKeyInd1KeyActiveDslProg S b).handle.queries tlSigDdhKeyInd.unsupportedW
  (fun _ => 0) + (sigKeyInd1KeyActiveDslProg S b).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  rw [sigActive_init_unsupported, sigActive_handle_unsupported, sigActive_finish_unsupported]

theorem shcrActive_init_unsupported (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S b).init.queries
  tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyInd1KeyActiveDslProg S b).init.queries keyIndUnsupportedPrimW zPrimWS = 0
  dsimp only [shcrKeyInd1KeyActiveDslProg]
  split_ifs <;> simp [bindV, Comp.queries]

theorem shcrActive_chDone_unsupported (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S b).chDone.queries
  tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

theorem shcrActive_resume_unsupported (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S b).resume.queries
  tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := shcrKeyIndProg_resume_unsupported S b.q_total (keyIndLoopBound b)

theorem shcrActive_finish_unsupported (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S b).finish.queries
  tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := shcrKeyIndProg_finish_unsupported S b.q_total (keyIndLoopBound b)

private theorem initPrin1KeyB_prim_unsupported (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂
  .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (initPrin1KeyB (Δ := Δ) K st u).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [initPrin1KeyB, bindV, Comp.queries]

private theorem shcrGenSpkB_prim_unsupported (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ shcrStTy) (x : Var Γ₂
  (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (shcrGenSpkB (Δ := Δ) S K s x).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [shcrGenSpkB, genSpkB, onBase, letV, bindV, caseOptV, Comp.queries]

private theorem shcrActiveGenSpkB_prim_unsupported (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ shcrStTy) (x :
  Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (shcrActiveGenSpkB (Δ := Δ) S K s x).queries keyIndUnsupportedPrimW
  zPrimWS = 0 := by
  simp [shcrActiveGenSpkB, genSpkB, onBase, letV, bindV, caseOptV, Comp.queries]

private theorem shcrActivePostTailC_eq_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (s : Var Γ shcrStTy) [Ext Γ Δ] (q : Var (keyIndQueryRestTy :: Δ) keyIndQueryRestTy)
    (h2 : (shcrPostTailC S K (Δ := Δ) s q).queries keyIndUnsupportedPrimW zPrimWS = 0) :
    (shcrActivePostTailC S K (Δ := Δ) s q).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  unfold shcrPostTailC at h2; unfold shcrActivePostTailC
  simp only [caseSumV, shcrGenSpkB_prim_unsupported, shcrActiveGenSpkB_prim_unsupported, Comp.queries] at h2 ⊢; omega

theorem shcrActive_handlePost_unsupported (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S
  b).handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have h2 := shcrKeyIndProg_handlePost_unsupported S b.q_total (keyIndLoopBound b)
  dsimp only [shcrKeyIndProg, shcrKeyInd1KeyActiveDslProg, keyIndCodec] at h2 ⊢
  change (shcrPostC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy,
    keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0 at h2
  change (shcr1KeyActivePostC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ :=
    [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0
  rw [shcrPostC_eq_tail] at h2; unfold shcr1KeyActivePostC
  simp only [caseSumV, onBase, letV, bindV, initPrin1KeyB_prim_unsupported, Comp.queries] at h2 ⊢
  have hTail : (shcrPostTailC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0 := by omega
  have hAct := shcrActivePostTailC_eq_queries S (keyIndLoopBound b) (Γ := [shcrStTy, keyIndQueryTy]) (Δ := [shcrStTy,
    keyIndQueryTy]) .zero .zero hTail
  omega

theorem shcrActive_handlePre_unsupported (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S
  b).handlePre.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have h2 := shcrKeyIndProg_handlePre_unsupported S b.q_total (keyIndLoopBound b)
  dsimp only [shcrKeyIndProg, shcrKeyInd1KeyActiveDslProg, keyIndCodec] at h2 ⊢
  change (shcrPreC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy,
    keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0 at h2
  change (shcr1KeyActivePreC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ :=
    [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0
  unfold shcrPreC at h2; unfold shcr1KeyActivePreC; rw [shcrPostC_eq_tail] at h2; unfold shcr1KeyActivePostC
  simp only [letV, bindV, caseOptV, caseSumV, onBase, initPrin1KeyB_prim_unsupported, Comp.queries] at h2 ⊢
  have hTail : (shcrPostTailC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Δ := (.opt pauseTy) :: [shcrStTy, keyIndQueryTy]) .zero .zero).queries
      keyIndUnsupportedPrimW zPrimWS = 0 := by omega
  have hAct := shcrActivePostTailC_eq_queries S (keyIndLoopBound b) (Γ := [shcrStTy, keyIndQueryTy]) (Δ := (.opt
    pauseTy) :: [shcrStTy, keyIndQueryTy]) .zero .zero hTail
  omega

theorem shcrActive_unsupported (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S b).init.queries
  tlPrimKeyInd.unsupportedW (fun _ => 0) + (shcrKeyInd1KeyActiveDslProg S b).handlePre.queries tlPrimKeyInd.unsupportedW
  (fun _ => 0) + (shcrKeyInd1KeyActiveDslProg S b).chDone.queries tlPrimKeyInd.unsupportedW (fun _ => 0) +
  (shcrKeyInd1KeyActiveDslProg S b).resume.queries tlPrimKeyInd.unsupportedW (fun _ => 0) + (shcrKeyInd1KeyActiveDslProg
  S b).handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) + (shcrKeyInd1KeyActiveDslProg S b).finish.queries
  tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  rw [shcrActive_init_unsupported, shcrActive_handlePre_unsupported, shcrActive_chDone_unsupported,
    shcrActive_resume_unsupported, shcrActive_handlePost_unsupported, shcrActive_finish_unsupported]

theorem gdhActive_init_unsupported (S : Setup) (b : QueryBudget) : (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries zSigDdhW zSigDdhWS = 0
  have hP : (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initParams1KeyActiveC S b
      (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
      (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero).queries zGapDhW zGapDhWS = 0 :=
    initParams1KeyActiveC_queries_zero S b .zero zGapDhW
  simp [fgKeyInd1KeyGapDhActiveDslProg, hP, letV, bindV, Comp.queries]

theorem gdhActive_handle_unsupported (S : Setup) (b : QueryBudget) : (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyActiveHandle S b.q_total).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S b.q_total).queries zGapDhW zGapDhWS = 0 :=
    gdhHandle2_unsupported S b.q_total
  simp [gdh1KeyActiveHandle, initPrin1KeyActiveGdhB, callGdhActiveHandle, renameComp_queries, genSpk1KeyActiveGdhB,
    genSpkGdhActiveB, genOpkActiveGdhB, initiateActiveGdhB, initiateGdhActiveInnerB, hGdh, letV, bindV, caseOptV,
    caseSumV, Comp.queries]

theorem gdhActive_finish_unsupported (S : Setup) (b : QueryBudget) : (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyActiveFinish S b.q_total).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (gdhFinish S b.q_total).queries zGapDhW zGapDhWS = 0 := gdhFinish_unsupported S b.q_total
  simp [gdh1KeyActiveFinish, hGdh, letV, Comp.queries]

theorem gdhActive_unsupported (S : Setup) (b : QueryBudget) : (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) + (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) + (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries
  tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  rw [gdhActive_init_unsupported, gdhActive_handle_unsupported, gdhActive_finish_unsupported]

end Unsupported

section SigActiveR64
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle sigAndDdhOracle pqSamplers
private def zPrim0W : pqPrimIface.Tag → ℕ := fun _ => 0
private def zGdh0W : pqGapDhIface.Tag → ℕ := fun _ => 0
private def zSigDdh0W : pqSigAndDdhIface.Tag → ℕ := fun _ => 0
private def kiR64WS : PSamp → ℕ := r64W
@[simp] private theorem sBool_r64 {Γ} : (sBool (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem sBytes32_r64 {Γ} : (sBytes32 (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem sRandom64_r64 {Γ} : (sRandom64 (Γ := Γ)).queries zPrim0W kiR64WS = 1 := rfl
@[simp] private theorem sIndex_r64 (N : ℕ) {Γ} : (sIndex N (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qX25519Base_r64 {Γ} (e : Expr pqxdhOps Γ (B 32)) : (qX25519Base e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qPow8_r64 {Γ} (e : Expr pqxdhOps Γ (B 32)) : (qPow8 e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qIsCanonical_r64 {Γ} (e : Expr pqxdhOps Γ (B 32)) : (qIsCanonical e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qSigVerify_r64 (m : ℕ+) {Γ} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qKemKeyGen_r64 {Γ} (e : Expr pqxdhOps Γ (B 64)) : (qKemKeyGen e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qSigDdhSign_r64 (m : ℕ+) {Γ} (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).queries zSigDdh0W kiR64WS = 0 := rfl

@[simp] private theorem s1Prim_r64 {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queries zSigDdh0W kiR64WS = c.queries zPrim0W kiR64WS := by
  unfold s1Prim; induction c with
  | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]

@[simp] private theorem liftGdhToSigDdh_r64 {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries zSigDdh0W kiR64WS = c.queries zGdh0W kiR64WS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[simp] private theorem findHonestC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries zPrim0W kiR64WS = 0 := by simp [findHonestC, letV, findMV, bindV, Comp.queries]

@[simp] private theorem isAdvRegC_r64 (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).queries zPrim0W kiR64WS = 0 := by simp [isAdvRegC, bindV, Comp.queries]

@[simp] private theorem honestPeerC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).queries zPrim0W kiR64WS = 0 := by simp [honestPeerC, bindV, Comp.queries]

@[simp] private theorem comp_rename_queries_gdh :
    ∀ {Γ Δ : List PT} {t : PT} (f : ∀ {τ}, Var Γ τ → Var Δ τ)
      (c : Comp pqxdhOps pqGapDhIface Γ t), (Comp.rename f c).queries zGdh0W kiR64WS = c.queries zGdh0W kiR64WS
  | _, _, _, _, .ret _ | _, _, _, _, .sample _ _ | _, _, _, _, .query _ _ => rfl
  | _, _, _, f, .bind c k => by simp [Comp.rename, Comp.queries, comp_rename_queries_gdh f c, comp_rename_queries_gdh _ k]
  | _, _, _, f, .ite _ c d => by simp [Comp.rename, Comp.queries, comp_rename_queries_gdh f c, comp_rename_queries_gdh f d]
  | _, _, _, f, .caseOpt _ n s => by simp [Comp.rename, Comp.queries, comp_rename_queries_gdh f n, comp_rename_queries_gdh _ s]
  | _, _, _, f, .caseSum _ l r => by simp [Comp.rename, Comp.queries, comp_rename_queries_gdh _ l, comp_rename_queries_gdh _ r]
  | _, _, _, _, .iter _ _ body => by simp [Comp.rename, Comp.queries, comp_rename_queries_gdh _ body]
  | _, _, _, _, .findM _ _ p | _, _, _, _, .anyM _ _ p | _, _, _, _, .mapM _ _ p
  | _, _, _, _, .consumeFirstM _ _ p _ | _, _, _, _, .foldM _ _ _ p => by
    simp [Comp.rename, Comp.queries, comp_rename_queries_gdh _ p]

@[local simp] private theorem sDrKey96_r64 {Γ : List PT} : (sDrKey96 (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem qX25519_r64 {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem qSigPkGen_r64 {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem qSigSign_r64 (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem qKemEncaps_r64 {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem qKemDecaps_r64 {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem qHkdfDerive96_r64 (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) :
    (qHkdfDerive96 w e).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem gPrim_r64 {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries zGdh0W kiR64WS = c.queries zPrim0W kiR64WS := by
  unfold gPrim; induction c with
  | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]
@[local simp] private theorem ddhQ_r64 {Γ : List PT} (x y z : Expr pqxdhOps Γ (B 32)) :
    (ddhQ x y z).queries zGdh0W kiR64WS = 0 := rfl
@[local simp] private theorem isGameSpkC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queries zPrim0W kiR64WS = 0 := by
  simp [isGameSpkC, letV, anyMV, bindV, Comp.queries]
@[local simp] private theorem isGameOpkC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queries zPrim0W kiR64WS = 0 := by
  simp [isGameOpkC, letV, anyMV, bindV, Comp.queries]
@[local simp] private theorem resolveSigPkC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).queries zPrim0W kiR64WS = 0 := by
  simp [resolveSigPkC, letV, bindV, Comp.queries]
@[local simp] private theorem checkProvC_r64 (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).queries zPrim0W kiR64WS = 0 := by
  simp [checkProvC, bindV, letV, caseOptV, anyMV, Comp.queries]
@[local simp] private theorem partnerC_r64 {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).queries zPrim0W kiR64WS = 0 := rfl
@[local simp] private theorem koskSenderOkPowsC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries zPrim0W kiR64WS = 0 := by
  simp [koskSenderOkPowsC, letV, bindV, Comp.queries]
@[local simp] private theorem koskBundleOkPowsC_r64 (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32)))) (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).queries zPrim0W kiR64WS = 0 := by
  simp [koskBundleOkPowsC, letV, bindV, caseOptV, Comp.queries]
@[local simp] private theorem lookupSpkSkC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (spkPk : Expr pqxdhOps Δ (B 32)) :
    (lookupSpkSkC S K st pows spkPk).queries zPrim0W kiR64WS = 0 := by
  simp [lookupSpkSkC, letV, bindV, findMV, Comp.queries]
@[local simp] private theorem chooseRespRandC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queries zGdh0W kiR64WS = 0 := by
  simp [chooseRespRandC, bindV, caseOptV, findMV, Comp.queries]
@[local simp] private theorem chooseInitRandC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queries zGdh0W kiR64WS = 0 := by
  simp [chooseInitRandC, bindV, caseOptV, findMV, Comp.queries]
@[local simp] private theorem mkSecretPosC_r64 {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) :
    (mkSecretPosC z).queries zGdh0W kiR64WS = 0 := by
  simp [mkSecretPosC, letV, bindV, Comp.queries]
@[local simp] private theorem mkPairPosC_r64 {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (mkPairPosC pk1 pk2).queries zGdh0W kiR64WS = 0 := by
  simp [mkPairPosC, letV, bindV, Comp.queries]
@[local simp] private theorem computePosC_r64 {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (computePosC sk1 sk2 pk1 pk2).queries zGdh0W kiR64WS = 0 := by
  simp [computePosC, bindV, Comp.queries]
@[local simp] private theorem computeOptPosInitC_r64 {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod SignalPqxdh.LegacyCosted.U32 (B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queries zGdh0W kiR64WS = 0 := by
  simp [computeOptPosInitC, letV, caseOptV, bindV, Comp.queries]
@[local simp] private theorem ddhEqC_r64 {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).queries zGdh0W kiR64WS = 0 := by
  simp [ddhEqC, letV, caseSumV, Comp.queries]
@[local simp] private theorem ddhEqOptC_r64 {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).queries zGdh0W kiR64WS = 0 := by
  simp [ddhEqOptC, letV, caseOptV, Comp.queries]
@[local simp] private theorem entryMatchesC_r64 {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queries zGdh0W kiR64WS = 0 := by
  simp [entryMatchesC, bindV, Comp.queries]
@[local simp] private theorem fgPatchC_r64 (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queries zGdh0W kiR64WS = 0 := by
  simp [fgPatchC, letV, bindV, findMV, caseOptV, Comp.queries]
@[local simp] private theorem roRawFallbackC_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (B 192)) :
    (roRawFallbackC (Δ := Δ) K sm sec).queries zGdh0W kiR64WS = 0 := by
  simp [roRawFallbackC, bindV, caseOptV, Comp.queries]
@[local simp] private theorem roParsedC_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (B 192)) :
    (roParsedC (Δ := Δ) K sm sec).queries zGdh0W kiR64WS = 0 := by
  simp [roParsedC, letV, bindV, Comp.queries]
@[local simp] private theorem finishAcceptGdhC_r64 (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod SignalPqxdh.LegacyCosted.U32
      (.prod SignalPqxdh.LegacyCosted.U32 (B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    (finishAcceptGdhC (Δ := Δ) S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).queries
      zGdh0W kiR64WS = 0 := by
  simp [finishAcceptGdhC, letV, bindV, Comp.queries]
@[local simp] private theorem acceptNoOpkGdhB_r64 (S : Setup) (K : Nat) {Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (x : Var Γ₄ accQTy) :
    (acceptNoOpkGdhB (Δ := Δ) S K sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [acceptNoOpkGdhB, letV, bindV, caseOptV, Comp.queries]
@[local simp] private theorem registerGdhB_r64 {Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (sk : Var Γ₄ (B 32)) :
    (registerGdhB (Δ := Δ) sm bSt sk).queries zGdh0W kiR64WS = 0 := by
  simp [registerGdhB, bindV, Comp.queries]
@[local simp] private theorem wrapBase2_r64 {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.wrapBase2 pa sm c).queries zGdh0W kiR64WS =
      c.queries zPrim0W kiR64WS := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.wrapBase2, bindV, Comp.queries]
@[local simp] private theorem wrapSim2_r64 {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2 pa c).queries zGdh0W kiR64WS =
      c.queries zGdh0W kiR64WS := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2, bindV, Comp.queries]
@[local simp] private theorem initPrinGdh2B_r64 (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty) (sm : Var Γ₂ simTy)
    (bSt : Var Γ₃ keyIndStateTy) (u : Var Γ₄ .nat) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinGdh2B (Δ := Δ) K pa sm bSt u).queries zGdh0W kiR64WS = 0 := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinGdh2B, letV, bindV, Comp.queries]
@[local simp] private theorem genSpkGdh2B_r64 (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty) (sm : Var Γ₂ simTy)
    (bSt : Var Γ₃ keyIndStateTy) (x : Var Γ₄ (.prod .nat .nat)) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.genSpkGdh2B (Δ := Δ) K pa sm bSt x).queries zGdh0W kiR64WS = 3 := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.genSpkGdh2B, letV, bindV, caseOptV, Comp.queries]
@[local simp] private theorem genOpkGdh2B_r64 (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty) (sm : Var Γ₂ simTy)
    (bSt : Var Γ₃ keyIndStateTy) (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.genOpkGdh2B (Δ := Δ) K pa sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.genOpkGdh2B, letV, bindV, Comp.queries]
@[local simp] private theorem initiateGdh2B_r64 (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty) (sm : Var Γ₂ simTy)
    (bSt : Var Γ₃ keyIndStateTy) (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B (Δ := Δ) S K pa sm bSt hasOpk x).queries zGdh0W kiR64WS = 0 := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B, letV, bindV, caseOptV, Comp.queries]
@[local simp] private theorem acceptOpkGdh2B_r64 (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty) (sm : Var Γ₂ simTy)
    (bSt : Var Γ₃ keyIndStateTy) (x : Var Γ₄ accQTy) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdh2B (Δ := Δ) S K pa sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdh2B, letV, bindV, caseOptV, Comp.queries]

private theorem gdhHandle2_r64_le (S : Setup) (K : Nat) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).queries zGdh0W kiR64WS ≤ 3 := by
  simp [SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2, corruptB, testB, revealB, revealSpkB,
    letV, caseOptV, caseSumV, Comp.queries]

private theorem sigKeyInd1KeyActiveDslProg_r64_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).totalQueries (fun _ => 0) (sampR64W tlSigDdhKeyInd.hsmp) b.q_total ≤ 4 * b.q_total := by
  change (sigKeyInd1KeyActiveDslProg S b).totalQueries zSigDdh0W kiR64WS b.q_total ≤ 4 * b.q_total
  have hInit : (sigKeyInd1KeyActiveDslProg S b).init.queries zSigDdh0W kiR64WS = 0 := by
    simp [sigKeyInd1KeyActiveDslProg, bindV, Comp.queries]
  have hFin : (sigKeyInd1KeyActiveDslProg S b).finish.queries zSigDdh0W kiR64WS = 0 := rfl
  have hGdh := gdhHandle2_r64_le S b.q_total
  have hPre : ∀ {Γ₁ Γ₂ Δ} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy)
      (qv : Var Γ₂ keyIndQueryTy),
      (sig1KeyActivePreDispatchC S b.q_total (Δ := Δ) st qv).queries zSigDdh0W kiR64WS ≤ 1 := by
    intros; simp only [sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
      sig1KeyActiveInitiateCheckC, extract1KeyActiveC, s1Prim_r64, qSigDdhSign_r64, honestPeerC_r64,
      sBytes32_r64, sRandom64_r64, qX25519Base_r64, qKemKeyGen_r64, qSigVerify_r64,
      letV, bindV, caseOptV, caseSumV, Comp.queries]; omega
  have hH : (sigKeyInd1KeyActiveDslProg S b).handle.queries zSigDdh0W kiR64WS ≤ 4 := by
    dsimp only [sigKeyInd1KeyActiveDslProg, keyIndCodec, sig1KeyActiveHandleC]
    have hp := hPre (Γ₁ := [sig1KeyActiveStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyActiveStTy, keyIndQueryTy])
      (Δ := [sig1KeyActiveStTy, keyIndQueryTy]) .zero (.succ .zero)
    simp only [liftGdhToSigDdh_r64, comp_rename_queries_gdh, letV, bindV, caseSumV, Comp.queries]; omega
  unfold CostedReduction.totalQueries; rw [hInit, hFin]; have hMul := Nat.mul_le_mul_left b.q_total hH; omega

end SigActiveR64

section DslCostAndQueries
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] pqChalIface pqPrimIface gapDhDdhOracle sigAndDdhOracle pqSamplers
@[simp] private theorem optNatMatchesE_costUB {Γ : List PT} (tpOpt : Expr pqxdhOps Γ (.opt .nat)) (u : Expr pqxdhOps Γ
  .nat) : (optNatMatchesE tpOpt u).costUB = tpOpt.costUB + u.costUB + 14 := by
  simp only [optNatMatchesE, eLet2, eLet, eCaseOpt_costUB, natEq, v_costUB, Expr.costUB]

private theorem sigKeyInd1KeyActiveDslProg_sigQueries_le (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S
  b).totalQueries lcSigW lcZeroWS b.q_total ≤ 2 * b.q_total := by
  have hPre : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy)
      (q : Var Γ₂ keyIndQueryTy),
      (sig1KeyActivePreDispatchC S b.q_total (Δ := Δ) st q).queries lcSigW lcZeroWS = 2 := by
    intros; simp [sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
      sig1KeyActiveInitiateCheckC, extract1KeyActiveC, letV, Comp.queries]
  have hH : (sig1KeyActiveHandleC S b.q_total).queries lcSigW lcZeroWS = 2 := by
    simp [sig1KeyActiveHandleC, hPre, SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_sigQueries, letV, Comp.queries]
  dsimp only [CostedReduction.totalQueries, sigKeyInd1KeyActiveDslProg, keyIndCodec]
  rw [hH]; simp only [bindV_queries, s1Prim_sigQueries, Comp.queries]; omega

section
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (F_X25519_length acceptOpkGdh2B bits_32 ephSidMatchesE freshE gdhHandle2 genOpkGdh2B genSpkGdh2B initPrinGdh2B initiateGdh2B kyberCheckE kyberEq nonZero32 oeUpd optU32Eq pa2DhFlag pa2EphTarget pa2OpkMode pa2OpkTarget pa2PrinTarget pa2SpkTarget pa2U pa2Up pa2V params2Ty peUpd qKJO reMk reUpd rs sbUpd smBase wrapBase2 wrapSim2)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (bits_128 bits_160 bits_192 bits_64 bits_96 chooseRespRandC_primUB eMap_costUB eqU32_costUB finishAcceptGdhC_costUB koskSenderOkPowsC_costUB koskSenderOkPowsC_primUB lenB_costUB mkSecretPosC_costUB mkSecretPosC_primUB qHdr_costUB qIsCanonical_costUB qIsCanonical_queriesUB qJ_costUB qK_costUB qKemDecaps_costUB qKemDecaps_queriesUB qO_costUB qPow8_costUB qPow8_queriesUB qSigPkGen_costUB qSigPkGen_queriesUB qX25519_costUB qX25519_queriesUB rCorr_costUB rDrKey_costUB rSpkSk_costUB sDrKey96_costUB sDrKey96_queriesUB slice32_costUB takeKB_costUB wDdhGdh wPrimBase wsZeroBase)

@[local simp] private theorem loc_wrapBase2_chal {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries wDdhGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero = 0 := by
  simp [wrapBase2, Comp.queries]

@[local simp] private theorem loc_wrapSim2_chal {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries wDdhGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero =
      c.queries wDdhGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero := by
  simp [wrapSim2, Comp.queries]

@[local simp] private theorem loc_wrapBase2_primUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queriesUB wPrimGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero =
      c.queriesUB wPrimBase SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZeroBase := by
  simp [wrapBase2, bindV_queriesUB, gPrim_queriesUB_wPrimGdh, Comp.queriesUB]

@[local simp] private theorem loc_wrapSim2_primUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queriesUB wPrimGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero =
      c.queriesUB wPrimGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero := by
  simp [wrapSim2, bindV_queriesUB, Comp.queriesUB]

private theorem gdhHandle2_chalQueries_local (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries wDdhGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero = 4 * K := by
  simp [gdhHandle2, initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B,
    finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB, roParsedC, roRawFallbackC,
    registerGdhB, Comp.queries]

private theorem gdhHandle2_primUB_local (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queriesUB wPrimGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero =
      153 + 72 * (min K S.N_dh) + 16 * (min K S.N_sess_tot) := by
  simp only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    loc_wrapBase2_primUB, loc_wrapSim2_primUB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, koskBundleOkPowsC_primUB, koskSenderOkPowsC_primUB,
    resolveSigPkC_primUB, lookupSpkSkC_primUB, honestPeerC_primUB, checkProvC_primUB,
    findHonestC_primUB, chooseInitRandC_primUB, chooseRespRandC_primUB,
    computePosC_primUB, computeOptPosInitC_primUB, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519_queriesUB, qX25519Base_queriesUB, qIsCanonical_queriesUB, qPow8_queriesUB,
    qSigPkGen_queriesUB, qSigSign_queriesUB, qSigVerify_queriesUB,
    qKemKeyGen_queriesUB, qKemEncaps_queriesUB, qKemDecaps_queriesUB,
    Comp.queriesUB]
  ring

private theorem gdhHandle2_primQueries_le_local (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries wPrimGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero ≤
      153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB wPrimGdh SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wsZero (gdhHandle2 S K)
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  rw [gdhHandle2_primUB_local] at h; omega

private theorem k1_letV_gdh_cost_add_le {Γ : List PT} {τ₁ τ₂ : PT}
    (e : Expr pqxdhOps Γ τ₁) (he : e.cost ≤ 2)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    {d c : ℕ} (hk : (k .zero).cost + (d + 4) ≤ c) :
    (letV e k).cost + d ≤ c := by
  simp only [letV, Comp.cost]
  omega

private theorem k1_caseSumV_gdh_cost_add_le {Γ : List PT} {τ₁ τ₂ τ : PT}
    (x : Var Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqGapDhIface (τ₂ :: Γ) τ)
    {d c : ℕ} (hl : (kl .zero).cost + (d + 2) ≤ c) (hr : (kr .zero).cost + (d + 2) ≤ c) :
    (caseSumV (v x) kl kr).cost + d ≤ c := by
  simp only [caseSumV, v, Comp.cost, Expr.cost]
  omega

private theorem k1_arm_cost_le {Γ : List PT} {τ : PT}
    (m : Comp pqxdhOps pqGapDhIface Γ τ) {d c : ℕ}
    (hub : m.costUB + d ≤ c) : m.cost + d ≤ c :=
  (Nat.add_le_add_right m.cost_le_costUB d).trans hub

private theorem tk_wrapBase2_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

private theorem tk_wrapSim2_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := rfl

set_option maxRecDepth 100000 in
private theorem k1_gdhHandle2_cost_tight_loc (S : Setup) (K : Nat) :
    (gdhHandle2 S K).cost ≤
      20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30000 := by
  unfold gdhHandle2
  refine Nat.le_of_add_right_le (k := 0) ?_
  refine k1_letV_gdh_cost_add_le _ (by simp [v, Expr.cost]) _ ?_
  refine k1_letV_gdh_cost_add_le _ (by simp [v, Expr.cost]) _ ?_
  refine k1_letV_gdh_cost_add_le _ (by simp [smBase, v, Expr.cost]) _ ?_
  refine k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ ?_)))))))))))) <;> (
    refine k1_arm_cost_le _ ?_
    simp only [initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
      initiateGdh2B, finishAcceptGdhC_costUB, acceptOpkGdh2B, acceptNoOpkGdhB,
      testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
      tk_wrapBase2_costUB, tk_wrapSim2_costUB,
      pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag,
      pa2EphTarget, pa2SpkTarget, pa2OpkMode, pa2OpkTarget, ephSidMatchesE,
      stMk, stUpd, peMk, peUpd, sbMk, sbUpd, oeMk, oeUpd, buMk, hdMk, seMk, seUpd, reUpd,
      smMk, smUpd, qKJO, rs, slice32_costUB,
      qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
      rNone_costUB, rInitPrin_costUB, rPk_costUB, rCorr_costUB, rBundle_costUB, rHdr_costUB,
      rInitUnfresh_costUB, rDrKey_costUB, rSpkSk_costUB,
      smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      initSidE, natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
      optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_costUB, encKEM_costUB,
      eLet2, reMk,
      letV_costUB, bindV_costUB, caseOptV_costUB,
      eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eAny_costUB, eMap_costUB,
      gPrim_costUB, koskBundleOkPowsC_costUB, koskSenderOkPowsC_costUB,
      resolveSigPkC_costUB, lookupSpkSkC_costUB, honestPeerC_costUB, checkProvC_costUB,
      findHonestC_costUB, chooseInitRandC_costUB,
      computePosC_costUB, computeOptPosInitC_costUB, mkSecretPosC_costUB, fgPatchC_costUB,
      sBytes32_costUB, sRandom64_costUB, sDrKey96_costUB,
      qX25519_costUB, qX25519Base_costUB, qIsCanonical_costUB, qPow8_costUB,
      qSigPkGen_costUB, qSigSign_costUB, qSigVerify_costUB,
      qKemKeyGen_costUB, qKemEncaps_costUB, qKemDecaps_costUB,
      litB_costUB, takeKB_costUB, lenB_costUB, eqB_costUB,
      u32OfNat_costUB, eqU32_costUB, v_costUB,
      Comp.costUB, Expr.costUB,
      List.length_nil, List.length_replicate, F_X25519_length, PNat.val_ofNat,
      SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
      ↓reduceIte, Bool.false_eq_true]
    omega)

private theorem gdhHandle2_cost_tight (S : Setup) (K : Nat) :
    (gdhHandle2 S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 60900 :=
  (k1_gdhHandle2_cost_tight_loc S K).trans (by omega)

end

private theorem k1_gdhHandle2_cost_tight (S : Setup) (K : Nat) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).cost ≤
      20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30000 :=
  k1_gdhHandle2_cost_tight_loc S K

private theorem sigKeyInd1KeyActiveDslProg_ddhQueries_quad_eq (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).totalQueries lcDdhW lcZeroWS b.q_total = 4 * b.q_total ^ 2 := by
  have hPre : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy)
      (q : Var Γ₂ keyIndQueryTy),
      (sig1KeyActivePreDispatchC S b.q_total (Δ := Δ) st q).queries lcDdhW lcZeroWS = 0 := by
    intros; simp [sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
      sig1KeyActiveInitiateCheckC, extract1KeyActiveC, letV, Comp.queries]
  have hH : (sig1KeyActiveHandleC S b.q_total).queries lcDdhW lcZeroWS = 4 * b.q_total := by
    simp [sig1KeyActiveHandleC, hPre, SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_ddhQueries,
      ReductionDsl.Comp.rename_queries, gdhHandle2_chalQueries_local, letV, Comp.queries]
  dsimp only [CostedReduction.totalQueries, sigKeyInd1KeyActiveDslProg, keyIndCodec]
  rw [hH]; simp only [bindV_queries, s1Prim_ddhQueries, Comp.queries]; ring

private theorem sigKeyInd1KeyActiveDslProg_ddhQueries_le (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S
  b).totalQueries lcDdhW lcZeroWS b.q_total ≤ 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  rw [sigKeyInd1KeyActiveDslProg_ddhQueries_quad_eq]; omega

private theorem extract1KeyActiveC_primUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁
  sig1KeyActiveStTy) (bu : Var Γ₂ preKeyBundleTy) : (extract1KeyActiveC S K (Δ := Δ) st bu).queriesUB lcPrimW lcZeroWS =
  2 * min K S.N_dh + 2 := by
  simp only [extract1KeyActiveC, bindV_queriesUB, s1Prim_primUB, letV_queriesUB, honestPeerC_primUB,
    qSigVerify_queriesUB, Comp.queriesUB]

private theorem sig1KeyActivePreDispatchC_primUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyActivePreDispatchC S K (Δ := Δ) st q).queriesUB lcPrimW lcZeroWS =
      4 * min K S.N_dh + 7 := by
  simp only [sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB, sig1KeyActiveInitiateCheckC,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB, s1Prim_primUB, extract1KeyActiveC_primUB,
    qSigDdhSign_primUB, sBytes32_queriesUB, sRandom64_queriesUB, qX25519Base_queriesUB, qKemKeyGen_queriesUB,
    Comp.queriesUB]; ring

private theorem sig1KeyActiveHandleC_primQueries_le (S : Setup) (K : Nat) : (sig1KeyActiveHandleC S K).queries lcPrimW
  lcZeroWS ≤ 160 + 76 * S.N_dh + 16 * S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB lcPrimW lcZeroWS (sig1KeyActiveHandleC S K)
  have hUB : (sig1KeyActiveHandleC S K).queriesUB lcPrimW lcZeroWS =
      160 + 76 * min K S.N_dh + 16 * min K S.N_sess_tot := by
    simp only [sig1KeyActiveHandleC, letV_queriesUB, bindV_queriesUB, caseSumV_queriesUB,
      sig1KeyActivePreDispatchC_primUB, SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_primUB,
      ReductionDsl.Comp.rename_queriesUB, gdhHandle2_primUB_local,
      Comp.queriesUB]; ring
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  rw [hUB] at h; omega

private theorem sigKeyInd1KeyActiveDslProg_primQueries_le (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S
  b).totalQueries lcPrimW lcZeroWS b.q_total ≤ primQueryBudget S b := by
  have hInit : (sigKeyInd1KeyActiveDslProg S b).init.queries lcPrimW lcZeroWS = 0 := by
    simp [sigKeyInd1KeyActiveDslProg, sIndex, sBool, Comp.queries]
  have hFin : (sigKeyInd1KeyActiveDslProg S b).finish.queries lcPrimW lcZeroWS = 0 := rfl
  have hH := Nat.mul_le_mul_left b.q_total (sig1KeyActiveHandleC_primQueries_le S b.q_total)
  have hTot : (sigKeyInd1KeyActiveDslProg S b).totalQueries lcPrimW lcZeroWS b.q_total ≤
      b.q_total * (160 + 76 * S.N_dh + 16 * S.N_sess_tot) := by
    dsimp only [CostedReduction.totalQueries]; rw [hInit, hFin]
    change 0 + b.q_total * (sig1KeyActiveHandleC S b.q_total).queries lcPrimW lcZeroWS + 0 ≤ _; omega
  unfold primQueryBudget; nlinarith

private theorem sig1KeyActivePreDispatchC_cost_le_min (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyActivePreDispatchC S K (Δ := Δ) st q).cost ≤ 412 * min K S.N_dh + 6612 * K + 26200 := by
  refine le_trans (sig1KeyActivePreDispatchC S K (Δ := Δ) st q).cost_le_costUB ?_
  simp only [sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB, sig1KeyActiveInitiateCheckC,
    extract1KeyActiveC, saTP, saInner, optNatMatchesE_costUB, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk,
    s1Upd, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, smMk, smUpd, stPrin, stSpks, stOpks,
    stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd, peIkAPk, peMk, sbSpkPk, sbPqspkPk, sbMk, buIkB,
    buSpkB, buSpkSig, buPqspkB, buPqspkSig, buMk, rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq, encEC_costUB,
    encKEM_costUB, widenEC_costUB, letV_costUB, bindV_costUB, caseOptV_costUB, caseSumV_costUB, s1Prim_costUB,
    honestPeerC_costUB, qSigVerify_costUB, qSigDdhSign_costUB, sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB,
    qKemKeyGen_costUB, eCaseOpt_costUB, eAny_costUB, eFind_costUB, eqB_costUB, litB_costUB, u32OfNat_costUB, v_costUB,
    Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]; omega

private theorem sig1KeyActivePreDispatchC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st :
  Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) : (sig1KeyActivePreDispatchC S K (Δ := Δ) st q).cost ≤ 412 *
  S.N_dh + 6612 * K + 26200 := by
  have h := sig1KeyActivePreDispatchC_cost_le_min S K (Δ := Δ) st q
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _; omega

private theorem active_bits_le_log_dh {n : Nat} {S : Setup} (h : n ≤ S.N_dh) :
    bits n ≤ Nat.log 2 S.N_dh + 1 := by
  rw [SignalPqxdh.Security.ReductionDsl.KeyInd.bits_eq_log2_succ, ← SignalPqxdh.Security.ReductionDsl.KeyInd.bits_eq_log2_succ]
  rw [SignalPqxdh.Security.ReductionDsl.KeyInd.bits_eq_log2_succ]; exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem sig1KeyActiveHandleC_cost_le_min (S : Setup) (K : Nat) :
    (sig1KeyActiveHandleC S K).cost ≤
      34627 * K + 27577 * min K S.N_dh + 14742 * min K S.N_sess_tot + 87500 := by
  have hPre := sig1KeyActivePreDispatchC_cost_le_min S K
    (Γ₁ := [sig1KeyActiveStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyActiveStTy, keyIndQueryTy])
    (Δ := [sig1KeyActiveStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hGdh := gdhHandle2_cost_tight S K
  have hLit : pqxdhOps.cost (Sum.inl (SignalPqxdh.LegacyCosted.BOp.lit 32 [])) ≤ 40 := by
    simp [pqxdhOps, SignalPqxdh.LegacyCosted.pqBytesOps, ReductionDsl.Ops.sum]
  simp only [sig1KeyActiveHandleC, SignalPqxdh.Security.ReductionDsl.KeyInd.pa2Mk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_cost, ReductionDsl.Comp.rename_cost,
    letV, bindV, caseSumV, saTP, saInner, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Mk,
    s1Upd, SignalPqxdh.Security.ReductionDsl.KeyInd.litB, v, Comp.cost, Expr.cost, bits_1]; omega

private theorem sig1KeyActiveHandleC_cost_le (S : Setup) (K : Nat) : (sig1KeyActiveHandleC S K).cost ≤ 34627 * K + 27612
  * S.N_dh + 14742 * S.N_sess_tot + 87500 := by
  have h := sig1KeyActiveHandleC_cost_le_min S K
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

private theorem sigKeyInd1KeyActiveDslProg_init_cost_le_min (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).init.cost ≤ Nat.log 2 S.N_dh + 2 * b.q_total + 120 := by
  refine le_trans (sigKeyInd1KeyActiveDslProg S b).init.cost_le_costUB ?_
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hn : activeIdCount S b.q_on ≤ S.N_dh := (Nat.min_le_right _ _).trans (by omega)
  have b1 := active_bits_le_log_dh hn
  have hsb : Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget S b ≤ b.q_total := Nat.min_le_left _ _
  have b2 : bits (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget S b) ≤ b.q_total + 1 :=
    (_root_.ReductionDsl.bits_mono hsb).trans (bits_le_succ b.q_total)
  have b3 := bits_le_succ (b.q_total + 1)
  dsimp only [sigKeyInd1KeyActiveDslProg]
  by_cases h0 : activeIdCount S b.q_on = 0 <;>
    (simp only [h0, ↓reduceIte, s1Mk, emptySimE, smMk, emptyStE, stMk, bindV_costUB, s1Prim_costUB,
      sIndex_costUB, sBool_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_0]; omega)

private theorem sigKeyInd1KeyActiveDslProg_init_cost_le (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg S
  b).init.cost ≤ 2 * S.N_dh + b.q_total + 120 := by
  refine le_trans (sigKeyInd1KeyActiveDslProg S b).init.cost_le_costUB ?_
  have hn : activeIdCount S b.q_on ≤ S.N_id := Nat.min_le_right _ _
  have b1 := bits_le_succ (activeIdCount S b.q_on)
  have hsb : Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget S b ≤ min S.N_spk_tot S.N_recv := Nat.min_le_right _ _
  have b2 : bits (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget S b) ≤ min S.N_spk_tot S.N_recv + 1 :=
    (_root_.ReductionDsl.bits_mono hsb).trans (bits_le_succ _)
  have b3 := bits_le_succ (b.q_total + 1)
  have bm := Nat.min_le_left S.N_spk_tot S.N_recv
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  dsimp only [sigKeyInd1KeyActiveDslProg]
  by_cases h0 : activeIdCount S b.q_on = 0 <;>
    (simp only [h0, ↓reduceIte, s1Mk, emptySimE, smMk, emptyStE, stMk, bindV_costUB, s1Prim_costUB,
      sIndex_costUB, sBool_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_0]; omega)

private theorem sigKeyInd1KeyActiveDslProg_totalCost_clamped_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).totalCost b.q_total ≤
      1830 + 87534 * b.q_total + 36 * (b.q_total + 1) * Nat.log 2 S.N_dh +
        34627 * (b.q_total * b.q_total) +
        27577 * (b.q_total * min b.q_total S.N_dh) +
        14742 * (b.q_total * min b.q_total S.N_sess_tot) := by
  have hI := sigKeyInd1KeyActiveDslProg_init_cost_le_min S b
  have hH := sig1KeyActiveHandleC_cost_le_min S b.q_total
  have hF : (sigKeyInd1KeyActiveDslProg S b).finish.cost ≤ 1710 := by
    refine le_trans (sigKeyInd1KeyActiveDslProg S b).finish.cost_le_costUB ?_
    dsimp only [sigKeyInd1KeyActiveDslProg]
    simp only [s1Forgery, saInner, eCaseOpt_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
      List.length_nil, PNat.val_ofNat]; omega
  have hmax : max 1 ((sig1KeyActiveHandleC S b.q_total).cost + 32) ≤
      34627 * b.q_total + 27577 * min b.q_total S.N_dh + 14742 * min b.q_total S.N_sess_tot +
        35 * Nat.log 2 S.N_dh + 87532 := by omega
  have hq := Nat.mul_le_mul_left b.q_total hmax
  have hExp : b.q_total * (34627 * b.q_total + 27577 * min b.q_total S.N_dh +
        14742 * min b.q_total S.N_sess_tot + 35 * Nat.log 2 S.N_dh + 87532) =
      87532 * b.q_total + 34627 * (b.q_total * b.q_total) +
        27577 * (b.q_total * min b.q_total S.N_dh) +
        14742 * (b.q_total * min b.q_total S.N_sess_tot) +
        35 * b.q_total * Nat.log 2 S.N_dh := by ring
  rw [hExp] at hq
  have hLog : Nat.log 2 S.N_dh + 35 * b.q_total * Nat.log 2 S.N_dh ≤
      36 * (b.q_total + 1) * Nat.log 2 S.N_dh := by
    have : 1 + 35 * b.q_total ≤ 36 * (b.q_total + 1) := by omega
    nlinarith
  change (sigKeyInd1KeyActiveDslProg S b).init.cost +
    b.q_total * max 1 ((sig1KeyActiveHandleC S b.q_total).cost + 32) +
    (sigKeyInd1KeyActiveDslProg S b).finish.cost ≤ _; omega

private theorem sigKeyInd1KeyActiveDslProg_totalCost_poly_le (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveDslProg
  S b).totalCost b.q_total ≤ 1830 + 87533 * b.q_total + 2 * S.N_dh + 34627 * (b.q_total * b.q_total) + 27612 *
  (b.q_total * S.N_dh) + 14742 * (b.q_total * S.N_sess_tot) := by
  have hI := sigKeyInd1KeyActiveDslProg_init_cost_le S b; have hH := sig1KeyActiveHandleC_cost_le S b.q_total
  have hF : (sigKeyInd1KeyActiveDslProg S b).finish.cost ≤ 1710 := by
    refine le_trans (sigKeyInd1KeyActiveDslProg S b).finish.cost_le_costUB ?_
    dsimp only [sigKeyInd1KeyActiveDslProg]
    simp only [s1Forgery, saInner, eCaseOpt_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB, List.length_nil,
      PNat.val_ofNat]; omega
  have hmax : max 1 ((sig1KeyActiveHandleC S b.q_total).cost + 32) ≤
      34627 * b.q_total + 27612 * S.N_dh + 14742 * S.N_sess_tot + 87532 := by omega
  have hq := Nat.mul_le_mul_left b.q_total hmax
  have hExp : b.q_total * (34627 * b.q_total + 27612 * S.N_dh + 14742 * S.N_sess_tot + 87532) =
      87532 * b.q_total + 34627 * (b.q_total * b.q_total) +
        27612 * (b.q_total * S.N_dh) + 14742 * (b.q_total * S.N_sess_tot) := by ring
  rw [hExp] at hq
  change (sigKeyInd1KeyActiveDslProg S b).init.cost +
    b.q_total * max 1 ((sig1KeyActiveHandleC S b.q_total).cost + 32) +
    (sigKeyInd1KeyActiveDslProg S b).finish.cost ≤ _; omega

@[simp] private theorem initPrin1KeyB_prim_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).queries primW primWS = 1 := by simp [initPrin1KeyB, bindV, Comp.queries]

@[simp] private theorem shcrActiveGenSpkB_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ shcrStTy) (x :
  Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (shcrActiveGenSpkB (Δ := Δ) S K s x).queries primW primWS = 4 := by
  simp [shcrActiveGenSpkB, caseOptV, bindV, Comp.queries]

private theorem shcr1KeyActivePostC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyActivePostC (Δ := Δ) S K s q).queries primW primWS ≤
      18 + S.N_dh * 18 + S.N_sess_tot * 8 := by
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  simp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV, onBase_queries, initPrin1KeyB_prim_queries,
    corruptB_queries, shcrActiveGenSpkB_queries, genOpkB_queries, shcrInitiateC_queries, shcrAcceptB_true_queries,
    shcrAcceptB_false_queries, testB_queries, roB_queries, revealDhB_queries, revealB_queries, registerB_queries,
    revealSpkB_queries, Comp.queries]; omega

private theorem shcrKeyInd1KeyActiveDslProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
  (shcrKeyInd1KeyActiveDslProg S b).totalQueries primW primWS b.q_total ≤ primQueryBudget S b := by
  have md : min (keyIndLoopBound b) S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min (keyIndLoopBound b) S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have h1 : (shcrKeyInd1KeyActiveDslProg S b).handlePre.queries primW primWS ≤
      16 * (4 * S.N_dh + S.N_sess_tot + 4) := by
    change (shcr1KeyActivePreC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ :=
      [shcrStTy, keyIndQueryTy]) .zero .zero).queries primW primWS ≤ _
    simp only [shcr1KeyActivePreC, pauseCheckC, tryPauseC, preCheckC_queries, checkSigsC_queries, bindV, letV, caseOptV,
      caseSumV, Comp.queries]
    have hPost := shcr1KeyActivePostC_queries_le S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ :=
      [keyIndQueryTy]) (Δ := (.opt pauseTy) :: [shcrStTy, keyIndQueryTy]) .zero .zero
    omega
  have h2 : (shcrKeyInd1KeyActiveDslProg S b).handlePost.queries primW primWS ≤ 16 * (4 * S.N_dh + S.N_sess_tot + 4) :=
    (shcr1KeyActivePostC_queries_le S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ
    := [shcrStTy, keyIndQueryTy]) .zero .zero).trans (by omega)
  have h3 : (shcrKeyInd1KeyActiveDslProg S b).resume.queries primW primWS ≤ 16 * (4 * S.N_dh + S.N_sess_tot + 4) :=
    (shcrKeyIndProg_resume_primQueries_le S b.q_total (keyIndLoopBound b)).trans (by omega)
  have hFin : (shcrKeyInd1KeyActiveDslProg S b).finish.queries primW primWS = b.q_total :=
    shcrKeyIndProg_finish_primQueries S b.q_total (keyIndLoopBound b)
  have hInit : (shcrKeyInd1KeyActiveDslProg S b).init.queries primW primWS = 0 := by
    dsimp only [shcrKeyInd1KeyActiveDslProg]
    split_ifs <;> simp [bindV, Comp.queries]
  have hCh : (shcrKeyInd1KeyActiveDslProg S b).chDone.queries primW primWS = 0 := rfl
  simp only [TwoStageCostedReduction.totalQueries, primQueryBudget, hFin, hInit, hCh]
  have hMul := Nat.mul_le_mul_left b.q_total (max_le h1 h2)
  have hResMax : max 0 ((shcrKeyInd1KeyActiveDslProg S b).resume.queries primW primWS) = (shcrKeyInd1KeyActiveDslProg S
    b).resume.queries primW primWS := Nat.zero_max _
  rw [hResMax]; nlinarith

private theorem shcr1KeyActivePostC_cost_tight_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyActivePostC (Δ := Δ) S K s q).cost ≤
      18910 + min K S.N_dh * 7980 + min K S.N_sess_tot * 7362 + K * 3806 := by
  have hInit := (initPrin1KeyB_cost_le K (Γ₁ := keyIndStateTy :: (.nat :: Δ)) (Γ₂ := .nat :: Δ)
    (Δ := keyIndStateTy :: (.nat :: Δ)) .zero .zero).trans (by rw [initPrinB_cost])
  have hSpkGen : ∀ {Γ' Δ' : List PT} [Ext Γ₁ Δ'] [Ext Γ' Δ'] (x : Var Γ' (.prod .nat .nat)),
      (shcrActiveGenSpkB (Δ := Δ') S K s x).cost ≤ 8900 + K * 40 := fun _ => by
    simp only [shcrActiveGenSpkB, caseOptV, bindV, onBase_cost, genSpkB_cost, eAny, eFind, nat2Eq, natEq, scBase, scTB,
      scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk, stUpd, stMk, stSecb, stPrin, stSpks, stOpks,
      stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, sbMk, buMk, peIkAPk, peSecIKAsign, rNone, rBundle,
      cost_sBytes32, cost_qX25519Base, cost_sRandom64, cost_qSigSign, cost_encEC, cost_encKEM, cost_u32OfNat, cost_v,
      Comp.cost, Expr.cost, PNat.val_ofNat]; omega
  let τRest := Ty.sum (.prod .nat .nat) (.sum (.prod .nat (.prod .nat .nat)) (.sum (.prod .nat (.prod .nat bundleT))
    (.sum (.prod .nat (.prod .nat bundleT)) (.sum (.prod .nat (.prod .nat (.prod .nat hdrT))) (.sum (.prod .nat (.prod
    .nat (.prod .nat hdrT))) (.sum sidT (.sum (B 192) (.sum .unit (.sum sidT (.sum (B 32) (.prod .nat .nat)))))))))))
  have hSpk := hSpkGen (Γ' := .prod .nat .nat :: τRest :: keyIndQueryRestTy :: Δ)
    (Δ' := .prod .nat .nat :: τRest :: keyIndQueryRestTy :: Δ) .zero
  simp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV, onBase_cost, corruptB_cost, genOpkB_cost,
    shcrInitiateC_true_cost, shcrInitiateC_false_cost, shcrAcceptB_true_cost, shcrAcceptB_false_cost, testB_cost,
    roB_true_cost, revealDhB_true_cost, revealB_cost, registerB_cost, revealSpkB_cost, cost_v, Comp.cost]; omega

private theorem shcr1KeyActivePostC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyActivePostC (Δ := Δ) S K s q).cost ≤
      18910 + bits (nRecv S) + S.N_dh * 7980 + S.N_sess_tot * 7362 + K * 3806 := by
  have h := shcr1KeyActivePostC_cost_tight_le S K (Δ := Δ) s q
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  nlinarith

private theorem shcrKeyInd1KeyActiveDslProg_init_cost_le_min (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).init.cost ≤ 80 + b.q_total + 4 * Nat.log 2 S.N_dh := by
  refine le_trans (shcrKeyInd1KeyActiveDslProg S b).init.cost_le_costUB ?_
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hSpk : activeSpkCount S b.q_on ≤ S.N_dh := (Nat.min_le_right _ _).trans (by omega)
  have hSend : activeSendCount S b.q_on ≤ S.N_dh := (Nat.min_le_right _ _).trans (by omega)
  have bSpk := active_bits_le_log_dh hSpk
  have bSend := active_bits_le_log_dh hSend
  have bQ := bits_le_succ (b.q_total + 1)
  dsimp only [shcrKeyInd1KeyActiveDslProg]
  by_cases h0 : activeSpkCount S b.q_on * activeSendCount S b.q_on = 0
  · simp only [h0, ↓reduceIte, emptyStE, stMk, scMk, bindV_costUB, sBool_costUB,
      v_costUB, Comp.costUB, Expr.costUB, bits_0]; omega
  · simp only [h0, ↓reduceIte, emptyStE, stMk, scMk, bindV_costUB, sIndex_costUB, sBool_costUB,
      v_costUB, Comp.costUB, Expr.costUB, bits_0]; omega

private theorem shcrKeyInd1KeyActiveDslProg_init_cost_le (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveDslProg S
  b).init.cost ≤ 80 + b.q_total + 4 * S.N_dh := by
  have h := shcrKeyInd1KeyActiveDslProg_init_cost_le_min S b
  have hLog : Nat.log 2 S.N_dh ≤ S.N_dh := Nat.log_le_self 2 S.N_dh
  omega

private theorem shcrKeyInd1KeyActiveDslProg_totalCost_clamped_le (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).totalCost b.q_total ≤
      14250 + 45200 * b.q_total +
        3144 * min b.q_total S.N_dh + 22086 * min b.q_total S.N_sess_tot +
        4 * (b.q_total + 1) * Nat.log 2 S.N_dh +
        8126 * (b.q_total * b.q_total) +
        26415 * (b.q_total * min b.q_total S.N_dh) +
        22086 * (b.q_total * min b.q_total S.N_sess_tot) := by
  have hKB : keyIndLoopBound b = 2 * b.q_total + 1 := rfl
  have h1 : (shcrKeyInd1KeyActiveDslProg S b).handlePre.cost ≤
      22778 + min (keyIndLoopBound b) S.N_dh * 8804 +
        min (keyIndLoopBound b) S.N_sess_tot * 7362 + keyIndLoopBound b * 4063 := by
    change (shcr1KeyActivePreC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).cost ≤ _
    simp only [shcr1KeyActivePreC, bindV, caseOptV, pauseCheckC_cost, buPqspkB, cost_v, Comp.cost, Expr.cost]
    have hPost := shcr1KeyActivePostC_cost_tight_le S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := (.opt pauseTy) :: [shcrStTy, keyIndQueryTy]) .zero .zero
    omega
  have h2 : (shcrKeyInd1KeyActiveDslProg S b).handlePost.cost ≤
      18910 + min (keyIndLoopBound b) S.N_dh * 7980 +
        min (keyIndLoopBound b) S.N_sess_tot * 7362 + keyIndLoopBound b * 3806 :=
    shcr1KeyActivePostC_cost_tight_le S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have h3 := shcrKeyIndProg_resume_cost S b.q_total (keyIndLoopBound b)
  have h4 := shcrKeyIndProg_finish_cost S b.q_total (keyIndLoopBound b)
  have h5 := shcrKeyInd1KeyActiveDslProg_init_cost_le_min S b
  have h6 := shcrKeyIndProg_chDone_cost S b.q_total (keyIndLoopBound b)
  dsimp only [TwoStageCostedReduction.totalCost]
  have hC : (keyIndCodec S).codecCost = 32 := rfl
  have hU : pqPrimIface.uCost = 1 := rfl
  change (shcrKeyInd1KeyActiveDslProg S b).init.cost +
    b.q_total * max pqPrimIface.uCost
      (max (shcrKeyInd1KeyActiveDslProg S b).handlePre.cost
        (shcrKeyInd1KeyActiveDslProg S b).handlePost.cost + (keyIndCodec S).codecCost) +
    max (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).chDone.cost
      (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).resume.cost +
    (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).finish.cost ≤ _
  rw [hC, hU, h3, h4, h6]
  generalize (shcrKeyInd1KeyActiveDslProg S b).handlePre.cost = hc1 at h1 ⊢
  generalize (shcrKeyInd1KeyActiveDslProg S b).handlePost.cost = hc2 at h2 ⊢
  generalize (shcrKeyInd1KeyActiveDslProg S b).init.cost = hi at h5 ⊢
  cases hq : b.q_total with
  | zero =>
    have md1 : min (keyIndLoopBound b) S.N_dh ≤ 1 := by omega
    have ms1 : min (keyIndLoopBound b) S.N_sess_tot ≤ 1 := by omega
    omega
  | succ q' =>
    have md3 : min (keyIndLoopBound b) S.N_dh ≤ 3 * min (q' + 1) S.N_dh := by omega
    have ms3 : min (keyIndLoopBound b) S.N_sess_tot ≤ 3 * min (q' + 1) S.N_sess_tot := by omega
    have hMaxH : max 1 (max hc1 hc2 + 32) ≤
        26873 + min (q' + 1) S.N_dh * 26415 + min (q' + 1) S.N_sess_tot * 22086 + (q' + 1) * 8126 := by omega
    have hMul := Nat.mul_le_mul_left (q' + 1) hMaxH
    have hExp : (q' + 1) * (26873 + min (q' + 1) S.N_dh * 26415 +
          min (q' + 1) S.N_sess_tot * 22086 + (q' + 1) * 8126) =
        26873 * (q' + 1) + 8126 * ((q' + 1) * (q' + 1)) +
          26415 * ((q' + 1) * min (q' + 1) S.N_dh) +
          22086 * ((q' + 1) * min (q' + 1) S.N_sess_tot) := by ring
    have hLog : 4 * Nat.log 2 S.N_dh ≤ 4 * (q' + 1 + 1) * Nat.log 2 S.N_dh := by nlinarith
    rw [hExp] at hMul; omega

private theorem shcrKeyInd1KeyActiveDslProg_totalCost_poly_le (S : Setup) (b : QueryBudget) :
  (shcrKeyInd1KeyActiveDslProg S b).totalCost b.q_total ≤ 5850 + 45200 * b.q_total + 1060 * S.N_dh + 7362 * S.N_sess_tot
  + 8126 * (b.q_total * b.q_total) + 8805 * (b.q_total * S.N_dh) + 7362 * (b.q_total * S.N_sess_tot) := by
  have md : min (keyIndLoopBound b) S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min (keyIndLoopBound b) S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have h1 : (shcrKeyInd1KeyActiveDslProg S b).handlePre.cost ≤
      22778 + bits (nRecv S) + S.N_dh * 8804 + S.N_sess_tot * 7362 + keyIndLoopBound b * 4063 := by
    change (shcr1KeyActivePreC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ :=
      [shcrStTy, keyIndQueryTy]) .zero .zero).cost ≤ _
    simp only [shcr1KeyActivePreC, bindV, caseOptV, pauseCheckC_cost, buPqspkB, cost_v, Comp.cost, Expr.cost]
    have hPost := shcr1KeyActivePostC_cost_le S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ :=
      [keyIndQueryTy]) (Δ := (.opt pauseTy) :: [shcrStTy, keyIndQueryTy]) .zero .zero
    omega
  have h2 : (shcrKeyInd1KeyActiveDslProg S b).handlePost.cost ≤
      18910 + bits (nRecv S) + S.N_dh * 7980 + S.N_sess_tot * 7362 + keyIndLoopBound b * 3806 :=
    shcr1KeyActivePostC_cost_le S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have h3 := shcrKeyIndProg_resume_cost S b.q_total (keyIndLoopBound b)
  have h4 := shcrKeyIndProg_finish_cost S b.q_total (keyIndLoopBound b)
  have h5 := shcrKeyInd1KeyActiveDslProg_init_cost_le S b
  have h6 := shcrKeyIndProg_chDone_cost S b.q_total (keyIndLoopBound b)
  have hbR := bits_nRecv_le S; have hKB : keyIndLoopBound b = 2 * b.q_total + 1 := rfl
  dsimp only [TwoStageCostedReduction.totalCost]; have hC : (keyIndCodec S).codecCost = 32 := rfl
  have hU : pqPrimIface.uCost = 1 := rfl
  change (shcrKeyInd1KeyActiveDslProg S b).init.cost +
    b.q_total * max pqPrimIface.uCost
      (max (shcrKeyInd1KeyActiveDslProg S b).handlePre.cost
        (shcrKeyInd1KeyActiveDslProg S b).handlePost.cost + (keyIndCodec S).codecCost) +
    max (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).chDone.cost
      (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).resume.cost +
    (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).finish.cost ≤ _
  rw [hC, hU, h3, h4, h6]
  generalize (shcrKeyInd1KeyActiveDslProg S b).handlePre.cost = hc1 at h1 ⊢
  generalize (shcrKeyInd1KeyActiveDslProg S b).handlePost.cost = hc2 at h2 ⊢
  generalize (shcrKeyInd1KeyActiveDslProg S b).init.cost = hi at h5 ⊢
  have hRes : 2155 + min (keyIndLoopBound b) S.N_dh * 1048 + min (keyIndLoopBound b) S.N_sess_tot * 7362 +
      keyIndLoopBound b * 3549 ≤ 2155 + S.N_dh * 1048 + S.N_sess_tot * 7362 + keyIndLoopBound b * 3549 := by nlinarith
  have hMaxH : max 1 (max hc1 hc2 + 32) ≤
      26874 + S.N_dh * 8805 + S.N_sess_tot * 7362 + b.q_total * 8126 := by omega
  have hMul := Nat.mul_le_mul_left b.q_total hMaxH
  have hExp : b.q_total * (26874 + S.N_dh * 8805 + S.N_sess_tot * 7362 + b.q_total * 8126) =
      26874 * b.q_total + 8126 * (b.q_total * b.q_total) +
        8805 * (b.q_total * S.N_dh) + 7362 * (b.q_total * S.N_sess_tot) := by ring
  rw [hExp] at hMul; omega

private theorem genSpk1KeyActiveGdhB_queries_prim_le (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁
  gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat .nat)) : (genSpk1KeyActiveGdhB K (Δ := Δ) stA x).queries wPrim1Key
  wsZero1Key ≤ 4 := by
  simp only [genSpk1KeyActiveGdhB, Comp.queries, letV_queries, bindV_queries, caseOptV_queries,
    liftGdhComp_queries_prim, gPrim_queries_wPrimGdh, sigChalQ_dsl_queries_prim]
  have hSub : (genSpkGdhActiveB K (Γ₁ := paramsTy :: gdh1KeyStateTy :: Δ)
      (Γ₂ := simTy :: paramsTy :: gdh1KeyStateTy :: Δ)
      (Γ₃ := keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) (Γ₄ := Γ₂)
      (Δ := .nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ)
      .zero .zero .zero x).queries wPrimGdh wsZero ≤ 4 := by
    refine le_trans (Comp.queries_le_queriesUB wPrimGdh wsZero _) ?_
    simp only [genSpkGdhActiveB, letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, gPrim_queriesUB_wPrimGdh,
      sBytes32_queriesUB, sRandom64_queriesUB, qX25519Base_queriesUB, qKemKeyGen_queriesUB, qSigSign_queriesUB,
      Comp.queriesUB]; omega
  simp only [sBytes32_queries, sRandom64_queries, qX25519Base_queries, qKemKeyGen_queries]; omega

private theorem initiateActiveGdhB_queries_ddh_le (S : Setup) (K : Nat) (hasOpk : Bool) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ]
  [Ext Γ₂ Δ] (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy) : (initiateActiveGdhB S K hasOpk (Δ := Δ) stA
  x).queries wDdh1Key wsZero1Key ≤ 4 * K := by
  simp only [initiateActiveGdhB, initiateGdhActiveInnerB, letV_queries, bindV_queries, caseOptV_queries,
    liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, computePosC_chal, computeOptPosInitC_chal, fgPatchC_chal,
    chooseInitRandC_chal, Comp.queries]; omega

private theorem initiateGdhActiveInnerB_queries_prim_le (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (sendOpkCnt : Var Γ₅ .nat) (x : Var Γ₄ initQTy) :
    (initiateGdhActiveInnerB S K (Δ := Δ) pa sm bSt sendOpkCnt hasOpk x).queries wPrimGdh wsZero ≤
      153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  refine le_trans (Comp.queries_le_queriesUB wPrimGdh wsZero _) ?_
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  cases hasOpk <;> (
    simp only [initiateGdhActiveInnerB, letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, gPrim_queriesUB_wPrimGdh,
      koskBundleOkPowsC_primUB, resolveSigPkC_primUB, lookupSpkSkC_primUB, honestPeerC_primUB, checkProvC_primUB,
      findHonestC_primUB, chooseInitRandC_primUB, computePosC_primUB, computeOptPosInitC_primUB, fgPatchC_primUB,
      sBytes32_queriesUB, qX25519Base_queriesUB, qSigVerify_queriesUB, qKemEncaps_queriesUB, Comp.queriesUB,
      ↓reduceIte, Bool.false_eq_true]
    linarith)

private theorem initiateActiveGdhB_queries_prim_le (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy) :
    (initiateActiveGdhB S K hasOpk (Δ := Δ) stA x).queries wPrim1Key wsZero1Key ≤
      153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  simp only [initiateActiveGdhB, letV_queries, bindV_queries, liftGdhComp_queries_prim, Comp.queries, add_zero]
  exact initiateGdhActiveInnerB_queries_prim_le S K hasOpk _ _ _ _ _

private theorem caseSumV_queries_le {Γ : List PT} {τ₁ τ₂ τ : PT} (w : pqSigAndDdhIface.Tag → ℕ) (ws :
  pqSigAndDdhIface.smp.Samp → ℕ) (x : Var Γ (.sum τ₁ τ₂)) (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ ::
  Γ) τ) (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqSigAndDdhIface (τ₂ :: Γ) τ) {c : ℕ} (hl : (kl .zero).queries w ws ≤ c)
  (hr : (kr .zero).queries w ws ≤ c) : (caseSumV (v x) kl kr).queries w ws ≤ c := by
  rw [caseSumV_queries]; exact Nat.max_le.mpr ⟨hl, hr⟩

private theorem fgKeyInd1KeyGapDhActiveDslProg_sigQueries_le (S : Setup) (b : QueryBudget) :
  (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries lcSigW lcZeroWS b.q_total ≤ 2 * b.q_total := by
  change (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries wSig1Key wsZero1Key b.q_total ≤ _
  have hI : (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries wSig1Key wsZero1Key = 0 := by
    simp [fgKeyInd1KeyGapDhActiveDslProg, letV, bindV, Comp.queries]
  have hH : (gdh1KeyActiveHandle S b.q_total).queries wSig1Key wsZero1Key = 2 := by
    simp [gdh1KeyActiveHandle, callGdhActiveHandle, initPrin1KeyActiveGdhB, genSpk1KeyActiveGdhB, genOpkActiveGdhB,
      initiateActiveGdhB, Comp.queries]
  have hF : (gdh1KeyActiveFinish S b.q_total).queries wSig1Key wsZero1Key = 0 := by
    simp [gdh1KeyActiveFinish]
  dsimp only [CostedReduction.totalQueries]; rw [hI]
  change 0 + b.q_total * (gdh1KeyActiveHandle S b.q_total).queries wSig1Key wsZero1Key + (gdh1KeyActiveFinish S
    b.q_total).queries wSig1Key wsZero1Key ≤ _
  rw [hH, hF]; omega

private theorem fgKeyInd1KeyGapDhActiveDslProg_ddhQueries_le (S : Setup) (b : QueryBudget) :
  (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries lcDdhW lcZeroWS b.q_total ≤
    4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  change (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries wDdh1Key wsZero1Key b.q_total ≤ _
  have hI : (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries wDdh1Key wsZero1Key = 0 := by
    have hP : (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initParams1KeyActiveC S b
        (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
        (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero).queries
        SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.wDdhGdh wsZero = 0 :=
      initParams1KeyActiveC_queries_zero S b .zero _
    simp [fgKeyInd1KeyGapDhActiveDslProg, liftGdhComp_queries_ddh, hP, letV, bindV, Comp.queries]
  have hH : (gdh1KeyActiveHandle S b.q_total).queries wDdh1Key wsZero1Key ≤ 4 * b.q_total := by
    unfold gdh1KeyActiveHandle
    refine caseSumV_queries_le _ _ _ _ _ (by simp [initPrin1KeyActiveGdhB, Comp.queries]) ?_
    refine caseSumV_queries_le _ _ _ _ _
      (by simp [callGdhActiveHandle, gdhHandle2_chalQueries_local, Comp.queries]) ?_
    refine caseSumV_queries_le _ _ _ _ _
      (by simp [genSpk1KeyActiveGdhB, genSpkGdhActiveB, letV, bindV, caseOptV, Comp.queries]) ?_
    refine caseSumV_queries_le _ _ _ _ _ (by simp [genOpkActiveGdhB, Comp.queries]) ?_
    refine caseSumV_queries_le _ _ _ _ _ (initiateActiveGdhB_queries_ddh_le S b.q_total true _ _) ?_
    exact caseSumV_queries_le _ _ _ _ _ (initiateActiveGdhB_queries_ddh_le S b.q_total false _ _)
      (by simp [callGdhActiveHandle, gdhHandle2_chalQueries_local, Comp.queries])
  have hF : (gdh1KeyActiveFinish S b.q_total).queries wDdh1Key wsZero1Key ≤
      b.q_total + S.N_dh + S.N_sess_tot := by
    have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
    simp only [gdh1KeyActiveFinish, letV_queries, renameComp_queries, liftGdhComp_queries_ddh, gdhFinish_chalQueries]
    omega
  have hMul := Nat.mul_le_mul_left b.q_total hH
  have hTot : (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries wDdh1Key wsZero1Key b.q_total ≤
      4 * b.q_total * b.q_total + b.q_total + S.N_dh + S.N_sess_tot := by
    dsimp only [CostedReduction.totalQueries]; rw [hI]
    change 0 + b.q_total * (gdh1KeyActiveHandle S b.q_total).queries wDdh1Key wsZero1Key + (gdh1KeyActiveFinish S
      b.q_total).queries wDdh1Key wsZero1Key ≤ _
    have : b.q_total * (4 * b.q_total) = 4 * b.q_total * b.q_total := by ring
    omega
  have hSq : 4 * b.q_total * b.q_total = 4 * b.q_total ^ 2 := by ring
  omega

private theorem gdh1KeyActiveHandle_queries_prim_le (S : Setup) (K : Nat) :
    (gdh1KeyActiveHandle S K).queries wPrim1Key wsZero1Key ≤ 153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have hGdh := gdhHandle2_primQueries_le_local S K
  unfold gdh1KeyActiveHandle
  refine caseSumV_queries_le _ _ _ _ _
    (by simp only [initPrin1KeyActiveGdhB, letV_queries, bindV_queries, liftGdhComp_queries_prim,
          gPrim_queries_wPrimGdh, sBytes32_queries, qX25519Base_queries, Comp.queries]; omega) ?_
  refine caseSumV_queries_le _ _ _ _ _
    (by simp only [callGdhActiveHandle, letV_queries, bindV_queries, renameComp_queries,
          liftGdhComp_queries_prim, Comp.queries]; omega) ?_
  refine caseSumV_queries_le _ _ _ _ _ ((genSpk1KeyActiveGdhB_queries_prim_le _ _ _).trans (by omega)) ?_
  refine caseSumV_queries_le _ _ _ _ _
    (by simp only [genOpkActiveGdhB, letV_queries, bindV_queries, liftGdhComp_queries_prim,
          gPrim_queries_wPrimGdh, sBytes32_queries, qX25519Base_queries, Comp.queries]; omega) ?_
  refine caseSumV_queries_le _ _ _ _ _ (initiateActiveGdhB_queries_prim_le S K true _ _) ?_
  exact caseSumV_queries_le _ _ _ _ _ (initiateActiveGdhB_queries_prim_le S K false _ _)
    (by simp only [callGdhActiveHandle, letV_queries, bindV_queries, renameComp_queries,
          liftGdhComp_queries_prim, Comp.queries]; omega)

private theorem fgKeyInd1KeyGapDhActiveDslProg_primQueries_le (S : Setup) (b : QueryBudget) :
  (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries lcPrimW lcZeroWS b.q_total ≤ primQueryBudget S b := by
  change (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries wPrim1Key wsZero1Key b.q_total ≤ _
  have hI : (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries wPrim1Key wsZero1Key = 0 := by
    have hP : (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initParams1KeyActiveC S b
        (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
        (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero).queries wPrimGdh wsZero = 0 :=
      initParams1KeyActiveC_queries_zero S b .zero _
    simp [fgKeyInd1KeyGapDhActiveDslProg, liftGdhComp_queries_prim, hP, letV, bindV, Comp.queries]
  have hH := gdh1KeyActiveHandle_queries_prim_le S b.q_total
  have hF : (gdh1KeyActiveFinish S b.q_total).queries wPrim1Key wsZero1Key ≤
      3 * S.N_dh + S.N_sess_tot := by
    simp only [gdh1KeyActiveFinish, letV_queries, renameComp_queries, liftGdhComp_queries_prim]
    exact gdhFinish_primQueries_le S b.q_total
  have hMul := Nat.mul_le_mul_left b.q_total hH
  have hTot : (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries wPrim1Key wsZero1Key b.q_total ≤
      b.q_total * (153 + 72 * S.N_dh + 16 * S.N_sess_tot) + 3 * S.N_dh + S.N_sess_tot := by
    dsimp only [CostedReduction.totalQueries]; rw [hI]
    change 0 + b.q_total * (gdh1KeyActiveHandle S b.q_total).queries wPrim1Key wsZero1Key +
      (gdh1KeyActiveFinish S b.q_total).queries wPrim1Key wsZero1Key ≤ _; omega
  unfold primQueryBudget; nlinarith

private theorem sigKeyInd1KeyActiveDslProg_init_primQueries (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).init.queries lcPrimW lcZeroWS = 0 := by
  simp [sigKeyInd1KeyActiveDslProg, sIndex, sBool, Comp.queries]

private theorem sigKeyInd1KeyActiveDslProg_finish_primQueries (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).finish.queries lcPrimW lcZeroWS = 0 := rfl

private theorem fgKeyInd1KeyGapDhActiveDslProg_init_primQueries (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries lcPrimW lcZeroWS = 0 := by
  change (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries wPrim1Key wsZero1Key = 0
  have hP : (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initParams1KeyActiveC S b
      (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
      (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero).queries wPrimGdh wsZero = 0 :=
    initParams1KeyActiveC_queries_zero S b .zero _
  simp [fgKeyInd1KeyGapDhActiveDslProg, liftGdhComp_queries_prim, hP, letV, bindV, Comp.queries]

private theorem fgKeyInd1KeyGapDhActiveDslProg_finish_primQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries lcPrimW lcZeroWS ≤ 3 * S.N_dh + S.N_sess_tot := by
  change (gdh1KeyActiveFinish S b.q_total).queries wPrim1Key wsZero1Key ≤ _
  simp only [gdh1KeyActiveFinish, letV_queries, renameComp_queries, liftGdhComp_queries_prim]
  exact gdhFinish_primQueries_le S b.q_total

private theorem callGdhActiveHandle_cost_le_min_tight (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhActiveHandle S K stA q).cost ≤
      20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30090 := by
  have hGdh := k1_gdhHandle2_cost_tight S K
  simp only [callGdhActiveHandle, SignalPqxdh.Security.ReductionDsl.KeyInd.pa2Mk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.paU, SignalPqxdh.Security.ReductionDsl.KeyInd.paV, SignalPqxdh.Security.ReductionDsl.KeyInd.paUp, SignalPqxdh.Security.ReductionDsl.KeyInd.paOpkMode, letV, bindV, renameComp_cost, liftGdhComp_cost,
    v, Comp.cost, Expr.cost, bits_1]; omega

private theorem callGdhActiveHandle_cost_le_min (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhActiveHandle S K stA q).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 60990 :=
  (callGdhActiveHandle_cost_le_min_tight S K stA q).trans (by omega)

private theorem initiateActiveGdhB_cost_le_min (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy) :
    (initiateActiveGdhB S K hasOpk (Δ := Δ) stA x).cost ≤
      7000 * K + 3000 * min K S.N_dh + 8000 * min K S.N_sess_tot + 25000 := by
  refine le_trans (initiateActiveGdhB S K hasOpk (Δ := Δ) stA x).cost_le_costUB ?_
  cases hasOpk <;> (
    simp only [initiateActiveGdhB, initiateGdhActiveInnerB, stPrin, stSess, stUpd, stSecb, stSpks, stOpks, stResps,
      stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peIkAPk, peSecIKA0, buIkB, buSpkId, buSpkB, buSpkSig, buOpkB,
      buPqspkId, buPqspkB, buPqspkSig, hdMk, seSid, seMk, seUpd, smUpd, smMk, smBase_costUB, smFgL_costUB, smRaw_costUB,
      smLog_costUB, smPows_costUB, paU_costUB, paDhFlag_costUB, paEphIdx_costUB, paOpkMode_costUB, rNone_costUB,
      rHdr_costUB, rInitUnfresh_costUB, initSidE, sidEq, isSomeE, optFst, optSnd, natEq, nat2Eq, nat3Eq, eLet2,
      encEC_costUB, encKEM_costUB, letV_costUB, bindV_costUB, caseOptV_costUB, eLet_costUB, eCaseOpt_costUB,
      eCaseSum_costUB, eAny_costUB, eFind_costUB, liftGdhComp_costUB, gPrim_costUB, koskBundleOkPowsC_costUB,
      resolveSigPkC_costUB, lookupSpkSkC_costUB, honestPeerC_costUB, checkProvC_costUB, findHonestC_costUB,
      chooseInitRandC_costUB, computePosC_costUB, computeOptPosInitC_costUB, fgPatchC_costUB, sBytes32_costUB,
      qX25519Base_costUB, qSigVerify_costUB, qKemEncaps_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
      List.length_nil, PNat.val_ofNat, bits_1, ↓reduceIte, Bool.false_eq_true]
    omega)

private theorem active_bits_le_two_log_dh {n : Nat} {S : Setup} (h : n ≤ S.N_dh * S.N_dh) :
    bits n ≤ 2 * Nat.log 2 S.N_dh + 2 := by
  have h1 : bits n ≤ bits (S.N_dh * S.N_dh) := _root_.ReductionDsl.bits_mono h
  have h2 := bits_mul S.N_dh S.N_dh
  have h3 : bits S.N_dh = Nat.log 2 S.N_dh + 1 := SignalPqxdh.Security.ReductionDsl.KeyInd.bits_eq_log2_succ S.N_dh
  omega

private theorem initParams1KeyActiveC_cost_le (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initParams1KeyActiveC S b (Δ := Δ) uv).cost ≤
      20 * Nat.log 2 S.N_dh + 4 * b.q_total + 200 := by
  open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (initParams1KeyActiveC) in
  open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (chooseArm2C) in
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hd2 : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hId : activeIdCount S b.q_on ≤ S.N_id := Nat.min_le_right _ _
  have hSpk : activeSpkCount S b.q_on ≤ S.N_spk_tot := Nat.min_le_right _ _
  have hOpk : activeOpkCount S b.q_on ≤ S.N_opk_tot := Nat.min_le_right _ _
  have hSend : activeSendCount S b.q_on ≤ S.N_send_tot := Nat.min_le_right _ _
  have hSendO : activeSendOpkCount S b.q_on ≤ S.N_send_opk_tot := Nat.min_le_right _ _
  have bId := active_bits_le_log_dh (S := S) (by omega : activeIdCount S b.q_on ≤ S.N_dh)
  have bSpk := active_bits_le_log_dh (S := S) (by omega : activeSpkCount S b.q_on ≤ S.N_dh)
  have bOpk := active_bits_le_log_dh (S := S) (by omega : activeOpkCount S b.q_on ≤ S.N_dh)
  have bSend := active_bits_le_log_dh (S := S) (by omega : activeSendCount S b.q_on ≤ S.N_dh)
  have bSendO := active_bits_le_log_dh (S := S) (by omega : activeSendOpkCount S b.q_on ≤ S.N_dh)
  have bUnr := bits_le_succ (b.q_total + 1)
  have hmA := Nat.mul_le_mul hId hSpk; have hmC := Nat.mul_le_mul hSend hSpk
  have hmB := Nat.mul_le_mul hSend hId; have hmD := Nat.mul_le_mul hSendO hOpk
  have hfgSq : fgTotalIndexCount S ≤ S.N_dh * S.N_dh := by
    unfold fgTotalIndexCount Setup.N_dh Setup.N_send_tot; nlinarith
  have hfg : fgTotalIndexCount S = S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot := rfl
  have bAC := active_bits_le_two_log_dh (S := S) (by omega :
    activeIdCount S b.q_on * activeSpkCount S b.q_on + activeSendCount S b.q_on * activeSpkCount S b.q_on ≤ S.N_dh * S.N_dh)
  have bBD := active_bits_le_two_log_dh (S := S) (by omega :
    activeSendCount S b.q_on * activeIdCount S b.q_on + activeSendOpkCount S b.q_on * activeOpkCount S b.q_on ≤ S.N_dh * S.N_dh)
  have bAll := active_bits_le_two_log_dh (S := S) (by omega :
    (activeIdCount S b.q_on * activeSpkCount S b.q_on + activeSendCount S b.q_on * activeSpkCount S b.q_on) +
    (activeSendCount S b.q_on * activeIdCount S b.q_on + activeSendOpkCount S b.q_on * activeOpkCount S b.q_on) ≤ S.N_dh * S.N_dh)
  let Bleaf := 2 * Nat.log 2 S.N_dh + 4 * b.q_total + 70
  have hLeafA : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if activeIdCount S b.q_on * activeSpkCount S b.q_on = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool true)
            (.nat (b.q_total + 1)) (.nat 0) (.bool false) (.nat (b.q_total + 1)) (.nat 0))
        else
          bindV (gPrim (sIndex (activeIdCount S b.q_on))) fun pOrd =>
          bindV (gPrim (sIndex (activeSpkCount S b.q_on))) fun spkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool true)
            (.nat (b.q_total + 1)) (v spkOrd) (.bool false) (.nat (b.q_total + 1)) (.nat 0))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).cost ≤ Bleaf := by
    intro Δ' _
    refine (Comp.cost_le_costUB _).trans ?_
    by_cases h : activeIdCount S b.q_on * activeSpkCount S b.q_on = 0
    · simp only [h, ↓reduceIte, paMk, v_costUB, Comp.costUB, Expr.costUB, bits_0]; dsimp [Bleaf]; omega
    · simp only [h, ↓reduceIte, paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_0]; dsimp [Bleaf]; omega
  have hLeafC : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if activeSendCount S b.q_on * activeSpkCount S b.q_on = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat (b.q_total + 1))
            (.bool false) (.nat 0) (.nat 0) (.bool false) (.nat (b.q_total + 1)) (.nat 1))
        else
          bindV (gPrim (sIndex (activeSendCount S b.q_on))) fun ephOrd =>
          bindV (gPrim (sIndex (activeSpkCount S b.q_on))) fun spkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat (b.q_total + 1))
            (.bool false) (v ephOrd) (v spkOrd) (.bool false) (.nat (b.q_total + 1)) (.nat 1))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).cost ≤ Bleaf := by
    intro Δ' _
    refine (Comp.cost_le_costUB _).trans ?_
    by_cases h : activeSendCount S b.q_on * activeSpkCount S b.q_on = 0
    · simp only [h, ↓reduceIte, paMk, v_costUB, Comp.costUB, Expr.costUB, bits_0, bits_1]; dsimp [Bleaf]; omega
    · simp only [h, ↓reduceIte, paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]; dsimp [Bleaf]; omega
  have hLeafB : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if activeSendCount S b.q_on * activeIdCount S b.q_on = 0 then
          .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool false)
            (.nat 0) (.nat (b.q_total + 1)) (.bool false) (.nat (b.q_total + 1)) (.nat 2))
        else
          bindV (gPrim (sIndex (activeSendCount S b.q_on))) fun ephOrd =>
          bindV (gPrim (sIndex (activeIdCount S b.q_on))) fun pOrd =>
          .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool false)
            (v ephOrd) (.nat (b.q_total + 1)) (.bool false) (.nat (b.q_total + 1)) (.nat 2))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).cost ≤ Bleaf := by
    intro Δ' _
    refine (Comp.cost_le_costUB _).trans ?_
    by_cases h : activeSendCount S b.q_on * activeIdCount S b.q_on = 0
    · simp only [h, ↓reduceIte, paMk, v_costUB, Comp.costUB, Expr.costUB, bits_0, bits_2]; dsimp [Bleaf]; omega
    · simp only [h, ↓reduceIte, paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_2]; dsimp [Bleaf]; omega
  have hLeafD : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if activeSendOpkCount S b.q_on * activeOpkCount S b.q_on = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat (b.q_total + 1))
            (.bool false) (.nat 0) (.nat (b.q_total + 1)) (.bool true) (.nat 0) (.nat 3))
        else
          bindV (gPrim (sIndex (activeSendOpkCount S b.q_on))) fun ephOrd =>
          bindV (gPrim (sIndex (activeOpkCount S b.q_on))) fun opkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat (b.q_total + 1))
            (.bool false) (v ephOrd) (.nat (b.q_total + 1)) (.bool true) (v opkOrd) (.nat 3))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).cost ≤ Bleaf := by
    intro Δ' _
    refine (Comp.cost_le_costUB _).trans ?_
    by_cases h : activeSendOpkCount S b.q_on * activeOpkCount S b.q_on = 0
    · simp only [h, ↓reduceIte, paMk, v_costUB, Comp.costUB, Expr.costUB, bits_0, bits_3]; dsimp [Bleaf]; omega
    · simp only [h, ↓reduceIte, paMk, bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_3]; dsimp [Bleaf]; omega
  unfold initParams1KeyActiveC
  dsimp only
  by_cases h0 : fgActiveTotalIndexCount S b.q_on = 0
  · simp only [h0, ↓reduceIte]
    refine (Comp.cost_le_costUB _).trans ?_
    simp only [paMk, v_costUB, Comp.costUB, Expr.costUB, bits_0]; omega
  · simp only [h0, ↓reduceIte]
    let Bmid := 8 * Nat.log 2 S.N_dh + 4 * b.q_total + 106
    have hTop := act_chooseArm2C_cost_le (Γ₁ := Γ₁) (Δ := Δ)
      (activeIdCount S b.q_on * activeSpkCount S b.q_on + activeSendCount S b.q_on * activeSpkCount S b.q_on)
      (activeSendCount S b.q_on * activeIdCount S b.q_on + activeSendOpkCount S b.q_on * activeOpkCount S b.q_on)
      _ _ Bmid
      (fun {Δ'} [_] => (act_chooseArm2C_cost_le (Γ₁ := Γ₁) (Δ := Δ')
        (activeIdCount S b.q_on * activeSpkCount S b.q_on)
        (activeSendCount S b.q_on * activeSpkCount S b.q_on) _ _ Bleaf
        (fun {Δ''} [_] => hLeafA (Δ' := Δ'')) (fun {Δ''} [_] => hLeafC (Δ' := Δ''))).trans (by dsimp [Bleaf, Bmid]; omega))
      (fun {Δ'} [_] => (act_chooseArm2C_cost_le (Γ₁ := Γ₁) (Δ := Δ')
        (activeSendCount S b.q_on * activeIdCount S b.q_on)
        (activeSendOpkCount S b.q_on * activeOpkCount S b.q_on) _ _ Bleaf
        (fun {Δ''} [_] => hLeafB (Δ' := Δ'')) (fun {Δ''} [_] => hLeafD (Δ' := Δ''))).trans (by dsimp [Bleaf, Bmid]; omega))
    dsimp [Bmid] at hTop; omega

private theorem fgKeyInd1KeyGapDhActiveDslProg_init_cost_le_min (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).init.cost ≤
      30 * Nat.log 2 S.N_dh + 10 * b.q_total + 300 := by
  have hP := initParams1KeyActiveC_cost_le S b
    (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
    (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero
  have hsb : Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget S b ≤ b.q_total := Nat.min_le_left _ _
  have bSb : bits (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget S b) ≤ b.q_total + 1 :=
    (_root_.ReductionDsl.bits_mono hsb).trans (bits_le_succ b.q_total)
  have hsB : (gPrim (sBool (Γ := paramsTy :: .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]))).cost ≤ 4 :=
    (Comp.cost_le_costUB _).trans (by simp [sBool_costUB])
  dsimp only [fgKeyInd1KeyGapDhActiveDslProg]
  simp only [letV, bindV, liftGdhComp_cost, emptySimE, smMk, emptyStE, stMk,
    v, Comp.cost, Expr.cost, bits_0]
  omega


private theorem callGdhActiveHandle_cost_le (S : Setup) (K : Nat) {Δ : List PT} (stA : Var Δ gdh1KeyActiveStateTy) (q :
  Var Δ keyIndQueryTy) : (callGdhActiveHandle S K stA q).cost ≤ 28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot +
  60990 := by
  have h := callGdhActiveHandle_cost_le_min S K stA q
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

private theorem initPrin1KeyActiveGdhB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁
  gdh1KeyActiveStateTy) (u : Var Γ₂ .nat) : (initPrin1KeyActiveGdhB K (Δ := Δ) stA u).cost ≤ 7 * K + 450 := by
  refine le_trans (initPrin1KeyActiveGdhB K (Δ := Δ) stA u).cost_le_costUB ?_
  simp only [initPrin1KeyActiveGdhB, stPrin, stUpd, stSecb, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
    stKyb, stRo, stAdv, stMk, peMk, smUpd, smMk, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB,
    smPows_costUB, paUp_costUB, paPrinFlag_costUB, paPrinIdx_costUB, rNone_costUB, rInitPrin_costUB, natEq,
    letV_costUB, bindV_costUB, eAny_costUB, liftGdhComp_costUB, gPrim_costUB, sBytes32_costUB,
    qX25519Base_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  omega

private theorem genSpk1KeyActiveGdhB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁
  gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat .nat)) : (genSpk1KeyActiveGdhB K (Δ := Δ) stA x).cost ≤ 40 * K + 19000 := by
  refine le_trans (genSpk1KeyActiveGdhB K (Δ := Δ) stA x).cost_le_costUB ?_
  simp only [genSpk1KeyActiveGdhB, genSpkGdhActiveB, optNatMatchesE, eLet2, eLet, eCaseOpt_costUB, stPrin, stSpks, stUpd, stSecb, stOpks,
    stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peIkAPk, peSecIKAsign, sbMk, buMk, smUpd, smMk,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, paV_costUB, paSpkIdx_costUB, rNone_costUB,
    rBundle_costUB, natEq, nat2Eq, encEC_costUB, encKEM_costUB, letV_costUB, bindV_costUB, caseOptV_costUB, eAny_costUB,
    eFind_costUB, liftGdhComp_costUB, gPrim_costUB, sigChalQ_dsl_costUB, sBytes32_costUB, sRandom64_costUB,
    qX25519Base_costUB, qKemKeyGen_costUB, qSigSign_costUB, litB_costUB, u32OfNat_costUB, v_costUB, Comp.costUB,
    Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]
  omega

private theorem genOpkActiveGdhB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁
  gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) : (genOpkActiveGdhB K (Δ := Δ) stA x).cost ≤ 30 * K
  + 500 := by
  refine le_trans (genOpkActiveGdhB K (Δ := Δ) stA x).cost_le_costUB ?_
  simp only [genOpkActiveGdhB, stOpks, stUpd, stSecb, stPrin, stSpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo,
    stAdv, stMk, oeMk, smUpd, smMk, smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, paV_costUB,
    paOpkMode_costUB, paOpkIdx_costUB, rNone_costUB, rPk_costUB, natEq, nat2Eq, nat3Eq, letV_costUB, bindV_costUB,
    eAny_costUB, liftGdhComp_costUB, gPrim_costUB, sBytes32_costUB, qX25519Base_costUB, litB_costUB, v_costUB,
    Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  omega

private theorem initiateActiveGdhB_cost_le (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy) :
    (initiateActiveGdhB S K hasOpk (Δ := Δ) stA x).cost ≤
      7000 * K + 3000 * S.N_dh + 8000 * S.N_sess_tot + 25000 := by
  have h := initiateActiveGdhB_cost_le_min S K hasOpk (Δ := Δ) stA x
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

private theorem caseSumV_cost_add_le' {Γ : List PT} {τ₁ τ₂ τ : PT} (x : Var Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqSigAndDdhIface (τ₂ :: Γ) τ)
    {d c : ℕ} (hl : (kl .zero).cost + (d + 2) ≤ c) (hr : (kr .zero).cost + (d + 2) ≤ c) :
    (caseSumV (v x) kl kr).cost + d ≤ c := by simp only [caseSumV, v, Comp.cost, Expr.cost]; omega

private theorem gdh1KeyActiveHandle_cost_le_min_tight (S : Setup) (K : Nat) :
    (gdh1KeyActiveHandle S K).cost ≤
      20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30110 := by
  unfold gdh1KeyActiveHandle; refine Nat.le_of_add_right_le (k := 0) ?_
  refine caseSumV_cost_add_le' _ _ _ ((Nat.add_le_add_right (initPrin1KeyActiveGdhB_cost_le _ _ _) 2).trans (by omega)) ?_
  refine caseSumV_cost_add_le' _ _ _ ((Nat.add_le_add_right (callGdhActiveHandle_cost_le_min_tight S K _ _) 4).trans (by omega)) ?_
  refine caseSumV_cost_add_le' _ _ _ ((Nat.add_le_add_right (genSpk1KeyActiveGdhB_cost_le _ _ _) 6).trans (by omega)) ?_
  refine caseSumV_cost_add_le' _ _ _ ((Nat.add_le_add_right (genOpkActiveGdhB_cost_le _ _ _) 8).trans (by omega)) ?_
  refine caseSumV_cost_add_le' _ _ _ ((Nat.add_le_add_right (initiateActiveGdhB_cost_le_min S K true _ _) 10).trans (by omega)) ?_
  exact caseSumV_cost_add_le' _ _ _ ((Nat.add_le_add_right (initiateActiveGdhB_cost_le_min S K false _ _) 12).trans (by omega))
    ((Nat.add_le_add_right (callGdhActiveHandle_cost_le_min_tight S K _ _) 12).trans (by omega))

private theorem gdh1KeyActiveHandle_cost_le_min (S : Setup) (K : Nat) :
    (gdh1KeyActiveHandle S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 61010 :=
  (gdh1KeyActiveHandle_cost_le_min_tight S K).trans (by omega)

private theorem gdh1KeyActiveHandle_cost_le (S : Setup) (K : Nat) : (gdh1KeyActiveHandle S K).cost ≤ 28015 * K + 27171 *
  S.N_dh + 14742 * S.N_sess_tot + 61010 := by
  have h := gdh1KeyActiveHandle_cost_le_min S K
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

private theorem fgKeyInd1KeyGapDhActiveDslProg_init_cost_le (S : Setup) (b : QueryBudget) :
  (fgKeyInd1KeyGapDhActiveDslProg S b).init.cost ≤ 26 * S.N_dh ^ 2 + 17 * S.N_dh + 10 * b.q_total + 300 := by
  have h := fgKeyInd1KeyGapDhActiveDslProg_init_cost_le_min S b
  have hLog : Nat.log 2 S.N_dh ≤ S.N_dh := Nat.log_le_self 2 S.N_dh
  cases hN : S.N_dh with
  | zero => simp [hN] at h; omega
  | succ n =>
    rw [hN] at hLog h
    nlinarith

private theorem max1_add32_le {c u : ℕ} (hc : c ≤ u) : max 1 (c + 32) ≤ u + 32 := by omega

private theorem fgKeyInd1KeyGapDhActiveDslProg_totalCost_clamped_le_tight (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).totalCost b.q_total ≤
      730 + 32285 * b.q_total +
        423 * min b.q_total S.N_dh + 263 * min b.q_total S.N_sess_tot +
        30 * (b.q_total + 1) * Nat.log 2 S.N_dh +
        20000 * (b.q_total * b.q_total) +
        10069 * (b.q_total * min b.q_total S.N_dh) +
        10000 * (b.q_total * min b.q_total S.N_sess_tot) +
        69 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        66 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by
  have hI := fgKeyInd1KeyGapDhActiveDslProg_init_cost_le_min S b
  have hF : (gdh1KeyActiveFinish S b.q_total).cost ≤
      69 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        69 * (b.q_total * min b.q_total S.N_dh) +
        66 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) +
        423 * min b.q_total S.N_dh + 263 * min b.q_total S.N_sess_tot +
        2132 * b.q_total + 420 := by
    clear hI
    have hFg := _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gdhFinish_cost_le_min S b.q_total
    have hSq : (min b.q_total S.N_dh) ^ 2 = min b.q_total S.N_dh * min b.q_total S.N_dh := by ring
    have h1 : 69 * b.q_total * min b.q_total S.N_dh = 69 * (b.q_total * min b.q_total S.N_dh) := by ring
    have h2 : 66 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot =
      66 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
    rw [hSq, h1, h2] at hFg
    simp only [gdh1KeyActiveFinish, letV, v, Comp.cost, Expr.cost, renameComp_cost, liftGdhComp_cost]
    omega
  have hq := Nat.mul_le_mul_left b.q_total (max1_add32_le (gdh1KeyActiveHandle_cost_le_min_tight S b.q_total))
  have hSum : (fgKeyInd1KeyGapDhActiveDslProg S b).totalCost b.q_total ≤
      (30 * Nat.log 2 S.N_dh + 10 * b.q_total + 300) +
      b.q_total * (20000 * b.q_total + 10000 * min b.q_total S.N_dh +
        10000 * min b.q_total S.N_sess_tot + 30110 + 32) +
      (69 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        69 * (b.q_total * min b.q_total S.N_dh) +
        66 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) +
        423 * min b.q_total S.N_dh + 263 * min b.q_total S.N_sess_tot +
        2132 * b.q_total + 420) :=
    Nat.add_le_add (Nat.add_le_add hI hq) hF
  clear hI hF hq
  refine hSum.trans ?_
  clear hSum
  have hExp : b.q_total * (20000 * b.q_total + 10000 * min b.q_total S.N_dh +
        10000 * min b.q_total S.N_sess_tot + 30110 + 32) =
      30142 * b.q_total + 20000 * (b.q_total * b.q_total) +
        10000 * (b.q_total * min b.q_total S.N_dh) +
        10000 * (b.q_total * min b.q_total S.N_sess_tot) := by ring
  rw [hExp]
  have hLog : 30 * Nat.log 2 S.N_dh ≤ 30 * (b.q_total + 1) * Nat.log 2 S.N_dh := by
    have : 30 ≤ 30 * (b.q_total + 1) := by omega
    exact Nat.mul_le_mul_right _ this
  omega

private theorem fgKeyInd1KeyGapDhActiveDslProg_totalCost_clamped_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).totalCost b.q_total ≤
      730 + 63185 * b.q_total +
        423 * min b.q_total S.N_dh + 263 * min b.q_total S.N_sess_tot +
        30 * (b.q_total + 1) * Nat.log 2 S.N_dh +
        28015 * (b.q_total * b.q_total) +
        27234 * (b.q_total * min b.q_total S.N_dh) +
        14742 * (b.q_total * min b.q_total S.N_sess_tot) +
        69 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        66 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) :=
  (fgKeyInd1KeyGapDhActiveDslProg_totalCost_clamped_le_tight S b).trans (by omega)

private theorem fgKeyInd1KeyGapDhActiveDslProg_totalCost_poly_le (S : Setup) (b : QueryBudget) :
  (fgKeyInd1KeyGapDhActiveDslProg S b).totalCost b.q_total ≤ 730 + 63185 * b.q_total + 440 * S.N_dh + 263 * S.N_sess_tot
  + 28015 * (b.q_total * b.q_total) + 27240 * (b.q_total * S.N_dh) + 14742 * (b.q_total * S.N_sess_tot) + 95 * (S.N_dh *
  S.N_dh) + 66 * (S.N_dh * S.N_sess_tot) := by
  have hI := fgKeyInd1KeyGapDhActiveDslProg_init_cost_le S b
  have hF : (gdh1KeyActiveFinish S b.q_total).cost ≤
      69 * S.N_dh ^ 2 + 69 * b.q_total * S.N_dh + 66 * S.N_dh * S.N_sess_tot +
        423 * S.N_dh + 263 * S.N_sess_tot + 2132 * b.q_total + 420 := by
    clear hI
    have hFg := gdhFinish_cost_le S b.q_total
    simp only [gdh1KeyActiveFinish, letV, v, Comp.cost, Expr.cost, renameComp_cost, liftGdhComp_cost]; omega
  have hq := Nat.mul_le_mul_left b.q_total (max1_add32_le (gdh1KeyActiveHandle_cost_le S b.q_total))
  have hSum : (fgKeyInd1KeyGapDhActiveDslProg S b).totalCost b.q_total ≤
      (26 * S.N_dh ^ 2 + 17 * S.N_dh + 10 * b.q_total + 300) +
      b.q_total * (28015 * b.q_total + 27171 * S.N_dh + 14742 * S.N_sess_tot + 61010 + 32) +
      (69 * S.N_dh ^ 2 + 69 * b.q_total * S.N_dh + 66 * S.N_dh * S.N_sess_tot +
        423 * S.N_dh + 263 * S.N_sess_tot + 2132 * b.q_total + 420) :=
    Nat.add_le_add (Nat.add_le_add hI hq) hF
  clear hI hF hq
  refine hSum.trans ?_
  clear hSum
  have hExp : b.q_total * (28015 * b.q_total + 27171 * S.N_dh + 14742 * S.N_sess_tot + 61010 + 32) =
      61042 * b.q_total + 28015 * (b.q_total * b.q_total) +
        27171 * (b.q_total * S.N_dh) + 14742 * (b.q_total * S.N_sess_tot) := by ring
  have hSq : S.N_dh ^ 2 = S.N_dh * S.N_dh := by ring
  have hKdh : 69 * b.q_total * S.N_dh = 69 * (b.q_total * S.N_dh) := by ring
  have hDhS : 66 * S.N_dh * S.N_sess_tot = 66 * (S.N_dh * S.N_sess_tot) := by ring
  rw [hExp, hSq, hKdh, hDhS]
  omega


end DslCostAndQueries

section PotHelpers
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] pqChalIface pqPrimIface gapDhDdhOracle sigAndDdhOracle pqSamplers
attribute [local simp] Expr.eval Env.get Ext.step_wk Ext.refl_wk

private theorem letV_s1_eval {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (letV e k).eval env = (k .zero).eval (.cons (e.eval env) env) := by simp [letV, Comp.eval]

private theorem potC_gdh_bind1 (m : ℕ+) {Γ : List PT} {τ₂ : PT} {Pot : τ₂.denote → ℕ}
    (arg : Expr pqxdhOps Γ (B m)) (k : Comp pqxdhOps pqSigAndDdhIface (B 64 :: Γ) τ₂)
    (env : Env Γ) {r n : ℕ}
    (hk : ∀ x, PotOK isSigChal1KeyQ Pot (k.eval (.cons x env)) r) (hmn : 1 + r ≤ n) :
    PotOK isSigChal1KeyQ Pot ((Comp.bind (sigChalQ_dsl m arg) k).eval env) n :=
  potC_bind lcSigW lcZeroWS hwSigChal1Key hUSigChal1Key _ k env hk (by
    have hq : (sigChalQ_dsl m arg).queries lcSigW lcZeroWS = 1 := rfl; omega)

private def sigActivePot (st : sig1KeyActiveStTy.denote) : ℕ := sigPot1Key st.2
private def preActivePot (m : ℕ) : (S1ARS.denote ⊕ Unit) → ℕ
  | .inl r => sigActivePot r.2 | .inr () => m

private theorem sig1KeyActiveInitPrinB_potOK (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁
  sig1KeyActiveStTy) (u : Var Γ₂ .nat) (env : Env Δ) {n : ℕ} (hn : sigActivePot ((v st : Expr pqxdhOps Δ
  sig1KeyActiveStTy).eval env) ≤ n) : PotOK isSigChal1KeyQ (fun r : S1ARS.denote => sigActivePot r.2)
  ((sig1KeyActiveInitPrinB K st u).eval env) n := by
  unfold sig1KeyActiveInitPrinB; rw [letV_s1_eval]; unfold bindV
  refine @potC_s1_ite _ S1ARS _ _ _ _ _ n (fun _ => @potC_s1_ret _ S1ARS _ _ _ n
    (by simpa [sigActivePot, sigPot1Key, v] using hn)) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ S1ARS _ _ _ _ n (by simp) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ S1ARS _ _ _ _ n (by simp) (fun _ => ?_)
  exact @potC_s1_ret _ S1ARS _ _ _ n (by simpa [sigActivePot, sigPot1Key, saInner, s1Upd, s1Mk, s1Budget, v] using hn)

private theorem sig1KeyActiveInitiateCheckC_potOK (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st :
  Var Γ₁ sig1KeyActiveStTy) (x : Var Γ₂ initQTy) (env : Env Δ) {n : ℕ} (hn : sigActivePot ((v st : Expr pqxdhOps Δ
  sig1KeyActiveStTy).eval env) ≤ n) : PotOK isSigChal1KeyQ (preActivePot n) ((sig1KeyActiveInitiateCheckC S K st x).eval
  env) n := by
  unfold sig1KeyActiveInitiateCheckC; rw [letV_s1_eval]; unfold bindV
  refine @potC_s1_bind0 _ _ (.sum S1ARS .unit) (preActivePot n) _ _ _ n
    (by simp [extract1KeyActiveC, letV, bindV, Comp.queries]) (fun _ => ?_)
  refine @potC_s1_ite _ (.sum S1ARS .unit) (preActivePot n) _ _ _ _ n (fun _ => @potC_s1_ret _ (.sum S1ARS .unit)
    (preActivePot n) _ _ n
    (by simpa [preActivePot, sigActivePot, sigPot1Key, saInner, s1Upd, s1Mk, s1Budget, v] using hn)) (fun _ =>
    @potC_s1_ret _ (.sum S1ARS .unit) (preActivePot n) _ _ n (by simp [preActivePot]))

private theorem sig1KeyActivePreDispatchC_potOK (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var
  Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) (env : Env Δ) {n : ℕ} (hn : sigActivePot ((v st : Expr pqxdhOps Δ
  sig1KeyActiveStTy).eval env) ≤ n) : PotOK isSigChal1KeyQ (preActivePot n) ((sig1KeyActivePreDispatchC S K st q).eval
  env) n := by
  unfold sig1KeyActivePreDispatchC caseSumV bindV
  refine @potC_s1_ite _ (.sum S1ARS .unit) (preActivePot n) _ _ _ env n (fun _ => @potC_s1_ret _ (.sum S1ARS .unit)
    (preActivePot n) _ env n (by simpa [preActivePot, sigActivePot, sigPot1Key, v] using hn)) (fun _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1ARS .unit) (preActivePot n) _ _ _ env n (fun u _ => PotOK.bindPot
    (sig1KeyActiveInitPrinB_potOK K st .zero (.cons u env) (by simpa [sigActivePot, v] using hn)) (fun _ => @potC_s1_ret
    _ (.sum S1ARS .unit) (preActivePot n) _ _ _ (by simp [preActivePot, v]))) (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1ARS .unit) (preActivePot n) _ _ _ _ n (fun _ _ => @potC_s1_ret _ (.sum S1ARS
    .unit) (preActivePot n) _ _ n (by simp [preActivePot])) (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1ARS .unit) (preActivePot n) _ _ _ _ n
    (fun _ _ => @potC_s1_ite _ (.sum S1ARS .unit) (preActivePot n) _ _ _ _ n
      (fun _ => by
        rw [letV_s1_eval]
        refine PotOK.bindPot (B₁ := fun r : S1RS.denote => sigPot1Key r.2) ?_ (fun _ => @potC_s1_ret _ (.sum S1ARS
          .unit) (preActivePot n) _ _ _ (by simp [preActivePot, sigActivePot, v]))
        exact sig1KeyTargetGenSpkB_potOK K .zero .zero _ (by simpa [sigActivePot, sigPot1Key, saInner, v] using hn))
      (fun _ => @potC_s1_ret _ (.sum S1ARS .unit) (preActivePot n) _ _ n (by simp [preActivePot])))
    (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1ARS .unit) (preActivePot n) _ _ _ _ n (fun _ _ => @potC_s1_ret _ (.sum S1ARS
    .unit) (preActivePot n) _ _ n (by simp [preActivePot])) (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1ARS .unit) (preActivePot n) _ _ _ _ n (fun _ _ =>
    sig1KeyActiveInitiateCheckC_potOK S K st .zero _ (by simpa [sigActivePot, v] using hn)) (fun _ _ => ?_)
  exact @potC_s1_caseSum _ _ _ (.sum S1ARS .unit) (preActivePot n) _ _ _ _ n (fun _ _ =>
    sig1KeyActiveInitiateCheckC_potOK S K st .zero _ (by simpa [sigActivePot, v] using hn)) (fun _ _ => @potC_s1_ret _
    (.sum S1ARS .unit) (preActivePot n) _ _ n (by simp [preActivePot]))

private theorem liftGdhToSigDdh_sigQueries_zero {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries lcSigW lcZeroWS = 0 := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

private theorem sig1KeyActiveHandleC_potOK (S : Setup) (K : ℕ) (st : sig1KeyActiveStTy.denote) (q :
  keyIndQueryTy.denote) : PotOK isSigChal1KeyQ (fun r : S1ARS.denote => sigActivePot r.2) ((sig1KeyActiveHandleC S
  K).eval (.cons st (.cons q .nil))) (sigActivePot st) := by
  unfold sig1KeyActiveHandleC caseSumV
  change PotOK isSigChal1KeyQ _ ((Comp.bind (sig1KeyActivePreDispatchC S K .zero (.succ .zero)) _).eval _) _
  refine PotOK.bindPot (sig1KeyActivePreDispatchC_potOK S K .zero (.succ .zero) (.cons st (.cons q .nil)) le_rfl) (fun
    pre => ?_)
  refine @potC_s1_caseSum _ _ _ S1ARS (fun r => sigActivePot r.2) _ _ _ _ (preActivePot (sigActivePot st) pre) (fun _
    hres => ?_) (fun u hu => ?_)
  · simp only [Expr.eval, v, Ext.refl_wk] at hres; subst hres
    exact @potC_s1_ret _ S1ARS (fun r => sigActivePot r.2) _ _ _ (by simp [preActivePot, v])
  · simp only [Expr.eval, v, Ext.refl_wk] at hu; subst hu; cases u
    iterate 2 rw [letV_s1_eval]
    unfold bindV
    refine @potC_s1_bind0 _ _ S1ARS (fun r => sigActivePot r.2) _ _ _ (sigActivePot st)
      (liftGdhToSigDdh_sigQueries_zero _) (fun _ => ?_)
    exact @potC_s1_ret _ S1ARS (fun r => sigActivePot r.2) _ _ (sigActivePot st)
      (by simp [sigActivePot, sigPot1Key, v])

theorem sigKeyInd1KeyActiveDslProg_sigBounded (S : Setup) (b : QueryBudget) (A : Unit → OracleComp (unifSpec +
  keyIndSpec S) Bool) (pk : Bytes) : ((sigKeyInd1KeyActiveDslProg S b).eval A pk).IsQueryBoundP (fun q => isSigChalQuery
  q = true) (2 * min S.N_spk_tot S.N_recv) := by
  have hInit : PotOK isSigChal1KeyQ (fun p : Unit × sig1KeyActiveStTy.denote => sigActivePot p.2)
      ((sigKeyInd1KeyActiveDslProg S b).init.eval (.cons pk .nil))
      (2 * min S.N_spk_tot S.N_recv) := by
    dsimp only [sigKeyInd1KeyActiveDslProg]; unfold bindV
    refine @potC_s1_bind0 _ _ (.prod .unit sig1KeyActiveStTy) _ _ _ _ _ (by simp) (fun _ => ?_)
    refine @potC_s1_bind0 _ _ (.prod .unit sig1KeyActiveStTy) _ _ _ _ _ (by simp) (fun _ => ?_)
    exact @potC_s1_ret _ (.prod .unit sig1KeyActiveStTy) _ _ _ _
      (by
        simp [sigActivePot, sigPot1Key,
          Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget])
  unfold CostedReduction.eval CostedReduction.impl
  refine PotOK.toQueryBound (P := isSigChal1KeyQ) (B := fun _ => 0) ?_ (fun _ => rfl)
  refine PotOK.bindPot hInit (fun as => ?_)
  exact PotOK.bindPot (B₁ := fun x : Bool × sig1KeyActiveStTy.denote => sigActivePot x.2) (potOK_simulateQ_handlerImpl
    sigActivePot hUSigChal1Key (sigKeyInd1KeyActiveDslProg S b).handle (fun gq st => sig1KeyActiveHandleC_potOK S
    b.q_total st gq) (A as.1) as.2) (fun _ => @potC_s1_ret _ _ _ _ _ _ (Nat.zero_le _))

private abbrev G1ARS : PT := .prod keyIndRespTy gdh1KeyActiveStateTy
private def gdhActivePot (stA : gdh1KeyActiveStateTy.denote) : ℕ := 2 * stA.1.2

private theorem callGdhHandle_potOK (S : Setup) (K : ℕ) {Δ : List PT} (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ
  keyIndQueryTy) (env : Env Δ) {n : ℕ} (hn : 2 * ((v st1 : Expr pqxdhOps Δ gdh1KeyStateTy).eval env).2 ≤ n) : PotOK
  isSigChal1KeyQ (fun r : (Ty.prod keyIndRespTy gdh1KeyStateTy).denote => 2 * r.2.2) ((callGdhHandle S K st1 q).eval
  env) n := by
  unfold callGdhHandle; rw [letV_s1_eval]; unfold bindV
  refine @potC_s1_bind0 _ _ (.prod keyIndRespTy gdh1KeyStateTy) _ _ _ _ n
    (by change (renameComp _ (liftGdhComp (gdhHandle S K))).queries wSig1Key wsZero1Key = 0; simp)
    (fun _ => @potC_s1_ret _ (.prod keyIndRespTy gdh1KeyStateTy) _ _ _ n (by simpa [v] using hn))

private theorem callGdhActiveHandle_potOK (S : Setup) (K : ℕ) {Δ : List PT} (stA : Var Δ gdh1KeyActiveStateTy) (q : Var
  Δ keyIndQueryTy) (env : Env Δ) {n : ℕ} (hn : gdhActivePot ((v stA : Expr pqxdhOps Δ gdh1KeyActiveStateTy).eval env) ≤
  n) : PotOK isSigChal1KeyQ (fun r : G1ARS.denote => gdhActivePot r.2) ((callGdhActiveHandle S K stA q).eval env) n := by
  unfold callGdhActiveHandle
  iterate 3 rw [letV_s1_eval]
  unfold bindV
  refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n
    (by
      change (renameComp _ (liftGdhComp (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K))).queries
        wSig1Key wsZero1Key = 0
      simp)
    (fun _ => @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn))

private theorem initPrin1KeyActiveGdhB_potOK (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁
  gdh1KeyActiveStateTy) (u : Var Γ₂ .nat) (env : Env Δ) {n : ℕ} (hn : gdhActivePot ((v stA : Expr pqxdhOps Δ
  gdh1KeyActiveStateTy).eval env) ≤ n) : PotOK isSigChal1KeyQ (fun r : G1ARS.denote => gdhActivePot r.2)
  ((initPrin1KeyActiveGdhB K stA u).eval env) n := by
  unfold initPrin1KeyActiveGdhB
  iterate 4 rw [letV_s1_eval]
  refine @potC_s1_ite _ G1ARS _ _ _ _ _ n (fun _ => @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn))
    (fun _ => ?_)
  rw [letV_s1_eval]; unfold bindV
  refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
  iterate 2 rw [letV_s1_eval]
  exact @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn)

private theorem genSpk1KeyActiveGdhB_potOK (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁
  gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ) {n : ℕ} (hn : gdhActivePot ((v stA : Expr pqxdhOps
  Δ gdh1KeyActiveStateTy).eval env) ≤ n) : PotOK isSigChal1KeyQ (fun r : G1ARS.denote => gdhActivePot r.2)
  ((genSpk1KeyActiveGdhB K stA x).eval env) n := by
  unfold genSpk1KeyActiveGdhB
  iterate 5 rw [letV_s1_eval]
  refine @potC_s1_ite _ G1ARS _ _ _ _ _ n (fun _ => ?_) (fun _ => ?_)
  · refine @potC_s1_ite _ G1ARS _ _ _ _ _ n
      (fun _ => @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn)) (fun _ => ?_)
    unfold caseOptV
    refine @potC_s1_caseOpt _ _ _ _ _ _ _ _ n (fun _ => @potC_s1_ret _ G1ARS _ _ _ n
      (by simpa [gdhActivePot, v] using hn)) (fun _ _ => ?_)
    refine @potC_s1_ite _ G1ARS _ _ _ _ _ n (fun _ => @potC_s1_ret _ G1ARS _ _ _ n
      (by simpa [gdhActivePot, v] using hn)) (fun hb => ?_)
    let bud : ℕ := (env.get (Ext.wk stA)).1.2
    simp only [Expr.eval, natEq, v, Env.get, Ext.step_wk, Ext.refl_wk, decide_eq_false_iff_not] at hb
    have hb' : bud ≠ 0 := hb
    have hn' : 2 * bud ≤ n := by simpa [bud, gdhActivePot, v] using hn
    rw [letV_s1_eval]; unfold bindV
    refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
    refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
    iterate 2 rw [letV_s1_eval]
    refine @potC_gdh_bind1 33 _ _ _ _ _ _ (n - 1) n (fun _ => ?_) (by omega)
    refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ (n - 1) (liftGdhComp_queries_sig _) (fun _ => ?_)
    refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ (n - 1) (liftGdhComp_queries_sig _) (fun _ => ?_)
    refine @potC_gdh_bind1 1569 _ _ _ _ _ _ (n - 2) (n - 1) (fun _ => ?_) (by omega)
    exact @potC_s1_ret _ G1ARS _ _ _ (n - 2) (by change 2 * (bud - 1) ≤ n - 2; omega)
  · unfold bindV
    refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
    exact @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn)

private theorem genOpkActiveGdhB_potOK (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁
  gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) (env : Env Δ) {n : ℕ} (hn : gdhActivePot ((v stA :
  Expr pqxdhOps Δ gdh1KeyActiveStateTy).eval env) ≤ n) : PotOK isSigChal1KeyQ (fun r : G1ARS.denote => gdhActivePot r.2)
  ((genOpkActiveGdhB K stA x).eval env) n := by
  unfold genOpkActiveGdhB
  iterate 4 rw [letV_s1_eval]
  refine @potC_s1_ite _ G1ARS _ _ _ _ _ n (fun _ => @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn))
    (fun _ => ?_)
  rw [letV_s1_eval]; unfold bindV
  refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
  iterate 2 rw [letV_s1_eval]
  exact @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn)

private theorem initiateActiveGdhB_potOK (S : Setup) (K : ℕ) (hasOpk : Bool) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
  (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy) (env : Env Δ) {n : ℕ} (hn : gdhActivePot ((v stA : Expr
  pqxdhOps Δ gdh1KeyActiveStateTy).eval env) ≤ n) : PotOK isSigChal1KeyQ (fun r : G1ARS.denote => gdhActivePot r.2)
  ((initiateActiveGdhB S K hasOpk stA x).eval env) n := by
  unfold initiateActiveGdhB
  iterate 5 rw [letV_s1_eval]
  unfold bindV
  refine @potC_s1_bind0 _ _ G1ARS _ _ _ _ n (liftGdhComp_queries_sig _) (fun _ => ?_)
  exact @potC_s1_ret _ G1ARS _ _ _ n (by simpa [gdhActivePot, v] using hn)

private theorem gdh1KeyActiveHandle_potOK (S : Setup) (K : ℕ) (stA : gdh1KeyActiveStateTy.denote) (q :
  keyIndQueryTy.denote) : PotOK isSigChal1KeyQ (fun r : G1ARS.denote => gdhActivePot r.2) ((gdh1KeyActiveHandle S
  K).eval (.cons stA (.cons q .nil))) (gdhActivePot stA) := by
  unfold gdh1KeyActiveHandle caseSumV
  refine @potC_s1_caseSum _ _ _ G1ARS _ _ _ _ (.cons stA (.cons q .nil)) (gdhActivePot stA) (fun _ _ =>
    initPrin1KeyActiveGdhB_potOK K .zero .zero _ (by simp [gdhActivePot, v])) (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ G1ARS _ _ _ _ _ (gdhActivePot stA) (fun _ _ => callGdhActiveHandle_potOK S K (.succ
    (.succ .zero)) (.succ (.succ (.succ .zero))) _ (by simp [gdhActivePot, v])) (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ G1ARS _ _ _ _ _ (gdhActivePot stA) (fun _ _ => genSpk1KeyActiveGdhB_potOK K .zero .zero
    _ (by simp [gdhActivePot, v])) (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ G1ARS _ _ _ _ _ (gdhActivePot stA) (fun _ _ => genOpkActiveGdhB_potOK K .zero .zero _
    (by simp [gdhActivePot, v])) (fun _ _ => ?_)
  refine @potC_s1_caseSum _ _ _ G1ARS _ _ _ _ _ (gdhActivePot stA) (fun _ _ => initiateActiveGdhB_potOK S K true .zero
    .zero _ (by simp [gdhActivePot, v])) (fun _ _ => ?_)
  exact @potC_s1_caseSum _ _ _ G1ARS _ _ _ _ _ (gdhActivePot stA) (fun _ _ => initiateActiveGdhB_potOK S K false .zero
    .zero _ (by simp [gdhActivePot, v])) (fun _ _ => callGdhActiveHandle_potOK S K (.succ (.succ (.succ (.succ (.succ
    (.succ .zero)))))) (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) _ (by simp [gdhActivePot, v]))

private theorem gdh1KeyActiveFinish_potOK (S : Setup) (K : ℕ) (stA : gdh1KeyActiveStateTy.denote) (bOut : Bool) {n : ℕ}
  : PotOK isSigChal1KeyQ (fun _ : Bytes => 0) ((gdh1KeyActiveFinish S K).eval (.cons stA (.cons bOut .nil))) n := by
  unfold gdh1KeyActiveFinish; rw [letV_s1_eval]
  have h0 : (renameComp (twoVarRen .zero (.succ (.succ .zero)))
      (liftGdhComp (gdhFinish S K)) : Comp pqxdhOps pqSigAndDdhIface
        [gdhStateTy, gdh1KeyActiveStateTy, .bool] (B 32)).queries lcSigW lcZeroWS = 0 := by
    change (renameComp _ (liftGdhComp (gdhFinish S K))).queries wSig1Key wsZero1Key = 0; simp
  have hRewrite : ∀ {Γ} (c : Comp pqxdhOps pqSigAndDdhIface Γ (B 32)) (env : Env Γ),
      c.eval env = (Comp.bind c (.ret (.var .zero))).eval env := fun _ _ => by simp [Comp.eval]
  rw [hRewrite]
  exact @potC_s1_bind0 _ _ (B 32) (fun _ => 0) _ _ _ n h0 (fun _ => @potC_s1_ret _ (B 32) (fun _ => 0) _ _ n
    (Nat.zero_le n))

theorem fgKeyInd1KeyGapDhActiveDslProg_sigBounded (S : Setup) (b : QueryBudget) (A : Unit → OracleComp (unifSpec +
  keyIndSpec S) Bool) (U V : Bytes) : ((fgKeyInd1KeyGapDhActiveDslProg S b).eval A (U, V)).IsQueryBoundP (fun q =>
  isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  have hInit : PotOK isSigChal1KeyQ (fun p : Unit × gdh1KeyActiveStateTy.denote => gdhActivePot p.2)
      ((fgKeyInd1KeyGapDhActiveDslProg S b).init.eval (.cons (U, V) .nil))
      (2 * min S.N_spk_tot S.N_recv) := by
    dsimp only [fgKeyInd1KeyGapDhActiveDslProg]; rw [letV_s1_eval]; unfold bindV
    refine @potC_s1_bind0 _ _ (.prod .unit gdh1KeyActiveStateTy) _ _ _ _ _ (liftGdhComp_queries_sig _) (fun _ => ?_)
    refine @potC_s1_bind0 _ _ (.prod .unit gdh1KeyActiveStateTy) _ _ _ _ _ (liftGdhComp_queries_sig _) (fun _ => ?_)
    exact @potC_s1_ret _ (.prod .unit gdh1KeyActiveStateTy) _ _ _ _
      (by simp [gdhActivePot, Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.activeSigBudget])
  unfold CostedReduction.eval CostedReduction.impl
  refine PotOK.toQueryBound (P := isSigChal1KeyQ) (B := fun _ => 0) ?_ (fun _ => rfl)
  refine PotOK.bindPot hInit (fun as => ?_)
  exact PotOK.bindPot (B₁ := fun x : Bool × gdh1KeyActiveStateTy.denote => gdhActivePot x.2)
    (potOK_simulateQ_handlerImpl gdhActivePot hUSigChal1Key (fgKeyInd1KeyGapDhActiveDslProg S b).handle (fun gq st =>
    gdh1KeyActiveHandle_potOK S b.q_total st gq) (A as.1) as.2) (fun bs => gdh1KeyActiveFinish_potOK S b.q_total bs.2
    bs.1)

end PotHelpers

private theorem sigAndDdh_ddhBounded_of_le (S : Setup) {ch out : PT}
    (R : CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S) ch .unit .bool out)
    {q B : Nat} (hR : R.totalQueries lcDdhW lcZeroWS q ≤ B)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) q) (c : ch.denote) :
    (R.eval A c).IsQueryBoundP (fun qr => isDdhChalQuery qr = true) B := by
  refine (CostedReduction.queryBound_eval R (fun qr => isDdhChalQuery qr = true) lcDdhW lcZeroWS ?_ ?_ A q hA c).mono hR
  · intro g x hx; rcases g with t | (m | ⟨⟩)
    · simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
    · simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
    · simp [lcDdhW, SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · intro n
    change IsQueryBoundP (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) : OracleComp
      (PrimBaseSpec + sigAndDdhSpec) _) (fun qr => isDdhChalQuery qr = true) 0
    rw [isQueryBoundP_query_iff]; simp [isDdhChalQuery]

private theorem sigAndDdh_primBounded_of_le (S : Setup) {ch out : PT}
    (R : CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S) ch .unit .bool out)
    {q B : Nat} (hR : R.totalQueries lcPrimW lcZeroWS q ≤ B)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) q) (c : ch.denote) :
    (R.eval A c).IsQueryBoundP (fun qr => isPrimQuery qr = true) B := by
  refine (CostedReduction.queryBound_eval R (fun qr => isPrimQuery qr = true) lcPrimW lcZeroWS ?_ ?_ A q hA c).mono hR
  · intro g x hx; rcases g with t | c'
    · simp [lcPrimW, SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    · simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) : OracleComp
      (PrimBaseSpec + sigAndDdhSpec) _) (fun qr => isPrimQuery qr = true) 0
    rw [isQueryBoundP_query_iff]; simp [isPrimQuery]

private theorem pullEnv_eq_ofRename :
    ∀ {Γ Δ : List PT} (ρ : SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ)
      (env : Env Δ),
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.pullEnv ρ env =
        _root_.ReductionDsl.Env.ofRename ρ env
  | [], _, _, _ => rfl
  | _ :: _, _, ρ, env => by
    simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.pullEnv,
      _root_.ReductionDsl.Env.ofRename, pullEnv_eq_ofRename (fun x => ρ (.succ x)) env]

private theorem liftRen_eq_liftRename {Γ Δ : List PT} {σ : PT}
    (ρ : SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ) :
    (fun {τ} => SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftRen (σ := σ) ρ (τ := τ)) =
      (fun {τ} => _root_.ReductionDsl.Var.liftRename (u := σ) (t := τ) ρ) := by
  funext τ x; cases x <;> rfl

private theorem renameExpr_eq_rename {Γ : List PT} {t : PT} (e : Expr pqxdhOps Γ t) :
    ∀ {Δ : List PT} (ρ : SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ),
    SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.renameExpr ρ e = e.rename ρ := by
  induction e <;> intro Δ ρ <;>
    simp [SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.renameExpr,
      _root_.ReductionDsl.Expr.rename, liftRen_eq_liftRename, *]

private theorem renameComp_eq_rename {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T} {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) :
    ∀ {Δ : List PT} (ρ : SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ),
    c.rename ρ = renameComp ρ c := by
  induction c <;> intro Δ ρ <;>
    simp [renameComp, _root_.ReductionDsl.Comp.rename, renameExpr_eq_rename, liftRen_eq_liftRename, *]

@[simp] private theorem comp_rename_eval {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T} {Γ Δ : List PT} {t : PT}
    (c : Comp pqxdhOps I Γ t)
    (ρ : SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ) (env : Env Δ) :
    (c.rename ρ).eval env = c.eval (_root_.ReductionDsl.Env.ofRename ρ env) := by
  rw [renameComp_eq_rename,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.renameComp_eval,
    pullEnv_eq_ofRename]

@[simp] private theorem liftGdhToSigDdh_eq_liftGdhComp {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    liftGdhToSigDdh c = liftGdhComp c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, liftGdhComp]

@[simp] private theorem liftGdhToSigDdh_eval {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) (env : Env Γ) :
    (liftGdhToSigDdh c).eval env =
      _root_.SignalPqxdh.Security.FgGapDh1Key.liftGdhToSign (c.eval env) := by
  rw [liftGdhToSigDdh_eq_liftGdhComp,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_eval]

section ActiveBilinearDdh

open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (S1ARS activeSigBudget
  callGdhActiveHandle extract1KeyActiveC fgKeyInd1KeyGapDhActiveDslProg gdh1KeyActiveFinish
  gdh1KeyActiveHandle gdh1KeyActiveStateTy genOpkActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB
  initParams1KeyActiveFlat initPrin1KeyActiveGdhB initiateActiveGdhB initiateGdhActiveInnerB
  optNatMatchesE saInner saTP sig1KeyActiveHandleC sig1KeyActiveInitPrinB sig1KeyActiveInitiateCheckC
  sig1KeyActivePreDispatchC sig1KeyActiveStTy sigKeyInd1KeyActiveDslProg)
open _root_.ReductionDsl (Comp Comp.rename_eval CostedReduction Env Env.ofRename Expr Ty Var handlerImpl
  isGameQuery isQueryBoundP_of_imp isQueryBoundP_or_add)
open _root_.SignalPqxdh (BoundedAdv Bytes KeyIndAdversary KeyIndQuery PrimBaseSpec QueryBudget Setup
  isDdhChalQuery isKeyIndRecvQuery isKeyIndRoQuery isKeyIndSendQuery keyIndSpec
  sigAndDdhSpec)
open _root_.SignalPqxdh.LegacyCosted (B gapDhDdhOracle keyIndCodec keyIndQenc pqChalIface
  pqGapDhIface pqPrimIface pqSigAndDdhIface pqxdhOps samplerZeroQueryWeight sigAndDdhOracle)
open _root_.SignalPqxdh.Security (gdhQueryBudget)
open _root_.SignalPqxdh.Security.Sig1Key (embedGdhSigDdh)
open _root_.SignalPqxdh.Security.FgGapDh (GdhSimSpec)
open _root_.SignalPqxdh.Security.FgGapDh1Key (GdhSignSimSpec liftGdhToSign)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (Env.get_succ' Env.get_zero' Ext Ext.refl_wk'
  Ext.step_wk' PT S1RS accQTy acceptNoOpkGdhB
  acceptOpkGdh2B bindV buIkB buMk buOpkB buPqspkB buPqspkId buPqspkSig buSpkB buSpkId buSpkSig
  caseOptV caseSumV checkProvC chooseInitRandC chooseRespRandC computeOptPosInitC computePosC ddhQ
  eAny eCaseOpt eFind emptySimE encEC encKEM eqB fgPatchC
  fgPatchEntryTy findHonestC finishAcceptGdhC gPrim gdhFinish gdhHandle2 gdhState2Ty gdhStateTy
  genOpkGdh2B genSpkGdh2B hdMk honestPeerC initPrinGdh2B initQTy initSidE initiateGdh2B isSomeE
  keyIndQueryTy keyIndRespTy keyIndStateTy koskBundleOkPowsC letV letV_eval liftBase liftGdhToSigDdh
  litB lookupSpkSkC mkSecretPosC nat2Eq nat3Eq natEq oeMk optFst optSnd pa2Mk
  paDhFlag paEphIdx paOpkIdx paOpkMode paPrinFlag paPrinIdx paSpkIdx paU paUp paV params2Ty
  paramsTy peIkAPk peMk peSecIKA0 peSecIKAsign qKemEncaps qKemKeyGen qSigDdhSign qSigSign
  qSigVerify qX25519Base rBundle rHdr rInitPrin rInitUnfresh rNone rPk registerGdhB renamePair
  resolveSigPkC s1Base s1Fg s1Forgery s1Mk s1Pk s1Prim s1Target s1Upd sBool sBytes32 sIndex
  sRandom64 sbMk sbPqspkPk sbSpkPk seMk seSid seUpd sidEq sig1KeyStTy sig1KeyTargetGenSpkB simTy
  smBase smFgL smMk smPows smUpd stOpks stPrin stSess stSpks stUpd u32OfNat v widenEC wrapBase2
  wrapSim2)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (DdhStep SessPost acceptNoOpkGdhB_ddhStep
  chooseInitRandC_chal computeOptPosInitC_chal computePosC_chal ddhStep_bindV ddhStep_bindV_zero
  ddhStep_caseOptV ddhStep_ite ddhStep_letV ddhStep_mono ddhStep_pure ddhStep_ret fgDdhPhi
  fgDdhPhi_le_sess_inc fgDdhPhi_mono fgDdhPhi_ro_step fgDdhPhi_sess_step fgDdhPhi_zero_done
  fgPatchC_any_step fgRDone fgSDone finishAcceptGdhC_ddhStep gPrim_queries_wDdhGdh isRoQ isSessQ
  mkSecretPosC_chal registerGdhB_ddhStep roParsedC_ddhStep sessPost_refl wDdhGdh wsZero)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (gdh1KeyFinish_queries_ddh
  gdh1KeyStateTy liftGdhComp liftGdhComp_eval mem_support_liftGdhToSign pullEnv_twoVarRen renameComp
  renameComp_eval sigChalQ_dsl twoVarRen wDdh1Key wsZero1Key)

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Ty.denote pqChalIface pqPrimIface sigAndDdhOracle sigAndDdhSpec
  SignalPqxdh.sigOracleSpec SignalPqxdh.gapDhOracleSpec gapDhDdhOracle Env.get Ext.wk

private theorem act_embedGdhSigDdh_pure {α : Type} (a : α) :
    embedGdhSigDdh (Pure.pure a) = Pure.pure a := rfl

private abbrev ActSigDdhSpec := PrimBaseSpec + sigAndDdhOracle.spec

private def ActSigDdhStep {α : Type} (m : ℕ) (Q : α → Prop)
    (oa : OracleComp ActSigDdhSpec α) : Prop :=
  oa.IsQueryBoundP (fun q => isDdhChalQuery q = true) m ∧ ∀ x ∈ support oa, Q x

private theorem act_hwDdh : ∀ (g : pqSigAndDdhIface.Tag) (x : (pqSigAndDdhIface.dom g).denote),
    isDdhChalQuery (pqSigAndDdhIface.enc g x) = true →
      1 ≤ SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight g := by
  intro g x hx
  cases g with
  | inl t => simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
  | inr t =>
    cases t with
    | inl m => simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
    | inr u => rcases u with ⟨⟩; decide

private theorem act_hUDdh : ∀ n : ℕ,
    (pqSigAndDdhIface.fwdU n).IsQueryBoundP (fun q => isDdhChalQuery q = true) 0 := by
  intro n
  change IsQueryBoundP
    (liftM (OracleSpec.query (spec := ActSigDdhSpec) (Sum.inl (Sum.inl n))))
    (fun q => isDdhChalQuery q = true) 0
  rw [isQueryBoundP_query_iff]
  simp [isDdhChalQuery]

private theorem act_mem_support_embedGdhSigDdh {α : Type}
    (oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α) (y : α) :
    y ∈ support (embedGdhSigDdh oa) ↔ y ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    rcases q with pq | dq
    · change y ∈ support (liftM (OracleSpec.query (spec := _root_.SignalPqxdh.Security.Sig1Key.SigDdhSimSpec) (Sum.inl pq)) >>=
          fun u => embedGdhSigDdh (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u
    · change y ∈ support (liftM (OracleSpec.query (spec := _root_.SignalPqxdh.Security.Sig1Key.SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => embedGdhSigDdh (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u

private theorem act_isQueryBoundP_embedGdhSigDdh {α : Type}
    (oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α) :
    ∀ {m : ℕ}, oa.IsQueryBoundP (fun q => q.isRight = true) m →
      (embedGdhSigDdh oa).IsQueryBoundP (fun q => isDdhChalQuery q = true) m := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m _
    simp
  | query_bind q r ih =>
    intro m h
    rw [isQueryBoundP_query_bind_iff] at h
    rcases q with pq | dq
    · change IsQueryBoundP
        (liftM (OracleSpec.query (spec := _root_.SignalPqxdh.Security.Sig1Key.SigDdhSimSpec) (Sum.inl pq)) >>=
          fun u => embedGdhSigDdh (r u))
        (fun q => isDdhChalQuery q = true) m
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by simp [isDdhChalQuery]), fun u => ?_⟩
      simp only [isDdhChalQuery, Bool.false_eq_true, ↓reduceIte]
      exact ih u (by simpa using h.2 u)
    · change IsQueryBoundP
        (liftM (OracleSpec.query (spec := _root_.SignalPqxdh.Security.Sig1Key.SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => embedGdhSigDdh (r u))
        (fun q => isDdhChalQuery q = true) m
      rw [isQueryBoundP_query_bind_iff]
      have hPos : 0 < m := h.1.resolve_left (by simp)
      refine ⟨Or.inr hPos, fun u => ?_⟩
      simp only [isDdhChalQuery, ↓reduceIte]
      exact ih u (by simpa using h.2 u)

private theorem act_embedGdhSigDdh_step {α : Type} {m : ℕ} {Q : α → Prop}
    {oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α}
    (h : DdhStep m Q oa) :
    ActSigDdhStep m Q (embedGdhSigDdh oa) :=
  ⟨act_isQueryBoundP_embedGdhSigDdh oa h.1,
   fun x hx => h.2 x ((act_mem_support_embedGdhSigDdh oa x).mp hx)⟩

private theorem act_liftGdhToSign_isQueryBoundP_ddh {α : Type}
    (m : OracleComp GdhSimSpec α) :
    ∀ {n : ℕ}, m.IsQueryBoundP (fun q => q.isRight = true) n →
      (liftGdhToSign m).IsQueryBoundP (fun q => isDdhChalQuery q = true) n := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    intro n _
    exact isQueryBoundP_pure _ a n
  | query_bind q r ih =>
    intro n hm
    rw [isQueryBoundP_query_bind_iff] at hm
    rcases q with bq | dq
    · change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
        fun u => liftGdhToSign (r u)).IsQueryBoundP (fun q => isDdhChalQuery q = true) n
      rw [isQueryBoundP_query_bind_iff]
      simp only [isDdhChalQuery, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inl (by decide), fun u => ih u (by simpa using hm.2 u)⟩
    · have hn : 0 < n := hm.1.resolve_left (by simp)
      change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
        fun u => liftGdhToSign (r u)).IsQueryBoundP (fun q => isDdhChalQuery q = true) n
      rw [isQueryBoundP_query_bind_iff]
      simp only [isDdhChalQuery, ↓reduceIte]
      exact ⟨Or.inr hn, fun u => ih u (by simpa using hm.2 u)⟩

private theorem act_ddhStep_letV_any {Γ : List PT} {τ₁ τ₂ : PT} {m : ℕ} {Q : τ₂.denote → Prop}
    (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ) (hk : ∀ y, DdhStep m Q ((k .zero).eval (.cons y env))) :
    DdhStep m Q ((letV e k).eval env) :=
  ddhStep_letV e k env (hk (e.eval env))

private theorem act_wrapBase2_ddhStep {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.2.1 = ((v sm).eval env).2.1) ((wrapBase2 pa sm c).eval env) := by
  unfold wrapBase2
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ddhStep_ret _ _ rfl

private theorem act_wrapSim2_ddhStep {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {m : ℕ}
    {Q : List fgPatchEntryTy.denote → Prop} (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) (env : Env Δ)
    (hc : DdhStep m (fun p => Q p.2.2.1) (c.eval env)) :
    DdhStep m (fun p => Q p.2.2.2.1) ((wrapSim2 pa c).eval env) := by
  unfold wrapSim2
  exact ddhStep_mono (m₁ := m + 0) (by omega) (fun _ hx => hx)
    (ddhStep_bindV _ _ _ hc fun _ hr => ddhStep_ret _ _ hr)

private theorem act_initPrinGdh2B_ddhStep (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((initPrinGdh2B K pa sm bSt u).eval env) := by
  unfold initPrinGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ret _ _ ?_
  simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

private theorem act_genSpkGdh2B_ddhStep (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((genSpkGdh2B K pa sm bSt x).eval env) := by
  unfold genSpkGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ret _ _ ?_
  simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

private theorem act_genOpkGdh2B_ddhStep (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((genOpkGdh2B K pa sm bSt x).eval env) := by
  unfold genOpkGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ret _ _ ?_
  simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

private theorem act_initiateGdh2B_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
      ((initiateGdh2B S K pa sm bSt hasOpk x).eval env) := by
  have hRet0 : ∀ {Δ' : List PT} [Ext Γ₂ Δ'] (env' : Env Δ'),
      ((v sm).eval env').2.1 = ((v sm).eval env).2.1 →
      DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
        (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
        ((Comp.ret (.pair rNone (v sm)) : Comp pqxdhOps pqGapDhIface Δ' _).eval env') := by
    intro Δ' _ env' hEq
    exact ddhStep_mono (m₁ := 0) (Nat.zero_le _) (fun _ h => h)
      (ddhStep_ret _ _ (by simpa [Expr.eval, hEq] using sessPost_refl ((v sm).eval env).2.1))
  unfold initiateGdh2B
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computeOptPosInitC_chal _ _ _) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_mono ?_ (fun _ h => h)
    (ddhStep_bindV (m₂ := 0) _ _ _ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hPatch => ?_)
  · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
  · refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (chooseInitRandC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ret _ _ ?_
    simp only [eCaseOpt, Expr.eval]
    split <;> simpa only [SessPost, smFgL, smUpd, smMk, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
      Env.get_zero', Env.get_succ'] using hPatch

private theorem act_acceptOpkGdh2B_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
      ((acceptOpkGdh2B S K pa sm bSt x).eval env) := by
  have hRet0 : ∀ {Δ' : List PT} [Ext Γ₂ Δ'] (env' : Env Δ'),
      ((v sm).eval env').2.1 = ((v sm).eval env).2.1 →
      DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
        (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
        ((Comp.ret (.pair rNone (v sm)) : Comp pqxdhOps pqGapDhIface Δ' _).eval env') := by
    intro Δ' _ env' hEq
    exact ddhStep_mono (m₁ := 0) (Nat.zero_le _) (fun _ h => h)
      (ddhStep_ret _ _ (by simpa [Expr.eval, hEq] using sessPost_refl ((v sm).eval env).2.1))
  unfold acceptOpkGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ rfl) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ rfl) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
    refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_mono ?_ (fun _ h => h)
      (ddhStep_bindV (m₂ := 0) _ _ _ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hPatch => ?_)
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · dsimp only []; apply finishAcceptGdhC_ddhStep
      simpa only [SessPost, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hPatch
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
    refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (mkSecretPosC_chal _) fun _ => ?_
    refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_mono ?_ (fun _ h => h)
      (ddhStep_bindV (m₂ := 0) _ _ _ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hPatch => ?_)
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · dsimp only []; apply finishAcceptGdhC_ddhStep
      simpa only [SessPost, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hPatch

private theorem act_gdhHandle2_ddhStep_ro (S : Setup) (K : Nat) (st : gdhState2Ty.denote)
    (gq : KeyIndQuery S) (hRo : isRoQ gq = true) :
    DdhStep (4 * fgSDone st.2.2.1)
      (fun p => fgRDone p.2.2.2.1 ≤ fgRDone st.2.2.1 + 1 ∧ fgSDone p.2.2.2.1 = fgSDone st.2.2.1)
      ((gdhHandle2 S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try simp [isRoQ] at hRo
  unfold gdhHandle2
  simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
    Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
  exact act_wrapSim2_ddhStep
    (Q := fun L' => fgRDone L' ≤ fgRDone st.2.2.1 + 1 ∧ fgSDone L' = fgSDone st.2.2.1)
    _ _ _ (roParsedC_ddhStep K _ _ _)

private theorem act_gdhHandle2_ddhStep_sess (S : Setup) (K : Nat) (st : gdhState2Ty.denote)
    (gq : KeyIndQuery S) (hSess : isSessQ gq = true) :
    DdhStep (4 * (fgRDone st.2.2.1 + fgSDone st.2.2.1))
      (fun p =>
        let r := fgRDone st.2.2.1
        let s := fgSDone st.2.2.1
        (fgRDone p.2.2.2.1 = r ∧ fgSDone p.2.2.2.1 = s) ∨
        (fgRDone p.2.2.2.1 = r + 1 ∧ fgSDone p.2.2.2.1 = s) ∨
        (fgRDone p.2.2.2.1 = r ∧ fgSDone p.2.2.2.1 = s + 1))
      ((gdhHandle2 S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try simp [isSessQ] at hSess
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (act_wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (act_initiateGdh2B_ddhStep S K _ _ _ true _ _))
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (act_wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (act_initiateGdh2B_ddhStep S K _ _ _ false _ _))
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (act_wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (act_acceptOpkGdh2B_ddhStep S K _ _ _ _ _))
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (act_wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (acceptNoOpkGdhB_ddhStep S K _ _ _ _))

private theorem act_gdhHandle2_ddhStep_other (S : Setup) (K : Nat) (st : gdhState2Ty.denote)
    (gq : KeyIndQuery S) (hRo : isRoQ gq = false) (hSess : isSessQ gq = false) :
    DdhStep 0 (fun p => p.2.2.2.1 = st.2.2.1)
      ((gdhHandle2 S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try (simp [isRoQ, isSessQ] at hRo hSess; done)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (act_initPrinGdh2B_ddhStep K _ _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapBase2_ddhStep _ _ _ _
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (act_genSpkGdh2B_ddhStep K _ _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (act_genOpkGdh2B_ddhStep K _ _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapBase2_ddhStep _ _ _ _
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_pure _ rfl
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapBase2_ddhStep _ _ _ _
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (registerGdhB_ddhStep _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact act_wrapBase2_ddhStep _ _ _ _

private theorem act_simulateQ_ddhPhi {S : Setup} {σ : PT} {α : Type}
    (fgLOf : σ.denote → List fgPatchEntryTy.denote)
    (h : Comp pqxdhOps pqSigAndDdhIface [σ, (keyIndCodec S).Q] (.prod (keyIndCodec S).R σ))
    (hStepRo : ∀ st gq, isRoQ gq = true →
      ActSigDdhStep (4 * fgSDone (fgLOf st))
        (fun p => fgRDone (fgLOf p.2) ≤ fgRDone (fgLOf st) + 1 ∧
          fgSDone (fgLOf p.2) = fgSDone (fgLOf st))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepSess : ∀ st gq, isSessQ gq = true →
      ActSigDdhStep (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
        (fun p =>
          let r := fgRDone (fgLOf st)
          let s := fgSDone (fgLOf st)
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r + 1 ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s + 1))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepOther : ∀ st gq, isRoQ gq = false → isSessQ gq = false →
      ActSigDdhStep 0 (fun p => fgLOf p.2 = fgLOf st)
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (oa : OracleComp (unifSpec + keyIndSpec S) α) :
    ∀ (r_rem s_rem : ℕ) (st : σ.denote),
      oa.IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_rem →
      oa.IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_rem →
      ((simulateQ (handlerImpl (C := keyIndCodec S) h) oa).run st).IsQueryBoundP
        (fun q => isDdhChalQuery q = true)
        (fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro r_rem s_rem st _ _
    simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro r_rem s_rem st hRo hSess
    rw [isQueryBoundP_query_bind_iff] at hRo hSess
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases t with uq | gq
    · have hStep0 : (((handlerImpl (C := keyIndCodec S) h) (.inl uq)).run st).IsQueryBoundP
          (fun q => isDdhChalQuery q = true) 0 := by
        have hb := isQueryBoundP_bind (n := 0) (m := 0) (act_hUDdh uq)
          (fun u _ => isQueryBoundP_pure
            (fun q : ActSigDdhSpec.Domain => isDdhChalQuery q = true) (u, st) 0)
        simpa [handlerImpl] using hb
      refine (isQueryBoundP_bind (n := 0)
        (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
        hStep0 fun x hx => ?_).mono (by omega)
      have hst : x.2 = st := by
        simp only [handlerImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨_, _, rfl⟩ := hx; rfl
      rw [← hst]
      exact ih x.1 r_rem s_rem x.2
        (by simpa [_root_.ReductionDsl.onGame] using hRo.2 x.1)
        (by simpa [_root_.ReductionDsl.onGame] using hSess.2 x.1)
    · cases hR : isRoQ gq
      · cases hS : isSessQ gq
        · have hs := hStepOther st gq hR hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => isDdhChalQuery q = true) 0 := by
            have hb := isQueryBoundP_bind (n := 0) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            simpa [handlerImpl] using hb
          refine (isQueryBoundP_bind (n := 0)
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
            hRun fun x hx => ?_).mono (by omega)
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          have hEq := hs.2 p hp
          have hCont := ih ((keyIndCodec S).rdec gq p.1) r_rem s_rem p.2
            (by simpa [_root_.ReductionDsl.onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [_root_.ReductionDsl.onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
          rwa [hEq] at hCont
        · have hPos : 0 < s_rem := hSess.1.resolve_left (by simp [_root_.ReductionDsl.onGame, hS])
          obtain ⟨s', rfl⟩ : ∃ s', s_rem = s' + 1 := ⟨s_rem - 1, by omega⟩
          have hs := hStepSess st gq hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => isDdhChalQuery q = true) (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) := by
            have hb := isQueryBoundP_bind
              (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            simpa [handlerImpl] using hb
          refine (isQueryBoundP_bind
            (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st) + 1) r_rem s')
            hRun fun x hx => ?_).mono (by rw [fgDdhPhi_sess_step])
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact (ih ((keyIndCodec S).rdec gq p.1) r_rem s' p.2
            (by simpa [_root_.ReductionDsl.onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [_root_.ReductionDsl.onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))).mono
            (fgDdhPhi_le_sess_inc (hs.2 p hp) r_rem s')
      · have hS : isSessQ gq = false := by cases gq <;> simp_all [isRoQ, isSessQ]
        have hPos : 0 < r_rem := hRo.1.resolve_left (by simp [_root_.ReductionDsl.onGame, hR])
        obtain ⟨r', rfl⟩ : ∃ r', r_rem = r' + 1 := ⟨r_rem - 1, by omega⟩
        have hs := hStepRo st gq hR
        have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
            (fun q => isDdhChalQuery q = true) (4 * fgSDone (fgLOf st)) := by
          have hb := isQueryBoundP_bind (n := 4 * fgSDone (fgLOf st)) (m := 0) hs.1
            (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
          simpa [handlerImpl] using hb
        refine (isQueryBoundP_bind
          (n := 4 * fgSDone (fgLOf st))
          (m := fgDdhPhi (fgRDone (fgLOf st) + 1) (fgSDone (fgLOf st)) r' s_rem)
          hRun fun x hx => ?_).mono (by rw [fgDdhPhi_ro_step])
        simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨hr_le, hs_eq⟩ := hs.2 p hp
        have hCont := ih ((keyIndCodec S).rdec gq p.1) r' s_rem p.2
          (by simpa [_root_.ReductionDsl.onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
          (by simpa [_root_.ReductionDsl.onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
        rw [hs_eq] at hCont
        exact hCont.mono (fgDdhPhi_mono hr_le le_rfl le_rfl)

private theorem sig1KeyActiveInitPrinB_fgL_eq (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (u : Var Γ₂ .nat) (env : Env Δ) :
    ∀ r ∈ support ((sig1KeyActiveInitPrinB K st u).eval env),
      r.2.2.1.2.1 = ((v st : Expr pqxdhOps Δ sig1KeyActiveStTy).eval env).2.1.2.1 := by
  unfold sig1KeyActiveInitPrinB
  rw [letV_eval]
  simp only [Comp.eval]
  split
  · intro r hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [v, Expr.eval, Env.get_succ', Ext.step_wk']
  · intro r hr
    simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨s0, _, ik, _, rfl⟩ := hr
    simp [saInner, smUpd, smMk, smFgL, s1Fg, v, Expr.eval, Env.get_zero',
      Env.get_succ', Ext.step_wk']

private theorem act_sig1KeyTargetGenSpkB_fgL_eq (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ) :
    ∀ r ∈ support ((sig1KeyTargetGenSpkB K s x).eval env),
      r.2.1.2.1 = ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env).1.2.1 := by
  unfold sig1KeyTargetGenSpkB
  simp only [Comp.eval]
  split
  · intro r hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · simp only [caseOptV, Comp.eval]
    cases (eFind K (stPrin (s1Base (v s))) fun e => natEq (.fst (v e)) (.fst (v x))).eval env with
    | none =>
      intro r hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    | some uE =>
      dsimp only [Comp.eval]
      split
      · intro r hr
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr; simp [v, Expr.eval]
      · intro r hr
        dsimp only [bindV, Comp.eval] at hr
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
        obtain ⟨spkSk, _, spkPk, _, sig1, _, seed, _, kp, _, sig2, _, rfl⟩ := hr
        simp [smUpd, smMk, smFgL, s1Fg, v, Expr.eval, Env.get_succ', Ext.step_wk']

private theorem sig1KeyActiveInitiateCheckC_fgL_eq (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (x : Var Γ₂ initQTy) (env : Env Δ) :
    ∀ pre ∈ support ((sig1KeyActiveInitiateCheckC S K st x).eval env),
      ∀ res, pre = .inl res →
        res.2.2.1.2.1 = ((v st : Expr pqxdhOps Δ sig1KeyActiveStTy).eval env).2.1.2.1 := by
  unfold sig1KeyActiveInitiateCheckC
  rw [letV_eval]
  simp only [bindV, Comp.eval, mem_support_bind_iff]
  rintro _ ⟨fg, _, hpre⟩ res rfl
  split at hpre
  · simp only [support_pure, Set.mem_singleton_iff] at hpre
    cases hpre
    simp [v, Expr.eval, Env.get_succ', Ext.step_wk']
  · simp only [support_pure, Set.mem_singleton_iff] at hpre
    cases hpre

private theorem sig1KeyActivePreDispatchC_ddhQueries (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyActivePreDispatchC S K (Δ := Δ) st q).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
  simp [sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyActiveInitiateCheckC, extract1KeyActiveC, honestPeerC,
    s1Prim, liftBase, qSigDdhSign, qSigVerify, qX25519Base, qKemKeyGen,
    sBytes32, sRandom64, letV, bindV, caseSumV, caseOptV, Comp.queries,
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight, samplerZeroQueryWeight]

private theorem act_caseSumV_eval {Γ : List PT} {τ₁ τ₂ τ : PT} (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqSigAndDdhIface (τ₂ :: Γ) τ) (env : Env Γ) :
    (caseSumV s kl kr).eval env =
      match s.eval env with
      | .inl x => (kl .zero).eval (.cons x env)
      | .inr y => (kr .zero).eval (.cons y env) := by
  simp only [caseSumV, Comp.eval]; cases s.eval env <;> rfl

private theorem act_caseSumV_zero_eval {Γ : List PT} {τ₁ τ₂ τ : PT} (val : (Ty.sum τ₁ τ₂).denote)
    (kl : Var (τ₁ :: Ty.sum τ₁ τ₂ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Ty.sum τ₁ τ₂ :: Γ) τ)
    (kr : Var (τ₂ :: Ty.sum τ₁ τ₂ :: Γ) τ₂ → Comp pqxdhOps pqSigAndDdhIface (τ₂ :: Ty.sum τ₁ τ₂ :: Γ) τ)
    (env : Env Γ) :
    (caseSumV (v (.zero : Var (Ty.sum τ₁ τ₂ :: Γ) (Ty.sum τ₁ τ₂))) kl kr).eval (.cons val env) =
      match val with
      | .inl x => (kl .zero).eval (.cons x (.cons val env))
      | .inr y => (kr .zero).eval (.cons y (.cons val env)) := by
  cases val <;> simp only [caseSumV, Comp.eval, v, Expr.eval, Ext.refl_wk', Env.get_zero']

private theorem sig1KeyActivePreDispatchC_sigDdhStep (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) (env : Env Δ) :
    ActSigDdhStep 0
      (fun pre => ∀ res, pre = .inl res →
        res.2.2.1.2.1 = ((v st : Expr pqxdhOps Δ sig1KeyActiveStTy).eval env).2.1.2.1)
      ((sig1KeyActivePreDispatchC S K st q).eval env) := by
  refine ⟨?_, ?_⟩
  · have hq := Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
      act_hwDdh act_hUDdh (sig1KeyActivePreDispatchC S K st q) env
    rwa [sig1KeyActivePreDispatchC_ddhQueries] at hq
  · unfold sig1KeyActivePreDispatchC
    simp only [Comp.eval]
    split
    · intro pre hpre res hEq
      simp only [support_pure, Set.mem_singleton_iff] at hpre
      subst hpre; cases hEq; rfl
    · rw [act_caseSumV_eval]
      rcases ((v q : Expr pqxdhOps Δ keyIndQueryTy).eval env) with u | q1
      · dsimp only
        intro pre hpre res hEq
        simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpre
        obtain ⟨r, hr, rfl⟩ := hpre; cases hEq
        simpa [v, Expr.eval, Env.get_succ', Ext.step_wk'] using sig1KeyActiveInitPrinB_fgL_eq K st .zero _ r hr
      · dsimp only
        rw [act_caseSumV_zero_eval]
        rcases q1 with _ | q2
        · dsimp only
          intro pre hpre res hEq
          simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hpre
          subst hpre; cases hEq
        · dsimp only
          rw [act_caseSumV_zero_eval]
          rcases q2 with x | q3
          · dsimp only
            simp only [Comp.eval]
            split
            · intro pre hpre res hEq
              rw [letV_eval] at hpre
              simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure,
                Set.mem_singleton_iff] at hpre
              obtain ⟨r, hr, rfl⟩ := hpre; cases hEq
              simpa [saInner, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk'] using
                act_sig1KeyTargetGenSpkB_fgL_eq K _ _ _ r hr
            · intro pre hpre res hEq
              simp only [support_pure, Set.mem_singleton_iff] at hpre
              subst hpre; cases hEq
          · dsimp only
            rw [act_caseSumV_zero_eval]
            rcases q3 with _ | q4
            · dsimp only
              intro pre hpre res hEq
              simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hpre
              subst hpre; cases hEq
            · dsimp only
              rw [act_caseSumV_zero_eval]
              rcases q4 with x | q5
              · dsimp only
                intro pre hpre res hEq
                simpa [v, Expr.eval, Env.get_succ', Ext.step_wk'] using
                  sig1KeyActiveInitiateCheckC_fgL_eq S K st .zero _ pre hpre res hEq
              · dsimp only
                rw [act_caseSumV_zero_eval]
                rcases q5 with x | _
                · dsimp only
                  intro pre hpre res hEq
                  simpa [v, Expr.eval, Env.get_succ', Ext.step_wk'] using
                    sig1KeyActiveInitiateCheckC_fgL_eq S K st .zero _ pre hpre res hEq
                · dsimp only
                  intro pre hpre res hEq
                  simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hpre
                  subst hpre; cases hEq

private theorem sig1KeyActiveHandleC_sigDdhStep (S : Setup) (K : ℕ)
    (st : sig1KeyActiveStTy.denote) (gq : KeyIndQuery S)
    {m : ℕ} {Q : List fgPatchEntryTy.denote → Prop}
    (hRefl : Q st.2.1.2.1)
    (hGdh : ∀ pa : params2Ty.denote,
      DdhStep m (fun p => Q p.2.2.2.1)
        ((gdhHandle2 S K).eval (.cons (pa, st.2.1) (.cons ((keyIndCodec S).qenc gq) .nil)))) :
    ActSigDdhStep m (fun r : S1ARS.denote => Q r.2.2.1.2.1)
      ((sig1KeyActiveHandleC S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  unfold sig1KeyActiveHandleC
  simp only [bindV, caseSumV, Comp.eval]
  have hPre := sig1KeyActivePreDispatchC_sigDdhStep S K
    (Γ₁ := [sig1KeyActiveStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyActiveStTy, keyIndQueryTy])
    (Δ := [sig1KeyActiveStTy, keyIndQueryTy]) .zero (.succ .zero)
    (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))
  refine ⟨?_, ?_⟩
  · refine (isQueryBoundP_bind (n := 0) (m := m) hPre.1 (fun pre _ => ?_)).mono (by omega)
    rcases pre with res | u
    · simp only [v, Expr.eval, Ext.refl_wk', Env.get_zero']
      exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le m)
    · simp only [v, Expr.eval, Ext.refl_wk', Env.get_zero', letV_eval, Comp.eval,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_eval, Comp.rename_eval]
      set paVal : params2Ty.denote :=
        (pa2Mk (litB 32 []) (s1Pk (.var .zero)) (litB 32 []) .none (.bool false) .none .none
          (.bool false) .none (.nat 1)).eval
          (Env.cons (t := sig1KeyStTy) st.2
            (Env.cons (t := .unit) u (Env.cons (t := .sum S1ARS .unit) (Sum.inr u)
              (.cons st (.cons ((keyIndCodec S).qenc gq) .nil)))))
      have hStep := act_embedGdhSigDdh_step (hGdh paVal)
      refine (isQueryBoundP_bind (n := m) (m := 0) hStep.1
        (fun r _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  · intro y hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨pre, hpre, hy⟩ := hy
    rcases pre with res | u
    · simp only [v, Expr.eval, Ext.refl_wk', Env.get_zero', support_pure, Set.mem_singleton_iff] at hy
      subst hy
      have hEq := hPre.2 (.inl y) hpre y rfl
      simpa [v, Expr.eval] using hEq.symm ▸ hRefl
    · simp only [v, Expr.eval, Ext.refl_wk', Env.get_zero', letV_eval, Comp.eval,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_eval, Comp.rename_eval,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      set paVal : params2Ty.denote :=
        (pa2Mk (litB 32 []) (s1Pk (.var .zero)) (litB 32 []) .none (.bool false) .none .none
          (.bool false) .none (.nat 1)).eval
          (Env.cons (t := sig1KeyStTy) st.2
            (Env.cons (t := .unit) u (Env.cons (t := .sum S1ARS .unit) (Sum.inr u)
              (.cons st (.cons ((keyIndCodec S).qenc gq) .nil)))))
      have hStep := act_embedGdhSigDdh_step (hGdh paVal)
      have hr' : r ∈ support (embedGdhSigDdh
          ((gdhHandle2 S K).eval (.cons (paVal, st.2.1) (.cons ((keyIndCodec S).qenc gq) .nil)))) := hr
      simpa [saTP, saInner, s1Fg, v, Expr.eval,
        Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'] using hStep.2 r hr'

private theorem sigKeyInd1KeyActiveDslProg_ddhBounded_bilinear (S : Setup) (b : QueryBudget)
    (r_max s_max : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hRo : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_max)
    (hSess : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_max)
    (pk : Bytes) :
    ((sigKeyInd1KeyActiveDslProg S b).eval A pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true)
      (4 * r_max * s_max + 2 * s_max * (s_max - 1)) := by
  have hInitQ : (((sigKeyInd1KeyActiveDslProg S b).init).eval (.cons pk .nil)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) 0 := by
    have hq := Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
      act_hwDdh act_hUDdh (sigKeyInd1KeyActiveDslProg S b).init (.cons pk .nil)
    have h0 : ((sigKeyInd1KeyActiveDslProg S b).init).queries
        SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
      simp [sigKeyInd1KeyActiveDslProg, bindV, s1Prim, liftBase, sIndex, sBool, Comp.queries,
        samplerZeroQueryWeight]
    rwa [h0] at hq
  have hInitEmpty : ∀ as ∈ support (((sigKeyInd1KeyActiveDslProg S b).init).eval (.cons pk .nil)),
      as.2.2.1.2.1 = [] := by
    unfold sigKeyInd1KeyActiveDslProg
    intro as has
    simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at has
    obtain ⟨k, _, secb, _, rfl⟩ := has
    simp [emptySimE, smMk, Expr.eval]
  unfold CostedReduction.eval CostedReduction.impl
  refine (isQueryBoundP_bind (n := 0)
    (m := 4 * r_max * s_max + 2 * s_max * (s_max - 1))
    hInitQ fun as has => ?_).mono (by omega)
  have hEmpty := hInitEmpty as has
  have hSim := act_simulateQ_ddhPhi (fun s : sig1KeyActiveStTy.denote => s.2.1.2.1)
    (sig1KeyActiveHandleC S b.q_total)
    (fun st gq hR => sig1KeyActiveHandleC_sigDdhStep
      (Q := fun L => fgRDone L ≤ fgRDone st.2.1.2.1 + 1 ∧ fgSDone L = fgSDone st.2.1.2.1)
      S b.q_total st gq ⟨Nat.le_succ _, rfl⟩
      (fun pa => act_gdhHandle2_ddhStep_ro S b.q_total (pa, st.2.1) gq hR))
    (fun st gq hS => sig1KeyActiveHandleC_sigDdhStep
      (Q := fun L =>
        let r := fgRDone st.2.1.2.1
        let s := fgSDone st.2.1.2.1
        (fgRDone L = r ∧ fgSDone L = s) ∨
        (fgRDone L = r + 1 ∧ fgSDone L = s) ∨
        (fgRDone L = r ∧ fgSDone L = s + 1))
      S b.q_total st gq (Or.inl ⟨rfl, rfl⟩)
      (fun pa => act_gdhHandle2_ddhStep_sess S b.q_total (pa, st.2.1) gq hS))
    (fun st gq hR hS => sig1KeyActiveHandleC_sigDdhStep
      (Q := fun L => L = st.2.1.2.1)
      S b.q_total st gq rfl
      (fun pa => act_gdhHandle2_ddhStep_other S b.q_total (pa, st.2.1) gq hR hS))
    (A as.1) r_max s_max as.2 (hRo as.1) (hSess as.1)
  rw [hEmpty, show fgRDone [] = 0 from rfl, show fgSDone [] = 0 from rfl,
    fgDdhPhi_zero_done] at hSim
  refine (isQueryBoundP_bind
    (n := 4 * r_max * s_max + 2 * s_max * (s_max - 1)) (m := 0)
    hSim fun bs _ => ?_).mono (by omega)
  have hFin := Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
    act_hwDdh act_hUDdh (sigKeyInd1KeyActiveDslProg S b).finish (.cons bs.2 (.cons bs.1 .nil))
  have hFin0 : ((sigKeyInd1KeyActiveDslProg S b).finish).queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
    simp [sigKeyInd1KeyActiveDslProg, Comp.queries]
  rwa [hFin0] at hFin

private theorem callGdhActiveHandle_ddhStep (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) (env : Env Δ)
    {m : ℕ} {Q : List fgPatchEntryTy.denote → Prop}
    (h : ∀ pa2 : params2Ty.denote,
      DdhStep m (fun p => Q p.2.2.2.1)
        ((gdhHandle2 S K).eval (.cons (pa2, (env.get stA).1.1.2) (.cons (env.get q) .nil)))) :
    ActSigDdhStep m (fun p => Q p.2.1.1.2.2.1) ((callGdhActiveHandle S K stA q).eval env) := by
  unfold callGdhActiveHandle
  simp only [letV_eval, bindV, Comp.eval, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
    Env.get_zero', Env.get_succ', renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval]
  set pa := (env.get stA).1.1.1
  set pa2 : params2Ty.denote :=
    (pa2Mk (paU (.var .zero)) (paV (.var .zero)) (paUp (.var .zero)) .none (.bool false)
      .none .none (paOpkMode (.var .zero)) .none (.nat 1)).eval
      (Env.cons (t := paramsTy) pa (Env.cons (t := gdh1KeyStateTy) (env.get stA).1 env))
  have hs := h pa2
  refine ⟨(isQueryBoundP_bind (n := m) (m := 0) (act_liftGdhToSign_isQueryBoundP_ddh _ hs.1)
    fun res _ => isQueryBoundP_pure _ _ 0).mono (by omega), fun p hp => ?_⟩
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨res, hres, rfl⟩ := hp
  exact hs.2 res (mem_support_liftGdhToSign hres)

private theorem gdh1KeyActiveHandle_ddhStep_of_inr5 (S : Setup) (K : Nat)
    (stA : gdh1KeyActiveStateTy.denote) (gq : KeyIndQuery S)
    {rest : _} (hq : (keyIndCodec S).qenc gq =
      .inr (.inr (.inr (.inr (.inr (.inr rest))))))
    {m : ℕ} {Q : List fgPatchEntryTy.denote → Prop}
    (h : ∀ pa2 : params2Ty.denote,
      DdhStep m (fun p => Q p.2.2.2.1)
        ((gdhHandle2 S K).eval (.cons (pa2, stA.1.1.2) (.cons ((keyIndCodec S).qenc gq) .nil)))) :
    ActSigDdhStep m (fun p => Q p.2.1.1.2.2.1)
      ((gdh1KeyActiveHandle S K).eval (.cons stA (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  conv =>
    arg 3
    unfold gdh1KeyActiveHandle
  simp only [caseSumV, Comp.eval, v, Expr.eval, Ext.refl_wk', Env.get_zero', Env.get_succ', hq]
  apply callGdhActiveHandle_ddhStep
  intro pa2
  rw [← hq]
  exact h pa2

private theorem initPrin1KeyActiveGdhB_ddhStep (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁ gdh1KeyActiveStateTy) (u : Var Γ₂ .nat) (env : Env Δ) :
    ActSigDdhStep 0 (fun p => p.2.1.1.2.2.1 = (env.get (Ext.wk stA)).1.1.2.2.1)
      ((initPrin1KeyActiveGdhB K stA u).eval env) := by
  refine ⟨?_, fun p hp => ?_⟩
  · refine (Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
      act_hwDdh act_hUDdh (initPrin1KeyActiveGdhB K stA u) env).mono ?_
    simp [initPrin1KeyActiveGdhB, liftGdhComp, gPrim, liftBase, sBytes32, qX25519Base,
      letV, bindV, Comp.queries, SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight, samplerZeroQueryWeight]
  · unfold initPrin1KeyActiveGdhB at hp
    simp only [letV_eval, bindV, Comp.eval] at hp
    split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ']
    · simp only [mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hp
      obtain ⟨sk0, _, pk0, _, rfl⟩ := hp
      simp [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ']

private theorem genSpk1KeyActiveGdhB_ddhStep (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁ gdh1KeyActiveStateTy)
    (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ) :
    ActSigDdhStep 0 (fun p => p.2.1.1.2.2.1 = (env.get (Ext.wk stA)).1.1.2.2.1)
      ((genSpk1KeyActiveGdhB K stA x).eval env) := by
  refine ⟨?_, fun p hp => ?_⟩
  · refine (Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
      act_hwDdh act_hUDdh (genSpk1KeyActiveGdhB K stA x) env).mono ?_
    simp [genSpk1KeyActiveGdhB, genSpkGdhActiveB, sigChalQ_dsl, liftGdhComp, gPrim, liftBase,
      sBytes32, sRandom64, qX25519Base, qKemKeyGen, qSigSign,
      letV, bindV, caseOptV, Comp.queries, SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight, samplerZeroQueryWeight]
  · unfold genSpk1KeyActiveGdhB at hp
    simp only [letV_eval, Comp.eval] at hp
    split at hp
    · split at hp
      · simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ']
      · simp only [caseOptV, Comp.eval] at hp
        split at hp
        · simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp; simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ']
        · split at hp
          · simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ']
          · simp only [letV_eval, bindV, Comp.eval, mem_support_bind_iff, support_pure,
              Set.mem_singleton_iff] at hp
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := hp
            simp [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
              Env.get_zero', Env.get_succ']
    · simp only [bindV, Comp.eval, liftGdhComp_eval, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hp
      obtain ⟨res, hres, rfl⟩ := hp
      have hres' := mem_support_liftGdhToSign hres
      unfold genSpkGdhActiveB at hres'
      simp only [Comp.eval] at hres'
      split at hres'
      · simp only [support_pure, Set.mem_singleton_iff] at hres'
        subst hres'; simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ']
      · simp only [caseOptV, Comp.eval] at hres'
        split at hres'
        · simp only [support_pure, Set.mem_singleton_iff] at hres'
          subst hres'; simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ']
        · simp only [letV_eval, bindV, Comp.eval, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hres'
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := hres'
          simp [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
            Env.get_zero', Env.get_succ']

private theorem genOpkActiveGdhB_ddhStep (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (stA : Var Γ₁ gdh1KeyActiveStateTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) (env : Env Δ) :
    ActSigDdhStep 0 (fun p => p.2.1.1.2.2.1 = (env.get (Ext.wk stA)).1.1.2.2.1)
      ((genOpkActiveGdhB K stA x).eval env) := by
  refine ⟨?_, fun p hp => ?_⟩
  · refine (Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
      act_hwDdh act_hUDdh (genOpkActiveGdhB K stA x) env).mono ?_
    simp [genOpkActiveGdhB, liftGdhComp, gPrim, liftBase, sBytes32, qX25519Base,
      letV, bindV, Comp.queries, SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight, samplerZeroQueryWeight]
  · unfold genOpkActiveGdhB at hp
    simp only [letV_eval, Comp.eval] at hp
    split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ']
    · simp only [letV_eval, bindV, Comp.eval, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hp
      obtain ⟨_, _, _, _, rfl⟩ := hp
      simp [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ']

private theorem initiateGdhActiveInnerB_ddhStep (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (sendOpkCnt : Var Γ₅ .nat) (hasOpk : Bool) (x : Var Γ₄ initQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.1.2.1)
      ((initiateGdhActiveInnerB S K pa sm bSt sendOpkCnt hasOpk x).eval env) := by
  have hRet0 : ∀ {Δ' : List PT} [Ext Γ₂ Δ'] [Ext Γ₅ Δ'] (env' : Env Δ'),
      ((v sm).eval env').2.1 = ((v sm).eval env).2.1 →
      DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
        (fun p => SessPost ((v sm).eval env).2.1 p.2.1.2.1)
        ((Comp.ret (.pair rNone (.pair (v sm) (v sendOpkCnt))) :
          Comp pqxdhOps pqGapDhIface Δ' _).eval env') := by
    intro Δ' _ _ env' hEq
    exact ddhStep_mono (m₁ := 0) (Nat.zero_le _) (fun _ h => h)
      (ddhStep_ret _ _ (by simpa [Expr.eval, hEq] using sessPost_refl ((v sm).eval env).2.1))
  unfold initiateGdhActiveInnerB
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computeOptPosInitC_chal _ _ _) fun _ => ?_
  refine act_ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_mono ?_ (fun _ h => h)
    (ddhStep_bindV (m₂ := 0) _ _ _ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hPatch => ?_)
  · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
  · refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine act_ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (chooseInitRandC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ret _ _ ?_
    simp only [eCaseOpt, Expr.eval]
    split <;> simpa only [SessPost, smFgL, smUpd, smMk, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
      Env.get_zero', Env.get_succ'] using hPatch

private theorem initiateActiveGdhB_ddhStep (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy) (env : Env Δ) :
    ActSigDdhStep
      (4 * (fgRDone (env.get (Ext.wk stA)).1.1.2.2.1 + fgSDone (env.get (Ext.wk stA)).1.1.2.2.1))
      (fun p => SessPost (env.get (Ext.wk stA)).1.1.2.2.1 p.2.1.1.2.2.1)
      ((initiateActiveGdhB S K hasOpk stA x).eval env) := by
  unfold initiateActiveGdhB
  simp only [letV_eval, bindV, Comp.eval, liftGdhComp_eval, v, Expr.eval,
    Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
  have hs := initiateGdhActiveInnerB_ddhStep S K
    (Γ₁ := paramsTy :: gdh1KeyStateTy :: Δ)
    (Γ₂ := simTy :: paramsTy :: gdh1KeyStateTy :: Δ)
    (Γ₃ := keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ)
    (Γ₄ := Γ₂)
    (Γ₅ := .nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ)
    (Δ := .nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ)
    .zero .zero .zero .zero hasOpk x
    (Env.cons (env.get (Ext.wk stA)).2.2
      (Env.cons (env.get (Ext.wk stA)).1.1.2.1
        (Env.cons (env.get (Ext.wk stA)).1.1.2
          (Env.cons (env.get (Ext.wk stA)).1.1.1
            (Env.cons (env.get (Ext.wk stA)).1 env)))))
  simp only [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] at hs
  refine ⟨(isQueryBoundP_bind (n := _) (m := 0) (act_liftGdhToSign_isQueryBoundP_ddh _ hs.1)
    fun res _ => isQueryBoundP_pure _ _ 0).mono (by omega), fun p hp => ?_⟩
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨res, hres, rfl⟩ := hp
  exact hs.2 res (mem_support_liftGdhToSign hres)

private theorem gdh1KeyActiveHandle_ddhStep_ro (S : Setup) (K : Nat)
    (stA : gdh1KeyActiveStateTy.denote) (gq : KeyIndQuery S) (hR : isRoQ gq = true) :
    ActSigDdhStep (4 * fgSDone stA.1.1.2.2.1)
      (fun p => fgRDone p.2.1.1.2.2.1 ≤ fgRDone stA.1.1.2.2.1 + 1 ∧
        fgSDone p.2.1.1.2.2.1 = fgSDone stA.1.1.2.2.1)
      ((gdh1KeyActiveHandle S K).eval (.cons stA (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq with
  | roQuery sec =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5
      (Q := fun L => fgRDone L ≤ fgRDone stA.1.1.2.2.1 + 1 ∧ fgSDone L = fgSDone stA.1.1.2.2.1)
      S K stA (.roQuery sec) rfl
      (fun pa2 => act_gdhHandle2_ddhStep_ro S K (pa2, stA.1.1.2) (.roQuery sec) hR)
  | _ => simp [isRoQ] at hR

private theorem gdh1KeyActiveHandle_ddhStep_sess (S : Setup) (K : Nat)
    (stA : gdh1KeyActiveStateTy.denote) (gq : KeyIndQuery S) (hS : isSessQ gq = true) :
    ActSigDdhStep (4 * (fgRDone stA.1.1.2.2.1 + fgSDone stA.1.1.2.2.1))
      (fun p =>
        let r := fgRDone stA.1.1.2.2.1
        let s := fgSDone stA.1.1.2.2.1
        (fgRDone p.2.1.1.2.2.1 = r ∧ fgSDone p.2.1.1.2.2.1 = s) ∨
        (fgRDone p.2.1.1.2.2.1 = r + 1 ∧ fgSDone p.2.1.1.2.2.1 = s) ∨
        (fgRDone p.2.1.1.2.2.1 = r ∧ fgSDone p.2.1.1.2.2.1 = s + 1))
      ((gdh1KeyActiveHandle S K).eval (.cons stA (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq with
  | initiateOPK u b bu =>
    unfold gdh1KeyActiveHandle
    simp only [keyIndCodec, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact initiateActiveGdhB_ddhStep S K true .zero .zero _
  | initiateNoOPK u b bu =>
    unfold gdh1KeyActiveHandle
    simp only [keyIndCodec, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact initiateActiveGdhB_ddhStep S K false .zero .zero _
  | acceptOPK k j o hdr =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5
      (Q := fun L =>
        let r := fgRDone stA.1.1.2.2.1
        let s := fgSDone stA.1.1.2.2.1
        (fgRDone L = r ∧ fgSDone L = s) ∨
        (fgRDone L = r + 1 ∧ fgSDone L = s) ∨
        (fgRDone L = r ∧ fgSDone L = s + 1))
      S K stA (.acceptOPK k j o hdr) rfl
      (fun pa2 => act_gdhHandle2_ddhStep_sess S K (pa2, stA.1.1.2) (.acceptOPK k j o hdr) hS)
  | acceptNoOPK k j l hdr =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5
      (Q := fun L =>
        let r := fgRDone stA.1.1.2.2.1
        let s := fgSDone stA.1.1.2.2.1
        (fgRDone L = r ∧ fgSDone L = s) ∨
        (fgRDone L = r + 1 ∧ fgSDone L = s) ∨
        (fgRDone L = r ∧ fgSDone L = s + 1))
      S K stA (.acceptNoOPK k j l hdr) rfl
      (fun pa2 => act_gdhHandle2_ddhStep_sess S K (pa2, stA.1.1.2) (.acceptNoOPK k j l hdr) hS)
  | _ => simp [isSessQ] at hS

private theorem gdh1KeyActiveHandle_ddhStep_other (S : Setup) (K : Nat)
    (stA : gdh1KeyActiveStateTy.denote) (gq : KeyIndQuery S)
    (hR : isRoQ gq = false) (hS : isSessQ gq = false) :
    ActSigDdhStep 0 (fun p => p.2.1.1.2.2.1 = stA.1.1.2.2.1)
      ((gdh1KeyActiveHandle S K).eval (.cons stA (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq with
  | initPrin u =>
    unfold gdh1KeyActiveHandle
    simp only [keyIndCodec, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact initPrin1KeyActiveGdhB_ddhStep K .zero .zero _
  | corruptIK u =>
    have hq : (keyIndCodec S).qenc (.corruptIK u) = .inr (.inl u.val) := rfl
    conv =>
      arg 3
      unfold gdh1KeyActiveHandle
    simp only [caseSumV, Comp.eval, v, Expr.eval, Ext.refl_wk', Env.get_zero', Env.get_succ', hq]
    apply callGdhActiveHandle_ddhStep (Q := fun L => L = stA.1.1.2.2.1)
    intro pa2
    rw [← hq]
    exact act_gdhHandle2_ddhStep_other S K (pa2, stA.1.1.2) (.corruptIK u) hR hS
  | genSPK u j =>
    unfold gdh1KeyActiveHandle
    simp only [keyIndCodec, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact genSpk1KeyActiveGdhB_ddhStep K .zero .zero _
  | genOPK u j o =>
    unfold gdh1KeyActiveHandle
    simp only [keyIndCodec, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact genOpkActiveGdhB_ddhStep K .zero .zero _
  | initiateOPK _ _ _ | initiateNoOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ =>
    simp [isSessQ] at hS
  | roQuery _ =>
    simp [isRoQ] at hR
  | testSession sid =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5 (Q := fun L => L = stA.1.1.2.2.1)
      S K stA (.testSession sid) rfl
      (fun pa2 => act_gdhHandle2_ddhStep_other S K (pa2, stA.1.1.2) (.testSession sid) hR hS)
  | revealSessionKey sid =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5 (Q := fun L => L = stA.1.1.2.2.1)
      S K stA (.revealSessionKey sid) rfl
      (fun pa2 => act_gdhHandle2_ddhStep_other S K (pa2, stA.1.1.2) (.revealSessionKey sid) hR hS)
  | revealDhSecrets =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5 (Q := fun L => L = stA.1.1.2.2.1)
      S K stA .revealDhSecrets rfl
      (fun pa2 => act_gdhHandle2_ddhStep_other S K (pa2, stA.1.1.2) .revealDhSecrets hR hS)
  | registerKey sk =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5 (Q := fun L => L = stA.1.1.2.2.1)
      S K stA (.registerKey sk) rfl
      (fun pa2 => act_gdhHandle2_ddhStep_other S K (pa2, stA.1.1.2) (.registerKey sk) hR hS)
  | revealSpkSk u j =>
    exact gdh1KeyActiveHandle_ddhStep_of_inr5 (Q := fun L => L = stA.1.1.2.2.1)
      S K stA (.revealSpkSk u j) rfl
      (fun pa2 => act_gdhHandle2_ddhStep_other S K (pa2, stA.1.1.2) (.revealSpkSk u j) hR hS)

private theorem gdh1KeyActiveFinish_ddhQueries_le (S : Setup) (K : Nat) :
    (gdh1KeyActiveFinish S K).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      K + min K S.N_dh + min K S.N_sess_tot := by
  change (gdh1KeyActiveFinish S K).queries wDdh1Key wsZero1Key ≤ _
  simp only [gdh1KeyActiveFinish, letV_queries,
    SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.renameComp_queries,
    SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_queries_ddh,
    SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gdhFinish_chalQueries]
  omega

end

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] pqChalIface pqPrimIface pqSigAndDdhIface pqGapDhIface
  sigAndDdhOracle sigAndDdhSpec gapDhDdhOracle pqSamplers

private theorem fgKeyInd1KeyGapDhActiveDslProg_init_ddhQ (S : Setup) (b : QueryBudget) (U V : Bytes) :
    (((fgKeyInd1KeyGapDhActiveDslProg S b).init).eval (.cons (U, V) .nil)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) 0 := by
  have hq := Comp.queryBound_eval (I := pqSigAndDdhIface) (fun q => isDdhChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
    act_hwDdh act_hUDdh (fgKeyInd1KeyGapDhActiveDslProg S b).init (.cons (U, V) .nil)
  have hP : (liftGdhComp (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initParams1KeyActiveC S b
      (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
      (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero)).queries wDdh1Key wsZero1Key = 0 :=
    (SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_queries_ddh _).trans
      (initParams1KeyActiveC_queries_zero S b .zero wDdhGdh)
  have hB : (liftGdhComp (gPrim (Γ := paramsTy :: .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) sBool)).queries
      wDdh1Key wsZero1Key = 0 := by
    rw [SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_queries_ddh]
    simp only [gPrim, liftBase, sBool, Comp.queries, wsZero]
  have hQLet : ∀ {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
      (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ₂),
      (k .zero).queries wDdh1Key wsZero1Key = 0 →
      (letV e k).queries wDdh1Key wsZero1Key = 0 := by
    intro _ _ _ _ _ hk; simp only [letV, Comp.queries, hk]
  have hQBind : ∀ {Γ : List PT} {τ₁ τ₂ : PT} (c1 : Comp pqxdhOps pqSigAndDdhIface Γ τ₁)
      (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ₂),
      c1.queries wDdh1Key wsZero1Key = 0 →
      (k .zero).queries wDdh1Key wsZero1Key = 0 →
      (bindV c1 k).queries wDdh1Key wsZero1Key = 0 := by
    intro _ _ _ _ _ h1 h2; simp only [bindV, Comp.queries, h1, h2]
  have hI : (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
    change (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries wDdh1Key wsZero1Key = 0
    dsimp only [fgKeyInd1KeyGapDhActiveDslProg]
    exact hQLet _ _ (hQBind _ _ hP (hQBind _ _ hB rfl))
  exact hq.mono hI.le

private theorem fgKeyInd1KeyGapDhActiveDslProg_init_fgLEmpty (S : Setup) (b : QueryBudget) (U V : Bytes) :
    ∀ (as : (Ty.prod .unit gdh1KeyActiveStateTy).denote),
      as ∈ support (((fgKeyInd1KeyGapDhActiveDslProg S b).init).eval (.cons (U, V) .nil)) →
      as.2.1.1.2.2.1 = [] := by
  have hLetSup : ∀ {Γ : List PT} {τ₁ τ₂ : PT}
      (e : Expr pqxdhOps Γ τ₁)
      (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ₂)
      (env : Env Γ) (y : τ₂.denote),
      y ∈ support ((letV e k).eval env) → y ∈ support ((k .zero).eval (.cons (e.eval env) env)) := by
    intro Γ τ₁ τ₂ e k env y hy
    exact Eq.mp (congrArg (fun oa => y ∈ support oa) (letV_eval e k env)) hy
  have hBindSup : ∀ {Γ : List PT} {τ₁ τ₂ : PT}
      (c1 : Comp pqxdhOps pqSigAndDdhIface Γ τ₁)
      (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ₂)
      (env : Env Γ) (y : τ₂.denote),
      y ∈ support ((bindV c1 k).eval env) → ∃ x, y ∈ support ((k .zero).eval (.cons x env)) := by
    intro Γ τ₁ τ₂ c1 k env y hy
    dsimp only [bindV, Comp.eval] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨x, _, hy⟩ := hy
    exact ⟨x, hy⟩
  intro as has
  dsimp only [fgKeyInd1KeyGapDhActiveDslProg] at has
  have has1 := hLetSup _ _ _ _ has
  obtain ⟨pa, has2⟩ := hBindSup _ _ _ _ has1
  obtain ⟨secb, has3⟩ := hBindSup _ _ _ _ has2
  dsimp only [Comp.eval] at has3
  rw [support_pure, Set.mem_singleton_iff] at has3
  subst has3
  simp only [emptySimE, smMk, v, Expr.eval]

private theorem fgKeyInd1KeyGapDhActiveDslProg_ddhBounded_bilinear (S : Setup) (b : QueryBudget)
    (r_max s_max : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hRo : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_max)
    (hSess : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_max)
    (U V : Bytes) :
    ((fgKeyInd1KeyGapDhActiveDslProg S b).eval A (U, V)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true)
      (4 * r_max * s_max + 2 * s_max * (s_max - 1) +
        b.q_total + min b.q_total S.N_dh + min b.q_total S.N_sess_tot) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine (isQueryBoundP_bind (n := 0)
    (m := 4 * r_max * s_max + 2 * s_max * (s_max - 1) +
      (b.q_total + min b.q_total S.N_dh + min b.q_total S.N_sess_tot))
    (fgKeyInd1KeyGapDhActiveDslProg_init_ddhQ S b U V) fun as has => ?_).mono (by omega)
  have hEmpty := fgKeyInd1KeyGapDhActiveDslProg_init_fgLEmpty S b U V as has
  have hSim := act_simulateQ_ddhPhi (fun s : gdh1KeyActiveStateTy.denote => s.1.1.2.2.1)
    (gdh1KeyActiveHandle S b.q_total)
    (gdh1KeyActiveHandle_ddhStep_ro S b.q_total)
    (gdh1KeyActiveHandle_ddhStep_sess S b.q_total)
    (gdh1KeyActiveHandle_ddhStep_other S b.q_total)
    (A as.1) r_max s_max as.2 (hRo as.1) (hSess as.1)
  rw [hEmpty, show fgRDone [] = 0 from rfl, show fgSDone [] = 0 from rfl,
    fgDdhPhi_zero_done] at hSim
  refine isQueryBoundP_bind
    (n := 4 * r_max * s_max + 2 * s_max * (s_max - 1))
    (m := b.q_total + min b.q_total S.N_dh + min b.q_total S.N_sess_tot)
    hSim fun bs _ => ?_
  exact (Comp.queryBound_eval (I := pqSigAndDdhIface) (fun q => isDdhChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight
    act_hwDdh act_hUDdh (gdh1KeyActiveFinish S b.q_total) (.cons bs.2 (.cons bs.1 .nil))).mono
    (gdh1KeyActiveFinish_ddhQueries_le S b.q_total)

end

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Ty.denote pqChalIface pqPrimIface sigAndDdhOracle sigAndDdhSpec
  SignalPqxdh.sigOracleSpec SignalPqxdh.gapDhOracleSpec gapDhDdhOracle Env.get Ext.wk

private theorem act_sigAndDdh_ddhBounded_of_le (S : Setup) {ch out : PT}
    (R : CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S) ch .unit .bool out)
    {q B : ℕ} (hq : R.totalQueries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight q ≤ B)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) q) (x : ch.denote) :
    (R.eval A x).IsQueryBoundP (fun t => isDdhChalQuery t = true) B :=
  (R.queryBound_eval (fun t => isDdhChalQuery t = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight act_hwDdh act_hUDdh A q hA x).mono hq

private theorem act_sigActive_totalDdhQueries_quad_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤ 4 * b.q_total ^ 2 :=
  (sigKeyInd1KeyActiveDslProg_ddhQueries_quad_eq S b).le

private theorem sigKeyInd1KeyActiveDslProg_ddhBounded_gdhQueryBudget (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    ((sigKeyInd1KeyActiveDslProg S b).eval (fun _ => A.1.run) pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (gdhQueryBudget S b) := by
  obtain ⟨hRoRaw, hSend, hRecv, hTotRaw, hOnRaw⟩ := A.2
  have hTot : A.1.run.IsQueryBoundP (isGameQuery (G := keyIndSpec S)) b.q_total := by
    convert hTotRaw using 1
    funext q; cases q
    · exact propext ⟨False.elim, Bool.noConfusion⟩
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  let M_ro := min b.q_ro b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  by_cases hLe : 4 * b.q_total ^ 2 ≤ 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)
  · refine (act_sigAndDdh_ddhBounded_of_le S (sigKeyInd1KeyActiveDslProg S b)
      (act_sigActive_totalDdhQueries_quad_le S b) (fun _ => A.1.run) (fun _ => hTot) pk).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * b.q_total ^ 2 ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [Nat.min_eq_left hLe]
    omega
  · have hMin : min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) =
        4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) :=
      Nat.min_eq_right (Nat.le_of_not_le hLe)
    have hRoOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) b.q_ro := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hRoRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isRoQ, isKeyIndRoQuery]
    have hSessOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) S.N_sess_tot := by
      refine isQueryBoundP_or_add (p₁ := isKeyIndSendQuery) (p₂ := isKeyIndRecvQuery) ?_ hSend hRecv
      intro t ht
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isSessQ, isKeyIndSendQuery, isKeyIndRecvQuery]
    have hSessQOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) b.q_on := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hOnRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isSessQ, SignalPqxdh.isKeyIndOnlineQuery]
    have hRoM : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) M_ro := by
      by_cases h1 : b.q_ro ≤ b.q_total
      · simpa [M_ro, Nat.min_eq_left h1] using hRoOn
      · simpa [M_ro, Nat.min_eq_right (Nat.le_of_not_le h1)] using isQueryBoundP_of_imp
          (fun t (ht : _root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessOnTot : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) (min b.q_on b.q_total) := by
      by_cases hOn : b.q_on ≤ b.q_total
      · simpa [Nat.min_eq_left hOn] using hSessQOn
      · simpa [Nat.min_eq_right (Nat.le_of_not_le hOn)] using isQueryBoundP_of_imp
          (fun t (ht : _root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessM : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) M_sess := by
      by_cases h2 : min b.q_on b.q_total ≤ S.N_sess_tot
      · simpa [M_sess, Nat.min_eq_left h2] using hSessOnTot
      · simpa [M_sess, Nat.min_eq_right (Nat.le_of_not_le h2)] using hSessOn
    refine (sigKeyInd1KeyActiveDslProg_ddhBounded_bilinear S b M_ro M_sess
      (fun _ => A.1.run) (fun _ => hRoM) (fun _ => hSessM) pk).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [hMin]
    omega

private theorem fgKeyInd1KeyGapDhActiveDslProg_ddhBounded_gdhQueryBudget (S : Setup) (b : QueryBudget)
    (hSyntacticQuad : (fgKeyInd1KeyGapDhActiveDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    ((fgKeyInd1KeyGapDhActiveDslProg S b).eval (fun _ => A.1.run) (U, V)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (gdhQueryBudget S b) := by
  obtain ⟨hRoRaw, hSend, hRecv, hTotRaw, hOnRaw⟩ := A.2
  have hTot : A.1.run.IsQueryBoundP (isGameQuery (G := keyIndSpec S)) b.q_total := by
    convert hTotRaw using 1
    funext q; cases q
    · exact propext ⟨False.elim, Bool.noConfusion⟩
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  let M_ro := min b.q_ro b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  by_cases hLe : 4 * b.q_total ^ 2 ≤ 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)
  · refine (act_sigAndDdh_ddhBounded_of_le S (fgKeyInd1KeyGapDhActiveDslProg S b)
      hSyntacticQuad (fun _ => A.1.run) (fun _ => hTot) (U, V)).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [Nat.min_eq_left hLe]
  · have hMin : min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) =
        4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) :=
      Nat.min_eq_right (Nat.le_of_not_le hLe)
    have hRoOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) b.q_ro := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hRoRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isRoQ, isKeyIndRoQuery]
    have hSessOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) S.N_sess_tot := by
      refine isQueryBoundP_or_add (p₁ := isKeyIndSendQuery) (p₂ := isKeyIndRecvQuery) ?_ hSend hRecv
      intro t ht
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isSessQ, isKeyIndSendQuery, isKeyIndRecvQuery]
    have hSessQOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) b.q_on := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hOnRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isSessQ, SignalPqxdh.isKeyIndOnlineQuery]
    have hRoM : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) M_ro := by
      by_cases h1 : b.q_ro ≤ b.q_total
      · simpa [M_ro, Nat.min_eq_left h1] using hRoOn
      · simpa [M_ro, Nat.min_eq_right (Nat.le_of_not_le h1)] using isQueryBoundP_of_imp
          (fun t (ht : _root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessOnTot : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) (min b.q_on b.q_total) := by
      by_cases hOn : b.q_on ≤ b.q_total
      · simpa [Nat.min_eq_left hOn] using hSessQOn
      · simpa [Nat.min_eq_right (Nat.le_of_not_le hOn)] using isQueryBoundP_of_imp
          (fun t (ht : _root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessM : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) M_sess := by
      by_cases h2 : min b.q_on b.q_total ≤ S.N_sess_tot
      · simpa [M_sess, Nat.min_eq_left h2] using hSessOnTot
      · simpa [M_sess, Nat.min_eq_right (Nat.le_of_not_le h2)] using hSessOn
    refine (fgKeyInd1KeyGapDhActiveDslProg_ddhBounded_bilinear S b M_ro M_sess
      (fun _ => A.1.run) (fun _ => hRoM) (fun _ => hSessM) U V).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) + b.q_total +
        min b.q_total S.N_dh + min b.q_total S.N_sess_tot ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [hMin]
    have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
    omega

end

end ActiveBilinearDdh

section IrredBounded
attribute [local irreducible] sigKeyInd1KeyActiveDslProg fgKeyInd1KeyGapDhActiveDslProg

theorem sigKeyInd1KeyActiveDslProg_ddhBounded (S : Setup) (b : QueryBudget)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) b.q_total) (pk : Bytes) :
    ((sigKeyInd1KeyActiveDslProg S b).eval A pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot) :=
  sigAndDdh_ddhBounded_of_le S (ch := B 32) (out := .prod (B 1569) (B 64)) (sigKeyInd1KeyActiveDslProg S b)
    (sigKeyInd1KeyActiveDslProg_ddhQueries_le S b) A hA pk

theorem sigKeyInd1KeyActiveDslProg_primBounded (S : Setup) (b : QueryBudget)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) b.q_total) (pk : Bytes) :
    ((sigKeyInd1KeyActiveDslProg S b).eval A pk).IsQueryBoundP
      (fun q => isPrimQuery q = true) (primQueryBudget S b) :=
  sigAndDdh_primBounded_of_le S (ch := B 32) (out := .prod (B 1569) (B 64)) (sigKeyInd1KeyActiveDslProg S b)
    (sigKeyInd1KeyActiveDslProg_primQueries_le S b) A hA pk

theorem fgKeyInd1KeyGapDhActiveDslProg_ddhBounded (S : Setup) (b : QueryBudget)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) b.q_total) (U V : Bytes) :
    ((fgKeyInd1KeyGapDhActiveDslProg S b).eval A (U, V)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot) :=
  sigAndDdh_ddhBounded_of_le S (ch := .prod (B 32) (B 32)) (out := B 32) (fgKeyInd1KeyGapDhActiveDslProg S b)
    (fgKeyInd1KeyGapDhActiveDslProg_ddhQueries_le S b) A hA (U, V)

theorem fgKeyInd1KeyGapDhActiveDslProg_primBounded (S : Setup) (b : QueryBudget)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) b.q_total) (U V : Bytes) :
    ((fgKeyInd1KeyGapDhActiveDslProg S b).eval A (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true) (primQueryBudget S b) :=
  sigAndDdh_primBounded_of_le S (ch := .prod (B 32) (B 32)) (out := B 32) (fgKeyInd1KeyGapDhActiveDslProg S b)
    (fgKeyInd1KeyGapDhActiveDslProg_primQueries_le S b) A hA (U, V)

end IrredBounded

section SessionSplit
open _root_.SignalPqxdh (KeyIndQuery)
open _root_.SignalPqxdh.LegacyCosted (keyIndQenc)
open _root_.SignalPqxdh.Security (gdhPrimQueryBudget)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (delegateFgNSC gdhHandleNS_primUB16 liftGdhToSigDdh_primUB
  gdhState2Ty params2Ty simTy pa2Mk renamePair wrapSim2 wrapBase2 initPrinGdh2B genSpkGdh2B genOpkGdh2B
  gdhHandle2 litB smBase paU paV paUp paOpkMode letV_eval Ext.step_wk' Ext.refl_wk' Env.get_zero' Env.get_succ')
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (mkSecretPosC_primUB sDrKey96_queriesUB
  qPow8_queriesUB qSigPkGen_queriesUB wPrimBase wsZeroBase)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (callGdhHandleNS callGdhHandleNS_queries_prim_le
  callGdhHandle_eval_NS comp_primBound isSessionQ ite_eval_queryBound keyIndAdv_gameBound keyIndAdv_sessionBound
  keyIndAdv_sessionBound_on split_prim_eq_gdhPrimQueryBudget)

private def gdhHandle2NS (_S : Setup) (K : Nat) :
    Comp pqxdhOps pqGapDhIface [gdhState2Ty, keyIndQueryTy] (.prod keyIndRespTy gdhState2Ty) :=
  let st : Var [gdhState2Ty, keyIndQueryTy] gdhState2Ty := .zero
  let q : Var [gdhState2Ty, keyIndQueryTy] keyIndQueryTy := .succ .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  caseSumV (v q) (fun u => wrapSim2 pa (initPrinGdh2B K pa sm bSt u)) fun r1 =>
  caseSumV (v r1) (fun u => wrapBase2 pa sm (corruptB K bSt u)) fun r2 =>
  caseSumV (v r2) (fun x => wrapSim2 pa (genSpkGdh2B K pa sm bSt x)) fun r3 =>
  caseSumV (v r3) (fun x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x)) fun r4 =>
  caseSumV (v r4) (fun _ => .ret (.pair rNone (v st))) fun r5 =>
  caseSumV (v r5) (fun _ => .ret (.pair rNone (v st))) fun r6 =>
  caseSumV (v r6) (fun _ => .ret (.pair rNone (v st))) fun r7 =>
  caseSumV (v r7) (fun _ => .ret (.pair rNone (v st))) fun r8 =>
  caseSumV (v r8) (fun sid => wrapBase2 pa sm (testB K bSt sid)) fun r9 =>
  caseSumV (v r9) (fun sec => wrapSim2 pa (roParsedC K sm sec)) fun r10 =>
  caseSumV (v r10) (fun _ => .ret (.pair rNone (v st))) fun r11 =>
  caseSumV (v r11) (fun sid => wrapBase2 pa sm (revealB K bSt sid)) fun r12 =>
  caseSumV (v r12) (fun sk => wrapSim2 pa (registerGdhB sm bSt sk))
                   (fun x => wrapBase2 pa sm (revealSpkB K bSt x))

private theorem gdhHandle2NS_primUB16 (S : Setup) (K : Nat) :
    (gdhHandle2NS S K).queriesUB wPrimGdh wsZero ≤ 16 := by
  have hwBase : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
      (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)),
      (wrapBase2 pa sm c).queriesUB wPrimGdh wsZero =
        c.queriesUB wPrimBase wsZeroBase := by
    intro _ _ _ _ _ pa sm c
    simp [wrapBase2, bindV_queriesUB, gPrim_queriesUB_wPrimGdh, Comp.queriesUB]
  have hwSim : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
      (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)),
      (wrapSim2 pa c).queriesUB wPrimGdh wsZero =
        c.queriesUB wPrimGdh wsZero := by
    intro _ _ _ pa c
    simp [wrapSim2, bindV_queriesUB, Comp.queriesUB]
  simp only [gdhHandle2NS, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    hwBase, hwSim,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519Base_queriesUB, qPow8_queriesUB, qSigPkGen_queriesUB, qSigSign_queriesUB,
    qKemKeyGen_queriesUB, Comp.queriesUB]
  omega

/-- Variant of `sig1KeyActivePreDispatchC` replacing the initiator signature-check arms with `.inr ()`. -/
@[expose] def sig1KeyActivePreDispatchNSC (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.sum S1ARS .unit) :=
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.inl (.pair rNone (v st)))) <|
  caseSumV (v q) (fun u => bindV (sig1KeyActiveInitPrinB K st u) fun r => .ret (.inl (v r))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q)
    (fun x => .ite (optNatMatchesE (saTP (v st)) (.fst (v x)))
      (letV (saInner (v st)) fun s =>
       bindV (sig1KeyTargetGenSpkB K s x) fun r =>
       .ret (.inl (.pair (.fst (v r)) (.pair (saTP (v st)) (.snd (v r))))))
      (.ret (.inr .unit))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun _ =>
  .ret (.inr .unit)

/-- Variant of `sig1KeyActiveHandleC` with the session arms replaced by no-ops. -/
@[expose] def sig1KeyActiveHandleNSC (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, keyIndQueryTy] S1ARS :=
  let st : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy := .zero
  let q : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  bindV (sig1KeyActivePreDispatchNSC K st q) fun pre =>
  caseSumV (v pre) (fun res => .ret (v res)) fun _ =>
  letV (saInner (v st)) fun s =>
  bindV (delegateFgNSC S K s q) fun r =>
  .ret (.pair (.fst (v r)) (.pair (saTP (v st)) (.snd (v r))))

private def sig1KeyActiveHandle2NSC (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, keyIndQueryTy] S1ARS :=
  let st : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy := .zero
  let q : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  bindV (sig1KeyActivePreDispatchNSC K st q) fun pre =>
  caseSumV (v pre) (fun res => .ret (v res)) fun _ =>
  letV (saInner (v st)) fun s =>
  letV (.pair (pa2Mk (litB 32 []) (s1Pk (v s)) (litB 32 []) .none (.bool false) .none .none
      (.bool false) .none (.nat 1)) (s1Fg (v s))) fun gdhSt2 =>
  bindV (liftGdhToSigDdh ((gdhHandle2NS S K).rename (renamePair gdhSt2 (Ext.wk q)))) fun r =>
  .ret (.pair (.fst (v r)) (.pair (saTP (v st)) (s1Upd (v s) (fg := .snd (.snd (v r))))))

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] pqChalIface pqPrimIface gapDhDdhOracle sigAndDdhOracle pqSamplers

private theorem sig1KeyActiveHandle2NSC_primQueries_le (S : Setup) (K : Nat) :
    (sig1KeyActiveHandle2NSC S K).queries lcPrimW lcZeroWS ≤ 32 := by
  refine (Comp.queries_le_queriesUB _ _ _).trans ?_
  have h16 := gdhHandle2NS_primUB16 S K
  simp only [sig1KeyActiveHandle2NSC, sig1KeyActivePreDispatchNSC,
    sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB, s1Prim_primUB, qSigDdhSign_primUB,
    liftGdhToSigDdh_primUB, Comp.rename_queriesUB, sBytes32_queriesUB,
    sRandom64_queriesUB, qX25519Base_queriesUB, qKemKeyGen_queriesUB, Comp.queriesUB]
  omega

end

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk
attribute [local irreducible] initPrinGdh2B corruptB genSpkGdh2B genOpkGdh2B
  testB roParsedC revealB registerGdhB revealSpkB wrapBase2 wrapSim2

private theorem sig1KeyActivePreDispatchC_eval_NS (S : Setup) (K : Nat) (q : KeyIndQuery S)
    (hq : isSessionQ q = false) (st : sig1KeyActiveStTy.denote) :
    (sig1KeyActivePreDispatchC S K
      (.zero : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy)
      (.succ .zero : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy)).eval
        (.cons st (.cons (keyIndQenc q) .nil)) =
      (sig1KeyActivePreDispatchNSC K
        (.zero : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy)
        (.succ .zero : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy)).eval
          (.cons st (.cons (keyIndQenc q) .nil)) := by
  cases q <;> simp only [isSessionQ, Bool.true_eq_false] at hq <;> rfl

private theorem gdhHandle2_eval_NS_sig (S : Setup) (K : Nat) (q : KeyIndQuery S)
    (hq : isSessionQ q = false) (gst : gdhState2Ty.denote) :
    (gdhHandle2 S K).eval (.cons gst (.cons (keyIndQenc q) .nil)) =
      (gdhHandle2NS S K).eval (.cons gst (.cons (keyIndQenc q) .nil)) := by
  cases q <;> simp only [isSessionQ, Bool.true_eq_false] at hq <;> rfl

attribute [local semireducible] initPrinGdh2B corruptB genSpkGdh2B genOpkGdh2B
  testB roParsedC revealB registerGdhB revealSpkB wrapBase2 wrapSim2
attribute [local semireducible] Env.get Ext.wk
end

section
set_option allowUnsafeReducibility true
attribute [local irreducible] gdhHandle2 gdhHandle2NS

private theorem sig1KeyActiveHandleC_eval_NS (S : Setup) (K : Nat) (q : KeyIndQuery S)
    (hq : isSessionQ q = false) (st : sig1KeyActiveStTy.denote) :
    (sig1KeyActiveHandleC S K).eval (.cons st (.cons (keyIndQenc q) .nil)) =
      (sig1KeyActiveHandle2NSC S K).eval (.cons st (.cons (keyIndQenc q) .nil)) := by
  unfold sig1KeyActiveHandleC sig1KeyActiveHandle2NSC
  simp only [bindV, Comp.eval, sig1KeyActivePreDispatchC_eval_NS S K q hq st]
  refine bind_congr fun pre => ?_
  rcases pre with res | ⟨⟩
  · rfl
  · simp only [caseSumV, v, Expr.eval, letV_eval, Comp.eval, liftGdhToSigDdh_eval,
      comp_rename_eval]
    have hEnv : ∀ (gst : gdhState2Ty.denote) (sVal : sig1KeyStTy.denote)
        (y : Ty.denote .unit) (preVal : Ty.denote (.sum S1ARS .unit)),
        _root_.ReductionDsl.Env.ofRename
          (renamePair .zero (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.cons gst (.cons sVal (.cons y (.cons preVal (.cons st (.cons (keyIndQenc q) .nil)))))) =
        .cons gst (.cons (keyIndQenc q) .nil) := fun _ _ _ _ => rfl
    simp only [Ext.wk, hEnv, gdhHandle2_eval_NS_sig S K q hq]

attribute [local semireducible] gdhHandle2 gdhHandle2NS
end

private abbrev SigActNSEq (S : Setup) (K : Nat) (q : KeyIndQuery S) : Prop :=
  ∀ st : sig1KeyActiveStTy.denote, (sig1KeyActiveHandleC S K).eval (.cons st (.cons (keyIndQenc q) .nil)) =
    (sig1KeyActiveHandle2NSC S K).eval (.cons st (.cons (keyIndQenc q) .nil))

private theorem sigActNS_initPrin (S : Setup) (K : Nat) (u) : SigActNSEq S K (.initPrin u) :=
  sig1KeyActiveHandleC_eval_NS S K (.initPrin u) rfl
private theorem sigActNS_corruptIK (S : Setup) (K : Nat) (u) : SigActNSEq S K (.corruptIK u) :=
  sig1KeyActiveHandleC_eval_NS S K (.corruptIK u) rfl
private theorem sigActNS_genSPK (S : Setup) (K : Nat) (u j) : SigActNSEq S K (.genSPK u j) :=
  sig1KeyActiveHandleC_eval_NS S K (.genSPK u j) rfl
private theorem sigActNS_genOPK (S : Setup) (K : Nat) (u j o) : SigActNSEq S K (.genOPK u j o) :=
  sig1KeyActiveHandleC_eval_NS S K (.genOPK u j o) rfl
private theorem sigActNS_testSession (S : Setup) (K : Nat) (sid) : SigActNSEq S K (.testSession sid) :=
  sig1KeyActiveHandleC_eval_NS S K (.testSession sid) rfl
private theorem sigActNS_roQuery (S : Setup) (K : Nat) (x) : SigActNSEq S K (.roQuery x) :=
  sig1KeyActiveHandleC_eval_NS S K (.roQuery x) rfl
private theorem sigActNS_revealDhSecrets (S : Setup) (K : Nat) : SigActNSEq S K .revealDhSecrets :=
  sig1KeyActiveHandleC_eval_NS S K .revealDhSecrets rfl
private theorem sigActNS_revealSessionKey (S : Setup) (K : Nat) (sid) :
    SigActNSEq S K (.revealSessionKey sid) :=
  sig1KeyActiveHandleC_eval_NS S K (.revealSessionKey sid) rfl
private theorem sigActNS_registerKey (S : Setup) (K : Nat) (sk) : SigActNSEq S K (.registerKey sk) :=
  sig1KeyActiveHandleC_eval_NS S K (.registerKey sk) rfl
private theorem sigActNS_revealSpkSk (S : Setup) (K : Nat) (u j) : SigActNSEq S K (.revealSpkSk u j) :=
  sig1KeyActiveHandleC_eval_NS S K (.revealSpkSk u j) rfl

private theorem sig1KeyActiveHandleC_primBound_heavy (S : Setup) (K : Nat) (s : sig1KeyActiveStTy.denote)
    (t : KeyIndQuery S) :
    ((sig1KeyActiveHandleC S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) (16 * (5 * S.N_dh + S.N_sess_tot + 12)) :=
  comp_primBound _ _ ((sig1KeyActiveHandleC_primQueries_le S K).trans (by omega))

private theorem sig1KeyActiveHandleC_primBound_light (S : Setup) (K : Nat) (s : sig1KeyActiveStTy.denote)
    (t : KeyIndQuery S) (ht : isSessionQ t = false) :
    ((sig1KeyActiveHandleC S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) 32 := by
  rw [sig1KeyActiveHandleC_eval_NS S K t ht s]
  exact comp_primBound _ _ (sig1KeyActiveHandle2NSC_primQueries_le S K)

private theorem split_arith_active (q k X F : ℕ) (hk : k ≤ q) (hX : 2 ≤ X) (hF : F ≤ 16 * X) :
    0 + (q * 32 + k * (16 * X - 32)) + F ≤ 32 * (q - k) + 16 * (k + 1) * X := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 16 * X = 32 + d := ⟨16 * X - 32, by omega⟩
  have h1 : 16 * X - 32 = d := by omega
  have h2 : k + r - k = r := by omega
  have h3 : 16 * (k + 1) * X = (k + 1) * (32 + d) := by rw [← hd]; ring
  rw [h1, h2, h3]
  nlinarith

theorem sigKeyInd1KeyActiveDslProg_primBounded_split (S : Setup) (b : QueryBudget) (q m : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) q)
    (hAH : ∀ a, (A a).IsQueryBoundP
      (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessionQ t = true)) m)
    (pk : Bytes) :
    ((sigKeyInd1KeyActiveDslProg S b).eval A pk).IsQueryBoundP (fun q => isPrimQuery q = true)
      (32 * (q - min q m) + 16 * (min q m + 1) * (5 * S.N_dh + S.N_sess_tot + 12)) := by
  refine (CostedReduction.queryBound_eval₂ (sigKeyInd1KeyActiveDslProg S b) (fun q => isPrimQuery q = true)
    lcPrimW lcZeroWS ?_ ?_ (fun t => isSessionQ t = true) (kL := 32)
    (kH := 16 * (5 * S.N_dh + S.N_sess_tot + 12)) (by omega)
    (fun t s _ => sig1KeyActiveHandleC_primBound_heavy S b.q_total s t)
    (fun t s ht => sig1KeyActiveHandleC_primBound_light S b.q_total s t (by simpa using ht))
    A q m hA hAH pk).mono ?_
  · intro g x hx; rcases g with t | c'
    · simp [lcPrimW, SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    · simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) : OracleComp
      (PrimBaseSpec + sigAndDdhSpec) _) (fun qr => isPrimQuery qr = true) 0
    rw [isQueryBoundP_query_iff]; simp [isPrimQuery]
  · rw [sigKeyInd1KeyActiveDslProg_init_primQueries, sigKeyInd1KeyActiveDslProg_finish_primQueries]
    exact split_arith_active q (min q m) _ 0 (min_le_left _ _) (by omega) (Nat.zero_le _)

/-- `sig` primitive-query bound at `gdhPrimQueryBudget` for a `b`-bounded `KeyInd` adversary. -/
theorem sigKeyInd1KeyActiveDslProg_primBounded_gdhPrimQueryBudget (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    ((sigKeyInd1KeyActiveDslProg S b).eval (fun _ => A.1.run) pk).IsQueryBoundP
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b) :=
  (sigKeyInd1KeyActiveDslProg_primBounded_split S b b.q_total (min b.q_on S.N_sess_tot) (fun _ => A.1.run)
    (keyIndAdv_gameBound S b A) (fun _ => keyIndAdv_sessionBound_on S b A) pk).mono
    (le_of_eq (split_prim_eq_gdhPrimQueryBudget S b))

open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (renameComp_eval pullEnv_twoVarRen liftGdhComp_eval)

/-- `callGdhActiveHandle` with `callGdhHandleNS` in place of `callGdhHandle`. -/
@[expose] def callGdhActiveHandleNS (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  letV (.fst (v stA)) fun st1 =>
  bindV (callGdhHandleNS S K st1 (.succ q)) fun res =>
  .ret (.pair (.fst (v res)) (.pair (.snd (v res)) (.snd (v stA))))

private def callGdhActiveHandle2NS (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.pair (pa2Mk (paU (v pa)) (paV (v pa)) (paUp (v pa)) .none (.bool false) .none .none
      (paOpkMode (v pa)) .none (.nat 1)) (.snd (.fst (v st1)))) fun gst2 =>
  bindV (renameComp (twoVarRen gst2 (.succ (.succ (.succ q)))) (liftGdhComp (gdhHandle2NS S K))) fun res =>
  .ret (.pair (.fst (v res))
    (.pair (.pair (.pair (v pa) (.snd (.snd (v res)))) (.snd (v st1))) (.snd (v stA))))

private theorem callGdhActiveHandle2NS_queries_prim_le (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (qV : Var Δ keyIndQueryTy) :
    (callGdhActiveHandle2NS S K stA qV).queries wPrim1Key wsZero1Key ≤ 32 := by
  have h16 := (Comp.queries_le_queriesUB wPrimGdh wsZero (gdhHandle2NS S K)).trans (gdhHandle2NS_primUB16 S K)
  simp only [callGdhActiveHandle2NS, letV_queries, bindV_queries, renameComp_queries,
    liftGdhComp_queries_prim, Comp.queries]
  omega

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk
attribute [local irreducible] gdhHandle2 gdhHandle2NS

private theorem callGdhActiveHandle_eval_NS (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (qV : Var Δ keyIndQueryTy) (env : Env Δ) (q : KeyIndQuery S)
    (hq : env.get qV = keyIndQenc q) (hns : isSessionQ q = false) :
    (callGdhActiveHandle S K stA qV).eval env = (callGdhActiveHandle2NS S K stA qV).eval env := by
  unfold callGdhActiveHandle callGdhActiveHandle2NS
  simp only [letV_eval, bindV, Comp.eval, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
    Env.get_zero', Env.get_succ', renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval, hq,
    gdhHandle2_eval_NS_sig S K q hns]

attribute [local semireducible] gdhHandle2 gdhHandle2NS

private theorem callGdhActiveHandle_primBound_NS (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (qV : Var Δ keyIndQueryTy) (env : Env Δ) (q : KeyIndQuery S)
    (hq : env.get qV = keyIndQenc q) (hns : isSessionQ q = false) :
    ((callGdhActiveHandle S K stA qV).eval env).IsQueryBoundP (fun q => isPrimQuery q = true) 32 := by
  rw [callGdhActiveHandle_eval_NS S K stA qV env q hq hns]
  exact comp_primBound _ env (callGdhActiveHandle2NS_queries_prim_le S K stA qV)

private theorem gdh1KeyActiveHandle_primBound_light (S : Setup) (K : Nat) (s : gdh1KeyActiveStateTy.denote)
    (t : KeyIndQuery S) (ht : isSessionQ t = false) :
    ((gdh1KeyActiveHandle S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) 32 := by
  cases t with
  | initPrin u =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact comp_primBound _ _ (by
      simp only [initPrin1KeyActiveGdhB, letV_queries, bindV_queries, liftGdhComp_queries_prim,
        gPrim_queries_wPrimGdh, sBytes32_queries, qX25519Base_queries, Comp.queries]; omega)
  | corruptIK u =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact callGdhActiveHandle_primBound_NS S K _ _ _ (.corruptIK u) rfl rfl
  | genSPK u j =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact comp_primBound _ _ ((genSpk1KeyActiveGdhB_queries_prim_le _ _ _).trans (by omega))
  | genOPK u j o =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact comp_primBound _ _ (by
      simp only [genOpkActiveGdhB, letV_queries, bindV_queries, liftGdhComp_queries_prim,
        gPrim_queries_wPrimGdh, sBytes32_queries, qX25519Base_queries, Comp.queries]; omega)
  | initiateOPK u i b => simp [isSessionQ] at ht
  | initiateNoOPK u i b => simp [isSessionQ] at ht
  | acceptOPK k j o h => simp [isSessionQ] at ht
  | acceptNoOPK k j l h => simp [isSessionQ] at ht
  | testSession sid =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact callGdhActiveHandle_primBound_NS S K _ _ _ (.testSession sid) rfl rfl
  | roQuery sec =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact callGdhActiveHandle_primBound_NS S K _ _ _ (.roQuery sec) rfl rfl
  | revealDhSecrets =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact callGdhActiveHandle_primBound_NS S K _ _ _ .revealDhSecrets rfl rfl
  | revealSessionKey sid =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact callGdhActiveHandle_primBound_NS S K _ _ _ (.revealSessionKey sid) rfl rfl
  | registerKey sk =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact callGdhActiveHandle_primBound_NS S K _ _ _ (.registerKey sk) rfl rfl
  | revealSpkSk u j =>
    simp only [gdh1KeyActiveHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval, Env.get,
      Ext.refl_wk]
    exact callGdhActiveHandle_primBound_NS S K _ _ _ (.revealSpkSk u j) rfl rfl

attribute [local semireducible] Env.get Ext.wk
end

private theorem gdh1KeyActiveHandle_primBound_heavy (S : Setup) (K : Nat) (s : gdh1KeyActiveStateTy.denote)
    (t : KeyIndQuery S) :
    ((gdh1KeyActiveHandle S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) (16 * (5 * S.N_dh + S.N_sess_tot + 12)) :=
  comp_primBound _ _ ((gdh1KeyActiveHandle_queries_prim_le S K).trans (by omega))

theorem fgKeyInd1KeyGapDhActiveDslProg_primBounded_split (S : Setup) (b : QueryBudget) (q m : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) q)
    (hAH : ∀ a, (A a).IsQueryBoundP
      (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessionQ t = true)) m)
    (U V : Bytes) :
    ((fgKeyInd1KeyGapDhActiveDslProg S b).eval A (U, V)).IsQueryBoundP (fun q => isPrimQuery q = true)
      (32 * (q - min q m) + 16 * (min q m + 1) * (5 * S.N_dh + S.N_sess_tot + 12)) := by
  refine (CostedReduction.queryBound_eval₂ (fgKeyInd1KeyGapDhActiveDslProg S b) (fun q => isPrimQuery q = true)
    lcPrimW lcZeroWS ?_ ?_ (fun t => isSessionQ t = true) (kL := 32)
    (kH := 16 * (5 * S.N_dh + S.N_sess_tot + 12)) (by omega)
    (fun t s _ => gdh1KeyActiveHandle_primBound_heavy S b.q_total s t)
    (fun t s ht => gdh1KeyActiveHandle_primBound_light S b.q_total s t (by simpa using ht))
    A q m hA hAH (U, V)).mono ?_
  · intro g x hx; rcases g with t | c'
    · simp [lcPrimW, SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    · simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) : OracleComp
      (PrimBaseSpec + sigAndDdhSpec) _) (fun qr => isPrimQuery qr = true) 0
    rw [isQueryBoundP_query_iff]; simp [isPrimQuery]
  · have hF := fgKeyInd1KeyGapDhActiveDslProg_finish_primQueries_le S b
    rw [fgKeyInd1KeyGapDhActiveDslProg_init_primQueries]
    exact split_arith_active q (min q m) _ _ (min_le_left _ _) (by omega) (hF.trans (by omega))

/-- `gdh` primitive-query bound at `gdhPrimQueryBudget` for a `b`-bounded `KeyInd` adversary. -/
theorem fgKeyInd1KeyGapDhActiveDslProg_primBounded_gdhPrimQueryBudget (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    ((fgKeyInd1KeyGapDhActiveDslProg S b).eval (fun _ => A.1.run) (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b) :=
  (fgKeyInd1KeyGapDhActiveDslProg_primBounded_split S b b.q_total (min b.q_on S.N_sess_tot) (fun _ => A.1.run)
    (keyIndAdv_gameBound S b A) (fun _ => keyIndAdv_sessionBound_on S b A) U V).mono
    (le_of_eq (split_prim_eq_gdhPrimQueryBudget S b))

end SessionSplit

private theorem prim0_qBound (n : ℕ) :
    IsQueryBoundP (liftM (OracleSpec.query (spec := PrimBaseSpec) (.inl n)) : OracleComp PrimBaseSpec _)
      (fun q => isPrimQuery₀ q = true) 0 := by
  rw [isQueryBoundP_query_iff]; simp [isPrimQuery₀]

@[expose] def shcrKeyInd1KeyActiveDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv where
  State := Mid (keyIndSpec S) Bool (shcrKeyInd1KeyActiveDslProg S b).π.denote
    (shcrKeyInd1KeyActiveDslProg S b).σ.denote Bytes
  choosePk pk sk := (shcrKeyInd1KeyActiveDslProg S b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
  findCollision st ss ct := (shcrKeyInd1KeyActiveDslProg S b).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

theorem shcrKeyInd1KeyActiveDslAdv_bounded (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (shcrKeyInd1KeyActiveDslAdv S b A).Bounded := by
  let R := shcrKeyInd1KeyActiveDslProg S b
  have hQ := shcrKeyInd1KeyActiveDslProg_totalPrimQueries_le S b
  refine ⟨fun pk sk => (TwoStageCostedReduction.eval1_queryBound R (fun q => isPrimQuery₀ q = true) primW primWS (fun _
    _ _ => le_rfl) prim0_qBound (fun _ => A.1.run) (pk, sk) b.q_total false).mono ?_, fun st ss ct =>
    (TwoStageCostedReduction.eval2_queryBound R (fun q => isPrimQuery₀ q = true) primW primWS (fun _ _ _ => le_rfl)
    prim0_qBound st (ss, ct) b.q_total false).mono ?_⟩
  · unfold TwoStageCostedReduction.totalQueries at hQ
    have h1 := Nat.mul_le_mul_left b.q_total (Nat.le_max_left (R.handlePre.queries primW primWS) (R.handlePost.queries primW primWS))
    have h2 := Nat.le_max_left (R.chDone.queries primW primWS) (R.resume.queries primW primWS)
    dsimp only [shcrKeyInd1KeyActiveDslAdv, R] at *; omega
  · unfold TwoStageCostedReduction.totalQueries at hQ
    have h1 := Nat.mul_le_mul_left b.q_total (Nat.le_max_right (R.handlePre.queries primW primWS) (R.handlePost.queries primW primWS))
    have h2 := Nat.le_max_right (R.chDone.queries primW primWS) (R.resume.queries primW primWS)
    dsimp only [shcrKeyInd1KeyActiveDslAdv, R] at *; omega

section AtomicAssembly

private theorem eleven_mul_clamped_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h11 : 11 * c ≤ 720896 + 1441792 * b.q_total +
      360448 * min b.q_total S.N_dh + 360448 * min b.q_total S.N_sess_tot +
      11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      720896 * (b.q_total * b.q_total) +
      360448 * (b.q_total * min b.q_total S.N_dh) +
      360448 * (b.q_total * min b.q_total S.N_sess_tot) +
      22528 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      2816 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ stepCostBudget S b := by
  unfold stepCostBudget; dsimp only
  have hEq : 11 * (2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * min b.q_total S.N_dh ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot) =
      720896 + 1441792 * b.q_total +
        360448 * min b.q_total S.N_dh + 360448 * min b.q_total S.N_sess_tot +
        11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        720896 * (b.q_total * b.q_total) +
        360448 * (b.q_total * min b.q_total S.N_dh) +
        360448 * (b.q_total * min b.q_total S.N_sess_tot) +
        22528 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        2816 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  exact Nat.le_of_mul_le_mul_left (h11.trans_eq hEq.symm) (by omega)

private theorem two_mul_clamped_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h2 : 2 * c ≤ 131072 + 262144 * b.q_total +
      65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
      2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      131072 * (b.q_total * b.q_total) +
      65536 * (b.q_total * min b.q_total S.N_dh) +
      65536 * (b.q_total * min b.q_total S.N_sess_tot) +
      4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ stepCostBudget S b := by
  unfold stepCostBudget; dsimp only
  have hEq : 2 * (2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * min b.q_total S.N_dh ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot) =
      131072 + 262144 * b.q_total +
        65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
        2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        131072 * (b.q_total * b.q_total) +
        65536 * (b.q_total * min b.q_total S.N_dh) +
        65536 * (b.q_total * min b.q_total S.N_sess_tot) +
        4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  exact Nat.le_of_mul_le_mul_left (h2.trans_eq hEq.symm) (by omega)

theorem sigActiveAtomic_totalCost_le (S : Setup) (b : QueryBudget) : (sigKeyInd1KeyActiveAtomicProg S b).totalCost
  b.q_total ≤ stepCostBudget S b := by
  refine two_mul_clamped_le_stepCostBudget S b (le_trans (liftKeyInd1Stage_totalCost_two_mul_le tlSigDdhKeyInd rfl S
    (sigKeyInd1KeyActiveDslProg S b) b.q_total) ?_)
  have hR64 := sigKeyInd1KeyActiveDslProg_r64_le S b
  have hp := sigKeyInd1KeyActiveDslProg_totalCost_clamped_le S b
  have hmd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left _ (Nat.min_le_left _ _)
  have hqq : b.q_total ≤ b.q_total * b.q_total := Nat.le_mul_self b.q_total
  have hLog : 3 * (36 * (b.q_total + 1) * Nat.log 2 S.N_dh) ≤
      2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
    nlinarith
  dsimp only [tlSigDdhKeyInd, sampR64W, kiR64WS, zSigDdh0W, pqSigAndDdhIface] at hR64 hp ⊢
  omega

theorem shcrActiveAtomic_totalCost_le (S : Setup) (b : QueryBudget) : (shcrKeyInd1KeyActiveAtomicProg S b).totalCost
  b.q_total ≤ stepCostBudget S b := by
  refine eleven_mul_clamped_le_stepCostBudget S b (le_trans (liftKeyInd2Stage_totalCost_eleven_mul_le tlPrimKeyInd rfl S
    (shcrKeyInd1KeyActiveDslProg S b) b.q_total) ?_)
  have hp := shcrKeyInd1KeyActiveDslProg_totalCost_clamped_le S b
  have hmd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left _ (Nat.min_le_left _ _)
  have hms : b.q_total * min b.q_total S.N_sess_tot ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left _ (Nat.min_le_left _ _)
  have hms1 : min b.q_total S.N_sess_tot ≤ b.q_total := Nat.min_le_left _ _
  have hLog : 23 * (4 * (b.q_total + 1) * Nat.log 2 S.N_dh) ≤
      11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
    nlinarith
  dsimp only [tlPrimKeyInd, pqPrimIface] at hp ⊢
  omega

theorem gdhActiveAtomic_totalCost_le (S : Setup) (b : QueryBudget) : (fgKeyInd1KeyGapDhActiveAtomicProg S b).totalCost
  b.q_total ≤ stepCostBudget S b := by
  refine eleven_mul_clamped_le_stepCostBudget S b (le_trans (liftKeyInd1Stage_totalCost_eleven_mul_le tlSigDdhKeyInd rfl S
    (fgKeyInd1KeyGapDhActiveDslProg S b) b.q_total) ?_)
  have hp := fgKeyInd1KeyGapDhActiveDslProg_totalCost_clamped_le_tight S b
  have hLog : 23 * (30 * (b.q_total + 1) * Nat.log 2 S.N_dh) ≤
      11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
    nlinarith
  dsimp only [tlSigDdhKeyInd, pqSigAndDdhIface] at hp ⊢
  omega

theorem sigActiveAtomic_eval_eq (S : Setup) (b : QueryBudget) (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
  (pk : Bytes) : (sigKeyInd1KeyActiveAtomicProg S b).eval adv pk = (sigKeyInd1KeyActiveDslProg S b).eval adv pk := by
  have h := liftKeyInd1Stage_eval tlSigDdhKeyInd S (sigKeyInd1KeyActiveDslProg S b) (sigActive_init_unsupported S b)
    (sigActive_handle_unsupported S b) (sigActive_finish_unsupported S b) adv pk
  have hId : embedVal (.prod (B 1569) (B 64)) = id := by funext ⟨_, _⟩; rfl
  rw [hId, id_map] at h; exact h

theorem gdhActiveAtomic_eval_eq (S : Setup) (b : QueryBudget) (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
  (U V : Bytes) : (fgKeyInd1KeyGapDhActiveAtomicProg S b).eval adv (U, V) = (fgKeyInd1KeyGapDhActiveDslProg S b).eval
  adv (U, V) := by
  have h := liftKeyInd1Stage_eval tlSigDdhKeyInd S (fgKeyInd1KeyGapDhActiveDslProg S b) (gdhActive_init_unsupported S b)
    (gdhActive_handle_unsupported S b) (gdhActive_finish_unsupported S b) adv (U, V)
  have hId : embedVal (B 32) = id := rfl; rw [hId, id_map] at h; exact h

section ActiveSizeHelpers
open Computational.Proofs.SignalPqxdh.AtomicLift (bits_le_bits_stepCostBudget compLitSize embedMid embedMid_projMid embedVal exprLitSize kemShCrAdv_bounded_of_state_retract keyIndUnsupportedPrimW liftKeyInd1Stage_eval liftKeyInd1Stage_size_le liftKeyInd1Stage_totalCost_eleven_mul_le liftKeyInd1Stage_totalCost_two_mul_le liftKeyInd1Stage_totalQueries_le liftKeyInd2Stage_eval1 liftKeyInd2Stage_eval2 liftKeyInd2Stage_size_le liftKeyInd2Stage_totalCost_eleven_mul_le liftKeyInd2Stage_totalQueries_le one_le_pqPrimIface_qCost one_le_pqSigAndDdhIface_qCost pqOpLitSize projMid r64W red1LitSize red2LitSize sampR64W tlPrimKeyInd tlPrimKeyInd_primW tlPrimKeyInd_sizeLe tlSigDdhKeyInd tlSigDdhKeyInd_ddhW tlSigDdhKeyInd_primW tlSigDdhKeyInd_sigW tlSigDdhKeyInd_sizeLe)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (S1ARS activeSigBudget callGdhActiveHandle extract1KeyActiveC fgActiveTotalIndexCount fgKeyInd1KeyGapDhActiveAtomicProg fgKeyInd1KeyGapDhActiveDslProg gdh1KeyActiveFinish gdh1KeyActiveHandle gdh1KeyActiveStateTy genOpkActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB initParams1KeyActiveC initParams1KeyActiveFlat initPrin1KeyActiveGdhB initiateActiveGdhB initiateGdhActiveInnerB optNatMatchesE pqxdhKeyInd1KeyActiveCostedSims saInner saTP shcr1KeyActivePostC shcr1KeyActivePreC shcrActiveGenSpkB shcrActivePostTailC shcrKeyInd1KeyActiveAtomicProg shcrKeyInd1KeyActiveDslProg sig1KeyActiveHandleC sig1KeyActiveInitPrinB sig1KeyActiveInitiateCheckC sig1KeyActivePreDispatchC sig1KeyActiveStTy sigKeyInd1KeyActiveAtomicProg sigKeyInd1KeyActiveDslProg)
open _root_.ReductionDsl (Comp CostedReduction Env Expr Iface Mid PotOK TwoStageCostedReduction Ty Var bits bits_le_succ bits_mono bits_mul isGameQuery)
open _root_.SignalPqxdh (BoundedAdv Bytes F_X25519 KemShCrAdv KeyIndAdversary KeyIndQuery PrimBaseSpec QueryBudget Setup activeIdCount activeOpkCount activeSendCount activeSendOpkCount activeSpkCount isDdhChalQuery isPrimQuery isPrimQuery₀ isSigChalQuery keyIndSpec sigAndDdhSpec)
open _root_.SignalPqxdh.LegacyCosted (B PSamp bundleT gapDhDdhOracle hdrT keyIndCodec keyIndQenc pqChalIface pqGapDhIface pqPrimIface pqSamplers pqSig pqSigAndDdhIface pqxdhOps samplerZeroQueryWeight sidT sigAndDdhOracle)
open _root_.SignalPqxdh.Security (KeyIndCostedReductionBounds KeyIndCostedReductionFamily KeyIndReductionQueryBounds chalIfaceDdhQueryWeight chalIfacePrimQueryWeight chalIfaceSigQueryWeight fgTotalIndexCount gdhPrimQueryBudget gdhQueryBudget primIfacePrimQueryWeight primQueryBudget stepCostBudget)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (Ext PT S1RS accQTy acceptNoOpkGdhB acceptOpkGdhB anyMV bernoulliRatioGdhC bindV bits_0 bits_1 bits_2 bits_3 bits_eq_log2_succ bits_nRecv_le buIkB buMk buOpkB buPqspkB buPqspkId buPqspkSig buSpkB buSpkId buSpkSig caseOptV caseSumV checkProvC chooseArm2C chooseInitRandC chooseRespRandC computeOptPosInitC computePosC corruptB ddhEqC ddhEqOptC ddhQ delegateFgC drKeyTy eAny eCaseOpt eCaseSum eFind eLet eLet2 eMap emptySimE emptyStE encEC encKEM entryMatchesC eqB extract1KeyC extractMode0C fgPatchC fgPatchEntryTy fgPosTy findHonestC findMV findMapStepC finishAcceptGdhC foldMV gPrim gdhFinish gdhHandle gdhHandle2 gdhState2Ty gdhStateTy genOpkB genOpkGdhB genSpkB genSpkGdhB getDBytes hdMk honestPeerC initDh1CandC initPrin1KeyB initPrinB initPrinGdhB initQTy initSidE initiateGdhB isAdvRegC isGameOpkC isGameSpkC isSomeE keyIndLoopBound keyIndLoopBound_le_security_stepCostBudget keyIndQueryRestTy keyIndQueryTy keyIndRespEntryTy keyIndRespTy keyIndSessionEntryTy keyIndStateTy koskBundleOkPowsC koskSenderOkPowsC letV liftBase liftGdhToSigDdh litB logFindC lookupFromPowsE lookupSpkSkC mapMV mkPairPosC mkSecretPosC mulRight nRecv nat2Eq nat3Eq natEq oeMk onBase opkEntryTy optBytesEq optFst optSnd orE pa2Mk paDhFlag paEphIdx paMk paMode paOpkIdx paOpkMode paPrinFlag paPrinIdx paSpkIdx paU paUp paV paramsTy partnerC pauseCheckC pauseTy peCorrupted peIkAPk peIkSignPk peMk peSecIKA0 peSecIKAsign preKeyBundleTy primW primWS principalEntryTy qHkdfDerive96 qIsCanonical qKemDecaps qKemEncaps qKemKeyGen qPow8 qSigDdhSign qSigPkGen qSigSign qSigVerify qX25519 qX25519Base rBundle rDrKey rHdr rInitPrin rInitUnfresh rNone rPk rSpkSk registerB registerGdhB renamePair resolveSigPkC respBundleKeyE respDh1CandC revealB revealDhB revealSpkB roB roParsedC roRawFallbackC s1Base s1Budget s1Fg s1Forgery s1Mk s1Pk s1Prim s1Target s1Upd sBool sBytes32 sDrKey96 sIndex sRandom64 sbMk sbPqspkPk sbPqspkSig sbPqspkSk sbRevealed sbSpkPk sbSpkSig sbSpkSk scBase scChosen scCnt scIR scMk scRR scSIdx scTB scTPk scTSk scUpd seHdr seMk sePeerSpk seSid seUpd shcrAcceptB shcrExtractC shcrGenSpkB shcrInitiateC shcrKeyIndProg shcrKeyIndProg_size_le_tight shcrPostC shcrPostC_eq_tail shcrPostTailC shcrPreC shcrResumeC shcrStTy sidEq sig1KeyHandleC sig1KeyInitPrinB sig1KeyInitiateCheckC sig1KeyPreDispatchC sig1KeyStTy sig1KeyTargetGenSpkB sigKeyInd1KeyProg simTy slice32 smBase smFgL smLog smMk smPows smRaw smUpd spkBundleEntryTy spkPowsC stAdv stKyb stMk stOpks stPrin stResps stRo stSecb stSess stSpks stUpd stUsedN stUsedO testB tryPauseC u32OfNat v widenB widenEC wrapBase wrapBase2 wrapSim wrapSim2)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (Ren callGdhHandle gdh1KeyStateTy liftGdhComp renameComp renameExpr sigChalQ_dsl twoVarRen wDdh1Key wPrim1Key wSig1Key wsZero1Key)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (bits_32 bits_64 bits_96 bits_128 bits_160 bits_192 gdhFinish2_size_le gdhHandle2_size_le wPrimGdh wsZero)
open Computational.Proofs.SignalPqxdh.AtomicLift (liftKeyInd1Stage liftKeyInd2Stage)
open _root_.SignalPqxdh.LegacyCosted (ChallengerOracle)

section
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface

private theorem act_liftBase_size_aux {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [liftBase, Comp.size, pqChalIface, pqPrimIface]

private theorem act_liftGdhToSigDdh_size_aux {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).size = c.size := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.size]

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

private theorem act_liftGdhToSigDdh_litSize_aux {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhToSigDdh c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, compLitSize]

private theorem act_liftGdhComp_litSize_aux {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhComp c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, compLitSize]
end

@[local simp] private theorem act_liftBase_size {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := act_liftBase_size_aux c

@[local simp] private theorem act_gPrim_size {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).size = c.size := act_liftBase_size c

@[local simp] private theorem act_s1Prim_size {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).size = c.size := act_liftBase_size c

@[local simp] private theorem act_liftGdhToSigDdh_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).size = c.size := act_liftGdhToSigDdh_size_aux c

@[local simp] private theorem act_liftGdhComp_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhComp c).size = c.size := act_liftGdhComp_size_aux c

@[local simp] private theorem act_expr_rename_size {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (e : Expr pqxdhOps Γ τ) :
    (e.rename ρ).size = e.size := by
  induction e generalizing Δ <;> simp only [Expr.rename, Expr.size, *]

@[local simp] private theorem act_comp_rename_size {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (c : Comp pqxdhOps I Γ τ) :
    (c.rename ρ).size = c.size := by
  induction c generalizing Δ <;> simp only [Comp.rename, Comp.size, act_expr_rename_size, *]

@[local simp] private theorem act_renameExpr_size {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (e : Expr pqxdhOps Γ τ) :
    (renameExpr ρ e).size = e.size := by
  induction e generalizing Δ <;> simp only [renameExpr, Expr.size, *]

@[local simp] private theorem act_renameComp_size {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (c : Comp pqxdhOps I Γ τ) :
    (renameComp ρ c).size = c.size := by
  induction c generalizing Δ <;> simp only [renameComp, Comp.size, act_renameExpr_size, *]

@[local simp] private theorem act_liftBase_litSize {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (liftBase (C := C) c) = compLitSize c := act_liftBase_litSize_aux c

@[local simp] private theorem act_gPrim_litSize {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (gPrim c) = compLitSize c := act_liftBase_litSize c

@[local simp] private theorem act_s1Prim_litSize {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (s1Prim c) = compLitSize c := act_liftBase_litSize c

@[local simp] private theorem act_liftGdhToSigDdh_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhToSigDdh c) = compLitSize c := act_liftGdhToSigDdh_litSize_aux c

@[local simp] private theorem act_liftGdhComp_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhComp c) = compLitSize c := act_liftGdhComp_litSize_aux c

@[local simp] private theorem act_expr_rename_litSize {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (e : Expr pqxdhOps Γ τ) :
    exprLitSize (e.rename ρ) = exprLitSize e := by
  induction e generalizing Δ <;> simp only [Expr.rename, exprLitSize, *]

@[local simp] private theorem act_comp_rename_litSize {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (c : Comp pqxdhOps I Γ τ) :
    compLitSize (c.rename ρ) = compLitSize c := by
  induction c generalizing Δ <;> simp only [Comp.rename, compLitSize, act_expr_rename_litSize, *]

@[local simp] private theorem act_renameExpr_litSize {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (e : Expr pqxdhOps Γ τ) :
    exprLitSize (renameExpr ρ e) = exprLitSize e := by
  induction e generalizing Δ <;> simp only [renameExpr, exprLitSize, *]

@[local simp] private theorem act_renameComp_litSize {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (c : Comp pqxdhOps I Γ τ) :
    compLitSize (renameComp ρ c) = compLitSize c := by
  induction c generalizing Δ <;> simp only [renameComp, compLitSize, act_renameExpr_litSize, *]

@[local simp] private theorem act_F_X25519_length : F_X25519.length = 32 := by decide

set_option linter.unusedSimpArgs false in
private theorem act_gdhHandle2_litSize_le (S : Setup) (K : Nat) :
    compLitSize (gdhHandle2 S K) ≤ 10000 := by
  simp (config := { maxSteps := 2000000 }) only [gdhHandle2, wrapBase2, wrapSim2,
    SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.genSpkGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.genOpkGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B,
    finishAcceptGdhC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdh2B,
    acceptNoOpkGdhB, registerGdhB,
    corruptB, testB, revealB, revealSpkB,
    roRawFallbackC, roParsedC,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
    koskSenderOkPowsC, koskBundleOkPowsC, lookupSpkSkC,
    resolveSigPkC, honestPeerC, checkProvC, partnerC,
    chooseRespRandC, chooseInitRandC,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC, fgPatchC,
    entryMatchesC, ddhEqC, ddhEqOptC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2U,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2V,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2Up,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2PrinTarget,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2DhFlag,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2EphTarget,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2SpkTarget,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2OpkMode,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2OpkTarget,
    SignalPqxdh.Security.ReductionDsl.KeyInd.ephSidMatchesE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.isAdvPowsE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.recordRespC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.hkdfOrRoC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.acceptKeysC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.aiIkSk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.aiSpkSk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.aiOpkSk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.aiPqSk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.aiReplay,
    SignalPqxdh.Security.ReductionDsl.KeyInd.aiHdr,
    SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
    SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
    SignalPqxdh.Security.ReductionDsl.KeyInd.qO,
    SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr,
    SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
    SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
    SignalPqxdh.Security.ReductionDsl.KeyInd.slice32,
    SignalPqxdh.Security.ReductionDsl.KeyInd.rCorr,
    SignalPqxdh.Security.ReductionDsl.KeyInd.rAccFresh,
    SignalPqxdh.Security.ReductionDsl.KeyInd.rDh,
    SignalPqxdh.Security.ReductionDsl.KeyInd.peUpd,
    SignalPqxdh.Security.ReductionDsl.KeyInd.sbUpd,
    SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkSk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkPk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.oeConsumed,
    SignalPqxdh.Security.ReductionDsl.KeyInd.oeUpd,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seHonestPeer,
    SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerIk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerSpk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerOpk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerPqspk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seSpkHon,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seOpkHon,
    SignalPqxdh.Security.ReductionDsl.KeyInd.sePqspkHon,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seEkASk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seFresh,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seDrReal,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seDrRand,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seHdr,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seTested,
    SignalPqxdh.Security.ReductionDsl.KeyInd.seRevealed,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reRespIk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reSpk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reOpk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.rePqspk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reSenderHonest,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reDrReal,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reDrRand,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reTested,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reRevealed,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reMk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.reUpd,
    SignalPqxdh.Security.ReductionDsl.KeyInd.hdIkAPk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.hdEkAPk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.hdSpkId,
    SignalPqxdh.Security.ReductionDsl.KeyInd.hdOpkId,
    SignalPqxdh.Security.ReductionDsl.KeyInd.hdPqspkId,
    SignalPqxdh.Security.ReductionDsl.KeyInd.hdKemCt,
    SignalPqxdh.Security.ReductionDsl.KeyInd.respBundleKeyE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.kyberEq,
    SignalPqxdh.Security.ReductionDsl.KeyInd.kyberCheckE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.freshE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.optU32Eq,
    SignalPqxdh.Security.ReductionDsl.KeyInd.dhOptNZ,
    SignalPqxdh.Security.ReductionDsl.KeyInd.guardE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.nonZero32,
    SignalPqxdh.Security.ReductionDsl.KeyInd.orE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.mulRight,
    SignalPqxdh.Security.ReductionDsl.KeyInd.buildSecretsE,
    SignalPqxdh.Security.ReductionDsl.KeyInd.fePos1,
    SignalPqxdh.Security.ReductionDsl.KeyInd.fePos2,
    SignalPqxdh.Security.ReductionDsl.KeyInd.fePos3,
    SignalPqxdh.Security.ReductionDsl.KeyInd.fePos4,
    SignalPqxdh.Security.ReductionDsl.KeyInd.feSs,
    SignalPqxdh.Security.ReductionDsl.KeyInd.feDk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.feMk,
    SignalPqxdh.Security.ReductionDsl.KeyInd.catB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.consB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.takeKB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.dropB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.lenB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.eqU32,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    oeMk, seSid, seMk, seUpd, hdMk,
    rNone, rInitPrin, rBundle, rPk, rHdr, rInitUnfresh, rDrKey, rSpkSk,
    initSidE, natEq, nat2Eq, nat3Eq, sidEq, optBytesEq, isSomeE, getDBytes, optFst, optSnd,
    encEC, encKEM, eLet2,
    letV, bindV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
    eLet, eCaseOpt, eCaseSum, eAny, eFind, eMap,
    act_gPrim_litSize, gPrim, ddhQ,
    sBool, sBytes32, sRandom64, sDrKey96, sIndex,
    qX25519, qX25519Base, qPow8, qIsCanonical, qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
    litB, widenB, eqB, u32OfNat, act_F_X25519_length, v,
    compLitSize, exprLitSize, pqOpLitSize,
    ↓reduceIte, Bool.false_eq_true,
    List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
  simp only [liftBase, compLitSize, exprLitSize, pqOpLitSize,
    SignalPqxdh.TAG_EC_DJB, SignalPqxdh.TAG_KYBER_1024,
    List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
  omega

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface pqSamplers

set_option linter.unusedSimpArgs false in
private theorem sig1KeyActivePreDispatchC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyActivePreDispatchC S K (Δ := Δ) st q).size ≤ 30 * bits K + 1500 := by
  simp (config := { maxSteps := 1000000 }) only [
    sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyActiveInitiateCheckC, extract1KeyActiveC, optNatMatchesE,
    honestPeerC, findHonestC, saTP, saInner,
    s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq, eLet2,
    encEC, encKEM, widenEC, SignalPqxdh.Security.ReductionDsl.KeyInd.consB, widenB,
    letV, bindV, caseOptV, caseSumV, findMV, anyMV,
    eLet, eCaseOpt, eAny, eFind, eqB, litB, u32OfNat,
    act_s1Prim_size, qSigDdhSign, qSigVerify, qPow8, sBytes32, sRandom64, qX25519Base, qKemKeyGen,
    v, Comp.size, Expr.size, bits_0, bits_1]
  simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
    ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
  have : bits (min K S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
  have : bits (K.min S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
  omega

set_option linter.unusedSimpArgs false in
private theorem sig1KeyActivePreDispatchC_litSize_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) :
    compLitSize (sig1KeyActivePreDispatchC S K (Δ := Δ) st q) ≤ 200 := by
  simp (config := { maxSteps := 1000000 }) only [
    sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyActiveInitiateCheckC, extract1KeyActiveC, optNatMatchesE,
    honestPeerC, findHonestC, saTP, saInner,
    s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq, eLet2,
    encEC, encKEM, widenEC, SignalPqxdh.Security.ReductionDsl.KeyInd.consB, widenB,
    letV, bindV, caseOptV, caseSumV, findMV, anyMV,
    eLet, eCaseOpt, eAny, eFind, eqB, litB, u32OfNat,
    act_s1Prim_litSize, s1Prim, liftBase,
    qSigDdhSign, qSigVerify, qPow8, sBytes32, sRandom64, qX25519Base, qKemKeyGen,
    v, compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem sigKeyInd1KeyActiveDslProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).size ≤
      28000 + 285 * bits (stepCostBudget S b) ∧
    red1LitSize (sigKeyInd1KeyActiveDslProg S b) ≤ 11000 := by
  have hPreSz := sig1KeyActivePreDispatchC_size_le S b.q_total
    (Γ₁ := [sig1KeyActiveStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyActiveStTy, keyIndQueryTy])
    (Δ := [sig1KeyActiveStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hPreLit := sig1KeyActivePreDispatchC_litSize_le S b.q_total
    (Γ₁ := [sig1KeyActiveStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyActiveStTy, keyIndQueryTy])
    (Δ := [sig1KeyActiveStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hGdhSz := gdhHandle2_size_le S b.q_total
  have hGdhLit := act_gdhHandle2_litSize_le S b.q_total
  have hHdlSz : (sig1KeyActiveHandleC S b.q_total).size ≤ 280 * bits b.q_total + 27000 := by
    have hLitSz : pqxdhOps.opSize (Sum.inl (SignalPqxdh.LegacyCosted.BOp.lit 32 [])) ≤ 40 := by
      simp [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
        _root_.SignalPqxdh.LegacyCosted.pqBytesOps, ReductionDsl.Ops.sum]
    simp only [sig1KeyActiveHandleC, pa2Mk, saTP, saInner, s1Pk, s1Fg, s1Upd, s1Mk,
      s1Base, s1Target, s1Budget, s1Forgery,
      bindV, caseSumV, letV, act_liftGdhToSigDdh_size, act_comp_rename_size,
      litB, v, Comp.size, Expr.size, bits_1]
    dsimp only [pqSigAndDdhIface, pqGapDhIface, pqChalIface, sigAndDdhOracle, gapDhDdhOracle, pqSamplers] at hPreSz hGdhSz ⊢
    omega
  have hHdlLit : compLitSize (sig1KeyActiveHandleC S b.q_total) ≤ 10300 := by
    simp only [sig1KeyActiveHandleC, pa2Mk, saTP, saInner, s1Pk, s1Fg, s1Upd, s1Mk,
      s1Base, s1Target, s1Budget, s1Forgery,
      bindV, caseSumV, letV, act_liftGdhToSigDdh_litSize, act_comp_rename_litSize,
      litB, v, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, Nat.add_zero, Nat.zero_add]
    dsimp only [pqSigAndDdhIface, pqGapDhIface, pqChalIface, sigAndDdhOracle, gapDhDdhOracle, pqSamplers] at hPreLit hGdhLit ⊢
    omega
  have hInitSz : (sigKeyInd1KeyActiveDslProg S b).init.size ≤
      bits (b.q_total + 1) + bits (activeSigBudget S b) + 100 := by
    dsimp only [sigKeyInd1KeyActiveDslProg]
    split <;> {
      simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
        bindV, act_s1Prim_size, sIndex, sBool, v, Comp.size, Expr.size, bits_0]
      omega
    }
  have hFinSz : (sigKeyInd1KeyActiveDslProg S b).finish.size ≤ 50 := by
    dsimp only [sigKeyInd1KeyActiveDslProg]
    simp only [s1Forgery, saInner, eCaseOpt, litB, v, Comp.size, Expr.size]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, ReductionDsl.Ops.sum, Sum.elim_inl]
    omega
  have hInitLit : compLitSize (sigKeyInd1KeyActiveDslProg S b).init ≤ 100 := by
    dsimp only [sigKeyInd1KeyActiveDslProg]
    split <;> {
      simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
        bindV, act_s1Prim_litSize, sIndex, sBool, v, compLitSize, exprLitSize, pqOpLitSize,
        Nat.add_zero, Nat.zero_add]
      omega
    }
  have hFinLit : compLitSize (sigKeyInd1KeyActiveDslProg S b).finish ≤ 100 := by
    dsimp only [sigKeyInd1KeyActiveDslProg]
    simp only [s1Forgery, saInner, eCaseOpt, litB, v, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, Nat.add_zero, Nat.zero_add]
    omega
  have hbQ : bits b.q_total ≤ bits (stepCostBudget S b) :=
    bits_le_bits_stepCostBudget S b (by omega)
  have hbQ1 : bits (b.q_total + 1) ≤ bits (stepCostBudget S b) :=
    bits_le_bits_stepCostBudget S b (by omega)
  have hbSig : bits (activeSigBudget S b) ≤ bits (stepCostBudget S b) := by
    have hle : activeSigBudget S b ≤ b.q_total := Nat.min_le_left _ _
    exact le_trans (_root_.ReductionDsl.bits_mono hle) hbQ
  refine ⟨?_, ?_⟩
  · change (sigKeyInd1KeyActiveDslProg S b).init.size +
      (sig1KeyActiveHandleC S b.q_total).size +
      (sigKeyInd1KeyActiveDslProg S b).finish.size ≤ _
    omega
  · change compLitSize (sigKeyInd1KeyActiveDslProg S b).init +
      compLitSize (sig1KeyActiveHandleC S b.q_total) +
      compLitSize (sigKeyInd1KeyActiveDslProg S b).finish ≤ _
    omega

private theorem two_mul_bits_q1_le_bits_stepCostBudget (S : Setup) (b : QueryBudget) :
    2 * bits (b.q_total + 1) ≤ bits (stepCostBudget S b) := by
  have hm : b.q_total + 1 ≠ 0 := Nat.succ_ne_zero _
  have hpow : 2 ^ Nat.log 2 (b.q_total + 1) ≤ b.q_total + 1 := Nat.pow_log_le_self 2 hm
  have hmul : 2 ^ Nat.log 2 (b.q_total + 1) * 2 ^ Nat.log 2 (b.q_total + 1) ≤
      (b.q_total + 1) * (b.q_total + 1) := Nat.mul_le_mul hpow hpow
  have heq : 2 ^ (2 * Nat.log 2 (b.q_total + 1) + 16) =
      2 ^ 16 * (2 ^ Nat.log 2 (b.q_total + 1) * 2 ^ Nat.log 2 (b.q_total + 1)) := by
    rw [two_mul, pow_add, pow_add]; ring
  have hsq : 2 ^ (2 * Nat.log 2 (b.q_total + 1) + 16) ≤ stepCostBudget S b := by
    have h16 := Nat.mul_le_mul_left (2 ^ 16) hmul
    have hAssoc : 2 ^ 16 * ((b.q_total + 1) * (b.q_total + 1)) =
        2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) := (Nat.mul_assoc _ _ _).symm
    unfold stepCostBudget; dsimp only; omega
  have hlog : 2 * Nat.log 2 (b.q_total + 1) + 16 ≤ Nat.log 2 (stepCostBudget S b) :=
    Nat.le_log_of_pow_le (by omega) hsq
  rw [bits_eq_log2_succ, bits_eq_log2_succ]
  omega

private theorem act_caseSumV_size_diff {Δ : List PT} {a b τ : PT}
    (e : Expr pqxdhOps Δ (.sum a b))
    (f1 g1 : Var (a :: Δ) a → Comp pqxdhOps pqPrimIface (a :: Δ) τ)
    (f2 g2 : Var (b :: Δ) b → Comp pqxdhOps pqPrimIface (b :: Δ) τ)
    (d1 d2 : Nat)
    (h1 : (f1 .zero).size ≤ (g1 .zero).size + d1)
    (h2 : (f2 .zero).size ≤ (g2 .zero).size + d2) :
    (caseSumV e f1 f2).size ≤ (caseSumV e g1 g2).size + d1 + d2 := by
  simp only [caseSumV, Comp.size]
  omega

private theorem act_caseSumV_lit_le {Δ : List PT} {a b τ : PT}
    (e : Expr pqxdhOps Δ (.sum a b))
    (f1 : Var (a :: Δ) a → Comp pqxdhOps pqPrimIface (a :: Δ) τ)
    (f2 : Var (b :: Δ) b → Comp pqxdhOps pqPrimIface (b :: Δ) τ)
    (B1 B2 : Nat)
    (he : exprLitSize e = 0)
    (h1 : compLitSize (f1 .zero) ≤ B1)
    (h2 : compLitSize (f2 .zero) ≤ B2) :
    compLitSize (caseSumV e f1 f2) ≤ B1 + B2 := by
  simp only [caseSumV, compLitSize, he]
  omega

private theorem act_add_100_500_le (x y z k : Nat)
    (h1 : y = z) (h2 : x ≤ z + (k + 100) + (6 * k + 500)) :
    x ≤ y + 7 * k + 600 := by
  have hEq : z + (k + 100) + (6 * k + 500) = z + 7 * k + 600 := by ring
  rw [h1, ← hEq]
  exact h2

set_option linter.unusedSimpArgs false in
private theorem shcr1KeyActivePostC_size_diff (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) :
    (shcr1KeyActivePostC (Δ := Δ) S K s q).size ≤
      (shcrPostC (Δ := Δ) S K s q).size + 7 * bits K + 600 := by
  have hPostEq : (shcrPostC (Δ := Δ) S K s q).size =
      (caseSumV (v q) (fun u => onBase s fun g => initPrinB K g u)
        (shcrPostTailC S K s)).size :=
    congrArg Comp.size (shcrPostC_eq_tail S K s q)
  have hInit : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (u : Var Δ' .nat),
      (onBase (Δ := Δ') s fun g => initPrin1KeyB K g u).size ≤
        (onBase (Δ := Δ') s fun g => initPrinB K g u).size + (bits K + 100) := by
    intro Δ' _ u
    simp only [onBase, initPrin1KeyB, initPrinB, scBase, scUpd, scMk, scTB, scTPk, scTSk,
      scCnt, scIR, scRR, scSIdx, scChosen,
      stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
      stMk, stUpd, peMk, rNone, rInitPrin, natEq,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      letV, bindV, eAny, v, sBytes32, qX25519Base, qSigPkGen, Comp.size, Expr.size]
    omega
  have hGenSpk : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (x : Var Δ' (.prod .nat .nat)),
      (shcrActiveGenSpkB (Δ := Δ') S K s x).size ≤
        (shcrGenSpkB (Δ := Δ') S K s x).size + (6 * bits K + 500) := by
    intro Δ' _ x
    simp only [shcrActiveGenSpkB, shcrGenSpkB, onBase, genSpkB,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
      stMk, stUpd, peIkAPk, peSecIKAsign, sbMk, buMk, rNone, rBundle,
      natEq, nat2Eq, u32OfNat, encEC, encKEM, SignalPqxdh.Security.ReductionDsl.KeyInd.consB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      letV, caseOptV, bindV, eAny, eFind, v,
      sBytes32, sRandom64, qX25519Base, qKemKeyGen, qSigSign,
      Comp.size, Expr.size, bits_0]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
      ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
    omega
  have hStep0 : ∀ {Δ0 : List PT} {a b τ : PT} (e : Expr pqxdhOps Δ0 (.sum a b))
      (f1 f2 : Var (a :: Δ0) a → Comp pqxdhOps pqPrimIface (a :: Δ0) τ)
      (g1 g2 : Var (b :: Δ0) b → Comp pqxdhOps pqPrimIface (b :: Δ0) τ) (d : Nat),
      f1 .zero = f2 .zero →
      (g1 .zero).size ≤ (g2 .zero).size + d →
      (caseSumV e f1 g1).size ≤ (caseSumV e f2 g2).size + d := by
    intro Δ0 a b τ e f1 f2 g1 g2 d hf hg
    have hfs : (f1 .zero).size = (f2 .zero).size := congrArg Comp.size hf
    simp only [caseSumV, Comp.size]
    omega
  have hStepL : ∀ {Δ0 : List PT} {a b τ : PT} (e : Expr pqxdhOps Δ0 (.sum a b))
      (f1 f2 : Var (a :: Δ0) a → Comp pqxdhOps pqPrimIface (a :: Δ0) τ)
      (g1 g2 : Var (b :: Δ0) b → Comp pqxdhOps pqPrimIface (b :: Δ0) τ) (d : Nat),
      (f1 .zero).size ≤ (f2 .zero).size + d →
      g1 .zero = g2 .zero →
      (caseSumV e f1 g1).size ≤ (caseSumV e f2 g2).size + d := by
    intro Δ0 a b τ e f1 f2 g1 g2 d hf hg
    have hgs : (g1 .zero).size = (g2 .zero).size := congrArg Comp.size hg
    simp only [caseSumV, Comp.size]
    omega
  have hTail : (shcrActivePostTailC S K s (Δ := Δ) .zero).size ≤
      (shcrPostTailC S K s (Δ := Δ) .zero).size + (6 * bits K + 500) := by
    unfold shcrActivePostTailC shcrPostTailC
    refine hStep0 _ _ _ _ _ (6 * bits K + 500) ?_ ?_
    · rfl
    · refine hStepL _ _ _ _ _ (6 * bits K + 500) ?_ ?_
      · exact hGenSpk (Δ' := _ :: _ :: keyIndQueryRestTy :: Δ) .zero
      · rfl
  have hMain : (shcr1KeyActivePostC (Δ := Δ) S K s q).size ≤
      (caseSumV (v (Δ := Δ) q) (fun u => onBase s fun g => initPrinB K g u)
        (shcrPostTailC S K s)).size + (bits K + 100) + (6 * bits K + 500) := by
    unfold shcr1KeyActivePostC
    exact act_caseSumV_size_diff (Δ := Δ) (v (Δ := Δ) q)
      (fun u => onBase s fun g => initPrin1KeyB K g u)
      (fun u => onBase s fun g => initPrinB K g u)
      (shcrActivePostTailC S K s)
      (shcrPostTailC S K s)
      (bits K + 100) (6 * bits K + 500) (hInit (Δ' := .nat :: Δ) .zero) hTail
  exact act_add_100_500_le _ _ _ (bits K) hPostEq hMain

private theorem shcr1KeyActivePreC_size_diff (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) :
    (shcr1KeyActivePreC (Δ := Δ) S K s q).size ≤
      (shcrPreC (Δ := Δ) S K s q).size + 7 * bits K + 600 := by
  have hPost := shcr1KeyActivePostC_size_diff S K (Γ₁ := Γ₁) (Γ₂ := Γ₂)
    (Δ := .opt pauseTy :: Δ) s q
  simp only [shcr1KeyActivePreC, shcrPreC, bindV, caseOptV, buPqspkB, v, Comp.size, Expr.size]
  omega

set_option linter.unusedSimpArgs false in
private theorem shcrInitiateC_litSize_le (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) :
    compLitSize (shcrInitiateC (Δ := Δ) S K hasOpk s x) ≤ 500 := by
  cases hasOpk <;> {
    simp (config := { maxSteps := 500000 }) only [
      shcrInitiateC, SignalPqxdh.Security.ReductionDsl.KeyInd.initGuardE,
      initSidE, SignalPqxdh.Security.ReductionDsl.KeyInd.initFinishC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.preCheckC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.checkSigsC,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.koskBundleOkC,
      resolveSigPkC, honestPeerC, checkProvC, partnerC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hkdfOrRoC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.shcrFinE,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed,
      SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkPk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.oeConsumed,
      seSid, SignalPqxdh.Security.ReductionDsl.KeyInd.seHonestPeer,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerIk,
      sePeerSpk, SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerOpk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerPqspk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seSpkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seOpkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePqspkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seEkASk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seFresh,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seDrReal,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seDrRand,
      seHdr, SignalPqxdh.Security.ReductionDsl.KeyInd.seTested,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seRevealed,
      seMk, seUpd,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reRespIk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reSpk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reOpk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rePqspk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdIkAPk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdEkAPk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdSpkId,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdOpkId,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdPqspkId,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdKemCt,
      hdMk, buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig,
      rNone, rHdr, rInitUnfresh, rDrKey,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qO,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      isSomeE, getDBytes, optBytesEq, optFst, optSnd, orE, natEq, nat2Eq, nat3Eq,
      SignalPqxdh.Security.ReductionDsl.KeyInd.optU32Eq, sidEq,
      SignalPqxdh.Security.ReductionDsl.KeyInd.kyberEq,
      SignalPqxdh.Security.ReductionDsl.KeyInd.buildSecretsE, eLet2,
      bindV, letV, caseOptV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, v,
      litB, SignalPqxdh.Security.ReductionDsl.KeyInd.catB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.consB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.lenB,
      widenB, eqB, u32OfNat, SignalPqxdh.Security.ReductionDsl.KeyInd.eqU32,
      sBytes32, sDrKey96,
      qX25519, qX25519Base, qPow8, qSigVerify, qKemEncaps, qHkdfDerive96, encEC, encKEM,
      act_F_X25519_length, compLitSize, exprLitSize, pqOpLitSize,
      Bool.not_true, ↓reduceIte, Bool.false_eq_true,
      List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
    omega
  }

set_option linter.unusedSimpArgs false in
private theorem shcrAcceptB_litSize_le (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ accQTy) :
    compLitSize (shcrAcceptB (Δ := Δ) S K hasOpk s x) ≤ 600 := by
  cases hasOpk <;> {
    simp (config := { maxSteps := 500000 }) only [
      shcrAcceptB, onBase,
      SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.acceptNoOpkB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.acceptKeysC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.recordRespC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hkdfOrRoC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.shcrFinE,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.koskSenderOkC,
      partnerC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.aiIkSk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.aiSpkSk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.aiOpkSk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.aiPqSk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.aiReplay,
      SignalPqxdh.Security.ReductionDsl.KeyInd.aiHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qO,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed,
      SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkSk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkPk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.oeConsumed,
      oeMk, SignalPqxdh.Security.ReductionDsl.KeyInd.oeUpd,
      seSid, SignalPqxdh.Security.ReductionDsl.KeyInd.seHonestPeer,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerIk,
      sePeerSpk, SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerOpk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerPqspk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seSpkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seOpkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePqspkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seEkASk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seFresh,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seDrReal,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seDrRand,
      seHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reRespIk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reSpk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reOpk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rePqspk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reSenderHonest,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reDrReal,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reDrRand,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reTested,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reRevealed,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reMk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdIkAPk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdEkAPk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdSpkId,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdOpkId,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdPqspkId,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdKemCt,
      rNone, SignalPqxdh.Security.ReductionDsl.KeyInd.rAccFresh, rDrKey,
      isSomeE, SignalPqxdh.Security.ReductionDsl.KeyInd.isNoneRespE,
      getDBytes, optBytesEq, optFst, optSnd,
      SignalPqxdh.Security.ReductionDsl.KeyInd.dhOptNZ,
      SignalPqxdh.Security.ReductionDsl.KeyInd.guardE,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      SignalPqxdh.Security.ReductionDsl.KeyInd.kyberCheckE,
      SignalPqxdh.Security.ReductionDsl.KeyInd.freshE,
      orE, natEq, nat2Eq, nat3Eq,
      SignalPqxdh.Security.ReductionDsl.KeyInd.optU32Eq, sidEq,
      SignalPqxdh.Security.ReductionDsl.KeyInd.kyberEq,
      SignalPqxdh.Security.ReductionDsl.KeyInd.nonZero32,
      SignalPqxdh.Security.ReductionDsl.KeyInd.buildSecretsE, eLet2,
      bindV, letV, caseOptV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap, v,
      litB, SignalPqxdh.Security.ReductionDsl.KeyInd.catB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.consB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.lenB,
      widenB, eqB, u32OfNat, SignalPqxdh.Security.ReductionDsl.KeyInd.eqU32,
      sDrKey96, qX25519, qIsCanonical, qPow8, qKemDecaps, qHkdfDerive96,
      act_F_X25519_length, compLitSize, exprLitSize, pqOpLitSize,
      Bool.not_true, ↓reduceIte, Bool.false_eq_true,
      List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
    omega
  }

set_option linter.unusedSimpArgs false in
private theorem shcr1KeyActivePostC_litSize_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) :
    compLitSize (shcr1KeyActivePostC (Δ := Δ) S K s q) ≤ 10000 := by
  have hI1 : ∀ {Γx Δx : List PT} [Ext Γ₁ Δx] [Ext Γx Δx] (x : Var Γx initQTy),
      compLitSize (shcrInitiateC (Δ := Δx) S K true s x) ≤ 500 :=
    fun x => shcrInitiateC_litSize_le S K true s x
  have hI2 : ∀ {Γx Δx : List PT} [Ext Γ₁ Δx] [Ext Γx Δx] (x : Var Γx initQTy),
      compLitSize (shcrInitiateC (Δ := Δx) S K false s x) ≤ 500 :=
    fun x => shcrInitiateC_litSize_le S K false s x
  have hA1 : ∀ {Γx Δx : List PT} [Ext Γ₁ Δx] [Ext Γx Δx] (x : Var Γx accQTy),
      compLitSize (shcrAcceptB (Δ := Δx) S K true s x) ≤ 600 :=
    fun x => shcrAcceptB_litSize_le S K true s x
  have hA2 : ∀ {Γx Δx : List PT} [Ext Γ₁ Δx] [Ext Γx Δx] (x : Var Γx accQTy),
      compLitSize (shcrAcceptB (Δ := Δx) S K false s x) ≤ 600 :=
    fun x => shcrAcceptB_litSize_le S K false s x
  have hGS : ∀ {Γx Δx : List PT} [Ext Γ₁ Δx] [Ext Γx Δx] (x : Var Γx (.prod .nat .nat)),
      compLitSize (shcrActiveGenSpkB (Δ := Δx) S K s x) ≤ 200 := by
    intro Γx Δx _ _ x
    simp only [shcrActiveGenSpkB, onBase, genSpkB,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd, peIkAPk, peSecIKAsign, sbMk, buMk, rNone, rBundle,
      natEq, nat2Eq, u32OfNat, encEC, encKEM, SignalPqxdh.Security.ReductionDsl.KeyInd.consB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      letV, caseOptV, bindV, eAny, eFind, v,
      sBytes32, sRandom64, qX25519Base, qKemKeyGen, qSigSign,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
    omega
  have hRestArms : ∀ {Δ0 : List PT} [Ext Γ₁ Δ0]
      (q0 : Var (keyIndQueryRestTy :: Δ0) keyIndQueryRestTy),
      compLitSize (shcrActivePostTailC S K s (Δ := Δ0) q0) ≤ 3500 := by
    intro Δ0 _ q0
    unfold shcrActivePostTailC
    refine le_trans (act_caseSumV_lit_le _ _ _ 50 3450 rfl ?_ ?_) (by omega)
    · simp only [onBase, corruptB, scBase, scUpd, stPrin, stUpd,
        stSecb, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk,
        peIkAPk, peCorrupted, peMk, peSecIKA0, peSecIKAsign, peIkSignPk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.peUpd,
        SignalPqxdh.Security.ReductionDsl.KeyInd.rCorr, rNone,
        SignalPqxdh.Security.ReductionDsl.KeyInd.rs, natEq,
        letV, bindV, caseOptV, eCaseOpt, eFind, eMap, v,
        compLitSize, exprLitSize, pqOpLitSize, List.length_nil, Nat.add_zero, Nat.zero_add]
      omega
    · refine le_trans (act_caseSumV_lit_le _ _ _ 200 3250 rfl (hGS .zero) ?_) (by omega)
      refine le_trans (act_caseSumV_lit_le _ _ _ 50 3200 rfl ?_ ?_) (by omega)
      · simp only [onBase, genOpkB, scBase, scUpd, stPrin, stOpks, stUpd, oeMk, rNone, rPk,
          SignalPqxdh.Security.ReductionDsl.KeyInd.rs, natEq, nat2Eq, nat3Eq,
          letV, bindV, eAny, v, sBytes32, qX25519Base,
          compLitSize, exprLitSize, pqOpLitSize, List.length_nil, Nat.add_zero, Nat.zero_add]
        omega
      · refine le_trans (act_caseSumV_lit_le _ _ _ 500 2700 rfl (hI1 .zero) ?_) (by omega)
        refine le_trans (act_caseSumV_lit_le _ _ _ 500 2200 rfl (hI2 .zero) ?_) (by omega)
        refine le_trans (act_caseSumV_lit_le _ _ _ 600 1600 rfl (hA1 .zero) ?_) (by omega)
        refine le_trans (act_caseSumV_lit_le _ _ _ 600 1000 rfl (hA2 .zero) ?_) (by omega)
        simp only [caseSumV, onBase, testB, roB, revealDhB, revealB, registerB, revealSpkB,
          SignalPqxdh.Security.ReductionDsl.KeyInd.hkdfOrRoC,
          SignalPqxdh.Security.ReductionDsl.KeyInd.freshE,
          scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
          stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
          stMk, stUpd, peIkAPk, peCorrupted,
          SignalPqxdh.Security.ReductionDsl.KeyInd.peUpd,
          sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed,
          SignalPqxdh.Security.ReductionDsl.KeyInd.sbUpd,
          oeMk, seSid,
          SignalPqxdh.Security.ReductionDsl.KeyInd.seFresh,
          SignalPqxdh.Security.ReductionDsl.KeyInd.seDrReal,
          SignalPqxdh.Security.ReductionDsl.KeyInd.seDrRand,
          SignalPqxdh.Security.ReductionDsl.KeyInd.seTested,
          SignalPqxdh.Security.ReductionDsl.KeyInd.seRevealed,
          seUpd,
          SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
          SignalPqxdh.Security.ReductionDsl.KeyInd.reSenderHonest,
          SignalPqxdh.Security.ReductionDsl.KeyInd.reDrReal,
          SignalPqxdh.Security.ReductionDsl.KeyInd.reDrRand,
          SignalPqxdh.Security.ReductionDsl.KeyInd.reTested,
          SignalPqxdh.Security.ReductionDsl.KeyInd.reRevealed,
          SignalPqxdh.Security.ReductionDsl.KeyInd.reUpd,
          rNone, rPk, SignalPqxdh.Security.ReductionDsl.KeyInd.rCorr, rDrKey,
          SignalPqxdh.Security.ReductionDsl.KeyInd.rDh, rSpkSk,
          SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
          natEq, nat2Eq, nat3Eq, sidEq, orE, eLet2,
          bindV, letV, caseOptV, eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap, v,
          litB, widenB, eqB, SignalPqxdh.Security.ReductionDsl.KeyInd.lenB,
          sBytes32, sDrKey96, qX25519Base, qIsCanonical, qPow8, qHkdfDerive96,
          compLitSize, exprLitSize, pqOpLitSize, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          List.length_nil, Nat.add_zero, Nat.zero_add]
        omega
  have bTail := hRestArms (Δ0 := Δ) .zero
  unfold shcr1KeyActivePostC
  simp only [caseSumV, onBase, initPrin1KeyB,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stMk, stUpd, peMk, rNone, rInitPrin, natEq,
    SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
    letV, bindV, eAny, v, sBytes32, qX25519Base,
    compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem shcr1KeyActivePreC_litSize_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) :
    compLitSize (shcr1KeyActivePreC (Δ := Δ) S K s q) ≤ 11500 := by
  have hPostLit := shcr1KeyActivePostC_litSize_le S K
    (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := .opt pauseTy :: Δ) s q
  have hPCLit : compLitSize (pauseCheckC (Δ := Δ) S K s q) ≤ 1000 := by
    simp only [pauseCheckC, tryPauseC, SignalPqxdh.Security.ReductionDsl.KeyInd.initGuardE,
      initSidE, SignalPqxdh.Security.ReductionDsl.KeyInd.preCheckC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.checkSigsC,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.koskBundleOkC, resolveSigPkC,
      scBase, scCnt, scSIdx, stPrin, stSpks, stOpks, stSess, stAdv,
      peIkAPk, peIkSignPk, sbSpkPk, SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkPk, seSid,
      buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig, isSomeE,
      orE, natEq, nat2Eq, nat3Eq, sidEq, eLet2,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, v,
      SignalPqxdh.Security.ReductionDsl.KeyInd.consB, eqB, qPow8, qSigVerify, encEC, encKEM,
      compLitSize, exprLitSize, pqOpLitSize, ↓reduceIte, Bool.false_eq_true,
      List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
    omega
  simp only [shcr1KeyActivePreC, bindV, caseOptV, buPqspkB, v,
    compLitSize, exprLitSize, pqOpLitSize]
  omega

set_option linter.unusedSimpArgs false in
private theorem shcrKeyInd1KeyActiveDslProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).size ≤
      31000 + 285 * bits (stepCostBudget S b) ∧
    red2LitSize (shcrKeyInd1KeyActiveDslProg S b) ≤ 25000 := by
  have hBase := shcrKeyIndProg_size_le_tight S b.q_total (keyIndLoopBound b)
  have hPostDiff : (shcrKeyInd1KeyActiveDslProg S b).handlePost.size ≤
      (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).handlePost.size +
        7 * bits (keyIndLoopBound b) + 600 :=
    shcr1KeyActivePostC_size_diff S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hPreDiff : (shcrKeyInd1KeyActiveDslProg S b).handlePre.size ≤
      (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).handlePre.size +
        7 * bits (keyIndLoopBound b) + 600 :=
    shcr1KeyActivePreC_size_diff S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hInitSz : (shcrKeyInd1KeyActiveDslProg S b).init.size ≤ bits (b.q_total + 1) + 100 := by
    dsimp only [shcrKeyInd1KeyActiveDslProg]
    split <;> {
      simp only [emptyStE, stMk, scMk, bindV, v, sBool, sIndex, Comp.size, Expr.size, bits_0]
      omega
    }
  have hInitLit : compLitSize (shcrKeyInd1KeyActiveDslProg S b).init ≤ 100 := by
    dsimp only [shcrKeyInd1KeyActiveDslProg]
    split <;> {
      simp only [emptyStE, stMk, scMk, bindV, v, sBool, sIndex,
        compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
      omega
    }
  have hPostLit : compLitSize (shcrKeyInd1KeyActiveDslProg S b).handlePost ≤ 10000 :=
    shcr1KeyActivePostC_litSize_le S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hPreLit : compLitSize (shcrKeyInd1KeyActiveDslProg S b).handlePre ≤ 11500 :=
    shcr1KeyActivePreC_litSize_le S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hRestLit : compLitSize (shcrKeyInd1KeyActiveDslProg S b).chDone +
      compLitSize (shcrKeyInd1KeyActiveDslProg S b).resume +
      compLitSize (shcrKeyInd1KeyActiveDslProg S b).finish ≤ 3000 := by
    dsimp only [shcrKeyInd1KeyActiveDslProg]
    simp (config := { maxSteps := 1000000 }) only [
      shcrResumeC, shcrExtractC, SignalPqxdh.Security.ReductionDsl.KeyInd.shcrFinE,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rrCt,
      SignalPqxdh.Security.ReductionDsl.KeyInd.initFinishC,
      findHonestC, honestPeerC, checkProvC, partnerC,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hkdfOrRoC,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd, peSecIKA0, peIkAPk, peCorrupted,
      sbSpkPk, sbPqspkPk, SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkPk,
      seSid, SignalPqxdh.Security.ReductionDsl.KeyInd.seHonestPeer,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerIk,
      sePeerSpk, SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerOpk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerPqspk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seSpkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seOpkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.sePqspkHon,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seEkASk,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seFresh,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seDrReal, seHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seTested,
      SignalPqxdh.Security.ReductionDsl.KeyInd.seRevealed,
      seMk, seUpd, SignalPqxdh.Security.ReductionDsl.KeyInd.reDrRand,
      buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
      hdMk, rHdr, rInitUnfresh,
      isSomeE, getDBytes, optBytesEq, optFst, optSnd,
      SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      orE, natEq, SignalPqxdh.Security.ReductionDsl.KeyInd.buildSecretsE, eLet2,
      bindV, letV, caseOptV, findMV, anyMV, eLet, eCaseOpt, eFind, eAny, v,
      litB, SignalPqxdh.Security.ReductionDsl.KeyInd.catB, widenB, eqB,
      sBytes32, sDrKey96,
      qX25519, qX25519Base, qPow8, qKemDecaps,
      act_F_X25519_length, compLitSize, exprLitSize, pqOpLitSize, ↓reduceIte,
      List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
    omega
  have hbQ : bits b.q_total ≤ bits (stepCostBudget S b) :=
    bits_le_bits_stepCostBudget S b (by omega)
  have hbQ1 : bits (b.q_total + 1) ≤ bits (stepCostBudget S b) :=
    bits_le_bits_stepCostBudget S b (by omega)
  have hbK : bits (keyIndLoopBound b) ≤ bits (stepCostBudget S b) :=
    bits_mono (keyIndLoopBound_le_security_stepCostBudget S b)
  refine ⟨?_, ?_⟩
  · unfold TwoStageCostedReduction.size at hBase ⊢
    have hChSz : (shcrKeyInd1KeyActiveDslProg S b).chDone.size =
        (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).chDone.size := rfl
    have hResSz : (shcrKeyInd1KeyActiveDslProg S b).resume.size =
        (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).resume.size := rfl
    have hFinSz : (shcrKeyInd1KeyActiveDslProg S b).finish.size =
        (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).finish.size := rfl
    rw [hChSz, hResSz, hFinSz]
    omega
  · unfold red2LitSize
    omega

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
private theorem initParams1KeyActiveC_size_and_lit (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams1KeyActiveC S b (Δ := Δ) uv).size ≤ 16 * bits (b.q_total + 1) + 400 ∧
    compLitSize (initParams1KeyActiveC S b (Δ := Δ) uv) ≤ 10 := by
  let unreach := b.q_total + 1
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_send_opk := activeSendOpkCount S b.q_on
  let nA := n_id * n_spk
  let nC := n_send * n_spk
  let nB := n_send * n_id
  let nD := n_send_opk * n_opk
  have hA : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if nA = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool true)
            (.nat unreach) (.nat 0) (.bool false) (.nat unreach) (.nat 0))
        else
          bindV (gPrim (sIndex n_id)) fun pOrd =>
          bindV (gPrim (sIndex n_spk)) fun spkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool true)
            (.nat unreach) (v spkOrd) (.bool false) (.nat unreach) (.nat 0))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).size ≤ 4 * bits unreach + 60 ∧
      compLitSize ((if nA = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool true)
            (.nat unreach) (.nat 0) (.bool false) (.nat unreach) (.nat 0))
        else
          bindV (gPrim (sIndex n_id)) fun pOrd =>
          bindV (gPrim (sIndex n_spk)) fun spkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool true)
            (.nat unreach) (v spkOrd) (.bool false) (.nat unreach) (.nat 0))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy) ≤ 0 := by
    intro Δ' _
    split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0]
      exact ⟨by omega, by omega⟩
    }
  have hC : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if nC = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (.nat 0) (.nat 0) (.bool false) (.nat unreach) (.nat 1))
        else
          bindV (gPrim (sIndex n_send)) fun ephOrd =>
          bindV (gPrim (sIndex n_spk)) fun spkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (v ephOrd) (v spkOrd) (.bool false) (.nat unreach) (.nat 1))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).size ≤ 4 * bits unreach + 60 ∧
      compLitSize ((if nC = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (.nat 0) (.nat 0) (.bool false) (.nat unreach) (.nat 1))
        else
          bindV (gPrim (sIndex n_send)) fun ephOrd =>
          bindV (gPrim (sIndex n_spk)) fun spkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (v ephOrd) (v spkOrd) (.bool false) (.nat unreach) (.nat 1))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy) ≤ 0 := by
    intro Δ' _
    split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0, bits_1]
      exact ⟨by omega, by omega⟩
    }
  have hB : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if nB = 0 then
          .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool false)
            (.nat 0) (.nat unreach) (.bool false) (.nat unreach) (.nat 2))
        else
          bindV (gPrim (sIndex n_send)) fun ephOrd =>
          bindV (gPrim (sIndex n_id)) fun pOrd =>
          .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool false)
            (v ephOrd) (.nat unreach) (.bool false) (.nat unreach) (.nat 2))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).size ≤ 4 * bits unreach + 60 ∧
      compLitSize ((if nB = 0 then
          .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (.nat 0) (.bool false)
            (.nat 0) (.nat unreach) (.bool false) (.nat unreach) (.nat 2))
        else
          bindV (gPrim (sIndex n_send)) fun ephOrd =>
          bindV (gPrim (sIndex n_id)) fun pOrd =>
          .ret (paMk (.snd (v uv)) (.fst (v uv)) (.fst (v uv)) (.bool true) (v pOrd) (.bool false)
            (v ephOrd) (.nat unreach) (.bool false) (.nat unreach) (.nat 2))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy) ≤ 0 := by
    intro Δ' _
    split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0, bits_2]
      exact ⟨by omega, by omega⟩
    }
  have hD : ∀ {Δ' : List PT} [Ext Γ₁ Δ'],
      ((if nD = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (.nat 0) (.nat unreach) (.bool true) (.nat 0) (.nat 3))
        else
          bindV (gPrim (sIndex n_send_opk)) fun ephOrd =>
          bindV (gPrim (sIndex n_opk)) fun opkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (v ephOrd) (.nat unreach) (.bool true) (v opkOrd) (.nat 3))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy).size ≤ 4 * bits unreach + 60 ∧
      compLitSize ((if nD = 0 then
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (.nat 0) (.nat unreach) (.bool true) (.nat 0) (.nat 3))
        else
          bindV (gPrim (sIndex n_send_opk)) fun ephOrd =>
          bindV (gPrim (sIndex n_opk)) fun opkOrd =>
          .ret (paMk (.fst (v uv)) (.snd (v uv)) (.fst (v uv)) (.bool false) (.nat unreach)
            (.bool false) (v ephOrd) (.nat unreach) (.bool true) (v opkOrd) (.nat 3))) :
        Comp pqxdhOps pqGapDhIface Δ' paramsTy) ≤ 0 := by
    intro Δ' _
    split_ifs <;> {
      simp only [paMk, bindV, act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, sIndex, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, bits_0, bits_3]
      exact ⟨by omega, by omega⟩
    }
  unfold initParams1KeyActiveC
  dsimp only
  by_cases h0 : fgActiveTotalIndexCount S b.q_on = 0
  · simp only [h0, ↓reduceIte, paMk, v, Comp.size, Expr.size, compLitSize, exprLitSize, bits_0]
    exact ⟨by omega, by omega⟩
  · simp only [h0, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · refine (act_chooseArm2C_size_and_lit (Γ₁ := Γ₁) (Δ := Δ)
        (activeIdCount S b.q_on * activeSpkCount S b.q_on + activeSendCount S b.q_on * activeSpkCount S b.q_on)
        (activeSendCount S b.q_on * activeIdCount S b.q_on + activeSendOpkCount S b.q_on * activeOpkCount S b.q_on)
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
          (fun {Δ''} [_] => hB (Δ' := Δ'')) (fun {Δ''} [_] => hD (Δ' := Δ'')))).1.trans ?_
      dsimp only [unreach]; omega
    · refine (act_chooseArm2C_size_and_lit (Γ₁ := Γ₁) (Δ := Δ)
        (activeIdCount S b.q_on * activeSpkCount S b.q_on + activeSendCount S b.q_on * activeSpkCount S b.q_on)
        (activeSendCount S b.q_on * activeIdCount S b.q_on + activeSendOpkCount S b.q_on * activeOpkCount S b.q_on)
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
          (fun {Δ''} [_] => hB (Δ' := Δ'')) (fun {Δ''} [_] => hD (Δ' := Δ'')))).2.trans (by omega)

section GdhActiveSizeReducible
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] gapDhDdhOracle pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface

set_option linter.unusedSimpArgs false in
private theorem gdh1KeyActiveHandle_size_and_lit (S : Setup) (K : Nat) :
    (gdh1KeyActiveHandle S K).size ≤ 600 * bits K + 57000 ∧
    compLitSize (gdh1KeyActiveHandle S K) ≤ 23000 := by
  have hCall : ∀ {Δ : List PT} (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy),
      (callGdhActiveHandle S K stA q).size ≤ 250 * bits K + 25100 ∧
      compLitSize (callGdhActiveHandle S K stA q) ≤ 10100 := by
    intro Δ stA q
    have hSz := gdhHandle2_size_le S K
    have hLit := act_gdhHandle2_litSize_le S K
    refine ⟨?_, ?_⟩
    · simp only [callGdhActiveHandle, pa2Mk, paU, paV, paUp, paOpkMode,
        letV, bindV, act_renameComp_size, act_liftGdhComp_size, v, Comp.size, Expr.size, bits_1]
      omega
    · simp only [callGdhActiveHandle, pa2Mk, paU, paV, paUp, paOpkMode,
        letV, bindV, act_renameComp_litSize, act_liftGdhComp_litSize, v, compLitSize, exprLitSize]
      omega
  have hInitPrin : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (stA : Var Γ₁ gdh1KeyActiveStateTy) (u : Var Γ₂ .nat),
      (initPrin1KeyActiveGdhB K (Δ := Δ) stA u).size ≤ 5 * bits K + 250 ∧
      compLitSize (initPrin1KeyActiveGdhB K (Δ := Δ) stA u) ≤ 100 := by
    intro Γ₁ Γ₂ Δ _ _ stA u
    refine ⟨?_, ?_⟩
    · simp only [initPrin1KeyActiveGdhB, paPrinFlag, paPrinIdx, paUp, smBase, smUpd, smMk,
        smFgL, smRaw, smLog, smPows,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
        stMk, stUpd, peMk, rNone, rInitPrin, natEq,
        letV, bindV, eAny, act_liftGdhComp_size, act_gPrim_size, liftGdhComp, gPrim, liftBase, sBytes32, qX25519Base,
        litB, v, Comp.size, Expr.size]
      simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
        _root_.SignalPqxdh.LegacyCosted.pqBytesOps, ReductionDsl.Ops.sum, Sum.elim_inl]
      omega
    · simp only [initPrin1KeyActiveGdhB, paPrinFlag, paPrinIdx, paUp, smBase, smUpd, smMk,
        smFgL, smRaw, smLog, smPows,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
        stMk, stUpd, peMk, rNone, rInitPrin, natEq,
        letV, bindV, eAny, act_liftGdhComp_litSize, act_gPrim_litSize, liftGdhComp, gPrim, liftBase, sBytes32, qX25519Base,
        litB, v, compLitSize, exprLitSize, pqOpLitSize,
        List.length_nil, Nat.add_zero, Nat.zero_add]
      omega
  have hGenSpk : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat .nat)),
      (genSpk1KeyActiveGdhB K (Δ := Δ) stA x).size ≤ 10 * bits K + 800 ∧
      compLitSize (genSpk1KeyActiveGdhB K (Δ := Δ) stA x) ≤ 300 := by
    intro Γ₁ Γ₂ Δ _ _ stA x
    refine ⟨?_, ?_⟩
    · simp only [genSpk1KeyActiveGdhB, genSpkGdhActiveB, optNatMatchesE, sigChalQ_dsl,
        paSpkIdx, paV, smBase, smUpd, smMk, smFgL, smRaw, smLog, smPows,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
        stMk, stUpd, peIkAPk, peSecIKAsign, sbMk, buMk, rNone, rBundle,
        natEq, nat2Eq, u32OfNat, encEC, encKEM, widenEC,
        SignalPqxdh.Security.ReductionDsl.KeyInd.consB, widenB,
        letV, bindV, caseOptV, eAny, eFind, eCaseOpt,
        act_liftGdhComp_size, act_gPrim_size, liftGdhComp, gPrim, liftBase, eLet2, eLet,
        sBytes32, sRandom64, qX25519Base, qKemKeyGen, qSigSign,
        litB, v, Comp.size, Expr.size, bits_0, bits_1]
      simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
        _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
        ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
      omega
    · simp only [genSpk1KeyActiveGdhB, genSpkGdhActiveB, optNatMatchesE, sigChalQ_dsl,
        paSpkIdx, paV, smBase, smUpd, smMk, smFgL, smRaw, smLog, smPows,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
        stMk, stUpd, peIkAPk, peSecIKAsign, sbMk, buMk, rNone, rBundle,
        natEq, nat2Eq, u32OfNat, encEC, encKEM, widenEC,
        SignalPqxdh.Security.ReductionDsl.KeyInd.consB, widenB,
        letV, bindV, caseOptV, eAny, eFind, eCaseOpt,
        act_liftGdhComp_litSize, act_gPrim_litSize, liftGdhComp, gPrim, liftBase, eLet2, eLet,
        sBytes32, sRandom64, qX25519Base, qKemKeyGen, qSigSign,
        litB, v, compLitSize, exprLitSize, pqOpLitSize,
        List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
      omega
  have hGenOpk : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))),
      (genOpkActiveGdhB K (Δ := Δ) stA x).size ≤ 5 * bits K + 250 ∧
      compLitSize (genOpkActiveGdhB K (Δ := Δ) stA x) ≤ 100 := by
    intro Γ₁ Γ₂ Δ _ _ stA x
    refine ⟨?_, ?_⟩
    · simp only [genOpkActiveGdhB, paOpkMode, paOpkIdx, paV,
        smBase, smUpd, smMk, smFgL, smRaw, smLog, smPows,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
        stMk, stUpd, oeMk, rNone, rPk, natEq, nat2Eq, nat3Eq,
        letV, bindV, eAny, act_liftGdhComp_size, act_gPrim_size, liftGdhComp, gPrim, liftBase, sBytes32, qX25519Base,
        litB, v, Comp.size, Expr.size]
      simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
        _root_.SignalPqxdh.LegacyCosted.pqBytesOps, ReductionDsl.Ops.sum, Sum.elim_inl]
      omega
    · simp only [genOpkActiveGdhB, paOpkMode, paOpkIdx, paV,
        smBase, smUpd, smMk, smFgL, smRaw, smLog, smPows,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
        stMk, stUpd, oeMk, rNone, rPk, natEq, nat2Eq, nat3Eq,
        letV, bindV, eAny, act_liftGdhComp_litSize, act_gPrim_litSize, liftGdhComp, gPrim, liftBase, sBytes32, qX25519Base,
        litB, v, compLitSize, exprLitSize, pqOpLitSize,
        List.length_nil, Nat.add_zero, Nat.zero_add]
      omega
  have hInitAct : ∀ (hasOpk : Bool) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy),
      (initiateActiveGdhB S K hasOpk (Δ := Δ) stA x).size ≤ 35 * bits K + 2500 ∧
      compLitSize (initiateActiveGdhB S K hasOpk (Δ := Δ) stA x) ≤ 900 := by
    intro hasOpk Γ₁ Γ₂ Δ _ _ stA x
    cases hasOpk <;> refine ⟨?_, ?_⟩
    all_goals
      simp (config := { maxSteps := 1500000 }) only [
        initiateActiveGdhB, initiateGdhActiveInnerB,
        koskBundleOkPowsC, SignalPqxdh.Security.ReductionDsl.KeyInd.isAdvPowsE,
        resolveSigPkC, lookupSpkSkC, honestPeerC, checkProvC, isGameSpkC, isGameOpkC,
        findHonestC, chooseInitRandC, partnerC,
        computePosC, computeOptPosInitC, mkSecretPosC, mkPairPosC, fgPatchC, entryMatchesC,
        ddhEqC, ddhEqOptC,
        SignalPqxdh.Security.ReductionDsl.KeyInd.fePos1,
        SignalPqxdh.Security.ReductionDsl.KeyInd.fePos2,
        SignalPqxdh.Security.ReductionDsl.KeyInd.fePos3,
        SignalPqxdh.Security.ReductionDsl.KeyInd.fePos4,
        SignalPqxdh.Security.ReductionDsl.KeyInd.feSs,
        SignalPqxdh.Security.ReductionDsl.KeyInd.feDk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.feMk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.buildSecretsE,
        SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
        SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
        SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
        SignalPqxdh.Security.ReductionDsl.KeyInd.qO,
        SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr,
        SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
        SignalPqxdh.Security.ReductionDsl.KeyInd.oeOpkPk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.oeConsumed,
        SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
        SignalPqxdh.Security.ReductionDsl.KeyInd.reRespIk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.reSpk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.reOpk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.rePqspk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr,
        SignalPqxdh.Security.ReductionDsl.KeyInd.hdIkAPk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.hdEkAPk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.hdSpkId,
        SignalPqxdh.Security.ReductionDsl.KeyInd.hdOpkId,
        SignalPqxdh.Security.ReductionDsl.KeyInd.hdPqspkId,
        SignalPqxdh.Security.ReductionDsl.KeyInd.hdKemCt,
        SignalPqxdh.Security.ReductionDsl.KeyInd.optU32Eq,
        SignalPqxdh.Security.ReductionDsl.KeyInd.kyberEq,
        SignalPqxdh.Security.ReductionDsl.KeyInd.catB,
        SignalPqxdh.Security.ReductionDsl.KeyInd.consB,
        SignalPqxdh.Security.ReductionDsl.KeyInd.lenB,
        SignalPqxdh.Security.ReductionDsl.KeyInd.eqU32,
        paDhFlag, paOpkMode, paEphIdx, paU,
        smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb,
        stMk, stUpd,
        peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
        sbSpkSk, sbSpkPk, sbPqspkPk,
        buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig,
        seSid, SignalPqxdh.Security.ReductionDsl.KeyInd.seHonestPeer,
        SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerIk,
        sePeerSpk, SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerOpk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerPqspk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.seSpkHon,
        SignalPqxdh.Security.ReductionDsl.KeyInd.seOpkHon,
        SignalPqxdh.Security.ReductionDsl.KeyInd.sePqspkHon,
        SignalPqxdh.Security.ReductionDsl.KeyInd.seEkASk,
        SignalPqxdh.Security.ReductionDsl.KeyInd.seFresh,
        SignalPqxdh.Security.ReductionDsl.KeyInd.seDrReal,
        SignalPqxdh.Security.ReductionDsl.KeyInd.seDrRand,
        seHdr, SignalPqxdh.Security.ReductionDsl.KeyInd.seTested,
        SignalPqxdh.Security.ReductionDsl.KeyInd.seRevealed,
        seMk, seUpd, hdMk, rNone, rHdr, rInitUnfresh,
        initSidE, isSomeE, optFst, optSnd, natEq, nat2Eq, nat3Eq, sidEq, orE, eLet2,
        encEC, encKEM, u32OfNat,
        letV, bindV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eAny, eFind,
        act_liftGdhComp_size, act_liftGdhComp_litSize,
        act_gPrim_size, act_gPrim_litSize, gPrim, liftBase, getDBytes, optBytesEq, ddhQ,
        sBytes32, sDrKey96, qX25519, qX25519Base, qIsCanonical, qPow8, qSigVerify, qKemEncaps, qHkdfDerive96,
        litB, widenB, eqB, act_F_X25519_length, v,
        Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
        bits_0, bits_1, bits_2, bits_3, ↓reduceIte, Bool.false_eq_true,
        List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
      try simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
        _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
        ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
      have : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
      have : bits (K.min S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
      have : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
      have : bits (K.min S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
      omega
  have hStep : ∀ {Δ : List PT} {a b : PT} (v0 : Var Δ (.sum a b))
      (f1 : Var (a :: Δ) a → Comp pqxdhOps pqSigAndDdhIface (a :: Δ) (.prod keyIndRespTy gdh1KeyActiveStateTy))
      (f2 : Var (b :: Δ) b → Comp pqxdhOps pqSigAndDdhIface (b :: Δ) (.prod keyIndRespTy gdh1KeyActiveStateTy))
      (S1 S2 S3 L1 L2 L3 : Nat),
      ((f1 .zero).size ≤ S1 ∧ compLitSize (f1 .zero) ≤ L1) →
      ((f2 .zero).size ≤ S2 ∧ compLitSize (f2 .zero) ≤ L2) →
      S1 + S2 + 2 ≤ S3 → L1 + L2 ≤ L3 →
      (caseSumV (v v0) f1 f2).size ≤ S3 ∧
      compLitSize (caseSumV (v v0) f1 f2) ≤ L3 := by
    intro Δ a b v0 f1 f2 S1 S2 S3 L1 L2 L3 ⟨hs1, hl1⟩ ⟨hs2, hl2⟩ hs3 hl3
    simp only [caseSumV, v, Comp.size, Expr.size, compLitSize, exprLitSize]
    exact ⟨by omega, by omega⟩
  unfold gdh1KeyActiveHandle
  dsimp only
  refine hStep _ _ _ (5 * bits K + 250) (585 * bits K + 56600) _ 100 22400 _
    (hInitPrin .zero .zero) ?_ (by omega) (by omega)
  refine hStep _ _ _ (250 * bits K + 25100) (335 * bits K + 31400) _ 10100 12300 _
    (hCall _ _) ?_ (by omega) (by omega)
  refine hStep _ _ _ (10 * bits K + 800) (325 * bits K + 30500) _ 300 12000 _
    (hGenSpk .zero .zero) ?_ (by omega) (by omega)
  refine hStep _ _ _ (5 * bits K + 250) (320 * bits K + 30200) _ 100 11900 _
    (hGenOpk .zero .zero) ?_ (by omega) (by omega)
  refine hStep _ _ _ (35 * bits K + 2500) (285 * bits K + 27610) _ 900 11000 _
    (hInitAct true .zero .zero) ?_ (by omega) (by omega)
  exact hStep _ _ _ (35 * bits K + 2500) (250 * bits K + 25100) _ 900 10100 _
    (hInitAct false .zero .zero) (hCall _ _) (by omega) (by omega)

set_option linter.unusedSimpArgs false in
private theorem gdh1KeyActiveFinish_size_and_lit (S : Setup) (K : Nat) :
    (gdh1KeyActiveFinish S K).size ≤ 35 * bits K + 2000 ∧
    compLitSize (gdh1KeyActiveFinish S K) ≤ 500 := by
  refine ⟨?_, ?_⟩
  · simp (config := { maxSteps := 1000000 }) only [
      gdh1KeyActiveFinish, act_renameComp_size, act_liftGdhComp_size,
      gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
      initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
      smBase, smLog, smPows, paU, paV, paMode,
      stSpks, stSess, stResps,
      sbSpkSk, sbSpkPk, sePeerSpk, seHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdIkAPk,
      natEq, nat2Eq, orE, mulRight, optBytesEq,
      letV, bindV, caseOptV, findMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eMap,
      act_gPrim_size, gPrim, liftBase, ddhQ, qPow8, qX25519,
      litB, SignalPqxdh.Security.ReductionDsl.KeyInd.takeKB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.dropB, eqB,
      v, Comp.size, Expr.size,
      bits_0, bits_1, bits_2, bits_3, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
      ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr]
    have : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
    have : bits (K.min S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
    have : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
    have : bits (K.min S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
    omega
  · simp (config := { maxSteps := 1000000 }) only [
      gdh1KeyActiveFinish, act_renameComp_litSize, act_liftGdhComp_litSize,
      gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
      initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
      smBase, smLog, smPows, paU, paV, paMode,
      stSpks, stSess, stResps,
      sbSpkSk, sbSpkPk, sePeerSpk, seHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
      SignalPqxdh.Security.ReductionDsl.KeyInd.reHdr,
      SignalPqxdh.Security.ReductionDsl.KeyInd.hdIkAPk,
      natEq, nat2Eq, orE, mulRight, optBytesEq,
      letV, bindV, caseOptV, findMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eMap,
      act_gPrim_litSize, gPrim, liftBase, ddhQ, qPow8, qX25519,
      litB, SignalPqxdh.Security.ReductionDsl.KeyInd.takeKB,
      SignalPqxdh.Security.ReductionDsl.KeyInd.dropB, eqB,
      v, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_replicate, Nat.add_zero, Nat.zero_add]
    omega

set_option linter.unusedSimpArgs false in
private theorem fgKeyInd1KeyGapDhActiveDslProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).size ≤
      60000 + 330 * bits (stepCostBudget S b) ∧
    red1LitSize (fgKeyInd1KeyGapDhActiveDslProg S b) ≤ 24000 := by
  obtain ⟨hP_sz, hP_lit⟩ := initParams1KeyActiveC_size_and_lit S b
    (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
    (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
  obtain ⟨hH_sz, hH_lit⟩ := gdh1KeyActiveHandle_size_and_lit S b.q_total
  obtain ⟨hF_sz, hF_lit⟩ := gdh1KeyActiveFinish_size_and_lit S b.q_total
  have hInitSz : (fgKeyInd1KeyGapDhActiveDslProg S b).init.size ≤
      16 * bits (b.q_total + 1) + bits (activeSigBudget S b) + 500 := by
    dsimp only [fgKeyInd1KeyGapDhActiveDslProg]
    simp only [emptySimE, smMk, emptyStE, stMk,
      letV, bindV, act_liftGdhComp_size, act_gPrim_size, sBool, v,
      Comp.size, Expr.size, bits_0]
    omega
  have hInitLit : compLitSize (fgKeyInd1KeyGapDhActiveDslProg S b).init ≤ 100 := by
    dsimp only [fgKeyInd1KeyGapDhActiveDslProg]
    simp only [emptySimE, smMk, emptyStE, stMk,
      letV, bindV, act_liftGdhComp_litSize, act_gPrim_litSize, sBool, v,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  have h2q1 := two_mul_bits_q1_le_bits_stepCostBudget S b
  have hq_le_q1 : bits b.q_total ≤ bits (b.q_total + 1) := bits_mono (by omega)
  have hbSig : bits (activeSigBudget S b) ≤ bits (stepCostBudget S b) := by
    have hle : activeSigBudget S b ≤ b.q_total + 1 :=
      le_trans (Nat.min_le_left _ _) (by omega)
    exact le_trans (bits_mono hle) (by omega)
  refine ⟨?_, ?_⟩
  · change (fgKeyInd1KeyGapDhActiveDslProg S b).init.size +
      (gdh1KeyActiveHandle S b.q_total).size +
      (gdh1KeyActiveFinish S b.q_total).size ≤ _
    omega
  · change compLitSize (fgKeyInd1KeyGapDhActiveDslProg S b).init +
      compLitSize (gdh1KeyActiveHandle S b.q_total) +
      compLitSize (gdh1KeyActiveFinish S b.q_total) ≤ _
    omega

end GdhActiveSizeReducible


private theorem sigActiveAtomic_size_le_budget (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (stepCostBudget S b) := by
  have hLift := liftKeyInd1Stage_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe S
    (sigKeyInd1KeyActiveDslProg S b)
  obtain ⟨hSz, hLit⟩ := sigKeyInd1KeyActiveDslProg_size_le_stepCostBudget S b
  have h0 : 291402 ≤ _root_.ReductionDsl.reductionSizeBudget := by decide
  have h1 : 2850 * _root_.ReductionDsl.bits (stepCostBudget S b) ≤
      2 ^ 12 * _root_.ReductionDsl.bits (stepCostBudget S b) :=
    Nat.mul_le_mul_right _ (by decide)
  change (liftKeyInd1Stage tlSigDdhKeyInd S (sigKeyInd1KeyActiveDslProg S b)).size ≤ _
  omega

private theorem shcrActiveAtomic_size_le_budget (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (stepCostBudget S b) := by
  have hLift := liftKeyInd2Stage_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe S
    (shcrKeyInd1KeyActiveDslProg S b)
  obtain ⟨hSz, hLit⟩ := shcrKeyInd1KeyActiveDslProg_size_le_stepCostBudget S b
  have h0 : 335804 ≤ _root_.ReductionDsl.reductionSizeBudget := by decide
  have h1 : 2850 * _root_.ReductionDsl.bits (stepCostBudget S b) ≤
      2 ^ 12 * _root_.ReductionDsl.bits (stepCostBudget S b) :=
    Nat.mul_le_mul_right _ (by decide)
  change (liftKeyInd2Stage tlPrimKeyInd S (shcrKeyInd1KeyActiveDslProg S b)).size ≤ _
  omega

private theorem gdhActiveAtomic_size_le_budget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (stepCostBudget S b) := by
  have hLift := liftKeyInd1Stage_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe S
    (fgKeyInd1KeyGapDhActiveDslProg S b)
  obtain ⟨hSz, hLit⟩ := fgKeyInd1KeyGapDhActiveDslProg_size_le_stepCostBudget S b
  have h0 : 624402 ≤ _root_.ReductionDsl.reductionSizeBudget := by decide
  have h1 : 3300 * _root_.ReductionDsl.bits (stepCostBudget S b) ≤
      2 ^ 12 * _root_.ReductionDsl.bits (stepCostBudget S b) :=
    Nat.mul_le_mul_right _ (by decide)
  change (liftKeyInd1Stage tlSigDdhKeyInd S (fgKeyInd1KeyGapDhActiveDslProg S b)).size ≤ _
  omega


end ActiveSizeHelpers

private abbrev l1Q (S : Setup) := liftKeyInd1Stage_totalQueries_le tlSigDdhKeyInd S
private abbrev l2Q (S : Setup) := liftKeyInd2Stage_totalQueries_le tlPrimKeyInd S

theorem boundedAdv_isGameQuery (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : ∀ _ : Unit,
  (A.1.run).IsQueryBoundP (isGameQuery (G := keyIndSpec S)) b.q_total := by
  intro _; obtain ⟨_, _, _, h, _⟩ := A.2; convert h using 1; funext q; cases q
  · exact propext ⟨False.elim, Bool.noConfusion⟩
  · exact propext ⟨fun _ => rfl, fun _ => trivial⟩

theorem pqxdhKeyInd1KeyActiveCostedSims_simBounds_impl (S : Setup) :
    KeyIndReductionQueryBounds S (pqxdhKeyInd1KeyActiveCostedSims S).eval where
  sig_bounded := fun b A =>
    ⟨fun pk => by dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyActiveCostedSims]; rw [sigActiveAtomic_eval_eq]; exact sigKeyInd1KeyActiveDslProg_sigBounded S b _ pk,
     fun pk => by dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyActiveCostedSims]; rw [sigActiveAtomic_eval_eq]; exact sigKeyInd1KeyActiveDslProg_ddhBounded_gdhQueryBudget S b A pk,
     fun pk => by dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyActiveCostedSims]; rw [sigActiveAtomic_eval_eq]; exact sigKeyInd1KeyActiveDslProg_primBounded_gdhPrimQueryBudget S b A pk⟩
  shcr_bounded := fun b A => by
    let P := shcrKeyInd1KeyActiveDslProg S b
    refine kemShCrAdv_bounded_of_state_retract (A := shcrKeyInd1KeyActiveDslAdv S b A) rfl (embedMid (π := P.π) (σ :=
      P.σ) (ch := B 1568)) (projMid (π := P.π) (σ := P.σ) (ch := B 1568)) (fun pk sk => liftKeyInd2Stage_eval1
      tlPrimKeyInd S P (shcrActive_init_unsupported S b) (shcrActive_handlePre_unsupported S b)
      (shcrActive_chDone_unsupported S b) (fun _ => A.1.run) (pk, sk) b.q_total false) (fun st' ss ct => ?_)
      (shcrKeyInd1KeyActiveDslAdv_bounded S b A)
    have hId : embedVal (B 1568) = id := rfl; have hRet := embedMid_projMid (π := P.π) (σ := P.σ) (ch := B 1568) st'
    have h := liftKeyInd2Stage_eval2 tlPrimKeyInd S P (shcrActive_resume_unsupported S b)
      (shcrActive_handlePost_unsupported S b) (shcrActive_finish_unsupported S b) (projMid (π := P.π) (σ := P.σ) (ch :=
      B 1568) st') (ss, ct) b.q_total false
    rw [hRet, hId, id_map] at h; exact h
  gdh_bounded := fun b A =>
    ⟨fun U V => by dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyActiveCostedSims]; rw [gdhActiveAtomic_eval_eq]; exact fgKeyInd1KeyGapDhActiveDslProg_ddhBounded_gdhQueryBudget S b (fgKeyInd1KeyGapDhActiveDslProg_ddhQueries_le S b) A U V,
     fun U V => by dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyActiveCostedSims]; rw [gdhActiveAtomic_eval_eq]; exact fgKeyInd1KeyGapDhActiveDslProg_sigBounded S b _ U V,
     fun U V => by dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyActiveCostedSims]; rw [gdhActiveAtomic_eval_eq]; exact fgKeyInd1KeyGapDhActiveDslProg_primBounded_gdhPrimQueryBudget S b A U V⟩

/-- Semantic query bounds for `(pqxdhKeyInd1KeyActiveCostedSims S).eval`. -/
theorem pqxdhKeyInd1KeyActiveCostedSims_simBounds (S : Setup) : KeyIndReductionQueryBounds S
  (pqxdhKeyInd1KeyActiveCostedSims S).eval := pqxdhKeyInd1KeyActiveCostedSims_simBounds_impl S

end AtomicAssembly
end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveBounds
