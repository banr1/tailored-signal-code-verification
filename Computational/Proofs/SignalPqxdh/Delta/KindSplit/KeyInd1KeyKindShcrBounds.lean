/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Specifications.Pqxdh.Security.Headline
import Computational.Proofs.ReductionDsl.AtomicSizeHonest
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost

/-!
# Cost, Query, and Block Bounds for `shcrKeyInd1KeyKindAtomicProg`

Proves total and per-query-kind step-cost bounds, syntactic primitive-query bounds, `.Bounded`
adversary query bounds, and two-stage block-size bounds (`GRed2BlockBounded`) for
`shcrKeyInd1KeyKindAtomicProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrBounds

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.SignalPqxdh (Setup QueryBudget BoundedAdv KeyIndAdversary KeyIndQuery keyIndSpec isPrimQuery₀ activeSpkCount activeSendCount)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit primQueryBudget GRed2BlockBounded keyIndQueryKind keyIndKindCounts primIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.ReductionDsl (Ty Var Expr Comp Iface TwoStageCostedReduction Mid pqAtomicSig pqAtomicOps pqAtomicSamplers pqPrimIface pqKeyIndCodec B PB drKeyT bits reductionSizeBudget)
open _root_.Computational.Proofs.ReductionDsl.AtomicSizeHonest (pqAtomicSamplers_sizeHonest)
open _root_.Computational.Proofs.ReductionDsl.KindedDispatch (twoStageCostBoundedByKind_fin2_of_armCosts)
open _root_.Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mul_le)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (TagLift tlPrimKeyInd tlPrimKeyInd_primW tlPrimKeyInd_sizeLe embedTy finSidToNatExpr exprRename compRename mapExpr mapComp exprRename_cost compRename_cost exprRename_size compRename_size pqxdhOps_opSize compLitSize exprLitSize pqOpLitSize mapComp_cost_eleven_mul_le mapComp_queries_le mapComp_size_le one_le_pqAtomicSamplers_sCost one_le_pqPrimIface_qCost gred2BlockBounded_atomic_of_totalCost_le)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (aop avlTy avlEmptyE avlHeightCap avlSearchResTy avlSearchB192C avlInsertAtPathC sampleDrKey96AtomicC samplePbytes32C dfltB192E dfltDrKeyE)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (samplePbytes32C_size_eq avlSearchB192C_size_le avlInsertAtPathC_size_le)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (Ext PT accQTy initQTy shcrStTy pauseTy keyIndStateTy SCS letV bindV caseOptV caseSumV findMV anyMV v eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap stSecb stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stRo stAdv stMk stUpd peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted peMk peUpd sbSpkSk sbSpkPk sbSpkSig sbPqspkSk sbPqspkPk sbPqspkSig sbRevealed sbMk sbUpd oeOpkSk oeOpkPk oeConsumed oeMk oeUpd seSid seHonestPeer sePeerIk sePeerSpk sePeerOpk sePeerPqspk seSpkHon seOpkHon sePqspkHon seEkASk seFresh seDrReal seDrRand seHdr seTested seRevealed seMk seUpd reSid reRespIk reSpk reOpk rePqspk reHdr reSenderHonest reDrReal reDrRand reTested reRevealed reMk reUpd buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig buMk hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt hdMk rNone rInitPrin rPk rCorr rBundle rHdr rInitUnfresh rAccFresh rDrKey rSpkSk rs scBase scTB scTPk scTSk scCnt scIR scRR scSIdx scChosen scMk scUpd emptyStE initGuardE initSidE shcrFinE isNoneRespE isSomeE getDBytes optFst optSnd orE natEq nat2Eq nat3Eq optBytesEq optU32Eq sidEq kyberEq kyberCheckE buildSecretsE guardE nonZero32 qK qJ qO qHdr qKJO aiIkSk aiSpkSk aiOpkSk aiPqSk aiReplay aiHdr litB catB consB widenB lenB eqB u32OfNat eqU32 encEC encKEM sBool sBytes32 sRandom64 sDrKey96 sIndex qX25519 qX25519Base qIsCanonical qPow8 qSigPkGen qSigSign qSigVerify qKemKeyGen qKemEncaps qKemDecaps qHkdfDerive96 findHonestC isAdvRegC isGameSpkC isGameOpkC koskBundleOkC koskSenderOkC resolveSigPkC honestPeerC checkProvC partnerC recordRespC acceptKeysC preCheckC checkSigsC tryPauseC shcrExtractC onBase initPrin1KeyB initPrinB corruptB genSpkB shcrGenSpkB genOpkB testB revealB revealDhB registerB revealSpkB primW primWS bits_0 bits_1 bits_32 bits_le_add_one bits_eq_log2_succ cost_v cost_sBool cost_sIndex onBase_cost initPrin1KeyB_cost_le initPrinB_cost corruptB_cost genSpkB_cost shcrGenSpkB_cost genOpkB_cost testB_cost revealB_cost revealDhB_true_cost registerB_cost revealSpkB_cost tryPauseC_true_cost tryPauseC_false_cost queries_sBool queries_sBytes32 queries_sRandom64 queries_sDrKey96 queries_sIndex queries_qX25519 queries_qX25519Base queries_qPow8 queries_qSigSign queries_qSigVerify queries_qKemEncaps queries_qKemDecaps findHonestC_queries koskSenderOkC_queries honestPeerC_queries checkProvC_queries partnerC_queries recordRespC_queries acceptKeysC_queries preCheckC_queries checkSigsC_queries onBase_queries initPrinB_queries corruptB_queries genSpkB_queries genOpkB_queries testB_queries revealB_queries revealDhB_queries registerB_queries revealSpkB_queries shcrExtractC_queries)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (KeyIndCoreFuels keyIndCoreFuels keyIndSentinel keyIndSentinel_le roAvlTy roListAtomicTy shcrKindStTy emptyRoAvlE roShadowQueryC shcrGetRoE shcrSetRoRespC initFinishPreRoC initFinishPostRoC shcrInitMidTy shcrAccMidTy shcrInitiatePreRoC shcrInitiatePostRoC coreAcceptPreRoC shcrAcceptPreRoC shcrAcceptPostRoC shcrResumePreRoC shcrResumePostRoC shcrInitPrin1KeyLeg shcrInitPrin2KeyLeg shcrCorruptLeg shcrGenSpkLeg shcrActiveGenSpkLeg shcrGenOpkLeg shcrTestLeg shcrRevDhLeg shcrRevSessLeg shcrRegKeyLeg shcrRevSpkLeg shcrChDoneLeg shcrExtractLeg atomicRNoneE finPairToNatE finTripleToNatE initPayToNatE accPayToNatE wkRen1 dispatchKeyIndQ ren1 ren2 ren3 ren4 ren5 ren6 wkTop3 runAt2 runAt3 runAt4 runAt5 runAt6 shcrRoListAtomicE shcrLiftLegArmK shcrRoArmK shcrInitArmPostK shcrInitArmPreK shcrAccArmPostK shcrKindHandlePreC shcrKindHandlePostC shcrKindChDoneC shcrKindResumeC shcrKindFinishC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost (roShadowQueryC_queries_zero roShadowQueryC_cost_le shcrInitiatePreRoC_cost_le shcrInitiatePostRoC_cost_le shcrAcceptPreRoC_cost_le shcrAcceptPostRoC_cost_le shcrActiveGenSpkLeg_cost_le shcrRoArmK_cost_le shcrKindHandlePreC_costAt_ro_le shcrKindHandlePostC_costAt_ro_le shcrOnlineArmBudget shcrKindHandlePreC_costAt_online_le shcrKindHandlePostC_costAt_online_le shcrKindResumeC_cost_le shcrKindChDoneC_cost_le shcrKindFinishC_cost_le)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (shcr1KeyKindBaseInit shcr1KeyKindInitC shcr1KeyKindHandlePreC shcr1KeyKindResumeC shcr1KeyKindHandlePostC shcrKeyInd1KeyKindAtomicProg pqxdhKeyInd1KeyKindCostedSims)

private theorem bits_le_log2_add_one (n : ℕ) : bits n ≤ Nat.log 2 n + 1 := by rw [bits_eq_log2_succ]

private theorem bits_keyIndSentinel_le_split (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b; bits (keyIndSentinel S b) ≤ Nat.log 2 S.N_dh + f.M_on + 4 := by
  intro f
  have hSent : keyIndSentinel S b ≤ S.N_dh + f.M_on + 1 := Nat.min_le_right _ _
  have hProd : S.N_dh + f.M_on + 1 ≤ max 1 S.N_dh * (f.M_on + 2) := by
    have h1 : 1 ≤ max 1 S.N_dh := Nat.le_max_left _ _; have h2 : S.N_dh ≤ max 1 S.N_dh := Nat.le_max_right _ _; nlinarith
  have hMono := _root_.ReductionDsl.bits_mono (Nat.le_trans hSent hProd)
  have hMul := bits_mul_le (max 1 S.N_dh) (f.M_on + 2)
  have hMaxBits : bits (max 1 S.N_dh) ≤ Nat.log 2 S.N_dh + 1 := by
    by_cases h0 : S.N_dh = 0
    · rw [h0]; decide
    · rw [Nat.max_eq_right (Nat.pos_of_ne_zero h0), bits_eq_log2_succ]
  have hMonBits : bits (f.M_on + 2) ≤ f.M_on + 3 := bits_le_add_one (f.M_on + 2); omega

private theorem bits_keyIndSentinel_le_total (S : Setup) (b : QueryBudget) :
    bits (keyIndSentinel S b) ≤ b.q_total + 2 := by
  have h := _root_.ReductionDsl.bits_mono (keyIndSentinel_le S b)
  have hb := bits_le_add_one (b.q_total + 1); omega

private theorem bits_activeSpkCount_le (S : Setup) (q_on : ℕ) :
    bits (activeSpkCount S q_on) ≤ Nat.log 2 S.N_dh + 1 :=
  Nat.le_trans (_root_.ReductionDsl.bits_mono (by unfold activeSpkCount Setup.N_dh; omega)) (bits_le_log2_add_one S.N_dh)

private theorem bits_activeSendCount_le (S : Setup) (q_on : ℕ) :
    bits (activeSendCount S q_on) ≤ Nat.log 2 S.N_dh + 1 :=
  Nat.le_trans (_root_.ReductionDsl.bits_mono (by unfold activeSendCount Setup.N_dh; omega)) (bits_le_log2_add_one S.N_dh)

private theorem emptyRoAvlE_cost_le {Γ : List (Ty pqAtomicSig)} : (emptyRoAvlE (Γ := Γ)).cost ≤ 320 := by
  simp [emptyRoAvlE, avlEmptyE, _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlMkE,
    dfltB192E, dfltDrKeyE, aop, Expr.cost, bits_0,
    pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost]

private theorem shcr1KeyKindBaseInit_cost_le_split (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b; (shcr1KeyKindBaseInit S b).cost ≤ 60 + 2 * Nat.log 2 S.N_dh + f.M_on := by
  intro f
  have hSent : bits (keyIndSentinel S b) ≤ Nat.log 2 S.N_dh + f.M_on + 4 := bits_keyIndSentinel_le_split S b
  have hSpk := bits_activeSpkCount_le S b.q_on; have hSend := bits_activeSendCount_le S b.q_on
  dsimp only [shcr1KeyKindBaseInit]; split
  · simp only [bindV, emptyStE, stMk, scMk, cost_sBool, cost_v, Comp.cost, Expr.cost, bits_0]; omega
  · simp only [bindV, emptyStE, stMk, scMk, cost_sIndex, cost_sBool, cost_v, Comp.cost, Expr.cost, bits_0]; omega

private theorem shcr1KeyKindBaseInit_cost_le_total (S : Setup) (b : QueryBudget) :
    (shcr1KeyKindBaseInit S b).cost ≤ 60 + 2 * Nat.log 2 S.N_dh + b.q_total := by
  have hSent := bits_keyIndSentinel_le_total S b
  have hSpk := bits_activeSpkCount_le S b.q_on; have hSend := bits_activeSendCount_le S b.q_on
  dsimp only [shcr1KeyKindBaseInit]; split
  · simp only [bindV, emptyStE, stMk, scMk, cost_sBool, cost_v, Comp.cost, Expr.cost, bits_0]; omega
  · simp only [bindV, emptyStE, stMk, scMk, cost_sIndex, cost_sBool, cost_v, Comp.cost, Expr.cost, bits_0]; omega

private theorem shcr1KeyKindInitC_cost_le_split (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b; (shcr1KeyKindInitC S b).cost ≤ 1000 + 22 * Nat.log 2 S.N_dh + 11 * f.M_on := by
  intro f
  have hBase : (shcr1KeyKindBaseInit S b).cost ≤ 60 + 2 * Nat.log 2 S.N_dh + f.M_on := shcr1KeyKindBaseInit_cost_le_split S b
  have hMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcr1KeyKindBaseInit S b)
  have hAvl := emptyRoAvlE_cost_le (Γ := [.prod .unit (embedTy shcrStTy), .prod (PB 1568) (PB 3168)])
  simp only [shcr1KeyKindInitC, Comp.cost, Expr.cost] at hAvl ⊢; omega

private theorem shcr1KeyKindInitC_cost_le_total (S : Setup) (b : QueryBudget) :
    (shcr1KeyKindInitC S b).cost ≤ 1000 + 22 * Nat.log 2 S.N_dh + 11 * b.q_total := by
  have hBase := shcr1KeyKindBaseInit_cost_le_total S b
  have hMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcr1KeyKindBaseInit S b)
  have hAvl := emptyRoAvlE_cost_le (Γ := [.prod .unit (embedTy shcrStTy), .prod (PB 1568) (PB 3168)])
  simp only [shcr1KeyKindInitC, Comp.cost, Expr.cost] at hAvl ⊢; omega

private theorem caseSum_cost_step {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig} (e : Expr pqAtomicOps Γ (.sum A B))
    (c1 : Comp pqAtomicOps I (A :: Γ) R) (c2 : Comp pqAtomicOps I (B :: Γ) R)
    {ce M K : ℕ} (he : e.cost ≤ ce) (h1 : c1.cost ≤ M) (h2 : c2.cost ≤ M) (hK : M + ce + 1 ≤ K) :
    (Comp.caseSum e c1 c2).cost ≤ K := by
  simp only [Comp.cost]; have hm : max c1.cost c2.cost ≤ M := Nat.max_le.mpr ⟨h1, h2⟩; omega

private theorem dispatchKeyIndQ_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (S : Setup) {Γ : List (Ty pqAtomicSig)} {R : Ty pqAtomicSig} (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q)) (M : ℕ)
    (a1 a2 : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) R)
    (a3 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R)
    (a4 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: Γ) R)
    (a5 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (a6 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_no_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (a7 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.prod (.base (.fin S.N_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (a8 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.prod (.base (.fin S.N_no_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (a9 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (a10 : Comp pqAtomicOps I (PB 192 :: Γ) R) (a11 : Comp pqAtomicOps I (.unit :: Γ) R)
    (a12 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (a13 : Comp pqAtomicOps I (PB 32 :: Γ) R)
    (a14 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R)
    (hq : qE.cost ≤ 2) (h1 : a1.cost ≤ M) (h2 : a2.cost ≤ M) (h3 : a3.cost ≤ M) (h4 : a4.cost ≤ M)
    (h5 : a5.cost ≤ M) (h6 : a6.cost ≤ M) (h7 : a7.cost ≤ M) (h8 : a8.cost ≤ M)
    (h9 : a9.cost ≤ M) (h10 : a10.cost ≤ M) (h11 : a11.cost ≤ M) (h12 : a12.cost ≤ M)
    (h13 : a13.cost ≤ M) (h14 : a14.cost ≤ M) :
    (dispatchKeyIndQ S qE a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14).cost ≤ M + 28 := by
  dsimp only [dispatchKeyIndQ]
  refine caseSum_cost_step _ _ _ hq (M := M + 24) (by omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 22) (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 20) (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 18) (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 16) (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 14) (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 12) (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 10) (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 8)  (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 6)  (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 4)  (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  refine caseSum_cost_step _ _ _ (ce := 1) (M := M + 2)  (by simp [Expr.v0, Expr.cost]) (by simp only [compRename_cost]; omega) ?_ (by omega)
  exact caseSum_cost_step _ _ _ (ce := 1) (M := M) (by simp [Expr.v0, Expr.cost])
    (by simp only [compRename_cost]; omega) (by simp only [compRename_cost]; omega) (by omega)

private theorem runAt2_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (c : Comp pqAtomicOps I [A, B] R) :
    (runAt2 aE bE c).cost = c.cost + aE.cost + bE.cost + 4 := by
  simp only [runAt2, Comp.cost, exprRename_cost, compRename_cost]; omega

private theorem runAt4_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (m : Comp pqAtomicOps I [A, B, C, D] R) :
    (runAt4 aE bE cE dE m).cost = m.cost + aE.cost + bE.cost + cE.cost + dE.cost + 8 := by
  simp only [runAt4, Comp.cost, exprRename_cost, compRename_cost]; omega

private theorem runAt5_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (m : Comp pqAtomicOps I [A, B, C, D, E] R) :
    (runAt5 aE bE cE dE eE m).cost = m.cost + aE.cost + bE.cost + cE.cost + dE.cost + eE.cost + 10 := by
  simp only [runAt5, Comp.cost, exprRename_cost, compRename_cost]; omega

private theorem wrapInl_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B : Ty pqAtomicSig} (c : Comp pqAtomicOps I Γ A) :
    (Comp.bind c (.ret (.inl .v0 : Expr pqAtomicOps (A :: Γ) (.sum A B)))).cost = c.cost + 4 := by
  simp only [Comp.cost, Expr.cost, Expr.v0]

private theorem shcrRoListAtomicE_cost_le {Γ : List (Ty pqAtomicSig)} (sE : Expr pqAtomicOps Γ (embedTy shcrStTy)) :
    (shcrRoListAtomicE sE).cost ≤ sE.cost + 20 := by
  simp only [shcrRoListAtomicE, shcrGetRoE, stRo, scBase, exprRename_cost, mapExpr, Expr.cost]; omega

private theorem shcrLiftLegArmK_cost_le_of (S : Setup) (K_on : ℕ) {A : Ty pqAtomicSig} {P : Ty pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (leg : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, P] SCS)
    (hPay : payE.cost ≤ 40) (hLeg : leg.cost ≤ 8900 + 350 * K_on) :
    (shcrLiftLegArmK S payE leg).cost ≤ 19000 + 750 * K_on := by
  have hMap := mapComp_cost_eleven_mul_le tlPrimKeyInd leg
  simp only [shcrLiftLegArmK, runAt2_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega

private theorem finSidToNatExpr_v0_cost_le (S : Setup) {Γ : List (Ty pqAtomicSig)} :
    (finSidToNatExpr S (.v0 : Expr pqAtomicOps (_root_.ReductionDsl.sidT S :: Γ) _)).cost ≤ 40 := by
  simp only [finSidToNatExpr, Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
    _root_.ReductionDsl.AtomicPureOp.cost]; norm_num [Nat.max_def]

private theorem shcrInitArmPostK_cost_le (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    (shcrInitArmPostK S K_on capRo N_s opk).cost ≤
      29800 + 4000 * min K_on S.N_dh + 15400 * min K_on S.N_sess_tot + 7250 * K_on + (4420 * bits capRo + 1400) := by
  have hPre := shcrInitiatePreRoC_cost_le S K_on opk
  have hPreMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrInitiatePreRoC S K_on opk)
  have hPost := shcrInitiatePostRoC_cost_le S K_on
  have hPostMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrInitiatePostRoC S K_on)
  let G0 := embedTy shcrInitMidTy :: embedTy (.sum SCS shcrInitMidTy) ::
    .prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
    shcrKindStTy :: (pqKeyIndCodec S).Q :: []
  have hRo := roShadowQueryC_cost_le tlPrimKeyInd capRo (Γ := G0) (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)
  have hRoList := shcrRoListAtomicE_cost_le (Γ := G0) (.fst .v3)
  simp only [shcrInitArmPostK, initPayToNatE, aop, runAt2_cost, runAt4_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v3, Expr.v4, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
    _root_.ReductionDsl.AtomicPureOp.cost] at hRo hRoList ⊢; omega

private theorem shcrInitArmPreK_cost_le (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    (shcrInitArmPreK S K_on capRo N_s opk).cost ≤
      37900 + 5750 * min K_on S.N_dh + 15400 * min K_on S.N_sess_tot + 7800 * K_on + (4420 * bits capRo + 1400) := by
  let tp := tryPauseC S K_on opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy]) .zero .zero
  have hTp : tp.cost = 3843 + min K_on S.N_dh * 824 + K_on * 257 := by
    cases opk; exact tryPauseC_false_cost S K_on .zero .zero; exact tryPauseC_true_cost S K_on .zero .zero
  have hTpMap := mapComp_cost_eleven_mul_le tlPrimKeyInd tp
  have hPost := shcrInitArmPostK_cost_le S K_on capRo N_s opk
  dsimp only [tp] at hTp hTpMap
  simp only [shcrInitArmPreK, initPayToNatE, aop, runAt2_cost, compRename_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v3, pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost]; omega

private theorem shcrAccArmPostK_cost_le (S : Setup) (K_on capRo N_o : ℕ) (opk : Bool) :
    (shcrAccArmPostK S K_on capRo N_o opk).cost ≤
      40700 + 16700 * min K_on S.N_dh + 960 * K_on + (4420 * bits capRo + 1400) := by
  have hPre := shcrAcceptPreRoC_cost_le S K_on opk
  have hPreMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrAcceptPreRoC S K_on opk)
  have hPost := shcrAcceptPostRoC_cost_le S K_on opk
  have hPostMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrAcceptPostRoC S K_on opk)
  let G0 := embedTy shcrAccMidTy :: embedTy (.opt shcrAccMidTy) ::
    .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.prod (.base (.fin N_o)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
    shcrKindStTy :: (pqKeyIndCodec S).Q :: []
  have hRo := roShadowQueryC_cost_le tlPrimKeyInd capRo (Γ := G0) (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)
  have hRoList := shcrRoListAtomicE_cost_le (Γ := G0) (.fst .v3)
  simp only [shcrAccArmPostK, accPayToNatE, atomicRNoneE, aop, runAt2_cost, runAt5_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
    _root_.ReductionDsl.AtomicPureOp.cost] at hRo hRoList ⊢; omega

private theorem nonSessionLegs_1Key_cost_le (S : Setup) (K : ℕ) :
    (shcrInitPrin1KeyLeg K).cost ≤ 8900 + 350 * K ∧ (shcrCorruptLeg K).cost ≤ 8900 + 350 * K ∧
    (shcrActiveGenSpkLeg S K).cost ≤ 8900 + 350 * K ∧ (shcrGenOpkLeg K).cost ≤ 8900 + 350 * K ∧
    (shcrTestLeg K).cost ≤ 8900 + 350 * K ∧ (shcrRevDhLeg K).cost ≤ 8900 + 350 * K ∧
    (shcrRevSessLeg K).cost ≤ 8900 + 350 * K ∧ shcrRegKeyLeg.cost ≤ 8900 + 350 * K ∧
    (shcrRevSpkLeg K).cost ≤ 8900 + 350 * K := by
  have h1k := initPrin1KeyB_cost_le K (Γ₁ := [keyIndStateTy, shcrStTy, .nat])
    (Γ₂ := [keyIndStateTy, shcrStTy, .nat]) (Δ := [keyIndStateTy, shcrStTy, .nat]) .zero (.succ (.succ .zero))
  have hGenAct := shcrActiveGenSpkLeg_cost_le S K
  exact ⟨by simp only [shcrInitPrin1KeyLeg, onBase_cost, initPrinB_cost] at h1k ⊢; omega,
    by simp only [shcrCorruptLeg, onBase_cost, corruptB_cost]; omega, by omega,
    by simp only [shcrGenOpkLeg, onBase_cost, genOpkB_cost]; omega,
    by simp only [shcrTestLeg, onBase_cost, testB_cost]; omega,
    by simp only [shcrRevDhLeg, onBase_cost, revealDhB_true_cost]; omega,
    by simp only [shcrRevSessLeg, onBase_cost, revealB_cost]; omega,
    by simp only [shcrRegKeyLeg, onBase_cost, registerB_cost]; omega,
    by simp only [shcrRevSpkLeg, onBase_cost, revealSpkB_cost]; omega⟩

private theorem shcrNonSessionArmsK_cost_le (S : Setup) (K : ℕ) :
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrInitPrin1KeyLeg K)).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg K)).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrActiveGenSpkLeg S K)).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat)) (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg K)).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrTestLeg K)).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (A := .unit) (P := .unit) .unit (shcrRevDhLeg K)).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrRevSessLeg K)).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg).cost ≤ 19000 + 750 * K ∧
    (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg K)).cost ≤ 19000 + 750 * K := by
  rcases nonSessionLegs_1Key_cost_le S K with ⟨hL1, hL2, hL3, hL4, hL9, hL11, hL12, hL13, hL14⟩
  have hSid := finSidToNatExpr_v0_cost_le S (Γ := [shcrKindStTy, (pqKeyIndCodec S).Q])
  have hPayFin1 : (aop (.finVal S.N_id) (.v0 : Expr pqAtomicOps [.base (.fin S.N_id), shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayPair : (finPairToNatE S.N_id S.N_recv (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)), shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [finPairToNatE, aop, Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayTriple : (finTripleToNatE S.N_id S.N_recv S.N_opk (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))), shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [finTripleToNatE, aop, Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayUnit : (.unit : Expr pqAtomicOps [.unit, shcrKindStTy, (pqKeyIndCodec S).Q] .unit).cost ≤ 40 := by simp [Expr.cost]
  have hPayV0 : (.v0 : Expr pqAtomicOps [PB 32, shcrKindStTy, (pqKeyIndCodec S).Q] (PB 32)).cost ≤ 40 := by simp [Expr.cost, Expr.v0]
  exact ⟨shcrLiftLegArmK_cost_le_of S K _ _ hPayFin1 hL1, shcrLiftLegArmK_cost_le_of S K _ _ hPayFin1 hL2,
    shcrLiftLegArmK_cost_le_of S K _ _ hPayPair hL3, shcrLiftLegArmK_cost_le_of S K _ _ hPayTriple hL4,
    shcrLiftLegArmK_cost_le_of S K _ _ hSid hL9, shcrLiftLegArmK_cost_le_of S K _ _ hPayUnit hL11,
    shcrLiftLegArmK_cost_le_of S K _ _ hSid hL12, shcrLiftLegArmK_cost_le_of S K _ _ hPayV0 hL13,
    shcrLiftLegArmK_cost_le_of S K _ _ hPayPair hL14⟩

private theorem shcr1KeyKindHandlePreC_cost_le (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b
    (shcr1KeyKindHandlePreC S b).cost + (pqKeyIndCodec S).codecCost ≤ shcrOnlineArmBudget f := by
  intro f
  have hMdh : min f.M_on S.N_dh = f.M_dh := rfl; have hMsess : min f.M_on S.N_sess_tot = f.M_sess := rfl
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  rcases shcrNonSessionArmsK_cost_le S f.M_on with ⟨hA1, hA2, hA3, hA4, hA9, hA11, hA12, hA13, hA14⟩
  have hA5 := shcrInitArmPreK_cost_le S f.M_on f.roCap S.N_send_opk true
  have hA6 := shcrInitArmPreK_cost_le S f.M_on f.roCap S.N_send_no_opk false
  have hA7 := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_opk true
  have hA8 := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_no_opk false
  have hA10 := shcrRoArmK_cost_le S f.roCap
  rw [hMdh] at hA5 hA6 hA7 hA8; rw [hMsess] at hA5 hA6
  let M := shcrOnlineArmBudget f - 92
  have hq : (.v1 : Expr pqAtomicOps [shcrKindStTy, (pqKeyIndCodec S).Q] ((pqKeyIndCodec S).Q)).cost ≤ 2 := by simp [Expr.v1, Expr.cost]
  have hD := dispatchKeyIndQ_cost_le S .v1 M
    (.bind (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrInitPrin1KeyLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrActiveGenSpkLeg S f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat)) (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg f.M_on)) (.ret (.inl .v0)))
    (shcrInitArmPreK S f.M_on f.roCap S.N_send_opk true) (shcrInitArmPreK S f.M_on f.roCap S.N_send_no_opk false)
    (.bind (shcrAccArmPostK S f.M_on f.roCap S.N_opk true) (.ret (.inl .v0)))
    (.bind (shcrAccArmPostK S f.M_on f.roCap S.N_no_opk false) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrTestLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrRoArmK S f.roCap) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrRevSessLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg f.M_on)) (.ret (.inl .v0)))
    hq (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega) (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega) (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega)
    (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega) (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega) (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega) (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega) (by simp only [wrapInl_cost, M, shcrOnlineArmBudget]; omega)
  rw [hCodec]; dsimp only [shcr1KeyKindHandlePreC, shcrKindHandlePreC]; dsimp only [f] at hD
  simp only [↓reduceIte, M, shcrOnlineArmBudget] at hD ⊢; omega

private theorem shcr1KeyKindHandlePostC_cost_le (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b
    (shcr1KeyKindHandlePostC S b).cost + (pqKeyIndCodec S).codecCost ≤ shcrOnlineArmBudget f := by
  intro f
  have hMdh : min f.M_on S.N_dh = f.M_dh := rfl; have hMsess : min f.M_on S.N_sess_tot = f.M_sess := rfl
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  rcases shcrNonSessionArmsK_cost_le S f.M_on with ⟨hA1, hA2, hA3, hA4, hA9, hA11, hA12, hA13, hA14⟩
  have hA5 := shcrInitArmPostK_cost_le S f.M_on f.roCap S.N_send_opk true
  have hA6 := shcrInitArmPostK_cost_le S f.M_on f.roCap S.N_send_no_opk false
  have hA7 := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_opk true
  have hA8 := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_no_opk false
  have hA10 := shcrRoArmK_cost_le S f.roCap
  rw [hMdh] at hA5 hA6 hA7 hA8; rw [hMsess] at hA5 hA6
  let M := shcrOnlineArmBudget f - 92
  have hq : (.v1 : Expr pqAtomicOps [shcrKindStTy, (pqKeyIndCodec S).Q] ((pqKeyIndCodec S).Q)).cost ≤ 2 := by simp [Expr.v1, Expr.cost]
  have hD := dispatchKeyIndQ_cost_le S .v1 M
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrInitPrin1KeyLeg f.M_on))
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg f.M_on))
    (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrActiveGenSpkLeg S f.M_on))
    (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat)) (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg f.M_on))
    (shcrInitArmPostK S f.M_on f.roCap S.N_send_opk true) (shcrInitArmPostK S f.M_on f.roCap S.N_send_no_opk false)
    (shcrAccArmPostK S f.M_on f.roCap S.N_opk true) (shcrAccArmPostK S f.M_on f.roCap S.N_no_opk false)
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrTestLeg f.M_on))
    (shcrRoArmK S f.roCap) (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg f.M_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrRevSessLeg f.M_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg)
    (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg f.M_on))
    hq (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
    (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
    (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
    (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
    (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
    (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
    (by simp only [M, shcrOnlineArmBudget]; omega) (by simp only [M, shcrOnlineArmBudget]; omega)
  rw [hCodec]; dsimp only [shcr1KeyKindHandlePostC, shcrKindHandlePostC]; dsimp only [f] at hD
  simp only [↓reduceIte, M, shcrOnlineArmBudget] at hD ⊢; omega

private theorem costByKind_join_le
    {cInit k0 uC c0 cCod k1 c1 cDone cRes cFin BInit B0 B1 BFin f_Mon f_Moff : ℕ}
    (hk0 : k0 = f_Mon) (hk1 : k1 = f_Moff) (hMax0 : max uC (c0 + cCod) ≤ B0) (hMax1 : max uC (c1 + cCod) ≤ B1)
    (hi : cInit ≤ BInit) (hd : cDone ≤ B0) (hr : cRes ≤ B0) (hf : cFin ≤ BFin) :
    cInit + k0 * max uC (c0 + cCod) + k1 * max uC (c1 + cCod) + max cDone cRes + cFin ≤
      BInit + (f_Mon + 1) * B0 + f_Moff * B1 + BFin := by
  subst hk0; subst hk1
  have hmCR : max cDone cRes ≤ B0 := Nat.max_le.mpr ⟨hd, hr⟩
  have hMul0 := Nat.mul_le_mul_left k0 hMax0; have hMul1 := Nat.mul_le_mul_left k1 hMax1; nlinarith

/-- Per-query-kind step-cost bound for `shcrKeyInd1KeyKindAtomicProg`. -/
theorem shcrKeyInd1KeyKindAtomicProg_costByKind (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyKindAtomicProg S b).CostBoundedByKind keyIndQueryKind (keyIndKindCounts b)
      (stepCostBudgetSplit S b b.q_ro) := by
  let f := keyIndCoreFuels S b; let c0 := shcrOnlineArmBudget f - 64; let c1 := 4420 * bits f.roCap + 1786
  refine twoStageCostBoundedByKind_fin2_of_armCosts (shcrKeyInd1KeyKindAtomicProg S b)
    keyIndQueryKind (keyIndKindCounts b) (c0 := c0) (c1 := c1)
    (fun st q hq => ?_) (fun st q hq => ?_) (fun st q hq => ?_) (fun st q hq => ?_) ?_
  · have h := shcrKindHandlePreC_costAt_online_le true S b st q hq
    dsimp only [shcrKeyInd1KeyKindAtomicProg, shcr1KeyKindHandlePreC, c0, f] at h ⊢; omega
  · have h := shcrKindHandlePostC_costAt_online_le true S b st q hq
    dsimp only [shcrKeyInd1KeyKindAtomicProg, shcr1KeyKindHandlePostC, c0, f] at h ⊢; omega
  · cases q with
    | roQuery sec =>
      have h := shcrKindHandlePreC_costAt_ro_le true S f.M_on f.roCap st sec
      dsimp only [shcrKeyInd1KeyKindAtomicProg, shcr1KeyKindHandlePreC, c1, f] at h ⊢; omega
    | _ => simp [keyIndQueryKind] at hq
  · cases q with
    | roQuery sec =>
      have h := shcrKindHandlePostC_costAt_ro_le true S f.M_on f.roCap st sec
      dsimp only [shcrKeyInd1KeyKindAtomicProg, shcr1KeyKindHandlePostC, c1, f] at h ⊢; omega
    | _ => simp [keyIndQueryKind] at hq
  · have hMax0 : max pqPrimIface.uCost (c0 + (pqKeyIndCodec S).codecCost) ≤ shcrOnlineArmBudget f := by
      change max 1 (c0 + 64) ≤ shcrOnlineArmBudget f; simp only [c0, shcrOnlineArmBudget]; omega
    have hMax1 : max pqPrimIface.uCost (c1 + (pqKeyIndCodec S).codecCost) ≤ 4420 * bits f.roCap + 1850 := by
      change max 1 (c1 + 64) ≤ 4420 * bits f.roCap + 1850; simp only [c1]; omega
    have hDone : (shcrKeyInd1KeyKindAtomicProg S b).chDone.cost ≤ shcrOnlineArmBudget f := by
      have : (shcrKeyInd1KeyKindAtomicProg S b).chDone.cost ≤ 50 := shcrKindChDoneC_cost_le
      simp only [shcrOnlineArmBudget]; omega
    refine Nat.le_trans (costByKind_join_le (f_Mon := f.M_on) (f_Moff := f.M_off)
      (rfl : keyIndKindCounts b 0 = f.M_on) (rfl : keyIndKindCounts b 1 = f.M_off) hMax0 hMax1
      (shcr1KeyKindInitC_cost_le_split S b : (shcrKeyInd1KeyKindAtomicProg S b).init.cost ≤ _) hDone
      (shcrKindResumeC_cost_le S b : (shcrKeyInd1KeyKindAtomicProg S b).resume.cost ≤ _)
      (shcrKindFinishC_cost_le f.M_on : (shcrKeyInd1KeyKindAtomicProg S b).finish.cost ≤ _)) ?_
    have hLHS : (1000 + 22 * Nat.log 2 S.N_dh + 11 * f.M_on) + (f.M_on + 1) * shcrOnlineArmBudget f +
        f.M_off * (4420 * bits f.roCap + 1850) + (100 + 23400 * f.M_on) ≤
        (1000 + 22 * Nat.log 2 S.N_dh + 11 * f.M_on) +
          (f.M_on + 1) * (42000 + 8000 * f.M_on + 16700 * f.M_dh + 15400 * f.M_sess) +
          (f.M_off + f.M_on + 1) * (4420 * bits f.roCap + 1850) + (100 + 23400 * f.M_on) := by
      simp only [shcrOnlineArmBudget]; nlinarith
    refine Nat.le_trans hLHS ?_
    unfold stepCostBudgetSplit
    change (1000 + 22 * Nat.log 2 S.N_dh + 11 * f.M_on) +
        (f.M_on + 1) * (42000 + 8000 * f.M_on + 16700 * f.M_dh + 15400 * f.M_sess) +
        (f.M_off + f.M_on + 1) * (4420 * bits f.roCap + 1850) + (100 + 23400 * f.M_on) ≤
      2 ^ 16 * (f.M_on + 1) * (f.M_on + 1) + 2 ^ 15 * (f.M_on + 1) * (f.M_dh + f.M_sess) +
        2 ^ 10 * (f.M_on + f.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        2 ^ 13 * (f.M_off + f.M_on) * (bits f.roCap + 4) + 2 ^ 13 * f.M_off * f.M_on +
        2 ^ 11 * f.M_dh ^ 2 + 2 ^ 8 * f.M_dh * f.M_sess
    by_cases hZero : f.M_off + f.M_on = 0
    · have hOff0 : f.M_off = 0 := by omega
      have hOn0 : f.M_on = 0 := by omega
      have hDh0 : f.M_dh = 0 := by dsimp [f, keyIndCoreFuels] at hOn0 ⊢; omega
      have hSess0 : f.M_sess = 0 := by dsimp [f, keyIndCoreFuels] at hOn0 ⊢; omega
      have hCap1 : f.roCap = 1 := by dsimp [f, keyIndCoreFuels] at hOff0 hOn0 ⊢; omega
      rw [hOff0, hOn0, hDh0, hSess0, hCap1, bits_1]; omega
    · have hPos : 1 ≤ f.M_off + f.M_on := by omega
      have hCapLe : f.roCap ≤ 3 * (f.M_off + f.M_on) := by dsimp [f, keyIndCoreFuels] at hPos ⊢; omega
      have hBitsLe : bits f.roCap ≤ 4 * (f.M_off + f.M_on) := by have := bits_le_add_one f.roCap; omega
      have hAvl : (f.M_off + f.M_on + 1) * (4420 * bits f.roCap + 1850) ≤
          2 ^ 13 * (f.M_off + f.M_on) * (bits f.roCap + 4) := by nlinarith
      have hQuad : 1100 + 23411 * f.M_on + (f.M_on + 1) * (42000 + 8000 * f.M_on) ≤
          2 ^ 16 * (f.M_on + 1) * (f.M_on + 1) := by nlinarith
      have hLin : (f.M_on + 1) * (16700 * f.M_dh + 15400 * f.M_sess) ≤
          2 ^ 15 * (f.M_on + 1) * (f.M_dh + f.M_sess) := by nlinarith
      have hLog : 22 * Nat.log 2 S.N_dh ≤
          2 ^ 10 * (f.M_on + f.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by nlinarith
      nlinarith

private theorem totalCost_join_le {cInit cPre cPost cCod uC cDone cRes cFin Q BInit BArm BFin : ℕ}
    (hU : uC ≤ BArm) (hi : cInit ≤ BInit) (hPre : cPre + cCod ≤ BArm) (hPost : cPost + cCod ≤ BArm)
    (hDone : cDone ≤ BArm) (hRes : cRes ≤ BArm) (hFin : cFin ≤ BFin) :
    cInit + Q * max uC (max cPre cPost + cCod) + max cDone cRes + cFin ≤ BInit + (Q + 1) * BArm + BFin := by
  have hm1 : max cPre cPost + cCod ≤ BArm := by omega
  have hmH : max uC (max cPre cPost + cCod) ≤ BArm := Nat.max_le.mpr ⟨hU, hm1⟩
  have hmCR : max cDone cRes ≤ BArm := Nat.max_le.mpr ⟨hDone, hRes⟩
  have hMul := Nat.mul_le_mul_left Q hmH; nlinarith

/-- Total step-cost bound for `shcrKeyInd1KeyKindAtomicProg`. -/
theorem shcrKeyInd1KeyKindAtomicProg_cost (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyKindAtomicProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  let f := keyIndCoreFuels S b
  have hU : pqPrimIface.uCost ≤ shcrOnlineArmBudget f := by
    change 1 ≤ shcrOnlineArmBudget f; simp only [shcrOnlineArmBudget]; omega
  have hDone : shcrKindChDoneC.cost ≤ shcrOnlineArmBudget f := by
    have := shcrKindChDoneC_cost_le; simp only [shcrOnlineArmBudget]; omega
  refine Nat.le_trans (totalCost_join_le hU (shcr1KeyKindInitC_cost_le_total S b)
    (shcr1KeyKindHandlePreC_cost_le S b) (shcr1KeyKindHandlePostC_cost_le S b)
    hDone (shcrKindResumeC_cost_le S b) (shcrKindFinishC_cost_le f.M_on)) ?_
  have hMonLe : f.M_on ≤ b.q_total := Nat.min_le_right _ _
  have hMoffLe : f.M_off ≤ b.q_total := Nat.min_le_right _ _
  have hMdhLe : f.M_dh ≤ min b.q_total S.N_dh := by dsimp [f, keyIndCoreFuels] at hMonLe ⊢; omega
  have hMsessLe : f.M_sess ≤ min b.q_total S.N_sess_tot := by dsimp [f, keyIndCoreFuels] at hMonLe ⊢; omega
  have hBitsCap : bits f.roCap ≤ 3 * b.q_total + 2 := by
    have hCap : f.roCap ≤ 3 * b.q_total + 1 := by dsimp [f, keyIndCoreFuels] at hMonLe hMoffLe ⊢; omega
    have hb := bits_le_add_one f.roCap; omega
  have hArmLe : shcrOnlineArmBudget f ≤
      52690 + 21260 * b.q_total + 16700 * min b.q_total S.N_dh + 15400 * min b.q_total S.N_sess_tot := by
    simp only [shcrOnlineArmBudget]; nlinarith
  have hMul := Nat.mul_le_mul_left (b.q_total + 1) hArmLe
  unfold stepCostBudget; dsimp only
  generalize min b.q_total S.N_dh = md at hMdhLe hArmLe hMul ⊢
  generalize min b.q_total S.N_sess_tot = ms at hMsessLe hArmLe hMul ⊢
  nlinarith

private theorem mapPrim_queries_le {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (mapComp tlPrimKeyInd c).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      c.queries primW primWS :=
  mapComp_queries_le tlPrimKeyInd primW primWS primIfacePrimQueryWeight tlPrimKeyInd_primW c

private theorem runAt2_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (c : Comp pqAtomicOps I [A, B] R) :
    (runAt2 aE bE c).queries w ws = c.queries w ws := by simp [runAt2, Comp.queries]

private theorem runAt3_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} {Γ : List (Ty pqAtomicSig)} {A B C R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (m : Comp pqAtomicOps I [A, B, C] R) :
    (runAt3 aE bE cE m).queries w ws = m.queries w ws := by simp [runAt3, Comp.queries]

private theorem runAt4_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} {Γ : List (Ty pqAtomicSig)} {A B C D R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (m : Comp pqAtomicOps I [A, B, C, D] R) :
    (runAt4 aE bE cE dE m).queries w ws = m.queries w ws := by simp [runAt4, Comp.queries]

private theorem runAt5_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} {Γ : List (Ty pqAtomicSig)} {A B C D E R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (m : Comp pqAtomicOps I [A, B, C, D, E] R) :
    (runAt5 aE bE cE dE eE m).queries w ws = m.queries w ws := by simp [runAt5, Comp.queries]

private theorem runAt6_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} {Γ : List (Ty pqAtomicSig)} {A B C D E F R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (fE : Expr pqAtomicOps Γ F)
    (m : Comp pqAtomicOps I [A, B, C, D, E, F] R) :
    (runAt6 aE bE cE dE eE fE m).queries w ws = m.queries w ws := by simp [runAt6, Comp.queries]

private theorem caseSum_queries_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (e : Expr pqAtomicOps Γ (.sum A B)) (c1 : Comp pqAtomicOps I (A :: Γ) R)
    (c2 : Comp pqAtomicOps I (B :: Γ) R) {M : ℕ} (h1 : c1.queries w ws ≤ M) (h2 : c2.queries w ws ≤ M) :
    (Comp.caseSum e c1 c2).queries w ws ≤ M := by
  simp only [Comp.queries]; exact Nat.max_le.mpr ⟨h1, h2⟩

private theorem compRename_queries_eq {S : _root_.ReductionDsl.Sig} {O : _root_.ReductionDsl.Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T} {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} :
    ∀ {Γ Δ : List (Ty S)} {t : Ty S} (ξ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp O I Γ t),
      (compRename ξ c).queries w ws = c.queries w ws
  | _, _, _, _, .ret _ | _, _, _, _, .sample _ _ | _, _, _, _, .query _ _ => rfl
  | _, _, _, ξ, .bind c k => by simp only [compRename, Comp.queries, compRename_queries_eq _ c, compRename_queries_eq _ k]
  | _, _, _, ξ, .ite b c d | _, _, _, ξ, .caseOpt b c d | _, _, _, ξ, .caseSum b c d => by
    simp only [compRename, Comp.queries, compRename_queries_eq _ c, compRename_queries_eq _ d]
  | _, _, _, ξ, .iter _ e body | _, _, _, ξ, .findM _ e body | _, _, _, ξ, .anyM _ e body | _, _, _, ξ, .mapM _ e body => by
    simp only [compRename, Comp.queries, compRename_queries_eq _ body]
  | _, _, _, ξ, .consumeFirstM _ l p mk => by simp only [compRename, Comp.queries, compRename_queries_eq _ p]
  | _, _, _, ξ, .foldM _ l z f => by simp only [compRename, Comp.queries, compRename_queries_eq _ f]

private theorem dispatchKeyIndQ_queries_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {w : I.Tag → ℕ} {ws : I.smp.Samp → ℕ} (S : Setup) {Γ : List (Ty pqAtomicSig)} {R : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q)) (M : ℕ)
    (a1 a2 : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) R)
    (a3 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R)
    (a4 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: Γ) R)
    (a5 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (a6 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_no_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (a7 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.prod (.base (.fin S.N_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (a8 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.prod (.base (.fin S.N_no_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (a9 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (a10 : Comp pqAtomicOps I (PB 192 :: Γ) R) (a11 : Comp pqAtomicOps I (.unit :: Γ) R)
    (a12 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (a13 : Comp pqAtomicOps I (PB 32 :: Γ) R)
    (a14 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R)
    (h1 : a1.queries w ws ≤ M) (h2 : a2.queries w ws ≤ M) (h3 : a3.queries w ws ≤ M) (h4 : a4.queries w ws ≤ M)
    (h5 : a5.queries w ws ≤ M) (h6 : a6.queries w ws ≤ M) (h7 : a7.queries w ws ≤ M) (h8 : a8.queries w ws ≤ M)
    (h9 : a9.queries w ws ≤ M) (h10 : a10.queries w ws ≤ M) (h11 : a11.queries w ws ≤ M) (h12 : a12.queries w ws ≤ M)
    (h13 : a13.queries w ws ≤ M) (h14 : a14.queries w ws ≤ M) :
    (dispatchKeyIndQ S qE a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14).queries w ws ≤ M := by
  dsimp only [dispatchKeyIndQ]
  refine caseSum_queries_le _ _ _ h1 <| caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <|
    caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <| caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <|
    caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <| caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <|
    caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <| caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <|
    caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <| caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <|
    caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <| caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) <|
    caseSum_queries_le _ _ _ (by simpa [compRename_queries_eq]) (by simpa [compRename_queries_eq])

private theorem shcrNonSessionLegs_queries_le (S : Setup) (K : ℕ) :
    (shcrInitPrin1KeyLeg K).queries primW primWS ≤ 4 ∧ (shcrCorruptLeg K).queries primW primWS ≤ 4 ∧
    (shcrActiveGenSpkLeg S K).queries primW primWS ≤ 4 ∧ (shcrGenOpkLeg K).queries primW primWS ≤ 4 ∧
    (shcrTestLeg K).queries primW primWS ≤ 4 ∧ (shcrRevDhLeg K).queries primW primWS ≤ 4 ∧
    (shcrRevSessLeg K).queries primW primWS ≤ 4 ∧ shcrRegKeyLeg.queries primW primWS ≤ 4 ∧
    (shcrRevSpkLeg K).queries primW primWS ≤ 4 := by
  refine ⟨by simp [shcrInitPrin1KeyLeg, initPrin1KeyB, onBase_queries, bindV, Comp.queries],
    by simp [shcrCorruptLeg, onBase_queries, corruptB_queries],
    by simp [shcrActiveGenSpkLeg, caseOptV, bindV, onBase_queries, genSpkB_queries, Comp.queries],
    by simp [shcrGenOpkLeg, onBase_queries, genOpkB_queries], by simp [shcrTestLeg, onBase_queries, testB_queries],
    by simp [shcrRevDhLeg, onBase_queries, revealDhB_queries], by simp [shcrRevSessLeg, onBase_queries, revealB_queries],
    by simp [shcrRegKeyLeg, onBase_queries, registerB_queries], by simp [shcrRevSpkLeg, onBase_queries, revealSpkB_queries]⟩

private theorem shcrLiftLegArmK_queries_le (S : Setup) {A : Ty pqAtomicSig} {P : Ty pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (leg : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, P] SCS)
    {Q : ℕ} (hLeg : leg.queries primW primWS ≤ Q) :
    (shcrLiftLegArmK S payE leg).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
  have hMap := mapPrim_queries_le leg
  simp only [shcrLiftLegArmK, runAt2_queries, Comp.queries]; omega

private theorem shcrInitArmPostK_queries_le (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    (shcrInitArmPostK S K_on capRo N_s opk).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      11 + 18 * S.N_dh + 8 * S.N_sess_tot := by
  have hPre : (shcrInitiatePreRoC S K_on opk).queries primW primWS ≤ 11 + 8 * S.N_dh := by
    have hM : min K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    simp only [shcrInitiatePreRoC, initFinishPreRoC, letV, bindV, caseOptV, preCheckC_queries,
      checkSigsC_queries, queries_sBytes32, queries_qKemEncaps, queries_qX25519Base, queries_qX25519, Comp.queries]; omega
  have hPost : (shcrInitiatePostRoC S K_on).queries primW primWS ≤ 10 * S.N_dh + 8 * S.N_sess_tot := by
    have hM : min K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    have hMs : min K_on S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
    simp only [shcrInitiatePostRoC, initFinishPostRoC, letV, bindV, caseOptV, findMV,
      honestPeerC_queries, checkProvC_queries, partnerC_queries, findHonestC_queries, queries_sDrKey96, Comp.queries]; omega
  have hPreM := Nat.le_trans (mapPrim_queries_le (shcrInitiatePreRoC S K_on opk)) hPre
  have hPostM := Nat.le_trans (mapPrim_queries_le (shcrInitiatePostRoC S K_on)) hPost
  have hRo : (roShadowQueryC tlPrimKeyInd capRo
      (Γ := embedTy shcrInitMidTy :: embedTy (.sum SCS shcrInitMidTy) ::
            .prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
            shcrKindStTy :: (pqKeyIndCodec S).Q :: [])
      (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).queries
      primIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
    roShadowQueryC_queries_zero tlPrimKeyInd primIfacePrimQueryWeight capRo _ _ _
  simp only [shcrInitArmPostK, runAt2_queries, runAt4_queries, Comp.queries]; rw [hRo]; omega

private theorem shcrInitArmPreK_queries_le (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    (shcrInitArmPreK S K_on capRo N_s opk).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      80 * S.N_dh + 16 * S.N_sess_tot + 176 := by
  let tp := tryPauseC S K_on opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy]) .zero .zero
  have hTp : tp.queries primW primWS ≤ 5 + 8 * S.N_dh := by
    have hM : min K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    dsimp only [tp]; cases opk <;> { simp only [tryPauseC, letV, bindV, caseOptV, preCheckC_queries, checkSigsC_queries, Comp.queries]; omega }
  have hTpM := Nat.le_trans (mapPrim_queries_le tp) hTp
  have hPost := shcrInitArmPostK_queries_le S K_on capRo N_s opk
  dsimp only [tp] at hTpM
  simp only [shcrInitArmPreK, runAt2_queries, compRename_queries_eq, Comp.queries]; omega

private theorem shcrAccArmPostK_queries_le (S : Setup) (K_on capRo N_o : ℕ) (opk : Bool) :
    (shcrAccArmPostK S K_on capRo N_o opk).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 80 * S.N_dh + 16 * S.N_sess_tot + 176 := by
  have hPre : (shcrAcceptPreRoC S K_on opk).queries primW primWS ≤ 13 + 2 * S.N_dh := by
    have hM : min K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    cases opk <;> {
      simp only [shcrAcceptPreRoC, coreAcceptPreRoC, letV, bindV, caseOptV, koskSenderOkC_queries,
        acceptKeysC_queries, queries_qKemDecaps, queries_qX25519, Comp.queries, ↓reduceIte, Bool.false_eq_true]
      omega }
  have hPost : (shcrAcceptPostRoC S K_on opk).queries primW primWS ≤ 1 + 12 * S.N_dh := by
    have hM : min K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    simp only [shcrAcceptPostRoC, letV, bindV, caseOptV, findHonestC_queries, recordRespC_queries,
      queries_qKemDecaps, Comp.queries]; omega
  have hPreM := Nat.le_trans (mapPrim_queries_le (shcrAcceptPreRoC S K_on opk)) hPre
  have hPostM := Nat.le_trans (mapPrim_queries_le (shcrAcceptPostRoC S K_on opk)) hPost
  have hRo : (roShadowQueryC tlPrimKeyInd capRo
      (Γ := embedTy shcrAccMidTy :: embedTy (.opt shcrAccMidTy) ::
            .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv))
              (.prod (.base (.fin N_o)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
            shcrKindStTy :: (pqKeyIndCodec S).Q :: [])
      (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).queries
      primIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
    roShadowQueryC_queries_zero tlPrimKeyInd primIfacePrimQueryWeight capRo _ _ _
  simp only [shcrAccArmPostK, runAt2_queries, runAt5_queries, Comp.queries]; rw [hRo]; omega

private theorem shcrRoArmK_queries_zero (S : Setup) (capRo : ℕ) :
    (shcrRoArmK S capRo).queries primIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hRo : (roShadowQueryC tlPrimKeyInd capRo (Γ := [PB 192, shcrKindStTy, (pqKeyIndCodec S).Q])
      (shcrRoListAtomicE (.fst .v1)) (.snd .v1) .v0).queries
      primIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
    roShadowQueryC_queries_zero tlPrimKeyInd primIfacePrimQueryWeight capRo _ _ _
  have hSet := mapPrim_queries_le shcrSetRoRespC
  have hSet0 : shcrSetRoRespC.queries primW primWS = 0 := rfl
  simp only [shcrRoArmK, runAt3_queries, Comp.queries]; omega

/-- Syntactic primitive-query bound for `shcrKeyInd1KeyKindAtomicProg`. -/
theorem shcrKeyInd1KeyKindAtomicProg_q_prim (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyKindAtomicProg S b).totalQueries
        primIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  let f := keyIndCoreFuels S b
  let Q := 80 * S.N_dh + 16 * S.N_sess_tot + 176
  have hInit : (shcr1KeyKindInitC S b).queries primIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
    have hB : (shcr1KeyKindBaseInit S b).queries primW primWS = 0 := by
      dsimp only [shcr1KeyKindBaseInit]; split <;> simp [bindV, queries_sBool, queries_sIndex, Comp.queries]
    have hM := mapPrim_queries_le (shcr1KeyKindBaseInit S b)
    simp only [shcr1KeyKindInitC, Comp.queries]; omega
  have hChDone : shcrKindChDoneC.queries primIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
    have hM := mapPrim_queries_le shcrChDoneLeg
    have h0 : shcrChDoneLeg.queries primW primWS = 0 := rfl
    simp only [shcrKindChDoneC, runAt2_queries]; omega
  have hFinish : (shcrKindFinishC f.M_on).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤ b.q_total := by
    have hM := mapPrim_queries_le (shcrExtractLeg f.M_on)
    have hE : (shcrExtractLeg f.M_on).queries primW primWS = f.M_on := by simp [shcrExtractLeg, shcrExtractC_queries]
    have hMon : f.M_on ≤ b.q_total := Nat.min_le_right _ _
    simp only [shcrKindFinishC, runAt3_queries]; omega
  have hResume : (shcr1KeyKindResumeC S b).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
    have hPre : shcrResumePreRoC.queries primW primWS = 5 := by
      simp [shcrResumePreRoC, initFinishPreRoC, letV, bindV, queries_sBytes32, queries_qX25519Base, queries_qX25519, Comp.queries]
    have hPost : (shcrResumePostRoC S f.M_on).queries primW primWS ≤ 10 * S.N_dh + 8 * S.N_sess_tot := by
      have hM : min f.M_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
      have hMs : min f.M_on S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
      simp only [shcrResumePostRoC, initFinishPostRoC, letV, bindV, caseOptV, findMV,
        honestPeerC_queries, checkProvC_queries, partnerC_queries, findHonestC_queries, queries_sDrKey96, Comp.queries]; omega
    have hPreM := mapPrim_queries_le shcrResumePreRoC
    have hPostM := Nat.le_trans (mapPrim_queries_le (shcrResumePostRoC S f.M_on)) hPost
    have hRo : (roShadowQueryC tlPrimKeyInd f.roCap
        (Γ := [embedTy (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
                 (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32))),
               shcrKindStTy, embedTy pauseTy, .prod (PB 32) (PB 1568)])
        (shcrRoListAtomicE (.fst .v1)) (.snd .v1) (.fst .v0)).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
      roShadowQueryC_queries_zero tlPrimKeyInd primIfacePrimQueryWeight f.roCap _ _ _
    dsimp only [shcr1KeyKindResumeC, shcrKindResumeC, f] at hRo hPostM ⊢
    simp only [runAt3_queries, runAt6_queries, Comp.queries, Q]; rw [hRo]; omega
  rcases shcrNonSessionLegs_queries_le S f.M_on with ⟨hL1, hL2, hL3, hL4, hL9, hL11, hL12, hL13, hL14⟩
  have hRo0 := shcrRoArmK_queries_zero S f.roCap
  have hPreQ : (shcrKeyInd1KeyKindAtomicProg S b).handlePre.queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
    dsimp only [shcrKeyInd1KeyKindAtomicProg, shcr1KeyKindHandlePreC, shcrKindHandlePreC]; simp only [↓reduceIte]
    refine dispatchKeyIndQ_queries_le S .v1 Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · have := shcrLiftLegArmK_queries_le S (aop (.finVal S.N_id) .v0) _ hL1; dsimp only [f] at this; simp only [Comp.queries]; omega
    · have := shcrLiftLegArmK_queries_le S (aop (.finVal S.N_id) .v0) _ hL2; dsimp only [f] at this; simp only [Comp.queries]; omega
    · have := shcrLiftLegArmK_queries_le S (finPairToNatE S.N_id S.N_recv .v0) _ hL3; dsimp only [f] at this; simp only [Comp.queries]; omega
    · have := shcrLiftLegArmK_queries_le S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) _ hL4; dsimp only [f] at this; simp only [Comp.queries]; omega
    · exact shcrInitArmPreK_queries_le S _ _ S.N_send_opk true
    · exact shcrInitArmPreK_queries_le S _ _ S.N_send_no_opk false
    · have := shcrAccArmPostK_queries_le S (keyIndCoreFuels S b).M_on (keyIndCoreFuels S b).roCap S.N_opk true; simp only [Comp.queries, Q] at this ⊢; omega
    · have := shcrAccArmPostK_queries_le S (keyIndCoreFuels S b).M_on (keyIndCoreFuels S b).roCap S.N_no_opk false; simp only [Comp.queries, Q] at this ⊢; omega
    · have := shcrLiftLegArmK_queries_le S (finSidToNatExpr S .v0) _ hL9; dsimp only [f] at this; simp only [Comp.queries]; omega
    · dsimp only [f] at hRo0; simp only [Comp.queries]; omega
    · have := shcrLiftLegArmK_queries_le S (A := .unit) .unit _ hL11; dsimp only [f] at this; simp only [Comp.queries]; omega
    · have := shcrLiftLegArmK_queries_le S (finSidToNatExpr S .v0) _ hL12; dsimp only [f] at this; simp only [Comp.queries]; omega
    · have := shcrLiftLegArmK_queries_le S .v0 _ hL13; simp only [Comp.queries]; omega
    · have := shcrLiftLegArmK_queries_le S (finPairToNatE S.N_id S.N_recv .v0) _ hL14; dsimp only [f] at this; simp only [Comp.queries]; omega
  have hPostQ : (shcrKeyInd1KeyKindAtomicProg S b).handlePost.queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
    dsimp only [shcrKeyInd1KeyKindAtomicProg, shcr1KeyKindHandlePostC, shcrKindHandlePostC]; simp only [↓reduceIte]
    refine dispatchKeyIndQ_queries_le S .v1 Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL1) (by omega)
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL2) (by omega)
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL3) (by omega)
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL4) (by omega)
    · exact Nat.le_trans (shcrInitArmPostK_queries_le S _ _ S.N_send_opk true) (by dsimp only [Q]; omega)
    · exact Nat.le_trans (shcrInitArmPostK_queries_le S _ _ S.N_send_no_opk false) (by dsimp only [Q]; omega)
    · exact shcrAccArmPostK_queries_le S _ _ S.N_opk true
    · exact shcrAccArmPostK_queries_le S _ _ S.N_no_opk false
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL9) (by omega)
    · dsimp only [f] at hRo0; omega
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S (A := .unit) _ _ hL11) (by omega)
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL12) (by omega)
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL13) (by omega)
    · exact Nat.le_trans (shcrLiftLegArmK_queries_le S _ _ hL14) (by omega)
  have hJoinQ {qInit qPre qPost qDone qRes qFin : ℕ}
      (hi : qInit = 0) (hPre : qPre ≤ Q) (hPost : qPost ≤ Q)
      (hd : qDone = 0) (hr : qRes ≤ Q) (hf : qFin ≤ b.q_total) :
      qInit + b.q_total * max qPre qPost + max qDone qRes + qFin ≤ (b.q_total + 1) * Q + b.q_total := by
    have hmH : max qPre qPost ≤ Q := Nat.max_le.mpr ⟨hPre, hPost⟩
    have hmCR : max qDone qRes ≤ Q := Nat.max_le.mpr ⟨by omega, hr⟩
    have hMul := Nat.mul_le_mul_left b.q_total hmH; nlinarith
  refine Nat.le_trans (hJoinQ hInit hPreQ hPostQ hChDone hResume hFinish) ?_
  unfold primQueryBudget; dsimp only [Q]; nlinarith

private theorem pqPrimIface_fwdU_qBound (n : ℕ) :
    (pqPrimIface.fwdU n).IsQueryBoundP (fun q => isPrimQuery₀ q = true) 0 :=
  (isQueryBoundP_query_iff (spec := _root_.SignalPqxdh.PrimBaseSpec)
    (fun q => isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h)

/-- Evaluates `shcrKeyInd1KeyKindAtomicProg` to a `.Bounded` two-stage `KemShCrAdv` across both stages. -/
theorem shcrKeyInd1KeyKindAtomicProg_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ((pqxdhKeyInd1KeyKindCostedSims S).eval.shcr b A).Bounded := by
  have hQ := shcrKeyInd1KeyKindAtomicProg_q_prim S b
  have hw : ∀ (g : pqPrimIface.Tag) (x : (pqPrimIface.dom g).denote),
      isPrimQuery₀ (pqPrimIface.enc g x) = true → 1 ≤ primIfacePrimQueryWeight g := fun _ _ _ => Nat.le_refl 1
  exact ⟨fun pk sk => (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.TwoStageCostedReduction.eval1_queryBound
      (shcrKeyInd1KeyKindAtomicProg S b) (fun q => isPrimQuery₀ q = true)
      primIfacePrimQueryWeight samplerZeroQueryWeight hw pqPrimIface_fwdU_qBound
      (fun _ => A.1.run) (pk, sk) b.q_total false).mono hQ,
    fun st ss ct => (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.TwoStageCostedReduction.eval2_queryBound
      (shcrKeyInd1KeyKindAtomicProg S b) (fun q => isPrimQuery₀ q = true)
      primIfacePrimQueryWeight samplerZeroQueryWeight hw pqPrimIface_fwdU_qBound
      st (ss, ct) b.q_total false).mono hQ⟩

private theorem bits_fuels_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b
    bits (keyIndSentinel S b) ≤ bits (stepCostBudget S b) ∧
    bits f.M_on ≤ bits (stepCostBudget S b) ∧
    bits (min f.M_on S.N_dh) ≤ bits (stepCostBudget S b) ∧
    bits (min f.M_on S.N_sess_tot) ≤ bits (stepCostBudget S b) ∧
    bits (avlHeightCap f.roCap) ≤ bits (stepCostBudget S b) := by
  intro f
  have hBud : 6 * b.q_total + 4 ≤ stepCostBudget S b := by
    have h0 : 6 * b.q_total + 4 ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) := by nlinarith
    unfold stepCostBudget; dsimp only; omega
  have hSent : keyIndSentinel S b ≤ stepCostBudget S b := Nat.le_trans (keyIndSentinel_le S b) (by omega)
  have hMon : f.M_on ≤ b.q_total := Nat.min_le_right _ _
  have hMoff : f.M_off ≤ b.q_total := Nat.min_le_right _ _
  have hHCap : avlHeightCap f.roCap ≤ stepCostBudget S b := by
    have hCap : f.roCap ≤ 3 * b.q_total + 1 := by dsimp [f, keyIndCoreFuels] at hMon hMoff ⊢; omega
    have hb := bits_le_add_one f.roCap; dsimp [avlHeightCap]; omega
  exact ⟨_root_.ReductionDsl.bits_mono hSent,
    _root_.ReductionDsl.bits_mono (Nat.le_trans hMon (by omega)),
    _root_.ReductionDsl.bits_mono (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans hMon (by omega))),
    _root_.ReductionDsl.bits_mono (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans hMon (by omega))),
    _root_.ReductionDsl.bits_mono hHCap⟩

private theorem runAt2_size {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (c : Comp pqAtomicOps I [A, B] R) :
    (runAt2 aE bE c).size = c.size + aE.size + bE.size + 4 := by
  simp only [runAt2, Comp.size, exprRename_size, compRename_size]; omega

private theorem runAt3_size {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (m : Comp pqAtomicOps I [A, B, C] R) :
    (runAt3 aE bE cE m).size = m.size + aE.size + bE.size + cE.size + 6 := by
  simp only [runAt3, Comp.size, exprRename_size, compRename_size]; omega

private theorem runAt4_size {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (m : Comp pqAtomicOps I [A, B, C, D] R) :
    (runAt4 aE bE cE dE m).size = m.size + aE.size + bE.size + cE.size + dE.size + 8 := by
  simp only [runAt4, Comp.size, exprRename_size, compRename_size]; omega

private theorem runAt5_size {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (m : Comp pqAtomicOps I [A, B, C, D, E] R) :
    (runAt5 aE bE cE dE eE m).size = m.size + aE.size + bE.size + cE.size + dE.size + eE.size + 10 := by
  simp only [runAt5, Comp.size, exprRename_size, compRename_size]; omega

private theorem runAt6_size {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E F R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (fE : Expr pqAtomicOps Γ F)
    (m : Comp pqAtomicOps I [A, B, C, D, E, F] R) :
    (runAt6 aE bE cE dE eE fE m).size =
      m.size + aE.size + bE.size + cE.size + dE.size + eE.size + fE.size + 12 := by
  simp only [runAt6, Comp.size, exprRename_size, compRename_size]; omega

private theorem roShadowQueryC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowQueryC tlPrimKeyInd cap roListE tblE secE).size ≤
      1800 + 2 * bits (avlHeightCap cap) + roListE.size + tblE.size + 2 * secE.size := by
  let P0 := Ty.prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192)))
  let A0 := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty))
  have hs1 := samplePbytes32C_size_eq (I := pqPrimIface) rfl (Γ := A0 :: P0 :: Γ)
  have hs2 := samplePbytes32C_size_eq (I := pqPrimIface) rfl (Γ := PB 32 :: A0 :: P0 :: Γ)
  have hs3 := samplePbytes32C_size_eq (I := pqPrimIface) rfl (Γ := PB 32 :: PB 32 :: A0 :: P0 :: Γ)
  have hSrch := avlSearchB192C_size_le (I := pqPrimIface) cap (Γ := P0 :: Γ)
    (V := drKeyT (ℓ := 0) (Pt := Empty)) (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))
  have hIns := avlInsertAtPathC_size_le (I := pqPrimIface) cap
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) :: A0 :: P0 :: Γ)
    (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
  simp only [roShadowQueryC, sampleDrKey96AtomicC, aop, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
    _root_.ReductionDsl.AtomicPureOp.opSize] at hSrch hIns ⊢
  omega

private theorem dispatchKeyIndQ_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (S : Setup) {Γ : List (Ty pqAtomicSig)} {R : Ty pqAtomicSig} (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q))
    (a1 a2 : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) R)
    (a3 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R)
    (a4 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: Γ) R)
    (a5 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (a6 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_send_no_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (a7 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.prod (.base (.fin S.N_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (a8 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.prod (.base (.fin S.N_no_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (a9 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (a10 : Comp pqAtomicOps I (PB 192 :: Γ) R) (a11 : Comp pqAtomicOps I (.unit :: Γ) R)
    (a12 : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (a13 : Comp pqAtomicOps I (PB 32 :: Γ) R)
    (a14 : Comp pqAtomicOps I (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R) :
    (dispatchKeyIndQ S qE a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14).size ≤
      qE.size + a1.size + a2.size + a3.size + a4.size + a5.size + a6.size + a7.size +
        a8.size + a9.size + a10.size + a11.size + a12.size + a13.size + a14.size + 30 := by
  dsimp only [dispatchKeyIndQ]; simp only [Comp.size, compRename_size, Expr.v0, Expr.size]; omega

private theorem shcrRoListAtomicE_size_le {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy shcrStTy)) : (shcrRoListAtomicE sE).size ≤ sE.size + 25 := by
  simp only [shcrRoListAtomicE, shcrGetRoE, scBase, stRo, mapExpr, exprRename_size, Expr.size]; omega

private theorem shcrLiftLegArmK_size_le (S : Setup) {A : Ty pqAtomicSig} {P : Ty pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (leg : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, P] SCS) :
    (shcrLiftLegArmK S payE leg).size ≤ 10 * leg.size + compLitSize leg + payE.size + 20 := by
  have hM := mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe leg
  simp only [shcrLiftLegArmK, runAt2_size, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega

private theorem shcrRoArmK_size_le (S : Setup) (capRo : ℕ) :
    (shcrRoArmK S capRo).size ≤ 4500 + 2 * bits (avlHeightCap capRo) := by
  have hRo := roShadowQueryC_size_le capRo (Γ := [PB 192, shcrKindStTy, (pqKeyIndCodec S).Q])
    (shcrRoListAtomicE (.fst .v1)) (.snd .v1) .v0
  have hRL := shcrRoListAtomicE_size_le (Γ := [PB 192, shcrKindStTy, (pqKeyIndCodec S).Q]) (.fst .v1)
  have hSet := mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe shcrSetRoRespC
  have hSetSz : 10 * shcrSetRoRespC.size + compLitSize shcrSetRoRespC ≤ 2500 := by
    simp only [shcrSetRoRespC, scBase, scUpd, stUpd, stSecb, stPrin, stSpks, stOpks, stSess,
      stResps, stUsedO, stUsedN, stKyb, stAdv, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx,
      scChosen, scMk, stMk, rDrKey, v, Comp.size, Expr.size, compLitSize, exprLitSize]
    omega
  simp only [shcrRoArmK, runAt3_size, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at hRo hRL ⊢
  omega

private theorem shcr1KeyKindInitC_size_le (S : Setup) (b : QueryBudget) :
    (shcr1KeyKindInitC S b).size ≤ 1200 + 10 * bits (stepCostBudget S b) := by
  have hM := mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe (shcr1KeyKindBaseInit S b)
  have hSent := (bits_fuels_le_stepCostBudget S b).1
  have hBase : 10 * (shcr1KeyKindBaseInit S b).size + compLitSize (shcr1KeyKindBaseInit S b) ≤
      1100 + 10 * bits (keyIndSentinel S b) := by
    dsimp only [shcr1KeyKindBaseInit]; split <;> {
      simp only [emptyStE, stMk, scMk, bindV, v, sBool, sIndex, Comp.size, Expr.size, compLitSize,
        exprLitSize, _root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
        _root_.SignalPqxdh.LegacyCosted.pqU32Ops, _root_.ReductionDsl.Ops.sum, bits_0, Nat.add_zero]; omega }
  have hEmp : (emptyRoAvlE (Γ := [embedTy (.prod .unit shcrStTy), .prod (PB 1568) (PB 3168)])).size ≤ 60 := by
    simp [emptyRoAvlE, avlEmptyE, dfltB192E, dfltDrKeyE, aop, Expr.size, bits_0,
      pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.opSize]
  simp only [shcr1KeyKindInitC, Comp.size, Expr.size]; omega

set_option linter.unusedSimpArgs false in
private theorem shcrNonSessionLegs_size_le (S : Setup) (K : ℕ) :
    let bK := bits K; let bD := bits (min K S.N_dh)
    10 * (shcrInitPrin1KeyLeg K).size + compLitSize (shcrInitPrin1KeyLeg K) ≤ 3500 + 30 * bK ∧
    10 * (shcrCorruptLeg K).size + compLitSize (shcrCorruptLeg K) ≤ 4000 + 40 * bK ∧
    10 * (shcrActiveGenSpkLeg S K).size + compLitSize (shcrActiveGenSpkLeg S K) ≤ 18000 + 100 * bK ∧
    10 * (shcrGenOpkLeg K).size + compLitSize (shcrGenOpkLeg K) ≤ 4500 + 40 * bK ∧
    10 * (shcrTestLeg K).size + compLitSize (shcrTestLeg K) ≤ 16000 + 100 * bK ∧
    10 * (shcrRevDhLeg K).size + compLitSize (shcrRevDhLeg K) ≤ 4000 + 30 * bK ∧
    10 * (shcrRevSessLeg K).size + compLitSize (shcrRevSessLeg K) ≤ 13000 + 90 * bK ∧
    10 * shcrRegKeyLeg.size + compLitSize shcrRegKeyLeg ≤ 4000 ∧
    10 * (shcrRevSpkLeg K).size + compLitSize (shcrRevSpkLeg K) ≤ 4500 + 40 * bK + 20 * bD := by
  intro bK bD; have hMin : K.min S.N_dh = min K S.N_dh := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
    simp (config := { maxSteps := 1000000 }) only [
      shcrInitPrin1KeyLeg, shcrCorruptLeg, shcrActiveGenSpkLeg, shcrGenOpkLeg, shcrTestLeg, shcrRevDhLeg,
      shcrRevSessLeg, shcrRegKeyLeg, shcrRevSpkLeg, onBase, initPrin1KeyB, corruptB, genSpkB, genOpkB,
      testB, revealDhB, revealB, registerB, revealSpkB,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.freshE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rDh,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd, seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk,
      sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr, seTested,
      seRevealed, seMk, seUpd, reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal,
      reDrRand, reTested, reRevealed, reMk, reUpd, buMk, rNone, rInitPrin, rPk, rCorr, rBundle, rDrKey,
      rSpkSk, rs, natEq, nat2Eq, nat3Eq, sidEq, orE, guardE, nonZero32, letV, bindV, caseOptV, caseSumV,
      findMV, anyMV, eLet, eLet2, eCaseOpt, eCaseSum, eFind, eAny, eMap, v, litB, catB, consB, widenB,
      lenB, eqB, u32OfNat, eqU32, encEC, encKEM, sBool, sBytes32, sRandom64, sDrKey96, sIndex, qX25519,
      qX25519Base, qIsCanonical, qPow8, qSigPkGen, qSigSign, qSigVerify, qKemKeyGen, qKemEncaps,
      qKemDecaps, qHkdfDerive96, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, hMin,
      ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    simp only [Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      _root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      _root_.SignalPqxdh.LegacyCosted.pqU32Ops, _root_.ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr,
      _root_.SignalPqxdh.TAG_EC_DJB, _root_.SignalPqxdh.TAG_KYBER_1024, bits_0, bits_1, bits_32,
      List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
    (try dsimp only [bK, bD]); omega
  }

set_option linter.unusedSimpArgs false in
private theorem shcrSessionAndStages_size_le (S : Setup) (K : ℕ) :
    let bK := bits K; let bD := bits (min K S.N_dh); let bS := bits (min K S.N_sess_tot)
    (∀ opk, 10 * (shcrInitiatePreRoC S K opk).size + compLitSize (shcrInitiatePreRoC S K opk) ≤ 18000 + 100 * bK + 40 * bD) ∧
    10 * (shcrInitiatePostRoC S K).size + compLitSize (shcrInitiatePostRoC S K) ≤ 18000 + 100 * bK + 50 * bD + 20 * bS ∧
    (∀ opk, 10 * (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy]) .zero .zero).size +
      compLitSize (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy]) .zero .zero) ≤ 15000 + 100 * bK + 40 * bD) ∧
    (∀ opk, 10 * (shcrAcceptPreRoC S K opk).size + compLitSize (shcrAcceptPreRoC S K opk) ≤ 27000 + 110 * bK + 40 * bD) ∧
    (∀ opk, 10 * (shcrAcceptPostRoC S K opk).size + compLitSize (shcrAcceptPostRoC S K opk) ≤ 20000 + 80 * bK + 40 * bD) ∧
    10 * shcrChDoneLeg.size + compLitSize shcrChDoneLeg ≤ 600 ∧
    10 * shcrResumePreRoC.size + compLitSize shcrResumePreRoC ≤ 6000 ∧
    10 * (shcrResumePostRoC S K).size + compLitSize (shcrResumePostRoC S K) ≤ 20000 + 100 * bK + 50 * bD + 20 * bS ∧
    10 * (shcrExtractLeg K).size + compLitSize (shcrExtractLeg K) ≤ 12000 + 70 * bK := by
  intro bK bD bS
  have hMin1 : K.min S.N_dh = min K S.N_dh := rfl
  have hMin2 : K.min S.N_sess_tot = min K S.N_sess_tot := rfl
  have hF : _root_.SignalPqxdh.F_X25519.length = 32 := rfl
  refine ⟨fun opk => ?_, ?_, fun opk => ?_, fun opk => ?_, fun opk => ?_, ?_, ?_, ?_, ?_⟩
  all_goals try cases opk
  all_goals {
    simp (config := { maxSteps := 1000000 }) only [
      shcrInitiatePreRoC, initFinishPreRoC, shcrInitiatePostRoC, initFinishPostRoC, tryPauseC,
      shcrAcceptPreRoC, coreAcceptPreRoC, shcrAcceptPostRoC, shcrChDoneLeg, shcrResumePreRoC,
      shcrResumePostRoC, shcrExtractLeg, shcrExtractC, preCheckC, checkSigsC, findHonestC, isAdvRegC,
      isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC, resolveSigPkC, honestPeerC, checkProvC,
      partnerC, recordRespC, acceptKeysC, initGuardE, initSidE, shcrFinE, isNoneRespE, isSomeE, getDBytes,
      optFst, optSnd, orE, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, kyberCheckE,
      buildSecretsE, guardE, nonZero32, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.dhOptNZ,
      qK, qJ, qO, qHdr, qKJO, aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rrCt,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd, seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk,
      sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr, seTested,
      seRevealed, seMk, seUpd, reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal,
      reDrRand, reTested, reRevealed, reMk, reUpd, buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId,
      buPqspkB, buPqspkSig, buMk, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rNone, rHdr, rInitUnfresh, rAccFresh, rDrKey, rs, letV, bindV, caseOptV, caseSumV, findMV, anyMV,
      eLet, eLet2, eCaseOpt, eCaseSum, eFind, eAny, eMap, v, litB, catB, consB, widenB, lenB, eqB,
      u32OfNat, eqU32, encEC, encKEM, sBool, sBytes32, sRandom64, sDrKey96, sIndex, qX25519, qX25519Base,
      qIsCanonical, qPow8, qSigPkGen, qSigSign, qSigVerify, qKemKeyGen, qKemEncaps, qKemDecaps,
      qHkdfDerive96, hF, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize, hMin1, hMin2,
      ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    simp only [Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      _root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      _root_.SignalPqxdh.LegacyCosted.pqU32Ops, _root_.ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr,
      _root_.SignalPqxdh.TAG_EC_DJB, _root_.SignalPqxdh.TAG_KYBER_1024, hF, bits_0, bits_1, bits_32,
      List.length_nil, List.length_cons, List.length_replicate, Nat.add_zero, Nat.zero_add]
    (try dsimp only [bK, bD, bS]); omega
  }

private theorem shcrSessionArmsK_size_le (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b; let bs := bits (stepCostBudget S b)
    (∀ N_s opk, (shcrInitArmPostK S f.M_on f.roCap N_s opk).size ≤ 39000 + 320 * bs) ∧
    (∀ N_s opk, (shcrInitArmPreK S f.M_on f.roCap N_s opk).size ≤ 55000 + 460 * bs) ∧
    (∀ N_o opk, (shcrAccArmPostK S f.M_on f.roCap N_o opk).size ≤ 50000 + 280 * bs) := by
  intro f bs
  obtain ⟨_, hbK, hbD, hbS, hbA⟩ := bits_fuels_le_stepCostBudget S b
  obtain ⟨hIPre, hIPost, hTp, hAPre, hAPost, -⟩ := shcrSessionAndStages_size_le S f.M_on
  refine ⟨fun N_s opk => ?_, fun N_s opk => ?_, fun N_o opk => ?_⟩
  · have hM1 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) (hIPre opk)
    have hM2 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) hIPost
    let Γi : List (Ty pqAtomicSig) := embedTy shcrInitMidTy :: embedTy (.sum SCS shcrInitMidTy) ::
      .prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
      shcrKindStTy :: (pqKeyIndCodec S).Q :: []
    have hRo := roShadowQueryC_size_le f.roCap (Γ := Γi) (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)
    have hRL := shcrRoListAtomicE_size_le (Γ := Γi) (.fst .v3)
    simp only [shcrInitArmPostK, initPayToNatE, aop, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
      _root_.ReductionDsl.AtomicPureOp.opSize, runAt2_size, runAt4_size, Comp.size, Expr.size,
      Expr.v0, Expr.v1, Expr.v3, Expr.v4] at hRo hRL ⊢
    dsimp only [f, bs, Γi] at hbK hbD hbS hbA hM1 hM2 hRo hRL ⊢; omega
  · have hM := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) (hTp opk)
    have hM1 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) (hIPre opk)
    have hM2 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) hIPost
    let Γi : List (Ty pqAtomicSig) := embedTy shcrInitMidTy :: embedTy (.sum SCS shcrInitMidTy) ::
      .prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
      shcrKindStTy :: (pqKeyIndCodec S).Q :: []
    have hRo := roShadowQueryC_size_le f.roCap (Γ := Γi) (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)
    have hRL := shcrRoListAtomicE_size_le (Γ := Γi) (.fst .v3)
    simp only [shcrInitArmPreK, shcrInitArmPostK, initPayToNatE, aop, pqAtomicOps,
      _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.opSize, runAt2_size, runAt4_size,
      compRename_size, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v3, Expr.v4] at hRo hRL ⊢
    dsimp only [f, bs, Γi] at hbK hbD hbS hbA hM hM1 hM2 hRo hRL ⊢; omega
  · have hM1 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) (hAPre opk)
    have hM2 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) (hAPost opk)
    let Γa : List (Ty pqAtomicSig) := embedTy shcrAccMidTy :: embedTy (.opt shcrAccMidTy) ::
      .prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv))
        (.prod (.base (.fin N_o)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
      shcrKindStTy :: (pqKeyIndCodec S).Q :: []
    have hRo := roShadowQueryC_size_le f.roCap (Γ := Γa) (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)
    have hRL := shcrRoListAtomicE_size_le (Γ := Γa) (.fst .v3)
    simp only [shcrAccArmPostK, accPayToNatE, atomicRNoneE, aop, pqAtomicOps,
      _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.opSize, runAt2_size, runAt5_size,
      Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hRo hRL ⊢
    dsimp only [f, bs, Γa] at hbK hbD hbS hbA hM1 hM2 hRo hRL ⊢; omega

private theorem twoStageSize_join_le {sInit sPre sDone sRes sPost sFin bs : ℕ}
    (h1 : sInit ≤ 1200 + 10 * bs) (h2 : sPre ≤ 289000 + 2000 * bs)
    (h3 : sDone ≤ 700) (h4 : sRes ≤ 28500 + 180 * bs)
    (h5 : sPost ≤ 257000 + 1720 * bs) (h6 : sFin ≤ 12200 + 70 * bs) :
    sInit + sPre + sDone + sRes + sPost + sFin ≤ 588600 + 3980 * bs := by omega

private theorem shcrKeyInd1KeyKindAtomicProg_size_le (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyKindAtomicProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  let f := keyIndCoreFuels S b; let bs := bits (stepCostBudget S b)
  obtain ⟨_, hbK, hbD, hbS, hbA⟩ := bits_fuels_le_stepCostBudget S b
  obtain ⟨hNS1, hNS2, hNS3, hNS4, hNS5, hNS6, hNS7, hNS8, hNS9⟩ := shcrNonSessionLegs_size_le S f.M_on
  obtain ⟨hIPostA, hIPreA, hAccA⟩ := shcrSessionArmsK_size_le S b
  obtain ⟨_, _, _, _, _, hDoneL, hResPreL, hResPostL, hExtL⟩ := shcrSessionAndStages_size_le S f.M_on
  have hSidSz {Γ : List (Ty pqAtomicSig)} :
      (finSidToNatExpr S (.v0 : Expr pqAtomicOps (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S :: Γ) _)).size ≤ 60 := by
    simp [finSidToNatExpr, _root_.Computational.Proofs.SignalPqxdh.AtomicLift.aop,
      pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.opSize, Expr.size, Expr.v0]
  let a1 := shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrInitPrin1KeyLeg f.M_on)
  let a2 := shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg f.M_on)
  let a3 := shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrActiveGenSpkLeg S f.M_on)
  let a4 := shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat)) (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg f.M_on)
  let a9 := shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrTestLeg f.M_on)
  let a11 := shcrLiftLegArmK S (A := .unit) (P := .unit) .unit (shcrRevDhLeg f.M_on)
  let a12 := shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrRevSessLeg f.M_on)
  let a13 := shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg
  let a14 := shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg f.M_on)
  have hNS_sum : a1.size + a2.size + a3.size + a4.size + a9.size + a11.size + a12.size + a13.size + a14.size ≤ 73000 + 500 * bs := by
    have hs := hSidSz (Γ := [shcrKindStTy, (pqKeyIndCodec S).Q])
    have hp1 : (aop (.finVal S.N_id) (.v0 : Expr pqAtomicOps [.base (.fin S.N_id), shcrKindStTy, (pqKeyIndCodec S).Q] _)).size ≤ 10 := by
      simp [pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.opSize, Expr.size, Expr.v0]
    have hp2 : (finPairToNatE S.N_id S.N_recv (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)), shcrKindStTy, (pqKeyIndCodec S).Q] _)).size ≤ 20 := by
      simp [finPairToNatE, aop, pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.opSize, Expr.size, Expr.v0]
    have hp3 : (finTripleToNatE S.N_id S.N_recv S.N_opk (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))), shcrKindStTy, (pqKeyIndCodec S).Q] _)).size ≤ 30 := by
      simp [finTripleToNatE, aop, pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.opSize, Expr.size, Expr.v0]
    have hpu : (.unit : Expr pqAtomicOps [.unit, shcrKindStTy, (pqKeyIndCodec S).Q] .unit).size = 1 := rfl
    have hpv : (.v0 : Expr pqAtomicOps [PB 32, shcrKindStTy, (pqKeyIndCodec S).Q] (PB 32)).size = 1 := rfl
    have l1 := shcrLiftLegArmK_size_le S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrInitPrin1KeyLeg f.M_on)
    have l2 := shcrLiftLegArmK_size_le S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg f.M_on)
    have l3 := shcrLiftLegArmK_size_le S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrActiveGenSpkLeg S f.M_on)
    have l4 := shcrLiftLegArmK_size_le S (P := .prod .nat (.prod .nat .nat)) (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg f.M_on)
    have l5 := shcrLiftLegArmK_size_le S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrTestLeg f.M_on)
    have l6 := shcrLiftLegArmK_size_le S (A := .unit) (P := .unit) .unit (shcrRevDhLeg f.M_on)
    have l7 := shcrLiftLegArmK_size_le S (P := _root_.SignalPqxdh.LegacyCosted.sidT) (finSidToNatExpr S .v0) (shcrRevSessLeg f.M_on)
    have l8 := shcrLiftLegArmK_size_le S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg
    have l9 := shcrLiftLegArmK_size_le S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg f.M_on)
    dsimp only [a1, a2, a3, a4, a9, a11, a12, a13, a14, f, bs] at hbK hbD hNS1 hNS2 hNS3 hNS4 hNS5 hNS6 hNS7 hNS8 hNS9 hs hp1 hp2 hp3 hpu hpv l1 l2 l3 l4 l5 l6 l7 l8 l9 ⊢
    omega
  have hRoA := shcrRoArmK_size_le S f.roCap
  have hPostSz : (shcrKeyInd1KeyKindAtomicProg S b).handlePost.size ≤ 257000 + 1720 * bs := by
    have hD := dispatchKeyIndQ_size_le S (Γ := [shcrKindStTy, (pqKeyIndCodec S).Q]) .v1
      a1 a2 a3 a4 (shcrInitArmPostK S f.M_on f.roCap S.N_send_opk true)
      (shcrInitArmPostK S f.M_on f.roCap S.N_send_no_opk false)
      (shcrAccArmPostK S f.M_on f.roCap S.N_opk true) (shcrAccArmPostK S f.M_on f.roCap S.N_no_opk false)
      a9 (shcrRoArmK S f.roCap) a11 a12 a13 a14
    have hi1 := hIPostA S.N_send_opk true; have hi2 := hIPostA S.N_send_no_opk false
    have ha1 := hAccA S.N_opk true; have ha2 := hAccA S.N_no_opk false
    change (shcrKindHandlePostC true S f.M_on f.roCap).size ≤ _
    dsimp only [shcrKindHandlePostC]; simp only [↓reduceIte, Expr.v1, Expr.size] at hD ⊢
    dsimp only [a1, a2, a3, a4, a9, a11, a12, a13, a14, f, bs] at hbA hRoA hNS_sum hD hi1 hi2 ha1 ha2 ⊢
    omega
  have hPreSz : (shcrKeyInd1KeyKindAtomicProg S b).handlePre.size ≤ 289000 + 2000 * bs := by
    let wrapInl {A} (c : Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
        (.prod ((pqKeyIndCodec S).R) shcrKindStTy)) :
        Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
          (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
                (.prod (PB 1568) (.prod (embedTy pauseTy) shcrKindStTy))) := .bind c (.ret (.inl .v0))
    have hWrap {A} (c : Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
        (.prod ((pqKeyIndCodec S).R) shcrKindStTy)) : (wrapInl c).size = c.size + 4 := by
      simp [wrapInl, Comp.size, Expr.size, Expr.v0]
    have hD := dispatchKeyIndQ_size_le S (Γ := [shcrKindStTy, (pqKeyIndCodec S).Q]) .v1
      (wrapInl a1) (wrapInl a2) (wrapInl a3) (wrapInl a4)
      (shcrInitArmPreK S f.M_on f.roCap S.N_send_opk true)
      (shcrInitArmPreK S f.M_on f.roCap S.N_send_no_opk false)
      (wrapInl (shcrAccArmPostK S f.M_on f.roCap S.N_opk true))
      (wrapInl (shcrAccArmPostK S f.M_on f.roCap S.N_no_opk false))
      (wrapInl a9) (wrapInl (shcrRoArmK S f.roCap)) (wrapInl a11) (wrapInl a12) (wrapInl a13) (wrapInl a14)
    have hi1 := hIPreA S.N_send_opk true; have hi2 := hIPreA S.N_send_no_opk false
    have ha1 := hAccA S.N_opk true; have ha2 := hAccA S.N_no_opk false
    change (shcrKindHandlePreC true S f.M_on f.roCap).size ≤ _
    dsimp only [shcrKindHandlePreC]; simp only [hWrap, Expr.v1, Expr.size] at hD
    dsimp only [wrapInl] at hD; simp only [↓reduceIte, Expr.v1]
    dsimp only [a1, a2, a3, a4, a9, a11, a12, a13, a14, f, bs] at hbA hRoA hNS_sum hD hi1 hi2 ha1 ha2 ⊢
    omega
  have hDoneSz : (shcrKeyInd1KeyKindAtomicProg S b).chDone.size ≤ 700 := by
    have hM := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) hDoneL
    change shcrKindChDoneC.size ≤ 700; simp only [shcrKindChDoneC, runAt2_size, Expr.size, Expr.v0, Expr.v1]; omega
  have hResSz : (shcrKeyInd1KeyKindAtomicProg S b).resume.size ≤ 28500 + 180 * bs := by
    have hM1 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) hResPreL
    have hM2 := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) hResPostL
    let Γr : List (Ty pqAtomicSig) :=
      embedTy (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32))) ::
      [shcrKindStTy, embedTy pauseTy, .prod (PB 32) (PB 1568)]
    have hRo := roShadowQueryC_size_le f.roCap (Γ := Γr) (shcrRoListAtomicE (.fst .v1)) (.snd .v1) (.fst .v0)
    have hRL := shcrRoListAtomicE_size_le (Γ := Γr) (.fst .v1)
    change (shcrKindResumeC S f.M_on f.roCap).size ≤ _
    simp only [shcrKindResumeC, runAt3_size, runAt6_size, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hRo hRL ⊢
    dsimp only [f, bs, Γr] at hbK hbD hbS hbA hM1 hM2 hRo hRL ⊢; omega
  have hFinSz : (shcrKeyInd1KeyKindAtomicProg S b).finish.size ≤ 12200 + 70 * bs := by
    have hM := Nat.le_trans (mapComp_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe _) hExtL
    change (shcrKindFinishC f.M_on).size ≤ _; simp only [shcrKindFinishC, runAt3_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
    dsimp only [f, bs] at hbK hM ⊢; omega
  have hTot := twoStageSize_join_le (shcr1KeyKindInitC_size_le S b) hPreSz hDoneSz hResSz hPostSz hFinSz
  have h0 : 588600 ≤ reductionSizeBudget := by decide
  have h1 : 3980 * bs ≤ 2 ^ 12 * bs := Nat.mul_le_mul_right bs (by decide)
  change (shcrKeyInd1KeyKindAtomicProg S b).init.size + (shcrKeyInd1KeyKindAtomicProg S b).handlePre.size +
    (shcrKeyInd1KeyKindAtomicProg S b).chDone.size + (shcrKeyInd1KeyKindAtomicProg S b).resume.size +
    (shcrKeyInd1KeyKindAtomicProg S b).handlePost.size + (shcrKeyInd1KeyKindAtomicProg S b).finish.size ≤ _
  exact Nat.le_trans hTot (Nat.add_le_add h0 h1)

/-- Two-stage block-size and program-size bound for `shcrKeyInd1KeyKindAtomicProg`. -/
theorem shcrKeyInd1KeyKindAtomicProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRed2BlockBounded S b ℓ (shcrKeyInd1KeyKindAtomicProg S b) :=
  gred2BlockBounded_atomic_of_totalCost_le (I := pqPrimIface) pqAtomicSamplers_sizeHonest
    one_le_pqPrimIface_qCost one_le_pqAtomicSamplers_sCost S b ℓ
    (shcrKeyInd1KeyKindAtomicProg S b) (shcrKeyInd1KeyKindAtomicProg_cost S b)
    (shcrKeyInd1KeyKindAtomicProg_size_le S b)

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrBounds
