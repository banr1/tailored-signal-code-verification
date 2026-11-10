/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.StepSimTwoStage -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim

/-!
# Helper Lemmas for Two-Stage `KemShCr` Forgetful Step Simulation

Proves sentinel-remap commutation (`fixShcrLegacySent`), unsupported-query vanishing, clamped
list-scan, and pre/post-RO split evaluation lemmas for `shcrKeyInd1KeyKindAtomicProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimHelpers

open OracleSpec OracleComp
open _root_.SignalPqxdh (
  Setup QueryBudget KeyIndQuery keyIndSpec isKeyIndOnlineQuery isKeyIndRoQuery
  activeSendCount activeSpkCount
)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface pqAtomicSig pqAtomicOps pqPrimIface pqKeyIndCodec
  PB B U32 drKeyT bundleT hdrT sidT
)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps keyIndCodec)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  embedTy embedVal projVal embedEnv mapExpr mapComp exprRename compRename
  embedVal_projVal projVal_embedVal mapExpr_eval mapComp_eval mapSamp_eval exprRename_eval compRename_eval
  tlPrimKeyInd keyIndUnsupportedPrimW finSidToNatExpr liftKeyIndHandle liftKeyIndHandle_eval liftKeyInd2Stage
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (aop)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open _root_.Computational.Proofs.ReductionDsl.StepSimTwoStage (TwoStageForgetSim forgetPreOut)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT RS SCS accQTy bindV buIkB buMk buOpkB buPqspkB buPqspkId buSpkB buSpkId caseOptV caseSumV
  checkProvC checkSigsC corruptB eAny eCaseOpt eFind eMap eqB eqU32 findHonestC findMV freshE
  genOpkB genSpkB hdEkAPk hdIkAPk hdKemCt hdMk hdOpkId hdPqspkId hdSpkId honestPeerC initFinishC
  initGuardE initPrin1KeyB initQTy initSidE isNoneRespE isSomeE keyIndLoopBound keyIndQueryTy
  keyIndRespEntryTy keyIndStateTy
  koskBundleOkC koskSenderOkC kyberCheckE lenB letV nat2Eq nat3Eq natEq oeConsumed oeOpkPk oeOpkSk
  oeUpd onBase optFst optSnd optU32Eq partnerC pauseCheckC pauseTy peIkAPk peSecIKA0 peSecIKAsign
  preCheckC principalEntryTy qHdr qJ qK qKJO qKemDecaps qKemEncaps qO qSigSign qX25519 qX25519Base
  rAccFresh rBundle rDrKey rHdr rInitUnfresh rNone reDrRand reMk recordRespC registerB resolveSigPkC
  revealB revealDhB revealSpkB roB rs sBool sBytes32 sDrKey96 sIndex sRandom64 sbMk sbPqspkPk
  sbPqspkSk sbSpkPk sbSpkSk scBase scChosen scCnt scIR scMk scRR scSIdx scTB scTPk scTSk scUpd seMk
  seUpd shcrAcceptB shcrExtractC shcrFinE shcrInitiateC shcrResumeC shcrStTy spkBundleEntryTy
  stKyb stOpks stPrin stResps stRo stSess stSpks stUpd stUsedN stUsedO testB tryPauseC u32OfNat v
  acceptKeysC acceptNoOpkB acceptOpkB buildSecretsE emptyStE hkdfOrRoC
)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  shcr1KeyActivePostC shcr1KeyActivePreC shcrActiveGenSpkB
  shcrActivePostTailC shcrKeyInd1KeyActiveAtomicProg shcrKeyInd1KeyActiveDslProg
)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  shcr1KeyKindBaseInit shcr1KeyKindBaseInit_unsupported shcr1KeyKindHandlePostC
  shcr1KeyKindHandlePreC shcr1KeyKindInitC shcr1KeyKindResumeC shcrChDoneLeg_unsupported
  shcrExtractLeg_unsupported shcrKeyInd1KeyKindAtomicProg
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  accPayToNatE atomicRNoneE coreAcceptPreRoC dispatchKeyIndQ emptyRoAvlE finPairToNatE
  finTripleToNatE forgetShcrKind initFinishPostRoC initFinishPreRoC initPayToNatE keyIndCoreFuels
  keyIndSentinel lt_keyIndSentinel ren1 ren2 ren3 ren4 ren5 ren6 roAvlTy roListAtomicTy
  roListLegacyTy roShadowQueryC runAt2 runAt3 runAt4 runAt5 runAt6 shcrAccArmPostK shcrAccMidTy
  shcrAcceptPostRoC shcrAcceptPreRoC shcrActiveGenSpkLeg shcrChDoneLeg shcrCorruptLeg
  shcrExtractLeg shcrGenOpkLeg shcrInitArmPostK shcrInitArmPreK shcrInitMidTy shcrInitPrin1KeyLeg
  shcrInitiatePostRoC shcrInitiatePreRoC shcrKindChDoneC shcrKindFinishC shcrKindHandlePostC
  shcrKindHandlePreC shcrKindResumeC shcrKindStTy shcrLiftLegArmK shcrRegKeyLeg shcrResumePostRoC
  shcrResumePreRoC shcrRevDhLeg shcrRevSessLeg shcrRevSpkLeg shcrRoArmK shcrRoListAtomicE
  shcrSetRoRespC shcrTestLeg wkTop3
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  BaseOnlineLenInv CoreInv RoCacheAvlInv ShcrPauseInv ShcrSimInv beq_fixSent_of_le_mOn
  bumpPred_keyIndSimPred_sum checkProvC_min_eq checkSigsC_min_eq corruptB_min_eq dispatchKeyIndQ_eval
  findHonestC_min_eq fixSent fixSent_keyIndSentinel fixSent_of_lt_N_dh fixShcrStSent
  forgetShcrKindActive freshE_min_eq genOpkB_min_eq genSpkB_min_eq honestPeerC_min_eq
  initPrin1KeyB_min_eq isKeyIndOnlineQuery_xor_isRoQuery keyIndSimBounds keyIndSimPred
  koskSenderOkC_min_eq kyberCheckE_min_eq mem_support_sIndex_lt preCheckC_min_eq recordRespC_min_eq
  revealB_min_eq revealDhB_min_eq revealSpkB_min_eq roShadowQueryC_eval_sim runAt2_eval runAt3_eval
  runAt4_eval runAt5_eval runAt6_eval shcrActiveGenSpkLeg_min_eq stAdvList stKybList stOpksList
  stPrinList stRespsList stRoList stSessList stSpksList stUsedNList stUsedOList
  take_min_eq_of_length_le testB_min_eq
)

/-- Legacy-signature counterpart of `fixShcrStSent` remapping `scSIdx` via `fixSent S b`. -/
@[expose] def fixShcrLegacySent (S : Setup) (b : QueryBudget)
    (s : Ty.denote shcrStTy) : Ty.denote shcrStTy :=
  (s.1, (s.2.1, (s.2.2.1, (s.2.2.2.1, (s.2.2.2.2.1,
    (s.2.2.2.2.2.1, (s.2.2.2.2.2.2.1, (fixSent S b s.2.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2.2))))))))

theorem forgetShcrKindActive_eq_embed (S : Setup) (b : QueryBudget)
    (sK : shcrKindStTy.denote) :
    forgetShcrKindActive S b sK =
      embedVal shcrStTy (fixShcrLegacySent S b (projVal shcrStTy sK.1)) := by
  rcases sK with ⟨⟨base, tb, tpk, tsk, cnt, ir, rr, sIdx, chosen⟩, roAvl⟩
  change (base, (tb, (tpk, (tsk, (cnt, (ir, (rr, (fixSent S b sIdx, chosen)))))))) =
    (embedVal keyIndStateTy (projVal keyIndStateTy base),
      (embedVal (.opt (.prod .nat .nat)) (projVal (.opt (.prod .nat .nat)) tb),
        (embedVal (_root_.SignalPqxdh.LegacyCosted.B 1568) (projVal (_root_.SignalPqxdh.LegacyCosted.B 1568) tpk),
          (embedVal (_root_.SignalPqxdh.LegacyCosted.B 3168) (projVal (_root_.SignalPqxdh.LegacyCosted.B 3168) tsk),
            (cnt,
              (embedVal _ (projVal _ ir),
                (embedVal _ (projVal _ rr),
                  (fixSent S b sIdx,
                    embedVal (_root_.SignalPqxdh.LegacyCosted.B 1568)
                      (projVal (_root_.SignalPqxdh.LegacyCosted.B 1568) chosen)))))))))
  simp only [embedVal_projVal]

theorem shcrRoListAtomicE_eval {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy shcrStTy)) (env : Env Γ) :
    (shcrRoListAtomicE sE).eval env =
      embedVal roListLegacyTy (stRoList (projVal shcrStTy (sE.eval env)).1) := by
  let sA := sE.eval env
  let sL := projVal shcrStTy sA
  have hsA : sA = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sA).symm
  simp only [shcrRoListAtomicE, Expr.eval]
  rw [exprRename_eval _ (fun {_} => ren1) (.cons sA .nil) (.cons sA env)
    (fun v => by cases v with | zero => rfl | succ v' => nomatch v')]
  have hEnv : Env.cons sA Env.nil = embedEnv (Env.cons sL Env.nil) := by
    change Env.cons sA Env.nil = Env.cons (embedVal shcrStTy sL) Env.nil
    rw [hsA]
  rw [hEnv, mapExpr_eval]
  rfl

section UnsupportedHelpers

open _root_.SignalPqxdh.LegacyCosted (pqSamplers)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  anyMV isAdvRegC isGameOpkC isGameSpkC keyIndSessionEntryTy
  qHkdfDerive96 qIsCanonical qKemKeyGen qPow8 qSigPkGen qSigVerify
)

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] _root_.SignalPqxdh.LegacyCosted.pqPrimIface pqSamplers

private def zPrimWS : _root_.SignalPqxdh.LegacyCosted.pqPrimIface.smp.Samp → ℕ := fun _ => 0

@[local simp] private theorem letV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ a) (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (letV e k).queries w ws = (k .zero).queries w ws := by
  simp [letV, Comp.queries]

@[local simp] private theorem bindV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (c : Comp pqxdhOps I Γ a) (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (bindV c k).queries w ws = c.queries w ws + (k .zero).queries w ws :=
  rfl

@[local simp] private theorem caseOptV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ (.opt a)) (cNone : Comp pqxdhOps I Γ b)
    (cSome : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (caseOptV e cNone cSome).queries w ws =
      max (cNone.queries w ws) ((cSome .zero).queries w ws) :=
  rfl

@[local simp] private theorem caseSumV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b c : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ (.sum a b))
    (cL : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) c)
    (cR : Var (b :: Γ) b → Comp pqxdhOps I (b :: Γ) c) :
    (caseSumV e cL cR).queries w ws =
      max ((cL .zero).queries w ws) ((cR .zero).queries w ws) :=
  rfl

@[local simp] private theorem findMV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (fuel : ℕ)
    (xs : Expr pqxdhOps Γ (.list a))
    (p : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) .bool) :
    (findMV fuel xs p).queries w ws = fuel * (p .zero).queries w ws := by
  simp [findMV, Comp.queries]

@[local simp] private theorem anyMV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (fuel : ℕ)
    (xs : Expr pqxdhOps Γ (.list a))
    (p : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) .bool) :
    (anyMV fuel xs p).queries w ws = fuel * (p .zero).queries w ws := by
  simp [anyMV, Comp.queries]

@[local simp] private theorem sBool_unsup {Γ : List PT} : (sBool (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sBytes32_unsup {Γ : List PT} : (sBytes32 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sRandom64_unsup {Γ : List PT} : (sRandom64 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sDrKey96_unsup {Γ : List PT} : (sDrKey96 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} : (sIndex N (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32))) : (qX25519 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519Base_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (qX25519Base e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qPow8_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (qPow8 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qIsCanonical_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (qIsCanonical e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigPkGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (qSigPkGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigSign_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (.prod (_root_.SignalPqxdh.LegacyCosted.B m) (_root_.SignalPqxdh.LegacyCosted.B 64)))) : (qSigSign m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigVerify_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (.prod (_root_.SignalPqxdh.LegacyCosted.B m) (_root_.SignalPqxdh.LegacyCosted.B 64)))) : (qSigVerify m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemKeyGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B 64)) : (qKemKeyGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemEncaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (_root_.SignalPqxdh.LegacyCosted.B 1568) (_root_.SignalPqxdh.LegacyCosted.B 32))) : (qKemEncaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemDecaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (_root_.SignalPqxdh.LegacyCosted.B 3168) (_root_.SignalPqxdh.LegacyCosted.B 1568))) : (qKemDecaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qHkdfDerive96_unsup (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (_root_.SignalPqxdh.LegacyCosted.B w)) : (qHkdfDerive96 w e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem findHonestC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (findHonestC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [findHonestC, Comp.queries]
@[local simp] private theorem isAdvRegC_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (isAdvRegC K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isAdvRegC, Comp.queries]
@[local simp] private theorem isGameSpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (isGameSpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameSpkC, Comp.queries]
@[local simp] private theorem isGameOpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (isGameOpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameOpkC, Comp.queries]
@[local simp] private theorem koskBundleOkC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (koskBundleOkC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskBundleOkC, Comp.queries]
@[local simp] private theorem koskSenderOkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (koskSenderOkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskSenderOkC, Comp.queries]
@[local simp] private theorem resolveSigPkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (resolveSigPkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [resolveSigPkC, Comp.queries]
@[local simp] private theorem honestPeerC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) : (honestPeerC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [honestPeerC, Comp.queries]
@[local simp] private theorem checkProvC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (checkProvC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [checkProvC, Comp.queries]
@[local simp] private theorem partnerC_unsup {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (partnerC (Δ := Δ) s r).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem recordRespC_unsup (S : Setup) (K : Nat) {Δ : List PT} (p : Expr pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) : (recordRespC S K p).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [recordRespC, Comp.queries]
@[local simp] private theorem hkdfOrRoC_true_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 192)) : (hkdfOrRoC K true st sec).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [hkdfOrRoC, Comp.queries]
@[local simp] private theorem acceptKeysC_unsup {Δ : List PT} (inp : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.accInpTy) : (acceptKeysC inp).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl

@[local simp] private theorem initFinishC_true_unsup (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [initFinishC, Comp.queries]

@[local simp] private theorem preCheckC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [preCheckC, Comp.queries]

@[local simp] private theorem checkSigsC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [checkSigsC, Comp.queries]

@[local simp] private theorem onBase_unsup {Γ₁ Δ : List PT} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (keyIndStateTy :: Δ) RS) :
    (onBase (Δ := Δ) s br).queries keyIndUnsupportedPrimW zPrimWS =
      (br .zero).queries keyIndUnsupportedPrimW zPrimWS := by
  simp [onBase, Comp.queries]

theorem hkdfOrRoC_unsup (K : Nat) :
    (hkdfOrRoC K true
      (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
      .zero (.var (.succ .zero))).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  hkdfOrRoC_true_unsup K .zero (.var (.succ .zero))

theorem shcr1KeyActiveInit_unsup (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).init.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyInd1KeyActiveDslProg S b).init.queries keyIndUnsupportedPrimW zPrimWS = 0
  unfold shcrKeyInd1KeyActiveDslProg; dsimp only; split_ifs <;> simp [Comp.queries]

private theorem shcr1KeyActivePostC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyActivePostC (Δ := Δ) S K s q).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, shcr1KeyActivePostC, shcrActivePostTailC,
    shcrActiveGenSpkB, shcrInitiateC, shcrAcceptB, initPrin1KeyB, corruptB, genSpkB, genOpkB,
    acceptOpkB, acceptNoOpkB, testB, revealB, roB, revealDhB, registerB, revealSpkB, Comp.queries]

theorem shcr1KeyActiveHandlePost_unsup (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcr1KeyActivePostC_unsup S (keyIndLoopBound b)
    (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy])
    .zero .zero

theorem shcr1KeyActiveHandlePre_unsup (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).handlePre.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcr1KeyActivePreC S (keyIndLoopBound b)
    (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy])
    .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcr1KeyActivePreC, pauseCheckC, tryPauseC, shcr1KeyActivePostC_unsup, Comp.queries]

theorem shcr1KeyActiveResume_unsup (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).resume.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyInd1KeyActiveDslProg S b).resume.queries keyIndUnsupportedPrimW zPrimWS = 0
  unfold shcrKeyInd1KeyActiveDslProg; dsimp only
  simp [shcrResumeC, letV, bindV, Comp.queries]

theorem shcr1KeyActiveFinish_unsup (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).finish.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyInd1KeyActiveDslProg S b).finish.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrKeyInd1KeyActiveDslProg, shcrExtractC, Comp.queries]

theorem shcrSetRoRespC_unsup :
    shcrSetRoRespC.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

private theorem initFinishPreRoC_unsup {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (bu : Var Γ₁ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₂ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₃ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₄ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (initFinishPreRoC (Δ := Δ) bu uE ekSk sc).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [initFinishPreRoC, Comp.queries]

private theorem initFinishPostRoC_unsup (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk : Var Γ₇ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk : Var Γ₈ _root_.SignalPqxdh.LegacyCosted.drKeyT) (roNew : Var Γ₉ roListLegacyTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ] :
    (initFinishPostRoC (Δ := Δ) S K st sid bu uE ekSk sc ekPk dk roNew).queries
      keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [initFinishPostRoC, Comp.queries]

theorem shcrInitiatePreRoC_unsup (S : Setup) (K : Nat) (opk : Bool) :
    (shcrInitiatePreRoC S K opk).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrInitiatePreRoC S K opk).queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrInitiatePreRoC, initFinishPreRoC_unsup, Comp.queries]

theorem shcrInitiatePostRoC_unsup (S : Setup) (K : Nat) :
    (shcrInitiatePostRoC S K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrInitiatePostRoC S K).queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrInitiatePostRoC, initFinishPostRoC_unsup, Comp.queries]

theorem shcrResumePreRoC_unsup :
    shcrResumePreRoC.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change shcrResumePreRoC.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrResumePreRoC, initFinishPreRoC_unsup, Comp.queries]

theorem shcrResumePostRoC_unsup (S : Setup) (K : Nat) :
    (shcrResumePostRoC S K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrResumePostRoC S K).queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrResumePostRoC, initFinishPostRoC_unsup, Comp.queries]

theorem shcrAcceptPreRoC_unsup (S : Setup) (K : Nat) (opk : Bool) :
    (shcrAcceptPreRoC S K opk).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrAcceptPreRoC S K opk).queries keyIndUnsupportedPrimW zPrimWS = 0
  cases opk <;> simp [shcrAcceptPreRoC, coreAcceptPreRoC, Comp.queries]

theorem shcrAcceptPostRoC_unsup (S : Setup) (K : Nat) (opk : Bool) :
    (shcrAcceptPostRoC S K opk).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrAcceptPostRoC S K opk).queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrAcceptPostRoC, Comp.queries]

theorem tryPauseC_unsup (S : Setup) (K : Nat) (opk : Bool) :
    (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy])
      .zero .zero).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy])
    .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [tryPauseC, Comp.queries]

theorem shcrInitPrin1KeyLeg_unsup (K : Nat) :
    (shcrInitPrin1KeyLeg K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrInitPrin1KeyLeg K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrInitPrin1KeyLeg, initPrin1KeyB, Comp.queries]
theorem shcrCorruptLeg_unsup (K : Nat) :
    (shcrCorruptLeg K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrCorruptLeg K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrCorruptLeg, corruptB, Comp.queries]
theorem shcrActiveGenSpkLeg_unsup (S : Setup) (K : Nat) :
    (shcrActiveGenSpkLeg S K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrActiveGenSpkLeg S K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrActiveGenSpkLeg, genSpkB, Comp.queries]
theorem shcrGenOpkLeg_unsup (K : Nat) :
    (shcrGenOpkLeg K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrGenOpkLeg K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrGenOpkLeg, genOpkB, Comp.queries]
theorem shcrTestLeg_unsup (K : Nat) :
    (shcrTestLeg K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrTestLeg K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrTestLeg, testB, Comp.queries]
theorem shcrRevDhLeg_unsup (K : Nat) :
    (shcrRevDhLeg K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrRevDhLeg K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrRevDhLeg, revealDhB, Comp.queries]
theorem shcrRevSessLeg_unsup (K : Nat) :
    (shcrRevSessLeg K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrRevSessLeg K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrRevSessLeg, revealB, Comp.queries]
theorem shcrRegKeyLeg_unsup : shcrRegKeyLeg.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := rfl
theorem shcrRevSpkLeg_unsup (K : Nat) :
    (shcrRevSpkLeg K).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrRevSpkLeg K).queries keyIndUnsupportedPrimW zPrimWS = 0; simp [shcrRevSpkLeg, revealSpkB, Comp.queries]

end UnsupportedHelpers

theorem fixSent_of_lt_activeSendCount {S : Setup} {b : QueryBudget} {k : ℕ}
    (hk : k < activeSendCount S b.q_on) :
    fixSent S b k = k := by
  unfold activeSendCount fixSent keyIndSentinel at *
  split_ifs with h <;> omega

theorem eFind_eq_of_le {Γ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eFind K₁ xs p).eval env = (eFind K₂ xs p).eval env := by
  simp only [eFind, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

theorem eAny_eq_of_le {Γ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eAny K₁ xs p).eval env = (eAny K₂ xs p).eval env := by
  simp only [eAny, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

theorem eMap_eq_of_le {Γ : List PT} {τ₁ τ₂ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eMap K₁ xs f).eval env = (eMap K₂ xs f).eval env := by
  simp only [eMap, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

theorem findMV_eq_of_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (findMV K₁ xs p).eval env = (findMV K₂ xs p).eval env := by
  simp only [findMV, Comp.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

theorem findMV_min_eq_of_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ : PT} {K₁ K₂ N : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (findMV (min K₁ N) xs p).eval env = (findMV (min K₂ N) xs p).eval env := by
  simp only [findMV, Comp.eval, take_min_eq_of_length_le (xs.eval env) hLen hLe]

theorem shcrLiftLegArmK_eval_eq (S : Setup)
    {A : Ty pqAtomicSig} {P : Ty pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (leg : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, P] SCS)
    (hUnsup : leg.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (a : A.denote) (sK : shcrKindStTy.denote) (q : ((pqKeyIndCodec S).Q).denote)
    (p : P.denote)
    (hPay : payE.eval (.cons a (.cons sK (.cons q .nil))) = embedVal P p) :
    (shcrLiftLegArmK S payE leg).eval (.cons a (.cons sK (.cons q .nil))) =
      (fun rs : Ty.denote SCS => (embedVal _ rs.1, (embedVal shcrStTy rs.2, sK.2))) <$>
        leg.eval (.cons (projVal shcrStTy sK.1) (.cons p .nil)) := by
  let sL := projVal shcrStTy sK.1
  have hs1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  simp only [shcrLiftLegArmK, Comp.eval]
  rw [runAt2_eval]
  have hEnv : Env.cons ((Expr.fst Expr.v1 :
      Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy shcrStTy)).eval
        (.cons a (.cons sK (.cons q .nil))))
      (.cons (payE.eval (.cons a (.cons sK (.cons q .nil)))) .nil) =
      embedEnv (.cons sL (.cons p .nil)) := by
    simp only [Expr.eval, Expr.v1, Env.get, hs1, hPay]
  rw [hEnv, mapComp_eval tlPrimKeyInd leg hUnsup]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
    Expr.eval, Expr.v0, Expr.v2, Env.get]
  rfl

theorem shcrLiftLegArmK_map_forget (S : Setup) (b : QueryBudget)
    {A : Ty pqAtomicSig} {P : Ty pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (leg : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, P] SCS)
    (hUnsup : leg.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (a : A.denote) (sK : shcrKindStTy.denote) (q : ((pqKeyIndCodec S).Q).denote)
    (p : P.denote)
    (hPay : payE.eval (.cons a (.cons sK (.cons q .nil))) = embedVal P p) :
    Prod.map id (forgetShcrKindActive S b) <$>
      (shcrLiftLegArmK S payE leg).eval (.cons a (.cons sK (.cons q .nil))) =
    embedVal SCS <$> (Prod.map id (fixShcrLegacySent S b) <$>
      leg.eval (.cons (projVal shcrStTy sK.1) (.cons p .nil))) := by
  rw [shcrLiftLegArmK_eval_eq S payE leg hUnsup a sK q p hPay]
  simp only [Functor.map_map]
  congr 1

theorem shcrExtractLeg_eq_active (S : Setup) (b : QueryBudget)
    (sL : Ty.denote shcrStTy) (bOut : Bool)
    (y : Ty.denote (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    {K_on : ℕ} (hRR : (sL.2.2.2.2.2.2.1).length ≤ K_on) (hLe : K_on ≤ b.q_total) :
    (shcrExtractLeg K_on).eval (.cons sL (.cons bOut (.cons y .nil))) =
      (shcrExtractC (Γ₁ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
          (_root_.SignalPqxdh.LegacyCosted.B 1568)])
        (Γ₃ := [shcrStTy, .bool, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
          (_root_.SignalPqxdh.LegacyCosted.B 1568)])
        (Δ := [shcrStTy, .bool, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
          (_root_.SignalPqxdh.LegacyCosted.B 1568)])
        b.q_total .zero .zero).eval
        (.cons (fixShcrLegacySent S b sL) (.cons bOut (.cons y .nil))) := by
  simp only [shcrExtractLeg, shcrExtractC, bindV, findMV, scRR, scTSk, scChosen, scTPk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rrCt,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optBytesEq,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.orE,
    qKemDecaps, eqB, eCaseOpt, Ext.wk, fixShcrLegacySent, v,
    Comp.eval, Expr.eval, Env.get,
    List.take_of_length_le hRR, List.take_of_length_le (Nat.le_trans hRR hLe)]
  rfl

theorem embedVal_roList_eq (l : roListLegacyTy.denote) :
    embedVal roListLegacyTy l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k, r, c, p⟩
    exact congrArg (_ :: ·) ih

@[simp] theorem env_get_succ {Γ : List PT} {σ τ : PT} (x : Var Γ τ) (a : σ.denote) (env : Env Γ) :
    (Env.cons a env).get (.succ x) = env.get x := rfl

@[simp] theorem env_get_zero {Γ : List PT} {τ : PT} (a : τ.denote) (env : Env Γ) :
    (Env.cons a env).get .zero = a := rfl

@[simp] theorem ext_step_wk {Γ Δ : List PT} {σ τ : PT} [h : Ext Γ Δ] (x : Var Γ τ) :
    (@Ext.step Γ Δ σ h).wk x = .succ (h.wk x) := rfl

@[simp] theorem ext_refl_wk {Γ : List PT} {τ : PT} (x : Var Γ τ) :
    (@Ext.refl Γ).wk x = x := rfl

@[simp] theorem v_eval_cons {Γ Δ : List PT} {σ τ : PT} [Ext Γ Δ]
    (x : Var Γ τ) (a : σ.denote) (env : Env Δ) :
    (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v Γ (σ :: Δ) τ Ext.step x).eval
        (.cons a env) =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v x).eval env := rfl

@[simp] theorem v_zero_eval {Γ : List PT} {τ : PT} (a : τ.denote) (env : Env Γ) :
    (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v (τ :: Γ) (τ :: Γ) τ Ext.refl .zero).eval
        (.cons a env) = a := rfl

theorem ro_bounds_of_le (S : Setup) (b : QueryBudget) {c : Fin 3 → ℕ} {len : ℕ}
    (hc : ∀ j, c j ≤ keyIndSimBounds b j) (hSum : c 0 + c 1 = c 2) (hLen : len ≤ c 2) :
    len < keyIndLoopBound b ∧ len + 1 ≤ (keyIndCoreFuels S b).roCap := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  simp only [keyIndSimBounds, keyIndLoopBound, keyIndCoreFuels] at h0 h1 h2 ⊢
  omega

theorem initFinishPostRoC_fuel_eq (S : Setup) {K₁ K₂ : ℕ} {c : Fin 3 → ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk : Var Γ₇ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk : Var Γ₈ _root_.SignalPqxdh.LegacyCosted.drKeyT) (roNew : Var Γ₉ roListLegacyTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ]
    (env : Env Δ)
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc0 : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (initFinishPostRoC (Δ := Δ) S K₁ st sid bu uE ekSk sc ekPk dk roNew).eval env =
      (initFinishPostRoC (Δ := Δ) S K₂ st sid bu uE ekSk sc ekPk dk roNew).eval env := by
  have hPrin  := Nat.le_trans hInv.prin_le hc0
  have hResps := Nat.le_trans hInv.resps_le hc0
  simp only [initFinishPostRoC, letV, bindV, Comp.eval, pure_bind]
  rw [honestPeerC_min_eq S st _ _ (by simpa using hPrin) hLe]
  congr 1; funext hp
  rw [checkProvC_min_eq S st bu _ (by simpa using hInv) hc0 hLe]
  congr 1; funext prov
  rw [findMV_min_eq_of_le _ _ _ (by simpa [stResps, stRespsList, Expr.eval] using hResps) hLe]
  congr 1; funext found
  congr 1; funext drr
  rw [findHonestC_min_eq S st _ _ (by simpa using hPrin) hLe]

theorem initFinishPostRoC_mem_support (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk : Var Γ₇ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk : Var Γ₈ _root_.SignalPqxdh.LegacyCosted.drKeyT) (roNew : Var Γ₉ roListLegacyTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ]
    (env : Env Δ) {r : Ty.denote RS}
    (hr : r ∈ support ((initFinishPostRoC (Δ := Δ) S K st sid bu uE ekSk sc ekPk dk roNew).eval env)) :
    let bSt := (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env
    stPrinList r.2 = stPrinList bSt ∧ stSpksList r.2 = stSpksList bSt ∧
    stOpksList r.2 = stOpksList bSt ∧ (stSessList r.2).length = (stSessList bSt).length + 1 ∧
    stRespsList r.2 = stRespsList bSt ∧ stUsedOList r.2 = stUsedOList bSt ∧
    stUsedNList r.2 = stUsedNList bSt ∧ stKybList r.2 = stKybList bSt ∧
    stRoList r.2 = (v roNew).eval env ∧ stAdvList r.2 = stAdvList bSt := by
  simp only [initFinishPostRoC, letV, bindV, Comp.eval, pure_bind, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨hp, _, prov, _, found, _, drr, _, fh, _, rfl⟩
  dsimp only [rs, stUpd, stPrinList, stSpksList, stOpksList, stSessList, stRespsList,
    stUsedOList, stUsedNList, stKybList, stRoList, stAdvList,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb,
    v_eval_cons, Expr.eval]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hkdfOrRoC_eval_congr (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (secE : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 192)) (env : Env Δ) :
    (hkdfOrRoC K true st secE).eval env =
      (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero))).eval
        (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)
          (.cons (secE.eval env) .nil)) := by
  simp only [hkdfOrRoC, ↓reduceIte, letV, caseOptV, bindV, Comp.eval, pure_bind,
    eFind, stRo, v_eval_cons, v_zero_eval, Expr.eval, Env.get]
  rcases List.find? (fun x => x.1 == secE.eval env)
      (List.take K (env.get (Ext.wk st)).2.2.2.2.2.2.2.2.2.1) with _ | val <;>
    simp [Expr.eval, v, Ext.wk]

private theorem letV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {σ τ : PT} (e : Expr pqxdhOps Γ σ)
    (k : Var (σ :: Γ) σ → Comp pqxdhOps I (σ :: Γ) τ) (env : Env Γ) :
    (letV e k).eval env = (k .zero).eval (.cons (e.eval env) env) := by
  simp [letV, Comp.eval]

private theorem bindV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {σ τ : PT} (c : Comp pqxdhOps I Γ σ)
    (k : Var (σ :: Γ) σ → Comp pqxdhOps I (σ :: Γ) τ) (env : Env Γ) :
    (bindV c k).eval env = c.eval env >>= fun x => (k .zero).eval (.cons x env) := rfl

private def mapVar9 {T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ : PT} {Δ : List PT}
    (x₁ : Var Δ T₁) (x₂ : Var Δ T₂) (x₃ : Var Δ T₃) (x₄ : Var Δ T₄) (x₅ : Var Δ T₅)
    (x₆ : Var Δ T₆) (x₇ : Var Δ T₇) (x₈ : Var Δ T₈) (x₉ : Var Δ T₉) :
    ∀ {a}, Var [T₁, T₂, T₃, T₄, T₅, T₆, T₇, T₈, T₉] a → Var Δ a
  | _, .zero => x₁ | _, .succ .zero => x₂ | _, .succ (.succ .zero) => x₃
  | _, .succ (.succ (.succ .zero)) => x₄ | _, .succ (.succ (.succ (.succ .zero))) => x₅
  | _, .succ (.succ (.succ (.succ (.succ .zero)))) => x₆
  | _, .succ (.succ (.succ (.succ (.succ (.succ .zero))))) => x₇
  | _, .succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))) => x₈
  | _, .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) => x₉

private theorem mapVar9_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ R : PT} {Δ : List PT}
    (x₁ : Var Δ T₁) (x₂ : Var Δ T₂) (x₃ : Var Δ T₃) (x₄ : Var Δ T₄) (x₅ : Var Δ T₅)
    (x₆ : Var Δ T₆) (x₇ : Var Δ T₇) (x₈ : Var Δ T₈) (x₉ : Var Δ T₉)
    (c : Comp pqxdhOps I [T₁, T₂, T₃, T₄, T₅, T₆, T₇, T₈, T₉] R) (env : Env Δ) :
    (compRename (mapVar9 x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) c).eval env =
      c.eval (.cons (env.get x₁) (.cons (env.get x₂) (.cons (env.get x₃)
        (.cons (env.get x₄) (.cons (env.get x₅) (.cons (env.get x₆)
          (.cons (env.get x₇) (.cons (env.get x₈) (.cons (env.get x₉) .nil))))))))) := by
  refine compRename_eval _ _ _ _ fun w => ?_
  match w with
  | .zero => rfl | .succ .zero => rfl | .succ (.succ .zero) => rfl
  | .succ (.succ (.succ .zero)) => rfl | .succ (.succ (.succ (.succ .zero))) => rfl
  | .succ (.succ (.succ (.succ (.succ .zero)))) => rfl
  | .succ (.succ (.succ (.succ (.succ (.succ .zero))))) => rfl
  | .succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))) => rfl
  | .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) => rfl
  | .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ w')))))))) => nomatch w'

private abbrev postRoCanonCtx : List PT :=
  [roListLegacyTy, _root_.SignalPqxdh.LegacyCosted.drKeyT, _root_.SignalPqxdh.LegacyCosted.B 32,
   .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
   _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
   _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy]

private abbrev postRoCanonComp (S : Setup) (K : ℕ) :=
  initFinishPostRoC S K
    (Γ₁ := [keyIndStateTy]) (Γ₂ := [_root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
    (Γ₃ := [_root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
    (Γ₄ := [.prod .nat principalEntryTy, _root_.SignalPqxdh.LegacyCosted.bundleT,
      _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
    (Γ₅ := [_root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
      _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
    (Γ₆ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
      _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
    (Γ₇ := [_root_.SignalPqxdh.LegacyCosted.B 32,
      .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
      _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
    (Γ₈ := [_root_.SignalPqxdh.LegacyCosted.drKeyT, _root_.SignalPqxdh.LegacyCosted.B 32,
      .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
      _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
    (Γ₉ := postRoCanonCtx) (Δ := postRoCanonCtx)
    .zero .zero .zero .zero .zero .zero .zero .zero .zero

private theorem initFinishPostRoC_eval_canon (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk : Var Γ₇ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk : Var Γ₈ _root_.SignalPqxdh.LegacyCosted.drKeyT) (roNew : Var Γ₉ roListLegacyTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ] (env : Env Δ) :
    (initFinishPostRoC (Δ := Δ) S K st sid bu uE ekSk sc ekPk dk roNew).eval env =
      (postRoCanonComp S K).eval
        (.cons ((v roNew).eval env) (.cons ((v dk).eval env) (.cons ((v ekPk).eval env)
          (.cons ((v sc).eval env) (.cons ((v ekSk).eval env) (.cons ((v uE).eval env)
            (.cons ((v bu).eval env) (.cons ((v sid).eval env) (.cons ((v st).eval env) .nil))))))))) := by
  have hSyn : initFinishPostRoC (Δ := Δ) S K st sid bu uE ekSk sc ekPk dk roNew =
      compRename (mapVar9 (Ext.wk roNew) (Ext.wk dk) (Ext.wk ekPk) (Ext.wk sc) (Ext.wk ekSk)
        (Ext.wk uE) (Ext.wk bu) (Ext.wk sid) (Ext.wk st)) (postRoCanonComp S K) := rfl
  rw [hSyn, mapVar9_eval]; rfl

private theorem bind_congr_eq {ι : Type} {S : OracleSpec ι} {α β : Type}
    {m₁ m₂ : OracleComp S α} {f₁ f₂ : α → OracleComp S β}
    (hm : m₁ = m₂) (hf : ∀ x, f₁ x = f₂ x) :
    (m₁ >>= f₁) = (m₂ >>= f₂) :=
  hm ▸ bind_congr hf

private def mapVar4 {T₁ T₂ T₃ T₄ : PT} {Δ : List PT}
    (x₁ : Var Δ T₁) (x₂ : Var Δ T₂) (x₃ : Var Δ T₃) (x₄ : Var Δ T₄) :
    ∀ {a}, Var [T₁, T₂, T₃, T₄] a → Var Δ a
  | _, .zero => x₁
  | _, .succ .zero => x₂
  | _, .succ (.succ .zero) => x₃
  | _, .succ (.succ (.succ .zero)) => x₄

private theorem mapVar4_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {T₁ T₂ T₃ T₄ R : PT} {Δ : List PT}
    (x₁ : Var Δ T₁) (x₂ : Var Δ T₂) (x₃ : Var Δ T₃) (x₄ : Var Δ T₄)
    (c : Comp pqxdhOps I [T₁, T₂, T₃, T₄] R) (env : Env Δ) :
    (compRename (mapVar4 x₁ x₂ x₃ x₄) c).eval env =
      c.eval (.cons (env.get x₁) (.cons (env.get x₂)
        (.cons (env.get x₃) (.cons (env.get x₄) .nil)))) := by
  refine compRename_eval _ _ _ _ fun w => ?_
  match w with
  | .zero => rfl
  | .succ .zero => rfl
  | .succ (.succ .zero) => rfl
  | .succ (.succ (.succ .zero)) => rfl
  | .succ (.succ (.succ (.succ w'))) => nomatch w'

private def mapVar6 {T₁ T₂ T₃ T₄ T₅ T₆ : PT} {Δ : List PT}
    (x₁ : Var Δ T₁) (x₂ : Var Δ T₂) (x₃ : Var Δ T₃)
    (x₄ : Var Δ T₄) (x₅ : Var Δ T₅) (x₆ : Var Δ T₆) :
    ∀ {a}, Var [T₁, T₂, T₃, T₄, T₅, T₆] a → Var Δ a
  | _, .zero => x₁
  | _, .succ .zero => x₂
  | _, .succ (.succ .zero) => x₃
  | _, .succ (.succ (.succ .zero)) => x₄
  | _, .succ (.succ (.succ (.succ .zero))) => x₅
  | _, .succ (.succ (.succ (.succ (.succ .zero)))) => x₆

private theorem mapVar6_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {T₁ T₂ T₃ T₄ T₅ T₆ R : PT} {Δ : List PT}
    (x₁ : Var Δ T₁) (x₂ : Var Δ T₂) (x₃ : Var Δ T₃)
    (x₄ : Var Δ T₄) (x₅ : Var Δ T₅) (x₆ : Var Δ T₆)
    (c : Comp pqxdhOps I [T₁, T₂, T₃, T₄, T₅, T₆] R) (env : Env Δ) :
    (compRename (mapVar6 x₁ x₂ x₃ x₄ x₅ x₆) c).eval env =
      c.eval (.cons (env.get x₁) (.cons (env.get x₂) (.cons (env.get x₃)
        (.cons (env.get x₄) (.cons (env.get x₅) (.cons (env.get x₆) .nil)))))) := by
  refine compRename_eval _ _ _ _ fun w => ?_
  match w with
  | .zero => rfl
  | .succ .zero => rfl
  | .succ (.succ .zero) => rfl
  | .succ (.succ (.succ .zero)) => rfl
  | .succ (.succ (.succ (.succ .zero))) => rfl
  | .succ (.succ (.succ (.succ (.succ .zero)))) => rfl
  | .succ (.succ (.succ (.succ (.succ (.succ w'))))) => nomatch w'

private abbrev preRoCanonCtx : List PT :=
  [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
   _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
   _root_.SignalPqxdh.LegacyCosted.bundleT]

private theorem initFinishPreRoC_eval_canon
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (bu : Var Γ₁ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₂ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₃ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₄ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (env : Env Δ) :
    (initFinishPreRoC (Δ := Δ) bu uE ekSk sc).eval env =
      (initFinishPreRoC
        (Γ₁ := [_root_.SignalPqxdh.LegacyCosted.bundleT])
        (Γ₂ := [.prod .nat principalEntryTy, _root_.SignalPqxdh.LegacyCosted.bundleT])
        (Γ₃ := [_root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
          _root_.SignalPqxdh.LegacyCosted.bundleT])
        (Γ₄ := preRoCanonCtx) (Δ := preRoCanonCtx)
        .zero .zero .zero .zero).eval
        (.cons ((v sc).eval env) (.cons ((v ekSk).eval env)
          (.cons ((v uE).eval env) (.cons ((v bu).eval env) .nil)))) := by
  have hSyn : initFinishPreRoC (Δ := Δ) bu uE ekSk sc =
      compRename (mapVar4 (Ext.wk sc) (Ext.wk ekSk) (Ext.wk uE) (Ext.wk bu))
        (initFinishPreRoC
          (Γ₁ := [_root_.SignalPqxdh.LegacyCosted.bundleT])
          (Γ₂ := [.prod .nat principalEntryTy, _root_.SignalPqxdh.LegacyCosted.bundleT])
          (Γ₃ := [_root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
            _root_.SignalPqxdh.LegacyCosted.bundleT])
          (Γ₄ := preRoCanonCtx) (Δ := preRoCanonCtx)
          .zero .zero .zero .zero) := rfl
  rw [hSyn, mapVar4_eval]
  rfl

private abbrev initFinishCanonCtx : List PT :=
  [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
   _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
   _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy]

private theorem initFinishC_eval_canon (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ]
    (env : Env Δ) :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).eval env =
      (initFinishC true S K
        (Γ₁ := [keyIndStateTy]) (Γ₂ := [_root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
        (Γ₃ := [_root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
        (Γ₄ := [.prod .nat principalEntryTy, _root_.SignalPqxdh.LegacyCosted.bundleT,
          _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
        (Γ₅ := [_root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
          _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
        (Γ₆ := initFinishCanonCtx) (Δ := initFinishCanonCtx)
        .zero .zero .zero .zero .zero .zero).eval
        (.cons ((v sc).eval env) (.cons ((v ekSk).eval env) (.cons ((v uE).eval env)
          (.cons ((v bu).eval env) (.cons ((v sid).eval env) (.cons ((v st).eval env) .nil)))))) := by
  have hSyn : initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc =
      compRename (mapVar6 (Ext.wk sc) (Ext.wk ekSk) (Ext.wk uE) (Ext.wk bu) (Ext.wk sid) (Ext.wk st))
        (initFinishC true S K
          (Γ₁ := [keyIndStateTy]) (Γ₂ := [_root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
          (Γ₃ := [_root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
          (Γ₄ := [.prod .nat principalEntryTy, _root_.SignalPqxdh.LegacyCosted.bundleT,
            _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
          (Γ₅ := [_root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
            _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
          (Γ₆ := initFinishCanonCtx) (Δ := initFinishCanonCtx)
          .zero .zero .zero .zero .zero .zero) := rfl
  rw [hSyn, mapVar6_eval]
  rfl

private def mapVar2 {T₁ T₂ : PT} {Δ : List PT} (x₁ : Var Δ T₁) (x₂ : Var Δ T₂) :
    ∀ {a}, Var [T₁, T₂] a → Var Δ a
  | _, .zero => x₁
  | _, .succ .zero => x₂

private theorem mapVar2_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {T₁ T₂ R : PT} {Δ : List PT} (x₁ : Var Δ T₁) (x₂ : Var Δ T₂)
    (c : Comp pqxdhOps I [T₁, T₂] R) (env : Env Δ) :
    (compRename (mapVar2 x₁ x₂) c).eval env =
      c.eval (.cons (env.get x₁) (.cons (env.get x₂) .nil)) := by
  refine compRename_eval _ _ _ _ fun w => ?_
  match w with | .zero => rfl | .succ .zero => rfl | .succ (.succ w') => nomatch w'

private theorem honestPeerC_buIkB_eval (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.honestPeerC (Δ := Δ) S K st
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (v bu))).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.honestPeerC S K
        (Γ := [keyIndStateTy]) (Δ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy])
        .zero (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (.var .zero))).eval
        (.cons ((v bu).eval env) (.cons ((v st).eval env) .nil)) := by
  have hSyn : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.honestPeerC (Δ := Δ) S K st
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (v bu)) =
    compRename (mapVar2 (Ext.wk bu) (Ext.wk st))
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.honestPeerC S K
        (Γ := [keyIndStateTy]) (Δ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy])
        .zero (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (.var .zero))) := rfl
  rw [hSyn, mapVar2_eval]; rfl

private theorem checkProvC_eval_canon (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.checkProvC (Δ := Δ) S K st bu).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.checkProvC S K
        (Γ₁ := [keyIndStateTy]) (Γ₂ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy]) .zero .zero).eval
        (.cons ((v bu).eval env) (.cons ((v st).eval env) .nil)) := by
  have hSyn : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.checkProvC (Δ := Δ) S K st bu =
    compRename (mapVar2 (Ext.wk bu) (Ext.wk st))
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.checkProvC S K
        (Γ₁ := [keyIndStateTy]) (Γ₂ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy])
        (Δ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy]) .zero .zero) := rfl
  rw [hSyn, mapVar2_eval]; rfl

private theorem findPartnerC_eval_canon (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy)
    (se : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndSessionEntryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV (Γ := Δ) (min K S.N_sess_tot)
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stResps (v st))
      fun r => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC se r).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV
        (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndSessionEntryTy, keyIndStateTy])
        (min K S.N_sess_tot)
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stResps (.var (.succ .zero)))
        fun r => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC
          (Γ₁ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndSessionEntryTy, keyIndStateTy])
          .zero r).eval
        (.cons ((v se).eval env) (.cons ((v st).eval env) .nil)) := by
  have hSyn : (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV (Γ := Δ) (min K S.N_sess_tot)
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stResps (v st))
      fun r => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC se r) =
    compRename (mapVar2 (Ext.wk se) (Ext.wk st))
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV
        (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndSessionEntryTy, keyIndStateTy])
        (min K S.N_sess_tot)
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stResps (.var (.succ .zero)))
        fun r => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC
          (Γ₁ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndSessionEntryTy, keyIndStateTy])
          .zero r) := rfl
  rw [hSyn, mapVar2_eval]; rfl

private theorem findHonestC_buIkB_eval (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC (Δ := Δ) S K st
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (v bu))).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC S K
        (Γ := [keyIndStateTy]) (Δ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy])
        .zero (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (.var .zero))).eval
        (.cons ((v bu).eval env) (.cons ((v st).eval env) .nil)) := by
  have hSyn : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC (Δ := Δ) S K st
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (v bu)) =
    compRename (mapVar2 (Ext.wk bu) (Ext.wk st))
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC S K
        (Γ := [keyIndStateTy]) (Δ := [_root_.SignalPqxdh.LegacyCosted.bundleT, keyIndStateTy])
        .zero (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buIkB (.var .zero))) := rfl
  rw [hSyn, mapVar2_eval]; rfl

theorem initFinishC_true_eq_split (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ]
    (env : Env Δ) :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).eval env =
      (initFinishPreRoC (Δ := Δ) bu uE ekSk sc).eval env >>= fun sp =>
        (hkdfOrRoC K true
          (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          .zero (.var (.succ .zero))).eval
          (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)
            (.cons sp.1 .nil)) >>= fun dr =>
          (initFinishPostRoC S K
            (Γ₁ := [keyIndStateTy]) (Γ₂ := [_root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            (Γ₃ := [_root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            (Γ₄ := [.prod .nat principalEntryTy, _root_.SignalPqxdh.LegacyCosted.bundleT,
              _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            (Γ₅ := [_root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
              _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            (Γ₆ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
              _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
              _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            (Γ₇ := [_root_.SignalPqxdh.LegacyCosted.B 32,
              .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
              _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
              _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            (Γ₈ := [_root_.SignalPqxdh.LegacyCosted.drKeyT, _root_.SignalPqxdh.LegacyCosted.B 32,
              .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
              _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
              _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            (Γ₉ := [roListLegacyTy, _root_.SignalPqxdh.LegacyCosted.drKeyT,
              _root_.SignalPqxdh.LegacyCosted.B 32,
              .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
              _root_.SignalPqxdh.LegacyCosted.B 32, .prod .nat principalEntryTy,
              _root_.SignalPqxdh.LegacyCosted.bundleT, _root_.SignalPqxdh.LegacyCosted.sidT, keyIndStateTy])
            .zero .zero .zero .zero .zero .zero .zero .zero .zero).eval
            (.cons dr.2 (.cons dr.1 (.cons sp.2
              (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v sc).eval env)
                (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v ekSk).eval env)
                  (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v uE).eval env)
                    (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v bu).eval env)
                      (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v sid).eval env)
                        (.cons ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)
                          .nil))))))))) := by
  rw [initFinishC_eval_canon, initFinishPreRoC_eval_canon]
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v sc).eval env = scV
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v ekSk).eval env = ekSkV
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v uE).eval env = uEV
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v bu).eval env = buV
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v sid).eval env = sidV
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env = stV
  dsimp only [initFinishC, initFinishPreRoC]
  rw [bindV_eval, bindV_eval, bind_assoc]; refine bind_congr_eq rfl fun ekPk => ?_
  rw [bindV_eval, bindV_eval, bind_assoc]; refine bind_congr_eq rfl fun dh1 => ?_
  rw [bindV_eval, bindV_eval, bind_assoc]; refine bind_congr_eq rfl fun dh2 => ?_
  rw [bindV_eval, bindV_eval, bind_assoc]; refine bind_congr_eq rfl fun dh3 => ?_
  rw [bindV_eval, bindV_eval, bind_assoc]; refine bind_congr_eq rfl fun dh4r => ?_
  rw [bindV_eval, show (Comp.ret _ : Comp pqxdhOps _ _ _).eval _ = pure _ from rfl, pure_bind,
    hkdfOrRoC_eval_congr]
  refine bind_congr_eq (by
    refine congrArg ((hkdfOrRoC K true
      (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
      .zero (.var (.succ .zero))).eval ·) ?_
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buildSecretsE_eval,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buOpkB, v, Ext.wk, Expr.eval, Env.get])
    fun dr => ?_
  dsimp only [initFinishPostRoC]
  rw [letV_eval, letV_eval, bindV_eval, bindV_eval]
  refine bind_congr_eq (by
    conv_lhs => rw [honestPeerC_buIkB_eval]
    conv_rhs => rw [honestPeerC_buIkB_eval]
    simp only [v, Ext.wk, Expr.eval, Env.get]) fun hp => ?_
  rw [bindV_eval, bindV_eval]
  refine bind_congr_eq (by
    conv_lhs => rw [checkProvC_eval_canon]
    conv_rhs => rw [checkProvC_eval_canon]
    simp only [v, Ext.wk, Expr.eval, Env.get]) fun prov => ?_
  rw [letV_eval, letV_eval, bindV_eval, bindV_eval]
  refine bind_congr_eq (by
    conv_lhs => rw [findPartnerC_eval_canon]
    conv_rhs => rw [findPartnerC_eval_canon]
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optFst,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optSnd,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
      v, Ext.wk, Expr.eval, Env.get]) fun found => ?_
  rw [bindV_eval, bindV_eval]
  refine bind_congr_eq (by
    rcases found with _ | rVal
    · rfl
    · simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseOptV,
        Comp.eval, v, Ext.wk, Expr.eval, Env.get]) fun drr => ?_
  rw [bindV_eval, bindV_eval]
  refine bind_congr_eq (by
    conv_lhs => rw [findHonestC_buIkB_eval]
    conv_rhs => rw [findHonestC_buIkB_eval]
    simp only [v, Ext.wk, Expr.eval, Env.get]) fun fh => ?_
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.seUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rInitUnfresh,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rHdr,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSess]
  simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optFst,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optSnd,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
    v, Ext.wk, Expr.eval, Env.get]

private theorem initFinishPreRoC_eval_eq_of_vals {Γ₁ Γ₂ Γ₃ Γ₄ Γ₁' Γ₂' Γ₃' Γ₄' Δ₁ Δ₂ : List PT}
    (bu₁ : Var Γ₁ _root_.SignalPqxdh.LegacyCosted.bundleT) (uE₁ : Var Γ₂ (.prod .nat principalEntryTy))
    (ekSk₁ : Var Γ₃ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc₁ : Var Γ₄ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁] [Ext Γ₃ Δ₁] [Ext Γ₄ Δ₁]
    (bu₂ : Var Γ₁' _root_.SignalPqxdh.LegacyCosted.bundleT) (uE₂ : Var Γ₂' (.prod .nat principalEntryTy))
    (ekSk₂ : Var Γ₃' (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc₂ : Var Γ₄' (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂] [Ext Γ₃' Δ₂] [Ext Γ₄' Δ₂] (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hbu : (v bu₁).eval env₁ = (v bu₂).eval env₂) (huE : (v uE₁).eval env₁ = (v uE₂).eval env₂)
    (hekSk : (v ekSk₁).eval env₁ = (v ekSk₂).eval env₂) (hsc : (v sc₁).eval env₁ = (v sc₂).eval env₂) :
    (initFinishPreRoC (Δ := Δ₁) bu₁ uE₁ ekSk₁ sc₁).eval env₁ =
      (initFinishPreRoC (Δ := Δ₂) bu₂ uE₂ ekSk₂ sc₂).eval env₂ := by
  rw [initFinishPreRoC_eval_canon (env := env₁), initFinishPreRoC_eval_canon (env := env₂), hbu, huE, hekSk, hsc]

private theorem initFinishPostRoC_eval_eq_of_vals (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁' Γ₂' Γ₃' Γ₄' Γ₅' Γ₆' Γ₇' Γ₈' Γ₉' Δ₁ Δ₂ : List PT}
    (st₁ : Var Γ₁ keyIndStateTy) (sid₁ : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu₁ : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT) (uE₁ : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk₁ : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc₁ : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk₁ : Var Γ₇ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk₁ : Var Γ₈ _root_.SignalPqxdh.LegacyCosted.drKeyT) (roNew₁ : Var Γ₉ roListLegacyTy)
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁] [Ext Γ₃ Δ₁] [Ext Γ₄ Δ₁] [Ext Γ₅ Δ₁] [Ext Γ₆ Δ₁] [Ext Γ₇ Δ₁] [Ext Γ₈ Δ₁] [Ext Γ₉ Δ₁]
    (st₂ : Var Γ₁' keyIndStateTy) (sid₂ : Var Γ₂' _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu₂ : Var Γ₃' _root_.SignalPqxdh.LegacyCosted.bundleT) (uE₂ : Var Γ₄' (.prod .nat principalEntryTy))
    (ekSk₂ : Var Γ₅' (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc₂ : Var Γ₆' (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk₂ : Var Γ₇' (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk₂ : Var Γ₈' _root_.SignalPqxdh.LegacyCosted.drKeyT) (roNew₂ : Var Γ₉' roListLegacyTy)
    [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂] [Ext Γ₃' Δ₂] [Ext Γ₄' Δ₂] [Ext Γ₅' Δ₂] [Ext Γ₆' Δ₂] [Ext Γ₇' Δ₂] [Ext Γ₈' Δ₂] [Ext Γ₉' Δ₂]
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂) (hsid : (v sid₁).eval env₁ = (v sid₂).eval env₂)
    (hbu : (v bu₁).eval env₁ = (v bu₂).eval env₂) (huE : (v uE₁).eval env₁ = (v uE₂).eval env₂)
    (hekSk : (v ekSk₁).eval env₁ = (v ekSk₂).eval env₂) (hsc : (v sc₁).eval env₁ = (v sc₂).eval env₂)
    (hekPk : (v ekPk₁).eval env₁ = (v ekPk₂).eval env₂) (hdk : (v dk₁).eval env₁ = (v dk₂).eval env₂)
    (hro : (v roNew₁).eval env₁ = (v roNew₂).eval env₂) :
    (initFinishPostRoC (Δ := Δ₁) S K st₁ sid₁ bu₁ uE₁ ekSk₁ sc₁ ekPk₁ dk₁ roNew₁).eval env₁ =
      (initFinishPostRoC (Δ := Δ₂) S K st₂ sid₂ bu₂ uE₂ ekSk₂ sc₂ ekPk₂ dk₂ roNew₂).eval env₂ := by
  rw [initFinishPostRoC_eval_canon (env := env₁), initFinishPostRoC_eval_canon (env := env₂),
    hst, hsid, hbu, huE, hekSk, hsc, hekPk, hdk, hro]

theorem shcrResumeC_eq_split (S : Setup) (K : ℕ)
    (sL : Ty.denote shcrStTy) (pL : Ty.denote pauseTy)
    (yL : Ty.denote (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568))) :
    (shcrResumeC S K
      (Γ₁ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)])
      (Γ₂ := [pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
        (_root_.SignalPqxdh.LegacyCosted.B 1568)])
      (Γ₃ := [shcrStTy, pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
        (_root_.SignalPqxdh.LegacyCosted.B 1568)])
      (Δ := [shcrStTy, pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
        (_root_.SignalPqxdh.LegacyCosted.B 1568)])
      .zero .zero .zero).eval (.cons sL (.cons pL (.cons yL .nil))) =
    shcrResumePreRoC.eval (.cons sL (.cons pL (.cons yL .nil))) >>= fun pre =>
      (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero))).eval (.cons sL.1 (.cons pre.1 .nil)) >>= fun dr =>
        (shcrResumePostRoC S K).eval
          (.cons dr.1 (.cons dr.2 (.cons pre.2 (.cons sL (.cons pL (.cons yL .nil)))))) := by
  dsimp only [shcrResumeC, shcrResumePreRoC, shcrResumePostRoC]
  iterate 4 rw [letV_eval]
  rw [bindV_eval]
  iterate 2 rw [letV_eval]
  rw [bindV_eval, bind_assoc]
  refine bind_congr_eq rfl fun ekSk => ?_
  rw [bindV_eval, bindV_eval, initFinishC_true_eq_split, bind_assoc, bind_assoc]
  refine bind_congr_eq
    (initFinishPreRoC_eval_eq_of_vals _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_) fun pre => ?_
  · simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_succ, env_get_zero]
  · simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_succ, env_get_zero]
  · simp only [v, ext_refl_wk, env_get_zero, Expr.eval]
  · simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_succ, env_get_zero]
  · rw [show (Comp.ret _ : Comp pqxdhOps _ _ _).eval _ = pure _ from rfl, pure_bind, bind_assoc]
    refine bind_congr_eq
      (by simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_succ, env_get_zero])
      fun dr => ?_
    iterate 6 rw [letV_eval]
    rw [bindV_eval]
    refine bind_congr_eq
      (initFinishPostRoC_eval_eq_of_vals S K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun r => ?_
    all_goals try (simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_succ, env_get_zero]; done)
    rw [letV_eval, letV_eval]
    simp only [shcrFinE, scUpd, v, ext_refl_wk, ext_step_wk, Comp.eval, Expr.eval,
      env_get_succ, env_get_zero]

theorem shcrResumePostRoC_fixSent_comm (S : Setup) (b : QueryBudget) (K : ℕ)
    (dk : Ty.denote _root_.SignalPqxdh.LegacyCosted.drKeyT)
    (roNew : Ty.denote roListLegacyTy)
    (ep : Ty.denote (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 32)))
    (sL : Ty.denote shcrStTy) (pL : Ty.denote pauseTy)
    (yL : Ty.denote (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568))) :
    Prod.map id (fixShcrLegacySent S b) <$>
      (shcrResumePostRoC S K).eval (.cons dk (.cons roNew (.cons ep (.cons sL (.cons pL (.cons yL .nil)))))) =
    (shcrResumePostRoC S K).eval
      (.cons dk (.cons roNew (.cons ep (.cons (fixShcrLegacySent S b sL) (.cons pL (.cons yL .nil)))))) := by
  dsimp only [shcrResumePostRoC]
  rw [map_eq_bind_pure_comp]
  iterate 6 rw [letV_eval]
  rw [bindV_eval, bind_assoc]
  iterate 6 rw [letV_eval]
  rw [bindV_eval]
  refine bind_congr_eq
    (initFinishPostRoC_eval_eq_of_vals S K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun r => ?_
  · simp only [v, ext_refl_wk, ext_step_wk, fixShcrLegacySent,
      Expr.eval, env_get_succ, env_get_zero]
  all_goals try (simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_succ, env_get_zero]; done)
  rw [letV_eval, letV_eval]
  simp only [shcrFinE, scUpd, scMk, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx,
    scChosen, fixShcrLegacySent, v, ext_refl_wk, ext_step_wk,
    Comp.eval, Expr.eval, env_get_succ, env_get_zero, pure_bind, Function.comp_def, Prod.map, id_eq]

theorem shcrInitiatePostRoC_fixSent_comm (S : Setup) (b : QueryBudget) (K : ℕ)
    (dk : Ty.denote _root_.SignalPqxdh.LegacyCosted.drKeyT)
    (roNew : Ty.denote roListLegacyTy)
    (mid : Ty.denote shcrInitMidTy)
    (sL : Ty.denote shcrStTy) :
    Prod.map id (fixShcrLegacySent S b) <$>
      (shcrInitiatePostRoC S K).eval (.cons dk (.cons roNew (.cons mid (.cons sL .nil)))) =
    (shcrInitiatePostRoC S K).eval
      (.cons dk (.cons roNew (.cons mid (.cons (fixShcrLegacySent S b sL) .nil)))) := by
  dsimp only [shcrInitiatePostRoC]
  rw [map_eq_bind_pure_comp]
  iterate 7 rw [letV_eval]
  rw [bindV_eval, bind_assoc]
  iterate 7 rw [letV_eval]
  rw [bindV_eval]
  refine bind_congr_eq
    (initFinishPostRoC_eval_eq_of_vals S K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun r => ?_
  · simp only [v, ext_refl_wk, ext_step_wk, fixShcrLegacySent,
      Expr.eval, env_get_succ, env_get_zero]
  all_goals try (simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_succ, env_get_zero]; done)
  simp only [shcrFinE, scUpd, scMk, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx,
    scChosen, fixShcrLegacySent, v, ext_refl_wk, ext_step_wk,
    Comp.eval, Expr.eval, env_get_succ, env_get_zero, pure_bind, Function.comp_def, Prod.map, id_eq]

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimHelpers
