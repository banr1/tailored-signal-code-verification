/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Bound
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyShcr
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Two-Stage `ReductionDsl` Advantage Equivalence for Active One-Key `KemShCr`

Proves `KemShCr` and `KemShCrReal` advantage equality between the atomic two-stage `ReductionDsl`
adversary `(pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A` and the shallow creation-order
reduction `shcrReductionKeyInd1KeyActive S b A`.
-/

set_option autoImplicit false

open OracleSpec OracleComp
open scoped ENNReal
open ReductionDsl (Ty Var Env Comp Expr TwoStageCostedReduction Mid)
open SignalPqxdh (Setup Primitives Bytes QueryBudget BoundedAdv KeyIndAdversary KeyIndQuery
  KeyIndResponse KeyIndState PreKeyBundleInput SessionId HandshakeHdr SpkBundleEntry PrincipalEntry
  KemShCrAdv KemShCr KemShCrReal kemShCrExp activeSpkCount activeSendCount primQueryBudget
  keyIndSpec PrimBaseSpec primBaseImpl sampleCoins32 sampleKemKeyGen kyberCtLen kyberPkLen
  sampleScalar32 encodeEC encodeKEM)
open SignalPqxdh.Costed (PB)
open SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface keyIndCodec B bundleT sidT keyIndRenc
  keyIndQenc keyIndRdec_keyIndRenc bundleV hdrV drKeyV sidV)
open SignalPqxdh.Security (embedUnif simulateQ_embedUnif primQ pqxdhKeyIndImplPrim)
open SignalPqxdh.Security.RoKem (KeyIndShCrState PausedShCrData ShCrFinishState
  pqxdhKeyIndImpl1KeyRoPrim pqxdhKeyIndShCrPrimImpl pqxdhKeyIndShCrPrimImpl1Key liftShCrBasePrim
  genSpkTargetKeyIndPrim tryPauseKeyIndQueryPrim postKemKeyIndPrim extractCollidingKemCtPrim
  runKeyIndShCrInitiatePrim runKeyIndShCrAcceptPrim recordAcceptKemGenericPrim isNoneKeyIndResp
  sampleIndexRange)
open SignalPqxdh.Security.ReductionDsl (HoldsOnLeaves PreStepInvC Stage1InvC RedProg2State
  GRed2_run1_eq_stepUntilPauseFuel runFuel_pqPrimIface_eq_runWithFuelPrim stepUntilPauseFuel
  stepUntilPauseFuel_char stepUntilPauseFuel_map_boundedC runWithFuelPrim runWithFuelPrim_char
  runWithFuelPrim_map_bounded kemShCrExp_congr)
open SignalPqxdh.Security.ReductionDsl.KeyInd (PT Ext shcrStTy pauseTy keyIndStateTy keyIndQueryTy
  keyIndQueryRestTy principalEntryTy keyIndSessionEntryTy keyIndRespEntryTy accInpTy SCS RS v letV
  bindV caseOptV caseSumV onBase scTB scBase scTPk scTSk scCnt scIR scRR scSIdx scChosen scUpd
  stSpks stPrin stUpd sbMk buMk buPqspkB rNone rBundle encEC encKEM peSecIKAsign peIkAPk u32OfNat
  natEq nat2Eq eAny eFind findMV anyMV sBytes32 sRandom64 sDrKey96 sIndex sBool qX25519 qX25519Base
  qPow8 qIsCanonical qSigPkGen qSigSign qSigVerify qKemKeyGen qKemEncaps qKemDecaps qHkdfDerive96
  scMk emptyStE pauseCheckC tryPauseC shcrResumeC shcrExtractC shcrGenSpkB shcrInitiateC
  shcrAcceptB genSpkB initPrin1KeyB corruptB genOpkB acceptOpkB acceptNoOpkB testB revealB roB
  revealDhB registerB revealSpkB findHonestC isAdvRegC isGameSpkC isGameOpkC koskBundleOkC
  koskSenderOkC resolveSigPkC honestPeerC checkProvC partnerC recordRespC hkdfOrRoC acceptKeysC
  initFinishC preCheckC checkSigsC shcrPostTailC shcr1KeyPostC shcrKeyIndProg keyIndLoopBound
  keyIndStateToVal keyIndQueryToVal keyIndRespToVal valToKeyIndResp shcrStToVal encSCS
  preKeyBundleToVal PauseMid encPause tryPauseMid tryPauseMid_shallow toPaused Gsh ShInv
  liftShCrBasePrim_inv pqxdhKeyIndImplPrim_hol pqxdhKeyIndShCrPrimImpl_inv
  pqxdhKeyIndShCrPrimImpl1Key_inv onBase_eval genSpkB_eval shcrPostC_eval shcr1KeyPostC_eval
  pauseCheckC_eval shcrResume_eval shcrFinish_eval postKem_inv chosenOf toShallow encMid
  sIndex_eval sBool_eval natEq_eval bind_congr2 KeyIndListsBounded)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (shcrActiveGenSpkB
  shcrActivePostTailC shcr1KeyActivePostC shcr1KeyActivePreC shcrKeyInd1KeyActiveDslProg
  pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlPrimKeyInd liftKeyInd2Stage embedVal embedMid
  liftKeyInd2Stage_eval1 liftKeyInd2Stage_eval2 kemShCr_eq_of_state_map keyIndUnsupportedPrimW)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (runKeyIndShCrActiveGenSPKPrim
  pqxdhKeyIndShCrActivePrimImpl1Key runWithFuelKeyInd1KeyActiveShCrPrim
  stepUntilShCrFuelKeyInd1KeyActivePrim resumePausedKeyInd1KeyActivePrim
  choosePkKeyInd1KeyActivePrimAt findCollisionKeyInd1KeyActivePrim
  shcrReductionKeyInd1KeyActiveCore shcrReductionKeyInd1KeyActive)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrEval

public section
attribute [local simp] bundleV hdrV drKeyV sidV keyIndRenc keyIndQenc

/-! ## Unsupported-query vanishing -/
private def zPrimWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0
@[local simp] private theorem sBool_unsup {Γ : List PT} : (sBool (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sBytes32_unsup {Γ : List PT} : (sBytes32 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sRandom64_unsup {Γ : List PT} : (sRandom64 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sDrKey96_unsup {Γ : List PT} : (sDrKey96 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} : (sIndex N (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) : (qX25519 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519Base_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qX25519Base e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qPow8_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qPow8 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qIsCanonical_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qIsCanonical e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigPkGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qSigPkGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigSign_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigSign m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigVerify_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigVerify m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemKeyGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) : (qKemKeyGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemEncaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) : (qKemEncaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemDecaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) : (qKemDecaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qHkdfDerive96_unsup (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) : (qHkdfDerive96 w e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem findHonestC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) : (findHonestC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [findHonestC, letV, findMV, bindV, Comp.queries]
@[local simp] private theorem isAdvRegC_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) : (isAdvRegC K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isAdvRegC, bindV, Comp.queries]
@[local simp] private theorem isGameSpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) : (isGameSpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameSpkC, letV, anyMV, bindV, Comp.queries]
@[local simp] private theorem isGameOpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) : (isGameOpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameOpkC, letV, anyMV, bindV, Comp.queries]
@[local simp] private theorem koskBundleOkC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (koskBundleOkC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskBundleOkC, bindV, caseOptV, Comp.queries]
@[local simp] private theorem koskSenderOkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) : (koskSenderOkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskSenderOkC, letV, bindV, Comp.queries]
@[local simp] private theorem resolveSigPkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) : (resolveSigPkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [resolveSigPkC, letV, bindV, Comp.queries]
@[local simp] private theorem honestPeerC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) : (honestPeerC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [honestPeerC, bindV, Comp.queries]
@[local simp] private theorem checkProvC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (checkProvC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [checkProvC, bindV, letV, caseOptV, anyMV, Comp.queries]
@[local simp] private theorem partnerC_unsup {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (partnerC (Δ := Δ) s r).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem recordRespC_unsup (S : Setup) (K : Nat) {Δ : List PT} (p : Expr pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) : (recordRespC S K p).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [recordRespC, letV, bindV, caseOptV, findMV, Comp.queries]
@[local simp] private theorem hkdfOrRoC_true_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) : (hkdfOrRoC K true st sec).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [hkdfOrRoC, letV, caseOptV, bindV, Comp.queries]
@[local simp] private theorem hkdfOrRoC_false_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) : (hkdfOrRoC K false st sec).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [hkdfOrRoC, letV, bindV, Comp.queries]
@[local simp] private theorem acceptKeysC_unsup {Δ : List PT} (inp : Expr pqxdhOps Δ accInpTy) : (acceptKeysC inp).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem initFinishC_true_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (bu : Var Γ₃ bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (B 32)) (sc : Var Γ₆ (.prod (B 32) (B 1568))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [initFinishC, bindV, letV, caseOptV, findMV, Comp.queries]
@[local simp] private theorem preCheckC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (u : Var Γ₃ .nat) (bu : Var Γ₄ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [preCheckC, caseOptV, bindV, Comp.queries]
@[local simp] private theorem checkSigsC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : (checkSigsC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [checkSigsC, bindV, Comp.queries]
@[local simp] private theorem onBase_unsup {Γ₁ Δ : List PT} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) → Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    (onBase (Δ := Δ) s br).queries keyIndUnsupportedPrimW zPrimWS = (br .zero).queries keyIndUnsupportedPrimW zPrimWS := by simp [onBase, bindV, letV, Comp.queries]
private theorem shcrActive_init_unsupported (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).init.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyInd1KeyActiveDslProg S b).init.queries keyIndUnsupportedPrimW zPrimWS = 0
  unfold shcrKeyInd1KeyActiveDslProg; dsimp only; split_ifs <;> simp [bindV, Comp.queries]
private theorem shcrActive_chDone_unsupported (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).chDone.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := rfl
private theorem shcrActive_resume_unsupported (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).resume.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyInd1KeyActiveDslProg S b).resume.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrKeyInd1KeyActiveDslProg, shcrResumeC, bindV, letV, Comp.queries]
private theorem shcrActive_finish_unsupported (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).finish.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyInd1KeyActiveDslProg S b).finish.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrKeyInd1KeyActiveDslProg, shcrExtractC, bindV, findMV, Comp.queries]
@[local simp] private theorem shcr1KeyActivePostC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyActivePostC (Δ := Δ) S K s q).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [shcr1KeyActivePostC, shcrActivePostTailC, shcrActiveGenSpkB, shcrInitiateC, shcrAcceptB,
    initPrin1KeyB, corruptB, genSpkB, genOpkB, acceptOpkB, acceptNoOpkB, testB, revealB, roB,
    revealDhB, registerB, revealSpkB, bindV, letV, caseOptV, caseSumV, Comp.queries]
private theorem shcrActive_handlePost_unsupported (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcr1KeyActivePostC_unsup S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
private theorem shcrActive_handlePre_unsupported (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyActiveDslProg S b).handlePre.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcr1KeyActivePreC S (keyIndLoopBound b) (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries
    keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcr1KeyActivePreC, pauseCheckC, tryPauseC, bindV, letV, caseOptV, caseSumV, Comp.queries]

/-! ## Generic `AtomicLift` two-stage `KemShCr` bridge -/

/-- Generic `KemShCrAdv` induced by a two-stage `ReductionDsl` program `R` on `A`. -/
@[expose] def twoStageDslAdv (S : Setup) (b : QueryBudget)
    (R : TwoStageCostedReduction pqxdhOps pqPrimIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568))
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv where
  State := Mid (keyIndSpec S) Bool R.π.denote R.σ.denote Bytes
  choosePk pk sk := R.eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
  findCollision st ss ct := R.eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b
private theorem kemShCr_liftKeyInd2Stage_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (R : TwoStageCostedReduction pqxdhOps pqPrimIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568))
    (hInit : R.init.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (hPre : R.handlePre.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (hDone : R.chDone.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (hRes : R.resume.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (hPost : R.handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (hFin : R.finish.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P
      ({ State := Mid (keyIndSpec S) Bool (liftKeyInd2Stage tlPrimKeyInd S R).π.denote
           (liftKeyInd2Stage tlPrimKeyInd S R).σ.denote (PB 1568).denote
         choosePk := fun pk sk =>
           (liftKeyInd2Stage tlPrimKeyInd S R).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
         findCollision := fun st ss ct =>
           (liftKeyInd2Stage tlPrimKeyInd S R).eval2 st (ss, ct) b.q_total false
         q_prim := primQueryBudget S b } : KemShCrAdv) =
      KemShCr P (twoStageDslAdv S b R A) := by
  refine kemShCr_eq_of_state_map P (twoStageDslAdv S b R A) _
    (embedMid (π := R.π) (σ := R.σ) (ch := B 1568))
    (fun pk sk => ?_) (fun st ss ct => ?_)
  · exact liftKeyInd2Stage_eval1 tlPrimKeyInd S R hInit hPre hDone
      (fun _ => A.1.run) (pk, sk) b.q_total false
  · have hId : embedVal (B 1568) = id := rfl
    have h := liftKeyInd2Stage_eval2 tlPrimKeyInd S R hRes hPost hFin st (ss, ct) b.q_total false
    rw [hId, id_map] at h; exact h

private def shcrKeyInd1KeyActiveProgK (S : Setup) (q_on Q K : ℕ) :
    TwoStageCostedReduction pqxdhOps pqPrimIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568) where
  σ := shcrStTy
  π := pauseTy
  init :=
    let n_spk := activeSpkCount S q_on
    let n_send := activeSendCount S q_on
    let n_prod := n_spk * n_send
    if n_prod = 0 then
      bindV sBool fun secb =>
      .ret (.pair .unit (scMk (emptyStE (v secb)) .none
        (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero))) (.nat 0) .nil .nil
        (.nat (Q + 1)) (.fst (.var (.succ .zero)))))
    else
      bindV (sIndex n_spk) fun spkOrd =>
      bindV (sIndex n_send) fun sIdx =>
      bindV sBool fun secb =>
      .ret (.pair .unit (scMk (emptyStE (v secb)) (.some (.pair (v spkOrd) (.nat 0)))
        (.fst (.var (.succ (.succ (.succ .zero))))) (.snd (.var (.succ (.succ (.succ .zero)))))
        (.nat 0) .nil .nil (v sIdx) (.fst (.var (.succ (.succ (.succ .zero)))))))
  handlePre := shcr1KeyActivePreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  chDone := .ret (scTPk (.var .zero))
  resume := shcrResumeC S K (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero
  handlePost := shcr1KeyActivePostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  finish := shcrExtractC (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) Q .zero .zero
private theorem shcrKeyInd1KeyActiveDslProg_eq (S : Setup) (b : QueryBudget) :
    shcrKeyInd1KeyActiveDslProg S b =
      shcrKeyInd1KeyActiveProgK S b.q_on b.q_total (keyIndLoopBound b) :=
  rfl

/-! ## Creation-order `genSPK` branch evaluation -/
private def scaleTB (S : Setup) (h : KeyIndShCrState S) : KeyIndShCrState S :=
  { h with targetBIdx? := h.targetBIdx?.map (· * S.N_recv) }
private def shcrActiveStToVal {S : Setup} (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes) :
    shcrStTy.denote :=
  shcrStToVal (scaleTB S h) sIdx chosen
private def encSCSActive {S : Setup} (sIdx : Nat) (chosen : Bytes)
    (p : KeyIndResponse × KeyIndShCrState S) : SCS.denote :=
  (keyIndRespToVal p.1, shcrActiveStToVal p.2 sIdx chosen)
private def encMidActive {S : Setup} (pk : Bytes)
    (x : ℕ × (Option Bytes × RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))) :
    Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes :=
  match x.2.2 with
  | .done a h => .done a (shcrActiveStToVal h x.1 pk)
  | .paused q d h c => .paused q d.2.1.pqspkB (encPause d) (shcrActiveStToVal h x.1 pk) c
private structure ShInvAct {S : Setup} (pk sk : Bytes) (n : ℕ) (h : KeyIndShCrState S) : Prop where
  sh : ShInv pk sk n h
  tv : h.targetBIdx?.isSome = true → 0 < S.N_recv
private theorem ShInvAct.mono {S : Setup} {pk sk : Bytes} {n m : ℕ} {h : KeyIndShCrState S}
    (hnm : n ≤ m) (hI : ShInvAct pk sk n h) : ShInvAct pk sk m h :=
  ⟨hI.sh.mono hnm, hI.tv⟩
private theorem holdsOnLeaves_and {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P Q : α → Prop} {m : OracleComp spec α}
    (hP : HoldsOnLeaves P m) (hQ : HoldsOnLeaves Q m) :
    HoldsOnLeaves (fun a => P a ∧ Q a) m :=
  ⟨fun {β} f g hfg => by
    classical
    let mid : α → OracleComp spec β := fun a => if P a then f a else g a
    have h1 : m >>= f = m >>= mid := hP.bind_congr f mid fun a hp => by simp [mid, hp]
    have h2 : m >>= mid = m >>= g := hQ.bind_congr mid g fun a hq => by
      by_cases hp : P a
      · simp [mid, hp, hfg a ⟨hp, hq⟩]
      · simp [mid, hp]
    exact h1.trans h2⟩
private theorem scaleTB_map_div_mod {S : Setup} (h : KeyIndShCrState S)
    (htv : h.targetBIdx?.isSome = true → 0 < S.N_recv) :
    (scaleTB S h).targetBIdx?.map (fun bIdx => (bIdx / S.N_recv, bIdx % S.N_recv)) =
      h.targetBIdx?.map (fun spkOrd => (spkOrd, 0)) := by
  rcases ht : h.targetBIdx? with _ | spkOrd
  · simp [scaleTB, ht]
  · have hN : 0 < S.N_recv := htv (by simp [ht])
    simp [scaleTB, ht, Nat.mul_div_cancel _ hN, Nat.mul_mod_left]
private theorem liftShCrBasePrim_scaleTB {S : Setup} {R : Type}
    (m : StateT (KeyIndState S) (OracleComp PrimBaseSpec) R) (h : KeyIndShCrState S) :
    (liftShCrBasePrim m).run (scaleTB S h) =
      Prod.map id (scaleTB S) <$> (liftShCrBasePrim m).run h := by
  dsimp only [liftShCrBasePrim, StateT.run, scaleTB]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
  exact bind_congr fun _ => rfl
private theorem liftShCrBasePrim_tb {S : Setup} {R : Type}
    (m : StateT (KeyIndState S) (OracleComp PrimBaseSpec) R) (h : KeyIndShCrState S) :
    HoldsOnLeaves (fun x : R × KeyIndShCrState S => x.2.targetBIdx? = h.targetBIdx?)
      ((liftShCrBasePrim m).run h) := by
  simp only [liftShCrBasePrim, StateT.run]
  exact HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.pure rfl
private theorem runKeyIndShCrInitiatePrim_scaleTB (S : Setup) (sid : SessionId S)
    (u : Fin S.N_id) (bu : PreKeyBundleInput) (h : KeyIndShCrState S) :
    (runKeyIndShCrInitiatePrim S sid u bu).run (scaleTB S h) =
      Prod.map id (scaleTB S) <$> (runKeyIndShCrInitiatePrim S sid u bu).run h := by
  dsimp only [runKeyIndShCrInitiatePrim, StateT.run]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | uE
  · rfl
  · simp only [bind_assoc]
    refine bind_congr fun _ => bind_congr fun _ => bind_congr fun sigOk => ?_
    by_cases hs : (!sigOk) = true
    · simp [hs]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine bind_congr fun km => ?_
      rcases km with _ | ⟨ss, kemCt⟩
      · rfl
      · simp only [bind_assoc, pure_bind]
        refine bind_congr fun out => ?_
        rcases out with ⟨r, _ | base'⟩ <;> rfl
private theorem runKeyIndShCrInitiatePrim_tb (S : Setup) (sid : SessionId S)
    (u : Fin S.N_id) (bu : PreKeyBundleInput) (h : KeyIndShCrState S) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => x.2.targetBIdx? = h.targetBIdx?)
      ((runKeyIndShCrInitiatePrim S sid u bu).run h) := by
  dsimp only [runKeyIndShCrInitiatePrim, StateT.run]
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | uE
  · exact HoldsOnLeaves.pure rfl
  · refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
      HoldsOnLeaves.bind_const _ fun sigOk => ?_
    split
    · exact HoldsOnLeaves.pure rfl
    · refine HoldsOnLeaves.bind_const _ fun km => ?_
      rcases km with _ | ⟨ss, kemCt⟩
      · exact HoldsOnLeaves.pure rfl
      · refine HoldsOnLeaves.bind_const _ fun out => ?_
        rcases out with ⟨_, _ | _⟩ <;> exact HoldsOnLeaves.pure rfl
private theorem runKeyIndShCrAcceptPrim_scaleTB (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (gq : KeyIndQuery S)
    (h : KeyIndShCrState S) :
    (runKeyIndShCrAcceptPrim S k j hdr gq).run (scaleTB S h) =
      Prod.map id (scaleTB S) <$> (runKeyIndShCrAcceptPrim S k j hdr gq).run h := by
  change ((liftShCrBasePrim (pqxdhKeyIndImplPrim true S gq)).run (scaleTB S h) >>= fun x =>
      recordAcceptKemGenericPrim KeyIndState.spkBundles isNoneKeyIndResp k j hdr x.1 x.2) =
    Prod.map id (scaleTB S) <$>
      ((liftShCrBasePrim (pqxdhKeyIndImplPrim true S gq)).run h >>= fun x =>
        recordAcceptKemGenericPrim KeyIndState.spkBundles isNoneKeyIndResp k j hdr x.1 x.2)
  rw [liftShCrBasePrim_scaleTB, bind_map_left]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
  refine bind_congr fun x => ?_
  rcases x with ⟨out, h'⟩
  dsimp only [Prod.map, id, recordAcceptKemGenericPrim, scaleTB]
  by_cases hn : isNoneKeyIndResp out = true
  · simp [hn]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    rcases hfd : h'.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bE⟩
    · simp [hfd]
    · simp only [hfd, bind_assoc]
      refine bind_congr fun dm => ?_
      rcases dm with _ | ss <;> rfl
private theorem runKeyIndShCrAcceptPrim_tb (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (gq : KeyIndQuery S)
    (h : KeyIndShCrState S) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => x.2.targetBIdx? = h.targetBIdx?)
      ((runKeyIndShCrAcceptPrim S k j hdr gq).run h) := by
  change HoldsOnLeaves _ ((liftShCrBasePrim (pqxdhKeyIndImplPrim true S gq)).run h >>= fun x =>
    recordAcceptKemGenericPrim KeyIndState.spkBundles isNoneKeyIndResp k j hdr x.1 x.2)
  refine HoldsOnLeaves.bind (liftShCrBasePrim_tb _ h) fun ⟨out, h'⟩ hh' => ?_
  dsimp only [recordAcceptKemGenericPrim]
  split
  · exact HoldsOnLeaves.pure hh'
  · rcases hfd : h'.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bE⟩
    · simp only [hfd]; exact HoldsOnLeaves.pure hh'
    · simp only [hfd]
      refine HoldsOnLeaves.bind_const _ fun dm => ?_
      rcases dm with _ | ss <;> exact HoldsOnLeaves.pure hh'
private theorem postKemKeyIndPrim_scaleTB (S : Setup) (sid : SessionId S)
    (bu : PreKeyBundleInput) (uE : PrincipalEntry) (h : KeyIndShCrState S) (ss kemCt : Bytes) :
    postKemKeyIndPrim S sid bu uE (scaleTB S h) ss kemCt =
      Prod.map id (scaleTB S) <$> postKemKeyIndPrim S sid bu uE h ss kemCt := by
  simp only [postKemKeyIndPrim, scaleTB, map_eq_bind_pure_comp, bind_assoc, Function.comp_def,
    pure_bind]
  refine bind_congr fun _ => bind_congr fun out => ?_
  rcases out with ⟨r, _ | base'⟩ <;> rfl
private theorem postKem_inv_act (S : Setup) (pk sk : Bytes) (n : ℕ) (d : PauseMid S)
    (h : KeyIndShCrState S) (hI : ShInvAct pk sk n h) (ss kemCt : Bytes) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInvAct pk sk (n + 1) x.2)
      (postKemKeyIndPrim S d.1 d.2.1 d.2.2.2 h ss kemCt) := by
  have htb : HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S =>
      x.2.targetBIdx? = h.targetBIdx?)
      (postKemKeyIndPrim S d.1 d.2.1 d.2.2.2 h ss kemCt) := by
    simp only [postKemKeyIndPrim]
    refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun out => ?_
    rcases out with ⟨_, _ | _⟩ <;> exact HoldsOnLeaves.pure rfl
  exact (holdsOnLeaves_and (postKem_inv S pk sk n d h hI.sh ss kemCt) htb).mono
    fun _ ⟨hS, heq⟩ => ⟨hS, heq ▸ hI.tv⟩
private theorem genSpkTargetKeyIndPrim_inv (S : Setup) (pk sk : Bytes) (n : ℕ)
    (u : Fin S.N_id) (j : Fin S.N_recv) (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((genSpkTargetKeyIndPrim S u j).run h) := by
  have hI1 : ShInv pk sk (n + 1) h := hI.mono (Nat.le_succ n)
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, htp, hts⟩ := hI
  simp only [genSpkTargetKeyIndPrim, StateT.run]
  split
  · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
      ShInv pk sk (n + 1) x.2) hI1
  split
  swap
  · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
      ShInv pk sk (n + 1) x.2) hI1
  refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.pure ⟨?_, htp, hts⟩
  khol_leaf
private theorem genSpkTargetKeyIndPrim_tb (S : Setup)
    (u : Fin S.N_id) (j : Fin S.N_recv) (h : KeyIndShCrState S) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => x.2.targetBIdx? = h.targetBIdx?)
      ((genSpkTargetKeyIndPrim S u j).run h) := by
  simp only [genSpkTargetKeyIndPrim, StateT.run]
  split
  · exact HoldsOnLeaves.pure rfl
  split
  swap
  · exact HoldsOnLeaves.pure rfl
  exact HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.pure rfl
private theorem pqxdhKeyIndShCrActivePrimImpl1Key_inv (S : Setup) (pk sk : Bytes) (n : ℕ)
    (q : KeyIndQuery S) (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((pqxdhKeyIndShCrActivePrimImpl1Key true S q).run h) := by
  cases q with
  | initPrin u =>
    exact pqxdhKeyIndShCrPrimImpl1Key_inv S pk sk n (.initPrin u) h hI
  | genSPK u j =>
    change HoldsOnLeaves _ (runKeyIndShCrActiveGenSPKPrim true S u j h)
    unfold runKeyIndShCrActiveGenSPKPrim
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases ht : h.targetBIdx? with _ | spkOrd
    · dsimp only
      exact liftShCrBasePrim_inv S pk sk n h hI (.genSPK u j)
    · dsimp only
      split
      · exact genSpkTargetKeyIndPrim_inv S pk sk n u j h hI
      · exact liftShCrBasePrim_inv S pk sk n h hI (.genSPK u j)
  | _ =>
    simpa [pqxdhKeyIndShCrActivePrimImpl1Key] using
      pqxdhKeyIndShCrPrimImpl_inv S pk sk n _ h hI
private theorem pqxdhKeyIndShCrActivePrimImpl1Key_tb (S : Setup)
    (q : KeyIndQuery S) (h : KeyIndShCrState S) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => x.2.targetBIdx? = h.targetBIdx?)
      ((pqxdhKeyIndShCrActivePrimImpl1Key true S q).run h) := by
  cases q with
  | initPrin u => exact liftShCrBasePrim_tb _ h
  | genSPK u j =>
    change HoldsOnLeaves _ (runKeyIndShCrActiveGenSPKPrim true S u j h)
    unfold runKeyIndShCrActiveGenSPKPrim
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases ht : h.targetBIdx? with _ | spkOrd
    · dsimp only; exact ht ▸ liftShCrBasePrim_tb _ h
    · dsimp only; split
      · exact ht ▸ genSpkTargetKeyIndPrim_tb S u j h
      · exact ht ▸ liftShCrBasePrim_tb _ h
  | initiateOPK u i bu =>
    dsimp only [pqxdhKeyIndShCrActivePrimImpl1Key, pqxdhKeyIndShCrPrimImpl]
    split
    · exact HoldsOnLeaves.pure rfl
    · exact runKeyIndShCrInitiatePrim_tb S (.sendOPK u i) u bu h
  | initiateNoOPK u i bu =>
    dsimp only [pqxdhKeyIndShCrActivePrimImpl1Key, pqxdhKeyIndShCrPrimImpl]
    split
    · exact HoldsOnLeaves.pure rfl
    · exact runKeyIndShCrInitiatePrim_tb S (.sendNoOPK u i) u bu h
  | acceptOPK k j i hdr => exact runKeyIndShCrAcceptPrim_tb S k j hdr (.acceptOPK k j i hdr) h
  | acceptNoOPK k j i hdr => exact runKeyIndShCrAcceptPrim_tb S k j hdr (.acceptNoOPK k j i hdr) h
  | _ => exact liftShCrBasePrim_tb _ h
private theorem pqxdhKeyIndShCrActivePrimImpl1Key_inv_act (S : Setup) (pk sk : Bytes) (n : ℕ)
    (q : KeyIndQuery S) (h : KeyIndShCrState S) (hI : ShInvAct pk sk n h) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInvAct pk sk (n + 1) x.2)
      ((pqxdhKeyIndShCrActivePrimImpl1Key true S q).run h) :=
  (holdsOnLeaves_and (pqxdhKeyIndShCrActivePrimImpl1Key_inv S pk sk n q h hI.sh)
    (pqxdhKeyIndShCrActivePrimImpl1Key_tb S q h)).mono fun _ ⟨hS, heq⟩ => ⟨hS, heq ▸ hI.tv⟩
private theorem shcrActiveGenSpkB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (sV : Var Γ₁ shcrStTy) (env : Env Δ) (h : KeyIndShCrState S)
    (sIdx : Nat) (chosen : Bytes) (hs : env.get (Ext.wk sV) = shcrActiveStToVal h sIdx chosen)
    (htv : h.targetBIdx?.isSome = true → 0 < S.N_recv)
    (hB : KeyIndListsBounded h.base K)
    (xV : Var Γ₂ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (Ext.wk xV) = (u.val, j.val)) :
    (shcrActiveGenSpkB S K sV xV).eval env =
      encSCSActive sIdx chosen <$>
        (pqxdhKeyIndShCrActivePrimImpl1Key true S (.genSPK u j)).run h := by
  have hgen : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] [Ext Γ₂ Δ'] (env' : Env Δ'),
      env'.get (Ext.wk sV) = shcrActiveStToVal h sIdx chosen → env'.get (Ext.wk xV) = (u.val, j.val) →
      (onBase sV fun g => genSpkB K g xV).eval env' =
        encSCSActive sIdx chosen <$>
          liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j)) h := by
    intro Δ' _ _ env' hs' hx'
    have ho := onBase_eval S env' sV (scaleTB S h) sIdx chosen hs' (fun g => genSpkB K g xV) _
      (genSpkB_eval (Γ₁ := keyIndStateTy :: _) true S K .zero (.cons (keyIndStateToVal h.base) env')
        h.base rfl hB xV u j (by simpa [Ext.wk, Env.get] using hx'))
    rw [ho]
    exact (liftShCrBasePrim_scaleTB (pqxdhKeyIndImplPrim true S (.genSPK u j)) h ▸
      (Functor.map_map (Prod.map id (scaleTB S)) (encSCS sIdx chosen)
        (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j)) h)).symm).symm.trans rfl
  have hMap := scaleTB_map_div_mod h htv
  unfold shcrActiveGenSpkB
  simp only [pqxdhKeyIndShCrActivePrimImpl1Key, runKeyIndShCrActiveGenSPKPrim,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run]
  rcases ht : h.targetBIdx? with _ | spkOrd
  · simp only [caseOptV, Comp.eval, Expr.eval, v, hs, scTB, shcrActiveStToVal, shcrStToVal,
      hMap, ht, Option.map_none]
    exact hgen env hs hx
  · simp only [caseOptV, Comp.eval, Expr.eval, v, hs, scTB, shcrActiveStToVal, shcrStToVal,
      hMap, ht, Option.map_some]
    have ha : (h.base.spkBundles.any fun x => x.1 == (↑u, ↑j)) =
        (h.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) := by
      congr 1
    by_cases hc : (h.base.spkBundles.length == spkOrd) = true
    · simp only [hc, ↓reduceIte, genSpkTargetKeyIndPrim]
      core_simp [hs, hx, scBase, scUpd, scTPk, scTSk, scTB, scCnt, scIR, scRR, scSIdx, scChosen,
        shcrActiveStToVal, shcrStToVal, scaleTB, List.take_of_length_le, hB.spkBundles_le,
        hB.principals_le, Prod.map, id]
      rw [ha]
      by_cases hDup : (h.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
      · simp [hDup, encSCSActive, shcrActiveStToVal, shcrStToVal, scaleTB, keyIndStateToVal,
          keyIndRespToVal, ht]
      · simp only [hDup, Bool.false_eq_true, ↓reduceIte]
        rcases hfd : h.base.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
        · simp [hfd, encSCSActive, shcrActiveStToVal, shcrStToVal, scaleTB, keyIndStateToVal,
            keyIndRespToVal, ht]
        · simp only [hfd, Option.map_some, Prod.map, id,
            hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp,
            bind_assoc, Function.comp_def, pure_bind, sampleScalar32]
          erw [hs]
          simp [encSCSActive, shcrActiveStToVal, shcrStToVal, scaleTB, keyIndStateToVal,
            keyIndRespToVal, ht, encodeEC, encodeKEM, map_eq_bind_pure_comp]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [← hgen env hs hx]
      by_cases hDup : (h.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
      · unfold onBase genSpkB
        core_simp [hs, hx, scBase, scUpd, scTPk, scTSk, scTB, scCnt, scIR, scRR, scSIdx, scChosen,
          shcrActiveStToVal, shcrStToVal, scaleTB, List.take_of_length_le, hB.spkBundles_le,
          Prod.map, id]
        simp [hDup]
      · simp only [Bool.not_eq_true] at hDup
        rcases hfd : h.base.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
        · unfold onBase genSpkB
          core_simp [hs, hx, scBase, scUpd, scTPk, scTSk, scTB, scCnt, scIR, scRR, scSIdx, scChosen,
            shcrActiveStToVal, shcrStToVal, scaleTB, List.take_of_length_le, hB.spkBundles_le,
            hB.principals_le, Prod.map, id]
          simp [hDup, hfd]
        · rw [hgen env hs hx]
          have hCond1 :
              (eAny K (stSpks (scBase (Expr.var (Ext.wk sV)))) fun e =>
                nat2Eq (Expr.var (Ext.wk e)).fst (Expr.var (Ext.wk xV))).eval
                (Env.cons (t := .prod .nat .nat) (spkOrd, 0) env) = false := by
            core_simp [hs, hx, scBase, shcrActiveStToVal, shcrStToVal, scaleTB,
              List.take_of_length_le, hB.spkBundles_le, Prod.map, id]
            exact hDup
          have hFind :
              (eFind K (stPrin (scBase (Expr.var (Ext.wk sV)))) fun e =>
                natEq (Expr.var (Ext.wk e)).fst (Expr.var (Ext.wk xV)).fst).eval
                (Env.cons (t := .prod .nat .nat) (spkOrd, 0) env) =
                some (i, SignalPqxdh.Security.ReductionDsl.KeyInd.principalEntryToVal e) := by
            core_simp [hs, hx, scBase, shcrActiveStToVal, shcrStToVal, scaleTB,
              List.take_of_length_le, hB.principals_le, Prod.map, id]
            simp [hfd]
          simp only [hCond1, Bool.false_eq_true, ↓reduceIte, hFind]
          have hCond2 :
              (natEq (stSpks (scBase (Expr.var (Ext.wk sV)))).len
                (Expr.var (Ext.wk (Γ := .prod .nat .nat :: Δ) Var.zero)).fst).eval
                (Env.cons
                  (t := .prod .nat SignalPqxdh.Security.ReductionDsl.KeyInd.principalEntryTy)
                  (i, SignalPqxdh.Security.ReductionDsl.KeyInd.principalEntryToVal e)
                  (Env.cons (t := .prod .nat .nat) (spkOrd, 0) env)) = false := by
            simp [Expr.eval, natEq_eval, Ext.wk, hs, scBase, shcrActiveStToVal, shcrStToVal,
              scaleTB, keyIndStateToVal, hc]
          simp only [hCond2, Bool.not_false, ↓reduceIte]
          exact hgen _ (by simpa [Ext.wk, Env.get] using hs)
            (by simpa [Ext.wk, Env.get] using hx)
private theorem shcr1KeyActivePostC_eval (S : Setup) (K n : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (sV : Var Γ₁ shcrStTy) (qV : Var Γ₂ keyIndQueryTy) (env : Env Δ)
    (q : KeyIndQuery S) (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (Ext.wk sV) = shcrActiveStToVal h sIdx chosen)
    (htv : h.targetBIdx?.isSome = true → 0 < S.N_recv)
    (hq : env.get (Ext.wk qV) = keyIndQueryToVal q)
    (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcr1KeyActivePostC S K sV qV).eval env =
      encSCSActive sIdx chosen <$> (pqxdhKeyIndShCrActivePrimImpl1Key true S q).run h := by
  have hK : KeyIndListsBounded h.base K := hB.mono (by omega)
  have hBs : KeyIndListsBounded (scaleTB S h).base n := hB
  cases q with
  | initPrin u =>
    have hEq : (shcr1KeyActivePostC S K sV qV).eval env = (shcr1KeyPostC S K sV qV).eval env := by
      unfold shcr1KeyActivePostC shcr1KeyPostC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcr1KeyPostC_eval S K n sV qV env (.initPrin u) (scaleTB S h) sIdx chosen hs hq hBs hn]
    change encSCS sIdx chosen <$> (liftShCrBasePrim _).run (scaleTB S h) = _
    rw [liftShCrBasePrim_scaleTB, Functor.map_map]; rfl
  | genSPK u j =>
    unfold shcr1KeyActivePostC shcrActivePostTailC
    simp only [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal, Env.get, Ext.wk]
    exact shcrActiveGenSpkB_eval S K sV _ h sIdx chosen
      (by simpa [Ext.wk, Env.get] using hs) htv hK .zero u j rfl
  | corruptIK u =>
    have hEq : (shcr1KeyActivePostC S K sV qV).eval env = (shcr1KeyPostC S K sV qV).eval env := by
      unfold shcr1KeyActivePostC shcr1KeyPostC shcrActivePostTailC shcrPostTailC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcr1KeyPostC_eval S K n sV qV env (.corruptIK u) (scaleTB S h) sIdx chosen hs hq hBs hn]
    change encSCS sIdx chosen <$> (liftShCrBasePrim _).run (scaleTB S h) = _
    rw [liftShCrBasePrim_scaleTB, Functor.map_map]; rfl
  | initiateOPK u i bu =>
    have hEq : (shcr1KeyActivePostC S K sV qV).eval env = (shcr1KeyPostC S K sV qV).eval env := by
      unfold shcr1KeyActivePostC shcr1KeyPostC shcrActivePostTailC shcrPostTailC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcr1KeyPostC_eval S K n sV qV env (.initiateOPK u i bu) (scaleTB S h) sIdx chosen hs hq hBs hn]
    dsimp only [pqxdhKeyIndShCrPrimImpl1Key, pqxdhKeyIndShCrActivePrimImpl1Key,
      pqxdhKeyIndShCrPrimImpl]
    split
    · rfl
    · change encSCS sIdx chosen <$> (runKeyIndShCrInitiatePrim S _ u bu).run (scaleTB S h) = _
      rw [runKeyIndShCrInitiatePrim_scaleTB, Functor.map_map]; rfl
  | initiateNoOPK u i bu =>
    have hEq : (shcr1KeyActivePostC S K sV qV).eval env = (shcr1KeyPostC S K sV qV).eval env := by
      unfold shcr1KeyActivePostC shcr1KeyPostC shcrActivePostTailC shcrPostTailC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcr1KeyPostC_eval S K n sV qV env (.initiateNoOPK u i bu) (scaleTB S h) sIdx chosen hs hq hBs hn]
    dsimp only [pqxdhKeyIndShCrPrimImpl1Key, pqxdhKeyIndShCrActivePrimImpl1Key,
      pqxdhKeyIndShCrPrimImpl]
    split
    · rfl
    · change encSCS sIdx chosen <$> (runKeyIndShCrInitiatePrim S _ u bu).run (scaleTB S h) = _
      rw [runKeyIndShCrInitiatePrim_scaleTB, Functor.map_map]; rfl
  | acceptOPK k j i hdr =>
    have hEq : (shcr1KeyActivePostC S K sV qV).eval env = (shcr1KeyPostC S K sV qV).eval env := by
      unfold shcr1KeyActivePostC shcr1KeyPostC shcrActivePostTailC shcrPostTailC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcr1KeyPostC_eval S K n sV qV env (.acceptOPK k j i hdr) (scaleTB S h) sIdx chosen hs hq hBs hn]
    change encSCS sIdx chosen <$> (runKeyIndShCrAcceptPrim S k j hdr _).run (scaleTB S h) = _
    rw [runKeyIndShCrAcceptPrim_scaleTB, Functor.map_map]; rfl
  | acceptNoOPK k j i hdr =>
    have hEq : (shcr1KeyActivePostC S K sV qV).eval env = (shcr1KeyPostC S K sV qV).eval env := by
      unfold shcr1KeyActivePostC shcr1KeyPostC shcrActivePostTailC shcrPostTailC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcr1KeyPostC_eval S K n sV qV env (.acceptNoOPK k j i hdr) (scaleTB S h) sIdx chosen hs hq hBs hn]
    change encSCS sIdx chosen <$> (runKeyIndShCrAcceptPrim S k j hdr _).run (scaleTB S h) = _
    rw [runKeyIndShCrAcceptPrim_scaleTB, Functor.map_map]; rfl
  | _ =>
    have hEq : (shcr1KeyActivePostC S K sV qV).eval env = (shcr1KeyPostC S K sV qV).eval env := by
      unfold shcr1KeyActivePostC shcr1KeyPostC shcrActivePostTailC shcrPostTailC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcr1KeyPostC_eval S K n sV qV env _ (scaleTB S h) sIdx chosen hs hq hBs hn]
    change encSCS sIdx chosen <$> (liftShCrBasePrim _).run (scaleTB S h) = _
    rw [liftShCrBasePrim_scaleTB, Functor.map_map]; rfl

/-! ## Stage 1 simulation -/
private def initShOpt (S : Setup) (secb : Bool) (tb? : Option ℕ) (pk sk : Bytes) :
    KeyIndShCrState S where
  base        := KeyIndState.empty S secb
  targetBIdx? := tb?
  targetPk    := pk
  targetSk    := sk
private theorem initShOpt_inv (S : Setup) (secb : Bool) (tb? : Option ℕ) (pk sk : Bytes) :
    ShInv pk sk 0 (initShOpt S secb tb? pk sk) :=
  ⟨⟨by simp [initShOpt, KeyIndState.empty], by simp [initShOpt, KeyIndState.empty],
    by simp [initShOpt, KeyIndState.empty], by simp [initShOpt, KeyIndState.empty],
    by simp [initShOpt, KeyIndState.empty], by simp [initShOpt, KeyIndState.empty],
    by simp [initShOpt, KeyIndState.empty], by simp [initShOpt, KeyIndState.empty],
    by simp [initShOpt, KeyIndState.empty], by simp [initShOpt, KeyIndState.empty]⟩,
    rfl, rfl⟩
private theorem activeProd_ne_zero_imp_nRecv_pos {S : Setup} {q_on : ℕ}
    (h0 : activeSpkCount S q_on * activeSendCount S q_on ≠ 0) : 0 < S.N_recv := by
  have h1 : activeSpkCount S q_on ≠ 0 := left_ne_zero_of_mul h0
  by_contra hN
  simp [activeSpkCount, Setup.N_spk_tot, show S.N_recv = 0 by omega] at h1
private theorem initShOpt_none_inv_act (S : Setup) (secb : Bool) (pk sk : Bytes) :
    ShInvAct pk sk 0 (initShOpt S secb none pk sk) :=
  ⟨initShOpt_inv _ _ _ _ _, by simp [initShOpt]⟩
private theorem initShOpt_some_inv_act {S : Setup} {q_on : ℕ}
    (h0 : activeSpkCount S q_on * activeSendCount S q_on ≠ 0)
    (secb : Bool) (spkOrd : ℕ) (pk sk : Bytes) :
    ShInvAct pk sk 0 (initShOpt S secb (some spkOrd) pk sk) :=
  ⟨initShOpt_inv _ _ _ _ _, fun _ => activeProd_ne_zero_imp_nRecv_pos h0⟩
private def stepMid1KeyActive (S : Setup) (sIdx : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S) :
    OracleComp PrimBaseSpec
      ((KeyIndResponse × KeyIndShCrState S) ⊕ (Bytes × (PauseMid S × KeyIndShCrState S))) := do
  match ← tryPauseMid S sIdx q h with
  | some d => pure (.inr (d.2.1.pqspkB, (d, h)))
  | none => Sum.inl <$> (pqxdhKeyIndShCrActivePrimImpl1Key true S q).run h
private theorem tryPauseMid_scaleTB (S : Setup) (sIdx : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) :
    tryPauseMid S sIdx q (scaleTB S h) = tryPauseMid S sIdx q h := by
  cases q <;> rfl
private theorem shcr1KeyActivePreC_eval (S : Setup) (K n : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (sIdx : ℕ) (chosen : Bytes)
    (htv : h.targetBIdx?.isSome = true → 0 < S.N_recv)
    (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcr1KeyActivePreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).eval
        (.cons (shcrActiveStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      Sum.map (encSCSActive sIdx chosen)
        (Prod.map id (Prod.map encPause (shcrActiveStToVal · sIdx chosen))) <$>
        stepMid1KeyActive S sIdx q h := by
  have hK : KeyIndListsBounded (scaleTB S h).base K := hB.mono (by omega)
  unfold shcr1KeyActivePreC
  simp only [bindV, caseOptV, Comp.eval]
  rw [pauseCheckC_eval S K _ _ (scaleTB S h) sIdx chosen rfl hK _ q rfl, tryPauseMid_scaleTB]
  simp only [stepMid1KeyActive, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | d
  · simp only [Option.map_none, Expr.eval]
    rw [shcr1KeyActivePostC_eval S K n _ _ _ q h sIdx chosen rfl htv rfl hB hn]
    simp [map_eq_bind_pure_comp, Expr.eval, v]
  · obtain ⟨sid, bu, k, e⟩ := d
    simp [Expr.eval, v, encPause, shcrActiveStToVal, shcrStToVal, preKeyBundleToVal]
private theorem stepUntilShCr1KeyActive_eq (S : Setup) (sIdx : ℕ)
    (mx : OracleComp (unifSpec + keyIndSpec S) Bool) (h : KeyIndShCrState S) (fuel : ℕ) :
    stepUntilShCrFuelKeyInd1KeyActivePrim S sIdx mx h fuel =
      Gsh S <$> stepUntilPauseFuel false (stepMid1KeyActive S sIdx) mx fuel h := by
  refine stepUntilPauseFuel_char false (stepMid1KeyActive S sIdx) (Gsh S)
    (fun mx fuel h => stepUntilShCrFuelKeyInd1KeyActivePrim S sIdx mx h fuel) ?_ ?_ ?_ ?_ mx fuel h
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilShCrFuelKeyInd1KeyActivePrim]; rw [OracleComp.construct_query_bind]
  · intro gq k s
    simp only [stepUntilShCrFuelKeyInd1KeyActivePrim]; rw [OracleComp.construct_query_bind]; rfl
  · intro gq k fuel s
    simp only [stepUntilShCrFuelKeyInd1KeyActivePrim]; rw [OracleComp.construct_query_bind]
    dsimp only
    rw [tryPauseMid_shallow, bind_map_left]
    simp only [stepMid1KeyActive, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with _ | d
    · simp only [Option.map_none, map_eq_bind_pure_comp, bind_assoc]; rfl
    · simp only [Option.map_some, pure_bind]; rfl
private theorem runWithFuelShCr1KeyActive_eq (S : Setup)
    (mx : OracleComp (unifSpec + keyIndSpec S) Bool) (h : KeyIndShCrState S) (fuel : ℕ) :
    runWithFuelKeyInd1KeyActiveShCrPrim S mx h fuel =
      runWithFuelPrim false (fun q s => (pqxdhKeyIndShCrActivePrimImpl1Key true S q).run s)
        mx fuel h := by
  have := runWithFuelPrim_char false
    (fun q s => (pqxdhKeyIndShCrActivePrimImpl1Key true S q).run s) id
    (fun mx fuel h => runWithFuelKeyInd1KeyActiveShCrPrim S mx h fuel) (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithFuelKeyInd1KeyActiveShCrPrim]; rw [OracleComp.construct_query_bind])
    (fun gq k s => by
      simp only [runWithFuelKeyInd1KeyActiveShCrPrim]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithFuelKeyInd1KeyActiveShCrPrim]; rw [OracleComp.construct_query_bind])
    mx fuel h
  rw [this, id_map]
private theorem stepMid1KeyActive_inv_act (S : Setup) (sIdx : ℕ) (pk sk : Bytes) (n : ℕ)
    (q : KeyIndQuery S) (h : KeyIndShCrState S) (hI : ShInvAct pk sk n h) :
    HoldsOnLeaves (PreStepInvC (ShInvAct pk sk) (fun d : PauseMid S => d.2.1.pqspkB) n)
      (stepMid1KeyActive S sIdx q h) := by
  unfold stepMid1KeyActive
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | d
  · exact HoldsOnLeaves.map _ (pqxdhKeyIndShCrActivePrimImpl1Key_inv_act S pk sk n q h hI)
      fun _ hx => hx
  · exact HoldsOnLeaves.pure ⟨rfl, hI⟩
private def midRun1KeyActive (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (ℕ × (Option Bytes ×
      RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))) :=
  let n_spk := activeSpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  if n_spk * n_send = 0 then do
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid1KeyActive S (b.q_total + 1)) A.run b.q_total
      (initShOpt S secb none pk sk)
    pure (b.q_total + 1, r)
  else do
    let spkOrd ← embedUnif (sampleIndexRange n_spk)
    let sIdx ← embedUnif (sampleIndexRange n_send)
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid1KeyActive S sIdx) A.run b.q_total
      (initShOpt S secb (some spkOrd) pk sk)
    pure (sIdx, r)
private def midAdv1KeyActive (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv where
  State := Bytes × Bytes × ℕ × (Option Bytes ×
    RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))
  choosePk := fun pk sk => (fun x => (chosenOf pk x.2.2, (pk, sk, x))) <$> midRun1KeyActive S b A.1 pk sk
  findCollision := fun st => findCollisionKeyInd1KeyActivePrim S b (toShallow st)
  q_prim := primQueryBudget S b
private theorem evalDist_sampleIndexRange_bind_true {N : ℕ} (hN : 0 < N) (g : ℕ → ProbComp Bool) :
    𝒟[sampleIndexRange N >>= g] {true} = ∑ k ∈ Finset.range N, 𝒟[g k] {true} * (N : ℝ≥0∞)⁻¹ := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : MeasurableSpace (Fin N) := ⊤
  simp only [sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
      (Measurable.of_discrete).aemeasurable, MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {true} * (N : ℝ≥0∞)⁻¹) N
private theorem sum_range_mul_div_mod_ennreal (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.range (M * N), g (k / N) (k % N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, g i j := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]; congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Nat.add_comm (m * N) j, Nat.add_mul_div_right j m (by omega), Nat.div_eq_of_lt hj,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
private theorem evalDist_sampleIndexRange_mul_true {M N : ℕ} (hMN : 0 < M * N)
    (g : ℕ → ℕ → ProbComp Bool) :
    𝒟[sampleIndexRange (M * N) >>= fun k => g (k / N) (k % N)] {true} =
      𝒟[sampleIndexRange M >>= fun i => sampleIndexRange N >>= fun j => g i j] {true} := by
  have hM : 0 < M := Nat.pos_of_mul_pos_right hMN
  have hN : 0 < N := Nat.pos_of_mul_pos_left hMN
  rw [evalDist_sampleIndexRange_bind_true hMN,
    sum_range_mul_div_mod_ennreal M N (fun i j => 𝒟[g i j] {true} * ((M * N : ℕ) : ℝ≥0∞)⁻¹),
    evalDist_sampleIndexRange_bind_true hM]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [evalDist_sampleIndexRange_bind_true hN, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, ENNReal.mul_inv (.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)))
    (.inl (ENNReal.natCast_ne_top M)), mul_assoc, mul_comm (M : ℝ≥0∞)⁻¹]
private theorem kemShCrExp_mid1KeyActive_core (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrReductionKeyInd1KeyActive S b A) = KemShCr P (midAdv1KeyActive S b A) := by
  let n_spk := activeSpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let h1 (tb? : Option ℕ) (sIdx : ℕ) (pk sk : Bytes) :
      OracleComp PrimBaseSpec (Bytes × (midAdv1KeyActive S b A).State) := do
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid1KeyActive S sIdx) A.1.run b.q_total
      (initShOpt S secb tb? pk sk)
    pure (chosenOf pk r.2, (pk, sk, sIdx, r))
  let body (tb? : Option ℕ) (sIdx : ℕ) (x : Bytes × Bytes) : ProbComp Bool := do
    let (pk', st) ← simulateQ (primBaseImpl P) (h1 tb? sIdx x.1 x.2)
    let r ← sampleCoins32
    let some (ss, ct) := P.kemEncaps pk' r | return false
    let ct' ← simulateQ (primBaseImpl P) ((midAdv1KeyActive S b A).findCollision st ss ct)
    return (decide (P.kemDecaps x.2 ct' = some ss) && decide (ct' ≠ ct ∨ pk' ≠ x.1) &&
            decide (ct'.length = kyberCtLen ∧ pk'.length = kyberPkLen))
  have hc1 : ∀ pk sk, (shcrReductionKeyInd1KeyActive S b A).choosePk pk sk = (do
      let idx ← embedUnif (sampleIndexRange (n_spk * n_send))
      let y ← h1 (if n_spk * n_send = 0 then none else some (idx / n_send))
                 (if n_spk * n_send = 0 then b.q_total + 1 else idx % n_send) pk sk
      pure (y.1, toShallow y.2)) := by
    intro pk sk
    dsimp only [shcrReductionKeyInd1KeyActive, shcrReductionKeyInd1KeyActiveCore,
      choosePkKeyInd1KeyActivePrimAt, initShOpt, h1, n_spk, n_send]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun idx => bind_congr fun secb => ?_
    rw [stepUntilShCr1KeyActive_eq, bind_map_left]
    refine bind_congr fun r => ?_
    rcases r with ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ <;> rfl
  have hExp1 : kemShCrExp P (shcrReductionKeyInd1KeyActive S b A) = (do
      let x ← sampleKemKeyGen P
      let idx ← sampleIndexRange (n_spk * n_send)
      body (if n_spk * n_send = 0 then none else some (idx / n_send))
           (if n_spk * n_send = 0 then b.q_total + 1 else idx % n_send) x) := by
    unfold kemShCrExp; refine bind_congr fun ⟨pk, sk⟩ => ?_
    dsimp only [body]; rw [hc1 pk sk]
    simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun idx => bind_congr fun y => ?_
    rcases y with ⟨pk', st⟩
    dsimp only; refine bind_congr fun r => ?_
    cases P.kemEncaps pk' r <;> rfl
  unfold KemShCr
  by_cases h0 : n_spk * n_send = 0
  · have hExp2 : kemShCrExp P (midAdv1KeyActive S b A) =
        (sampleKemKeyGen P >>= body none (b.q_total + 1)) := by
      unfold kemShCrExp; refine bind_congr fun ⟨pk, sk⟩ => ?_
      simp only [midAdv1KeyActive, midRun1KeyActive, h0, ↓reduceIte, n_spk, n_send, h1, body,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; rfl
    have hEq0 : kemShCrExp P (shcrReductionKeyInd1KeyActive S b A) =
        (sampleKemKeyGen P >>= body none (b.q_total + 1)) := by
      rw [hExp1]; refine bind_congr fun x => ?_; simp [h0, sampleIndexRange]
    rw [hEq0, hExp2]
  · let sample2 : ProbComp (ℕ × ℕ) := do
      let spkOrd ← sampleIndexRange n_spk; let sIdx ← sampleIndexRange n_send; pure (spkOrd, sIdx)
    have hExp2 : kemShCrExp P (midAdv1KeyActive S b A) = (do
        let x ← sampleKemKeyGen P; let q ← sample2; body (some q.1) q.2 x) := by
      unfold kemShCrExp; refine bind_congr fun ⟨pk, sk⟩ => ?_
      simp only [midAdv1KeyActive, midRun1KeyActive, h0, ↓reduceIte, n_spk, n_send, h1, body,
        sample2, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_embedUnif,
        bind_assoc, pure_bind]; rfl
    have hExp1' : kemShCrExp P (shcrReductionKeyInd1KeyActive S b A) = (do
        let x ← sampleKemKeyGen P; let idx ← sampleIndexRange (n_spk * n_send)
        body (some (idx / n_send)) (idx % n_send) x) := by
      rw [hExp1]; refine bind_congr fun x => bind_congr fun idx => ?_; simp [h0]
    rw [show 𝒟[kemShCrExp P (shcrReductionKeyInd1KeyActive S b A)] =
          𝒟[sampleIndexRange (n_spk * n_send) >>= fun idx =>
            sampleKemKeyGen P >>= body (some (idx / n_send)) (idx % n_send)] from by
          rw [hExp1', OracleComp.evalDist_bind_bind_swap],
        show 𝒟[kemShCrExp P (midAdv1KeyActive S b A)] =
          𝒟[sample2 >>= fun q => sampleKemKeyGen P >>= body (some q.1) q.2] from by
          rw [hExp2, OracleComp.evalDist_bind_bind_swap]]
    simp only [sample2, bind_assoc, pure_bind]
    exact evalDist_sampleIndexRange_mul_true (Nat.pos_of_ne_zero h0)
      (fun spkOrd sIdx => sampleKemKeyGen P >>= body (some spkOrd) sIdx)
private def stepPreD1KeyActive (S : Setup) (q_on Q K : ℕ) (q : KeyIndQuery S)
    (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec ((KeyIndResponse × shcrStTy.denote) ⊕
      (Bytes × (pauseTy.denote × shcrStTy.denote))) :=
  (shcrKeyInd1KeyActiveProgK S q_on Q K).handlePre.eval
    (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote ⊕ (Bytes × (pauseTy.denote × shcrStTy.denote))) => match x with
    | .inl (rVal, st') => pure (.inl (valToKeyIndResp rVal, st'))
    | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st')))
private theorem stepPreD1KeyActive_eq (S : Setup) (q_on Q K K' : ℕ) (sIdx : ℕ) (pk sk : Bytes)
    (q : KeyIndQuery S) (h : KeyIndShCrState S) (hI : ShInvAct pk sk K' h) (hK : K' + 1 ≤ K) :
    stepPreD1KeyActive S q_on Q K q (shcrActiveStToVal h sIdx pk) =
      Sum.map (Prod.map id (shcrActiveStToVal · sIdx pk))
        (Prod.map id (Prod.map encPause (shcrActiveStToVal · sIdx pk))) <$>
        stepMid1KeyActive S sIdx q h := by
  unfold stepPreD1KeyActive
  have hpre : (shcrKeyInd1KeyActiveProgK S q_on Q K).handlePre.eval
      (.cons (shcrActiveStToVal h sIdx pk) (.cons (keyIndQueryToVal q) .nil)) = _ :=
    shcr1KeyActivePreC_eval S K K' q h sIdx pk hI.tv hI.sh.bnd hK
  rw [hpre, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h'⟩ | ⟨c, d, h'⟩
  · have hr : valToKeyIndResp (keyIndRespToVal r) = r := keyIndRdec_keyIndRenc r
    simp only [Function.comp_apply, Sum.map_inl, encSCSActive, Prod.map, id]
    erw [pure_bind]
    simp only [hr]
  · rfl
private theorem eval1_1KeyActive_unfold (S : Setup) (q_on Q K : ℕ) (A : KeyIndAdversary S)
    (pk sk : Bytes) (fuel : ℕ) :
    (shcrKeyInd1KeyActiveProgK S q_on Q K).eval1 (fun _ => A.run) (pk, sk) fuel false =
    (do
      let (_, st0) ← (shcrKeyInd1KeyActiveProgK S q_on Q K).init.eval (.cons (pk, sk) .nil)
      let r : Option Bytes × RedProg2State (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote ←
          stepUntilPauseFuel false (stepPreD1KeyActive S q_on Q K) A.run fuel st0
      match r with
      | (_, .done aOut stFinal) => do
        let v ← (shcrKeyInd1KeyActiveProgK S q_on Q K).chDone.eval (.cons stFinal (.cons aOut .nil))
        pure (v, .done aOut stFinal)
      | (c?, .paused gq p stPaused c) =>
        let ch1 := c?.getD pk
        pure (ch1, .paused gq ch1 p stPaused c) :
      OracleComp PrimBaseSpec (Bytes × Mid (keyIndSpec S) Bool pauseTy.denote
        shcrStTy.denote Bytes)) := by
  unfold TwoStageCostedReduction.eval1
  refine bind_congr (m := OracleComp PrimBaseSpec) fun ast0 => ?_
  rcases ast0 with ⟨a, st0⟩
  dsimp only
  rw [GRed2_run1_eq_stepUntilPauseFuel (shcrKeyInd1KeyActiveProgK S q_on Q K) false pk A.run fuel st0,
    bind_map_left]
  refine bind_congr2 ?_ fun r => ?_
  · congr 1; funext q st; unfold stepPreD1KeyActive
    refine bind_congr fun x => ?_
    rcases x with ⟨_, _⟩ | ⟨_, _, _⟩ <;> rfl
  rcases r with ⟨c?, ⟨aOut, stFinal⟩ | ⟨gq, p, stPaused, c⟩⟩ <;> rfl
private theorem stepRun1KeyActive_bounded (S : Setup) (q_on Q K Ks sIdx : ℕ) (pk sk : Bytes)
    (A : KeyIndAdversary S) (h0 : KeyIndShCrState S) (hI0 : ShInvAct pk sk 0 h0)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) Ks)
    (hK : Ks + 1 ≤ K) :
    HoldsOnLeaves (Stage1InvC (ShInvAct pk sk) (fun d : PauseMid S => d.2.1.pqspkB) Ks)
        (stepUntilPauseFuel false (stepMid1KeyActive S sIdx) A.run Ks h0) ∧
      stepUntilPauseFuel false (stepPreD1KeyActive S q_on Q K) A.run Ks (shcrActiveStToVal h0 sIdx pk) =
        Prod.map id (RedProg2State.mapSt encPause (shcrActiveStToVal · sIdx pk)) <$>
          stepUntilPauseFuel false (stepMid1KeyActive S sIdx) A.run Ks h0 :=
  stepUntilPauseFuel_map_boundedC false encPause (shcrActiveStToVal · sIdx pk)
    (ShInvAct pk sk) (fun d : PauseMid S => d.2.1.pqspkB) (fun hnm hI => ShInvAct.mono hnm hI)
    (stepMid1KeyActive S sIdx) (stepPreD1KeyActive S q_on Q K) Ks
    (fun _ q st hn hI => stepPreD1KeyActive_eq S q_on Q K _ sIdx pk sk q st hI (by omega))
    (fun n q st hI => stepMid1KeyActive_inv_act S sIdx pk sk n q st hI)
    A.run Ks hA Ks 0 h0 hI0 (by omega)
private theorem midRun1KeyActive_inv (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S)
    (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total) :
    HoldsOnLeaves
      (fun x => Stage1InvC (ShInvAct pk sk) (fun d : PauseMid S => d.2.1.pqspkB) b.q_total x.2)
      (midRun1KeyActive S b A pk sk) := by
  dsimp only [midRun1KeyActive]
  split_ifs with h0
  · refine HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun1KeyActive_bounded S b.q_on b.q_total (b.q_total + 1) b.q_total
      (b.q_total + 1) pk sk A (initShOpt S secb none pk sk) (initShOpt_none_inv_act _ _ _ _) hA
      le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr
  · refine HoldsOnLeaves.bind_const _ fun spkOrd => HoldsOnLeaves.bind_const _ fun sIdx =>
      HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun1KeyActive_bounded S b.q_on b.q_total (b.q_total + 1) b.q_total
      sIdx pk sk A (initShOpt S secb (some spkOrd) pk sk) (initShOpt_some_inv_act h0 _ _ _ _) hA
      le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr
private theorem shcr1KeyActiveInit_eval (S : Setup) (q_on Q K : ℕ) (pk sk : Bytes) :
    (shcrKeyInd1KeyActiveProgK S q_on Q K).init.eval (.cons (pk, sk) .nil) =
      if activeSpkCount S q_on * activeSendCount S q_on = 0 then (do
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrActiveStToVal (initShOpt S secb none pk sk) (Q + 1) pk))
      else (do
        let spkOrd ← embedUnif (sampleIndexRange (activeSpkCount S q_on))
        let sIdx ← embedUnif (sampleIndexRange (activeSendCount S q_on))
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrActiveStToVal (initShOpt S secb (some spkOrd) pk sk) sIdx pk)) := by
  dsimp only [shcrKeyInd1KeyActiveProgK]
  split_ifs with h0
  · simp only [bindV, Comp.eval, sBool_eval]
    refine bind_congr fun secb => ?_
    simp [Expr.eval, v, emptyStE, shcrActiveStToVal, shcrStToVal, scaleTB, initShOpt,
      keyIndStateToVal, KeyIndState.empty]
  · have hN : 0 < S.N_recv := activeProd_ne_zero_imp_nRecv_pos h0
    simp only [bindV, Comp.eval, sIndex_eval, sBool_eval]
    change (embedUnif (sampleIndexRange _) >>= fun spkOrd =>
      embedUnif (sampleIndexRange _) >>= fun sIdx => _) = _
    refine bind_congr fun spkOrd => bind_congr fun sIdx => bind_congr fun secb => ?_
    simp [Expr.eval, v, emptyStE, shcrActiveStToVal, shcrStToVal, scaleTB, initShOpt,
      keyIndStateToVal, KeyIndState.empty, Nat.mul_div_cancel _ hN, Nat.mul_mod_left]
private theorem eval1_1KeyActive_eq (S : Setup) (K : ℕ) (b : QueryBudget) (A : KeyIndAdversary S)
    (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    (shcrKeyInd1KeyActiveProgK S b.q_on b.q_total K).eval1 (fun _ => A.run) (pk, sk) b.q_total false =
    (fun x => (chosenOf pk x.2.2, encMidActive pk x)) <$> midRun1KeyActive S b A pk sk := by
  have hBody : ∀ tb? sIdx secb, ShInvAct pk sk 0 (initShOpt S secb tb? pk sk) →
      (stepUntilPauseFuel false (stepPreD1KeyActive S b.q_on b.q_total K) A.run b.q_total
        (shcrActiveStToVal (initShOpt S secb tb? pk sk) sIdx pk) >>= fun r =>
        match r with
        | (_, .done aOut stFinal) => do
          let v ← (shcrKeyInd1KeyActiveProgK S b.q_on b.q_total K).chDone.eval
            (.cons stFinal (.cons aOut .nil))
          pure (v, .done aOut stFinal)
        | (c?, .paused gq p stPaused c) =>
          let ch1 := c?.getD pk
          pure (ch1, .paused gq ch1 p stPaused c)) =
      (stepUntilPauseFuel false (stepMid1KeyActive S sIdx) A.run b.q_total
        (initShOpt S secb tb? pk sk) >>= fun r =>
        pure (chosenOf pk r.2, encMidActive pk (sIdx, r))) := by
    intro tb? sIdx secb hI0
    obtain ⟨hInv, hEq⟩ := stepRun1KeyActive_bounded S b.q_on b.q_total K b.q_total sIdx pk sk A
      (initShOpt S secb tb? pk sk) hI0 hA hK
    erw [hEq, bind_map_left]
    refine hInv.bind_congr _ _ fun r hr => ?_
    obtain ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ := r
    · obtain ⟨rfl, hI⟩ := hr
      simp [shcrKeyInd1KeyActiveProgK, Comp.eval, Expr.eval, shcrActiveStToVal, shcrStToVal,
        scaleTB, chosenOf, encMidActive, RedProg2State.mapSt, hI.sh.tpk]
    · obtain ⟨rfl, -⟩ := hr; rfl
  rw [eval1_1KeyActive_unfold, shcr1KeyActiveInit_eval]
  dsimp only [midRun1KeyActive]
  split_ifs with h0 <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · refine bind_congr fun secb => hBody none (b.q_total + 1) secb (initShOpt_none_inv_act _ _ _ _)
  · refine bind_congr fun spkOrd => bind_congr fun sIdx => bind_congr fun secb =>
      hBody (some spkOrd) sIdx secb (initShOpt_some_inv_act h0 _ _ _ _)

/-! ## Stage 2 simulation and `KemShCr` advantage equality -/
private def stepPostD1KeyActive (S : Setup) (q_on Q K : ℕ) (q : KeyIndQuery S)
    (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec (KeyIndResponse × shcrStTy.denote) :=
  (shcrKeyInd1KeyActiveProgK S q_on Q K).handlePost.eval
    (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote) => pure (valToKeyIndResp x.1, x.2)
private theorem stepPostD1KeyActive_eq (S : Setup) (q_on Q K Ks sIdx : ℕ) (pk sk chosen : Bytes)
    (q : KeyIndQuery S) (h : KeyIndShCrState S) (hI : ShInvAct pk sk Ks h) (hK : Ks + 1 ≤ K) :
    stepPostD1KeyActive S q_on Q K q (shcrActiveStToVal h sIdx chosen) =
      Prod.map id (shcrActiveStToVal · sIdx chosen) <$>
        (pqxdhKeyIndShCrActivePrimImpl1Key true S q).run h := by
  unfold stepPostD1KeyActive
  have hpost : (shcrKeyInd1KeyActiveProgK S q_on Q K).handlePost.eval
      (.cons (shcrActiveStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      encSCSActive sIdx chosen <$> (pqxdhKeyIndShCrActivePrimImpl1Key true S q).run h :=
    shcr1KeyActivePostC_eval S K Ks (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero _ q h sIdx chosen rfl hI.tv rfl hI.sh.bnd hK
  rw [hpost, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  have hr : valToKeyIndResp (keyIndRespToVal x.1) = x.1 := keyIndRdec_keyIndRenc x.1
  simp only [Function.comp_apply, encSCSActive, Prod.map, id]
  erw [pure_bind]
  simp only [hr]
private theorem eval2_1KeyActive_done (S : Setup) (q_on Q K fuel : ℕ) (a : Bool)
    (st : shcrStTy.denote) (ss ct : Bytes) :
    (shcrKeyInd1KeyActiveProgK S q_on Q K).eval2 (.done a st) (ss, ct) fuel false =
    (shcrKeyIndProg S Q K).finish.eval (.cons st (.cons a (.cons (ss, ct) .nil))) := by
  simp only [TwoStageCostedReduction.eval2, pure_bind]; rfl
private theorem eval2_1KeyActive_paused (S : Setup) (q_on Q K fuel : ℕ) (q : KeyIndQuery S)
    (ch : Bytes) (p : pauseTy.denote) (st : shcrStTy.denote)
    (k : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool)
    (ss ct : Bytes) :
    (shcrKeyInd1KeyActiveProgK S q_on Q K).eval2 (.paused q ch p st k) (ss, ct) fuel false =
    ((shcrKeyIndProg S Q K).resume.eval (.cons st (.cons p (.cons (ss, ct) .nil))) >>=
      fun (x : SCS.denote) => runWithFuelPrim false (stepPostD1KeyActive S q_on Q K)
        (k (valToKeyIndResp x.1)) fuel x.2 >>= fun (y : Bool × shcrStTy.denote) =>
      (shcrKeyIndProg S Q K).finish.eval (.cons y.2 (.cons y.1 (.cons (ss, ct) .nil)))) := by
  simp only [TwoStageCostedReduction.eval2]
  refine bind_congr fun x => ?_
  rw [runFuel_pqPrimIface_eq_runWithFuelPrim]
  rfl
private theorem kemShCrExp_dsl1KeyActive_mid (P : Primitives) (S : Setup) (b : QueryBudget) (K : ℕ)
    (A : BoundedAdv (KeyIndAdversary S) b) (hK : b.q_total + 1 ≤ K) :
    kemShCrExp P
      (twoStageDslAdv S b (shcrKeyInd1KeyActiveProgK S b.q_on b.q_total K) A) =
      kemShCrExp P (midAdv1KeyActive S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    have h := A.2.2.2.2.1
    convert h using 1; funext q; cases q <;> rfl
  refine kemShCrExp_congr P (midAdv1KeyActive S b A)
    (twoStageDslAdv S b (shcrKeyInd1KeyActiveProgK S b.q_on b.q_total K) A)
    (fun st => Stage1InvC (ShInvAct st.1 st.2.1) (fun d : PauseMid S => d.2.1.pqspkB)
      b.q_total st.2.2.2)
    (fun st => encMidActive st.1 st.2.2) ?_ ?_ ?_
  · intro pk sk
    simp only [twoStageDslAdv, midAdv1KeyActive]
    rw [eval1_1KeyActive_eq S K b A.1 pk sk hA hK, Functor.map_map]
    rfl
  · intro pk sk
    simp only [midAdv1KeyActive]
    exact HoldsOnLeaves.map _ (midRun1KeyActive_inv S b A.1 pk sk hA) fun _ hx => hx
  · rintro ⟨pk, sk, sIdx, c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ ⟨_, hI⟩ ss ct
    · have hI' : ShInvAct pk sk b.q_total h := hI
      show (shcrKeyInd1KeyActiveProgK S b.q_on b.q_total K).eval2
          (.done a (shcrActiveStToVal h sIdx pk)) (ss, ct) b.q_total false =
        findCollisionKeyInd1KeyActivePrim S b (pk, sk, pk, .inl (a, h)) ss ct
      erw [eval2_1KeyActive_done, shcrFinish_eval]
      simp only [findCollisionKeyInd1KeyActivePrim, pure_bind, scaleTB, hI'.sh.tpk, hI'.sh.tsk]
    · obtain ⟨n, r, hIn, hnr, hk⟩ := hI
      show (shcrKeyInd1KeyActiveProgK S b.q_on b.q_total K).eval2
          (.paused q d.2.1.pqspkB (encPause d) (shcrActiveStToVal h sIdx pk) k) (ss, ct) b.q_total
          false =
        findCollisionKeyInd1KeyActivePrim S b (pk, sk, d.2.1.pqspkB, .inr (toPaused h k d)) ss ct
      erw [eval2_1KeyActive_paused,
        shcrResume_eval S _ K d (scaleTB S h) sIdx pk ss ct (hIn.sh.bnd.mono (by omega))]
      rw [postKemKeyIndPrim_scaleTB, Functor.map_map]
      erw [bind_map_left]
      simp only [findCollisionKeyInd1KeyActivePrim, resumePausedKeyInd1KeyActivePrim, toPaused,
        bind_assoc, Prod.map, id]
      refine (postKem_inv_act S pk sk n d h hIn ss ct).bind_congr _ _ fun p hp => ?_
      obtain ⟨resp, h'⟩ := p
      have hr : valToKeyIndResp (keyIndRespToVal resp) = resp := keyIndRdec_keyIndRenc resp
      dsimp only [encSCS]
      rw [hr]
      obtain ⟨hInvR, hEqR⟩ := runWithFuelPrim_map_bounded false (shcrActiveStToVal · sIdx d.2.1.pqspkB)
        (fun n h => ShInvAct pk sk n h) (fun hnm hI => ShInvAct.mono hnm hI)
        (fun q s => (pqxdhKeyIndShCrActivePrimImpl1Key true S q).run s)
        (stepPostD1KeyActive S b.q_on b.q_total K)
        b.q_total
        (fun q st hI => stepPostD1KeyActive_eq S b.q_on b.q_total K b.q_total sIdx pk sk _ q st hI hK)
        (fun n q st hI => pqxdhKeyIndShCrActivePrimImpl1Key_inv_act S pk sk n q st hI)
        (k resp) r (hk resp)
        b.q_total (n + 1) h' hp (by omega)
      dsimp only [shcrActiveStToVal] at hEqR
      rw [hEqR, bind_map_left, runWithFuelShCr1KeyActive_eq]
      refine hInvR.bind_congr _ _ fun y hy => ?_
      obtain ⟨a, hf⟩ := y
      dsimp only [Prod.map, id]
      erw [shcrFinish_eval]
      dsimp only [scaleTB]
      rw [hy.sh.tpk, hy.sh.tsk]

/-- Two-stage `KemShCrAdv` induced by `shcrKeyInd1KeyActiveDslProg S b` on `A`. -/
@[expose] def shcrKeyInd1KeyActiveDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv :=
  twoStageDslAdv S b (shcrKeyInd1KeyActiveDslProg S b) A

theorem kemShCrExp_shcrKeyInd1KeyActiveDslProg_eq (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyInd1KeyActiveDslAdv S b A) =
      KemShCr P (shcrReductionKeyInd1KeyActive S b A) := by
  rw [kemShCrExp_mid1KeyActive_core]
  unfold KemShCr shcrKeyInd1KeyActiveDslAdv
  rw [shcrKeyInd1KeyActiveDslProg_eq,
    kemShCrExp_dsl1KeyActive_mid P S b (keyIndLoopBound b) A
      (by change b.q_total + 1 ≤ 2 * b.q_total + 1; omega)]

theorem KemShCr_shcrKeyInd1KeyActiveAtomicProg_eq (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) =
      KemShCr P (shcrReductionKeyInd1KeyActive S b A) :=
  (kemShCr_liftKeyInd2Stage_eq P S b (shcrKeyInd1KeyActiveDslProg S b)
      (shcrActive_init_unsupported S b) (shcrActive_handlePre_unsupported S b)
      (shcrActive_chDone_unsupported S b) (shcrActive_resume_unsupported S b)
      (shcrActive_handlePost_unsupported S b) (shcrActive_finish_unsupported S b) A).trans
    (kemShCrExp_shcrKeyInd1KeyActiveDslProg_eq S P b A)

/-- Real-valued `KemShCrReal` advantage equality between
    `(pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A` and
    `shcrReductionKeyInd1KeyActive S b A`. -/
theorem kemShCrReal_shcrKeyInd1KeyActiveAtomicProg_eq (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrReal P ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) =
      KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) :=
  congrArg ENNReal.toReal (KemShCr_shcrKeyInd1KeyActiveAtomicProg_eq S P b A)

theorem KemShCrReal_shcrKeyInd1KeyActiveAtomicProg_eq (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrReal P ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) =
      KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) :=
  kemShCrReal_shcrKeyInd1KeyActiveAtomicProg_eq S P b A

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrEval
