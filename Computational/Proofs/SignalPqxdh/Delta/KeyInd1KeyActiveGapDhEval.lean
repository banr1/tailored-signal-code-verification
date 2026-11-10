/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveInitEval -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStepInit

/-!
# Evaluation Equivalence for Active One-Key `GapDhWithSign` Reduction

Proves `ReductionDsl` evaluation equivalence and `AtomicLift` `GapDhWithSign` advantage equality
between `(pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh b A` and the shallow creation-order
simulator `fgKeyInd1KeyGapDhActiveAdv4 S b A`.
-/

set_option autoImplicit false

open OracleSpec OracleComp Function
open ReductionDsl (Ty Var Env Expr Comp CostedReduction handlerImpl isGameQuery)
open SignalPqxdh (Setup Bytes QueryBudget KeyIndQuery KeyIndResponse KeyIndState KeyIndAdversary
  PrincipalEntry SpkBundleEntry OpkEntry PreKeyBundleInput HandshakeHdr KeyIndInitiatorEntry
  SessionId BoundedAdv Primitives GapDhWithSignAdv GapDhWithSign GapDhWithSignReal
  sampleScalar32 sampleCoins32 sampleRandom64
  encodeEC encodeKEM activeIdCount activeSpkCount activeOpkCount activeSendCount
  activeSendOpkCount gdhQueryBudget primQueryBudget gdhPrimQueryBudget keyIndSpec)
open SignalPqxdh.LegacyCosted (pqSig B pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface
  sigAndDdhOracle keyIndCodec keyIndQenc keyIndRdec_keyIndRenc bundleV bundleOfV sidV)
open SignalPqxdh.Security (primQ)
open SignalPqxdh.Security.RoKem (sampleIndexRange)
open SignalPqxdh.Security.FgGapDh (GdhSimSpec FgKeyIndSimState unifGdh
  primGdhQ extractCdhFromSimState fgKeyIndStep fgRunAcceptOPKGdh)
open SignalPqxdh.Security.FgGapDh.Ik (extractCdh2FromAdvRoLog)
open SignalPqxdh.Security.FgGapDh.Opk (fgRunAcceptOPKGdhOpk extractCdh4FromAdvRoLog)
open SignalPqxdh.Security.FgGapDh1Key (GdhSignSimSpec FgKeyInd1KeySimState liftGdhToSign
  unifGdhSign primGdhSignQ sigChalQ liftSimStep1Key runWithGdhSignStep)
open SignalPqxdh.Security.ReductionDsl.KeyInd (PT Ext v letV letV_eval bindV caseOptV caseSumV
  isSomeE optFst optSnd eLet eLet2 eCaseOpt eAny eFind natEq natEq_eval nat2Eq nat2_beq
  nat3Eq nat3_beq litB sBool sBool_eval sBytes32 sRandom64 sDrKey96 sIndex sIndex_eval
  qX25519 qX25519Base qPow8 qIsCanonical qSigPkGen qKemKeyGen qKemEncaps qKemDecaps
  qHkdfDerive96 qSigDdhSign ddhQ liftBase
  qSigSign qSigVerify encEC encKEM rNone rInitPrin rPk rBundle rHdr rInitUnfresh
  buMk sbMk oeMk peMk hdMk seMk seUpd stUpd stPrin stSpks stOpks stSess
  peIkAPk peSecIKA0 peSecIKAsign buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig
  seSid sidEq sidEqV initSidE u32OfNat keyIndQueryTy keyIndRespTy keyIndStateTy preKeyBundleTy initQTy
  paramsTy simTy paMk paU paV paUp paPrinFlag paPrinIdx paDhFlag paEphIdx paSpkIdx
  paOpkMode paOpkIdx paMode smBase smFgL smPows smUpd emptySimE simStateToVal
  gPrim gdhHandle gdhFinish
  keyIndQueryToVal keyIndRespToVal
  keyIndStateToVal principalEntryToVal spkBundleEntryToVal opkEntryToVal keyIndSessionEntryToVal
  preKeyBundleToVal valToPreKeyBundle handshakeHdrToVal sessionIdToVal
  decPrin_enc decSpks_enc decOpks_enc decOpks_enc' checkProvK_eq
  honestPeerC honestPeerC_eval findHonestC findHonestC_eval isAdvRegC isGameSpkC isGameOpkC
  resolveSigPkC resolveSigPkC_eval checkProvC checkProvC_eval partnerC recordRespC acceptKeysC
  koskBundleOkPowsC koskSenderOkPowsC lookupSpkSkC computePosC computeOptPosInitC
  mkSecretPosC mkPairPosC fgPatchC entryMatchesC ddhEqC ddhEqOptC
  chooseInitRandC chooseRespRandC
  extractMode0C logFindC spkPowsC findMapStepC initDh1CandC respDh1CandC
  Env.get_zero' Env.get_succ' Ext.step_wk' Ext.refl_wk')
open scoped SignalPqxdh.Security.ReductionDsl.KeyInd
open scoped SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (emptySimE_eval encSimRS encGdhRS
  letV_queries bindV_queries caseOptV_queries caseSumV_queries
  findMV_queries anyMV_queries mapMV_queries foldMV_queries
  FgSimListsBounded Inv Grow Grow.refl AllOut AllOut.pure_of AllOut.bind_of
  gPrim_eval koskBundleOkPowsC_eval'
  lookupSpkSkC_eval computePosC_eval computeOptPosInitC_eval fgPatchC_eval
  chooseInitRandC_eval decSpks_enc' sidEqV_sendOPK sidEqV_sendNoOPK
  gdhHandle_eval_step
  gdhFinish_eval_mode0 gdhFinish_eval_mode1 gdhFinish_eval_mode2 gdhFinish_eval_mode3
  fgKeyIndStep_grow fgRunAcceptOPKGdh_grow fgRunAcceptOPKGdhOpk_grow
  FgGapDh_embedPrim_eq FgGapDh_embedUnif_eq)
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh renaming bind_congr → gdh_bind_congr
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (Ren gdh1KeyStateTy sim1KeyStateToVal
  encGdh1KeyRS callGdhHandle callGdhHandle_eval liftGdhComp liftGdhComp_eval
  liftGdhComp_gPrim_sBytes32_eval liftGdhComp_gPrim_sRandom64_eval
  liftGdhComp_gPrim_qX25519Base_eval liftGdhComp_gPrim_qKemKeyGen_eval
  liftGdhToSign_bind liftGdhToSign_pure mem_support_liftGdhToSign
  sigChalQ_dsl sigChalQ_dsl_eval twoVarRen pullEnv_twoVarRen renameComp renameComp_eval
  simulateQ_handlerImpl_bind_eq_runWithGdhSignStep_bind)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (optNatMatchesE fgActiveTotalIndexCount gdh1KeyActiveStateTy callGdhActiveHandle initPrin1KeyActiveGdhB genSpkGdhActiveB genSpk1KeyActiveGdhB genOpkActiveGdhB initiateGdhActiveInnerB initiateActiveGdhB gdh1KeyActiveHandle gdh1KeyActiveFinish initParams1KeyActiveFlat fgKeyInd1KeyGapDhActiveDslProg fgKeyInd1KeyGapDhActiveAtomicProg pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.AtomicLift (liftKeyInd1Stage_eval tlGapDhKeyInd tlSigDdhKeyInd keyIndUnsupportedPrimW embedVal)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (optNatMatches
  FgActiveParams activeParamsDh1 activeParamsDh3 activeParamsDh2 activeParamsDh4
  activeParamsZero activeParamsFlat activeParamsFlat_mode_lt4
  FgKeyInd1KeyActiveSimState liftSimStep1KeyActive
  fgInitPrin1KeyActiveGdh fgGenSpkActiveGdh fgGenSPK1KeyActiveGdh fgGenOPKActiveGdh
  fgRunInitiateActiveGdh fgInitiateActiveGdh fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveFinish
  fgKeyInd1KeyActiveRunWithParams fgKeyInd1KeyGapDhActiveRunAtFlat fgKeyInd1KeyGapDhActiveAdv4)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveInitEval
  (gdhActive_init_unsupported_1278 paramsToVal sim1KeyActiveStateToVal encGdh1KeyActiveRS
   runFrom1KeyActive gapDhWithSign_fgKeyInd1KeyGapDhActiveAtomicProg_1278_eq
   gapDhWithSignReal_fgKeyInd1KeyGapDhActiveAtomicProg_1278_eq)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhEval

public section
section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle
end

/-! ## Atomic evaluation bridge -/

section Unsupported

private def zPrimW : SignalPqxdh.LegacyCosted.pqPrimIface.Tag → ℕ := keyIndUnsupportedPrimW
private def zPrimWS : SignalPqxdh.LegacyCosted.pqPrimIface.smp.Samp → ℕ := fun _ => 0
private def zGapDhW : pqGapDhIface.Tag → ℕ := tlGapDhKeyInd.unsupportedW
private def zGapDhWS : pqGapDhIface.smp.Samp → ℕ := fun _ => 0
private def zSigDdhW : pqSigAndDdhIface.Tag → ℕ := tlSigDdhKeyInd.unsupportedW
private def zSigDdhWS : pqSigAndDdhIface.smp.Samp → ℕ := fun _ => 0
attribute [local simp] letV_queries bindV_queries caseOptV_queries caseSumV_queries findMV_queries anyMV_queries mapMV_queries foldMV_queries

@[simp] private theorem sBool_unsup {Γ : List PT} :
    (sBool (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem sBytes32_unsup {Γ : List PT} :
    (sBytes32 (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem sRandom64_unsup {Γ : List PT} :
    (sRandom64 (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem sDrKey96_unsup {Γ : List PT} :
    (sDrKey96 (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} :
    (sIndex N (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qX25519_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qX25519Base_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qPow8_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qPow8 e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qIsCanonical_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qIsCanonical e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qSigPkGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qSigSign_unsup (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qSigVerify_unsup (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qKemKeyGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qKemEncaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qKemDecaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem qHkdfDerive96_unsup (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) :
    (qHkdfDerive96 w e).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem gPrim_unsup {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (gPrim c).queries zGapDhW zGapDhWS = c.queries zPrimW zPrimWS := by
  unfold gPrim; induction c with | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]
@[simp] private theorem ddhQ_unsup {Γ : List PT} (x y z : Expr pqxdhOps Γ (B 32)) :
    (ddhQ x y z).queries zGapDhW zGapDhWS = 0 := rfl
@[simp] private theorem qSigDdhSign_unsupported (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).queries zSigDdhW zSigDdhWS = 0 := rfl
@[simp] private theorem sigChalQ_dsl_unsupported (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).queries zSigDdhW zSigDdhWS = 0 := rfl
@[simp] private theorem liftGdhComp_unsupported {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    (liftGdhComp c).queries zSigDdhW zSigDdhWS = c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[simp] private theorem renameComp_queries' {ι : Type} {T : OracleSpec ι}
    {I : ReductionDsl.Iface pqSig T} {Γ Δ : List PT} {τ : PT}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (ρ : Ren Γ Δ) (c : Comp pqxdhOps I Γ τ) :
    (renameComp ρ c).queries w ws = c.queries w ws := by
  induction c generalizing Δ <;> simp_all [renameComp, Comp.queries]

private theorem gdhActive_init_unsupported (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      0 :=
  gdhActive_init_unsupported_1278 S b

@[simp] private theorem gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).queries zGapDhW zGapDhWS = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2,
    SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2,
    SignalPqxdh.Security.ReductionDsl.KeyInd.wrapBase2,
    SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.corruptB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.genSpkGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.genOpkGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdh2B,
    SignalPqxdh.Security.ReductionDsl.KeyInd.acceptNoOpkGdhB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.finishAcceptGdhC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.testB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.roParsedC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.roRawFallbackC,
    SignalPqxdh.Security.ReductionDsl.KeyInd.revealB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.registerGdhB,
    SignalPqxdh.Security.ReductionDsl.KeyInd.revealSpkB,
    koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC, computePosC, computeOptPosInitC,
    mkSecretPosC, mkPairPosC, fgPatchC, entryMatchesC, ddhEqC, ddhEqOptC,
    chooseInitRandC, chooseRespRandC, honestPeerC, findHonestC, isGameSpkC,
    isGameOpkC, resolveSigPkC, checkProvC, partnerC, Comp.queries]

private theorem gdhActive_handle_unsupported (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      0 := by
  change (gdh1KeyActiveHandle S b.q_total).queries zSigDdhW zSigDdhWS = 0
  simp [-sup_of_le_left, -sup_of_le_right, gdh1KeyActiveHandle, initPrin1KeyActiveGdhB,
    callGdhActiveHandle, genSpk1KeyActiveGdhB, genSpkGdhActiveB, genOpkActiveGdhB,
    initiateActiveGdhB, initiateGdhActiveInnerB, koskBundleOkPowsC, lookupSpkSkC,
    computePosC, computeOptPosInitC, mkSecretPosC, mkPairPosC, fgPatchC, entryMatchesC,
    ddhEqC, ddhEqOptC, chooseInitRandC, honestPeerC, findHonestC, isGameSpkC,
    isGameOpkC, resolveSigPkC, checkProvC, partnerC, Comp.queries]

private theorem gdhActive_finish_unsupported (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      0 := by
  change (gdh1KeyActiveFinish S b.q_total).queries zSigDdhW zSigDdhWS = 0
  simp [-sup_of_le_left, -sup_of_le_right, gdh1KeyActiveFinish, gdhFinish, extractMode0C,
    logFindC, spkPowsC, findMapStepC, initDh1CandC, respDh1CandC, Comp.queries]

end Unsupported

theorem fgKeyInd1KeyGapDhActiveAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyInd1KeyGapDhActiveAtomicProg S b).eval adv (U, V) =
      (fgKeyInd1KeyGapDhActiveDslProg S b).eval adv (U, V) := by
  have h := liftKeyInd1Stage_eval tlSigDdhKeyInd S (fgKeyInd1KeyGapDhActiveDslProg S b)
    (gdhActive_init_unsupported S b)
    (gdhActive_handle_unsupported S b)
    (gdhActive_finish_unsupported S b) adv (U, V)
  have hId : embedVal (B 32) = id := rfl
  rw [hId, id_map] at h
  exact h

/-! ## State encoding and parameter evaluation -/

@[simp] theorem optNatMatchesE_eval {Γ : List PT}
    (tpOpt : Expr pqxdhOps Γ (.opt .nat)) (u : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (optNatMatchesE tpOpt u).eval env = optNatMatches (tpOpt.eval env) (u.eval env) := by
  unfold optNatMatchesE optNatMatches eLet2 eLet eCaseOpt
  rcases h : tpOpt.eval env with _ | t
  · simp [Expr.eval, v, h]
  · simp [Expr.eval, v, h, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', natEq_eval]

@[simp] theorem initParams1KeyActiveFlat_eval (S : Setup) (b : QueryBudget) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (initParams1KeyActiveFlat S b U V idx).eval env =
      paramsToVal (activeParamsFlat S b (U.eval env) (V.eval env) (idx.eval env)) := by
  unfold initParams1KeyActiveFlat activeParamsFlat
  dsimp only
  by_cases h0 : fgActiveTotalIndexCount S b.q_on = 0
  · simp [h0, activeParamsZero, paMk, paramsToVal, Expr.eval]
  · simp only [h0, ↓reduceIte]
    by_cases h1 : idx.eval env < activeIdCount S b.q_on * activeSpkCount S b.q_on
    · simp [h1, activeParamsDh1, paMk, paramsToVal, Expr.eval]
    · by_cases h2 : idx.eval env <
          activeIdCount S b.q_on * activeSpkCount S b.q_on +
            activeSendCount S b.q_on * activeSpkCount S b.q_on
      · simp [h1, h2, activeParamsDh3, paMk, paramsToVal, Expr.eval]
      · by_cases h3 : idx.eval env <
            activeIdCount S b.q_on * activeSpkCount S b.q_on +
              activeSendCount S b.q_on * activeSpkCount S b.q_on +
              activeSendCount S b.q_on * activeIdCount S b.q_on
        · simp [h1, h2, h3, activeParamsDh2, paMk, paramsToVal, Expr.eval]
        · simp [h1, h2, h3, activeParamsDh4, paMk, paramsToVal, Expr.eval]

private def activeDummyParams2 (pa : FgActiveParams) :
    SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty.denote :=
  (pa.U, (pa.V, (pa.Up, (none, (false, (none, (none, (pa.opkMode, (none, 1)))))))))

theorem callGdhActiveHandle_eval {S : Setup} (K : Nat) {Δ : List PT}
    (stAV : Var Δ gdh1KeyActiveStateTy) (qV : Var Δ keyIndQueryTy) (env : Env Δ)
    (pa : FgActiveParams) (stA : FgKeyInd1KeyActiveSimState S)
    (q : KeyIndQuery S)
    (f : FgKeyIndSimState S → OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (hst : env.get stAV = sim1KeyActiveStateToVal pa stA)
    (hq : env.get qV = keyIndQueryToVal q)
    (hGdh : (gdhHandle S K).eval
        (.cons (SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S
          (pa.U, (pa.V, (pa.Up, (none, (false, (none, (none, (pa.opkMode, (none, 1))))))))),
          simStateToVal stA.st1.sim) (.cons (keyIndQueryToVal q) .nil)) =
      encGdhRS (SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S
        (pa.U, (pa.V, (pa.Up, (none, (false, (none, (none, (pa.opkMode, (none, 1)))))))))) <$>
        f stA.st1.sim) :
    (callGdhActiveHandle S K stAV qV).eval env =
      encGdh1KeyActiveRS pa <$> liftSimStep1KeyActive f stA := by
  let pa2 : SignalPqxdh.Security.ReductionDsl.KeyInd.params2Ty.denote := activeDummyParams2 pa
  have hInB : SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.InBoundsParams2 S pa2 :=
    Or.inr ⟨by simp [pa2, activeDummyParams2], by simp [pa2, activeDummyParams2],
      by simp [pa2, activeDummyParams2], by simp [pa2, activeDummyParams2]⟩
  have hEq2 := (SignalPqxdh.Security.ReductionDsl.KeyIndGapDh.gdhHandle2_eval_map_eq
    S K pa2 hInB (simStateToVal stA.st1.sim) q).1
  unfold callGdhActiveHandle liftSimStep1KeyActive
  simp only [letV_eval, bindV, Comp.eval, renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval,
    v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', hst, hq,
    sim1KeyActiveStateToVal, sim1KeyStateToVal,
    SignalPqxdh.Security.ReductionDsl.KeyInd.pa2Mk,
    paU, paV, paUp, paOpkMode, paramsToVal]
  change (do
      let res ← liftGdhToSign ((SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).eval
        (.cons (pa2, simStateToVal stA.st1.sim) (.cons ((keyIndCodec S).qenc q) .nil)))
      pure (res.1, (((paramsToVal pa, res.2.2), stA.st1.sigBudget),
        (stA.resolvedPrin?, stA.sendOpkCnt)))) = _
  have hMap :
      (do
        let res ← liftGdhToSign ((SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).eval
          (.cons (pa2, simStateToVal stA.st1.sim) (.cons ((keyIndCodec S).qenc q) .nil)))
        pure (res.1, (((paramsToVal pa, res.2.2), stA.st1.sigBudget),
          (stA.resolvedPrin?, stA.sendOpkCnt)))) =
      liftGdhToSign
        ((fun r : keyIndRespTy.denote × (paramsTy.denote × simTy.denote) =>
            (r.1, (((paramsToVal pa, r.2.2), stA.st1.sigBudget),
              (stA.resolvedPrin?, stA.sendOpkCnt)))) <$>
          ((fun r : keyIndRespTy.denote ×
                SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty.denote =>
              (r.1, (SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S r.2.1, r.2.2))) <$>
            (SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).eval
              (.cons (pa2, simStateToVal stA.st1.sim) (.cons ((keyIndCodec S).qenc q) .nil)))) := by
    simp only [map_eq_bind_pure_comp, liftGdhToSign_bind, liftGdhToSign_pure,
      bind_assoc, pure_bind, Function.comp_def]
  rw [hMap, hEq2]
  change liftGdhToSign
      ((fun r : keyIndRespTy.denote × (paramsTy.denote × simTy.denote) =>
          (r.1, (((paramsToVal pa, r.2.2), stA.st1.sigBudget),
            (stA.resolvedPrin?, stA.sendOpkCnt)))) <$>
        (gdhHandle S K).eval
          (.cons (SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S pa2,
            simStateToVal stA.st1.sim) (.cons (keyIndQueryToVal q) .nil))) = _
  dsimp only [pa2, activeDummyParams2]
  rw [hGdh]
  simp only [map_eq_bind_pure_comp, liftGdhToSign_bind, liftGdhToSign_pure,
    bind_assoc, pure_bind, Function.comp_def, encGdhRS, encGdh1KeyActiveRS,
    sim1KeyActiveStateToVal, sim1KeyStateToVal]

theorem gdh1KeyActiveFinish_eval_eq (S : Setup) (K : Nat) (a : Bool) (pa : FgActiveParams)
    (stA : FgKeyInd1KeyActiveSimState S) :
    (gdh1KeyActiveFinish S K).eval
      (.cons (sim1KeyActiveStateToVal pa stA) (.cons a .nil)) =
      liftGdhToSign
        ((gdhFinish S K).eval (.cons (paramsToVal pa, simStateToVal stA.st1.sim) (.cons a .nil))) := by
  simp [gdh1KeyActiveFinish, sim1KeyActiveStateToVal, sim1KeyStateToVal, letV_eval,
    renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval, v, Expr.eval,
    Env.get_zero', Env.get_succ', Ext.refl_wk']

theorem gdh1KeyActiveFinish_eval (S : Setup) (K : Nat) (a : Bool) (pa : FgActiveParams)
    (stA : FgKeyInd1KeyActiveSimState S)
    (hMode : pa.mode = 0 ∨ pa.mode = 1 ∨ pa.mode = 2 ∨ pa.mode = 3)
    (hB : FgSimListsBounded stA.st1.sim K) :
    (gdh1KeyActiveFinish S K).eval (.cons (sim1KeyActiveStateToVal pa stA) (.cons a .nil)) =
      fgKeyInd1KeyActiveFinish pa S K stA := by
  rw [gdh1KeyActiveFinish_eval_eq]; unfold fgKeyInd1KeyActiveFinish
  rcases hMode with h0 | h1 | h2 | h3
  · rw [gdhFinish_eval_mode0 S K a (paramsToVal pa) stA.st1.sim h0 hB.advKeyPows_le hB.base_le]
    simp [h0, paramsToVal]
  · rw [gdhFinish_eval_mode1 S K a (paramsToVal pa) stA.st1.sim h1]; simp [h1, paramsToVal]
  · rw [gdhFinish_eval_mode2 S K a (paramsToVal pa) stA.st1.sim h2]; simp [h2, paramsToVal]
  · rw [gdhFinish_eval_mode3 S K a (paramsToVal pa) stA.st1.sim h3]; simp [h3, paramsToVal]

/-! ## Handler evaluation equivalence -/

private theorem initPrin1KeyActiveGdhB_eval {S : Setup} (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stAV : Var Γ₁ gdh1KeyActiveStateTy) (uV : Var Γ₂ .nat) (env : Env Δ)
    (pa : FgActiveParams) (stA : FgKeyInd1KeyActiveSimState S) (u : Fin S.N_id)
    (hst : env.get (Ext.wk stAV) = sim1KeyActiveStateToVal pa stA)
    (hu : env.get (Ext.wk uV) = u.val)
    (hB : FgSimListsBounded stA.st1.sim K) :
    (initPrin1KeyActiveGdhB K stAV uV).eval env =
      encGdh1KeyActiveRS pa <$>
        fgInitPrin1KeyActiveGdh pa.prinFlag pa.prinIdx pa.Up u stA := by
  unfold initPrin1KeyActiveGdhB fgInitPrin1KeyActiveGdh
  simp only [letV_eval, bindV, Comp.eval, liftGdhComp_gPrim_sBytes32_eval,
    liftGdhComp_gPrim_qX25519Base_eval]
  gdh_simp [hst, hu, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
    List.take_of_length_le, List.length_map, hB.base_le.principals_le]
  by_cases h : (stA.st1.sim.base.principals.any fun x => x.1 == ↑u) = true
  · simp [h, encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
      keyIndRespToVal, simStateToVal]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr fun sk0 => ?_
    refine bind_congr fun pk0 => ?_
    simp [encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
      keyIndRespToVal, simStateToVal, keyIndStateToVal, principalEntryToVal]

set_option maxHeartbeats 600000 in
private theorem genSpkGdhActiveB_eval {S : Setup} (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (paV : Var Γ₁ paramsTy) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
    (xV : Var Γ₄ (.prod .nat .nat)) (env : Env Δ)
    (pa : FgActiveParams) (st : FgKeyIndSimState S) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hpa : env.get (Ext.wk paV) = paramsToVal pa)
    (hsm : env.get (Ext.wk smV) = simStateToVal st)
    (hbSt : env.get (Ext.wk bStV) = keyIndStateToVal st.base)
    (hx : env.get (Ext.wk xV) = (u.val, j.val))
    (hB : FgSimListsBounded st K) :
    (genSpkGdhActiveB K paV smV bStV xV).eval env =
      encSimRS <$> fgGenSpkActiveGdh pa.spkIdx pa.V u j st := by
  unfold genSpkGdhActiveB fgGenSpkActiveGdh
  gdh_simp [hpa, hsm, hbSt, hx, paramsToVal, List.take_of_length_le, List.length_map,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, nat2_beq,
    unifGdh, sampleScalar32, primGdhQ]
  by_cases h : (st.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
  · simp [h, encSimRS, keyIndRespToVal, simStateToVal]
  · rcases hf : st.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨idx, uE⟩
    · simp [h, hf, encSimRS, keyIndRespToVal, simStateToVal]
    · simp only [h, hf, Bool.false_eq_true, ↓reduceIte, Option.map_some,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun spkSkRaw => bind_congr fun spkPkRaw => bind_congr fun rSpk =>
        bind_congr fun spkSig => bind_congr fun seed => bind_congr fun kp =>
        bind_congr fun rPq => bind_congr fun pqSig => ?_
      simp [encSimRS, keyIndRespToVal, simStateToVal, keyIndStateToVal, spkBundleEntryToVal]

set_option maxHeartbeats 800000 in
private theorem genSpk1KeyActiveGdhB_eval {S : Setup} (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stAV : Var Γ₁ gdh1KeyActiveStateTy) (xV : Var Γ₂ (.prod .nat .nat)) (env : Env Δ)
    (pa : FgActiveParams) (stA : FgKeyInd1KeyActiveSimState S)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (hst : env.get (Ext.wk stAV) = sim1KeyActiveStateToVal pa stA)
    (hx : env.get (Ext.wk xV) = (u.val, j.val))
    (hB : FgSimListsBounded stA.st1.sim K) :
    (genSpk1KeyActiveGdhB K stAV xV).eval env =
      encGdh1KeyActiveRS pa <$> fgGenSPK1KeyActiveGdh pa.spkIdx pa.V u j stA := by
  unfold genSpk1KeyActiveGdhB fgGenSPK1KeyActiveGdh
  let smZ : Var (simTy :: paramsTy :: gdh1KeyStateTy :: Δ) simTy := .zero
  let env5 : Env (.nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) :=
    .cons (env.get (Ext.wk stAV)).1.2
      (.cons ((smBase (v smZ)).eval (.cons (env.get (Ext.wk stAV)).1.1.2
          (.cons (env.get (Ext.wk stAV)).1.1.1 (.cons (env.get (Ext.wk stAV)).1 env))))
        (.cons (env.get (Ext.wk stAV)).1.1.2
          (.cons (env.get (Ext.wk stAV)).1.1.1
            (.cons (env.get (Ext.wk stAV)).1 env))))
  have hCond : (optNatMatchesE (.fst (.snd (v stAV))) (.fst (v xV))).eval env5 =
      optNatMatches stA.resolvedPrin? u.val := by
    simp [env5, optNatMatchesE_eval, v, Expr.eval, Env.get_succ', Ext.step_wk', Ext.refl_wk',
      hst, hx, sim1KeyActiveStateToVal]
  simp only [letV_eval, Comp.eval, v, Expr.eval, Env.get_zero', Ext.refl_wk']
  change (if (optNatMatchesE (.fst (.snd (v stAV))) (.fst (v xV))).eval env5 = true then _ else _) = _
  rw [hCond]
  by_cases hT : optNatMatches stA.resolvedPrin? u.val = true
  · simp only [hT, ↓reduceIte, letV_eval, bindV, caseOptV, Comp.eval,
      liftGdhComp_gPrim_sBytes32_eval, liftGdhComp_gPrim_sRandom64_eval,
      liftGdhComp_gPrim_qX25519Base_eval, liftGdhComp_gPrim_qKemKeyGen_eval,
      sigChalQ_dsl_eval]
    gdh_simp [smZ, hst, hx, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
      List.take_of_length_le, List.length_map,
      hB.base_le.principals_le, hB.base_le.spkBundles_le, nat2_beq]
    by_cases hAny : (stA.st1.sim.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
    · simp [hAny, encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
        keyIndRespToVal, simStateToVal]
    · rcases hf : stA.st1.sim.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨idx, uE⟩
      · simp [hAny, hf, encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal,
          paramsToVal, keyIndRespToVal, simStateToVal]
      · simp only [hAny, hf, Bool.false_eq_true, ↓reduceIte, Option.map_some]
        by_cases hZ : (stA.st1.sigBudget == 0) = true
        · simp [hZ, encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
            keyIndRespToVal, simStateToVal]
        · simp only [hZ, Bool.false_eq_true, ↓reduceIte,
            map_eq_bind_pure_comp, bind_assoc, pure_bind]
          refine bind_congr fun spkSkRaw => bind_congr fun spkPkRaw => bind_congr fun spkSig =>
            bind_congr fun seed => bind_congr fun ⟨pqPk, pqSk⟩ => bind_congr fun pqSig => ?_
          simp [encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
            keyIndRespToVal, simStateToVal, keyIndStateToVal, spkBundleEntryToVal,
            principalEntryToVal]
  · simp only [hT, Bool.false_eq_true, ↓reduceIte, bindV, Comp.eval, liftGdhComp_eval]
    have hInner := genSpkGdhActiveB_eval K
      (.zero : Var (paramsTy :: gdh1KeyStateTy :: Δ) paramsTy)
      smZ
      (.zero : Var (keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) keyIndStateTy)
      xV env5 pa stA.st1.sim u j
      (by simp [env5, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
            sim1KeyStateToVal])
      (by simp [env5, smZ, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
            sim1KeyStateToVal])
      (by simp [env5, smZ, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
            sim1KeyStateToVal, smBase, v, Expr.eval, simStateToVal])
      (by simp [env5, Env.get_succ', Ext.step_wk', hx])
      hB
    change (liftGdhToSign ((genSpkGdhActiveB K _ _ _ xV).eval env5) >>= _) = _
    rw [hInner]
    simp only [liftSimStep1KeyActive, encSimRS, encGdh1KeyActiveRS, sim1KeyActiveStateToVal,
      sim1KeyStateToVal, hst, Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk',
      Ext.refl_wk', map_eq_bind_pure_comp, liftGdhToSign_bind, liftGdhToSign_pure,
      bind_assoc, Function.comp_def, pure_bind]

private theorem genOpkActiveGdhB_eval {S : Setup} (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stAV : Var Γ₁ gdh1KeyActiveStateTy)
    (xV : Var Γ₂ (.prod .nat (.prod .nat .nat))) (env : Env Δ)
    (pa : FgActiveParams) (stA : FgKeyInd1KeyActiveSimState S)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hst : env.get (Ext.wk stAV) = sim1KeyActiveStateToVal pa stA)
    (hx : env.get (Ext.wk xV) = (u.val, (j.val, o.val)))
    (hB : FgSimListsBounded stA.st1.sim K) :
    (genOpkActiveGdhB K stAV xV).eval env =
      encGdh1KeyActiveRS pa <$> fgGenOPKActiveGdh pa.opkMode pa.opkIdx pa.V u j o stA := by
  unfold genOpkActiveGdhB fgGenOPKActiveGdh
  simp only [letV_eval, bindV, Comp.eval, liftGdhComp_gPrim_sBytes32_eval,
    liftGdhComp_gPrim_qX25519Base_eval]
  gdh_simp [hst, hx, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
    List.take_of_length_le, List.length_map, hB.base_le.opkEntries_le, nat3_beq]
  by_cases h :
      (stA.st1.sim.base.opkEntries.any fun x => x.1.1 == ↑u && (x.1.2.1 == ↑j && x.1.2.2 == ↑o)) =
        true
  · simp [h, encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
      keyIndRespToVal, simStateToVal]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr fun opkSkRaw => ?_
    refine bind_congr fun opkPkRaw => ?_
    simp [encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal, paramsToVal,
      keyIndRespToVal, simStateToVal, keyIndStateToVal, opkEntryToVal]

private def encInitActiveRS {S : Setup} (p : KeyIndResponse × (FgKeyIndSimState S × Nat)) :
    (Ty.prod keyIndRespTy (.prod simTy .nat)).denote :=
  (keyIndRespToVal p.1, (simStateToVal p.2.1, p.2.2))

set_option maxHeartbeats 1200000 in
private theorem initiateOpkGdhActiveInnerB_eval (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (paV : Var Γ₁ paramsTy) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
    (cntV : Var Γ₅ .nat) (xV : Var Γ₄ initQTy) (env : Env Δ)
    (pa : FgActiveParams) (st : FgKeyIndSimState S) (cnt : Nat)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
    (hpa : env.get (Ext.wk paV) = paramsToVal pa)
    (hsm : env.get (Ext.wk smV) = simStateToVal st)
    (hbSt : env.get (Ext.wk bStV) = keyIndStateToVal st.base)
    (hcnt : env.get (Ext.wk cntV) = cnt)
    (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bundle)))
    (hB : FgSimListsBounded st K) :
    (initiateGdhActiveInnerB S K paV smV bStV cntV true xV).eval env =
      encInitActiveRS <$>
        fgRunInitiateActiveGdh pa.dhFlag pa.opkMode pa.ephIdx S K pa.U true
          (.sendOPK u i) u bundle st cnt := by
  unfold initiateGdhActiveInnerB fgRunInitiateActiveGdh
  obtain ⟨ikB, sId, spkB, spkSig, opkB?, pqId, pqB, pqSig⟩ := bundle
  simp only [letV_eval, bindV, caseOptV, Comp.eval, gPrim_eval,
    koskBundleOkPowsC_eval',
    resolveSigPkC_eval, honestPeerC_eval, checkProvC_eval, findHonestC_eval]
  gdh_simp [hpa, hsm, hbSt, hcnt, hx, paramsToVal, List.take_of_length_le, List.length_map,
    sidEqV_sendOPK,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, hB.base_le.opkEntries_le,
    hB.base_le.sessions_le, hB.advKeyPows_le,
    decPrin_enc, decSpks_enc, decSpks_enc', decOpks_enc, decOpks_enc', checkProvK_eq,
    preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV, unifGdh, sampleScalar32,
    sampleCoins32, primGdhQ]
  try erw [hx]
  try rw [decPrin_enc]
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  try rw [decOpks_enc]
  try rw [decOpks_enc']
  gdh_simp [sidEqV_sendOPK, checkProvK_eq, List.length_map,
    hB.base_le.spkBundles_le, hB.advKeyPows_le,
    List.take_of_length_le, preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV]
  rcases opkB? with _ | ⟨oId, opkPk⟩
  · simp [encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hAny : (st.base.sessions.any fun x =>
      sidEqV (sidV x.sid) (.inl (u.val, i.val))) =
      (st.base.sessions.any fun x => x.sid == .sendOPK u i) := by
    congr 1; funext x; exact sidEqV_sendOPK x.sid u i
  dsimp only [sidV, sessionIdToVal] at hAny
  rw [hAny]
  by_cases h1 : (st.base.sessions.any fun x => x.sid == SessionId.sendOPK u i) = true
  · simp [h1, encInitActiveRS, keyIndRespToVal, simStateToVal]
  rcases h2 : st.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨u', uE⟩
  · simp [h1, h2, encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Option.map_some,
    map_eq_bind_pure_comp, bind_assoc]
  simp only [List.take_of_length_le hB.base_le.principals_le,
    List.take_of_length_le hB.base_le.opkEntries_le]
  refine gdh_bind_congr fun bOk => ?_
  cases bOk
  · simp [encInitActiveRS, keyIndRespToVal, simStateToVal]
  gdh_simp [Bool.not_true, List.length_map, principalEntryToVal, primQ, primGdhQ, bind_assoc]
  refine gdh_bind_congr fun ekSkRaw => gdh_bind_congr fun coins =>
    gdh_bind_congr fun sigPk => gdh_bind_congr fun v1 => gdh_bind_congr fun v2 => ?_
  by_cases hv : (v1 && v2) = true
  swap
  · simp only [Bool.not_eq_true] at hv
    simp [hv, encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine gdh_bind_congr fun krOpt => ?_
  rcases krOpt with _ | ⟨ss, kemCt⟩
  · simp [encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [bind_assoc]
  refine gdh_bind_congr fun ekPkRaw => ?_
  rw [lookupSpkSkC_eval S K bStV _ _ _ st.advKeyPows
    (by simp [Expr.eval, hsm, simStateToVal]) hB.advKeyPows_le]
  gdh_simp [hbSt, hx, decSpks_enc, decSpks_enc']
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  rw [List.take_of_length_le hB.base_le.spkBundles_le]
  refine gdh_bind_congr fun spkSk => ?_
  gdh_simp [computePosC_eval, computeOptPosInitC_eval, hx,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine gdh_bind_congr fun pos1 => gdh_bind_congr fun pos2 =>
    gdh_bind_congr fun pos3 => gdh_bind_congr fun pos4? => ?_
  rw [fgPatchC_eval K _ _ _ _ _ _ _ pos1 pos2 pos3 pos4? ss st.fgL
    rfl rfl rfl rfl rfl (by simp [Expr.eval, hsm, simStateToVal])]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine gdh_bind_congr fun ⟨drKeyReal, fgL'⟩ => ?_
  refine gdh_bind_congr fun hp => ?_
  rw [checkProvK_eq S K _ _ _ _ hB.base_le.principals_le hB.base_le.spkBundles_le
    hB.base_le.opkEntries_le]
  refine gdh_bind_congr fun ⟨spkHon, opkHon, pqspkHon⟩ => ?_
  let isTE := (!pa.dhFlag) && ((if pa.opkMode then cnt else st.base.sessions.length) == pa.ephIdx)
  let ekSk := if isTE then ([] : Bytes) else ekSkRaw
  let ekPk := if isTE then pa.U else ekPkRaw
  let hdr : HandshakeHdr := {
    ikAPk := uE.ikAPk, ekAPk := ekPk, spkId := sId,
    opkId? := some oId, pqspkId := pqId, kemCt := kemCt
  }
  let sInit : KeyIndInitiatorEntry S := {
    sid := .sendOPK u i, honestPeer := hp, peerIkPk := ikB, peerSpkPk := spkB,
    peerOpkPk? := some opkPk, peerPqspkPk := pqB, spkHonest := spkHon,
    opkHonest := opkHon, pqspkHonest := pqspkHon, ekASk := ekSk,
    fresh := hp.isSome, drKeyReal := drKeyReal, drKeyRand := drKeyReal,
    hdr := hdr, tested := false
  }
  rw [chooseInitRandC_eval S K bStV .zero _ st.base.respSessions sInit
    (by simp [hbSt, keyIndStateToVal])
    (by cases hp <;> simp [sInit, hdr, ekPk, ekSk, isTE, keyIndSessionEntryToVal])
    hB.base_le.respSessions_le]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine gdh_bind_congr fun drKeyRand => ?_
  refine gdh_bind_congr fun fh => ?_
  cases fh <;> cases hp <;>
    (gdh_simp [sInit, hdr, ekPk, ekSk, isTE,
      hsm, hbSt, hcnt, hx, encInitActiveRS, keyIndRespToVal, simStateToVal, keyIndStateToVal,
      keyIndSessionEntryToVal, preKeyBundleToVal, handshakeHdrToVal, sessionIdToVal]; rfl)

set_option maxHeartbeats 1200000 in
private theorem initiateNoOpkGdhActiveInnerB_eval (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (paV : Var Γ₁ paramsTy) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
    (cntV : Var Γ₅ .nat) (xV : Var Γ₄ initQTy) (env : Env Δ)
    (pa : FgActiveParams) (st : FgKeyIndSimState S) (cnt : Nat)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (hpa : env.get (Ext.wk paV) = paramsToVal pa)
    (hsm : env.get (Ext.wk smV) = simStateToVal st)
    (hbSt : env.get (Ext.wk bStV) = keyIndStateToVal st.base)
    (hcnt : env.get (Ext.wk cntV) = cnt)
    (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bundle)))
    (hB : FgSimListsBounded st K) :
    (initiateGdhActiveInnerB S K paV smV bStV cntV false xV).eval env =
      encInitActiveRS <$>
        fgRunInitiateActiveGdh pa.dhFlag pa.opkMode pa.ephIdx S K pa.U false
          (.sendNoOPK u i) u bundle st cnt := by
  unfold initiateGdhActiveInnerB fgRunInitiateActiveGdh
  obtain ⟨ikB, sId, spkB, spkSig, opkB?, pqId, pqB, pqSig⟩ := bundle
  simp only [letV_eval, bindV, caseOptV, Comp.eval, gPrim_eval,
    koskBundleOkPowsC_eval',
    resolveSigPkC_eval, honestPeerC_eval, checkProvC_eval, findHonestC_eval]
  gdh_simp [hpa, hsm, hbSt, hcnt, hx, paramsToVal, List.take_of_length_le, List.length_map,
    sidEqV_sendNoOPK,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, hB.base_le.opkEntries_le,
    hB.base_le.sessions_le, hB.advKeyPows_le,
    decPrin_enc, decSpks_enc, decSpks_enc', decOpks_enc, decOpks_enc', checkProvK_eq,
    preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV, unifGdh, sampleScalar32,
    sampleCoins32, primGdhQ]
  try erw [hx]
  try rw [decPrin_enc]
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  try rw [decOpks_enc]
  try rw [decOpks_enc']
  gdh_simp [sidEqV_sendNoOPK, checkProvK_eq, List.length_map,
    hB.base_le.spkBundles_le, hB.advKeyPows_le,
    List.take_of_length_le, preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV]
  rcases opkB? with _ | ⟨oId, opkPk⟩
  swap
  · simp [encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [Option.isSome_none, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hAny : (st.base.sessions.any fun x =>
      sidEqV (sidV x.sid) (.inr (.inl (u.val, i.val)))) =
      (st.base.sessions.any fun x => x.sid == .sendNoOPK u i) := by
    congr 1; funext x; exact sidEqV_sendNoOPK x.sid u i
  dsimp only [sidV, sessionIdToVal] at hAny
  rw [hAny]
  by_cases h1 : (st.base.sessions.any fun x => x.sid == SessionId.sendNoOPK u i) = true
  · simp [h1, encInitActiveRS, keyIndRespToVal, simStateToVal]
  rcases h2 : st.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨u', uE⟩
  · simp [h1, h2, encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Option.map_some,
    map_eq_bind_pure_comp, bind_assoc]
  simp only [List.take_of_length_le hB.base_le.principals_le,
    List.take_of_length_le hB.base_le.opkEntries_le]
  refine gdh_bind_congr fun bOk => ?_
  cases bOk
  · simp [encInitActiveRS, keyIndRespToVal, simStateToVal]
  gdh_simp [Bool.not_true, List.length_map, principalEntryToVal, primQ, primGdhQ, bind_assoc]
  refine gdh_bind_congr fun ekSkRaw => gdh_bind_congr fun coins =>
    gdh_bind_congr fun sigPk => gdh_bind_congr fun v1 => gdh_bind_congr fun v2 => ?_
  by_cases hv : (v1 && v2) = true
  swap
  · simp only [Bool.not_eq_true] at hv
    simp [hv, encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine gdh_bind_congr fun krOpt => ?_
  rcases krOpt with _ | ⟨ss, kemCt⟩
  · simp [encInitActiveRS, keyIndRespToVal, simStateToVal]
  simp only [bind_assoc]
  refine gdh_bind_congr fun ekPkRaw => ?_
  rw [lookupSpkSkC_eval S K bStV _ _ _ st.advKeyPows
    (by simp [Expr.eval, hsm, simStateToVal]) hB.advKeyPows_le]
  gdh_simp [hbSt, hx, decSpks_enc, decSpks_enc']
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  rw [List.take_of_length_le hB.base_le.spkBundles_le]
  refine gdh_bind_congr fun spkSk => ?_
  gdh_simp [computePosC_eval, computeOptPosInitC_eval, hx,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine gdh_bind_congr fun pos1 => gdh_bind_congr fun pos2 =>
    gdh_bind_congr fun pos3 => gdh_bind_congr fun pos4? => ?_
  rw [fgPatchC_eval K _ _ _ _ _ _ _ pos1 pos2 pos3 pos4? ss st.fgL
    rfl rfl rfl rfl rfl (by simp [Expr.eval, hsm, simStateToVal])]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine gdh_bind_congr fun ⟨drKeyReal, fgL'⟩ => ?_
  refine gdh_bind_congr fun hp => ?_
  rw [checkProvK_eq S K _ _ _ _ hB.base_le.principals_le hB.base_le.spkBundles_le
    hB.base_le.opkEntries_le]
  refine gdh_bind_congr fun ⟨spkHon, opkHon, pqspkHon⟩ => ?_
  let isTE := (!pa.dhFlag) && ((!pa.opkMode) && (st.base.sessions.length == pa.ephIdx))
  let ekSk := if isTE then ([] : Bytes) else ekSkRaw
  let ekPk := if isTE then pa.U else ekPkRaw
  let hdr : HandshakeHdr := {
    ikAPk := uE.ikAPk, ekAPk := ekPk, spkId := sId,
    opkId? := none, pqspkId := pqId, kemCt := kemCt
  }
  let sInit : KeyIndInitiatorEntry S := {
    sid := .sendNoOPK u i, honestPeer := hp, peerIkPk := ikB, peerSpkPk := spkB,
    peerOpkPk? := none, peerPqspkPk := pqB, spkHonest := spkHon,
    opkHonest := opkHon, pqspkHonest := pqspkHon, ekASk := ekSk,
    fresh := hp.isSome, drKeyReal := drKeyReal, drKeyRand := drKeyReal,
    hdr := hdr, tested := false
  }
  rw [chooseInitRandC_eval S K bStV .zero _ st.base.respSessions sInit
    (by simp [hbSt, keyIndStateToVal])
    (by cases hp <;> simp [sInit, hdr, ekPk, ekSk, isTE, keyIndSessionEntryToVal])
    hB.base_le.respSessions_le]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine gdh_bind_congr fun drKeyRand => ?_
  refine gdh_bind_congr fun fh => ?_
  cases fh <;> cases hp <;>
    (gdh_simp [sInit, hdr, ekPk, ekSk, isTE,
      hsm, hbSt, hcnt, hx, encInitActiveRS, keyIndRespToVal, simStateToVal, keyIndStateToVal,
      keyIndSessionEntryToVal, preKeyBundleToVal, handshakeHdrToVal, sessionIdToVal]; rfl)

private theorem initiateOpkActiveGdhB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stAV : Var Γ₁ gdh1KeyActiveStateTy) (xV : Var Γ₂ initQTy) (env : Env Δ)
    (pa : FgActiveParams) (stA : FgKeyInd1KeyActiveSimState S)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
    (hst : env.get (Ext.wk stAV) = sim1KeyActiveStateToVal pa stA)
    (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bundle)))
    (hB : FgSimListsBounded stA.st1.sim K) :
    (initiateActiveGdhB S K true stAV xV).eval env =
      encGdh1KeyActiveRS pa <$>
        fgInitiateActiveGdh pa.dhFlag pa.opkMode pa.ephIdx S K pa.U true
          (.sendOPK u i) u bundle stA := by
  unfold initiateActiveGdhB fgInitiateActiveGdh
  let smZ : Var (simTy :: paramsTy :: gdh1KeyStateTy :: Δ) simTy := .zero
  let env5 : Env (.nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) :=
    .cons (env.get (Ext.wk stAV)).2.2
      (.cons ((smBase (v smZ)).eval (.cons (env.get (Ext.wk stAV)).1.1.2
          (.cons (env.get (Ext.wk stAV)).1.1.1 (.cons (env.get (Ext.wk stAV)).1 env))))
        (.cons (env.get (Ext.wk stAV)).1.1.2
          (.cons (env.get (Ext.wk stAV)).1.1.1
            (.cons (env.get (Ext.wk stAV)).1 env))))
  simp only [letV_eval, bindV, Comp.eval, liftGdhComp_eval, v, Expr.eval, Env.get_zero',
    Ext.refl_wk']
  have hInner := initiateOpkGdhActiveInnerB_eval S K
    (.zero : Var (paramsTy :: gdh1KeyStateTy :: Δ) paramsTy)
    smZ
    (.zero : Var (keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) keyIndStateTy)
    (.zero : Var (.nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) .nat)
    xV env5 pa stA.st1.sim stA.sendOpkCnt u i bundle
    (by simp [env5, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
          sim1KeyStateToVal])
    (by simp [env5, smZ, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
          sim1KeyStateToVal])
    (by simp [env5, smZ, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
          sim1KeyStateToVal, smBase, v, Expr.eval, simStateToVal])
    (by simp [env5, Env.get_zero', Ext.refl_wk', hst, sim1KeyActiveStateToVal])
    (by simp [env5, Env.get_succ', Ext.step_wk', hx])
    hB
  change (liftGdhToSign ((initiateGdhActiveInnerB S K _ _ _ _ true xV).eval env5) >>= _) = _
  rw [hInner]
  simp only [encInitActiveRS, encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal,
    hst, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
    map_eq_bind_pure_comp, liftGdhToSign_bind, liftGdhToSign_pure,
    bind_assoc, Function.comp_def, pure_bind]

private theorem initiateNoOpkActiveGdhB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stAV : Var Γ₁ gdh1KeyActiveStateTy) (xV : Var Γ₂ initQTy) (env : Env Δ)
    (pa : FgActiveParams) (stA : FgKeyInd1KeyActiveSimState S)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (hst : env.get (Ext.wk stAV) = sim1KeyActiveStateToVal pa stA)
    (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bundle)))
    (hB : FgSimListsBounded stA.st1.sim K) :
    (initiateActiveGdhB S K false stAV xV).eval env =
      encGdh1KeyActiveRS pa <$>
        fgInitiateActiveGdh pa.dhFlag pa.opkMode pa.ephIdx S K pa.U false
          (.sendNoOPK u i) u bundle stA := by
  unfold initiateActiveGdhB fgInitiateActiveGdh
  let smZ : Var (simTy :: paramsTy :: gdh1KeyStateTy :: Δ) simTy := .zero
  let env5 : Env (.nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) :=
    .cons (env.get (Ext.wk stAV)).2.2
      (.cons ((smBase (v smZ)).eval (.cons (env.get (Ext.wk stAV)).1.1.2
          (.cons (env.get (Ext.wk stAV)).1.1.1 (.cons (env.get (Ext.wk stAV)).1 env))))
        (.cons (env.get (Ext.wk stAV)).1.1.2
          (.cons (env.get (Ext.wk stAV)).1.1.1
            (.cons (env.get (Ext.wk stAV)).1 env))))
  simp only [letV_eval, bindV, Comp.eval, liftGdhComp_eval, v, Expr.eval, Env.get_zero',
    Ext.refl_wk']
  have hInner := initiateNoOpkGdhActiveInnerB_eval S K
    (.zero : Var (paramsTy :: gdh1KeyStateTy :: Δ) paramsTy)
    smZ
    (.zero : Var (keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) keyIndStateTy)
    (.zero : Var (.nat :: keyIndStateTy :: simTy :: paramsTy :: gdh1KeyStateTy :: Δ) .nat)
    xV env5 pa stA.st1.sim stA.sendOpkCnt u i bundle
    (by simp [env5, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
          sim1KeyStateToVal])
    (by simp [env5, smZ, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
          sim1KeyStateToVal])
    (by simp [env5, smZ, Env.get_succ', Ext.step_wk', Ext.refl_wk', hst, sim1KeyActiveStateToVal,
          sim1KeyStateToVal, smBase, v, Expr.eval, simStateToVal])
    (by simp [env5, Env.get_zero', Ext.refl_wk', hst, sim1KeyActiveStateToVal])
    (by simp [env5, Env.get_succ', Ext.step_wk', hx])
    hB
  change (liftGdhToSign ((initiateGdhActiveInnerB S K _ _ _ _ false xV).eval env5) >>= _) = _
  rw [hInner]
  simp only [encInitActiveRS, encGdh1KeyActiveRS, sim1KeyActiveStateToVal, sim1KeyStateToVal,
    hst, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
    map_eq_bind_pure_comp, liftGdhToSign_bind, liftGdhToSign_pure,
    bind_assoc, Function.comp_def, pure_bind]

private theorem gdhHandle_acceptOPK_active {S : Setup} (K : Nat) (pa : FgActiveParams)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (st : FgKeyIndSimState S) (hB : FgSimListsBounded st K) :
    (gdhHandle S K).eval
      (.cons (SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S (activeDummyParams2 pa),
        simStateToVal st)
        (.cons (keyIndQueryToVal (.acceptOPK k j o hdr)) .nil)) =
      encGdhRS (SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S (activeDummyParams2 pa)) <$>
        (if pa.opkMode then fgRunAcceptOPKGdhOpk S K k j o hdr
         else fgRunAcceptOPKGdh S K k j o hdr) st := by
  let paFlat := SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S (activeDummyParams2 pa)
  have hStep := gdhHandle_eval_step S K paFlat (.acceptOPK k j o hdr) st hB
  have hOpk : paFlat.2.2.2.2.2.2.2.2.1 = pa.opkMode := rfl
  cases h' : pa.opkMode <;>
    simp only [hOpk, h', ↓reduceIte, Bool.false_eq_true] at hStep ⊢ <;>
    exact hStep

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

set_option maxHeartbeats 400000 in
theorem gdh1KeyActiveHandle_eval_step (S : Setup) (K : Nat) (pa : FgActiveParams)
    (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S)
    (hB : FgSimListsBounded stA.st1.sim K) :
    (gdh1KeyActiveHandle S K).eval
      (.cons (sim1KeyActiveStateToVal pa stA) (.cons (keyIndQueryToVal q) .nil)) =
      encGdh1KeyActiveRS pa <$> fgKeyInd1KeyActiveStep pa S K q stA := by
  let paFlat := SignalPqxdh.Security.ReductionDsl.KeyInd.params2ToFlat S (activeDummyParams2 pa)
  cases q <;>
    simp only [gdh1KeyActiveHandle, fgKeyInd1KeyActiveStep, keyIndQueryToVal, keyIndQenc,
      caseSumV, Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
  case initPrin u => exact initPrin1KeyActiveGdhB_eval K _ _ _ pa stA u rfl rfl hB
  case corruptIK u =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.corruptIK u) _ rfl rfl
      (gdhHandle_eval_step S K paFlat (.corruptIK u) stA.st1.sim hB)
  case genSPK u j => exact genSpk1KeyActiveGdhB_eval K _ _ _ pa stA u j rfl rfl hB
  case genOPK u j o => exact genOpkActiveGdhB_eval K _ _ _ pa stA u j o rfl rfl hB
  case initiateOPK u i b => exact initiateOpkActiveGdhB_eval S K _ _ _ pa stA u i b rfl rfl hB
  case initiateNoOPK u i b => exact initiateNoOpkActiveGdhB_eval S K _ _ _ pa stA u i b rfl rfl hB
  case acceptOPK k j o h =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.acceptOPK k j o h) _ rfl rfl
      (gdhHandle_acceptOPK_active K pa k j o h stA.st1.sim hB)
  case acceptNoOPK k j l h =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.acceptNoOPK k j l h) _ rfl rfl
      (gdhHandle_eval_step S K paFlat (.acceptNoOPK k j l h) stA.st1.sim hB)
  case testSession sid =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.testSession sid) _ rfl rfl
      (gdhHandle_eval_step S K paFlat (.testSession sid) stA.st1.sim hB)
  case roQuery sec =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.roQuery sec) _ rfl rfl
      (gdhHandle_eval_step S K paFlat (.roQuery sec) stA.st1.sim hB)
  case revealDhSecrets =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA .revealDhSecrets _ rfl rfl
      (gdhHandle_eval_step S K paFlat .revealDhSecrets stA.st1.sim hB)
  case revealSessionKey sid =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.revealSessionKey sid) _ rfl rfl
      (gdhHandle_eval_step S K paFlat (.revealSessionKey sid) stA.st1.sim hB)
  case registerKey sk =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.registerKey sk) _ rfl rfl
      (gdhHandle_eval_step S K paFlat (.registerKey sk) stA.st1.sim hB)
  case revealSpkSk u j =>
    exact callGdhActiveHandle_eval K _ _ _ pa stA (.revealSpkSk u j) _ rfl rfl
      (gdhHandle_eval_step S K paFlat (.revealSpkSk u j) stA.st1.sim hB)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Env.get Ext.wk
end

/-! ## One-step list-growth bounds -/

private theorem liftSimStep1KeyActive_grow {S : Setup}
    (f : FgKeyIndSimState S → OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (stA : FgKeyInd1KeyActiveSimState S)
    (hf : ∀ y ∈ support (f stA.st1.sim), Grow stA.st1.sim y.2) :
    ∀ x ∈ support (liftSimStep1KeyActive f stA), Grow stA.st1.sim x.2.st1.sim := by
  intro x hx
  unfold liftSimStep1KeyActive at hx
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨y, hy, hx⟩ := hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact hf y (mem_support_liftGdhToSign hy)

private theorem fgInitPrin1KeyActiveGdh_grow {S : Setup} (prinFlag : Bool) (prinIdx : Nat)
    (Up : Bytes) (u : Fin S.N_id) (stA : FgKeyInd1KeyActiveSimState S) :
    ∀ x ∈ support (fgInitPrin1KeyActiveGdh prinFlag prinIdx Up u stA),
      Grow stA.st1.sim x.2.st1.sim := by
  show AllOut (fgInitPrin1KeyActiveGdh prinFlag prinIdx Up u stA)
    (fun x => Grow stA.st1.sim x.2.st1.sim)
  unfold fgInitPrin1KeyActiveGdh
  grow_loop
  all_goals grow_leaf

private theorem fgGenSpkActiveGdh_grow {S : Setup} (spkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgKeyIndSimState S) :
    ∀ x ∈ support (fgGenSpkActiveGdh spkIdx V u j st), Grow st x.2 := by
  show AllOut (fgGenSpkActiveGdh spkIdx V u j st) (fun x => Grow st x.2)
  unfold fgGenSpkActiveGdh
  grow_loop
  all_goals grow_leaf

private theorem fgGenSPK1KeyActiveGdh_grow {S : Setup} (spkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (stA : FgKeyInd1KeyActiveSimState S) :
    ∀ x ∈ support (fgGenSPK1KeyActiveGdh spkIdx V u j stA),
      Grow stA.st1.sim x.2.st1.sim := by
  unfold fgGenSPK1KeyActiveGdh
  by_cases hT : optNatMatches stA.resolvedPrin? u.val = true
  · simp only [hT, ↓reduceIte]
    show AllOut _ (fun x : KeyIndResponse × FgKeyInd1KeyActiveSimState S => Grow stA.st1.sim x.2.st1.sim)
    grow_loop
    all_goals grow_leaf
  · simp only [hT, Bool.false_eq_true, ↓reduceIte]
    exact liftSimStep1KeyActive_grow _ stA (fgGenSpkActiveGdh_grow spkIdx V u j stA.st1.sim)

private theorem fgGenOPKActiveGdh_grow {S : Setup} (opkMode : Bool) (opkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ∀ x ∈ support (fgGenOPKActiveGdh opkMode opkIdx V u j o stA),
      Grow stA.st1.sim x.2.st1.sim := by
  show AllOut (fgGenOPKActiveGdh opkMode opkIdx V u j o stA)
    (fun x => Grow stA.st1.sim x.2.st1.sim)
  unfold fgGenOPKActiveGdh
  grow_loop
  all_goals grow_leaf

private theorem fgRunInitiateActiveGdh_grow {S : Setup} (dhFlag opkMode : Bool) (ephIdx K : Nat)
    (U : Bytes) (hasOpk : Bool) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) (cnt : Nat) :
    ∀ x ∈ support (fgRunInitiateActiveGdh dhFlag opkMode ephIdx S K U hasOpk sid u bundle st cnt),
      Grow st x.2.1 := by
  show AllOut (fgRunInitiateActiveGdh dhFlag opkMode ephIdx S K U hasOpk sid u bundle st cnt)
    (fun x => Grow st x.2.1)
  unfold fgRunInitiateActiveGdh
  grow_loop
  all_goals grow_leaf

private theorem fgInitiateActiveGdh_grow {S : Setup} (dhFlag opkMode : Bool) (ephIdx K : Nat)
    (U : Bytes) (hasOpk : Bool) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (stA : FgKeyInd1KeyActiveSimState S) :
    ∀ x ∈ support (fgInitiateActiveGdh dhFlag opkMode ephIdx S K U hasOpk sid u bundle stA),
      Grow stA.st1.sim x.2.st1.sim := by
  intro x hx; unfold fgInitiateActiveGdh at hx
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hx; obtain ⟨y, hy, hx⟩ := hx
  simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
  exact fgRunInitiateActiveGdh_grow dhFlag opkMode ephIdx K U hasOpk sid u bundle
    stA.st1.sim stA.sendOpkCnt y (mem_support_liftGdhToSign hy)

theorem fgKeyInd1KeyActiveStep_grow {S : Setup} (pa : FgActiveParams) (K : Nat)
    (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S) :
    ∀ x ∈ support (fgKeyInd1KeyActiveStep pa S K q stA),
      Grow stA.st1.sim x.2.st1.sim := by
  cases q with
  | initPrin u => exact fgInitPrin1KeyActiveGdh_grow pa.prinFlag pa.prinIdx pa.Up u stA
  | genSPK u j => exact fgGenSPK1KeyActiveGdh_grow pa.spkIdx pa.V u j stA
  | genOPK u j o => exact fgGenOPKActiveGdh_grow pa.opkMode pa.opkIdx pa.V u j o stA
  | initiateOPK u i bundle =>
    exact fgInitiateActiveGdh_grow pa.dhFlag pa.opkMode pa.ephIdx K pa.U true (.sendOPK u i) u bundle stA
  | initiateNoOPK u i bundle =>
    exact fgInitiateActiveGdh_grow pa.dhFlag pa.opkMode pa.ephIdx K pa.U false (.sendNoOPK u i) u bundle stA
  | acceptOPK k j o hdr =>
    dsimp only [fgKeyInd1KeyActiveStep]; refine liftSimStep1KeyActive_grow _ stA ?_
    cases pa.opkMode
    · exact fgRunAcceptOPKGdh_grow K k j o hdr stA.st1.sim
    · exact fgRunAcceptOPKGdhOpk_grow K k j o hdr stA.st1.sim
  | corruptIK u =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V (.corruptIK u) stA.st1.sim)
  | acceptNoOPK k j l hdr =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V (.acceptNoOPK k j l hdr) stA.st1.sim)
  | testSession sid =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V (.testSession sid) stA.st1.sim)
  | roQuery sec =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V (.roQuery sec) stA.st1.sim)
  | revealDhSecrets =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V .revealDhSecrets stA.st1.sim)
  | revealSessionKey sid =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V (.revealSessionKey sid) stA.st1.sim)
  | registerKey sk =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V (.registerKey sk) stA.st1.sim)
  | revealSpkSk u j =>
    exact liftSimStep1KeyActive_grow _ stA
      (fgKeyIndStep_grow pa.dhFlag pa.ephIdx pa.spkIdx K pa.U pa.V (.revealSpkSk u j) stA.st1.sim)

/-! ## End-to-end advantage equality -/

private theorem runFrom1KeyActive_eq (S : Setup) (b : QueryBudget) (K : Nat) (pa : FgActiveParams)
    (hMode : pa.mode = 0 ∨ pa.mode = 1 ∨ pa.mode = 2 ∨ pa.mode = 3)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K)
    (secb : Bool) :
    runFrom1KeyActive S K A
      (sim1KeyActiveStateToVal pa (FgKeyInd1KeyActiveSimState.empty S b secb)) =
      (do
        let (_, finalSt) ← runWithGdhSignStep (fgKeyInd1KeyActiveStep pa S K) A
          (FgKeyInd1KeyActiveSimState.empty S b secb)
        fgKeyInd1KeyActiveFinish pa S K finalSt) := by
  unfold runFrom1KeyActive
  refine simulateQ_handlerImpl_bind_eq_runWithGdhSignStep_bind
    (C := keyIndCodec S) (σ := gdh1KeyActiveStateTy) (gdh1KeyActiveHandle S K)
    (fgKeyInd1KeyActiveStep pa S K) (sim1KeyActiveStateToVal pa)
    (fun k stA => Inv K k stA.st1.sim) (fun k stA h => Inv.mono K k stA.st1.sim h)
    (fun k q stA h => ?_)
    (fun k q stA h x hx =>
      Inv.of_grow K k stA.st1.sim x.2.st1.sim h (fgKeyInd1KeyActiveStep_grow pa K q stA x hx))
    (fun p => (gdh1KeyActiveFinish S K).eval (.cons p.2 (.cons p.1 .nil)))
    (fun p => fgKeyInd1KeyActiveFinish pa S K p.2)
    (fun a stA h => gdh1KeyActiveFinish_eval S K a pa stA hMode (Inv.bnd K 0 stA.st1.sim h))
    A K hA _ (Inv.empty S K secb)
  dsimp only [keyIndCodec, keyIndQueryToVal]
  rw [gdh1KeyActiveHandle_eval_step S K pa q stA (Inv.bnd K (k + 1) stA.st1.sim h)]
  simp only [encGdh1KeyActiveRS, keyIndRespToVal, keyIndRdec_keyIndRenc,
    map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

private theorem isQueryBoundP_adv_run (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
  obtain ⟨_, _, _, h, _⟩ := A.2
  convert h using 1
  funext q; cases q <;> rfl

theorem gapDhWithSign_fgKeyInd1KeyGapDhActiveAtomicProg_eq (S : Setup) (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSign P isValidDhTriple pow8
      ((pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh b A) =
    GapDhWithSign P isValidDhTriple pow8
      (fgKeyInd1KeyGapDhActiveAdv4 S b A) :=
  gapDhWithSign_fgKeyInd1KeyGapDhActiveAtomicProg_1278_eq S P isValidDhTriple pow8 b A
    (gdhActive_handle_unsupported S b) (gdhActive_finish_unsupported S b)
    (fun pa hMode secb =>
      runFrom1KeyActive_eq S b b.q_total pa hMode A.1.run (isQueryBoundP_adv_run S b A) secb)

/-- Real-valued `GapDhWithSignReal` advantage equality for
    `(pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh`. -/
theorem gapDhWithSignReal_fgKeyInd1KeyGapDhActiveAtomicProg_eq (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSignReal P P.isValidDhTriple P.pow8
      ((pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh b A) =
    GapDhWithSignReal P P.isValidDhTriple P.pow8
      (fgKeyInd1KeyGapDhActiveAdv4 S b A) :=
  gapDhWithSignReal_fgKeyInd1KeyGapDhActiveAtomicProg_1278_eq S P b A
    (gdhActive_handle_unsupported S b) (gdhActive_finish_unsupported S b)
    (fun pa hMode secb =>
      runFrom1KeyActive_eq S b b.q_total pa hMode A.1.run (isQueryBoundP_adv_run S b A) secb)

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhEval
