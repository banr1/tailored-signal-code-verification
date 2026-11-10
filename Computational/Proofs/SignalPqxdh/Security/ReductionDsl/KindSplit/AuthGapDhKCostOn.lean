/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigStepBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigWire

/-!
# Kind-0 Online Arm Cost, Query, and Size Bounds

Proves per-arm syntactic `.cost`, `.queries`, and `.size` upper bounds for the ten
online `AuthQuery` constructors of `a1g2KindProg` and `a1s2KindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostOn

open _root_.SignalPqxdh (Setup QueryBudget F_X25519)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle
  sigAndDdhOracle chalIfaceDdhQueryWeight chalIfaceSigQueryWeight chalIfacePrimQueryWeight)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface)
open _root_.SignalPqxdh.Security (authChalIfaceDdhQueryWeight authChalIfaceSigQueryWeight
  authChalIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy authRespTy drKeyTy fgPosTy fgPatchEntryTy)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (liftBase)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  Ext v letV bindV caseOptV caseSumV findMV mapMV eAny eFind eMap eCaseOpt eCaseSum natEq nat2Eq nat3Eq sidEq
  optU32Eq isSomeE sendGuardE kyberCheckE firstMsgADE encEC encKEM slice32 bytesEmpty zero32 optFst optSnd
  stPrin stSpks stOpks stSess stUsedS stUsedO stUsedN stKyb stAdv stSecb stUpd peMk peSecIKA0 peIkAPk
  peSecIKAsign peCorrupted sbMk sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk oeOpkSk oeOpkPk oeConsumed oeUpd buMk buIkB
  buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig hdMk hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId
  hdKemCt pmHdr pmEphAPk pmPqMsg pmAeadCt seMk aNone aInitPrin aBundle aPk aSendFresh aSendUnfresh aRecvHonest
  aRecvUnfresh findHonestC resolveSigPkC corruptB genOpkB rootEntryTy fgSimTy patchKeyTy sendQTy recvQTy
  a1gParams2Ty a1g2StTy a1sStTy a1sRS fsBase fsL fsRootL fsRaw fsLog fsResp fsPows fsUpd pa2U pa2Role pkP1 pkP2
  pkP3 pkP4 pkSs feDk reRk rePos reRk1 reCk q4 mkSecretPosC twoSideC twoSideOptC ddhEqC ddhEqOptC entryMatchesC
  koskBundleOkPowsC koskSenderOkPowsC lookupSpkSkC onBaseF fgRegisterC fgGenSpk2C a1gInitPrin2C a1gGenSpk2C
  a1sCaseAPa2 a1sG a1sTp a1sTpk a1sFg a1sMk a1sBase bits_0 bits_1 extractC_queries_prim)
open _root_.ReductionDsl (Ty Var Expr Comp bits pqAtomicSig pqAtomicOps PB AtomicPureOp atomicPureOps
  pqAtomicSamplers atomicBaseSamplers unifSamplers AtomicBaseUnif)
open _root_.ReductionDsl.Expr (litBytes)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface embedTy embedCtx embedVar exprRename compRename mapOpExpr mapExpr mapComp mapSamp mapSampH
  mapSampCast castLegacySamp aiAuthSigDdh tlAuthSigDdh r64W sampR64W exprRename_cost compRename_cost
  compRename_queries exprRename_size compRename_size mapExpr_size exprLitSize compLitSize mapSampH_cost_le
  mapSampH_size_le expr_cost_two_mul_le mapComp_cost_two_mul_le mapComp_queries_le mapComp_size_le
  tlAuthSigDdh_primW tlAuthSigDdh_sigW tlAuthSigDdh_ddhW tlAuthSigDdh_sizeLe samplerZeroQueryWeight_eq)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  AuthKindFuels wk1 wk2 liftExpr1 liftExpr2 authQueryAtomicTy authSendQAtomicTy authRecvQAtomicTy
  authRespAtomicTy aNoneAtomicE extractKC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK (
  seqFgEntryTy seqRootEntryTy sessAuxLegTy fgAuthShadowAuxTy a1g2ShadowStTy a1s2ShadowStTy fgCoreOutTy
  auxFgSessE auxFgCtrE auxFgRoAvlE auxFgRootSessE auxFgRootCtrE auxFgRootRoAvlE auxRawAvlE fgAuxMkE
  auxSessSliceE auxPutSessSliceE wk0 liftCs0 liftCs1 liftGdh0 liftGdh1 saFgSess saFgCtr saRootSess saRootCtr
  patchWithShadowC rootPatchWithShadowC fgSend2ShadowC fgRecvShadowC fgRecvShadowB a1gInitPrin2LegC
  fgCorruptLegC a1gGenSpk2LegC fgGenOpkLegC fgRegisterLegC a1sSendCheckLegC a1gHaltGuard2E fgCoreArm_initPrin
  fgCoreArm_corrupt fgCoreArm_genSPK fgCoreArm_genOPK fgCoreArm_send fgCoreArm_recv fgCoreArm_revealDh
  fgCoreArm_registerKey a1gWrapCoreArm a1gArm_initPrin a1gArm_corrupt a1gArm_genSPK a1gArm_genOPK a1gArm_send
  a1gArm_recv a1gArm_revealDh a1gArm_registerKey a1sIsFrozenE a1sCaseAPa2AtomicE a1sSimAtomicE a1sSigBAtomicE
  a1sPutSimSigBE a1sDelegateCoreArm a1sWrapNonSendArm a1sArm_initPrin a1sArm_corrupt a1sArm_genSPK a1sArm_genOPK
  a1sArm_send a1sArm_recv a1sArm_revealDh a1sArm_registerKey a1gHaltGuard2E_cost_le a1gHaltGuard2E_size_le
  a1sIsFrozenE_cost_le a1sIsFrozenE_size_le a1sCaseAPa2AtomicE_cost_le a1sCaseAPa2AtomicE_size_le
  a1sPutSimSigBE_cost_le a1sPutSimSigBE_size_le)

private theorem liftCs1_cost {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftCs1 c argE).cost = 2 + argE.cost + (mapComp tlAuthSigDdh c).cost := by
  have h := compRename_cost (ξ := fun {_} => wk1 (Γ := Γ)) (mapComp tlAuthSigDdh c)
  change (argE.cost + 1) + (compRename (fun {_} => wk1) (mapComp tlAuthSigDdh c)).cost + 1 = _; omega
private theorem liftCs1_queries {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    (liftCs1 c argE).queries wq samplerZeroQueryWeight = (mapComp tlAuthSigDdh c).queries wq (fun _ => 0) := by
  have h := compRename_queries (I := pqAuthSigAndDdhIface) wq (fun _ => 0) (ξ := fun {_} => wk1 (Γ := Γ))
    (mapComp tlAuthSigDdh c)
  simp only [liftCs1, Comp.queries, samplerZeroQueryWeight_eq, h, Nat.zero_add]
private theorem liftCs1_size {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftCs1 c argE).size = 2 + argE.size + (mapComp tlAuthSigDdh c).size := by
  have h := compRename_size (ξ := fun {_} => wk1 (Γ := Γ)) (mapComp tlAuthSigDdh c)
  change (argE.size + 1) + (compRename (fun {_} => wk1) (mapComp tlAuthSigDdh c)).size + 1 = _; omega
private theorem liftGdh1_cost {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftGdh1 c argE).cost = 2 + argE.cost + (mapComp tlAuthSigDdh (liftGdhComp c)).cost := by
  simp only [liftGdh1, liftCs1_cost]
private theorem liftGdh1_queries {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    (liftGdh1 c argE).queries wq samplerZeroQueryWeight =
      (mapComp tlAuthSigDdh (liftGdhComp c)).queries wq (fun _ => 0) :=
  liftCs1_queries (liftGdhComp c) argE wq
private theorem liftGdh1_size {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftGdh1 c argE).size = 2 + argE.size + (mapComp tlAuthSigDdh (liftGdhComp c)).size := by
  simp only [liftGdh1, liftCs1_size]
private theorem a1gWrapCoreArm_cost_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1g2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1gWrapCoreArm F stE core).cost ≤ 3 * stE.cost + 5 * F.K_on + 60 + core.cost := by
  have hHalt := a1gHaltGuard2E_cost_le F.K_on (.fst (.fst (.fst stE))) (.snd (.fst (.fst stE)))
  simp only [Expr.cost] at hHalt
  simp only [a1gWrapCoreArm, aNoneAtomicE, Expr.v0, Expr.v1, Comp.cost, Expr.cost, compRename_cost]; omega
private theorem a1gWrapCoreArm_queries_eq (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1g2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy)
    (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    (a1gWrapCoreArm F stE core).queries wq samplerZeroQueryWeight = core.queries wq samplerZeroQueryWeight := by
  simp [a1gWrapCoreArm, Comp.queries, compRename_queries]
private theorem a1gWrapCoreArm_size_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1g2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1gWrapCoreArm F stE core).size ≤ 4 * stE.size + bits F.K_on + 75 + core.size := by
  have hHalt := a1gHaltGuard2E_size_le F.K_on (.fst (.fst (.fst stE))) (.snd (.fst (.fst stE)))
  simp only [Expr.size] at hHalt
  simp only [a1gWrapCoreArm, aNoneAtomicE, Expr.v0, Expr.v1, Comp.size, Expr.size, compRename_size]; omega
private theorem a1sDelegateCoreArm_cost_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1sDelegateCoreArm F stE core).cost ≤ 3 * stE.cost + 5 * F.K_on + 110 + core.cost := by
  have hPa := a1sCaseAPa2AtomicE_cost_le (.fst stE)
  have hHalt := a1gHaltGuard2E_cost_le F.K_on (a1sCaseAPa2AtomicE (.fst stE)) (a1sSimAtomicE (.fst stE))
  have hPut := a1sPutSimSigBE_cost_le (Γ := fgCoreOutTy :: .prod a1s2ShadowStTy .unit :: Γ)
    (.fst (.fst .v1)) (.fst (.snd .v0))
  simp only [a1sSimAtomicE, Expr.v0, Expr.v1, Expr.cost] at hPa hHalt hPut
  simp only [a1sDelegateCoreArm, a1sSimAtomicE, aNoneAtomicE, Expr.v0, Expr.v1,
    Comp.cost, Expr.cost, compRename_cost]; omega
private theorem a1sDelegateCoreArm_queries_eq (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy)
    (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    (a1sDelegateCoreArm F stE core).queries wq samplerZeroQueryWeight = core.queries wq samplerZeroQueryWeight := by
  simp [a1sDelegateCoreArm, Comp.queries, compRename_queries]
private theorem a1sDelegateCoreArm_size_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1sDelegateCoreArm F stE core).size ≤ 4 * stE.size + bits F.K_on + 120 + core.size := by
  have hPa := a1sCaseAPa2AtomicE_size_le (.fst stE)
  have hHalt := a1gHaltGuard2E_size_le F.K_on (a1sCaseAPa2AtomicE (.fst stE)) (a1sSimAtomicE (.fst stE))
  have hPut := a1sPutSimSigBE_size_le (Γ := fgCoreOutTy :: .prod a1s2ShadowStTy .unit :: Γ)
    (.fst (.fst .v1)) (.fst (.snd .v0))
  simp only [a1sSimAtomicE, Expr.v0, Expr.v1, Expr.size] at hPa hHalt hPut
  simp only [a1sDelegateCoreArm, a1sSimAtomicE, aNoneAtomicE, Expr.v0, Expr.v1,
    Comp.size, Expr.size, compRename_size]; omega
private theorem a1sWrapNonSendArm_cost_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1sWrapNonSendArm F stE core).cost ≤ 4 * stE.cost + 5 * F.K_on + 130 + core.cost := by
  have hFrz := a1sIsFrozenE_cost_le (.fst stE); have hDel := a1sDelegateCoreArm_cost_le F stE core
  simp only [Expr.cost] at hFrz; simp only [a1sWrapNonSendArm, aNoneAtomicE, Comp.cost, Expr.cost]; omega
private theorem a1sWrapNonSendArm_queries_eq (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy)
    (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    (a1sWrapNonSendArm F stE core).queries wq samplerZeroQueryWeight = core.queries wq samplerZeroQueryWeight := by
  simp [a1sWrapNonSendArm, a1sDelegateCoreArm, Comp.queries, compRename_queries]
private theorem a1sWrapNonSendArm_size_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1sWrapNonSendArm F stE core).size ≤ 6 * stE.size + bits F.K_on + 145 + core.size := by
  have hFrz := a1sIsFrozenE_size_le (.fst stE); have hDel := a1sDelegateCoreArm_size_le F stE core
  simp only [Expr.size] at hFrz; simp only [a1sWrapNonSendArm, aNoneAtomicE, Comp.size, Expr.size]; omega

private theorem pqBytesOps_opSize_zero (o : SignalPqxdh.LegacyCosted.pqBytesOps.Op) :
    SignalPqxdh.LegacyCosted.pqBytesOps.opSize o = 0 := rfl
private theorem pqU32Ops_opSize_zero (o : SignalPqxdh.LegacyCosted.pqU32Ops.Op) :
    SignalPqxdh.LegacyCosted.pqU32Ops.opSize o = 0 := rfl
private theorem mapComp_ddh_le {Δ : List (Ty pqSig)} {out : Ty pqSig} (c : Comp pqxdhOps pqSigAndDdhIface Δ out) :
    (mapComp tlAuthSigDdh c).queries authChalIfaceDdhQueryWeight (fun _ => 0) ≤
      c.queries chalIfaceDdhQueryWeight (fun _ => 0) :=
  mapComp_queries_le tlAuthSigDdh _ (fun _ => 0) _ tlAuthSigDdh_ddhW c
private theorem mapComp_sig_le {Δ : List (Ty pqSig)} {out : Ty pqSig} (c : Comp pqxdhOps pqSigAndDdhIface Δ out) :
    (mapComp tlAuthSigDdh c).queries authChalIfaceSigQueryWeight (fun _ => 0) ≤
      c.queries chalIfaceSigQueryWeight (fun _ => 0) :=
  mapComp_queries_le tlAuthSigDdh _ (fun _ => 0) _ tlAuthSigDdh_sigW c
private theorem mapComp_prim_le {Δ : List (Ty pqSig)} {out : Ty pqSig} (c : Comp pqxdhOps pqSigAndDdhIface Δ out) :
    (mapComp tlAuthSigDdh c).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤
      c.queries chalIfacePrimQueryWeight (fun _ => 0) :=
  mapComp_queries_le tlAuthSigDdh _ (fun _ => 0) _ tlAuthSigDdh_primW c
private theorem liftGdhComp_sig_zero {Δ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Δ out) : (liftGdhComp c).queries chalIfaceSigQueryWeight (fun _ => 0) = 0 := by
  induction c <;> simp_all [liftGdhComp, Comp.queries]; rename_i g _; rcases g with _ | ⟨⟩ <;> rfl
private theorem liftGdhComp_atomic_sig_zero {Δ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Δ out) :
    (mapComp tlAuthSigDdh (liftGdhComp c)).queries authChalIfaceSigQueryWeight (fun _ => 0) = 0 := by
  have h1 := mapComp_sig_le (liftGdhComp c); have h2 := liftGdhComp_sig_zero c; omega
private theorem liftGdhComp_r64_eq {Δ : List (Ty pqSig)} {out : Ty pqSig}
    (ws : SignalPqxdh.LegacyCosted.PSamp → ℕ) (c : Comp pqxdhOps pqGapDhIface Δ out) :
    (liftGdhComp c).queries (fun _ => 0) ws = c.queries (fun _ => 0) ws := by
  induction c <;> simp_all [liftGdhComp, Comp.queries]; rename_i g _; rcases g with _ | ⟨⟩ <;> rfl
private theorem liftGdhComp_compLitSize {Δ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Δ out) : compLitSize (liftGdhComp c) = compLitSize c := by
  induction c <;> simp_all [liftGdhComp, compLitSize]; rename_i g _; rcases g with _ | ⟨⟩ <;> rfl
private theorem liftGdhComp_cost {Δ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Δ out) : (liftGdhComp c).cost = c.cost := by
  induction c <;> simp_all [liftGdhComp, Comp.cost]; rename_i g _; rcases g with _ | ⟨⟩ <;> rfl
private theorem mapComp_liftGdhComp_cost_le {Δ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Δ out) :
    (mapComp tlAuthSigDdh (liftGdhComp c)).cost ≤ 2 * c.cost + 39 * c.queries (fun _ => 0) r64W := by
  have h := mapComp_cost_two_mul_le tlAuthSigDdh (liftGdhComp c)
  have hsmp : sampR64W tlAuthSigDdh.hsmp = r64W := rfl
  rw [liftGdhComp_cost, hsmp, liftGdhComp_r64_eq] at h; omega
private theorem mapComp_liftGdhComp_size_le {Δ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Δ out) :
    (mapComp tlAuthSigDdh (liftGdhComp c)).size ≤ 10 * c.size + compLitSize c := by
  have h := mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (liftGdhComp c)
  rw [SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_size, liftGdhComp_compLitSize] at h
  exact h
private theorem liftGdhComp_ddh_eq {Δ : List (Ty pqSig)} {out : Ty pqSig} (c : Comp pqxdhOps pqGapDhIface Δ out) :
    (liftGdhComp c).queries chalIfaceDdhQueryWeight (fun _ => 0) =
      c.queries SignalPqxdh.Security.ReductionDsl.AuthHs.gdhChalW SignalPqxdh.Security.ReductionDsl.AuthHs.gdhWS := by
  induction c <;> simp_all [liftGdhComp, Comp.queries, SignalPqxdh.Security.ReductionDsl.AuthHs.gdhWS]
  rename_i g _; rcases g with _ | ⟨⟩ <;> rfl
private theorem liftGdhComp_prim_eq {Δ : List (Ty pqSig)} {out : Ty pqSig} (c : Comp pqxdhOps pqGapDhIface Δ out) :
    (liftGdhComp c).queries chalIfacePrimQueryWeight (fun _ => 0) =
      c.queries SignalPqxdh.Security.ReductionDsl.AuthHs.gdhPrimW SignalPqxdh.Security.ReductionDsl.AuthHs.gdhWS := by
  induction c <;> simp_all [liftGdhComp, Comp.queries, SignalPqxdh.Security.ReductionDsl.AuthHs.gdhWS]
  rename_i g _; rcases g with _ | ⟨⟩ <;> rfl
private theorem castLegacySamp_eq (s : SignalPqxdh.LegacyCosted.PSamp) :
    castLegacySamp tlAuthSigDdh.hsmp s = s := rfl

set_option linter.unusedSimpArgs false in
private theorem patchWithShadowC_atomic_cost_both (K_ro : ℕ) {Γ₁ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ] (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy)) (fgCtr : Expr pqxdhOps Δ .nat) :
    (mapComp tlAuthSigDdh (liftGdhComp (patchWithShadowC K_ro k fgL fgSess fgCtr))).cost ≤
      400 + 1350 * K_ro + (mapExpr fgL).cost + (mapExpr fgSess).cost + (mapExpr fgCtr).cost ∧
    (mapComp tlAuthSigDdh (liftGdhComp (patchWithShadowC K_ro k fgL fgSess fgCtr))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (patchWithShadowC 0 k fgL fgSess fgCtr))).cost +
        1350 * K_ro := by
  simp only [patchWithShadowC, liftGdhComp, findMV, entryMatchesC, ddhEqOptC, ddhEqC, letV, bindV,
    caseOptV, caseSumV, eCaseOpt, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.caseSumC,
    Comp.findBoundedM, Comp.sampleDrKey96C, SignalPqxdh.Security.ReductionDsl.AuthHs.Comp.queryDdh,
    Comp.queryChal, v, Expr.bytesBeq, Expr.boolAnd, Expr.boolOr, Expr.boolNot, Expr.litBool,
    Expr.litNat, Expr.listCons, pkP1, pkP2, pkP3, pkP4, pkSs,
    SignalPqxdh.Security.ReductionDsl.AuthHs.feP1, SignalPqxdh.Security.ReductionDsl.AuthHs.feP2,
    SignalPqxdh.Security.ReductionDsl.AuthHs.feP3, SignalPqxdh.Security.ReductionDsl.AuthHs.feP4,
    SignalPqxdh.Security.ReductionDsl.AuthHs.feSs, feDk, embedTy, embedCtx, mapComp, mapExpr, mapOpExpr]
  simp only [tlAuthSigDdh, mapSampCast, mapSampH, castLegacySamp_eq, mapSamp, aiAuthSigDdh,
    Computational.Proofs.SignalPqxdh.AtomicLift.aiOfIface, AtomicIface.toIface,
    pqAuthSigAndDdhIface, SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.sigAndDdhOracle,
    SignalPqxdh.Costed.gapDhDdhOracle, pqAtomicSamplers, atomicBaseSamplers, unifSamplers,
    AtomicBaseUnif.cost, Computational.Proofs.SignalPqxdh.AtomicLift.aop, pqAtomicOps,
    atomicPureOps, AtomicPureOp.cost, Expr.v0, Expr.v1, Expr.v2, bits_0, bits_1,
    Comp.cost, Expr.cost, PNat.val_ofNat, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  simp (discharger := decide) only [Nat.max_eq_left, Nat.max_eq_right, Nat.reduceAdd]
  exact ⟨by omega, by omega⟩

theorem patchWithShadowC_atomic_cost_le (K_ro : ℕ) {Γ₁ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ] (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy)) (fgCtr : Expr pqxdhOps Δ .nat) :
    (mapComp tlAuthSigDdh (liftGdhComp (patchWithShadowC K_ro k fgL fgSess fgCtr))).cost ≤
      400 + 1350 * K_ro + (mapExpr fgL).cost + (mapExpr fgSess).cost + (mapExpr fgCtr).cost :=
  (patchWithShadowC_atomic_cost_both K_ro k fgL fgSess fgCtr).1

private theorem patchWithShadowC_atomic_cost_split (K_ro : ℕ) {Γ₁ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ] (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy)) (fgCtr : Expr pqxdhOps Δ .nat) :
    (mapComp tlAuthSigDdh (liftGdhComp (patchWithShadowC K_ro k fgL fgSess fgCtr))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (patchWithShadowC 0 k fgL fgSess fgCtr))).cost +
        1350 * K_ro :=
  (patchWithShadowC_atomic_cost_both K_ro k fgL fgSess fgCtr).2

set_option linter.unusedSimpArgs false in
private theorem rootPatchWithShadowC_atomic_cost_both (K_ro : ℕ) {Δ : List (Ty pqSig)}
    (rk : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (rootL : Expr pqxdhOps Δ (.list rootEntryTy)) (rootSess : Expr pqxdhOps Δ (.list seqRootEntryTy))
    (rootCtr : Expr pqxdhOps Δ .nat) :
    (mapComp tlAuthSigDdh
      (liftGdhComp (rootPatchWithShadowC K_ro rk pos rootL rootSess rootCtr))).cost ≤
      350 + 383 * K_ro + (mapExpr rk).cost + (mapExpr pos).cost +
        (mapExpr rootL).cost + (mapExpr rootSess).cost + (mapExpr rootCtr).cost ∧
    (mapComp tlAuthSigDdh
      (liftGdhComp (rootPatchWithShadowC K_ro rk pos rootL rootSess rootCtr))).cost ≤
      (mapComp tlAuthSigDdh
        (liftGdhComp (rootPatchWithShadowC 0 rk pos rootL rootSess rootCtr))).cost +
        383 * K_ro := by
  simp only [rootPatchWithShadowC, AuthGapDhK.sampleRootPair64LegC, liftGdhComp, findMV, ddhEqC,
    letV, bindV, caseOptV, caseSumV, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.caseSumC,
    Comp.findBoundedM, Comp.sampleBytes32C, SignalPqxdh.Security.ReductionDsl.AuthHs.Comp.queryDdh,
    Comp.queryChal, v, Expr.bytesBeq, Expr.boolAnd, Expr.boolOr, Expr.boolNot, Expr.litBool,
    Expr.litNat, Expr.listCons, reRk, rePos, reRk1, reCk, embedTy, embedCtx, mapComp, mapExpr, mapOpExpr]
  simp only [tlAuthSigDdh, mapSampCast, mapSampH, castLegacySamp_eq, mapSamp, aiAuthSigDdh,
    Computational.Proofs.SignalPqxdh.AtomicLift.aiOfIface, AtomicIface.toIface,
    pqAuthSigAndDdhIface, SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.sigAndDdhOracle,
    SignalPqxdh.Costed.gapDhDdhOracle, pqAtomicSamplers, atomicBaseSamplers, unifSamplers,
    AtomicBaseUnif.cost, Computational.Proofs.SignalPqxdh.AtomicLift.aop, pqAtomicOps,
    atomicPureOps, AtomicPureOp.cost, Expr.v0, Expr.v1, Expr.v2, bits_0, bits_1,
    Comp.cost, Expr.cost, PNat.val_ofNat, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  simp (discharger := decide) only [Nat.max_eq_left, Nat.max_eq_right, Nat.reduceAdd]
  exact ⟨by omega, by omega⟩

theorem rootPatchWithShadowC_atomic_cost_le (K_ro : ℕ) {Δ : List (Ty pqSig)}
    (rk : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (rootL : Expr pqxdhOps Δ (.list rootEntryTy)) (rootSess : Expr pqxdhOps Δ (.list seqRootEntryTy))
    (rootCtr : Expr pqxdhOps Δ .nat) :
    (mapComp tlAuthSigDdh (liftGdhComp (rootPatchWithShadowC K_ro rk pos rootL rootSess rootCtr))).cost ≤
      350 + 383 * K_ro + (mapExpr rk).cost + (mapExpr pos).cost +
        (mapExpr rootL).cost + (mapExpr rootSess).cost + (mapExpr rootCtr).cost :=
  (rootPatchWithShadowC_atomic_cost_both K_ro rk pos rootL rootSess rootCtr).1

private theorem rootPatchWithShadowC_atomic_cost_split (K_ro : ℕ) {Δ : List (Ty pqSig)}
    (rk : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (rootL : Expr pqxdhOps Δ (.list rootEntryTy)) (rootSess : Expr pqxdhOps Δ (.list seqRootEntryTy))
    (rootCtr : Expr pqxdhOps Δ .nat) :
    (mapComp tlAuthSigDdh (liftGdhComp (rootPatchWithShadowC K_ro rk pos rootL rootSess rootCtr))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (rootPatchWithShadowC 0 rk pos rootL rootSess rootCtr))).cost +
        383 * K_ro :=
  (rootPatchWithShadowC_atomic_cost_both K_ro rk pos rootL rootSess rootCtr).2

private theorem acost_letV {Δ : List (Ty pqSig)} {a out : Ty pqSig} (e : Expr pqxdhOps Δ a)
    (b1 b0 : Var (a :: Δ) a → Comp pqxdhOps pqGapDhIface (a :: Δ) out) {D : ℕ}
    (h : (mapComp tlAuthSigDdh (liftGdhComp (b1 .vz))).cost ≤ (mapComp tlAuthSigDdh (liftGdhComp (b0 .vz))).cost + D) :
    (mapComp tlAuthSigDdh (liftGdhComp (letV e b1))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (letV e b0))).cost + D := by
  simp only [letV, Comp.letC, liftGdhComp, mapComp, Comp.cost]; omega
private theorem acost_ite_r {Δ : List (Ty pqSig)} {out : Ty pqSig} (c : Expr pqxdhOps Δ .bool)
    (t b1 b0 : Comp pqxdhOps pqGapDhIface Δ out) {D : ℕ}
    (h : (mapComp tlAuthSigDdh (liftGdhComp b1)).cost ≤ (mapComp tlAuthSigDdh (liftGdhComp b0)).cost + D) :
    (mapComp tlAuthSigDdh (liftGdhComp (.iteC c t b1))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (.iteC c t b0))).cost + D := by
  simp only [liftGdhComp, mapComp, Comp.cost]; omega
private theorem acost_caseOpt_r {Δ : List (Ty pqSig)} {a out : Ty pqSig} (e : Expr pqxdhOps Δ (.opt a))
    (n : Comp pqxdhOps pqGapDhIface Δ out) (b1 b0 : Var (a :: Δ) a → Comp pqxdhOps pqGapDhIface (a :: Δ) out) {D : ℕ}
    (h : (mapComp tlAuthSigDdh (liftGdhComp (b1 .vz))).cost ≤ (mapComp tlAuthSigDdh (liftGdhComp (b0 .vz))).cost + D) :
    (mapComp tlAuthSigDdh (liftGdhComp (caseOptV e n b1))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (caseOptV e n b0))).cost + D := by
  simp only [caseOptV, Comp.caseOptC, liftGdhComp, mapComp, Comp.cost]; omega
private theorem acost_bind_r {Δ : List (Ty pqSig)} {a out : Ty pqSig} (c : Comp pqxdhOps pqGapDhIface Δ a)
    (b1 b0 : Var (a :: Δ) a → Comp pqxdhOps pqGapDhIface (a :: Δ) out) {D : ℕ}
    (h : (mapComp tlAuthSigDdh (liftGdhComp (b1 .vz))).cost ≤ (mapComp tlAuthSigDdh (liftGdhComp (b0 .vz))).cost + D) :
    (mapComp tlAuthSigDdh (liftGdhComp (bindV c b1))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (bindV c b0))).cost + D := by
  simp only [bindV, liftGdhComp, mapComp, Comp.cost]; omega
private theorem acost_bind_lr {Δ : List (Ty pqSig)} {a out : Ty pqSig}
    {c1 c0 : Comp pqxdhOps pqGapDhIface Δ a} {b1 b0 : Var (a :: Δ) a → Comp pqxdhOps pqGapDhIface (a :: Δ) out} {D1 D2 : ℕ}
    (hc : (mapComp tlAuthSigDdh (liftGdhComp c1)).cost ≤ (mapComp tlAuthSigDdh (liftGdhComp c0)).cost + D1)
    (hb : (mapComp tlAuthSigDdh (liftGdhComp (b1 .vz))).cost ≤ (mapComp tlAuthSigDdh (liftGdhComp (b0 .vz))).cost + D2) :
    (mapComp tlAuthSigDdh (liftGdhComp (bindV c1 b1))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (bindV c0 b0))).cost + (D1 + D2) := by
  simp only [bindV, liftGdhComp, mapComp, Comp.cost]; omega

private theorem bits_32 : bits 32 = 6 := by decide
private theorem bits_33 : bits 33 = 6 := by decide
private theorem bits_64 : bits 64 = 7 := by decide
private theorem bits_96 : bits 96 = 7 := by decide
private theorem bits_158 : bits 158 = 8 := by decide
private theorem bits_192 : bits 192 = 8 := by decide
private theorem bits_1536 : bits 1536 = 11 := by decide
private theorem bits_1568 : bits 1568 = 11 := by decide
private theorem bits_1569 : bits 1569 = 11 := by decide
private theorem bits_3168 : bits 3168 = 12 := by decide
private theorem F_X25519_len : F_X25519.length = 32 := by decide

local macro "leg_base_simp" : tactic => `(tactic|
  simp only [Bool.false_eq_true, ↓reduceIte, liftGdhComp, Comp.liftChal, liftBase, patchWithShadowC,
    rootPatchWithShadowC, AuthGapDhK.sampleRootPair64LegC, entryMatchesC, ddhEqOptC, ddhEqC, twoSideC,
    twoSideOptC, mkSecretPosC, SignalPqxdh.Security.ReductionDsl.AuthHs.mkPairPosC, findHonestC,
    resolveSigPkC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    SignalPqxdh.Security.ReductionDsl.AuthHs.isAdvPowsC, SignalPqxdh.Security.ReductionDsl.AuthHs.isGameSpkC,
    SignalPqxdh.Security.ReductionDsl.AuthHs.isGameOpkC, pkP1, pkP2, pkP3, pkP4, pkSs, feDk, reRk, rePos,
    reRk1, reCk, SignalPqxdh.Security.ReductionDsl.AuthHs.feP1, SignalPqxdh.Security.ReductionDsl.AuthHs.feP2,
    SignalPqxdh.Security.ReductionDsl.AuthHs.feP3, SignalPqxdh.Security.ReductionDsl.AuthHs.feP4,
    SignalPqxdh.Security.ReductionDsl.AuthHs.feSs, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsUpd,
    SignalPqxdh.Security.ReductionDsl.AuthHs.fsMk, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN,
    stKyb, stAdv, stSecb, stUpd, SignalPqxdh.Security.ReductionDsl.AuthHs.stHasWon,
    SignalPqxdh.Security.ReductionDsl.AuthHs.stSOE, SignalPqxdh.Security.ReductionDsl.AuthHs.stSNE,
    SignalPqxdh.Security.ReductionDsl.AuthHs.stROE, SignalPqxdh.Security.ReductionDsl.AuthHs.stRNE,
    SignalPqxdh.Security.ReductionDsl.AuthHs.stRo, SignalPqxdh.Security.ReductionDsl.AuthHs.stRoot,
    SignalPqxdh.Security.ReductionDsl.AuthHs.stMk, pa2U, pa2Role, SignalPqxdh.Security.ReductionDsl.AuthHs.pa2V,
    SignalPqxdh.Security.ReductionDsl.AuthHs.pa2TS, peMk, peSecIKA0, peIkAPk, peSecIKAsign, peCorrupted,
    SignalPqxdh.Security.ReductionDsl.AuthHs.peIkSignPk, SignalPqxdh.Security.ReductionDsl.AuthHs.peUpd,
    sbMk, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed, oeUpd,
    SignalPqxdh.Security.ReductionDsl.AuthHs.oeMk, buMk, buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId,
    buPqspkB, buPqspkSig, hdMk, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, pmHdr, pmEphAPk,
    pmPqMsg, pmAeadCt, seMk, aNone, aInitPrin, aBundle, aPk, aSendFresh, aSendUnfresh, aRecvHonest,
    aRecvUnfresh, SignalPqxdh.Security.ReductionDsl.AuthHs.aCorr, SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
    a1sG, a1sTp, a1sTpk, a1sFg, a1sMk, a1sBase, saFgSess, saFgCtr, saRootSess, saRootCtr, natEq, nat2Eq,
    nat3Eq, sidEq, optU32Eq, isSomeE, sendGuardE, kyberCheckE, firstMsgADE,
    SignalPqxdh.Security.ReductionDsl.AuthHs.kyberEq, SignalPqxdh.Security.ReductionDsl.AuthHs.eLet,
    SignalPqxdh.Security.ReductionDsl.AuthHs.eLet2, encEC, encKEM, slice32, bytesEmpty, zero32, optFst, optSnd,
    q4, letV, bindV, caseOptV, caseSumV, findMV, mapMV, eAny, eFind, eMap, eCaseOpt, eCaseSum, v,
    SignalPqxdh.Security.ReductionDsl.AuthHs.anyMV, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.caseSumC,
    Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM, Comp.sampleBytes32, Comp.sampleRandom64,
    Comp.sampleDrKey96, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C, Comp.queryPrim,
    Comp.queryPrimC, Comp.queryChal, SignalPqxdh.Security.ReductionDsl.AuthHs.Comp.queryDdh,
    SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.sigChalQ_dsl, Expr.litUnit, Expr.litBool, Expr.litNat,
    Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr, Expr.listNil, Expr.listCons,
    Expr.findBounded, Expr.anyBounded, Expr.mapBounded, Expr.litBytes, Expr.bytesAppend, Expr.bytesCons,
    Expr.bytesWiden, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq])

local macro "leg_cost_simp" : tactic => `(tactic| (
  leg_base_simp;
  simp only [↓reduceIte, pqxdhOps, ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr,
    SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.pqU32Ops, pqPrimIface, pqGapDhIface,
    pqSigAndDdhIface, SignalPqxdh.LegacyCosted.pqChalIface, SignalPqxdh.LegacyCosted.pqSamplers,
    SignalPqxdh.LegacyCosted.PSamp.cost, SignalPqxdh.LegacyCosted.PSamp.ty, SignalPqxdh.LegacyCosted.PTag.dom,
    SignalPqxdh.LegacyCosted.PTag.cod, SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
    SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, sigAndDdhOracle, gapDhDdhOracle,
    SignalPqxdh.LegacyCosted.eufCmaSignOracle, SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
    Comp.cost, Expr.cost, PNat.add_coe, PNat.val_ofNat, Nat.zero_mul, Nat.zero_add, Nat.add_zero,
    List.length_nil, List.length_cons, List.length_replicate, F_X25519_len,
    bits_0, bits_1, bits_32, bits_33, bits_64, bits_96, bits_158, bits_192, bits_1536, bits_1568, bits_1569,
    bits_3168];
  simp (discharger := decide) only [Nat.max_eq_left, Nat.max_eq_right, Nat.reduceAdd]))

local macro "leg_size_simp" : tactic => `(tactic| (
  leg_base_simp;
  simp only [Comp.size, Expr.size, pqxdhOps, ReductionDsl.Ops.sum, Sum.elim_inl, Sum.elim_inr,
    pqBytesOps_opSize_zero, pqU32Ops_opSize_zero, bits_0, bits_1, bits_32, bits_33, bits_64, bits_96,
    bits_158, bits_192, bits_1536, bits_1568, bits_1569, bits_3168];
  simp (discharger := decide) only [Nat.max_eq_left, Nat.max_eq_right, Nat.reduceAdd]))

local macro "leg_litsz_simp" : tactic => `(tactic| (
  leg_base_simp;
  simp only [compLitSize, exprLitSize, Computational.Proofs.SignalPqxdh.AtomicLift.pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, F_X25519_len]))

local macro "leg_q_simp" : tactic => `(tactic|
  simp [liftGdhComp, Comp.liftChal, liftBase, patchWithShadowC, rootPatchWithShadowC,
    AuthGapDhK.sampleRootPair64LegC, entryMatchesC, ddhEqOptC, ddhEqC, twoSideC, twoSideOptC, mkSecretPosC,
    SignalPqxdh.Security.ReductionDsl.AuthHs.mkPairPosC, findHonestC, resolveSigPkC, koskBundleOkPowsC,
    koskSenderOkPowsC, lookupSpkSkC, SignalPqxdh.Security.ReductionDsl.AuthHs.isAdvPowsC,
    SignalPqxdh.Security.ReductionDsl.AuthHs.isGameSpkC, SignalPqxdh.Security.ReductionDsl.AuthHs.isGameOpkC,
    letV, bindV, caseOptV, caseSumV, findMV, mapMV, SignalPqxdh.Security.ReductionDsl.AuthHs.anyMV,
    Comp.iteC, Comp.letC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96, Comp.sampleBytes32C, Comp.sampleRandom64C,
    Comp.sampleDrKey96C, Comp.queryPrim, Comp.queryPrimC, Comp.queryChal,
    SignalPqxdh.Security.ReductionDsl.AuthHs.Comp.queryDdh,
    SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.sigChalQ_dsl,
    chalIfaceDdhQueryWeight, chalIfaceSigQueryWeight, chalIfacePrimQueryWeight,
    SignalPqxdh.Security.ReductionDsl.AuthHs.gdhChalW, SignalPqxdh.Security.ReductionDsl.AuthHs.gdhPrimW,
    SignalPqxdh.Security.ReductionDsl.AuthHs.gdhWS, SignalPqxdh.Security.ReductionDsl.AuthHs.primW,
    SignalPqxdh.Security.ReductionDsl.AuthHs.primWS, r64W, Comp.queries])

set_option linter.unusedSimpArgs false in
private theorem a1gInitPrin2LegC_atomic_bounds (F : AuthKindFuels) :
    (mapComp tlAuthSigDdh (liftGdhComp (a1gInitPrin2LegC F))).cost ≤ 1000 + 30 * F.K_on ∧
    (mapComp tlAuthSigDdh (liftGdhComp (a1gInitPrin2LegC F))).queries authChalIfaceDdhQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (a1gInitPrin2LegC F))).queries authChalIfaceSigQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (a1gInitPrin2LegC F))).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤ 1 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (a1gInitPrin2LegC F))).size ≤ 4500 + 10 * bits F.K_on := by
  have hc0 : (a1gInitPrin2LegC F).cost ≤ 500 + 15 * F.K_on := by
    simp only [a1gInitPrin2LegC, a1gInitPrin2C]; leg_cost_simp; omega
  have hr64 : (a1gInitPrin2LegC F).queries (fun _ => 0) r64W = 0 := by
    simp [a1gInitPrin2LegC, a1gInitPrin2C, letV, bindV, Comp.iteC, Comp.letC,
      Comp.sampleBytes32C, Comp.queryPrimC, r64W, Comp.queries]
  have hddh0 : (liftGdhComp (a1gInitPrin2LegC F)).queries chalIfaceDdhQueryWeight (fun _ => 0) = 0 := by
    rw [liftGdhComp_ddh_eq]; simp [a1gInitPrin2LegC, a1gInitPrin2C, letV, bindV, Comp.iteC,
      Comp.letC, Comp.sampleBytes32C, Comp.queryPrimC, SignalPqxdh.Security.ReductionDsl.AuthHs.gdhChalW,
      SignalPqxdh.Security.ReductionDsl.AuthHs.gdhWS, Comp.queries]
  have hprim0 : (liftGdhComp (a1gInitPrin2LegC F)).queries chalIfacePrimQueryWeight (fun _ => 0) ≤ 1 := by
    rw [liftGdhComp_prim_eq]; simp [a1gInitPrin2LegC, a1gInitPrin2C, letV, bindV, Comp.iteC,
      Comp.letC, Comp.sampleBytes32C, Comp.queryPrimC, SignalPqxdh.Security.ReductionDsl.AuthHs.gdhPrimW,
      SignalPqxdh.Security.ReductionDsl.AuthHs.gdhWS, Comp.queries]
  have hsz0 : (a1gInitPrin2LegC F).size ≤ 400 + bits F.K_on := by
    simp only [a1gInitPrin2LegC, a1gInitPrin2C]; leg_size_simp; omega
  have hlit0 : compLitSize (a1gInitPrin2LegC F) ≤ 100 := by
    simp only [a1gInitPrin2LegC, a1gInitPrin2C]; leg_litsz_simp; omega
  have hcost := mapComp_liftGdhComp_cost_le (a1gInitPrin2LegC F)
  have hddh := mapComp_ddh_le (liftGdhComp (a1gInitPrin2LegC F))
  have hprim := mapComp_prim_le (liftGdhComp (a1gInitPrin2LegC F))
  have hsz := mapComp_liftGdhComp_size_le (a1gInitPrin2LegC F)
  exact ⟨by omega, by omega, liftGdhComp_atomic_sig_zero _, by omega, by omega⟩

set_option linter.unusedSimpArgs false in
private theorem fgCorruptLegC_atomic_bounds (F : AuthKindFuels) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgCorruptLegC F))).cost ≤ 1200 + 100 * F.K_on ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgCorruptLegC F))).queries authChalIfaceDdhQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgCorruptLegC F))).queries authChalIfaceSigQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgCorruptLegC F))).queries authChalIfacePrimQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgCorruptLegC F))).size ≤ 4500 + 20 * bits F.K_on := by
  have hc0 : (fgCorruptLegC F).cost ≤ 600 + 50 * F.K_on := by simp only [fgCorruptLegC, onBaseF, corruptB]; leg_cost_simp; omega
  have hr64 : (fgCorruptLegC F).queries (fun _ => 0) r64W = 0 := by simp only [fgCorruptLegC, onBaseF, corruptB]; leg_q_simp
  have hddh0 : (liftGdhComp (fgCorruptLegC F)).queries chalIfaceDdhQueryWeight (fun _ => 0) = 0 := by simp only [fgCorruptLegC, onBaseF, corruptB]; leg_q_simp
  have hprim0 : (liftGdhComp (fgCorruptLegC F)).queries chalIfacePrimQueryWeight (fun _ => 0) = 0 := by simp only [fgCorruptLegC, onBaseF, corruptB]; leg_q_simp
  have hsz0 : (fgCorruptLegC F).size ≤ 450 + 2 * bits F.K_on := by simp only [fgCorruptLegC, onBaseF, corruptB]; leg_size_simp; omega
  have hlit0 : compLitSize (fgCorruptLegC F) = 0 := by simp only [fgCorruptLegC, onBaseF, corruptB]; leg_litsz_simp
  have hcost := mapComp_liftGdhComp_cost_le (fgCorruptLegC F); have hddh := mapComp_ddh_le (liftGdhComp (fgCorruptLegC F))
  have hprim := mapComp_prim_le (liftGdhComp (fgCorruptLegC F)); have hsz := mapComp_liftGdhComp_size_le (fgCorruptLegC F)
  exact ⟨by omega, by omega, liftGdhComp_atomic_sig_zero _, by omega, by omega⟩

set_option linter.unusedSimpArgs false in
private theorem fgGenOpkLegC_atomic_bounds (F : AuthKindFuels) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgGenOpkLegC F))).cost ≤ 1200 + 50 * F.K_on ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgGenOpkLegC F))).queries authChalIfaceDdhQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgGenOpkLegC F))).queries authChalIfaceSigQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgGenOpkLegC F))).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤ 1 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgGenOpkLegC F))).size ≤ 4000 + 10 * bits F.K_on := by
  have hc0 : (fgGenOpkLegC F).cost ≤ 600 + 25 * F.K_on := by simp only [fgGenOpkLegC, onBaseF, genOpkB]; leg_cost_simp; omega
  have hr64 : (fgGenOpkLegC F).queries (fun _ => 0) r64W = 0 := by simp only [fgGenOpkLegC, onBaseF, genOpkB]; leg_q_simp
  have hddh0 : (liftGdhComp (fgGenOpkLegC F)).queries chalIfaceDdhQueryWeight (fun _ => 0) = 0 := by simp only [fgGenOpkLegC, onBaseF, genOpkB]; leg_q_simp
  have hprim0 : (liftGdhComp (fgGenOpkLegC F)).queries chalIfacePrimQueryWeight (fun _ => 0) ≤ 1 := by simp only [fgGenOpkLegC, onBaseF, genOpkB]; leg_q_simp
  have hsz0 : (fgGenOpkLegC F).size ≤ 400 + bits F.K_on := by simp only [fgGenOpkLegC, onBaseF, genOpkB]; leg_size_simp; omega
  have hlit0 : compLitSize (fgGenOpkLegC F) = 0 := by simp only [fgGenOpkLegC, onBaseF, genOpkB]; leg_litsz_simp
  have hcost := mapComp_liftGdhComp_cost_le (fgGenOpkLegC F); have hddh := mapComp_ddh_le (liftGdhComp (fgGenOpkLegC F))
  have hprim := mapComp_prim_le (liftGdhComp (fgGenOpkLegC F)); have hsz := mapComp_liftGdhComp_size_le (fgGenOpkLegC F)
  exact ⟨by omega, by omega, liftGdhComp_atomic_sig_zero _, by omega, by omega⟩

set_option linter.unusedSimpArgs false in
private theorem fgRegisterLegC_atomic_bounds :
    (mapComp tlAuthSigDdh (liftGdhComp fgRegisterLegC)).cost ≤ 1000 ∧
    (mapComp tlAuthSigDdh (liftGdhComp fgRegisterLegC)).queries authChalIfaceDdhQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp fgRegisterLegC)).queries authChalIfaceSigQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp fgRegisterLegC)).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤ 2 ∧
    (mapComp tlAuthSigDdh (liftGdhComp fgRegisterLegC)).size ≤ 3500 := by
  have hc0 : fgRegisterLegC.cost ≤ 500 := by simp only [fgRegisterLegC, fgRegisterC, SignalPqxdh.Security.ReductionDsl.AuthHs.registerB]; leg_cost_simp; omega
  have hr64 : fgRegisterLegC.queries (fun _ => 0) r64W = 0 := by simp only [fgRegisterLegC, fgRegisterC, SignalPqxdh.Security.ReductionDsl.AuthHs.registerB]; leg_q_simp
  have hddh0 : (liftGdhComp fgRegisterLegC).queries chalIfaceDdhQueryWeight (fun _ => 0) = 0 := by simp only [fgRegisterLegC, fgRegisterC, SignalPqxdh.Security.ReductionDsl.AuthHs.registerB]; leg_q_simp
  have hprim0 : (liftGdhComp fgRegisterLegC).queries chalIfacePrimQueryWeight (fun _ => 0) ≤ 2 := by simp only [fgRegisterLegC, fgRegisterC, SignalPqxdh.Security.ReductionDsl.AuthHs.registerB]; leg_q_simp
  have hsz0 : fgRegisterLegC.size ≤ 350 := by simp only [fgRegisterLegC, fgRegisterC, SignalPqxdh.Security.ReductionDsl.AuthHs.registerB]; leg_size_simp; omega
  have hlit0 : compLitSize fgRegisterLegC = 0 := by simp only [fgRegisterLegC, fgRegisterC, SignalPqxdh.Security.ReductionDsl.AuthHs.registerB]; leg_litsz_simp
  have hcost := mapComp_liftGdhComp_cost_le fgRegisterLegC; have hddh := mapComp_ddh_le (liftGdhComp fgRegisterLegC)
  have hprim := mapComp_prim_le (liftGdhComp fgRegisterLegC); have hsz := mapComp_liftGdhComp_size_le fgRegisterLegC
  exact ⟨by omega, by omega, liftGdhComp_atomic_sig_zero _, by omega, by omega⟩

set_option linter.unusedSimpArgs false in
private theorem a1gGenSpk2LegC_atomic_bounds (F : AuthKindFuels) :
    (mapComp tlAuthSigDdh (a1gGenSpk2LegC F)).cost ≤ 14500 + 100 * F.K_on ∧
    (mapComp tlAuthSigDdh (a1gGenSpk2LegC F)).queries authChalIfaceDdhQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (a1gGenSpk2LegC F)).queries authChalIfaceSigQueryWeight (fun _ => 0) ≤ 2 ∧
    (mapComp tlAuthSigDdh (a1gGenSpk2LegC F)).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤ 4 ∧
    (mapComp tlAuthSigDdh (a1gGenSpk2LegC F)).size ≤ 13000 + 40 * bits F.K_on := by
  have hc0 : (a1gGenSpk2LegC F).cost ≤ 9500 + 50 * F.K_on := by simp only [a1gGenSpk2LegC, a1gGenSpk2C, fgGenSpk2C]; leg_cost_simp; omega
  have hr64 : (a1gGenSpk2LegC F).queries (fun _ => 0) (sampR64W tlAuthSigDdh.hsmp) ≤ 3 := by
    change (a1gGenSpk2LegC F).queries (fun _ => 0) r64W ≤ 3; simp only [a1gGenSpk2LegC, a1gGenSpk2C, fgGenSpk2C]; leg_q_simp
  have hddh0 : (a1gGenSpk2LegC F).queries chalIfaceDdhQueryWeight (fun _ => 0) = 0 := by simp only [a1gGenSpk2LegC, a1gGenSpk2C, fgGenSpk2C]; leg_q_simp
  have hsig0 : (a1gGenSpk2LegC F).queries chalIfaceSigQueryWeight (fun _ => 0) ≤ 2 := by simp only [a1gGenSpk2LegC, a1gGenSpk2C, fgGenSpk2C]; leg_q_simp
  have hprim0 : (a1gGenSpk2LegC F).queries chalIfacePrimQueryWeight (fun _ => 0) ≤ 4 := by simp only [a1gGenSpk2LegC, a1gGenSpk2C, fgGenSpk2C]; leg_q_simp
  have hsz0 : (a1gGenSpk2LegC F).size ≤ 1200 + 4 * bits F.K_on := by simp only [a1gGenSpk2LegC, a1gGenSpk2C, fgGenSpk2C]; leg_size_simp; omega
  have hlit0 : compLitSize (a1gGenSpk2LegC F) ≤ 250 := by simp only [a1gGenSpk2LegC, a1gGenSpk2C, fgGenSpk2C]; leg_litsz_simp; omega
  have hcost := mapComp_cost_two_mul_le tlAuthSigDdh (a1gGenSpk2LegC F)
  have hddh := mapComp_ddh_le (a1gGenSpk2LegC F); have hsig := mapComp_sig_le (a1gGenSpk2LegC F)
  have hprim := mapComp_prim_le (a1gGenSpk2LegC F); have hsz := mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (a1gGenSpk2LegC F)
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

set_option linter.unusedSimpArgs false in
theorem a1sSendCheckLegC_atomic_bounds (S : Setup) (F : AuthKindFuels) :
    (mapComp tlAuthSigDdh (a1sSendCheckLegC S F)).cost ≤
      11500 + 5500 * F.K_on + 320 * min F.K_on S.N_dh ∧
    (mapComp tlAuthSigDdh (a1sSendCheckLegC S F)).queries authChalIfaceDdhQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (a1sSendCheckLegC S F)).queries authChalIfaceSigQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (a1sSendCheckLegC S F)).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤
      2 + 2 * min F.K_on S.N_dh ∧
    (mapComp tlAuthSigDdh (a1sSendCheckLegC S F)).size ≤
      9500 + 20 * bits F.K_on + 10 * bits (min F.K_on S.N_dh) := by
  have hc0 : (a1sSendCheckLegC S F).cost ≤ 7500 + 3500 * F.K_on + 210 * min F.K_on S.N_dh := by
    simp only [a1sSendCheckLegC, extractKC, SignalPqxdh.Security.ReductionDsl.AuthHs.extractC,
      SignalPqxdh.Security.ReductionDsl.AuthHs.honestPeerC]; leg_cost_simp; omega
  have hr64 : (a1sSendCheckLegC S F).queries (fun _ => 0) (sampR64W tlAuthSigDdh.hsmp) = 0 := by
    change (a1sSendCheckLegC S F).queries (fun _ => 0) r64W = 0
    simp only [a1sSendCheckLegC, extractKC, SignalPqxdh.Security.ReductionDsl.AuthHs.extractC,
      SignalPqxdh.Security.ReductionDsl.AuthHs.honestPeerC]; leg_q_simp
  have hddh0 : (a1sSendCheckLegC S F).queries chalIfaceDdhQueryWeight (fun _ => 0) = 0 := by
    simp only [a1sSendCheckLegC, extractKC, SignalPqxdh.Security.ReductionDsl.AuthHs.extractC,
      SignalPqxdh.Security.ReductionDsl.AuthHs.honestPeerC]; leg_q_simp
  have hsig0 : (a1sSendCheckLegC S F).queries chalIfaceSigQueryWeight (fun _ => 0) = 0 := by
    simp only [a1sSendCheckLegC, extractKC, SignalPqxdh.Security.ReductionDsl.AuthHs.extractC,
      SignalPqxdh.Security.ReductionDsl.AuthHs.honestPeerC]; leg_q_simp
  have hprim0 : (a1sSendCheckLegC S F).queries chalIfacePrimQueryWeight (fun _ => 0) ≤
      2 + 2 * min F.K_on S.N_dh := by
    simp only [a1sSendCheckLegC, extractKC, SignalPqxdh.Security.ReductionDsl.AuthHs.extractC,
      SignalPqxdh.Security.ReductionDsl.AuthHs.honestPeerC]; leg_q_simp; omega
  have hsz0 : (a1sSendCheckLegC S F).size ≤ 900 + 2 * bits F.K_on + bits (min F.K_on S.N_dh) := by
    simp only [a1sSendCheckLegC, extractKC, SignalPqxdh.Security.ReductionDsl.AuthHs.extractC,
      SignalPqxdh.Security.ReductionDsl.AuthHs.honestPeerC]; leg_size_simp; omega
  have hlit0 : compLitSize (a1sSendCheckLegC S F) ≤ 100 := by
    simp only [a1sSendCheckLegC, extractKC, SignalPqxdh.Security.ReductionDsl.AuthHs.extractC,
      SignalPqxdh.Security.ReductionDsl.AuthHs.honestPeerC]; leg_litsz_simp; omega
  have hcost := mapComp_cost_two_mul_le tlAuthSigDdh (a1sSendCheckLegC S F)
  have hddh := mapComp_ddh_le (a1sSendCheckLegC S F); have hsig := mapComp_sig_le (a1sSendCheckLegC S F)
  have hprim := mapComp_prim_le (a1sSendCheckLegC S F)
  have hsz := mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (a1sSendCheckLegC S F)
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem fgSend2ShadowC_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgSend2ShadowC S F opk))).cost ≤
      1733 * F.K_ro + 8000 * F.K_on + 10000 * min F.K_on S.N_dh + 40000 := by
  have hsplit : (mapComp tlAuthSigDdh (liftGdhComp (fgSend2ShadowC S F opk))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (fgSend2ShadowC S { F with K_ro := 0 } opk))).cost +
        (1350 * F.K_ro + (383 * F.K_ro + 0)) := by
    dsimp only [fgSend2ShadowC]
    repeat' first
      | apply acost_letV | apply acost_ite_r | apply acost_caseOpt_r | apply acost_bind_r
      | refine acost_bind_lr (patchWithShadowC_atomic_cost_split F.K_ro _ _ _ _) ?_
      | refine acost_bind_lr (rootPatchWithShadowC_atomic_cost_split F.K_ro _ _ _ _ _) ?_
      | exact Nat.le_add_right _ 0
  have hc0 : (fgSend2ShadowC S { F with K_ro := 0 } opk).cost ≤
      19000 + 4000 * F.K_on + 5000 * min F.K_on S.N_dh := by
    cases opk <;> (simp only [fgSend2ShadowC]; leg_cost_simp; omega)
  have hr64 : (fgSend2ShadowC S { F with K_ro := 0 } opk).queries (fun _ => 0) r64W = 0 := by
    cases opk <;> (simp only [fgSend2ShadowC]; leg_q_simp)
  have hcost := mapComp_liftGdhComp_cost_le (fgSend2ShadowC S { F with K_ro := 0 } opk)
  omega

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem fgSend2ShadowC_q_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgSend2ShadowC S F opk))).queries
      authChalIfaceDdhQueryWeight (fun _ => 0) ≤ 5 * F.K_ro ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgSend2ShadowC S F opk))).queries
      authChalIfaceSigQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgSend2ShadowC S F opk))).queries
      authChalIfacePrimQueryWeight (fun _ => 0) ≤ 26 + 12 * min F.K_on S.N_dh := by
  have hddh0 : (liftGdhComp (fgSend2ShadowC S F opk)).queries chalIfaceDdhQueryWeight (fun _ => 0) ≤
      5 * F.K_ro := by cases opk <;> (simp only [fgSend2ShadowC]; leg_q_simp; omega)
  have hprim0 : (liftGdhComp (fgSend2ShadowC S F opk)).queries chalIfacePrimQueryWeight (fun _ => 0) ≤
      26 + 12 * min F.K_on S.N_dh := by cases opk <;> (simp only [fgSend2ShadowC]; leg_q_simp; omega)
  have hddh := mapComp_ddh_le (liftGdhComp (fgSend2ShadowC S F opk))
  have hprim := mapComp_prim_le (liftGdhComp (fgSend2ShadowC S F opk))
  exact ⟨by omega, liftGdhComp_atomic_sig_zero _, by omega⟩

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem fgSend2ShadowC_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgSend2ShadowC S F opk))).size ≤
      46000 + 80 * bits F.K_on + 20 * bits F.K_ro + 60 * bits (min F.K_on S.N_dh) := by
  have hsz0 : (fgSend2ShadowC S F opk).size ≤
      4500 + 8 * bits F.K_on + 2 * bits F.K_ro + 6 * bits (min F.K_on S.N_dh) := by
    cases opk <;> (simp only [fgSend2ShadowC]; leg_size_simp; omega)
  have hlit0 : compLitSize (fgSend2ShadowC S F opk) ≤ 1000 := by
    cases opk <;> (simp only [fgSend2ShadowC]; leg_litsz_simp; omega)
  have hsz := mapComp_liftGdhComp_size_le (fgSend2ShadowC S F opk); omega

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem fgRecvShadowB_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgRecvShadowB S F opk))).cost ≤
      1733 * F.K_ro + 5000 * F.K_on + 8000 * min F.K_on S.N_dh + 40000 := by
  have hsplit : (mapComp tlAuthSigDdh (liftGdhComp (fgRecvShadowB S F opk))).cost ≤
      (mapComp tlAuthSigDdh (liftGdhComp (fgRecvShadowB S { F with K_ro := 0 } opk))).cost +
        (1350 * F.K_ro + (383 * F.K_ro + 0)) := by
    dsimp only [fgRecvShadowB, fgRecvShadowC]
    repeat' first
      | apply acost_letV | apply acost_ite_r | apply acost_caseOpt_r | apply acost_bind_r
      | refine acost_bind_lr (patchWithShadowC_atomic_cost_split F.K_ro _ _ _ _) ?_
      | refine acost_bind_lr (rootPatchWithShadowC_atomic_cost_split F.K_ro _ _ _ _ _) ?_
      | exact Nat.le_add_right _ 0
  have hc0 : (fgRecvShadowB S { F with K_ro := 0 } opk).cost ≤
      19000 + 2500 * F.K_on + 4000 * min F.K_on S.N_dh := by
    cases opk <;> (simp only [fgRecvShadowB, fgRecvShadowC]; leg_cost_simp; omega)
  have hr64 : (fgRecvShadowB S { F with K_ro := 0 } opk).queries (fun _ => 0) r64W = 0 := by
    cases opk <;> (simp only [fgRecvShadowB, fgRecvShadowC]; leg_q_simp)
  have hcost := mapComp_liftGdhComp_cost_le (fgRecvShadowB S { F with K_ro := 0 } opk)
  omega

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem fgRecvShadowB_q_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgRecvShadowB S F opk))).queries
      authChalIfaceDdhQueryWeight (fun _ => 0) ≤ 5 * F.K_ro ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgRecvShadowB S F opk))).queries
      authChalIfaceSigQueryWeight (fun _ => 0) = 0 ∧
    (mapComp tlAuthSigDdh (liftGdhComp (fgRecvShadowB S F opk))).queries
      authChalIfacePrimQueryWeight (fun _ => 0) ≤ 22 + 4 * min F.K_on S.N_dh := by
  have hddh0 : (liftGdhComp (fgRecvShadowB S F opk)).queries chalIfaceDdhQueryWeight (fun _ => 0) ≤
      5 * F.K_ro := by cases opk <;> (simp only [fgRecvShadowB, fgRecvShadowC]; leg_q_simp; omega)
  have hprim0 : (liftGdhComp (fgRecvShadowB S F opk)).queries chalIfacePrimQueryWeight (fun _ => 0) ≤
      22 + 4 * min F.K_on S.N_dh := by
    cases opk <;> (simp only [fgRecvShadowB, fgRecvShadowC]; leg_q_simp; omega)
  have hddh := mapComp_ddh_le (liftGdhComp (fgRecvShadowB S F opk))
  have hprim := mapComp_prim_le (liftGdhComp (fgRecvShadowB S F opk))
  exact ⟨by omega, liftGdhComp_atomic_sig_zero _, by omega⟩

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem fgRecvShadowB_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgRecvShadowB S F opk))).size ≤
      46000 + 80 * bits F.K_on + 20 * bits F.K_ro + 20 * bits (min F.K_on S.N_dh) := by
  have hsz0 : (fgRecvShadowB S F opk).size ≤
      4500 + 8 * bits F.K_on + 2 * bits F.K_ro + 2 * bits (min F.K_on S.N_dh) := by
    cases opk <;> (simp only [fgRecvShadowB, fgRecvShadowC]; leg_size_simp; omega)
  have hlit0 : compLitSize (fgRecvShadowB S F opk) ≤ 1000 := by
    cases opk <;> (simp only [fgRecvShadowB, fgRecvShadowC]; leg_litsz_simp; omega)
  have hsz := mapComp_liftGdhComp_size_le (fgRecvShadowB S F opk); omega

@[expose] def a1g2Kind0ArmCostBound (S : Setup) (F : AuthKindFuels) : ℕ :=
  1733 * F.K_ro + 9000 * F.K_on + 12000 * min F.K_on S.N_dh + 45000
@[expose] def a1s2Kind0ArmCostBound (S : Setup) (F : AuthKindFuels) : ℕ :=
  1733 * F.K_ro + 15000 * F.K_on + 13000 * min F.K_on S.N_dh + 55000
@[expose] def authKind0ArmSizeBound (S : Setup) (F : AuthKindFuels) : ℕ :=
  105 * bits F.K_on + 25 * bits F.K_ro + 75 * bits (min F.K_on S.N_dh) + 60000

private def CoreBnd {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) (cb db sb pb szb : ℕ) : Prop :=
  c.cost ≤ cb ∧ c.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ db ∧
  c.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ sb ∧
  c.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ pb ∧ c.size ≤ szb

private def ArmBnd {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    (c : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out) (cb db sb pb szb : ℕ) : Prop :=
  c.cost ≤ cb ∧ c.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ db ∧
  c.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ sb ∧
  c.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ pb ∧ c.size ≤ szb

local macro "core_all_simp" : tactic => `(tactic|
  simp only [CoreBnd, fgCoreArm_initPrin, fgCoreArm_corrupt, fgCoreArm_genSPK, fgCoreArm_genOPK,
    fgCoreArm_send, fgCoreArm_recv, fgCoreArm_revealDh, fgCoreArm_registerKey,
    auxSessSliceE, auxFgSessE, auxFgCtrE, auxFgRootSessE, auxFgRootCtrE,
    auxPutSessSliceE, fgAuxMkE, auxFgRoAvlE, auxFgRootRoAvlE, auxRawAvlE, aNoneAtomicE,
    liftGdh1_cost, liftCs1_cost, liftGdh1_size, liftCs1_size,
    exprRename_cost, exprRename_size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Comp.cost, Expr.cost, Comp.size, Expr.size, Comp.queries, Nat.zero_add, Nat.add_zero, Nat.zero_max])

set_option linter.unusedSimpArgs false in
private theorem fgCore_initPrin_bnd (F : AuthKindFuels) {Γ} (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (uE : Expr pqAtomicOps Γ .nat) :
    CoreBnd (fgCoreArm_initPrin F paE simE sigBE auxE uE)
      (paE.cost + simE.cost + sigBE.cost + auxE.cost + uE.cost + 1050 + 30 * F.K_on) 0 0 1
      (paE.size + simE.size + sigBE.size + auxE.size + uE.size + 4550 + 10 * bits F.K_on) := by
  rcases a1gInitPrin2LegC_atomic_bounds F with ⟨hc, hd, hs, hp, hsz⟩; core_all_simp
  exact ⟨by omega, (liftGdh1_queries _ _ _).trans_le hd.le, (liftGdh1_queries _ _ _).trans_le hs.le,
    (liftGdh1_queries _ _ _).trans_le hp, by omega⟩
set_option linter.unusedSimpArgs false in
private theorem fgCore_corrupt_bnd (F : AuthKindFuels) {Γ} (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (uE : Expr pqAtomicOps Γ .nat) :
    CoreBnd (fgCoreArm_corrupt F simE sigBE auxE uE)
      (simE.cost + sigBE.cost + auxE.cost + uE.cost + 1250 + 100 * F.K_on) 0 0 0
      (simE.size + sigBE.size + auxE.size + uE.size + 4550 + 20 * bits F.K_on) := by
  rcases fgCorruptLegC_atomic_bounds F with ⟨hc, hd, hs, hp, hsz⟩; core_all_simp
  exact ⟨by omega, (liftGdh1_queries _ _ _).trans_le hd.le, (liftGdh1_queries _ _ _).trans_le hs.le,
    (liftGdh1_queries _ _ _).trans_le hp.le, by omega⟩
set_option linter.unusedSimpArgs false in
private theorem fgCore_genSPK_bnd (F : AuthKindFuels) {Γ} (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (xE : Expr pqAtomicOps Γ (.prod .nat .nat)) :
    CoreBnd (fgCoreArm_genSPK F paE simE sigBE auxE xE)
      (paE.cost + simE.cost + sigBE.cost + auxE.cost + xE.cost + 14550 + 100 * F.K_on) 0 2 4
      (paE.size + simE.size + sigBE.size + auxE.size + xE.size + 13050 + 40 * bits F.K_on) := by
  rcases a1gGenSpk2LegC_atomic_bounds F with ⟨hc, hd, hs, hp, hsz⟩; core_all_simp
  exact ⟨by omega, (liftCs1_queries _ _ _).trans_le hd.le, (liftCs1_queries _ _ _).trans_le hs,
    (liftCs1_queries _ _ _).trans_le hp, by omega⟩
set_option linter.unusedSimpArgs false in
private theorem fgCore_genOPK_bnd (F : AuthKindFuels) {Γ} (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (xE : Expr pqAtomicOps Γ (.prod .nat (.prod .nat .nat))) :
    CoreBnd (fgCoreArm_genOPK F simE sigBE auxE xE)
      (simE.cost + sigBE.cost + auxE.cost + xE.cost + 1250 + 50 * F.K_on) 0 0 1
      (simE.size + sigBE.size + auxE.size + xE.size + 4050 + 10 * bits F.K_on) := by
  rcases fgGenOpkLegC_atomic_bounds F with ⟨hc, hd, hs, hp, hsz⟩; core_all_simp
  exact ⟨by omega, (liftGdh1_queries _ _ _).trans_le hd.le, (liftGdh1_queries _ _ _).trans_le hs.le,
    (liftGdh1_queries _ _ _).trans_le hp, by omega⟩
set_option linter.unusedSimpArgs false in
private theorem fgCore_revealDh_bnd {Γ} (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    CoreBnd (fgCoreArm_revealDh simE sigBE auxE)
      (simE.cost + sigBE.cost + auxE.cost + 20) 0 0 0 (simE.size + sigBE.size + auxE.size + 25) := by
  core_all_simp; exact ⟨by omega, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, by omega⟩
set_option linter.unusedSimpArgs false in
private theorem fgCore_registerKey_bnd {Γ} (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (skE : Expr pqAtomicOps Γ (PB 32)) :
    CoreBnd (fgCoreArm_registerKey simE sigBE auxE skE)
      (simE.cost + sigBE.cost + auxE.cost + skE.cost + 1050) 0 0 2
      (simE.size + sigBE.size + auxE.size + skE.size + 3550) := by
  rcases fgRegisterLegC_atomic_bounds with ⟨hc, hd, hs, hp, hsz⟩; core_all_simp
  exact ⟨by omega, (liftGdh1_queries _ _ _).trans_le hd.le, (liftGdh1_queries _ _ _).trans_le hs.le,
    (liftGdh1_queries _ _ _).trans_le hp, by omega⟩
set_option linter.unusedSimpArgs false in
private theorem fgCore_send_bnd (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty)) (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (xE : Expr pqAtomicOps Γ authSendQAtomicTy) :
    CoreBnd (fgCoreArm_send S F opk paE simE sigBE auxE xE)
      (paE.cost + simE.cost + sigBE.cost + auxE.cost + xE.cost +
        1733 * F.K_ro + 8000 * F.K_on + 10000 * min F.K_on S.N_dh + 40150)
      (5 * F.K_ro) 0 (26 + 12 * min F.K_on S.N_dh)
      (paE.size + simE.size + sigBE.size + auxE.size + xE.size +
        46150 + 80 * bits F.K_on + 20 * bits F.K_ro + 60 * bits (min F.K_on S.N_dh)) := by
  have hC := fgSend2ShadowC_cost_le S F opk; rcases fgSend2ShadowC_q_le S F opk with ⟨hd, hs, hp⟩
  have hS := fgSend2ShadowC_size_le S F opk; core_all_simp
  exact ⟨by omega, (liftGdh1_queries _ _ _).trans_le hd, (liftGdh1_queries _ _ _).trans_le hs.le,
    (liftGdh1_queries _ _ _).trans_le hp, by omega⟩
set_option linter.unusedSimpArgs false in
private theorem fgCore_recv_bnd (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (xE : Expr pqAtomicOps Γ authRecvQAtomicTy) :
    CoreBnd (fgCoreArm_recv S F opk simE sigBE auxE xE)
      (simE.cost + sigBE.cost + auxE.cost + xE.cost +
        1733 * F.K_ro + 5000 * F.K_on + 8000 * min F.K_on S.N_dh + 40150)
      (5 * F.K_ro) 0 (22 + 4 * min F.K_on S.N_dh)
      (simE.size + sigBE.size + auxE.size + xE.size +
        46150 + 80 * bits F.K_on + 20 * bits F.K_ro + 20 * bits (min F.K_on S.N_dh)) := by
  have hC := fgRecvShadowB_cost_le S F opk; rcases fgRecvShadowB_q_le S F opk with ⟨hd, hs, hp⟩
  have hS := fgRecvShadowB_size_le S F opk; core_all_simp
  exact ⟨by omega, (liftGdh1_queries _ _ _).trans_le hd, (liftGdh1_queries _ _ _).trans_le hs.le,
    (liftGdh1_queries _ _ _).trans_le hp, by omega⟩
private theorem a1gWrap_bnd (F : AuthKindFuels) {qTy : Ty pqAtomicSig}
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface [qTy, a1g2ShadowStTy, authQueryAtomicTy] fgCoreOutTy)
    {cb db sb pb szb cb' db' sb' pb' szb' : ℕ} (hc : CoreBnd core cb db sb pb szb)
    (h1 : 5 * F.K_on + 63 + cb ≤ cb') (h2 : db ≤ db') (h3 : sb ≤ sb') (h4 : pb ≤ pb')
    (h5 : bits F.K_on + 79 + szb ≤ szb') : ArmBnd (a1gWrapCoreArm F .v1 core) cb' db' sb' pb' szb' := by
  have hC := a1gWrapCoreArm_cost_le F (Γ := [qTy, a1g2ShadowStTy, authQueryAtomicTy]) .v1 core
  have hS := a1gWrapCoreArm_size_le F (Γ := [qTy, a1g2ShadowStTy, authQueryAtomicTy]) .v1 core
  rcases hc with ⟨hc1, hc2, hc3, hc4, hc5⟩
  refine ⟨?_, (a1gWrapCoreArm_queries_eq F .v1 core _).trans_le (hc2.trans h2),
    (a1gWrapCoreArm_queries_eq F .v1 core _).trans_le (hc3.trans h3),
    (a1gWrapCoreArm_queries_eq F .v1 core _).trans_le (hc4.trans h4), ?_⟩
  · dsimp only [Expr.v1, Expr.cost] at hC ⊢; omega
  · dsimp only [Expr.v1, Expr.size] at hS ⊢; omega
private theorem a1sWrap_bnd (F : AuthKindFuels) {qTy : Ty pqAtomicSig}
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface [qTy, a1s2ShadowStTy, authQueryAtomicTy] fgCoreOutTy)
    {cb db sb pb szb cb' db' sb' pb' szb' : ℕ} (hc : CoreBnd core cb db sb pb szb)
    (h1 : 5 * F.K_on + 134 + cb ≤ cb') (h2 : db ≤ db') (h3 : sb ≤ sb') (h4 : pb ≤ pb')
    (h5 : bits F.K_on + 151 + szb ≤ szb') : ArmBnd (a1sWrapNonSendArm F .v1 core) cb' db' sb' pb' szb' := by
  have hC := a1sWrapNonSendArm_cost_le F (Γ := [qTy, a1s2ShadowStTy, authQueryAtomicTy]) .v1 core
  have hS := a1sWrapNonSendArm_size_le F (Γ := [qTy, a1s2ShadowStTy, authQueryAtomicTy]) .v1 core
  rcases hc with ⟨hc1, hc2, hc3, hc4, hc5⟩
  refine ⟨?_, (a1sWrapNonSendArm_queries_eq F .v1 core _).trans_le (hc2.trans h2),
    (a1sWrapNonSendArm_queries_eq F .v1 core _).trans_le (hc3.trans h3),
    (a1sWrapNonSendArm_queries_eq F .v1 core _).trans_le (hc4.trans h4), ?_⟩
  · dsimp only [Expr.v1, Expr.cost] at hC ⊢; omega
  · dsimp only [Expr.v1, Expr.size] at hS ⊢; omega
set_option linter.unusedSimpArgs false in
private theorem a1s_send_bnd (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    ArmBnd (a1sArm_send S F opk) (a1s2Kind0ArmCostBound S F) (5 * F.K_ro) 2
      (176 + 32 * min F.K_on S.N_dh) (authKind0ArmSizeBound S F) := by
  let Γ0 : List (Ty pqAtomicSig) := [authSendQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy]
  let Γ2 : List (Ty pqAtomicSig) := embedTy .unit :: embedTy (.sum a1sRS .unit) :: Γ0
  have hFrzC := a1sIsFrozenE_cost_le (Γ := Γ0) (.fst .v1); have hFrzS := a1sIsFrozenE_size_le (Γ := Γ0) (.fst .v1)
  rcases a1sSendCheckLegC_atomic_bounds S F with ⟨hChkC, hChkD, hChkSg, hChkP, hChkS⟩
  have hPaC := a1sCaseAPa2AtomicE_cost_le (Γ := Γ2) (.fst .v3); have hPaS := a1sCaseAPa2AtomicE_size_le (Γ := Γ2) (.fst .v3)
  let core := fgCoreArm_send S F opk (Γ := Γ2) (a1sCaseAPa2AtomicE (.fst .v3)) (a1sSimAtomicE (.fst .v3)) (a1sSigBAtomicE (.fst .v3)) (.snd .v3) .v2
  have hCore := fgCore_send_bnd S F opk (Γ := Γ2) (a1sCaseAPa2AtomicE (.fst .v3)) (a1sSimAtomicE (.fst .v3)) (a1sSigBAtomicE (.fst .v3)) (.snd .v3) .v2
  change CoreBnd core _ _ _ _ _ at hCore; rcases hCore with ⟨hcC, hcD, hcSg, hcP, hcS⟩
  have hDelC := a1sDelegateCoreArm_cost_le F (Γ := Γ2) .v3 core; have hDelS := a1sDelegateCoreArm_size_le F (Γ := Γ2) .v3 core
  change ArmBnd (.ite (a1sIsFrozenE (.fst .v1)) (.ret (.pair aNoneAtomicE .v1))
    (.bind (liftCs1 (a1sSendCheckLegC S F) (.pair (.fst .v1) .v0))
      (.caseSum .v0 (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v3)))) (a1sDelegateCoreArm F .v3 core)))) _ _ _ _ _
  simp only [ArmBnd, a1s2Kind0ArmCostBound, authKind0ArmSizeBound, aNoneAtomicE,
    liftCs1_cost, liftCs1_size, Comp.cost, Comp.size, Comp.queries, Nat.zero_add, Nat.add_zero, Nat.zero_max]
  refine ⟨?_,
    (Nat.add_le_add ((liftCs1_queries _ _ _).trans_le hChkD.le) ((a1sDelegateCoreArm_queries_eq F .v3 core _).trans_le hcD)).trans (by omega),
    (Nat.add_le_add ((liftCs1_queries _ _ _).trans_le hChkSg.le) ((a1sDelegateCoreArm_queries_eq F .v3 core _).trans_le hcSg)).trans (by omega),
    (Nat.add_le_add ((liftCs1_queries _ _ _).trans_le hChkP) ((a1sDelegateCoreArm_queries_eq F .v3 core _).trans_le hcP)).trans (by omega), ?_⟩
  · simp only [a1sSimAtomicE, a1sSigBAtomicE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.cost] at *; omega
  · simp only [a1sSimAtomicE, a1sSigBAtomicE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.size] at *; omega
local macro "arm_fin" : tactic => `(tactic| (
  try simp only [a1g2Kind0ArmCostBound, a1s2Kind0ArmCostBound, authKind0ArmSizeBound,
    a1sSimAtomicE, a1sSigBAtomicE, Expr.v0, Expr.v1, Expr.cost, Expr.size] at *
  omega))
private theorem a1g_initPrin (F : AuthKindFuels) : ArmBnd (a1gArm_initPrin F) (1200 + 35 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1gWrap_bnd F _ (fgCore_initPrin_bnd F _ _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1g_corrupt (F : AuthKindFuels) : ArmBnd (a1gArm_corrupt F) (1400 + 105 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1gWrap_bnd F _ (fgCore_corrupt_bnd F _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1g_genSPK (F : AuthKindFuels) : ArmBnd (a1gArm_genSPK F) (14700 + 105 * F.K_on) (5 * F.K_ro) 2 4 (42 * bits F.K_on + 15000) := by
  refine a1gWrap_bnd F _ (fgCore_genSPK_bnd F _ _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1g_genOPK (F : AuthKindFuels) : ArmBnd (a1gArm_genOPK F) (1400 + 55 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1gWrap_bnd F _ (fgCore_genOPK_bnd F _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1g_revealDh (F : AuthKindFuels) : ArmBnd (a1gArm_revealDh F) (200 + 5 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1gWrap_bnd (qTy := .unit) F _ (fgCore_revealDh_bnd _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1g_registerKey (F : AuthKindFuels) : ArmBnd (a1gArm_registerKey F) (1200 + 5 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1gWrap_bnd F _ (fgCore_registerKey_bnd _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1g_send (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    ArmBnd (a1gArm_send S F opk) (a1g2Kind0ArmCostBound S F) (5 * F.K_ro) 2 (174 + 30 * min F.K_on S.N_dh) (authKind0ArmSizeBound S F) := by
  refine a1gWrap_bnd F _ (fgCore_send_bnd S F opk _ _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1g_recv (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    ArmBnd (a1gArm_recv S F opk) (a1g2Kind0ArmCostBound S F) (5 * F.K_ro) 2 (174 + 30 * min F.K_on S.N_dh) (authKind0ArmSizeBound S F) := by
  refine a1gWrap_bnd F _ (fgCore_recv_bnd S F opk _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1s_initPrin (F : AuthKindFuels) : ArmBnd (a1sArm_initPrin F) (1300 + 35 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  have hPaC := a1sCaseAPa2AtomicE_cost_le (Γ := [.nat, a1s2ShadowStTy, authQueryAtomicTy]) (.fst .v1)
  have hPaS := a1sCaseAPa2AtomicE_size_le (Γ := [.nat, a1s2ShadowStTy, authQueryAtomicTy]) (.fst .v1)
  change ArmBnd (a1sWrapNonSendArm F .v1 (fgCoreArm_initPrin F (a1sCaseAPa2AtomicE (.fst .v1)) (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)) _ _ _ _ _
  generalize a1sCaseAPa2AtomicE (.fst .v1) = pa at hPaC hPaS ⊢
  refine a1sWrap_bnd F _ (fgCore_initPrin_bnd F pa _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1s_corrupt (F : AuthKindFuels) : ArmBnd (a1sArm_corrupt F) (1500 + 105 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1sWrap_bnd F _ (fgCore_corrupt_bnd F _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1s_genSPK (F : AuthKindFuels) : ArmBnd (a1sArm_genSPK F) (14800 + 105 * F.K_on) (5 * F.K_ro) 2 4 (42 * bits F.K_on + 15000) := by
  have hPaC := a1sCaseAPa2AtomicE_cost_le (Γ := [.prod .nat .nat, a1s2ShadowStTy, authQueryAtomicTy]) (.fst .v1)
  have hPaS := a1sCaseAPa2AtomicE_size_le (Γ := [.prod .nat .nat, a1s2ShadowStTy, authQueryAtomicTy]) (.fst .v1)
  change ArmBnd (a1sWrapNonSendArm F .v1 (fgCoreArm_genSPK F (a1sCaseAPa2AtomicE (.fst .v1)) (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)) _ _ _ _ _
  generalize a1sCaseAPa2AtomicE (.fst .v1) = pa at hPaC hPaS ⊢
  refine a1sWrap_bnd F _ (fgCore_genSPK_bnd F pa _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1s_genOPK (F : AuthKindFuels) : ArmBnd (a1sArm_genOPK F) (1500 + 55 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1sWrap_bnd F _ (fgCore_genOPK_bnd F _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1s_revealDh (F : AuthKindFuels) : ArmBnd (a1sArm_revealDh F) (250 + 5 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1sWrap_bnd (qTy := .unit) F _ (fgCore_revealDh_bnd _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1s_registerKey (F : AuthKindFuels) : ArmBnd (a1sArm_registerKey F) (1300 + 5 * F.K_on) (5 * F.K_ro) 2 4 (22 * bits F.K_on + 15000) := by
  refine a1sWrap_bnd F _ (fgCore_registerKey_bnd _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin
private theorem a1s_recv (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    ArmBnd (a1sArm_recv S F opk) (a1s2Kind0ArmCostBound S F) (5 * F.K_ro) 2 (176 + 32 * min F.K_on S.N_dh) (authKind0ArmSizeBound S F) := by
  refine a1sWrap_bnd F _ (fgCore_recv_bnd S F opk _ _ _ _) ?_ ?_ ?_ ?_ ?_ <;> arm_fin

theorem a1gArm_initPrin_cost_le (S : Setup) (F : AuthKindFuels) : (a1gArm_initPrin F).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_initPrin F).1.trans (by dsimp [a1g2Kind0ArmCostBound]; omega)
theorem a1gArm_initPrin_ddh_le (F : AuthKindFuels) : (a1gArm_initPrin F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_initPrin F).2.1
theorem a1gArm_initPrin_sig_le (F : AuthKindFuels) : (a1gArm_initPrin F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_initPrin F).2.2.1
theorem a1gArm_initPrin_prim_le (S : Setup) (F : AuthKindFuels) : (a1gArm_initPrin F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_initPrin F).2.2.2.1.trans (by omega)
theorem a1gArm_initPrin_size_sharp_le (F : AuthKindFuels) : (a1gArm_initPrin F).size ≤ 22 * bits F.K_on + 15000 := (a1g_initPrin F).2.2.2.2
theorem a1gArm_initPrin_size_le (S : Setup) (F : AuthKindFuels) : (a1gArm_initPrin F).size ≤ authKind0ArmSizeBound S F := (a1g_initPrin F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1gArm_corrupt_cost_le (S : Setup) (F : AuthKindFuels) : (a1gArm_corrupt F).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_corrupt F).1.trans (by dsimp [a1g2Kind0ArmCostBound]; omega)
theorem a1gArm_corrupt_ddh_le (F : AuthKindFuels) : (a1gArm_corrupt F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_corrupt F).2.1
theorem a1gArm_corrupt_sig_le (F : AuthKindFuels) : (a1gArm_corrupt F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_corrupt F).2.2.1
theorem a1gArm_corrupt_prim_le (S : Setup) (F : AuthKindFuels) : (a1gArm_corrupt F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_corrupt F).2.2.2.1.trans (by omega)
theorem a1gArm_corrupt_size_sharp_le (F : AuthKindFuels) : (a1gArm_corrupt F).size ≤ 22 * bits F.K_on + 15000 := (a1g_corrupt F).2.2.2.2
theorem a1gArm_corrupt_size_le (S : Setup) (F : AuthKindFuels) : (a1gArm_corrupt F).size ≤ authKind0ArmSizeBound S F := (a1g_corrupt F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1gArm_genSPK_cost_le (S : Setup) (F : AuthKindFuels) : (a1gArm_genSPK F).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_genSPK F).1.trans (by dsimp [a1g2Kind0ArmCostBound]; omega)
theorem a1gArm_genSPK_ddh_le (F : AuthKindFuels) : (a1gArm_genSPK F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_genSPK F).2.1
theorem a1gArm_genSPK_sig_le (F : AuthKindFuels) : (a1gArm_genSPK F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_genSPK F).2.2.1
theorem a1gArm_genSPK_prim_le (S : Setup) (F : AuthKindFuels) : (a1gArm_genSPK F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_genSPK F).2.2.2.1.trans (by omega)
theorem a1gArm_genSPK_size_sharp_le (F : AuthKindFuels) : (a1gArm_genSPK F).size ≤ 42 * bits F.K_on + 15000 := (a1g_genSPK F).2.2.2.2
theorem a1gArm_genSPK_size_le (S : Setup) (F : AuthKindFuels) : (a1gArm_genSPK F).size ≤ authKind0ArmSizeBound S F := (a1g_genSPK F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1gArm_genOPK_cost_le (S : Setup) (F : AuthKindFuels) : (a1gArm_genOPK F).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_genOPK F).1.trans (by dsimp [a1g2Kind0ArmCostBound]; omega)
theorem a1gArm_genOPK_ddh_le (F : AuthKindFuels) : (a1gArm_genOPK F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_genOPK F).2.1
theorem a1gArm_genOPK_sig_le (F : AuthKindFuels) : (a1gArm_genOPK F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_genOPK F).2.2.1
theorem a1gArm_genOPK_prim_le (S : Setup) (F : AuthKindFuels) : (a1gArm_genOPK F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_genOPK F).2.2.2.1.trans (by omega)
theorem a1gArm_genOPK_size_sharp_le (F : AuthKindFuels) : (a1gArm_genOPK F).size ≤ 22 * bits F.K_on + 15000 := (a1g_genOPK F).2.2.2.2
theorem a1gArm_genOPK_size_le (S : Setup) (F : AuthKindFuels) : (a1gArm_genOPK F).size ≤ authKind0ArmSizeBound S F := (a1g_genOPK F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1gArm_send_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_send S F opk).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_send S F opk).1
theorem a1gArm_send_ddh_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_send S F opk).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_send S F opk).2.1
theorem a1gArm_send_sig_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_send S F opk).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_send S F opk).2.2.1
theorem a1gArm_send_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_send S F opk).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_send S F opk).2.2.2.1
theorem a1gArm_send_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_send S F opk).size ≤ authKind0ArmSizeBound S F := (a1g_send S F opk).2.2.2.2
theorem a1gArm_recv_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_recv S F opk).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_recv S F opk).1
theorem a1gArm_recv_ddh_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_recv S F opk).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_recv S F opk).2.1
theorem a1gArm_recv_sig_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_recv S F opk).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_recv S F opk).2.2.1
theorem a1gArm_recv_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_recv S F opk).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_recv S F opk).2.2.2.1
theorem a1gArm_recv_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1gArm_recv S F opk).size ≤ authKind0ArmSizeBound S F := (a1g_recv S F opk).2.2.2.2
theorem a1gArm_revealDh_cost_le (S : Setup) (F : AuthKindFuels) : (a1gArm_revealDh F).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_revealDh F).1.trans (by dsimp [a1g2Kind0ArmCostBound]; omega)
theorem a1gArm_revealDh_ddh_le (F : AuthKindFuels) : (a1gArm_revealDh F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_revealDh F).2.1
theorem a1gArm_revealDh_sig_le (F : AuthKindFuels) : (a1gArm_revealDh F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_revealDh F).2.2.1
theorem a1gArm_revealDh_prim_le (S : Setup) (F : AuthKindFuels) : (a1gArm_revealDh F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_revealDh F).2.2.2.1.trans (by omega)
theorem a1gArm_revealDh_size_sharp_le (F : AuthKindFuels) : (a1gArm_revealDh F).size ≤ 22 * bits F.K_on + 15000 := (a1g_revealDh F).2.2.2.2
theorem a1gArm_revealDh_size_le (S : Setup) (F : AuthKindFuels) : (a1gArm_revealDh F).size ≤ authKind0ArmSizeBound S F := (a1g_revealDh F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1gArm_registerKey_cost_le (S : Setup) (F : AuthKindFuels) : (a1gArm_registerKey F).cost ≤ a1g2Kind0ArmCostBound S F := (a1g_registerKey F).1.trans (by dsimp [a1g2Kind0ArmCostBound]; omega)
theorem a1gArm_registerKey_ddh_le (F : AuthKindFuels) : (a1gArm_registerKey F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1g_registerKey F).2.1
theorem a1gArm_registerKey_sig_le (F : AuthKindFuels) : (a1gArm_registerKey F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1g_registerKey F).2.2.1
theorem a1gArm_registerKey_prim_le (S : Setup) (F : AuthKindFuels) : (a1gArm_registerKey F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min F.K_on S.N_dh := (a1g_registerKey F).2.2.2.1.trans (by omega)
theorem a1gArm_registerKey_size_sharp_le (F : AuthKindFuels) : (a1gArm_registerKey F).size ≤ 22 * bits F.K_on + 15000 := (a1g_registerKey F).2.2.2.2
theorem a1gArm_registerKey_size_le (S : Setup) (F : AuthKindFuels) : (a1gArm_registerKey F).size ≤ authKind0ArmSizeBound S F := (a1g_registerKey F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)

theorem a1sArm_initPrin_cost_le (S : Setup) (F : AuthKindFuels) : (a1sArm_initPrin F).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_initPrin F).1.trans (by dsimp [a1s2Kind0ArmCostBound]; omega)
theorem a1sArm_initPrin_ddh_le (F : AuthKindFuels) : (a1sArm_initPrin F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_initPrin F).2.1
theorem a1sArm_initPrin_sig_le (F : AuthKindFuels) : (a1sArm_initPrin F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_initPrin F).2.2.1
theorem a1sArm_initPrin_prim_le (S : Setup) (F : AuthKindFuels) : (a1sArm_initPrin F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_initPrin F).2.2.2.1.trans (by omega)
theorem a1sArm_initPrin_size_sharp_le (F : AuthKindFuels) : (a1sArm_initPrin F).size ≤ 22 * bits F.K_on + 15000 := (a1s_initPrin F).2.2.2.2
theorem a1sArm_initPrin_size_le (S : Setup) (F : AuthKindFuels) : (a1sArm_initPrin F).size ≤ authKind0ArmSizeBound S F := (a1s_initPrin F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1sArm_corrupt_cost_le (S : Setup) (F : AuthKindFuels) : (a1sArm_corrupt F).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_corrupt F).1.trans (by dsimp [a1s2Kind0ArmCostBound]; omega)
theorem a1sArm_corrupt_ddh_le (F : AuthKindFuels) : (a1sArm_corrupt F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_corrupt F).2.1
theorem a1sArm_corrupt_sig_le (F : AuthKindFuels) : (a1sArm_corrupt F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_corrupt F).2.2.1
theorem a1sArm_corrupt_prim_le (S : Setup) (F : AuthKindFuels) : (a1sArm_corrupt F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_corrupt F).2.2.2.1.trans (by omega)
theorem a1sArm_corrupt_size_sharp_le (F : AuthKindFuels) : (a1sArm_corrupt F).size ≤ 22 * bits F.K_on + 15000 := (a1s_corrupt F).2.2.2.2
theorem a1sArm_corrupt_size_le (S : Setup) (F : AuthKindFuels) : (a1sArm_corrupt F).size ≤ authKind0ArmSizeBound S F := (a1s_corrupt F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1sArm_genSPK_cost_le (S : Setup) (F : AuthKindFuels) : (a1sArm_genSPK F).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_genSPK F).1.trans (by dsimp [a1s2Kind0ArmCostBound]; omega)
theorem a1sArm_genSPK_ddh_le (F : AuthKindFuels) : (a1sArm_genSPK F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_genSPK F).2.1
theorem a1sArm_genSPK_sig_le (F : AuthKindFuels) : (a1sArm_genSPK F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_genSPK F).2.2.1
theorem a1sArm_genSPK_prim_le (S : Setup) (F : AuthKindFuels) : (a1sArm_genSPK F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_genSPK F).2.2.2.1.trans (by omega)
theorem a1sArm_genSPK_size_sharp_le (F : AuthKindFuels) : (a1sArm_genSPK F).size ≤ 42 * bits F.K_on + 15000 := (a1s_genSPK F).2.2.2.2
theorem a1sArm_genSPK_size_le (S : Setup) (F : AuthKindFuels) : (a1sArm_genSPK F).size ≤ authKind0ArmSizeBound S F := (a1s_genSPK F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1sArm_genOPK_cost_le (S : Setup) (F : AuthKindFuels) : (a1sArm_genOPK F).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_genOPK F).1.trans (by dsimp [a1s2Kind0ArmCostBound]; omega)
theorem a1sArm_genOPK_ddh_le (F : AuthKindFuels) : (a1sArm_genOPK F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_genOPK F).2.1
theorem a1sArm_genOPK_sig_le (F : AuthKindFuels) : (a1sArm_genOPK F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_genOPK F).2.2.1
theorem a1sArm_genOPK_prim_le (S : Setup) (F : AuthKindFuels) : (a1sArm_genOPK F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_genOPK F).2.2.2.1.trans (by omega)
theorem a1sArm_genOPK_size_sharp_le (F : AuthKindFuels) : (a1sArm_genOPK F).size ≤ 22 * bits F.K_on + 15000 := (a1s_genOPK F).2.2.2.2
theorem a1sArm_genOPK_size_le (S : Setup) (F : AuthKindFuels) : (a1sArm_genOPK F).size ≤ authKind0ArmSizeBound S F := (a1s_genOPK F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1sArm_send_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_send S F opk).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_send_bnd S F opk).1
theorem a1sArm_send_ddh_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_send S F opk).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_send_bnd S F opk).2.1
theorem a1sArm_send_sig_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_send S F opk).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_send_bnd S F opk).2.2.1
theorem a1sArm_send_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_send S F opk).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_send_bnd S F opk).2.2.2.1
theorem a1sArm_send_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_send S F opk).size ≤ authKind0ArmSizeBound S F := (a1s_send_bnd S F opk).2.2.2.2
theorem a1sArm_recv_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_recv S F opk).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_recv S F opk).1
theorem a1sArm_recv_ddh_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_recv S F opk).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_recv S F opk).2.1
theorem a1sArm_recv_sig_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_recv S F opk).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_recv S F opk).2.2.1
theorem a1sArm_recv_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_recv S F opk).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_recv S F opk).2.2.2.1
theorem a1sArm_recv_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) : (a1sArm_recv S F opk).size ≤ authKind0ArmSizeBound S F := (a1s_recv S F opk).2.2.2.2
theorem a1sArm_revealDh_cost_le (S : Setup) (F : AuthKindFuels) : (a1sArm_revealDh F).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_revealDh F).1.trans (by dsimp [a1s2Kind0ArmCostBound]; omega)
theorem a1sArm_revealDh_ddh_le (F : AuthKindFuels) : (a1sArm_revealDh F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_revealDh F).2.1
theorem a1sArm_revealDh_sig_le (F : AuthKindFuels) : (a1sArm_revealDh F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_revealDh F).2.2.1
theorem a1sArm_revealDh_prim_le (S : Setup) (F : AuthKindFuels) : (a1sArm_revealDh F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_revealDh F).2.2.2.1.trans (by omega)
theorem a1sArm_revealDh_size_sharp_le (F : AuthKindFuels) : (a1sArm_revealDh F).size ≤ 22 * bits F.K_on + 15000 := (a1s_revealDh F).2.2.2.2
theorem a1sArm_revealDh_size_le (S : Setup) (F : AuthKindFuels) : (a1sArm_revealDh F).size ≤ authKind0ArmSizeBound S F := (a1s_revealDh F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)
theorem a1sArm_registerKey_cost_le (S : Setup) (F : AuthKindFuels) : (a1sArm_registerKey F).cost ≤ a1s2Kind0ArmCostBound S F := (a1s_registerKey F).1.trans (by dsimp [a1s2Kind0ArmCostBound]; omega)
theorem a1sArm_registerKey_ddh_le (F : AuthKindFuels) : (a1sArm_registerKey F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * F.K_ro := (a1s_registerKey F).2.1
theorem a1sArm_registerKey_sig_le (F : AuthKindFuels) : (a1sArm_registerKey F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 := (a1s_registerKey F).2.2.1
theorem a1sArm_registerKey_prim_le (S : Setup) (F : AuthKindFuels) : (a1sArm_registerKey F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min F.K_on S.N_dh := (a1s_registerKey F).2.2.2.1.trans (by omega)
theorem a1sArm_registerKey_size_sharp_le (F : AuthKindFuels) : (a1sArm_registerKey F).size ≤ 22 * bits F.K_on + 15000 := (a1s_registerKey F).2.2.2.2
theorem a1sArm_registerKey_size_le (S : Setup) (F : AuthKindFuels) : (a1sArm_registerKey F).size ≤ authKind0ArmSizeBound S F := (a1s_registerKey F).2.2.2.2.trans (by dsimp [authKind0ArmSizeBound]; omega)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostOn
