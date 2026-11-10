/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStep
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq

/-!
# Shadow-Indexed `.roQuery` Simulation for `KeyInd` Gap-DH

Proves forgetful simulation and `GdhSimInv` preservation for `roRawFallbackShadowAtomicC` and
`roParsedShadowAtomicC`, and derives `sigKeyInd1KeyKindAtomicProg_hStep_roQuery` and
`fgKeyInd1KeyGapDhKindAtomicProg_hStep_roQuery`.
-/

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimRo
set_option autoImplicit false
public section

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Expr Comp Env Iface pqAtomicSig pqAtomicOps pqSigAndDdhIface pqKeyIndCodec drKeyT findML)
open _root_.SignalPqxdh (Bytes Setup QueryBudget KeyIndQuery F_X25519)
open _root_.SignalPqxdh.Costed (PB)
open _root_.SignalPqxdh.Security.FgGapDh (GdhSimSpec)
open _root_.SignalPqxdh.Security.FgGapDh1Key (liftGdhToSign)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface keyIndCodec B)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (PT Ext v letV bindV caseOptV caseSumV findMV
  keyIndStateTy keyIndRespTy keyIndQueryTy fgPosTy fgPatchEntryTy drKeyTy paramsTy params2Ty gdhState2Ty simTy
  fePos1 fePos2 fePos3 fePos4 feSs feMk feDk rNone rDrKey eFind eqB takeKB dropB lenB natEq litB isSomeE
  smBase smFgL smRaw smLog smPows smMk smUpd liftBase gPrim sDrKey96 qIsCanonical slice32 mkSecretPosC
  ddhEqC ddhEqOptC entryMatchesC fgPatchC roRawFallbackC roParsedC paU paV paUp paOpkMode pa2Mk wrapSim2 gdhHandle2
  s1Target s1Budget s1Forgery s1Pk s1Fg s1Mk s1Upd litB_eval takeKB_eval lenB_eval eqB_eval natEq_eval letV_eval
  Ext.refl_wk' Ext.step_wk' Env.get_zero' Env.get_succ' liftGdhToSigDdh renamePair)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (gPrim_eval slice32_eval)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (Ren liftRen pullEnv pullEnv_get pullEnv_succ
  pullEnv_liftRen pullEnv_twoVarRen renameExpr renameExpr_eval liftGdhComp liftGdhComp_eval liftGdhToSign_pure
  liftGdhToSign_bind renameComp renameComp_eval twoVarRen)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift (AtomicIface embedTy embedVal projVal projVal_embedVal
  embedVal_projVal embedCtx embedVar embedEnv exprRename exprRename_eval compRename compRename_eval mapExpr
  mapExpr_eval mapComp mapComp_eval tlGapDhKeyInd tlSigDdhKeyInd finKeyIndQToNatExpr finKeyIndQToNatExpr_eval
  swapHandlerVar liftKeyInd1Stage liftKeyIndHandle liftKeyIndHandle_eval)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (sig1KeyActiveStTy gdh1KeyActiveStateTy saTP
  saInner sig1KeyActivePreDispatchC sig1KeyActiveHandleC sigKeyInd1KeyActiveDslProg sigKeyInd1KeyActiveAtomicProg
  callGdhActiveHandle gdh1KeyActiveHandle fgKeyInd1KeyGapDhActiveDslProg fgKeyInd1KeyGapDhActiveAtomicProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (aop avlSearchB192C avlInsertAtPathC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec (avlInsertAtPathC_eval_congr)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine (TaggedEntry roEntriesOf
  ShadowRelB192 RoCacheRelB192 shadowScanMinIdx findML_take_eq_shadowScanMinIdx avlLookup_eq_none_of_miss_support)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (emptyVarRen atomicRNoneE
  dispatchKeyIndQ runAt2 runAt3 runAt4)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (keyIndSimPred
  keyIndSimBounds fixSent BaseOnlineLenInv bumpPred_keyIndSimPred_sum dispatchKeyIndQ_eval runAt2_eval runAt3_eval runAt4_eval)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (KeyIndKFuels keyIndKFuelsOfBudget
  seqFgEntryTy roPosPackTy sessScanMinPredC fgSessScanC fgSessScanPackC roParsedPrePos160C roParsedPrePos192C
  fgShadowAtomicTy simShadowAtomicTy forgetSimShadow forgetGdhShadow2 GdhAtomicLift gdhLift2Key gdhLift1Key
  liftGdhAtomic ren1 wkSndVar runAt1 sampleDrKey96LiftC roNotPrefixE roLenEqE seqFgEntryDkE roHitRespSimE rawMissRespSimE
  parsedMissRespSimE roRawFallbackShadowAtomicC roParsedPostPosShadowAtomicC roParsedShadowAtomicC liftKind1RoArm gdhShadowHandle2Atomic)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (sig1KeyActiveKindStTy
  gdh1KeyActiveKindStateTy sigHasForgeryAtomicE sigGetFgAtomicE sigSetFgAtomicE sigKindRoArm gdhKindRoArm
  sig1KeyKindHandleC gdh1KeyKindHandleC sigKeyInd1KeyKindAtomicProg fgKeyInd1KeyGapDhKindAtomicProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (FgEntryA DrKeyA fgEntryDk
  RoFgEntryWf RoQueryPackWf GdhAtomicLiftValid gdhLift2Key_valid gdhLift1Key_valid fixParamsSent fixSig1KeyActiveSent
  forgetSig1KeyActiveK fixGdh1KeyActiveSent forgetGdh1KeyActiveK GdhSimInv Gdh2SimInv Sig1KeyActiveSimInv
  Gdh1KeyActiveSimInv KeyIndStepSim)

@[simp] private theorem runAt1_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A R : Ty pqAtomicSig} (aE : Expr pqAtomicOps Γ A) (c : Comp pqAtomicOps I [A] R) (env : Env Γ) :
    (runAt1 aE c).eval env = c.eval (.cons (aE.eval env) .nil) := by
  simp only [runAt1, Comp.eval, pure_bind]
  exact compRename_eval c ren1 (.cons (aE.eval env) .nil) (.cons (aE.eval env) env)
    (fun {a} x => by cases x with | zero => rfl | succ y => nomatch y)

private theorem sDrKey96_unsupported_zero {Γ : List PT} :
    (gPrim (sDrKey96 (Γ := Γ))).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := rfl
private theorem gPrim_sDrKey96_eval_const {Γ : List PT} (ρ : Env Γ) :
    (gPrim (sDrKey96 (Γ := Γ))).eval ρ = (gPrim (sDrKey96 (Γ := []))).eval .nil := by unfold gPrim; rw [gPrim_eval, gPrim_eval]; rfl

private theorem sampleDrKey96LiftC_eval {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) {Γ : List (Ty pqAtomicSig)} (env : Env Γ) :
    (sampleDrKey96LiftC gl).eval env = embedVal drKeyTy <$> evalGdh ((gPrim (sDrKey96 (Γ := []))).eval .nil) := by
  unfold sampleDrKey96LiftC; rw [compRename_eval _ emptyVarRen .nil env (fun {a} x => nomatch x)]
  exact hgl.liftGdhAtomic_eval (gPrim (sDrKey96 (Γ := []))) sDrKey96_unsupported_zero .nil

private theorem mkSecretPosC_unsupported_zero {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) :
    (mkSecretPosC z).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [mkSecretPosC, gPrim, liftBase, qIsCanonical, letV, bindV, Comp.queries, tlGapDhKeyInd,
    Computational.Proofs.SignalPqxdh.AtomicLift.keyIndUnsupportedPrimW]
private theorem roParsedPrePos160C_unsupported_zero {Γ Δ : List PT} [Ext Γ Δ] (sec : Var Γ (B 192)) :
    (roParsedPrePos160C (Δ := Δ) sec).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [roParsedPrePos160C, letV, bindV, Comp.queries, mkSecretPosC_unsupported_zero]
private theorem roParsedPrePos192C_unsupported_zero {Γ Δ : List PT} [Ext Γ Δ] (sec : Var Γ (B 192)) :
    (roParsedPrePos192C (Δ := Δ) sec).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [roParsedPrePos192C, letV, bindV, Comp.queries, mkSecretPosC_unsupported_zero]

private theorem mkSecretPosC_eval_slice32 {Γ : List PT} (off : ℕ) (bs : Expr pqxdhOps Γ (B 192)) (ρ : Env Γ) :
    (mkSecretPosC (slice32 off bs)).eval ρ = (mkSecretPosC (Γ := [B 192]) (slice32 off (.var .zero))).eval (.cons (bs.eval ρ) .nil) := by
  simp only [mkSecretPosC, letV, bindV, v, Comp.eval, Expr.eval, pure_bind, slice32_eval, Env.get_zero']
  unfold gPrim; rw [gPrim_eval, gPrim_eval]; rfl

private theorem mem_support_mkSecretPosC {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) (ρ : Env Γ)
    {p : fgPosTy.denote} (hp : p ∈ support ((mkSecretPosC z).eval ρ)) : ∃ c : Bool, p = .inl (z.eval ρ, c) := by
  simp only [mkSecretPosC, letV, bindV, v, Comp.eval, Expr.eval, pure_bind, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
  rcases hp with ⟨c, _, rfl⟩; exact ⟨c, rfl⟩

private theorem roParsedPrePos160C_support_wf (sec : Bytes) (hPre : sec.take 32 = F_X25519) (hLen : sec.length = 160)
    {pack : roPosPackTy.denote} (hMem : pack ∈ support ((roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero).eval (.cons sec .nil))) :
    RoQueryPackWf sec pack.1 pack.2.1 pack.2.2.1 pack.2.2.2.1 pack.2.2.2.2 := by
  simp only [roParsedPrePos160C, bindV, letV, v, Comp.eval, Expr.eval, pure_bind, Ext.refl_wk', Ext.step_wk',
    Env.get_zero', Env.get_succ', slice32_eval, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hMem
  rcases hMem with ⟨p1, hp1, p2, hp2, p3, hp3, rfl⟩
  obtain ⟨c1, hp1Eq⟩ := mem_support_mkSecretPosC _ _ hp1; obtain ⟨c2, hp2Eq⟩ := mem_support_mkSecretPosC _ _ hp2
  obtain ⟨c3, hp3Eq⟩ := mem_support_mkSecretPosC _ _ hp3
  simp only [slice32_eval, Expr.eval, Env.get_zero', Env.get_succ'] at hp1Eq hp2Eq hp3Eq
  exact ⟨hPre, Or.inl ⟨hLen, ⟨c1, c2, c3, hp1Eq, hp2Eq, hp3Eq⟩, rfl, rfl⟩⟩

private theorem roParsedPrePos192C_support_wf (sec : Bytes) (hPre : sec.take 32 = F_X25519) (hLen : sec.length = 192)
    {pack : roPosPackTy.denote} (hMem : pack ∈ support ((roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero).eval (.cons sec .nil))) :
    RoQueryPackWf sec pack.1 pack.2.1 pack.2.2.1 pack.2.2.2.1 pack.2.2.2.2 := by
  simp only [roParsedPrePos192C, bindV, letV, v, Comp.eval, Expr.eval, pure_bind, Ext.refl_wk', Ext.step_wk',
    Env.get_zero', Env.get_succ', slice32_eval, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hMem
  rcases hMem with ⟨p1, hp1, p2, hp2, p3, hp3, p4, hp4, rfl⟩
  obtain ⟨c1, hp1Eq⟩ := mem_support_mkSecretPosC _ _ hp1; obtain ⟨c2, hp2Eq⟩ := mem_support_mkSecretPosC _ _ hp2
  obtain ⟨c3, hp3Eq⟩ := mem_support_mkSecretPosC _ _ hp3; obtain ⟨c4, hp4Eq⟩ := mem_support_mkSecretPosC _ _ hp4
  simp only [slice32_eval, Expr.eval, Env.get_zero', Env.get_succ'] at hp1Eq hp2Eq hp3Eq hp4Eq
  exact ⟨hPre, Or.inr ⟨hLen, ⟨c1, c2, c3, c4, hp1Eq, hp2Eq, hp3Eq, congrArg some hp4Eq⟩, rfl⟩⟩

@[simp] private theorem embedVal_drKeyTy (x : drKeyTy.denote) : embedVal drKeyTy x = x := by rcases x with ⟨_, _, _⟩; rfl
@[simp] private theorem projVal_drKeyTy (x : DrKeyA) : projVal drKeyTy x = x := by rcases x with ⟨_, _, _⟩; rfl
@[simp] private theorem embedVal_rawList_eq (l : List (Bytes × DrKeyA)) :
    embedVal (.list (.prod (B 192) drKeyTy)) l = l := by
  induction l with | nil => rfl | cons hd _ _ => rcases hd with ⟨_, _⟩; simp [embedVal]
@[simp] private theorem embedVal_logList_eq (l : List Bytes) : embedVal (.list (B 192)) l = l := by
  induction l with | nil => rfl | cons _ _ _ => simp [embedVal]

private theorem embedVal_simTy_upd (sA : (embedTy simTy).denote) (fgL : List fgPatchEntryTy.denote)
    (rawL : List ((B 192).denote × drKeyTy.denote)) (logL : List (B 192).denote) :
    embedVal simTy ((projVal simTy sA).1, (fgL, (rawL, (logL, (projVal simTy sA).2.2.2.2)))) =
      (sA.1, (embedVal (.list fgPatchEntryTy) fgL, (rawL, (logL, sA.2.2.2.2)))) := by
  have h := embedVal_projVal simTy sA
  have h1 : embedVal keyIndStateTy (projVal simTy sA).1 = sA.1 := congrArg Prod.fst h
  have h5 : embedVal (.list (.prod (B 32) (B 32))) (projVal simTy sA).2.2.2.2 = sA.2.2.2.2 :=
    congrArg (fun x => x.2.2.2.2) h
  change (embedVal keyIndStateTy _, (embedVal (.list fgPatchEntryTy) fgL,
    (embedVal (.list (.prod (B 192) drKeyTy)) rawL, (embedVal (.list (B 192)) logL,
      embedVal (.list (.prod (B 32) (B 32))) _)))) = _
  rw [h1, h5, embedVal_rawList_eq, embedVal_logList_eq]

private abbrev rDrKeyVal (dk : DrKeyA) : keyIndRespTy.denote :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk))))))))
private theorem bump_roQuery_zero (S : Setup) (c : Fin 3 → ℕ) (sec : Bytes) :
    bumpPred (keyIndSimPred S) c (.roQuery sec) 0 = c 0 := by simp [bumpPred, keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery]
private theorem bump_roQuery_one (S : Setup) (c : Fin 3 → ℕ) (sec : Bytes) :
    bumpPred (keyIndSimPred S) c (.roQuery sec) 1 = c 1 + 1 := by simp [bumpPred, keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery]

private theorem baseOnlineLenInv_bump_roQuery {S : Setup} {c : Fin 3 → ℕ} {sec : Bytes}
    {st : keyIndStateTy.denote} (h : BaseOnlineLenInv c st) :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c (.roQuery sec)) st := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, bumpPred_keyIndSimPred_sum (S := S) (.roQuery sec) h.counts_eq⟩ <;>
    rw [bump_roQuery_zero]
  exacts [h.prin_le, h.spks_le, h.opks_le, h.sess_le, h.resps_le, h.usedO_le, h.usedN_le, h.kyb_le, h.adv_le]

private theorem roHitRespSimE_eval (dk : DrKeyA) (smA : (embedTy simTy).denote) (sec : Bytes) :
    (mapExpr roHitRespSimE).eval (.cons dk (.cons smA (.cons sec .nil))) =
      (embedVal keyIndRespTy (rDrKeyVal dk), (smA.1, (smA.2.1, (smA.2.2.1, (sec :: smA.2.2.2.1, smA.2.2.2.2))))) := by
  have hEnv : (.cons dk (.cons smA (.cons sec .nil)) : Env [embedTy drKeyTy, embedTy simTy, PB 192]) =
      embedEnv (Γ := [drKeyTy, simTy, B 192]) (.cons dk (.cons (projVal simTy smA) (.cons sec .nil))) := by
    simp only [embedEnv, embedVal_projVal, embedVal_drKeyTy]; rfl
  rw [hEnv, mapExpr_eval]; have hSm := embedVal_projVal simTy smA; rcases smA with ⟨bA, fgLA, rawLA, logLA, powsA⟩
  have hb : embedVal keyIndStateTy (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).1 = bA := congrArg Prod.fst hSm
  have hfg : embedVal (.list fgPatchEntryTy) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.1 = fgLA := congrArg (fun x => x.2.1) hSm
  have hraw : embedVal (.list (.prod (B 192) drKeyTy)) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.1 = rawLA := congrArg (fun x => x.2.2.1) hSm
  have hlog : embedVal (.list (B 192)) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.2.1 = logLA := congrArg (fun x => x.2.2.2.1) hSm
  have hpows : embedVal (.list (.prod (B 32) (B 32))) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.2.2 = powsA := congrArg (fun x => x.2.2.2.2) hSm
  simp only [roHitRespSimE, smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
  change (embedVal keyIndRespTy (rDrKeyVal dk), (embedVal keyIndStateTy _, (embedVal (.list fgPatchEntryTy) _,
    (embedVal (.list (.prod (B 192) drKeyTy)) _, (embedVal (B 192) sec :: embedVal (.list (B 192)) _,
      embedVal (.list (.prod (B 32) (B 32))) _))))) = _
  rw [hb, hfg, hraw, hlog, hpows]; rfl

private theorem rawMissRespSimE_eval (dk : DrKeyA) (smA : (embedTy simTy).denote) (sec : Bytes) :
    (mapExpr rawMissRespSimE).eval (.cons dk (.cons smA (.cons sec .nil))) =
      (embedVal keyIndRespTy (rDrKeyVal dk), (smA.1, (smA.2.1, ((sec, dk) :: smA.2.2.1, (sec :: smA.2.2.2.1, smA.2.2.2.2))))) := by
  have hEnv : (.cons dk (.cons smA (.cons sec .nil)) : Env [embedTy drKeyTy, embedTy simTy, PB 192]) =
      embedEnv (Γ := [drKeyTy, simTy, B 192]) (.cons dk (.cons (projVal simTy smA) (.cons sec .nil))) := by
    simp only [embedEnv, embedVal_projVal, embedVal_drKeyTy]; rfl
  rw [hEnv, mapExpr_eval]; have hSm := embedVal_projVal simTy smA; rcases smA with ⟨bA, fgLA, rawLA, logLA, powsA⟩
  have hb : embedVal keyIndStateTy (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).1 = bA := congrArg Prod.fst hSm
  have hfg : embedVal (.list fgPatchEntryTy) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.1 = fgLA := congrArg (fun x => x.2.1) hSm
  have hraw : embedVal (.list (.prod (B 192) drKeyTy)) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.1 = rawLA := congrArg (fun x => x.2.2.1) hSm
  have hlog : embedVal (.list (B 192)) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.2.1 = logLA := congrArg (fun x => x.2.2.2.1) hSm
  have hpows : embedVal (.list (.prod (B 32) (B 32))) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.2.2 = powsA := congrArg (fun x => x.2.2.2.2) hSm
  simp only [rawMissRespSimE, smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
  change (embedVal keyIndRespTy (rDrKeyVal dk), (embedVal keyIndStateTy _, (embedVal (.list fgPatchEntryTy) _,
    ((embedVal (B 192) sec, embedVal drKeyTy dk) :: embedVal (.list (.prod (B 192) drKeyTy)) _,
      (embedVal (B 192) sec :: embedVal (.list (B 192)) _, embedVal (.list (.prod (B 32) (B 32))) _))))) = _
  rw [hb, hfg, hraw, hlog, hpows]; simp [embedVal]

/-- Forgetful simulation and `GdhSimInv` preservation for `roRawFallbackShadowAtomicC`. -/
theorem roRawFallbackShadowAtomicC_sim {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ) (sK : simShadowAtomicTy.denote) (sec : Bytes)
    (hRoom : ∀ j, keyIndSimPred S j (.roQuery sec) → c j + 1 ≤ keyIndSimBounds b j) (hInv : GdhSimInv S b c sK) :
    Prod.map id forgetSimShadow <$> (roRawFallbackShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil)) =
      embedVal (.prod keyIndRespTy simTy) <$> evalGdh ((roRawFallbackC b.q_total (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192])
        (Δ := [simTy, B 192]) .zero (.succ .zero)).eval (.cons (projVal simTy sK.1) (.cons sec .nil))) ∧
    ∀ out ∈ support ((roRawFallbackShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil))),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c (.roQuery sec)) out.2 := by
  set f := keyIndKFuelsOfBudget S b; set env0 : Env [simShadowAtomicTy, PB 192] := .cons sK (.cons sec .nil)
  obtain ⟨path, hSearch, hIns⟩ := RoCacheRelB192.search_and_insert_spec (I := A.toIface) (V := drKeyT (ℓ := 0) (Pt := Empty))
    (listCap := b.q_total) (avlCap := f.kAvl) (l := sK.1.2.2.1) (.snd (.snd (.snd (.snd .v0)))) (aop (.pbytesToBytes 192) .v1) env0 sec rfl hInv.raw_shadow
  have hFindEq : ((sK.1.2.2.1.take b.q_total).find? (fun p => p.1 == sec)).map Prod.snd =
      (sK.1.2.2.1.find? (fun p => p.1 == sec)).map Prod.snd := hInv.raw_shadow.1.find?_take_map_snd sec
  have hRawProj : (projVal simTy sK.1).2.2.1 = sK.1.2.2.1 := by simp [projVal]
  have hfg : embedVal (.list fgPatchEntryTy) (projVal simTy sK.1).2.1 = sK.1.2.1 := congrArg (fun x => x.2.1) (embedVal_projVal simTy sK.1)
  have hlog : (projVal simTy sK.1).2.2.2.1 = sK.1.2.2.2.1 := by
    have h := congrArg (fun x => x.2.2.2.1) (embedVal_projVal simTy sK.1)
    change embedVal (.list (B 192)) (projVal simTy sK.1).2.2.2.1 = sK.1.2.2.2.1 at h; rwa [embedVal_logList_eq] at h
  have hFindLeg : ((eFind b.q_total (smRaw (v (.zero : Var [simTy, B 192] simTy)))
      fun p => eqB (.fst (v p)) (v (.succ .zero : Var [simTy, B 192] (B 192)))).eval
      ((.cons (projVal simTy sK.1) (.cons sec .nil)) : Env [simTy, B 192])) =
      (sK.1.2.2.1.take b.q_total).find? (fun p => p.1 == sec) := by
    simp [eFind, smRaw, eqB_eval, v, Expr.eval, Env.get_zero', Env.get_succ', hRawProj]
  unfold roRawFallbackShadowAtomicC; simp only [Comp.eval, hSearch, pure_bind]
  cases hTake : (sK.1.2.2.1.take b.q_total).find? (fun p => p.1 == sec) with
  | none =>
    have hMiss : (sK.1.2.2.1.find? (fun p => p.1 == sec)).map Prod.snd = none := by rw [← hFindEq, hTake]; rfl
    simp only [Expr.eval, Expr.v0, Env.get, hMiss]
    have hSample := sampleDrKey96LiftC_eval hgl (Env.cons (t := .prod (.opt (embedTy drKeyTy)) (.list (.prod .nat .bool))) (none, path) env0)
    have hDrId : embedVal drKeyTy = id := funext embedVal_drKeyTy; rw [hDrId, id_map] at hSample; rw [hSample]
    have hInsStep (dk : (embedTy drKeyTy).denote) :
        ∃ tbl', (avlInsertAtPathC (I := A.toIface) f.kAvl (.snd (.snd (.snd (.snd .v2)))) (.snd .v1)
            (aop (.pbytesToBytes 192) .v3) (.var .zero)).eval
            (Env.cons (t := embedTy drKeyTy) dk (Env.cons (t := .prod (.opt (embedTy drKeyTy)) (.list (.prod .nat .bool))) (none, path) env0)) =
          pure tbl' ∧ RoCacheRelB192 (embedTy drKeyTy) b.q_total f.kAvl ((sec, dk) :: sK.1.2.2.1) tbl' := by
      obtain ⟨tbl', hInsEval, hRel'⟩ := hIns hMiss (hInv.smRaw_add_one_le_q_total hRoom) (hInv.smRaw_add_one_le_kAvl hRoom) dk
      exact ⟨tbl', by rw [avlInsertAtPathC_eval_congr]; exact hInsEval, hRel'⟩
    have hLeg : (roRawFallbackC b.q_total (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192]) (Δ := [simTy, B 192])
        .zero (.succ .zero)).eval ((.cons (projVal simTy sK.1) (.cons sec .nil)) : Env [simTy, B 192]) =
        (gPrim (sDrKey96 (Γ := []))).eval .nil >>= fun dk =>
          pure (rDrKeyVal dk, ((projVal simTy sK.1).1, ((projVal simTy sK.1).2.1,
            ((sec, dk) :: sK.1.2.2.1, (sec :: (projVal simTy sK.1).2.2.2.1, (projVal simTy sK.1).2.2.2.2))))) := by
      simp only [roRawFallbackC, caseOptV, bindV, Comp.eval, hFindLeg, hTake]; rw [gPrim_sDrKey96_eval_const]; congr 1; funext dk
      simp [rDrKey, rDrKeyVal, smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', hRawProj]
    refine ⟨?_, ?_⟩
    · rw [hLeg, hgl.evalGdh_bind, map_bind, map_bind]; congr 1; funext dk
      obtain ⟨tbl', hIns', _⟩ := hInsStep dk; rw [hIns', pure_bind, runAt3_eval]
      simp only [Comp.eval, Expr.eval, Expr.v1, Expr.v3, env0, Env.get, rawMissRespSimE_eval, pure_bind, map_pure, hgl.evalGdh_pure, forgetSimShadow, Prod.map, id]
      congr 1; change (_, _) = (embedVal keyIndRespTy (rDrKeyVal dk), embedVal simTy _); rw [embedVal_simTy_upd, hfg, hlog]
    · intro out hOut; simp only [support_bind, Set.mem_iUnion, exists_prop] at hOut
      rcases hOut with ⟨dk, _, hOut2⟩; obtain ⟨tbl', hIns', hRel'⟩ := hInsStep dk; rw [hIns'] at hOut2
      simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, runAt3_eval, Comp.eval, Expr.eval, Expr.v1, Expr.v3, env0, Env.get, rawMissRespSimE_eval] at hOut2
      subst hOut2; obtain ⟨tagged, hFgRel, hFgWf, hFgRoLe⟩ := hInv.fg_shadow
      exact ⟨baseOnlineLenInv_bump_roQuery hInv.online_len, by rw [bump_roQuery_zero]; exact hInv.fg_sess_le,
        ⟨tagged, hFgRel, hFgWf, by rw [bump_roQuery_one]; omega⟩,
        by dsimp only; simp only [List.length_cons, bump_roQuery_one]; have := hInv.raw_len; omega, hRel',
        by dsimp only; simp only [List.length_cons, bump_roQuery_one]; have := hInv.log_len; omega,
        by rw [bump_roQuery_zero]; exact hInv.pows_len⟩
  | some kd =>
    rcases kd with ⟨kFound, dk⟩
    have hHit : (sK.1.2.2.1.find? (fun p => p.1 == sec)).map Prod.snd = some dk := by rw [← hFindEq, hTake]; rfl
    simp only [Expr.eval, Expr.v0, Expr.v2, Expr.v3, env0, Env.get, hHit, runAt3_eval, Comp.eval, roHitRespSimE_eval, pure_bind]
    have hLeg : (roRawFallbackC b.q_total (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192]) (Δ := [simTy, B 192])
        .zero (.succ .zero)).eval ((.cons (projVal simTy sK.1) (.cons sec .nil)) : Env [simTy, B 192]) =
        pure (rDrKeyVal dk, ((projVal simTy sK.1).1, ((projVal simTy sK.1).2.1,
          (sK.1.2.2.1, (sec :: (projVal simTy sK.1).2.2.2.1, (projVal simTy sK.1).2.2.2.2))))) := by
      simp only [roRawFallbackC, caseOptV, Comp.eval, hFindLeg, hTake]
      simp [rDrKey, rDrKeyVal, smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', hRawProj]
    refine ⟨?_, ?_⟩
    · rw [hLeg, hgl.evalGdh_pure, map_pure, map_pure]; simp only [forgetSimShadow, Prod.map, id]; congr 1
      change (_, _) = (embedVal keyIndRespTy (rDrKeyVal dk), embedVal simTy _); rw [embedVal_simTy_upd, hfg, hlog]
    · intro out hOut; simp only [support_pure, Set.mem_singleton_iff] at hOut; subst hOut
      obtain ⟨tagged, hFgRel, hFgWf, hFgRoLe⟩ := hInv.fg_shadow
      exact ⟨baseOnlineLenInv_bump_roQuery hInv.online_len, by rw [bump_roQuery_zero]; exact hInv.fg_sess_le,
        ⟨tagged, hFgRel, hFgWf, by rw [bump_roQuery_one]; omega⟩,
        by dsimp only; rw [bump_roQuery_one]; have := hInv.raw_len; omega, hInv.raw_shadow,
        by dsimp only; simp only [List.length_cons, bump_roQuery_one]; have := hInv.log_len; omega,
        by rw [bump_roQuery_zero]; exact hInv.pows_len⟩

private theorem sessScanMinPredC_unsupported_zero {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (minIdx : Var Γ₀ .nat) (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (se : Var Δ seqFgEntryTy) :
    (sessScanMinPredC minIdx pos1 pos2 pos3 pos4? ss se).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [sessScanMinPredC, letV, Comp.queries,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.entryMatchesC_unsupported_zero]

private theorem fgSessScanPackC_unsupported_zero (kOn : ℕ) :
    (fgSessScanPackC kOn).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [fgSessScanPackC, fgSessScanC, letV, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV,
    Comp.queries, sessScanMinPredC_unsupported_zero]

private theorem findML_map_embed {ι : Type} {T : OracleSpec ι} {α β : Type}
    (f : α → β) (g : β → α) (hfg : ∀ b, f (g b) = b) (p : α → OracleComp T Bool) (L : List β) :
    Option.map f <$> findML p (L.map g) = findML (fun b => p (g b)) L := by
  induction L with
  | nil => simp [findML]
  | cons b bs ih => simp only [List.map_cons, findML, map_bind]; congr 1; funext c; cases c <;> [exact ih; simp [hfg b]]

private def roEntryPredGdh {ι : Type} {T : OracleSpec ι}
    (evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α)
    (pack : roPosPackTy.denote) (eA : FgEntryA) : OracleComp T Bool :=
  let (p1, (p2, (p3, (p4?, ss)))) := pack
  evalGdh ((entryMatchesC (Γ₁ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
    (Γ₂ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
    (Γ₃ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
    (Γ₄ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
    (Γ₅ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
    (Δ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
    (.succ .zero) (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))
    (.succ (.succ (.succ (.succ .zero)))) (.succ (.succ (.succ (.succ (.succ .zero))))) .zero).eval
    (.cons (projVal fgPatchEntryTy eA) (.cons p1 (.cons p2 (.cons p3 (.cons p4? (.cons ss .nil)))))))

private theorem ddhEqC_eval_eq {Γ Δ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy)
    (q1 q2 : Expr pqxdhOps Δ fgPosTy) (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (h1 : p1.eval ρ₁ = q1.eval ρ₂) (h2 : p2.eval ρ₁ = q2.eval ρ₂) :
    (ddhEqC p1 p2).eval ρ₁ = (ddhEqC q1 q2).eval ρ₂ := by
  simp only [ddhEqC, letV, caseSumV, v, Comp.eval, Expr.eval, pure_bind, Env.get, Ext.refl_wk', Ext.step_wk', h1, h2]
  cases q1.eval ρ₂ <;> cases q2.eval ρ₂ <;> rfl

private theorem ddhEqOptC_eval_eq {Γ Δ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy))
    (q1? q2? : Expr pqxdhOps Δ (.opt fgPosTy)) (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (h1 : p1?.eval ρ₁ = q1?.eval ρ₂) (h2 : p2?.eval ρ₁ = q2?.eval ρ₂) :
    (ddhEqOptC p1? p2?).eval ρ₁ = (ddhEqOptC q1? q2?).eval ρ₂ := by
  simp only [ddhEqOptC, letV, caseOptV, v, Comp.eval, Expr.eval, pure_bind, Env.get, Ext.refl_wk', Ext.step_wk', h1, h2]
  cases q1?.eval ρ₂ <;> cases q2?.eval ρ₂ <;> [rfl; rfl; rfl; exact ddhEqC_eval_eq _ _ _ _ _ _ rfl rfl]

private theorem entryMatchesC_eval_congr {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) (ρ : Env Δ) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).eval ρ =
      (entryMatchesC (Γ₁ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
        (Γ₂ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
        (Γ₃ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
        (Γ₄ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
        (Γ₅ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
        (Δ := [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32])
        (.succ .zero) (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))
        (.succ (.succ (.succ (.succ .zero)))) (.succ (.succ (.succ (.succ (.succ .zero))))) .zero).eval
        (.cons (ρ.get e) (.cons (ρ.get (Ext.wk pos1)) (.cons (ρ.get (Ext.wk pos2))
          (.cons (ρ.get (Ext.wk pos3)) (.cons (ρ.get (Ext.wk pos4?)) (.cons (ρ.get (Ext.wk ss)) .nil)))))) := by
  simp only [entryMatchesC, feSs, bindV, v, Comp.eval, Expr.eval, eqB_eval, Env.get, Ext.refl_wk', Ext.step_wk']
  split_ifs with hSs
  · rfl
  · set env6 : Env [fgPatchEntryTy, fgPosTy, fgPosTy, fgPosTy, .opt fgPosTy, B 32] :=
      .cons (ρ.get e) (.cons (ρ.get (Ext.wk pos1)) (.cons (ρ.get (Ext.wk pos2))
        (.cons (ρ.get (Ext.wk pos3)) (.cons (ρ.get (Ext.wk pos4?)) (.cons (ρ.get (Ext.wk ss)) .nil)))))
    rw [ddhEqC_eval_eq _ _ (.var (.succ .zero)) (fePos1 (.var .zero)) ρ env6 rfl rfl]; congr 1

private theorem roEntryPredGdh_ro_eq_beq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) {sec sec' : Bytes} {pack : roPosPackTy.denote} {eA : FgEntryA}
    (hQ : RoQueryPackWf sec pack.1 pack.2.1 pack.2.2.1 pack.2.2.2.1 pack.2.2.2.2)
    (hE : RoFgEntryWf sec' eA) : roEntryPredGdh evalGdh pack eA = pure (sec' == sec) := by
  rcases pack with ⟨p1, p2, p3, p4?, ss⟩; dsimp only [roEntryPredGdh]
  have hEmb := embedVal_projVal fgPatchEntryTy eA
  rw [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.entryMatchesC_ro_eval_eq_beq
    (.succ .zero) (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))
    (.succ (.succ (.succ (.succ .zero)))) (.succ (.succ (.succ (.succ (.succ .zero))))) .zero
    (.cons (projVal fgPatchEntryTy eA) (.cons p1 (.cons p2 (.cons p3 (.cons p4? (.cons ss .nil))))))
    sec sec' (by simpa [Env.get_zero', Env.get_succ', Ext.refl_wk'] using hQ) (by simpa [Env.get_zero', hEmb] using hE)]
  exact hgl.evalGdh_pure (sec' == sec)

private theorem fgSessScanPackC_eval_eq {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) (kOn minIdx : ℕ) (packA : (embedTy roPosPackTy).denote) (fgSessA : List (ℕ × FgEntryA)) :
    (liftGdhAtomic gl (fgSessScanPackC kOn)).eval (.cons minIdx (.cons packA (.cons fgSessA .nil))) =
      findML (fun ie => if decide (minIdx ≤ ie.1) then roEntryPredGdh evalGdh (projVal roPosPackTy packA) ie.2 else pure false) (fgSessA.take kOn) := by
  have hEnv : (.cons minIdx (.cons packA (.cons fgSessA .nil)) : Env [.nat, embedTy roPosPackTy, .list (embedTy seqFgEntryTy)]) =
      embedEnv (Γ := [.nat, roPosPackTy, .list seqFgEntryTy])
        (.cons minIdx (.cons (projVal roPosPackTy packA) (.cons (projVal (.list seqFgEntryTy) fgSessA) .nil))) := by
    simp only [embedEnv, embedVal_projVal]; rfl
  rw [hEnv, hgl.liftGdhAtomic_eval _ (fgSessScanPackC_unsupported_zero kOn)]
  set pack := projVal roPosPackTy packA; rcases pack with ⟨p1, p2, p3, p4?, ss⟩
  have hTakeMap : (projVal (.list seqFgEntryTy) fgSessA).take kOn =
      (fgSessA.take kOn).map (fun ie => (ie.1, projVal fgPatchEntryTy ie.2)) := by simp only [projVal, List.map_take]
  have hOpt : embedVal (.opt seqFgEntryTy) = Option.map (embedVal seqFgEntryTy) := by funext x; cases x <;> simp [embedVal]
  simp only [fgSessScanPackC, fgSessScanC, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV,
    letV, v, Comp.eval, Expr.eval, pure_bind, Env.get, Ext.refl_wk', Ext.step_wk', hTakeMap, hgl.evalGdh_findML, hOpt]
  rw [findML_map_embed (embedVal seqFgEntryTy) (fun ie => (ie.1, projVal fgPatchEntryTy ie.2))
    (fun ie => by rcases ie with ⟨i, e⟩; change (i, embedVal fgPatchEntryTy (projVal fgPatchEntryTy e)) = (i, e); rw [embedVal_projVal])]
  congr 1; funext ie; rcases ie with ⟨(idx : ℕ), eA⟩
  simp only [sessScanMinPredC, letV, v, Comp.eval, Expr.eval, pure_bind, Env.get, Ext.refl_wk', Ext.step_wk']
  by_cases hLt : idx < minIdx
  · simp [hLt, Nat.not_le.mpr hLt, hgl.evalGdh_pure]
  · simp only [hLt, ↓reduceIte, decide_eq_true (Nat.le_of_not_lt hLt)]; rw [entryMatchesC_eval_congr]; rfl

private theorem parsedMissRespSimE_eval (dk : DrKeyA) (packA : (embedTy roPosPackTy).denote)
    (smA : (embedTy simTy).denote) (sec : Bytes) :
    (mapExpr parsedMissRespSimE).eval (.cons dk (.cons packA (.cons smA (.cons sec .nil)))) =
      (embedVal keyIndRespTy (rDrKeyVal dk),
       (smA.1, ((packA.1, (packA.2.1, (packA.2.2.1, (packA.2.2.2.1, (packA.2.2.2.2, dk))))) :: smA.2.1,
        (smA.2.2.1, (sec :: smA.2.2.2.1, smA.2.2.2.2))))) := by
  have hEnv : (.cons dk (.cons packA (.cons smA (.cons sec .nil))) : Env [embedTy drKeyTy, embedTy roPosPackTy, embedTy simTy, PB 192]) =
      embedEnv (Γ := [drKeyTy, roPosPackTy, simTy, B 192])
        (.cons dk (.cons (projVal roPosPackTy packA) (.cons (projVal simTy smA) (.cons sec .nil)))) := by
    simp only [embedEnv, embedVal_projVal, embedVal_drKeyTy]; rfl
  rw [hEnv, mapExpr_eval]; have hSm := embedVal_projVal simTy smA; have hPk := embedVal_projVal roPosPackTy packA
  rcases smA with ⟨bA, fgLA, rawLA, logLA, powsA⟩; rcases packA with ⟨p1A, p2A, p3A, p4A, ssA⟩
  have hb : embedVal keyIndStateTy (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).1 = bA := congrArg Prod.fst hSm
  have hfg : embedVal (.list fgPatchEntryTy) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.1 = fgLA := congrArg (fun x => x.2.1) hSm
  have hraw : embedVal (.list (.prod (B 192) drKeyTy)) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.1 = rawLA := congrArg (fun x => x.2.2.1) hSm
  have hlog : embedVal (.list (B 192)) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.2.1 = logLA := congrArg (fun x => x.2.2.2.1) hSm
  have hpows : embedVal (.list (.prod (B 32) (B 32))) (projVal simTy (bA, fgLA, rawLA, logLA, powsA)).2.2.2.2 = powsA := congrArg (fun x => x.2.2.2.2) hSm
  have hp1 : embedVal fgPosTy (projVal roPosPackTy (p1A, p2A, p3A, p4A, ssA)).1 = p1A := congrArg Prod.fst hPk
  have hp2 : embedVal fgPosTy (projVal roPosPackTy (p1A, p2A, p3A, p4A, ssA)).2.1 = p2A := congrArg (fun x => x.2.1) hPk
  have hp3 : embedVal fgPosTy (projVal roPosPackTy (p1A, p2A, p3A, p4A, ssA)).2.2.1 = p3A := congrArg (fun x => x.2.2.1) hPk
  have hp4 : embedVal (.opt fgPosTy) (projVal roPosPackTy (p1A, p2A, p3A, p4A, ssA)).2.2.2.1 = p4A := congrArg (fun x => x.2.2.2.1) hPk
  have hss : embedVal (B 32) (projVal roPosPackTy (p1A, p2A, p3A, p4A, ssA)).2.2.2.2 = ssA := congrArg (fun x => x.2.2.2.2) hPk
  simp only [parsedMissRespSimE, feMk, smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
  change (embedVal keyIndRespTy (rDrKeyVal dk), (embedVal keyIndStateTy _,
    ((embedVal fgPosTy _, (embedVal fgPosTy _, (embedVal fgPosTy _, (embedVal (.opt fgPosTy) _,
      (embedVal (B 32) _, embedVal drKeyTy dk))))) :: embedVal (.list fgPatchEntryTy) _,
      (embedVal (.list (.prod (B 192) drKeyTy)) _, (embedVal (B 192) sec :: embedVal (.list (B 192)) _,
        embedVal (.list (.prod (B 32) (B 32))) _))))) = _
  rw [hb, hfg, hraw, hlog, hpows, hp1, hp2, hp3, hp4, hss]; rfl

private theorem seqFgEntryDkE_eval {Γ : List (Ty pqAtomicSig)} (seA : (embedTy seqFgEntryTy).denote) (env : Env Γ) :
    (exprRename ren1 (mapExpr seqFgEntryDkE)).eval (.cons seA env) = fgEntryDk seA.2 := by
  rw [exprRename_eval (mapExpr seqFgEntryDkE) ren1 (.cons seA .nil) (.cons seA env)
    (fun {a} x => by cases x with | zero => rfl | succ y => nomatch y)]
  have hEnv : (.cons seA .nil : Env [embedTy seqFgEntryTy]) = embedEnv (.cons (projVal seqFgEntryTy seA) .nil) := by simp [embedEnv]
  rw [hEnv, mapExpr_eval]; rcases seA with ⟨idx, p1A, p2A, p3A, p4A, ssA, dkA⟩
  simp [seqFgEntryDkE, feDk, fgEntryDk, v, Expr.eval, Env.get_zero', projVal, embedVal]

private theorem roFgEntryWf_of_pack {sec : Bytes} {pack : roPosPackTy.denote} (dk : DrKeyA)
    (hQ : RoQueryPackWf sec pack.1 pack.2.1 pack.2.2.1 pack.2.2.2.1 pack.2.2.2.2) :
    RoFgEntryWf sec ((embedVal roPosPackTy pack).1, ((embedVal roPosPackTy pack).2.1,
      ((embedVal roPosPackTy pack).2.2.1, ((embedVal roPosPackTy pack).2.2.2.1, ((embedVal roPosPackTy pack).2.2.2.2, dk))))) := by
  rcases pack with ⟨p1, p2, p3, p4?, ss⟩; rcases hQ with ⟨hPre, h160 | h192⟩
  · obtain ⟨hLen, ⟨c1, c2, c3, hp1, hp2, hp3⟩, hp4, hss⟩ := h160; dsimp only at hp1 hp2 hp3 hp4 hss
    subst hp1; subst hp2; subst hp3; subst hp4; subst hss; exact ⟨hPre, Or.inl ⟨hLen, ⟨c1, c2, c3, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
  · obtain ⟨hLen, ⟨c1, c2, c3, c4, hp1, hp2, hp3, hp4⟩, hss⟩ := h192; dsimp only at hp1 hp2 hp3 hp4 hss
    subst hp1; subst hp2; subst hp3; subst hp4; subst hss; exact ⟨hPre, Or.inr ⟨hLen, ⟨c1, c2, c3, c4, rfl, rfl, rfl, rfl⟩, rfl⟩⟩

private def roPostPosSem {ι : Type} {T : OracleSpec ι}
    (evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α)
    (K : ℕ) (pack : roPosPackTy.denote) (sA : (embedTy simTy).denote) (sec : Bytes) :
    OracleComp T ((embedTy keyIndRespTy).denote × (embedTy simTy).denote) :=
  (Option.map fgEntryDk <$> findML (roEntryPredGdh evalGdh pack) (sA.2.1.take K)) >>= fun hit? =>
  match hit? with
  | some dk => pure (embedVal keyIndRespTy (rDrKeyVal dk), (sA.1, (sA.2.1, (sA.2.2.1, (sec :: sA.2.2.2.1, sA.2.2.2.2)))))
  | none =>
      evalGdh ((gPrim (sDrKey96 (Γ := []))).eval .nil) >>= fun dk =>
      let packA := embedVal roPosPackTy pack
      pure (embedVal keyIndRespTy (rDrKeyVal dk), (sA.1,
        ((packA.1, (packA.2.1, (packA.2.2.1, (packA.2.2.2.1, (packA.2.2.2.2, dk))))) :: sA.2.1,
         (sA.2.2.1, (sec :: sA.2.2.2.1, sA.2.2.2.2)))))

private theorem roParsedPostPosShadowAtomicC_sim {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : simShadowAtomicTy.denote) (sec : Bytes) (pack : roPosPackTy.denote) (packA : (embedTy roPosPackTy).denote)
    (hPackEq : packA = embedVal roPosPackTy pack)
    (hQ : RoQueryPackWf sec pack.1 pack.2.1 pack.2.2.1 pack.2.2.2.1 pack.2.2.2.2)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j (.roQuery sec) → c j + 1 ≤ keyIndSimBounds b j) (hInv : GdhSimInv S b c sK) :
    Prod.map id forgetSimShadow <$> (roParsedPostPosShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval
        (.cons packA (.cons sK (.cons sec .nil))) = roPostPosSem evalGdh b.q_total pack sK.1 sec ∧
    ∀ out ∈ support ((roParsedPostPosShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons packA (.cons sK (.cons sec .nil)))),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c (.roQuery sec)) out.2 := by
  have hProjPack : projVal roPosPackTy packA = pack := hPackEq ▸ projVal_embedVal roPosPackTy pack
  set f := keyIndKFuelsOfBudget S b
  set env0 : Env [embedTy roPosPackTy, simShadowAtomicTy, PB 192] := .cons packA (.cons sK (.cons sec .nil))
  obtain ⟨tagged, hFgRel, hFgWf, hFgRoLe⟩ := hInv.fg_shadow
  obtain ⟨path, hSearch, hIns⟩ := ShadowRelB192.search_and_insert_spec (I := A.toIface) (V := drKeyT (ℓ := 0) (Pt := Empty))
    (listCap := b.q_total) (avlCap := f.kAvl) (valOf := fgEntryDk) (l := sK.1.2.1) (tagged := tagged) (sess := sK.2.1)
    (ctr := sK.2.2.1) (.fst (.snd (.snd (.snd .v1)))) (aop (.pbytesToBytes 192) .v2) env0 sec rfl hFgRel
  set avlHit := ((roEntriesOf fgEntryDk tagged).find? (fun p => p.1 == sec)).map Prod.snd
  have hScanEq : Option.map fgEntryDk <$> findML (roEntryPredGdh evalGdh pack) (sK.1.2.1.take b.q_total) =
      shadowScanMinIdx fgEntryDk (roEntryPredGdh evalGdh pack) avlHit (sK.2.1.take f.kOn) :=
    findML_take_eq_shadowScanMinIdx hFgRel.1 (hInv.fgSess_length_le_kOn hB) sec (roEntryPredGdh evalGdh pack)
      (fun te hMem sec' hTag => roEntryPredGdh_ro_eq_beq hgl hQ (hFgWf te hMem sec' hTag))
  let minIdx : ℕ := avlHit.elim 0 (fun p => p.2 + 1)
  have hMinIdx : ((.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1)) :
      Expr pqAtomicOps [.prod (.opt (.prod (embedTy drKeyTy) .nat)) (.list (.prod .nat .bool)),
        embedTy roPosPackTy, simShadowAtomicTy, PB 192] .nat).eval (.cons (avlHit, path) env0)) = minIdx := by
    rcases avlHit with _ | ⟨dk, idx_ro⟩ <;> rfl
  have hDrId : embedVal drKeyTy = id := funext embedVal_drKeyTy
  have hHitInv : ∀ dk, GdhSimInv S b (bumpPred (keyIndSimPred S) c (.roQuery sec))
      (((mapExpr roHitRespSimE).eval (.cons dk (.cons sK.1 (.cons sec .nil)))).2, sK.2) := by
    intro dk; rw [roHitRespSimE_eval]
    exact ⟨baseOnlineLenInv_bump_roQuery hInv.online_len, by rw [bump_roQuery_zero]; exact hInv.fg_sess_le,
      ⟨tagged, hFgRel, hFgWf, by rw [bump_roQuery_one]; omega⟩,
      by dsimp only; rw [bump_roQuery_one]; have := hInv.raw_len; omega, hInv.raw_shadow,
      by dsimp only; simp only [List.length_cons, bump_roQuery_one]; have := hInv.log_len; omega,
      by rw [bump_roQuery_zero]; exact hInv.pows_len⟩
  unfold roParsedPostPosShadowAtomicC
  simp only [Comp.eval, hSearch, pure_bind, runAt3_eval, hMinIdx]
  have hScanEnv :
      (Env.cons (t := .nat) minIdx
        (Env.cons (t := embedTy roPosPackTy)
          (Expr.eval (O := pqAtomicOps) Expr.v1
            (Env.cons (t := .prod (.opt (.prod (embedTy drKeyTy) .nat)) (.list (.prod .nat .bool)))
              (avlHit, path) env0))
          (Env.cons (t := .list (embedTy seqFgEntryTy))
            (Expr.eval (O := pqAtomicOps) (Expr.fst (Expr.snd Expr.v2))
              (Env.cons (t := .prod (.opt (.prod (embedTy drKeyTy) .nat)) (.list (.prod .nat .bool)))
                (avlHit, path) env0))
            Env.nil))) =
        .cons minIdx (.cons packA (.cons sK.2.1 .nil)) := by
    simp [Expr.eval, Expr.v1, Expr.v2, env0, Env.get]
  rw [hScanEnv, fgSessScanPackC_eval_eq hgl, hProjPack]
  have hAvlCap : (roEntriesOf fgEntryDk tagged).length + 1 ≤ f.kAvl := by
    have h1 := hRoom 1 (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
    dsimp only [keyIndSimBounds, f, keyIndKFuelsOfBudget] at h1 ⊢; omega
  cases hAvl : avlHit with
  | none =>
    rw [hAvl] at hScanEq; have hMin0 : minIdx = 0 := by simp [minIdx, hAvl]
    let newE (dk : (embedTy drKeyTy).denote) : FgEntryA := (packA.1, (packA.2.1, (packA.2.2.1, (packA.2.2.2.1, (packA.2.2.2.2, dk)))))
    have hInsStep (dk : (embedTy drKeyTy).denote) :
        ∃ tbl', (avlInsertAtPathC (I := A.toIface) f.kAvl
            (.fst (.snd (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero))))))))) (.snd .v2)
            (aop (.pbytesToBytes 192) (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
            (.pair (.var .zero) (.fst (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))).eval
            (Env.cons (t := embedTy drKeyTy) dk
              (Env.cons (t := .opt (embedTy seqFgEntryTy)) none
                (Env.cons (t := .prod (.opt (.prod (embedTy drKeyTy) .nat)) (.list (.prod .nat .bool)))
                  (none, path) env0))) = pure tbl' ∧
          ShadowRelB192 drKeyT b.q_total f.kAvl fgEntryDk
            (newE dk :: sK.1.2.1) (⟨sK.2.2.1, .ro sec, newE dk⟩ :: tagged) tbl' sK.2.1 (sK.2.2.1 + 1) := by
      obtain ⟨tbl', hInsEval, hRel'⟩ := hIns hAvl (hInv.ctr_add_one_le_q_total hRoom) hAvlCap (newE dk)
      exact ⟨tbl', by rw [avlInsertAtPathC_eval_congr]; exact hInsEval, hRel'⟩
    refine ⟨?_, ?_⟩
    · unfold roPostPosSem; rw [hScanEq]; unfold shadowScanMinIdx
      change (Prod.map id forgetSimShadow <$> (findML _ (sK.2.1.take f.kOn) >>= _)) = ((_ <$> findML _ (sK.2.1.take f.kOn)) >>= _)
      rw [map_bind, bind_map_left, hMin0]; congr 1; funext sHit; cases sHit with
      | some se => rcases se with ⟨idx, eA⟩; simp only [Expr.eval, Expr.v0, env0, Env.get, seqFgEntryDkE_eval, roHitRespSimE_eval, map_pure, forgetSimShadow, Prod.map, id]
      | none =>
        simp only [Expr.eval, Expr.v0, Expr.v1, env0, Env.get, Option.map]
        have hSample := sampleDrKey96LiftC_eval hgl
          (Env.cons (t := .opt (embedTy seqFgEntryTy)) none
            (Env.cons (t := .prod (.opt (.prod (embedTy drKeyTy) .nat)) (.list (.prod .nat .bool)))
              (none, path) env0))
        rw [hDrId, id_map] at hSample; rw [hSample, map_bind]; congr 1; funext dk
        obtain ⟨tbl', hIns', _⟩ := hInsStep dk; rw [hIns', pure_bind, runAt4_eval]
        simp only [Comp.eval, Expr.eval, Env.get, parsedMissRespSimE_eval, pure_bind, map_pure, forgetSimShadow, Prod.map, id]
        subst hPackEq; rfl
    · intro out hOut; simp only [support_bind, Set.mem_iUnion, exists_prop] at hOut; rcases hOut with ⟨sHit, _, hOutS⟩
      cases sHit with
      | some se =>
        rcases se with ⟨idx, eA⟩; simp only [Expr.eval, Expr.v0, env0, Env.get, seqFgEntryDkE_eval, support_pure, Set.mem_singleton_iff] at hOutS
        subst hOutS; exact hHitInv (fgEntryDk eA)
      | none =>
        simp only [Expr.eval, Expr.v0, Expr.v1, env0, Env.get, support_bind, Set.mem_iUnion, exists_prop] at hOutS
        rcases hOutS with ⟨dk, _, hOutDk⟩; obtain ⟨tbl', hIns', hRel'⟩ := hInsStep dk; rw [hIns'] at hOutDk
        simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, runAt4_eval, Comp.eval, Expr.eval, Env.get, parsedMissRespSimE_eval] at hOutDk
        subst hOutDk
        refine ⟨baseOnlineLenInv_bump_roQuery hInv.online_len, by dsimp only; rw [bump_roQuery_zero]; exact hInv.fg_sess_le,
          ⟨⟨sK.2.2.1, .ro sec, newE dk⟩ :: tagged, hRel', ?_, ?_⟩,
          by dsimp only; rw [bump_roQuery_one]; have := hInv.raw_len; omega, hInv.raw_shadow,
          by dsimp only; simp only [List.length_cons, bump_roQuery_one]; have := hInv.log_len; omega,
          by rw [bump_roQuery_zero]; exact hInv.pows_len⟩
        · intro te hMem sec' hTag; rcases List.mem_cons.mp hMem with rfl | hMemTl
          · injection hTag with hSecEq; subst hSecEq; subst hPackEq; exact roFgEntryWf_of_pack dk hQ
          · exact hFgWf te hMemTl sec' hTag
        · have hCons : (roEntriesOf fgEntryDk (⟨sK.2.2.1, .ro sec, newE dk⟩ :: tagged)).length = (roEntriesOf fgEntryDk tagged).length + 1 := rfl
          rw [hCons, bump_roQuery_one]; omega
  | some di =>
    rcases di with ⟨dk, idx_ro⟩; rw [hAvl] at hScanEq; have hMinS : minIdx = idx_ro + 1 := by simp [minIdx, hAvl]
    refine ⟨?_, ?_⟩
    · unfold roPostPosSem; rw [hScanEq]; unfold shadowScanMinIdx
      change (Prod.map id forgetSimShadow <$> (findML _ (sK.2.1.take f.kOn) >>= _)) = ((_ <$> findML _ (sK.2.1.take f.kOn)) >>= _)
      rw [map_bind, bind_map_left, hMinS]; congr 1; funext sHit; cases sHit with
      | some se => rcases se with ⟨idx, eA⟩; simp only [Expr.eval, Expr.v0, env0, Env.get, seqFgEntryDkE_eval, roHitRespSimE_eval, map_pure, forgetSimShadow, Prod.map, id]
      | none => simp only [Expr.eval, Expr.v0, Expr.v1, env0, Env.get, roHitRespSimE_eval, map_pure, Option.map, forgetSimShadow, Prod.map, id]
    · intro out hOut; simp only [support_bind, Set.mem_iUnion, exists_prop] at hOut; rcases hOut with ⟨sHit, _, hOutS⟩
      cases sHit with
      | some se => rcases se with ⟨idx, eA⟩; simp only [Expr.eval, Expr.v0, env0, Env.get, seqFgEntryDkE_eval, support_pure, Set.mem_singleton_iff] at hOutS; subst hOutS; exact hHitInv (fgEntryDk eA)
      | none => simp only [Expr.eval, Expr.v0, Expr.v1, env0, Env.get, support_pure, Set.mem_singleton_iff] at hOutS; subst hOutS; exact hHitInv dk

private theorem findML_map_right {ι : Type} {T : OracleSpec ι} {α β : Type}
    (g : α → β) (p : β → OracleComp T Bool) (L : List α) :
    Option.map g <$> findML (fun a => p (g a)) L = findML p (L.map g) := by
  induction L with
  | nil => simp [findML]
  | cons a as ih => simp only [List.map_cons, findML, map_bind]; congr 1; funext c; cases c <;> simp [ih]

private theorem fgPatchC_eval_eq_roPostPosSem
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) (K : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γsm Γsec Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γsm Δ] [Ext Γsec Δ]
    (p1 : Var Γ₁ fgPosTy) (p2 : Var Γ₂ fgPosTy) (p3 : Var Γ₃ fgPosTy)
    (p4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (sm : Var Γsm simTy) (sec : Var Γsec (B 192))
    (ρ : Env Δ) (sA : (embedTy simTy).denote) (secVal : Bytes) (pack : roPosPackTy.denote)
    (hSm : ρ.get (Ext.wk sm) = projVal simTy sA) (hSec : ρ.get (Ext.wk sec) = secVal)
    (hPack : (ρ.get (Ext.wk p1), (ρ.get (Ext.wk p2), (ρ.get (Ext.wk p3), (ρ.get (Ext.wk p4?), ρ.get (Ext.wk ss))))) = pack) :
    embedVal (.prod keyIndRespTy simTy) <$>
      evalGdh ((bindV (fgPatchC K p1 p2 p3 p4? ss (smFgL (v sm))) fun res =>
        .ret (.pair (rDrKey (.fst (v res)))
          (smUpd (v sm) (fgL := .snd (v res)) (log := .cons (v sec) (smLog (v sm)))))).eval ρ) =
      roPostPosSem evalGdh K pack sA secVal := by
  subst hPack; set lVVal := (projVal simTy sA).2.1
  have hFgMap : lVVal.map (embedVal fgPatchEntryTy) = sA.2.1 := congrArg (fun x => x.2.1) (embedVal_projVal simTy sA)
  have hRaw : (projVal simTy sA).2.2.1 = sA.2.2.1 := by
    have h := congrArg (fun x => x.2.2.1) (embedVal_projVal simTy sA)
    change embedVal (.list (.prod (B 192) drKeyTy)) (projVal simTy sA).2.2.1 = sA.2.2.1 at h; rwa [embedVal_rawList_eq] at h
  have hLog : (projVal simTy sA).2.2.2.1 = sA.2.2.2.1 := by
    have h := congrArg (fun x => x.2.2.2.1) (embedVal_projVal simTy sA)
    change embedVal (.list (B 192)) (projVal simTy sA).2.2.2.1 = sA.2.2.2.1 at h; rwa [embedVal_logList_eq] at h
  have hSmFg : (smFgL (v sm)).eval ρ = lVVal := by simp [smFgL, v, Expr.eval, hSm, lVVal]
  have hPred : ∀ e : fgPatchEntryTy.denote,
      evalGdh ((entryMatchesC p1 p2 p3 p4? ss .zero).eval (.cons e (.cons lVVal ρ))) =
        roEntryPredGdh evalGdh (ρ.get (Ext.wk p1), (ρ.get (Ext.wk p2), (ρ.get (Ext.wk p3), (ρ.get (Ext.wk p4?), ρ.get (Ext.wk ss)))))
          (embedVal fgPatchEntryTy e) := by
    intro e; rw [entryMatchesC_eval_congr]; simp only [roEntryPredGdh, projVal_embedVal, Env.get, Ext.step_wk']
  simp only [fgPatchC, bindV, letV_eval, Comp.eval]; rw [hSmFg]
  simp only [caseOptV, findMV, Comp.eval, bind_assoc, hgl.evalGdh_bind, hgl.evalGdh_pure,
    hgl.evalGdh_findML, map_bind, v, Expr.eval, Env.get_zero', Ext.refl_wk']
  have hFindCongr : findML (fun x => evalGdh ((entryMatchesC p1 p2 p3 p4? ss .zero).eval (.cons x (.cons lVVal ρ)))) (lVVal.take K) =
      findML (fun e => roEntryPredGdh evalGdh (ρ.get (Ext.wk p1), (ρ.get (Ext.wk p2),
        (ρ.get (Ext.wk p3), (ρ.get (Ext.wk p4?), ρ.get (Ext.wk ss))))) (embedVal fgPatchEntryTy e)) (lVVal.take K) := by
    congr 1; funext e; exact hPred e
  rw [hFindCongr]; unfold roPostPosSem
  have hTakeMap : sA.2.1.take K = (lVVal.take K).map (embedVal fgPatchEntryTy) := by rw [← hFgMap, List.map_take]
  rw [hTakeMap, ← findML_map_right (embedVal fgPatchEntryTy), bind_map_left, bind_map_left]
  congr 1; funext found; cases found with
  | none =>
    simp only [gPrim_sDrKey96_eval_const, bind_assoc, pure_bind, hgl.evalGdh_bind, hgl.evalGdh_pure, map_pure, Option.map]
    congr 1; funext dk
    simp only [feMk, rDrKey, rDrKeyVal, smUpd, smMk, smBase, smRaw, smLog, smPows,
      Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', hSm, hSec, hRaw, hLog]
    congr 1; change (embedVal keyIndRespTy (rDrKeyVal dk), embedVal simTy _) = _
    rw [embedVal_simTy_upd]; congr 3
    change embedVal fgPatchEntryTy _ :: lVVal.map (embedVal fgPatchEntryTy) = _
    rw [hFgMap]; change (_, (_, (_, (_, (_, embedVal drKeyTy dk))))) :: _ = _; rw [embedVal_drKeyTy]; rfl
  | some e =>
    simp only [pure_bind, hgl.evalGdh_pure, map_pure, Option.map, feDk, rDrKey, rDrKeyVal, smUpd, smMk, smBase, smRaw, smLog, smPows,
      Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', hSm, hSec, hRaw, hLog]
    have hDk : fgEntryDk (embedVal fgPatchEntryTy e) = e.2.2.2.2.2 := embedVal_drKeyTy e.2.2.2.2.2
    rw [hDk]; congr 1; change (embedVal keyIndRespTy (rDrKeyVal e.2.2.2.2.2), embedVal simTy _) = _
    rw [embedVal_simTy_upd]; congr 3

private theorem bind_congr_of_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (mx : OracleComp spec α) (f g : α → OracleComp spec β) (h : ∀ a ∈ support mx, f a = g a) : (mx >>= f) = (mx >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]; congr 1; ext u; exact ih u (fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩))

private theorem roNotPrefixE_eval (sK : simShadowAtomicTy.denote) (sec : Bytes) :
    (exprRename wkSndVar (mapExpr roNotPrefixE)).eval (.cons sK (.cons sec .nil)) = !(sec.take 32 == F_X25519) := by
  rw [exprRename_eval (mapExpr roNotPrefixE) wkSndVar (embedEnv (.cons sec .nil)) _
    (by intro _ v; dsimp only [AtomicLift.embedCtx] at v; cases v with | zero => rfl | succ v => nomatch v), mapExpr_eval]
  simp [roNotPrefixE, v, Expr.eval, Env.get_zero', embedVal]

private theorem roLenEqE_eval (n : ℕ) (sK : simShadowAtomicTy.denote) (sec : Bytes) :
    (exprRename wkSndVar (mapExpr (roLenEqE n))).eval (.cons sK (.cons sec .nil)) = (sec.length == n) := by
  rw [exprRename_eval (mapExpr (roLenEqE n)) wkSndVar (embedEnv (.cons sec .nil)) _
    (by intro _ v; dsimp only [AtomicLift.embedCtx] at v; cases v with | zero => rfl | succ v => nomatch v), mapExpr_eval]
  simp [roLenEqE, v, Expr.eval, Env.get_zero', embedVal]

private theorem roNotPrefixLeg_eval (sL : simTy.denote) (sec : Bytes) :
    ((.not (eqB (takeKB 192 32 (v (Γ := [simTy, B 192]) (.succ .zero))) (litB 32 F_X25519)) :
      Expr pqxdhOps [simTy, B 192] .bool).eval (.cons sL (.cons sec .nil))) = !(sec.take 32 == F_X25519) := by
  simp [v, Expr.eval, Env.get_succ', Ext.refl_wk']

private theorem roLenEqLeg_eval (n : ℕ) (sL : simTy.denote) (sec : Bytes) :
    ((natEq (lenB (v (Γ := [simTy, B 192]) (.succ .zero))) (.nat n) :
      Expr pqxdhOps [simTy, B 192] .bool).eval (.cons sL (.cons sec .nil))) = (sec.length == n) := by
  simp [v, Expr.eval, Env.get_succ', Ext.refl_wk']

private theorem bindV_mkSecretPosC_eval {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) {Γ Δ : List PT} [Ext Γ Δ] (off : ℕ) (sec : Var Γ (B 192))
    (k : Var (fgPosTy :: Δ) fgPosTy → Comp pqxdhOps pqGapDhIface (fgPosTy :: Δ) (.prod keyIndRespTy simTy))
    (ρ : Env Δ) :
    embedVal (.prod keyIndRespTy simTy) <$> evalGdh ((bindV (mkSecretPosC (slice32 off (v sec))) k).eval ρ) =
      evalGdh ((mkSecretPosC (Γ := [B 192]) (slice32 off (.var .zero))).eval (.cons (ρ.get (Ext.wk sec)) .nil)) >>=
        fun p => embedVal (.prod keyIndRespTy simTy) <$> evalGdh ((k .zero).eval (.cons p ρ)) := by
  simp only [bindV, Comp.eval, hgl.evalGdh_bind, map_bind]; rw [mkSecretPosC_eval_slice32]; rfl

private theorem bindV_mkSecretPosPre_eval {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) {Γ Δ : List PT} [Ext Γ Δ] {β : Type}
    (off : ℕ) (sec : Var Γ (B 192))
    (k : Var (fgPosTy :: Δ) fgPosTy → Comp pqxdhOps pqGapDhIface (fgPosTy :: Δ) roPosPackTy)
    (f : roPosPackTy.denote → OracleComp T β) (ρ : Env Δ) :
    (evalGdh ((bindV (mkSecretPosC (slice32 off (v sec))) k).eval ρ) >>= f) =
      evalGdh ((mkSecretPosC (Γ := [B 192]) (slice32 off (.var .zero))).eval (.cons (ρ.get (Ext.wk sec)) .nil)) >>=
        fun p => evalGdh ((k .zero).eval (.cons p ρ)) >>= f := by
  simp only [bindV, Comp.eval, hgl.evalGdh_bind, bind_assoc]; rw [mkSecretPosC_eval_slice32]; rfl

private theorem roParsed192_sim
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : simShadowAtomicTy.denote) (sec : Bytes)
    (hPre : sec.take 32 = F_X25519) (hLen192 : sec.length = 192)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j (.roQuery sec) → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c sK) :
    Prod.map id forgetSimShadow <$>
        (roParsedShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil)) =
      embedVal (.prod keyIndRespTy simTy) <$>
        evalGdh ((roParsedC b.q_total (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192])
          (Δ := [simTy, B 192]) .zero (.succ .zero)).eval (.cons (projVal simTy sK.1) (.cons sec .nil))) ∧
    ∀ out ∈ support ((roParsedShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil))),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c (.roQuery sec)) out.2 := by
  unfold roParsedShadowAtomicC roParsedC
  have hNP : (!(sec.take 32 == F_X25519)) = false := by simp [hPre]
  have hN160 : (sec.length == 160) = false := by simp [hLen192]
  have hY192 : (sec.length == 192) = true := by simp [hLen192]
  simp only [Comp.eval, roNotPrefixE_eval, roLenEqE_eval, roNotPrefixLeg_eval, roLenEqLeg_eval,
    hNP, hN160, hY192, Bool.false_eq_true, ↓reduceIte]
  have hEnvSec : Env.cons (S := pqAtomicSig) (t := PB 192) sec Env.nil =
      embedEnv (Γ := [B 192]) (.cons sec .nil) := rfl
  have hPreEval := hgl.liftGdhAtomic_eval
    (roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero)
    (roParsedPrePos192C_unsupported_zero .zero) (.cons (sec : (B 192).denote) .nil)
  rw [runAt1_eval]; simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get]
  rw [hEnvSec, hPreEval]; simp only [bind_map_left, runAt3_eval, Expr.eval, Env.get]
  refine ⟨?_, ?_⟩
  · rw [map_bind]
    trans (evalGdh ((roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero).eval (.cons sec .nil)) >>=
      fun pack => roPostPosSem evalGdh b.q_total pack sK.1 sec)
    · refine bind_congr_of_support _ _ _ fun pack hMem => ?_
      have hWf := roParsedPrePos192C_support_wf sec hPre hLen192 (hgl.mem_support_evalGdh hMem)
      exact (roParsedPostPosShadowAtomicC_sim hgl S b c sK sec pack (embedVal roPosPackTy pack)
        rfl hWf hB hRoom hInv).1
    · symm; dsimp only [roParsedPrePos192C]
      rw [bindV_mkSecretPosC_eval hgl, bindV_mkSecretPosPre_eval hgl]; congr 1; funext p1
      rw [bindV_mkSecretPosC_eval hgl, bindV_mkSecretPosPre_eval hgl]; congr 1; funext p2
      rw [bindV_mkSecretPosC_eval hgl, bindV_mkSecretPosPre_eval hgl]; congr 1; funext p3
      rw [bindV_mkSecretPosC_eval hgl, bindV_mkSecretPosPre_eval hgl]; congr 1; funext p4Raw
      rw [letV_eval, letV_eval]
      conv_rhs => simp only [letV, Comp.eval, hgl.evalGdh_pure, pure_bind, v, Expr.eval,
        Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', slice32_eval]
      apply fgPatchC_eval_eq_roPostPosSem hgl <;>
        simp [v, Expr.eval, slice32_eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk']
  · intro out hOut
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hOut
    rcases hOut with ⟨pack, hMem, hOutPost⟩
    have hWf := roParsedPrePos192C_support_wf sec hPre hLen192 (hgl.mem_support_evalGdh hMem)
    exact (roParsedPostPosShadowAtomicC_sim hgl S b c sK sec pack (embedVal roPosPackTy pack)
      rfl hWf hB hRoom hInv).2 out hOutPost

private theorem roParsed160_sim
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : simShadowAtomicTy.denote) (sec : Bytes)
    (hPre : sec.take 32 = F_X25519) (hLen160 : sec.length = 160)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j (.roQuery sec) → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c sK) :
    Prod.map id forgetSimShadow <$>
        (roParsedShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil)) =
      embedVal (.prod keyIndRespTy simTy) <$>
        evalGdh ((roParsedC b.q_total (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192])
          (Δ := [simTy, B 192]) .zero (.succ .zero)).eval (.cons (projVal simTy sK.1) (.cons sec .nil))) ∧
    ∀ out ∈ support ((roParsedShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil))),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c (.roQuery sec)) out.2 := by
  unfold roParsedShadowAtomicC roParsedC
  have hNP : (!(sec.take 32 == F_X25519)) = false := by simp [hPre]
  have hY160 : (sec.length == 160) = true := by simp [hLen160]
  simp only [Comp.eval, roNotPrefixE_eval, roLenEqE_eval, roNotPrefixLeg_eval, roLenEqLeg_eval,
    hNP, hY160, Bool.false_eq_true, ↓reduceIte]
  have hEnvSec : Env.cons (S := pqAtomicSig) (t := PB 192) sec Env.nil =
      embedEnv (Γ := [B 192]) (.cons sec .nil) := rfl
  have hPreEval := hgl.liftGdhAtomic_eval
    (roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero)
    (roParsedPrePos160C_unsupported_zero .zero) (.cons (sec : (B 192).denote) .nil)
  rw [runAt1_eval]; simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get]
  rw [hEnvSec, hPreEval]; simp only [bind_map_left, runAt3_eval, Expr.eval, Env.get]
  refine ⟨?_, ?_⟩
  · rw [map_bind]
    trans (evalGdh ((roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero).eval (.cons sec .nil)) >>=
      fun pack => roPostPosSem evalGdh b.q_total pack sK.1 sec)
    · refine bind_congr_of_support _ _ _ fun pack hMem => ?_
      have hWf := roParsedPrePos160C_support_wf sec hPre hLen160 (hgl.mem_support_evalGdh hMem)
      exact (roParsedPostPosShadowAtomicC_sim hgl S b c sK sec pack (embedVal roPosPackTy pack)
        rfl hWf hB hRoom hInv).1
    · symm; dsimp only [roParsedPrePos160C]
      rw [bindV_mkSecretPosC_eval hgl, bindV_mkSecretPosPre_eval hgl]; congr 1; funext p1
      rw [bindV_mkSecretPosC_eval hgl, bindV_mkSecretPosPre_eval hgl]; congr 1; funext p2
      rw [bindV_mkSecretPosC_eval hgl, bindV_mkSecretPosPre_eval hgl]; congr 1; funext p3
      rw [letV_eval, letV_eval]
      conv_rhs => simp only [letV, Comp.eval, hgl.evalGdh_pure, pure_bind, v, Expr.eval,
        Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', slice32_eval]
      apply fgPatchC_eval_eq_roPostPosSem hgl <;>
        simp [v, Expr.eval, slice32_eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk']
  · intro out hOut
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hOut
    rcases hOut with ⟨pack, hMem, hOutPost⟩
    have hWf := roParsedPrePos160C_support_wf sec hPre hLen160 (hgl.mem_support_evalGdh hMem)
    exact (roParsedPostPosShadowAtomicC_sim hgl S b c sK sec pack (embedVal roPosPackTy pack)
      rfl hWf hB hRoom hInv).2 out hOutPost

/-- Full forgetful simulation and `GdhSimInv` preservation for `roParsedShadowAtomicC`
    against `roParsedC b.q_total`, polymorphic in `GdhAtomicLiftValid`. -/
theorem roParsedShadowAtomicC_sim
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A} {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh) (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : simShadowAtomicTy.denote) (sec : Bytes)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j (.roQuery sec) → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c sK) :
    Prod.map id forgetSimShadow <$>
        (roParsedShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil)) =
      embedVal (.prod keyIndRespTy simTy) <$>
        evalGdh ((roParsedC b.q_total (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192])
          (Δ := [simTy, B 192]) .zero (.succ .zero)).eval (.cons (projVal simTy sK.1) (.cons sec .nil))) ∧
    ∀ out ∈ support ((roParsedShadowAtomicC gl (keyIndKFuelsOfBudget S b)).eval (.cons sK (.cons sec .nil))),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c (.roQuery sec)) out.2 := by
  cases hNotPre : !(sec.take 32 == F_X25519)
  · have hPre : sec.take 32 = F_X25519 := by simpa using hNotPre
    cases hIs160 : (sec.length == 160)
    · cases hIs192 : (sec.length == 192)
      · unfold roParsedShadowAtomicC roParsedC
        simp only [Comp.eval, roNotPrefixE_eval, roLenEqE_eval, roNotPrefixLeg_eval, roLenEqLeg_eval,
          hNotPre, hIs160, hIs192, Bool.false_eq_true, ↓reduceIte]
        exact roRawFallbackShadowAtomicC_sim hgl S b c sK sec hRoom hInv
      · exact roParsed192_sim hgl S b c sK sec hPre (by simpa using hIs192) hB hRoom hInv
    · exact roParsed160_sim hgl S b c sK sec hPre (by simpa using hIs160) hB hRoom hInv
  · unfold roParsedShadowAtomicC roParsedC
    simp only [Comp.eval, roNotPrefixE_eval, roNotPrefixLeg_eval, hNotPre, ↓reduceIte]
    exact roRawFallbackShadowAtomicC_sim hgl S b c sK sec hRoom hInv

private theorem gdhSimInv_bump_roQuery {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ} {sec : Bytes}
    {sK : simShadowAtomicTy.denote} (hInv : GdhSimInv S b c sK) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c (.roQuery sec)) sK := by
  obtain ⟨tagged, hRel, hWf, hRoLe⟩ := hInv.fg_shadow
  refine ⟨baseOnlineLenInv_bump_roQuery hInv.online_len, ?_, ⟨tagged, hRel, hWf, ?_⟩, ?_, hInv.raw_shadow, ?_, ?_⟩
  · rw [bump_roQuery_zero]; exact hInv.fg_sess_le
  · rw [bump_roQuery_one]; exact Nat.le_succ_of_le hRoLe
  · rw [bump_roQuery_one]; exact Nat.le_succ_of_le hInv.raw_len
  · rw [bump_roQuery_one]; exact Nat.le_succ_of_le hInv.log_len
  · rw [bump_roQuery_zero]; exact hInv.pows_len

private theorem liftGdhToSigDdh_eq_liftGdhComp {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) : liftGdhToSigDdh c = liftGdhComp c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp [liftGdhToSigDdh, liftGdhComp, *]

private theorem roRawFallbackC_eval_congr (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (smV : Var Γ₁ simTy) (secV : Var Γ₂ (B 192)) (ρ : Env Δ) :
    (roRawFallbackC K smV secV).eval ρ = (roRawFallbackC K (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192])
      (Δ := [simTy, B 192]) .zero (.succ .zero)).eval (.cons (ρ.get (Ext.wk smV)) (.cons (ρ.get (Ext.wk secV)) .nil)) := by
  simp only [roRawFallbackC, caseOptV, bindV, eFind, smRaw, smUpd, smMk, smBase, smFgL, smLog, smPows,
    rDrKey, eqB_eval, v, Comp.eval, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', gPrim_sDrKey96_eval_const]

private theorem fgPatchC_eval_congr (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    {Γ₁' Γ₂' Γ₃' Γ₄' Γ₅' Δ' : List PT} [Ext Γ₁' Δ'] [Ext Γ₂' Δ'] [Ext Γ₃' Δ'] [Ext Γ₄' Δ'] [Ext Γ₅' Δ']
    (p1 : Var Γ₁ fgPosTy) (p2 : Var Γ₂ fgPosTy) (p3 : Var Γ₃ fgPosTy) (p4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (lE : Expr pqxdhOps Δ (.list fgPatchEntryTy)) (q1 : Var Γ₁' fgPosTy) (q2 : Var Γ₂' fgPosTy) (q3 : Var Γ₃' fgPosTy)
    (q4? : Var Γ₄' (.opt fgPosTy)) (qs : Var Γ₅' (B 32)) (lE' : Expr pqxdhOps Δ' (.list fgPatchEntryTy))
    (ρ : Env Δ) (ρ' : Env Δ') (h1 : ρ.get (Ext.wk p1) = ρ'.get (Ext.wk q1)) (h2 : ρ.get (Ext.wk p2) = ρ'.get (Ext.wk q2))
    (h3 : ρ.get (Ext.wk p3) = ρ'.get (Ext.wk q3)) (h4 : ρ.get (Ext.wk p4?) = ρ'.get (Ext.wk q4?))
    (h5 : ρ.get (Ext.wk ss) = ρ'.get (Ext.wk qs)) (hl : lE.eval ρ = lE'.eval ρ') :
    (fgPatchC K p1 p2 p3 p4? ss lE).eval ρ = (fgPatchC K q1 q2 q3 q4? qs lE').eval ρ' := by
  simp only [fgPatchC, bindV, letV, caseOptV, findMV, feMk, feDk, v, Comp.eval, Expr.eval,
    pure_bind, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk', gPrim_sDrKey96_eval_const, h1, h2, h3, h4, h5, hl]
  have hF : findML (fun x => (entryMatchesC p1 p2 p3 p4? ss .zero).eval (.cons x (.cons (lE'.eval ρ') ρ))) ((lE'.eval ρ').take K) =
      findML (fun x => (entryMatchesC q1 q2 q3 q4? qs .zero).eval (.cons x (.cons (lE'.eval ρ') ρ'))) ((lE'.eval ρ').take K) := by
    congr 1; funext x
    conv_lhs => rw [entryMatchesC_eval_congr]
    conv_rhs => rw [entryMatchesC_eval_congr]
    simp only [Env.get, Ext.step_wk', h1, h2, h3, h4, h5]
  rw [hF]

private theorem bind_congr' {ι : Type} {S₀ : OracleSpec ι} {α β : Type}
    {m₁ m₂ : OracleComp S₀ α} {f₁ f₂ : α → OracleComp S₀ β} (hm : m₁ = m₂) (hf : ∀ a, f₁ a = f₂ a) : (m₁ >>= f₁) = (m₂ >>= f₂) :=
  hm ▸ congrArg (m₁ >>= ·) (funext hf)

private theorem roParsedC_eval_congr (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (smV : Var Γ₁ simTy) (secV : Var Γ₂ (B 192)) (ρ : Env Δ) :
    (roParsedC K smV secV).eval ρ = (roParsedC K (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192])
      (Δ := [simTy, B 192]) .zero (.succ .zero)).eval (.cons (ρ.get (Ext.wk smV)) (.cons (ρ.get (Ext.wk secV)) .nil)) := by
  unfold roParsedC; simp only [Comp.eval, roNotPrefixLeg_eval, roLenEqLeg_eval]
  have hP1 : (Expr.not (eqB (takeKB 192 32 (v secV)) (litB 32 F_X25519))).eval ρ = !((ρ.get (Ext.wk secV)).take 32 == F_X25519) := by simp [v, Expr.eval]
  have hL160 : (natEq (lenB (v secV)) (.nat 160)).eval ρ = ((ρ.get (Ext.wk secV)).length == 160) := by simp [v, Expr.eval]
  have hL192 : (natEq (lenB (v secV)) (.nat 192)).eval ρ = ((ρ.get (Ext.wk secV)).length == 192) := by simp [v, Expr.eval]
  rw [hP1, hL160, hL192]; split_ifs with h1 h2 h3
  · exact roRawFallbackC_eval_congr K smV secV ρ
  · simp only [bindV, letV, v, Comp.eval, Expr.eval, pure_bind, slice32_eval, mkSecretPosC_eval_slice32, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk']
    refine bind_congr' rfl fun p1 => bind_congr' rfl fun p2 => bind_congr' rfl fun p3 => bind_congr' ?_ fun res => ?_
    · exact fgPatchC_eval_congr K .zero .zero .zero .zero .zero _ .zero .zero .zero .zero .zero _ _ _ rfl rfl rfl rfl rfl (by simp [smFgL, Expr.eval, Env.get_zero', Env.get_succ'])
    · simp [rDrKey, smUpd, smMk, smBase, smRaw, smLog, smPows, Expr.eval, Env.get_zero', Env.get_succ']
  · simp only [bindV, letV, v, Comp.eval, Expr.eval, pure_bind, slice32_eval, mkSecretPosC_eval_slice32, Env.get_zero', Env.get_succ', Ext.refl_wk', Ext.step_wk']
    refine bind_congr' rfl fun p1 => bind_congr' rfl fun p2 => bind_congr' rfl fun p3 => bind_congr' rfl fun p4 => bind_congr' ?_ fun res => ?_
    · exact fgPatchC_eval_congr K .zero .zero .zero .zero .zero _ .zero .zero .zero .zero .zero _ _ _ rfl rfl rfl rfl rfl (by simp [smFgL, Expr.eval, Env.get_zero', Env.get_succ'])
    · simp [rDrKey, smUpd, smMk, smBase, smRaw, smLog, smPows, Expr.eval, Env.get_zero', Env.get_succ']
  · exact roRawFallbackC_eval_congr K smV secV ρ

private theorem ddhEqC_sigDdh_unsup {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (liftGdhComp (ddhEqC p1 p2)).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [ddhEqC, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ, liftGdhComp, letV, caseSumV, Comp.queries, tlSigDdhKeyInd]
private theorem ddhEqOptC_sigDdh_unsup {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (liftGdhComp (ddhEqOptC p1 p2)).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [ddhEqOptC, ddhEqC_sigDdh_unsup, liftGdhComp, letV, caseOptV, Comp.queries]
private theorem renameComp_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ Δ : List PT} {t : PT}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (ξ : Ren Γ Δ) (c : Comp pqxdhOps I Γ t) :
    (renameComp ξ c).queries w ws = c.queries w ws := by induction c generalizing Δ <;> simp [renameComp, Comp.queries, *]

private theorem renameComp_roParsedC_unsup {Γ₁ Γ₂ Δ Δ' : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (ξ : Ren Δ Δ') (K : ℕ) (sm : Var Γ₁ simTy) (sec : Var Γ₂ (B 192)) :
    (renameComp ξ (liftGdhComp (roParsedC K sm sec))).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  rw [renameComp_queries]; dsimp only [roParsedC, roRawFallbackC, fgPatchC, entryMatchesC, bindV, letV, caseOptV, findMV, liftGdhComp]
  simp only [Comp.queries, ddhEqC_sigDdh_unsup, ddhEqOptC_sigDdh_unsup]
  simp [mkSecretPosC, gPrim, liftBase, sDrKey96, qIsCanonical, bindV, letV, liftGdhComp, Comp.queries, tlSigDdhKeyInd,
    Computational.Proofs.SignalPqxdh.AtomicLift.keyIndUnsupportedPrimW]

private theorem liftRen_eq_varLiftRename {Γ Δ : List PT} {σ : PT} (ρ : Ren Γ Δ) :
    (fun {τ} => @ReductionDsl.Var.liftRename pqSig Γ Δ σ τ ρ) = (fun {τ} => @liftRen Γ Δ σ ρ τ) := by funext _ x; cases x <;> rfl
private theorem expr_rename_eq_renameExpr {Γ Δ : List PT} {t : PT} (ξ : Ren Γ Δ) (e : Expr pqxdhOps Γ t) :
    e.rename ξ = renameExpr ξ e := by induction e generalizing Δ <;> simp [ReductionDsl.Expr.rename, renameExpr, liftRen_eq_varLiftRename, *]
private theorem comp_rename_eq_renameComp {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {t : PT} (ξ : Ren Γ Δ) (c : Comp pqxdhOps I Γ t) : c.rename ξ = renameComp ξ c := by
  induction c generalizing Δ <;> simp [ReductionDsl.Comp.rename, renameComp, expr_rename_eq_renameExpr, liftRen_eq_varLiftRename, *]
private theorem liftGdhComp_renameComp {Γ Δ : List PT} {t : PT} (ξ : Ren Γ Δ) (c : Comp pqxdhOps pqGapDhIface Γ t) :
    liftGdhComp (renameComp ξ c) = renameComp ξ (liftGdhComp c) := by
  induction c generalizing Δ with
  | sample _ _ => rfl
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | _ => simp [liftGdhComp, renameComp, *]

private theorem liftKeyIndHandle_eval_mapComp {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {A : AtomicIface T}
    (tl : Computational.Proofs.SignalPqxdh.AtomicLift.TagLift I A) (S : Setup) {σ outH : Ty pqSig}
    (h : Comp pqxdhOps I [σ, (keyIndCodec S).Q] outH) (sA : (embedTy σ).denote) (t : KeyIndQuery S) :
    (liftKeyIndHandle tl S h).eval (.cons sA (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (mapComp tl h).eval (.cons sA (.cons (embedVal (keyIndCodec S).Q ((keyIndCodec S).qenc t)) .nil)) := by
  unfold liftKeyIndHandle; simp only [Comp.eval, pure_bind]; rw [finKeyIndQToNatExpr_eval S sA t]
  exact compRename_eval (mapComp tl h) swapHandlerVar (.cons sA (.cons (embedVal (keyIndCodec S).Q ((keyIndCodec S).qenc t)) .nil)) _
    (fun {a} v => by cases v with | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v)

private def embEnv {Γ : List PT} (ρ : Env Γ) : Env (embedCtx Γ) := embedEnv ρ
private theorem embEnv_push {Γ : List PT} {u : PT} (x : u.denote) (ρ : Env Γ) : Env.cons (embedVal u x) (embEnv ρ) = embEnv (.cons x ρ) := rfl
private theorem mapExpr_eval_emb {Γ : List PT} {t : PT} (e : Expr pqxdhOps Γ t) (ρ : Env Γ) :
    (mapExpr e).eval (embEnv ρ) = embedVal t (e.eval ρ) := mapExpr_eval e ρ
private theorem mapComp_eval_emb {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {A : AtomicIface T}
    (tl : Computational.Proofs.SignalPqxdh.AtomicLift.TagLift I A) {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps I Γ t) (hOk : c.queries tl.unsupportedW (fun _ => 0) = 0) (ρ : Env Γ) :
    (mapComp tl c).eval (embEnv ρ) = embedVal t <$> c.eval ρ := mapComp_eval tl c hOk ρ
private theorem bind_ret_mapExpr_emb {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List PT} {a : PT} {out : Ty pqAtomicSig} (e : Expr pqxdhOps Γ a) (k : Comp pqAtomicOps I (embedCtx (a :: Γ)) out) (ρ : Env Γ) :
    (Comp.bind (.ret (mapExpr e)) k).eval (embEnv ρ) = k.eval (embEnv (.cons (e.eval ρ) ρ)) := by
  simp only [Comp.eval, pure_bind, mapExpr_eval_emb, embEnv_push]
private theorem caseSum_mapExpr_emb {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List PT} {a b : PT} {out : Ty pqAtomicSig} (e : Expr pqxdhOps Γ (.sum a b))
    (l : Comp pqAtomicOps I (embedCtx (a :: Γ)) out) (r : Comp pqAtomicOps I (embedCtx (b :: Γ)) out) (ρ : Env Γ) :
    (Comp.caseSum (mapExpr e) l r).eval (embEnv ρ) = match e.eval ρ with
      | .inl x => l.eval (embEnv (.cons x ρ)) | .inr y => r.eval (embEnv (.cons y ρ)) := by
  simp only [Comp.eval, mapExpr_eval_emb]; cases e.eval ρ <;> rfl
private theorem ite_mapExpr_emb {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T} {Γ : List PT} {out : Ty pqAtomicSig}
    (b : Expr pqxdhOps Γ .bool) (c d : Comp pqAtomicOps I (embedCtx Γ) out) (ρ : Env Γ) :
    (Comp.ite (mapExpr b) c d).eval (embEnv ρ) = if b.eval ρ then c.eval (embEnv ρ) else d.eval (embEnv ρ) := by
  simp only [Comp.eval, mapExpr_eval_emb]; rfl
private theorem bind_ite_mapExpr_emb {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T} {Γ : List PT} {a out : Ty pqAtomicSig}
    (b : Expr pqxdhOps Γ .bool) (c d : Comp pqAtomicOps I (embedCtx Γ) a) (k : Comp pqAtomicOps I (a :: embedCtx Γ) out) (ρ : Env Γ) :
    (Comp.bind (.ite (mapExpr b) c d) k).eval (embEnv ρ) =
      ((if b.eval ρ then c.eval (embEnv ρ) else d.eval (embEnv ρ)) >>= fun x => k.eval (.cons x (embEnv ρ))) := by
  rw [Comp.eval, ite_mapExpr_emb]
private theorem bind_mapComp_ret_mapExpr_emb {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {A : AtomicIface T}
    (tl : Computational.Proofs.SignalPqxdh.AtomicLift.TagLift I A) {Γ : List PT} {a out : PT} (c : Comp pqxdhOps I Γ a)
    (hOk : c.queries tl.unsupportedW (fun _ => 0) = 0) (e : Expr pqxdhOps (a :: Γ) out) (ρ : Env Γ) :
    (Comp.bind (mapComp tl c) (.ret (mapExpr e))).eval (embEnv ρ) = (fun x => embedVal out (e.eval (.cons x ρ))) <$> c.eval ρ := by
  rw [Comp.eval, mapComp_eval_emb tl c hOk ρ, bind_map_left, map_eq_bind_pure_comp]
  congr 1; funext x; simp only [Function.comp_def, Comp.eval, embEnv_push, mapExpr_eval_emb]

private theorem sigActiveHandle_eval_mapComp (S : Setup) (b : QueryBudget)
    (sA : (sigKeyInd1KeyActiveAtomicProg S b).σ.denote) (t : KeyIndQuery S) :
    (sigKeyInd1KeyActiveAtomicProg S b).handle.eval (.cons sA (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (mapComp tlSigDdhKeyInd (sig1KeyActiveHandleC S b.q_total)).eval
        (.cons sA (.cons (embedVal keyIndQueryTy ((keyIndCodec S).qenc t)) .nil)) := by
  unfold sigKeyInd1KeyActiveAtomicProg liftKeyInd1Stage sigKeyInd1KeyActiveDslProg
  exact liftKeyIndHandle_eval_mapComp tlSigDdhKeyInd S (sig1KeyActiveHandleC S b.q_total) sA t

private theorem gdhActiveHandle_eval_mapComp (S : Setup) (b : QueryBudget)
    (sA : (fgKeyInd1KeyGapDhActiveAtomicProg S b).σ.denote) (t : KeyIndQuery S) :
    (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle.eval (.cons sA (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (mapComp tlSigDdhKeyInd (gdh1KeyActiveHandle S b.q_total)).eval
        (.cons sA (.cons (embedVal keyIndQueryTy ((keyIndCodec S).qenc t)) .nil)) := by
  unfold fgKeyInd1KeyGapDhActiveAtomicProg liftKeyInd1Stage fgKeyInd1KeyGapDhActiveDslProg
  exact liftKeyIndHandle_eval_mapComp tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total) sA t

private theorem mapComp_renameComp_gdhHandle2_roQuery (S : Setup) (K : ℕ) {Δ : List PT}
    (ξ : Ren [gdhState2Ty, keyIndQueryTy] Δ) (env : Env Δ)
    (pa : params2Ty.denote) (sm : simTy.denote) (sec : Bytes)
    (hSt : env.get (ξ .zero) = (pa, sm))
    (hQ : env.get (ξ (.succ .zero)) = (keyIndCodec S).qenc (.roQuery sec)) :
    (mapComp tlSigDdhKeyInd (renameComp ξ (liftGdhComp (gdhHandle2 S K)))).eval (embEnv env) =
      (fun rs => (rs.1, (embedVal params2Ty pa, rs.2))) <$>
        (embedVal (.prod keyIndRespTy simTy) <$>
          liftGdhToSign ((roParsedC K (Γ₁ := [simTy, B 192]) (Γ₂ := [simTy, B 192])
            (Δ := [simTy, B 192]) .zero (.succ .zero)).eval (.cons sm (.cons sec .nil)))) := by
  have hQ' : (keyIndCodec S).qenc (.roQuery sec) =
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))) := rfl
  unfold gdhHandle2
  dsimp only [letV, caseSumV, wrapSim2, bindV, liftGdhComp, renameComp, mapComp]
  simp only [bind_ret_mapExpr_emb, caseSum_mapExpr_emb, renameExpr_eval, pullEnv_liftRen, pullEnv_get,
    smBase, v, Expr.eval, Env.get, Ext.refl_wk', Ext.step_wk', hSt, hQ, hQ']
  rw [bind_mapComp_ret_mapExpr_emb tlSigDdhKeyInd _ (renameComp_roParsedC_unsup _ K _ _)]
  rw [renameComp_eval, liftGdhComp_eval, roParsedC_eval_congr]
  simp only [pullEnv_liftRen, Env.get, Ext.refl_wk', Ext.step_wk', _root_.Functor.map_map]
  congr 1

private theorem sig1KeyActivePreDispatchC_roQuery_none (S : Setup) (K : ℕ)
    (st : sig1KeyActiveStTy.denote) (sec : Bytes) (hFg : st.2.2.2.2.2 = none) :
    (mapComp tlSigDdhKeyInd (sig1KeyActivePreDispatchC S K
      (Γ₁ := [sig1KeyActiveStTy, keyIndQueryTy])
      (Γ₂ := [sig1KeyActiveStTy, keyIndQueryTy])
      (Δ := [sig1KeyActiveStTy, keyIndQueryTy]) .zero (.succ .zero))).eval
      (embEnv (Γ := [sig1KeyActiveStTy, keyIndQueryTy])
        (.cons st (.cons ((keyIndCodec S).qenc (.roQuery sec)) .nil))) =
    pure (embedVal (.sum (.prod keyIndRespTy sig1KeyActiveStTy) .unit) (.inr ())) := by
  have hQ : ((keyIndCodec S).qenc (.roQuery sec) : keyIndQueryTy.denote) =
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))) := rfl
  unfold sig1KeyActivePreDispatchC; dsimp only [caseSumV, mapComp]
  simp only [ite_mapExpr_emb, caseSum_mapExpr_emb, isSomeE, saInner, s1Forgery, v, Expr.eval, Env.get,
    Ext.refl_wk', Ext.step_wk', hFg, hQ, Bool.false_eq_true, ↓reduceIte]
  simp [Comp.eval, mapExpr_eval_emb, Expr.eval]

/-- `.roQuery` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_roQuery (S : Setup) (b : QueryBudget) :
    ∀ sec, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.roQuery sec) := by
  intro sec c s' hB hRoom hInv
  rcases s' with ⟨⟨tp?, ⟨smA, ⟨ord, ⟨pk, ⟨bud, fg?⟩⟩⟩⟩⟩, shA⟩
  have hHasFg : ∀ qVal, (sigHasForgeryAtomicE (.fst .v1) : Expr pqAtomicOps
      [PB 192, sig1KeyActiveKindStTy, (pqKeyIndCodec S).Q] .bool).eval
      (.cons sec (.cons ((tp?, (smA, (ord, (pk, (bud, fg?))))), shA) (.cons qVal .nil))) =
      fg?.isSome := by
    intro qVal; dsimp [sigHasForgeryAtomicE, isSomeE, saInner, s1Forgery, mapExpr, exprRename, ren1,
      Computational.Proofs.SignalPqxdh.AtomicLift.liftRen, embedVar, Expr.eval, Expr.v1, Env.get]
    cases fg? <;> rfl
  unfold sig1KeyKindHandleC; rw [dispatchKeyIndQ_eval]; dsimp only
  cases fg? with
  | some fv =>
    unfold sigKindRoArm
    simp only [Comp.eval, hHasFg, Option.isSome_some, ↓reduceIte]
    simp only [Expr.eval, Expr.v1, Env.get, map_pure, support_pure, Set.mem_singleton_iff]
    refine ⟨Eq.trans ?_ (sigActiveHandle_eval_mapComp S b _ (.roQuery sec)).symm,
      fun p hp => by subst hp; exact gdhSimInv_bump_roQuery hInv⟩
    set stFixS := forgetSig1KeyActiveK S b ((tp?, (smA, (ord, (pk, (bud, some fv))))), shA)
    have hEnvS : Env.cons stFixS (.cons (embedVal keyIndQueryTy ((keyIndCodec S).qenc (.roQuery sec))) .nil) =
        embEnv (Γ := [sig1KeyActiveStTy, keyIndQueryTy])
          (.cons (projVal sig1KeyActiveStTy stFixS) (.cons ((keyIndCodec S).qenc (.roQuery sec)) .nil)) := by
      simp [embEnv, embedEnv, embedVal_projVal]
    have hFgSome : (projVal sig1KeyActiveStTy stFixS).2.2.2.2.2 =
        some (projVal (.prod (B 1569) (B 64)) fv) := rfl
    rw [hEnvS]
    unfold sig1KeyActiveHandleC sig1KeyActivePreDispatchC
    dsimp only [bindV, caseSumV, mapComp]
    rw [bind_ite_mapExpr_emb]
    simp only [isSomeE, saInner, s1Forgery, v, Expr.eval, Env.get, Ext.refl_wk', hFgSome, ↓reduceIte]
    simp only [Comp.eval, mapExpr_eval_emb, pure_bind, embEnv_push, Expr.eval, Env.get, Ext.step_wk']
    have hRNone : ∀ {Γ} (ρ : Env Γ), embedVal keyIndRespTy ((rNone : Expr _ Γ keyIndRespTy).eval ρ) = .inl () :=
      fun _ => rfl
    change pure (Sum.inl (), stFixS) =
      pure (embedVal keyIndRespTy _, embedVal sig1KeyActiveStTy (projVal sig1KeyActiveStTy stFixS))
    rw [hRNone, embedVal_projVal]
  | none =>
    unfold sigKindRoArm
    simp only [Comp.eval, hHasFg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, runAt2_eval]
    dsimp only [sigGetFgAtomicE, sigSetFgAtomicE, saTP, s1Upd, s1Mk, s1Target, s1Pk, s1Budget, s1Forgery,
      mapExpr, exprRename, ren1, Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.ren1,
      Computational.Proofs.SignalPqxdh.AtomicLift.liftRen, embedVar, v,
      Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, Ext.refl_wk', Ext.step_wk']
    have hRoSim := roParsedShadowAtomicC_sim gdhLift1Key_valid S b c (smA, shA) sec hB hRoom hInv
    refine ⟨Eq.trans ?_ (sigActiveHandle_eval_mapComp S b _ (.roQuery sec)).symm, ?_⟩
    · set stFix := forgetSig1KeyActiveK S b ((tp?, (smA, (ord, (pk, (bud, none))))), shA)
      have hEnv : Env.cons stFix (.cons (embedVal keyIndQueryTy ((keyIndCodec S).qenc (.roQuery sec))) .nil) =
          embEnv (Γ := [sig1KeyActiveStTy, keyIndQueryTy])
            (.cons (projVal sig1KeyActiveStTy stFix) (.cons ((keyIndCodec S).qenc (.roQuery sec)) .nil)) := by
        simp [embEnv, embedEnv, embedVal_projVal]
      rw [hEnv]
      have hFgNone : (projVal sig1KeyActiveStTy stFix).2.2.2.2.2 = none := rfl
      have hQ : ((keyIndCodec S).qenc (.roQuery sec) : keyIndQueryTy.denote) =
          .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))) := rfl
      unfold sig1KeyActiveHandleC
      simp only [liftGdhToSigDdh_eq_liftGdhComp, comp_rename_eq_renameComp, liftGdhComp_renameComp]
      dsimp only [letV, bindV, caseSumV, mapComp]
      rw [Comp.eval, sig1KeyActivePreDispatchC_roQuery_none S b.q_total _ sec hFgNone, pure_bind, embEnv_push]
      simp only [caseSum_mapExpr_emb, bind_ret_mapExpr_emb,
        saInner, s1Pk, s1Fg, pa2Mk, litB_eval, v, Expr.eval, Env.get, Ext.refl_wk', Ext.step_wk', hQ]
      simp only [Comp.eval]
      set pa2Val : params2Ty.denote :=
        ([], (projVal (B 32) pk, ([], (none, (false, (none, (none, (false, (none, 1)))))))))
      rw [mapComp_renameComp_gdhHandle2_roQuery S b.q_total _ _ pa2Val (projVal simTy smA) sec
        (by simp [renamePair, stFix, forgetSig1KeyActiveK, fixSig1KeyActiveSent, pa2Val, projVal])
        (by rw [hQ]; rfl)]
      have hLhs : (Prod.map id (forgetSig1KeyActiveK S b) <$>
          ((roParsedShadowAtomicC gdhLift1Key (keyIndKFuelsOfBudget S b)).eval (.cons (smA, shA) (.cons sec .nil)) >>=
            fun x => pure (x.1, ((tp?, (x.2.1, (ord, (pk, (bud, none))))), x.2.2)))) =
          (fun rs : (embedTy keyIndRespTy).denote × (embedTy simTy).denote =>
            (rs.1, (tp?, (rs.2, (fixSent S b ord, (pk, (bud, none))))))) <$>
            (Prod.map id forgetSimShadow <$>
              (roParsedShadowAtomicC gdhLift1Key (keyIndKFuelsOfBudget S b)).eval (.cons (smA, shA) (.cons sec .nil))) := by
        simp [_root_.Functor.map_map, Prod.map, forgetSig1KeyActiveK, fixSig1KeyActiveSent, forgetSimShadow]
      rw [hLhs, hRoSim.1]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      congr 1; funext x
      have hPush : ((embedVal (.prod keyIndRespTy simTy) x).1,
          (embedVal params2Ty pa2Val, (embedVal (.prod keyIndRespTy simTy) x).2)) =
          embedVal (.prod keyIndRespTy gdhState2Ty) (x.1, (pa2Val, x.2)) := rfl
      rw [hPush, embEnv_push, mapExpr_eval_emb]
      congr 1
      dsimp only [saTP, s1Upd, s1Mk, s1Target, s1Pk, s1Budget, s1Forgery, v, Expr.eval, Env.get,
        Ext.refl_wk', Ext.step_wk', stFix, forgetSig1KeyActiveK, fixSig1KeyActiveSent]
      simp [embedVal, projVal, embedVal_projVal]
    · intro p hp
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hp
      rcases hp with ⟨out, hOut, rfl⟩
      exact hRoSim.2 out hOut

/-- `.roQuery` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_roQuery (S : Setup) (b : QueryBudget) :
    ∀ sec, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.roQuery sec) := by
  intro sec c s' hB hRoom hInv
  rcases s' with ⟨⟨⟨⟨paA, smA⟩, sigBA⟩, ⟨tpA, cntA⟩⟩, shA⟩
  have hRoSim := roParsedShadowAtomicC_sim gdhLift1Key_valid S b c (smA, shA) sec hB hRoom hInv.sim_inv
  unfold gdh1KeyKindHandleC; rw [dispatchKeyIndQ_eval]; dsimp only
  unfold gdhKindRoArm
  simp only [Comp.eval, runAt2_eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get]
  refine ⟨Eq.trans ?_ (gdhActiveHandle_eval_mapComp S b _ (.roQuery sec)).symm, ?_⟩
  · set stFix := forgetGdh1KeyActiveK S b ((((paA, smA), sigBA), (tpA, cntA)), shA)
    set paFix := fixParamsSent S b paA
    have hEnv : Env.cons stFix (.cons (embedVal keyIndQueryTy ((keyIndCodec S).qenc (.roQuery sec))) .nil) =
        embEnv (Γ := [gdh1KeyActiveStateTy, keyIndQueryTy])
          (.cons (projVal gdh1KeyActiveStateTy stFix) (.cons ((keyIndCodec S).qenc (.roQuery sec)) .nil)) := by
      simp [embEnv, embedEnv, embedVal_projVal]
    rw [hEnv]
    have hQ : ((keyIndCodec S).qenc (.roQuery sec) : keyIndQueryTy.denote) =
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))) := rfl
    unfold gdh1KeyActiveHandle callGdhActiveHandle
    dsimp only [letV, bindV, caseSumV, mapComp]
    simp only [caseSum_mapExpr_emb, bind_ret_mapExpr_emb, paU, paV, paUp, paOpkMode, pa2Mk, v,
      Expr.eval, Env.get, Ext.refl_wk', Ext.step_wk', hQ]
    simp only [Comp.eval]
    set pa2Val : params2Ty.denote :=
      ((projVal paramsTy paFix).1, ((projVal paramsTy paFix).2.1, ((projVal paramsTy paFix).2.2.1,
        (none, (false, (none, (none, ((projVal paramsTy paFix).2.2.2.2.2.2.2.2.1, (none, 1)))))))))
    rw [mapComp_renameComp_gdhHandle2_roQuery S b.q_total _ _ pa2Val (projVal simTy smA) sec
      (by simp [twoVarRen, stFix, forgetGdh1KeyActiveK, fixGdh1KeyActiveSent, paFix, pa2Val, projVal])
      (by rw [hQ]; rfl)]
    have hLhs : (Prod.map id (forgetGdh1KeyActiveK S b) <$>
        ((roParsedShadowAtomicC gdhLift1Key (keyIndKFuelsOfBudget S b)).eval (.cons (smA, shA) (.cons sec .nil)) >>=
          fun x => pure (x.1, ((((paA, x.2.1), sigBA), (tpA, cntA)), x.2.2)))) =
        (fun rs : (embedTy keyIndRespTy).denote × (embedTy simTy).denote =>
          (rs.1, (((paFix, rs.2), sigBA), (tpA, cntA)))) <$>
          (Prod.map id forgetSimShadow <$>
            (roParsedShadowAtomicC gdhLift1Key (keyIndKFuelsOfBudget S b)).eval (.cons (smA, shA) (.cons sec .nil))) := by
      simp [_root_.Functor.map_map, Prod.map, forgetGdh1KeyActiveK,
        fixGdh1KeyActiveSent, forgetSimShadow, paFix]
    rw [hLhs, hRoSim.1]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext x
    have hPush : ((embedVal (.prod keyIndRespTy simTy) x).1,
        (embedVal params2Ty pa2Val, (embedVal (.prod keyIndRespTy simTy) x).2)) =
        embedVal (.prod keyIndRespTy gdhState2Ty) (x.1, (pa2Val, x.2)) := rfl
    rw [hPush, embEnv_push, mapExpr_eval_emb]
    congr 1
    simp [Expr.eval, stFix, forgetGdh1KeyActiveK, fixGdh1KeyActiveSent, pa2Val, paFix,
      embedVal, projVal, embedVal_projVal]
  · intro p hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hp
    rcases hp with ⟨out, hOut, rfl⟩
    exact ⟨hRoSim.2 out hOut, by dsimp only; rw [bump_roQuery_zero]; exact hInv.sendOpkCnt_le⟩

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimRo
