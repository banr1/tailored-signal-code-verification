/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq

/-!
# `Recv` Arm Forgetful Simulation for `Auth` Gap-DH and EUF-CMA

Proves the forgetful simulation contracts `fgArmSim_recvOPK` and `fgArmSim_recvNoOPK` for the
`.recvOPK` and `.recvNoOPK` query arms, shared by `a1g2KindProg` and `a1s2KindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRecv

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Expr Comp Env pqAtomicSig pqAtomicOps)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred bind_congr_support)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal projVal embedVal_projVal embedEnv authQenc_eq
   exprRename exprRename_eval compRename compRename_eval
   mapExpr mapExpr_eval mapComp mapComp_eval comp_queries_zero_of_zero tlAuthSigDdh)
open _root_.SignalPqxdh
  (Setup QueryBudget AuthQuery PreKeyMsg Bytes)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle B)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface authCodec preKeyMsgV)
open _root_.SignalPqxdh.Security (liftGdhToSign)
open _root_.SignalPqxdh.Security.ReductionDsl
  (authStateTy fgPosTy fgPatchEntryTy authQueryTy authRespTy eval_queryPrimC)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
  (Ren twoVarRen renameComp renameComp_eval
   liftGdhComp liftGdhComp_eval liftGdhToSign_map mem_support_liftGdhToSign)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext v letV bindV caseOptV caseSumV findMV eAny eFind eMap eCaseOpt eLet eLet2
   Env.get_vz Env.get_vs eval_natEq twoSideC_eval twoSideOptC_eval firstMsgADE_evalHs
   RSF patchKeyTy recvQTy fgSimTy rootEntryTy respRecTy a1gParams2Ty
   isSomeE kyberCheckE kyberEq natEq nat2Eq nat3Eq optU32Eq firstMsgADE
   hdSpkId hdPqspkId hdOpkId hdIkAPk hdEkAPk hdKemCt pmHdr pmEphAPk pmPqMsg pmAeadCt
   peSecIKA0 peIkAPk sbSpkSk sbSpkPk sbPqspkSk oeConsumed oeOpkSk oeOpkPk oeUpd
   q4 twoSideC twoSideOptC aNone aRecvHonest aRecvUnfresh
   stPrin stSpks stOpks stUsedO stUsedN stKyb stUpd
   fsBase fsPows fsL fsRootL fsResp fsUpd
   findHonestC isAdvPowsC koskSenderOkPowsC
   patchC rootPatchC fgRecvC fgRecvB fgStep2C a1gPre2C)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (findB_min_eval_eq anyB_min_eval_eq mapB_min_eval_eq findM_min_eval_eq)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels wk1 authRecvQAtomicTy)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv AuthBaseValOnlineBounded AuthBaseAtomOnlineBounded)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (seqFgEntryTy seqRootEntryTy sessAuxLegTy fgAuthShadowAuxTy fgCoreOutTy
   fgAuxMkE auxFgSessE auxFgCtrE auxFgRoAvlE auxFgRootSessE auxFgRootCtrE auxFgRootRoAvlE auxRawAvlE
   auxFgSess auxFgCtr auxFgRoAvl auxFgRootSess auxFgRootCtr auxFgRootRoAvl auxRawAvl
   auxSessSliceE auxPutSessSliceE
   liftCs1 liftGdh1 saFgSess saFgCtr saRootSess saRootCtr
   patchWithShadowC rootPatchWithShadowC fgRecvShadowC fgRecvShadowB fgCoreArm_recv)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
  (AuthSigDdhSpec FgTableShadow RootTableShadow FgSimShadowInv
   patchWithShadowC_sim rootPatchWithShadowC_sim
   legacyCoreArmComp legacyCoreArmEval armEval_recvOPK armEval_recvNoOPK
   FgArmSim)

private theorem liftCs1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out)
    (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftCs1 c argE).eval ρ =
      embedVal out <$> c.eval (.cons (projVal a (argE.eval ρ)) .nil) := by
  simp only [liftCs1, Comp.eval, pure_bind]
  refine (compRename_eval (mapComp tlAuthSigDdh c) wk1
    (embedEnv (.cons (projVal a (argE.eval ρ)) .nil)) (.cons (argE.eval ρ) ρ) ?_).trans ?_
  · intro _ vr
    cases vr with
    | zero => exact (embedVal_projVal a (argE.eval ρ)).symm
    | succ v' => nomatch v'
  · exact mapComp_eval tlAuthSigDdh c (comp_queries_zero_of_zero (fun _ => rfl) c) _

private theorem liftGdh1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out)
    (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftGdh1 c argE).eval ρ =
      embedVal out <$> liftGdhToSign (c.eval (.cons (projVal a (argE.eval ρ)) .nil)) := by
  rw [liftGdh1, liftCs1_eval, liftGdhComp_eval]

private theorem queryPrim_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (tag : _root_.SignalPqxdh.LegacyCosted.PTag)
    (e₁ : Expr pqxdhOps Γ₁ (pqPrimIface.dom tag)) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ (pqPrimIface.dom tag)) (ρ₂ : Env Γ₂)
    (h : e₁.eval ρ₁ = e₂.eval ρ₂) :
    (Comp.queryPrim tag e₁).eval ρ₁ = (Comp.queryPrim tag e₂).eval ρ₂ := by
  simp only [Comp.queryPrim, Comp.eval]
  exact h ▸ rfl

private theorem bind_congr_eq {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {oa₁ oa₂ : OracleComp spec α} {f₁ f₂ : α → OracleComp spec β}
    (ha : oa₁ = oa₂) (hf : ∀ a ∈ support oa₂, f₁ a = f₂ a) :
    oa₁ >>= f₁ = oa₂ >>= f₂ := by
  rw [ha]; exact bind_congr_support oa₂ f₁ f₂ hf

private theorem embedVal_length {t : Ty pqSig} (l : List t.denote) :
    (embedVal (.list t) l).length = l.length := by
  change (l.map (embedVal t)).length = l.length
  exact List.length_map _

private theorem findHonestC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (ik₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (ik₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁.wk st₁) = Env.get ρ₂ (h₂.wk st₂))
    (hik : ik₁.eval ρ₁ = ik₂.eval ρ₂)
    (hPrin : (Env.get ρ₁ (h₁.wk st₁)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (findHonestC S (AuthKindFuels.ofBudget S b).K_on st₁ ik₁).eval ρ₁ =
      (findHonestC S b.q_total st₂ ik₂).eval ρ₂ := by
  let F := AuthKindFuels.ofBudget S b
  have hMin : min F.K_on S.N_dh = min (min b.q_total S.N_dh) F.M_on :=
    Nat.min_right_comm b.q_total F.M_on S.N_dh
  simp only [findHonestC, letV, Comp.eval_letC, hik, findMV, Comp.findBoundedM]
  rw [hMin, findM_min_eval_eq (min b.q_total S.N_dh) F.M_on _ _ _
    (by simpa [stPrin, v, Expr.eval, Ext.step_wk, Env.get] using hPrin)]
  simp only [Comp.eval, v, Expr.eval, Ext.step_wk, Env.get, hst]
  rfl

private theorem isAdvPowsC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (pows₁ : Var Γ₁ (.list (.prod (B 32) (B 32)))) [h₁ : Ext Γ₁ Δ₁]
    (pk₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (pows₂ : Var Γ₂ (.list (.prod (B 32) (B 32)))) [h₂ : Ext Γ₂ Δ₂]
    (pk₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hpows : Env.get ρ₁ (h₁.wk pows₁) = Env.get ρ₂ (h₂.wk pows₂))
    (hpk : pk₁.eval ρ₁ = pk₂.eval ρ₂)
    (hPowsLen : (Env.get ρ₁ (h₁.wk pows₁)).length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (isAdvPowsC (AuthKindFuels.ofBudget S b).K_on pows₁ pk₁).eval ρ₁ =
      (isAdvPowsC b.q_total pows₂ pk₂).eval ρ₂ := by
  let F := AuthKindFuels.ofBudget S b
  have hKon : F.K_on = min b.q_total F.M_on := rfl
  simp only [isAdvPowsC, bindV, Comp.eval]
  refine bind_congr_eq (queryPrim_eval_congr .pow8 pk₁ ρ₁ pk₂ ρ₂ hpk) fun w _ => ?_
  congr 1
  rw [eAny, hKon, anyB_min_eval_eq b.q_total F.M_on _ _ (.cons w ρ₁)
    (by simpa [v, Expr.eval, Ext.step_wk, Env.get] using hPowsLen)]
  simp [eAny, Expr.eval, v, Ext.step_wk, Ext.refl_wk, hpows]

private theorem koskSenderOkPowsC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Γ₁' Γ₂' Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) (pows₁ : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [h₁₁ : Ext Γ₁ Δ₁] [h₁₂ : Ext Γ₂ Δ₁] (ik₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₁' authStateTy) (pows₂ : Var Γ₂' (.list (.prod (B 32) (B 32))))
    [h₂₁ : Ext Γ₁' Δ₂] [h₂₂ : Ext Γ₂' Δ₂] (ik₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁₁.wk st₁) = Env.get ρ₂ (h₂₁.wk st₂))
    (hpows : Env.get ρ₁ (h₁₂.wk pows₁) = Env.get ρ₂ (h₂₂.wk pows₂))
    (hik : ik₁.eval ρ₁ = ik₂.eval ρ₂)
    (hPrin : (Env.get ρ₁ (h₁₁.wk st₁)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on)
    (hPowsLen : (Env.get ρ₁ (h₁₂.wk pows₁)).length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (koskSenderOkPowsC S (AuthKindFuels.ofBudget S b).K_on st₁ pows₁ ik₁).eval ρ₁ =
      (koskSenderOkPowsC S b.q_total st₂ pows₂ ik₂).eval ρ₂ := by
  simp only [koskSenderOkPowsC, letV, bindV, Comp.eval_letC, Comp.eval, hik]
  refine bind_congr_eq ?_ fun f _ => ?_
  · apply findHonestC_kon_eq S b
    · simpa [Ext.step_wk, Env.get] using hst
    · simp [v, Expr.eval, Ext.refl_wk]
    · simpa [Ext.step_wk, Env.get] using hPrin
  · refine bind_congr_eq ?_ fun _ _ => rfl
    apply isAdvPowsC_kon_eq S b
    · simpa [Ext.step_wk, Env.get] using hpows
    · simp [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    · simpa [Ext.step_wk, Env.get] using hPowsLen

private theorem eAny_kon_eq {a : Ty pqSig} {Γ₁ Γ₂ : List (Ty pqSig)}
    (K M : ℕ) (xs₁ : Expr pqxdhOps Γ₁ (.list a))
    (p₁ : Var (a :: Γ₁) a → Expr pqxdhOps (a :: Γ₁) .bool) (ρ₁ : Env Γ₁)
    (xs₂ : Expr pqxdhOps Γ₂ (.list a))
    (p₂ : Var (a :: Γ₂) a → Expr pqxdhOps (a :: Γ₂) .bool) (ρ₂ : Env Γ₂)
    (hxs : xs₁.eval ρ₁ = xs₂.eval ρ₂)
    (hp : ∀ x, (p₁ .vz).eval (.cons x ρ₁) = (p₂ .vz).eval (.cons x ρ₂))
    (hlen : (xs₁.eval ρ₁).length ≤ M) :
    (eAny (min K M) xs₁ p₁).eval ρ₁ = (eAny K xs₂ p₂).eval ρ₂ := by
  rw [eAny, anyB_min_eval_eq K M _ _ ρ₁ hlen]
  simp only [eAny, Expr.eval, hxs]
  congr 1; funext x; exact hp x

private theorem list_take_kon_eq {α : Type} (S : Setup) (b : QueryBudget) (l : List α)
    (hl : l.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    l.take (AuthKindFuels.ofBudget S b).K_on = l.take b.q_total := by
  change l.take (min b.q_total (AuthKindFuels.ofBudget S b).M_on) = l.take b.q_total
  rw [← List.take_take, List.take_of_length_le hl]

private theorem kyberCheckE_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ : List (Ty pqSig)}
    (used₁ : Expr pqxdhOps Γ₁ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))))
    (entry₁ : Expr pqxdhOps Γ₁ (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) (ρ₁ : Env Γ₁)
    (used₂ : Expr pqxdhOps Γ₂ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))))
    (entry₂ : Expr pqxdhOps Γ₂ (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) (ρ₂ : Env Γ₂)
    (hUsed : used₁.eval ρ₁ = used₂.eval ρ₂)
    (hEntry : entry₁.eval ρ₁ = entry₂.eval ρ₂)
    (hLen : (used₁.eval ρ₁).length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (kyberCheckE (AuthKindFuels.ofBudget S b).K_on used₁ entry₁).eval ρ₁ =
      (kyberCheckE b.q_total used₂ entry₂).eval ρ₂ := by
  simp only [kyberCheckE, eLet2, eLet,
    kyberEq, eAny, eval_natEq, Expr.u32Beq, Expr.bytesBeq,
    v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hUsed, hEntry,
    list_take_kon_eq S b _ (hUsed ▸ hLen)]

private theorem queryPrimC_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (op : _root_.SignalPqxdh.LegacyCosted.PTag)
    (e₁ : Expr pqxdhOps Γ₁ op.dom) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ op.dom) (ρ₂ : Env Γ₂)
    (h : e₁.eval ρ₁ = e₂.eval ρ₂) :
    (Comp.queryPrimC (C := gapDhDdhOracle) op e₁).eval ρ₁ =
      (Comp.queryPrimC (C := gapDhDdhOracle) op e₂).eval ρ₂ := by
  simp only [eval_queryPrimC]
  rw [h]

private theorem twoSideC_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (q₁ : Expr pqxdhOps Γ₁ (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))) (ρ₁ : Env Γ₁)
    (q₂ : Expr pqxdhOps Γ₂ (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))) (ρ₂ : Env Γ₂)
    (h : q₁.eval ρ₁ = q₂.eval ρ₂) :
    (twoSideC q₁).eval ρ₁ = (twoSideC q₂).eval ρ₂ := by
  rw [twoSideC_eval, twoSideC_eval, h]

private theorem twoSideOptC_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (q₁ : Expr pqxdhOps Γ₁ (.opt (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))))
    (ρ₁ : Env Γ₁)
    (q₂ : Expr pqxdhOps Γ₂ (.opt (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))))
    (ρ₂ : Env Γ₂)
    (h : q₁.eval ρ₁ = q₂.eval ρ₂) :
    (twoSideOptC q₁).eval ρ₁ = (twoSideOptC q₂).eval ρ₂ := by
  rw [twoSideOptC_eval, twoSideOptC_eval, h]

private theorem liftChal_gdh_congr {Γ₁ Γ₂ : List (Ty pqSig)} {t : Ty pqSig}
    (c₁ : Comp pqxdhOps pqPrimIface Γ₁ t) (ρ₁ : Env Γ₁)
    (c₂ : Comp pqxdhOps pqPrimIface Γ₂ t) (ρ₂ : Env Γ₂)
    (h : c₁.eval ρ₁ = c₂.eval ρ₂) :
    (Comp.liftChal (C := gapDhDdhOracle) c₁).eval ρ₁ =
      (Comp.liftChal (C := gapDhDdhOracle) c₂).eval ρ₂ := by
  simp only [Comp.eval_liftChal]
  exact congrArg _ h

private theorem eFind_kon_eq {a : Ty pqSig} {Γ₁ Γ₂ : List (Ty pqSig)}
    (K M : ℕ) (xs₁ : Expr pqxdhOps Γ₁ (.list a))
    (p₁ : Var (a :: Γ₁) a → Expr pqxdhOps (a :: Γ₁) .bool) (ρ₁ : Env Γ₁)
    (xs₂ : Expr pqxdhOps Γ₂ (.list a))
    (p₂ : Var (a :: Γ₂) a → Expr pqxdhOps (a :: Γ₂) .bool) (ρ₂ : Env Γ₂)
    (hxs : xs₁.eval ρ₁ = xs₂.eval ρ₂)
    (hp : ∀ x, (p₁ .vz).eval (.cons x ρ₁) = (p₂ .vz).eval (.cons x ρ₂))
    (hlen : (xs₁.eval ρ₁).length ≤ M) :
    (eFind (min K M) xs₁ p₁).eval ρ₁ = (eFind K xs₂ p₂).eval ρ₂ := by
  rw [eFind, findB_min_eval_eq K M _ _ ρ₁ hlen]
  simp only [eFind, Expr.eval, hxs]
  congr 1; funext x; exact hp x

private theorem eMap_kon_eq {a c : Ty pqSig} {Γ₁ Γ₂ : List (Ty pqSig)}
    (K M : ℕ) (xs₁ : Expr pqxdhOps Γ₁ (.list a))
    (f₁ : Var (a :: Γ₁) a → Expr pqxdhOps (a :: Γ₁) c) (ρ₁ : Env Γ₁)
    (xs₂ : Expr pqxdhOps Γ₂ (.list a))
    (f₂ : Var (a :: Γ₂) a → Expr pqxdhOps (a :: Γ₂) c) (ρ₂ : Env Γ₂)
    (hxs : xs₁.eval ρ₁ = xs₂.eval ρ₂)
    (hf : ∀ x, (f₁ .vz).eval (.cons x ρ₁) = (f₂ .vz).eval (.cons x ρ₂))
    (hlen : (xs₁.eval ρ₁).length ≤ M) :
    (eMap (min K M) xs₁ f₁).eval ρ₁ = (eMap K xs₂ f₂).eval ρ₂ := by
  rw [eMap, mapB_min_eval_eq K M _ _ ρ₁ hlen]
  simp only [eMap, Expr.eval, hxs]
  congr 1; funext x; exact hf x

private theorem eq_and_inv_retC {Γ₁ Γ₂ : List (Ty pqSig)} {t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ t₁) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ t₂) (ρ₂ : Env Γ₂)
    (heq : projB (e₁.eval ρ₁) = e₂.eval ρ₂)
    (hp : P (e₁.eval ρ₁)) :
    projB <$> (Comp.ret (I := pqGapDhIface) e₁).eval ρ₁ =
      (Comp.ret (I := pqGapDhIface) e₂).eval ρ₂ ∧
    ∀ b ∈ support ((Comp.ret (I := pqGapDhIface) e₁).eval ρ₁), P b := by
  refine ⟨by simp only [Comp.eval, map_pure, heq], fun b hb => ?_⟩
  simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hb
  exact hb ▸ hp

private theorem eq_and_inv_retC_val {Γ₁ Γ₂ : List (Ty pqSig)} {t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ t₁) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ t₂) (ρ₂ : Env Γ₂)
    (v₁ : t₁.denote) (hv₁ : e₁.eval ρ₁ = v₁)
    (heq : projB v₁ = e₂.eval ρ₂)
    (hp : P v₁) :
    projB <$> (Comp.ret (I := pqGapDhIface) e₁).eval ρ₁ =
      (Comp.ret (I := pqGapDhIface) e₂).eval ρ₂ ∧
    ∀ b ∈ support ((Comp.ret (I := pqGapDhIface) e₁).eval ρ₁), P b := by
  refine ⟨by simp only [Comp.eval, map_pure, hv₁, heq], fun b hb => ?_⟩
  simp only [Comp.eval, support_pure, Set.mem_singleton_iff, hv₁] at hb
  exact hb ▸ hp

private theorem eq_and_inv_letV_l {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ a) (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁)
    (ρ₁ : Env Γ₁) (c₂ : Comp pqxdhOps pqGapDhIface Γ₂ t₂) (ρ₂ : Env Γ₂)
    (val : a.denote) (hval : e₁.eval ρ₁ = val)
    (hk : projB <$> (k₁ .vz).eval (.cons val ρ₁) = c₂.eval ρ₂ ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (letV e₁ k₁).eval ρ₁ = c₂.eval ρ₂ ∧
      ∀ b ∈ support ((letV e₁ k₁).eval ρ₁), P b := by
  simpa only [letV, Comp.eval_letC, hval] using hk

private theorem eq_and_inv_letV {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ a) (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁)
    (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ a) (k₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂)
    (ρ₂ : Env Γ₂)
    (he : e₁.eval ρ₁ = e₂.eval ρ₂)
    (hk : ∀ val : a.denote,
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (letV e₁ k₁).eval ρ₁ = (letV e₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((letV e₁ k₁).eval ρ₁), P b := by
  simp only [letV, Comp.eval_letC, he]
  exact hk (e₂.eval ρ₂)

private theorem eq_and_inv_letV_val {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ a) (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁)
    (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ a) (k₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂)
    (ρ₂ : Env Γ₂)
    (val : a.denote) (he₁ : e₁.eval ρ₁ = val) (he₂ : e₂.eval ρ₂ = val)
    (hk : projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (letV e₁ k₁).eval ρ₁ = (letV e₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((letV e₁ k₁).eval ρ₁), P b := by
  simpa only [letV, Comp.eval_letC, he₁, he₂] using hk

private theorem eq_and_inv_iteC {Γ₁ Γ₂ : List (Ty pqSig)} {t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (c₁ : Expr pqxdhOps Γ₁ .bool) (tr₁ fl₁ : Comp pqxdhOps pqGapDhIface Γ₁ t₁) (ρ₁ : Env Γ₁)
    (c₂ : Expr pqxdhOps Γ₂ .bool) (tr₂ fl₂ : Comp pqxdhOps pqGapDhIface Γ₂ t₂) (ρ₂ : Env Γ₂)
    (hc : c₁.eval ρ₁ = c₂.eval ρ₂)
    (ht : projB <$> tr₁.eval ρ₁ = tr₂.eval ρ₂ ∧ ∀ b ∈ support (tr₁.eval ρ₁), P b)
    (hf : projB <$> fl₁.eval ρ₁ = fl₂.eval ρ₂ ∧ ∀ b ∈ support (fl₁.eval ρ₁), P b) :
    projB <$> (Comp.iteC c₁ tr₁ fl₁).eval ρ₁ = (Comp.iteC c₂ tr₂ fl₂).eval ρ₂ ∧
      ∀ b ∈ support ((Comp.iteC c₁ tr₁ fl₁).eval ρ₁), P b := by
  simp only [Comp.eval, hc]
  cases c₂.eval ρ₂
  · simpa using hf
  · simpa using ht

private theorem eval_u32OfNat {Γ : List (Ty pqSig)} (a : Expr pqxdhOps Γ .nat) (ρ : Env Γ) :
    (Expr.u32OfNat a).eval ρ = pqxdhOps.eval (.inr .ofNat) (a.eval ρ) := rfl

private theorem eval_optU32Eq {Γ : List (Ty pqSig)}
    (a b : Expr pqxdhOps Γ (.opt .u32)) (ρ : Env Γ) :
    (optU32Eq a b).eval ρ =
      match a.eval ρ, b.eval ρ with
      | none, none => true
      | some x, some y => pqxdhOps.eval (.inr .eq) (x, y)
      | _, _ => false := by
  simp only [optU32Eq, eLet2, eLet, eCaseOpt, Expr.u32Beq,
    v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get]
  cases a.eval ρ <;> cases b.eval ρ <;> rfl

private theorem caseOptV_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)} {a t : Ty pqSig}
    (o₁ : Expr pqxdhOps Γ₁ (.opt a)) (n₁ : Comp pqxdhOps pqGapDhIface Γ₁ t)
    (s₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t) (ρ₁ : Env Γ₁)
    (o₂ : Expr pqxdhOps Γ₂ (.opt a)) (n₂ : Comp pqxdhOps pqGapDhIface Γ₂ t)
    (s₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t) (ρ₂ : Env Γ₂)
    (ho : o₁.eval ρ₁ = o₂.eval ρ₂) (hn : n₁.eval ρ₁ = n₂.eval ρ₂)
    (hs : ∀ val, (s₁ .vz).eval (.cons val ρ₁) = (s₂ .vz).eval (.cons val ρ₂)) :
    (caseOptV o₁ n₁ s₁).eval ρ₁ = (caseOptV o₂ n₂ s₂).eval ρ₂ := by
  simp only [caseOptV, Comp.eval, ho]
  cases o₂.eval ρ₂ with
  | none => exact hn
  | some val => exact hs val

private theorem eq_and_inv_caseOptV {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (o₁ : Expr pqxdhOps Γ₁ (.opt a)) (n₁ : Comp pqxdhOps pqGapDhIface Γ₁ t₁)
    (s₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (o₂ : Expr pqxdhOps Γ₂ (.opt a)) (n₂ : Comp pqxdhOps pqGapDhIface Γ₂ t₂)
    (s₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (ho : o₁.eval ρ₁ = o₂.eval ρ₂)
    (hn : projB <$> n₁.eval ρ₁ = n₂.eval ρ₂ ∧ ∀ b ∈ support (n₁.eval ρ₁), P b)
    (hs : ∀ val : a.denote,
      projB <$> (s₁ .vz).eval (.cons val ρ₁) = (s₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((s₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (caseOptV o₁ n₁ s₁).eval ρ₁ = (caseOptV o₂ n₂ s₂).eval ρ₂ ∧
      ∀ b ∈ support ((caseOptV o₁ n₁ s₁).eval ρ₁), P b := by
  simp only [caseOptV, Comp.eval, ho]
  cases o₂.eval ρ₂ with
  | none => simpa using hn
  | some val => simpa using hs val

private theorem eq_and_inv_bindV {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (m₁ : Comp pqxdhOps pqGapDhIface Γ₁ a)
    (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (m₂ : Comp pqxdhOps pqGapDhIface Γ₂ a)
    (k₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (hm : m₁.eval ρ₁ = m₂.eval ρ₂)
    (hk : ∀ val ∈ support (m₁.eval ρ₁),
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (bindV m₁ k₁).eval ρ₁ = (bindV m₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((bindV m₁ k₁).eval ρ₁), P b := by
  simp only [bindV, Comp.eval]
  refine ⟨?_, ?_⟩
  · rw [← hm, map_bind]
    exact bind_congr_support (m₁.eval ρ₁) _ _ fun val hval => (hk val hval).1
  · intro b hb
    rw [mem_support_bind_iff] at hb
    rcases hb with ⟨val, hval, hb⟩
    exact (hk val hval).2 b hb

private theorem map_eq_and_inv_bindV {Γ₁ Γ₂ : List (Ty pqSig)} {a₁ a₂ t₁ t₂ : Ty pqSig}
    (projA : a₁.denote → a₂.denote) (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (m₁ : Comp pqxdhOps pqGapDhIface Γ₁ a₁)
    (k₁ : Var (a₁ :: Γ₁) a₁ → Comp pqxdhOps pqGapDhIface (a₁ :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (m₂ : Comp pqxdhOps pqGapDhIface Γ₂ a₂)
    (k₂ : Var (a₂ :: Γ₂) a₂ → Comp pqxdhOps pqGapDhIface (a₂ :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (hm : projA <$> m₁.eval ρ₁ = m₂.eval ρ₂)
    (hk : ∀ val ∈ support (m₁.eval ρ₁),
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons (projA val) ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (bindV m₁ k₁).eval ρ₁ = (bindV m₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((bindV m₁ k₁).eval ρ₁), P b := by
  simp only [bindV, Comp.eval]
  refine ⟨?_, ?_⟩
  · rw [← hm, bind_map_left, map_bind]
    exact bind_congr_support (m₁.eval ρ₁) _ _ fun val hval => (hk val hval).1
  · intro b hb
    rw [mem_support_bind_iff] at hb
    rcases hb with ⟨val, hval, hb⟩
    exact (hk val hval).2 b hb

private theorem eq_and_inv_letV_eq {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ a) (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁)
    (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ a) (k₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂)
    (ρ₂ : Env Γ₂)
    (he : e₁.eval ρ₁ = e₂.eval ρ₂)
    (hk : ∀ val : a.denote, val = e₁.eval ρ₁ →
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (letV e₁ k₁).eval ρ₁ = (letV e₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((letV e₁ k₁).eval ρ₁), P b := by
  simp only [letV, Comp.eval_letC, ← he]
  exact hk (e₁.eval ρ₁) rfl

private theorem map_eq_and_inv_bindV_joint {Γ₁ Γ₂ : List (Ty pqSig)} {a₁ a₂ t₁ t₂ : Ty pqSig}
    (projA : a₁.denote → a₂.denote) (projB : t₁.denote → t₂.denote)
    (Q : a₁.denote → Prop) (P : t₁.denote → Prop)
    (m₁ : Comp pqxdhOps pqGapDhIface Γ₁ a₁)
    (k₁ : Var (a₁ :: Γ₁) a₁ → Comp pqxdhOps pqGapDhIface (a₁ :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (m₂ : Comp pqxdhOps pqGapDhIface Γ₂ a₂)
    (k₂ : Var (a₂ :: Γ₂) a₂ → Comp pqxdhOps pqGapDhIface (a₂ :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (hm : projA <$> m₁.eval ρ₁ = m₂.eval ρ₂ ∧ ∀ r ∈ support (m₁.eval ρ₁), Q r)
    (hk : ∀ val, Q val →
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons (projA val) ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (bindV m₁ k₁).eval ρ₁ = (bindV m₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((bindV m₁ k₁).eval ρ₁), P b :=
  map_eq_and_inv_bindV projA projB P m₁ k₁ ρ₁ m₂ k₂ ρ₂ hm.1 fun val hval => hk val (hm.2 val hval)

@[reducible] private def putSauxAtom (aux : fgAuthShadowAuxTy.denote)
    (s : (embedTy sessAuxLegTy).denote) : fgAuthShadowAuxTy.denote :=
  (s.1, (s.2.1, (auxFgRoAvl aux, (s.2.2.1, (s.2.2.2, (auxFgRootRoAvl aux, auxRawAvl aux))))))

private theorem putSauxAtom_self (aux : fgAuthShadowAuxTy.denote) :
    putSauxAtom aux (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux))) = aux := by
  rcases aux with ⟨_, _, _, _, _, _, _⟩
  rfl

@[reducible] private def recvStUpdE (K : ℕ) (opk : Bool) {Γs Γk Γc Δ : List (Ty pqSig)}
    (st : Var Γs authStateTy) (kjo : Var Γk (.prod .nat (.prod .nat .nat)))
    (kc : Var Γc (.prod .bool (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))))
    [Ext Γs Δ] [Ext Γk Δ] [Ext Γc Δ] : Expr pqxdhOps Δ authStateTy :=
  if opk then
    stUpd (v st)
      (opks := eMap K (stOpks (v st)) fun e =>
        .ite (nat3Eq (.fst (v e)) (v kjo))
          (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .litBool true))) (v e))
      (usedO := .listCons (v kjo) (stUsedO (v st))) (kyb := .snd (v kc))
  else
    stUpd (v st) (usedN := .listCons (v kjo) (stUsedN (v st))) (kyb := .snd (v kc))

private theorem recvStUpdE_eval_eq (S : Setup) (b : QueryBudget) (opk : Bool)
    {Γs₁ Γk₁ Γc₁ Δ₁ Γs₂ Γk₂ Γc₂ Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γs₁ authStateTy) (kjo₁ : Var Γk₁ (.prod .nat (.prod .nat .nat)))
    (kc₁ : Var Γc₁ (.prod .bool (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))))
    [hs₁ : Ext Γs₁ Δ₁] [hk₁ : Ext Γk₁ Δ₁] [hc₁ : Ext Γc₁ Δ₁] (ρ₁ : Env Δ₁)
    (st₂ : Var Γs₂ authStateTy) (kjo₂ : Var Γk₂ (.prod .nat (.prod .nat .nat)))
    (kc₂ : Var Γc₂ (.prod .bool (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))))
    [hs₂ : Ext Γs₂ Δ₂] [hk₂ : Ext Γk₂ Δ₂] [hc₂ : Ext Γc₂ Δ₂] (ρ₂ : Env Δ₂)
    (st_l : authStateTy.denote) (kjo_l : (Ty.prod .nat (.prod .nat .nat)).denote)
    (kc_l : (Ty.prod .bool (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))).denote)
    (hst₁ : Env.get ρ₁ (hs₁.wk st₁) = st_l) (hst₂ : Env.get ρ₂ (hs₂.wk st₂) = st_l)
    (hkjo₁ : Env.get ρ₁ (hk₁.wk kjo₁) = kjo_l) (hkjo₂ : Env.get ρ₂ (hk₂.wk kjo₂) = kjo_l)
    (hkc₁ : Env.get ρ₁ (hc₁.wk kc₁) = kc_l) (hkc₂ : Env.get ρ₂ (hc₂.wk kc₂) = kc_l)
    (hBaseVal : AuthBaseValOnlineBounded (AuthKindFuels.ofBudget S b).M_on st_l) :
    (recvStUpdE (AuthKindFuels.ofBudget S b).K_on opk st₁ kjo₁ kc₁).eval ρ₁ =
      (recvStUpdE b.q_total opk st₂ kjo₂ kc₂).eval ρ₂ := by
  dsimp only [recvStUpdE]
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte,
      v, Expr.eval, hst₁, hst₂, hkjo₁, hkjo₂, hkc₁, hkc₂]
  · simp only [↓reduceIte, eMap, nat3Eq, nat2Eq, natEq,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get,
      hst₁, hst₂, hkjo₁, hkjo₂, hkc₁, hkc₂,
      list_take_kon_eq S b _ hBaseVal.opkEntries_le]

private theorem recvStUpdE_online (S : Setup) (b : QueryBudget) (opk : Bool) (c0 : ℕ)
    {Γs₁ Γk₁ Γc₁ Δ₁ : List (Ty pqSig)}
    (st₁ : Var Γs₁ authStateTy) (kjo₁ : Var Γk₁ (.prod .nat (.prod .nat .nat)))
    (kc₁ : Var Γc₁ (.prod .bool (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))))
    [hs₁ : Ext Γs₁ Δ₁] [hk₁ : Ext Γk₁ Δ₁] [hc₁ : Ext Γc₁ Δ₁] (ρ₁ : Env Δ₁)
    (st_l st' : authStateTy.denote) (kjo_l : (Ty.prod .nat (.prod .nat .nat)).denote)
    (kc_l : (Ty.prod .bool (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))).denote)
    (hst' : st' = (recvStUpdE (AuthKindFuels.ofBudget S b).K_on opk st₁ kjo₁ kc₁).eval ρ₁)
    (hst₁ : Env.get ρ₁ (hs₁.wk st₁) = st_l)
    (hkjo₁ : Env.get ρ₁ (hk₁.wk kjo₁) = kjo_l)
    (hkc₁ : Env.get ρ₁ (hc₁.wk kc₁) = kc_l)
    (hBaseC0 : AuthBaseValOnlineBounded c0 st_l)
    (hkcLen : kc_l.2.length ≤ st_l.2.2.2.2.2.2.2.2.2.1.length + 1) :
    AuthBaseValOnlineBounded (c0 + 1) st' := by
  subst hst'
  dsimp only [recvStUpdE]
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte, v, Expr.eval, hst₁, hkjo₁, hkc₁]
    exact
      { principals_le        := Nat.le_succ_of_le hBaseC0.principals_le
        spkBundles_le        := Nat.le_succ_of_le hBaseC0.spkBundles_le
        opkEntries_le        := Nat.le_succ_of_le hBaseC0.opkEntries_le
        sessions_le          := Nat.le_succ_of_le hBaseC0.sessions_le
        usedSendSessions_le  := Nat.le_succ_of_le hBaseC0.usedSendSessions_le
        usedRecvOPK_le       := Nat.le_succ_of_le hBaseC0.usedRecvOPK_le
        usedRecvNoOPK_le     := Nat.succ_le_succ hBaseC0.usedRecvNoOPK_le
        seenKyberBaseKeys_le := Nat.le_trans hkcLen (Nat.succ_le_succ hBaseC0.seenKyberBaseKeys_le)
        sentOPKEvents_le     := Nat.le_succ_of_le hBaseC0.sentOPKEvents_le
        sentNoOPKEvents_le   := Nat.le_succ_of_le hBaseC0.sentNoOPKEvents_le
        recvdOPKEvents_le    := Nat.le_succ_of_le hBaseC0.recvdOPKEvents_le
        recvdNoOPKEvents_le  := Nat.le_succ_of_le hBaseC0.recvdNoOPKEvents_le
        advKeys_le           := Nat.le_succ_of_le hBaseC0.advKeys_le }
  · simp only [↓reduceIte, eMap, v, Expr.eval, hst₁, hkjo₁, hkc₁]
    refine
      { principals_le        := Nat.le_succ_of_le hBaseC0.principals_le
        spkBundles_le        := Nat.le_succ_of_le hBaseC0.spkBundles_le
        opkEntries_le        := ?_
        sessions_le          := Nat.le_succ_of_le hBaseC0.sessions_le
        usedSendSessions_le  := Nat.le_succ_of_le hBaseC0.usedSendSessions_le
        usedRecvOPK_le       := Nat.succ_le_succ hBaseC0.usedRecvOPK_le
        usedRecvNoOPK_le     := Nat.le_succ_of_le hBaseC0.usedRecvNoOPK_le
        seenKyberBaseKeys_le := Nat.le_trans hkcLen (Nat.succ_le_succ hBaseC0.seenKyberBaseKeys_le)
        sentOPKEvents_le     := Nat.le_succ_of_le hBaseC0.sentOPKEvents_le
        sentNoOPKEvents_le   := Nat.le_succ_of_le hBaseC0.sentNoOPKEvents_le
        recvdOPKEvents_le    := Nat.le_succ_of_le hBaseC0.recvdOPKEvents_le
        recvdNoOPKEvents_le  := Nat.le_succ_of_le hBaseC0.recvdNoOPKEvents_le
        advKeys_le           := Nat.le_succ_of_le hBaseC0.advKeys_le }
    simp only [List.length_map, List.length_take]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_succ_of_le hBaseC0.opkEntries_le)

private theorem fgRecv_commit_inv {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote}
    {sim_l : fgSimTy.denote} {t : AuthQuery S}
    (hs_emb : embedVal fgSimTy sim_l = sim)
    (hon : authSimPred S 0 t) (hn1 : ¬ authSimPred S 1 t) (hn2 : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux)
    (st'_l : authStateTy.denote)
    (hBaseNew : AuthBaseValOnlineBounded (c 0 + 1) st'_l)
    (newResp_l : respRecTy.denote)
    (fgL' : (Ty.list fgPatchEntryTy).denote)
    (fgSess' : (Ty.list seqFgEntryTy).denote) (fgCtr' : ℕ)
    (rootL' : (Ty.list rootEntryTy).denote)
    (rootSess' : (Ty.list seqRootEntryTy).denote) (rootCtr' : ℕ)
    (hFG : FgTableShadow S b (c 0 + 1) (c 1)
      (embedVal (.list fgPatchEntryTy) fgL') (auxFgRoAvl aux)
      (embedVal (.list seqFgEntryTy) fgSess') fgCtr')
    (hRT : RootTableShadow S b (c 0 + 1) (c 2)
      (embedVal (.list rootEntryTy) rootL') (auxFgRootRoAvl aux)
      (embedVal (.list seqRootEntryTy) rootSess') rootCtr') :
    let sim''_l : fgSimTy.denote :=
      (st'_l, (fgL', (rootL', (sim_l.2.2.2.1, (sim_l.2.2.2.2.1,
        (newResp_l :: sim_l.2.2.2.2.2.1, sim_l.2.2.2.2.2.2))))))
    let saux'_l : sessAuxLegTy.denote :=
      (fgSess', (fgCtr', (rootSess', rootCtr')))
    FgSimShadowInv S b (bumpPred (authSimPred S) c t)
      (embedVal fgSimTy sim''_l) (putSauxAtom aux (embedVal sessAuxLegTy saux'_l)) := by
  intro sim''_l saux'_l
  have hb0 : bumpPred (authSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, hon]
  have hb1 : bumpPred (authSimPred S) c t 1 = c 1 := by simp [bumpPred, hn1]
  have hb2 : bumpPred (authSimPred S) c t 2 = c 2 := by simp [bumpPred, hn2]
  have hPowsEq : (embedVal fgSimTy sim''_l).2.2.2.2.2.2 = sim.2.2.2.2.2.2 := by
    change (embedVal fgSimTy sim_l).2.2.2.2.2.2 = sim.2.2.2.2.2.2
    exact congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.2.2) hs_emb
  have hRespEq : (embedVal fgSimTy sim''_l).2.2.2.2.2.1 =
      embedVal respRecTy newResp_l :: sim.2.2.2.2.2.1 := by
    change embedVal respRecTy newResp_l :: (embedVal fgSimTy sim_l).2.2.2.2.2.1 =
      embedVal respRecTy newResp_l :: sim.2.2.2.2.2.1
    exact congrArg (embedVal respRecTy newResp_l :: ·)
      (congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.2.1) hs_emb)
  have hLogEq : (embedVal fgSimTy sim''_l).2.2.2.2.1 = sim.2.2.2.2.1 := by
    change (embedVal fgSimTy sim_l).2.2.2.2.1 = sim.2.2.2.2.1
    exact congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.1) hs_emb
  have hRawEq : (embedVal fgSimTy sim''_l).2.2.2.1 = sim.2.2.2.1 := by
    change (embedVal fgSimTy sim_l).2.2.2.1 = sim.2.2.2.1
    exact congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.1) hs_emb
  refine
    { counter_inv := hInv.counter_inv.bump t hroom
      base_online := by
        change AuthBaseAtomOnlineBounded _ (embedVal authStateTy st'_l)
        exact hb0 ▸ (AuthBaseAtomOnlineBounded.iff_embedVal st'_l).mpr hBaseNew
      pows_len    := by rw [hPowsEq, hb0]; exact Nat.le_succ_of_le hInv.pows_len
      resp_len    := by
        rw [hRespEq, hb0, List.length_cons]
        exact Nat.succ_le_succ hInv.resp_len
      log_len     := by rw [hLogEq, hb1]; exact hInv.log_len
      fg_shadow   := by
        change FgTableShadow S b _ _ (embedVal (.list fgPatchEntryTy) fgL') (auxFgRoAvl aux)
          (embedVal (.list seqFgEntryTy) fgSess') fgCtr'
        simpa only [hb0, hb1] using hFG
      root_shadow := by
        change RootTableShadow S b _ _ (embedVal (.list rootEntryTy) rootL') (auxFgRootRoAvl aux)
          (embedVal (.list seqRootEntryTy) rootSess') rootCtr'
        simpa only [hb0, hb2] using hRT
      raw_rel     := by
        have hRawAux : auxRawAvl (putSauxAtom aux (embedVal sessAuxLegTy saux'_l)) = auxRawAvl aux := rfl
        rw [hRawEq, hRawAux]; exact hInv.raw_rel
      raw_len     := by rw [hRawEq, hb1]; exact hInv.raw_len }

set_option maxHeartbeats 1600000 in
private theorem fgRecvShadowB_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (vsim : Var Γ₁ fgSimTy) (vx : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (sim_l : fgSimTy.denote) (saux_l : sessAuxLegTy.denote) (x_l : recvQTy.denote)
    (sim : (embedTy fgSimTy).denote) (aux : fgAuthShadowAuxTy.denote)
    (hsim : Env.get env (h₁.wk vsim) = sim_l)
    (hx : Env.get env (h₂.wk vx) = x_l)
    (hs_emb : embedVal fgSimTy sim_l = sim)
    (hsaux_emb : embedVal sessAuxLegTy saux_l =
      (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux))))
    (hon : authSimPred S 0 t)
    (hn1 : ¬ authSimPred S 1 t)
    (hn2 : ¬ authSimPred S 2 t)
    (hbound : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux) :
    let F := AuthKindFuels.ofBudget S b
    ((fun r => (r.1, r.2.1)) <$>
      (fgRecvShadowB S F opk).eval (.cons (sim_l, (saux_l, x_l)) .nil)) =
    (fgRecvB S b.q_total opk vsim vx).eval env ∧
    ∀ out ∈ support ((fgRecvShadowB S F opk).eval (.cons (sim_l, (saux_l, x_l)) .nil)),
      FgSimShadowInv S b (bumpPred (authSimPred S) c t)
        (embedVal fgSimTy out.2.1) (putSauxAtom aux (embedVal sessAuxLegTy out.2.2)) := by
  let F := AuthKindFuels.ofBudget S b
  let dropSaux : (Ty.prod authRespTy (.prod fgSimTy sessAuxLegTy)).denote → RSF.denote :=
    fun r => (r.1, r.2.1)
  let P : (Ty.prod authRespTy (.prod fgSimTy sessAuxLegTy)).denote → Prop :=
    fun out => FgSimShadowInv S b (bumpPred (authSimPred S) c t)
      (embedVal fgSimTy out.2.1) (putSauxAtom aux (embedVal sessAuxLegTy out.2.2))
  let newResp_l : respRecTy.denote :=
    ((x_l.1, x_l.2.1), (x_l.2.2.2.1.1, x_l.2.2.2.1.2.1))
  let sim'_l : fgSimTy.denote :=
    (sim_l.1, (sim_l.2.1, (sim_l.2.2.1, (sim_l.2.2.2.1, (sim_l.2.2.2.2.1,
      (newResp_l :: sim_l.2.2.2.2.2.1, sim_l.2.2.2.2.2.2))))))
  have hAbort : ∀ r : authRespTy.denote, P (r, (sim'_l, saux_l)) := by
    intro r
    dsimp only [P]
    have hSim' : embedVal fgSimTy sim'_l =
        (sim.1, (sim.2.1, (sim.2.2.1, (sim.2.2.2.1, (sim.2.2.2.2.1,
          (embedVal respRecTy newResp_l :: sim.2.2.2.2.2.1, sim.2.2.2.2.2.2)))))) := by
      rw [← hs_emb]; rfl
    rw [hSim', hsaux_emb, putSauxAtom_self]
    exact hInv.bump_resp_cons (embedVal respRecTy newResp_l) t hon hroom
  have hBaseEq : embedVal authStateTy sim_l.1 = sim.1 := congrArg Prod.fst hs_emb
  have hBaseC0 : AuthBaseValOnlineBounded (c 0) sim_l.1 :=
    (AuthBaseAtomOnlineBounded.iff_embedVal sim_l.1).mp (hBaseEq ▸ hInv.base_online)
  have hBaseVal : AuthBaseValOnlineBounded F.M_on sim_l.1 :=
    AuthBaseValOnlineBounded.mono (hbound 0) hBaseC0
  have hPowsLen : sim_l.2.2.2.2.2.2.length ≤ F.M_on := by
    have hp : (embedVal (.list (.prod (B 32) (B 32))) sim_l.2.2.2.2.2.2).length =
        sim.2.2.2.2.2.2.length :=
      congrArg List.length (congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.2.2) hs_emb)
    rw [embedVal_length] at hp
    exact Nat.le_trans (hp ▸ hInv.pows_len) (hbound 0)
  have hStep := hInv.counter_inv.online_step_bounds hon hroom
  have hFgSh : FgTableShadow S b (c 0) (c 1)
      (embedVal (.list fgPatchEntryTy) sim_l.2.1) (auxFgRoAvl aux)
      (embedVal (.list seqFgEntryTy) saux_l.1) saux_l.2.1 := by
    have h1 : embedVal (.list fgPatchEntryTy) sim_l.2.1 = sim.2.1 :=
      congrArg (fun g : (embedTy fgSimTy).denote => g.2.1) hs_emb
    have h2 : embedVal (.list seqFgEntryTy) saux_l.1 = auxFgSess aux :=
      congrArg Prod.fst hsaux_emb
    have h3 : saux_l.2.1 = auxFgCtr aux :=
      congrArg (fun s : (embedTy sessAuxLegTy).denote => s.2.1) hsaux_emb
    rw [h1, h2, h3]; exact hInv.fg_shadow
  have hRtSh : RootTableShadow S b (c 0) (c 2)
      (embedVal (.list rootEntryTy) sim_l.2.2.1) (auxFgRootRoAvl aux)
      (embedVal (.list seqRootEntryTy) saux_l.2.2.1) saux_l.2.2.2 := by
    have h1 : embedVal (.list rootEntryTy) sim_l.2.2.1 = sim.2.2.1 :=
      congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.1) hs_emb
    have h2 : embedVal (.list seqRootEntryTy) saux_l.2.2.1 = auxFgRootSess aux :=
      congrArg (fun s : (embedTy sessAuxLegTy).denote => s.2.2.1) hsaux_emb
    have h3 : saux_l.2.2.2 = auxFgRootCtr aux :=
      congrArg (fun s : (embedTy sessAuxLegTy).denote => s.2.2.2) hsaux_emb
    rw [h1, h2, h3]; exact hInv.root_shadow
  dsimp only [fgRecvShadowB, fgRecvB, fgRecvShadowC, fgRecvC]
  refine eq_and_inv_letV_l dropSaux P _ _ _ _ _ sim_l rfl ?_
  refine eq_and_inv_letV_l dropSaux P _ _ _ _ _ saux_l rfl ?_
  refine eq_and_inv_letV_l dropSaux P _ _ _ _ _ x_l rfl ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ sim'_l rfl
    (by simp only [sim'_l, newResp_l, v, Expr.eval, hsim, hx]) ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ sim_l.1 rfl rfl ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ sim_l.2.2.2.2.2.2 rfl rfl ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ x_l.2.2.2 rfl
    (by simp only [v, Expr.eval, Ext.step_wk, Var.vs, Env.get, hx]) ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ x_l.2.2.2.1 rfl rfl ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ (x_l.1, (x_l.2.1, x_l.2.2.1)) rfl
    (by simp only [v, Expr.eval, Ext.step_wk, Var.vs, Env.get, hx]) ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _
    (by
      dsimp only [Expr.eval]
      congr 1
      refine congrArg₂ Bool.and ?_ rfl
      refine congrArg₂ Bool.and ?_ rfl
      refine congrArg₂ Bool.and ?_ rfl
      cases opk <;>
        simp only [Bool.false_eq_true, ↓reduceIte, eval_optU32Eq, Expr.u32Beq, eval_u32OfNat,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hx])
    (eq_and_inv_retC dropSaux P _ _ _ _ (by rfl) (hAbort _)) ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _
    (by cases opk
        · exact eAny_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl (fun _ => rfl) hBaseVal.usedRecvNoOPK_le
        · exact eAny_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl (fun _ => rfl) hBaseVal.usedRecvOPK_le)
    (eq_and_inv_retC dropSaux P _ _ _ _ (by rfl) (hAbort _)) ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
    (liftChal_gdh_congr _ _ _ _
      (koskSenderOkPowsC_kon_eq S b Var.vz Var.vz _ _ Var.vz Var.vz _ _
        rfl rfl rfl hBaseVal.principals_le hPowsLen))
    fun ok _ => ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC dropSaux P _ _ _ _ (by rfl) (hAbort _)) ?_
  refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _
    (eFind_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl
      (fun _ => by simp only [eval_natEq, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hx])
      hBaseVal.principals_le)
    (eq_and_inv_retC dropSaux P _ _ _ _ (by rfl) (hAbort _)) fun kE => ?_
  refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _
    (eFind_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl
      (fun _ => by simp only [nat2Eq, eval_natEq, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hx])
      hBaseVal.spkBundles_le)
    (eq_and_inv_retC dropSaux P _ _ _ _ (by rfl) (hAbort _)) fun bE => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
    (by
      cases opk
      · rfl
      · simp only [↓reduceIte]
        apply caseOptV_eval_congr
        · refine eFind_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl (fun _ => rfl) ?_
          exact hBaseVal.opkEntries_le
        · rfl
        · intro _; rfl)
    fun oChk _ => ?_
  refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC dropSaux P _ _ _ _ (by rfl) (hAbort _)) fun oKey => ?_
  refine eq_and_inv_letV_eq dropSaux P _ _ _ _ _ _
    (kyberCheckE_kon_eq S b _ _ _ _ _ _ rfl
      (by simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hx])
      hBaseVal.seenKyberBaseKeys_le)
    fun kc hkc => ?_
  have hkcLen : kc.2.length ≤ sim_l.1.2.2.2.2.2.2.2.2.2.1.length + 1 := by
    rw [hkc]
    simp only [kyberCheckE, eLet2, eLet,
      eAny, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get]
    split <;> simp
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun can _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun canE _ => ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC_val dropSaux P _ _ _ _ (.inl (), (sim'_l, saux_l))
      (by simp only [aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
      (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
      (hAbort _)) ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun ss? _ => ?_
  refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC_val dropSaux P _ _ _ _ (.inl (), (sim'_l, saux_l))
      (by simp only [aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
      (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
      (hAbort _)) fun ss => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideOptC_eval_congr _ _ _ _ rfl) fun p4 _ => ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun kE' => ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun bE' => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideC_eval_congr _ _ _ _ rfl) fun p1 _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideC_eval_congr _ _ _ _ rfl) fun p2 _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideC_eval_congr _ _ _ _ rfl) fun p3 _ => ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun pk => ?_
  apply map_eq_and_inv_bindV_joint
  · refine patchWithShadowC_sim (S := S) (b := b) (nOn := c 0) (nRo := c 1)
      Var.vz Var.vz _ _ _ _ _ _ (auxFgRoAvl aux) ?_ ?_ hStep.2.1 ?_
    · rfl
    · rfl
    · exact hFgSh
  · intro dkL hDkL
    refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideC_eval_congr _ _ _ _ rfl) fun posR _ => ?_
    apply map_eq_and_inv_bindV_joint
    · refine rootPatchWithShadowC_sim (S := S) (b := b) (nOn := c 0) (nRoot := c 2)
        _ _ _ _ _ _ _ _ _ _ (auxFgRootRoAvl aux) ?_ ?_ ?_ hStep.2.2.1 ?_
      · rfl
      · rfl
      · rfl
      · exact hRtSh
    · intro rkOut hRkOut
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun mkSeed _ => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun ck11 _ => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun sp? _ => ?_
      refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _ rfl
        (eq_and_inv_retC_val dropSaux P _ _ _ _ (.inl (), (sim'_l, saux_l))
          (by simp only [aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (hAbort _)) fun sp => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun mk _ => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
        (queryPrimC_eval_congr _ _ _ _ _
          (by simp only [firstMsgADE_evalHs, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get]))
        fun pt? _ => ?_
      refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _ rfl
        (eq_and_inv_retC_val dropSaux P _ _ _ _ (.inl (), (sim'_l, saux_l))
          (by simp only [aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (hAbort _)) fun pt => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
        (liftChal_gdh_congr _ _ _ _
          (findHonestC_kon_eq S b Var.vz _ _ Var.vz _ _
            (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
            (by simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
            hBaseVal.principals_le))
        fun snd? _ => ?_
      refine eq_and_inv_letV_eq dropSaux P _ _ _ _ _ _
        (recvStUpdE_eval_eq S b opk _ _ _ _ _ _ _ _
          sim_l.1 (x_l.1, (x_l.2.1, x_l.2.2.1)) kc
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          hBaseVal)
        fun st' hst' => ?_
      have hBaseNew : AuthBaseValOnlineBounded (c 0 + 1) st' :=
        recvStUpdE_online S b opk (c 0) _ _ _ _
          sim_l.1 st' (x_l.1, (x_l.2.1, x_l.2.2.1)) kc hst'
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          (by simp only [Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
          hBaseC0 hkcLen
      let sim''_l : fgSimTy.denote :=
        (st', (dkL.2.1, (rkOut.2.1, (sim_l.2.2.2.1, (sim_l.2.2.2.2.1,
          (newResp_l :: sim_l.2.2.2.2.2.1, sim_l.2.2.2.2.2.2))))))
      let saux'_l : sessAuxLegTy.denote := (dkL.2.2.1, (dkL.2.2.2, rkOut.2.2))
      let resp_l : authRespTy.denote :=
        match snd? with
        | none => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (dkL.1, (rkOut.1.1, (ck11, pt)))))))))))
        | some _ => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
      exact eq_and_inv_retC_val dropSaux P _ _ _ _ (resp_l, (sim''_l, saux'_l))
        (by cases snd? <;> simp only [resp_l, sim''_l, sim'_l, saux'_l,
          eCaseOpt, aRecvHonest, aRecvUnfresh,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
        (by cases snd? <;> simp only [resp_l, sim''_l, sim'_l, dropSaux,
          eCaseOpt, aRecvHonest, aRecvUnfresh,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
        (fgRecv_commit_inv hs_emb hon hn1 hn2 hroom hInv st' hBaseNew newResp_l
          dkL.2.1 dkL.2.2.1 dkL.2.2.2 rkOut.2.1 rkOut.2.2.1 rkOut.2.2.2 hDkL hRkOut)

private theorem oracleComp_bind_pure_eq_map {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (mx : OracleComp spec α) (f : α → β) :
    (mx >>= fun a => pure (f a)) = f <$> mx := by
  rw [map_eq_bind_pure_comp]
  rfl

private theorem oracleComp_map_map {ι : Type} {spec : OracleSpec ι} {α β γ : Type}
    (f : α → β) (g : β → γ) (mx : OracleComp spec α) :
    g <$> (f <$> mx) = (fun x => g (f x)) <$> mx :=
  Functor.map_map f g mx

private theorem embed_bind_liftGdhToSign (sigB : ℕ)
    (mx : OracleComp _ (authRespTy.denote × fgSimTy.denote)) :
    (embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
      ((liftGdhToSign mx : OracleComp AuthSigDdhSpec _) >>= fun x => pure (x.1, x.2, sigB))) =
    ((fun x => (embedVal authRespTy x.1, (embedVal fgSimTy x.2, sigB))) <$>
      (liftGdhToSign mx : OracleComp AuthSigDdhSpec _)) := by
  rw [oracleComp_bind_pure_eq_map, oracleComp_map_map]
  rfl

theorem fgArmSim_recvOPK (S : Setup) (b : QueryBudget) :
    FgArmSim S b
      (fun p => AuthQuery.recvOPK p.1 p.2.1 p.2.2.1 p.2.2.2)
      (armEval_recvOPK S b) := by
  intro c pa sim sigB aux p t hbound hroom hInv
  rcases p with ⟨u, j, o, msg⟩
  let F := AuthKindFuels.ofBudget S b
  let pa_l := projVal a1gParams2Ty pa
  let sim_l := projVal fgSimTy sim
  let saux_atom : (embedTy sessAuxLegTy).denote :=
    (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux)))
  let saux_l := projVal sessAuxLegTy saux_atom
  let x_l : recvQTy.denote :=
    (u.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))
  have hx_l : projVal recvQTy (u.val, (j.val, (o.val, preKeyMsgV msg))) = x_l := by
    rcases msg with ⟨⟨_, _, _, _ | _, _, _⟩, _, _, _⟩ <;> rfl
  let mxSign : OracleComp AuthSigDdhSpec
      (authRespTy.denote × fgSimTy.denote × sessAuxLegTy.denote) :=
    liftGdhToSign ((fgRecvShadowB S F true).eval (.cons (sim_l, (saux_l, x_l)) .nil))
  have hArm : armEval_recvOPK S b pa sim sigB aux (u, (j, (o, msg))) =
      (fun out => (embedVal authRespTy out.1,
        ((embedVal fgSimTy out.2.1, sigB), putSauxAtom aux (embedVal sessAuxLegTy out.2.2)))) <$>
        mxSign := by
    simp only [armEval_recvOPK, fgCoreArm_recv, Comp.eval, Expr.eval, Env.get, pure_bind]
    rw [liftGdh1_eval]
    have hArg : projVal (.prod fgSimTy (.prod sessAuxLegTy recvQTy))
        ((Expr.pair (exprRename Var.succ (.var (.succ (.succ .zero))))
          (.pair (auxSessSliceE (.snd .v0)) (exprRename Var.succ (.var .zero)))).eval
          (Env.cons (t := .prod .nat fgAuthShadowAuxTy) (sigB, aux)
            (.cons (t := authRecvQAtomicTy) (u.val, (j.val, (o.val, preKeyMsgV msg)))
              (.cons pa (.cons sim (.cons (t := .nat) sigB (.cons aux .nil))))))) =
        (sim_l, (saux_l, x_l)) := by
      dsimp only [exprRename, auxSessSliceE, auxFgSessE, auxFgCtrE, auxFgRootSessE, auxFgRootCtrE,
        Expr.eval, Env.get]
      exact congrArg (fun z => (sim_l, (saux_l, z))) hx_l
    rw [hArg]
    refine (bind_map_left (embedVal (.prod authRespTy (.prod fgSimTy sessAuxLegTy)))
      mxSign _).trans ?_
    exact oracleComp_bind_pure_eq_map mxSign _
  have hon : authSimPred S 0 t := trivial
  have hn1 : ¬ authSimPred S 1 t := fun h => nomatch h
  have hn2 : ¬ authSimPred S 2 t := fun h => nomatch h
  refine ⟨?_, ?_⟩
  · rw [hArm, oracleComp_map_map]
    let q_l := (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t
    have hLeg : legacyCoreArmEval S b pa sim sigB t =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval (.cons pa_l (.cons sim_l (.cons (t := .nat) sigB (.cons q_l .nil)))) := by
      rw [← mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
      unfold legacyCoreArmEval
      congr 1
      dsimp only [embedEnv, pa_l, sim_l, q_l]
      rw [embedVal_projVal, embedVal_projVal, authQenc_eq t]
      rfl
    rw [hLeg]
    dsimp only [legacyCoreArmComp, a1gPre2C, fgStep2C,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      bindV, caseSumV, v, q_l, t]
    simp only [Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vz, Env.get_vs,
      pure_bind, liftGdhComp_eval]
    rw [embed_bind_liftGdhToSign sigB]
    rw [← (fgRecvShadowB_sim S b true _ _ _ c t
      sim_l saux_l x_l sim aux rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).1, liftGdhToSign_map, oracleComp_map_map]
    rfl
  · intro pOut hpOut
    rw [hArm] at hpOut
    have hpImg := Eq.mp (congrArg (pOut ∈ ·) (support_map _ _)) hpOut
    rcases hpImg with ⟨out, houtSign, rfl⟩
    have hSim2 := (fgRecvShadowB_sim S b true
      (.zero : Var [fgSimTy, recvQTy] fgSimTy)
      (.succ .zero : Var [fgSimTy, recvQTy] recvQTy)
      (.cons sim_l (.cons x_l .nil)) c t sim_l saux_l x_l sim aux rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).2
    exact hSim2 out (mem_support_liftGdhToSign houtSign)

theorem fgArmSim_recvNoOPK (S : Setup) (b : QueryBudget) :
    FgArmSim S b
      (fun p => AuthQuery.recvNoOPK p.1 p.2.1 p.2.2.1 p.2.2.2)
      (armEval_recvNoOPK S b) := by
  intro c pa sim sigB aux p t hbound hroom hInv
  rcases p with ⟨u, j, l, msg⟩
  let F := AuthKindFuels.ofBudget S b
  let pa_l := projVal a1gParams2Ty pa
  let sim_l := projVal fgSimTy sim
  let saux_atom : (embedTy sessAuxLegTy).denote :=
    (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux)))
  let saux_l := projVal sessAuxLegTy saux_atom
  let x_l : recvQTy.denote :=
    (u.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))
  have hx_l : projVal recvQTy (u.val, (j.val, (l.val, preKeyMsgV msg))) = x_l := by
    rcases msg with ⟨⟨_, _, _, _ | _, _, _⟩, _, _, _⟩ <;> rfl
  let mxSign : OracleComp AuthSigDdhSpec
      (authRespTy.denote × fgSimTy.denote × sessAuxLegTy.denote) :=
    liftGdhToSign ((fgRecvShadowB S F false).eval (.cons (sim_l, (saux_l, x_l)) .nil))
  have hArm : armEval_recvNoOPK S b pa sim sigB aux (u, (j, (l, msg))) =
      (fun out => (embedVal authRespTy out.1,
        ((embedVal fgSimTy out.2.1, sigB), putSauxAtom aux (embedVal sessAuxLegTy out.2.2)))) <$>
        mxSign := by
    simp only [armEval_recvNoOPK, fgCoreArm_recv, Comp.eval, Expr.eval, Env.get, pure_bind]
    rw [liftGdh1_eval]
    have hArg : projVal (.prod fgSimTy (.prod sessAuxLegTy recvQTy))
        ((Expr.pair (exprRename Var.succ (.var (.succ (.succ .zero))))
          (.pair (auxSessSliceE (.snd .v0)) (exprRename Var.succ (.var .zero)))).eval
          (Env.cons (t := .prod .nat fgAuthShadowAuxTy) (sigB, aux)
            (.cons (t := authRecvQAtomicTy) (u.val, (j.val, (l.val, preKeyMsgV msg)))
              (.cons pa (.cons sim (.cons (t := .nat) sigB (.cons aux .nil))))))) =
        (sim_l, (saux_l, x_l)) := by
      dsimp only [exprRename, auxSessSliceE, auxFgSessE, auxFgCtrE, auxFgRootSessE, auxFgRootCtrE,
        Expr.eval, Env.get]
      exact congrArg (fun z => (sim_l, (saux_l, z))) hx_l
    rw [hArg]
    refine (bind_map_left (embedVal (.prod authRespTy (.prod fgSimTy sessAuxLegTy)))
      mxSign _).trans ?_
    exact oracleComp_bind_pure_eq_map mxSign _
  have hon : authSimPred S 0 t := trivial
  have hn1 : ¬ authSimPred S 1 t := fun h => nomatch h
  have hn2 : ¬ authSimPred S 2 t := fun h => nomatch h
  refine ⟨?_, ?_⟩
  · rw [hArm, oracleComp_map_map]
    let q_l := (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t
    have hLeg : legacyCoreArmEval S b pa sim sigB t =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval (.cons pa_l (.cons sim_l (.cons (t := .nat) sigB (.cons q_l .nil)))) := by
      rw [← mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
      unfold legacyCoreArmEval
      congr 1
      dsimp only [embedEnv, pa_l, sim_l, q_l]
      rw [embedVal_projVal, embedVal_projVal, authQenc_eq t]
      rfl
    rw [hLeg]
    dsimp only [legacyCoreArmComp, a1gPre2C, fgStep2C,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      bindV, caseSumV, v, q_l, t]
    simp only [Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vz, Env.get_vs,
      pure_bind, liftGdhComp_eval]
    rw [embed_bind_liftGdhToSign sigB]
    rw [← (fgRecvShadowB_sim S b false _ _ _ c t
      sim_l saux_l x_l sim aux rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).1, liftGdhToSign_map, oracleComp_map_map]
    rfl
  · intro pOut hpOut
    rw [hArm] at hpOut
    have hpImg := Eq.mp (congrArg (pOut ∈ ·) (support_map _ _)) hpOut
    rcases hpImg with ⟨out, houtSign, rfl⟩
    have hSim2 := (fgRecvShadowB_sim S b false
      (.zero : Var [fgSimTy, recvQTy] fgSimTy)
      (.succ .zero : Var [fgSimTy, recvQTy] recvQTy)
      (.cons sim_l (.cons x_l .nil)) c t sim_l saux_l x_l sim aux rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).2
    exact hSim2 out (mem_support_liftGdhToSign houtSign)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRecv
