/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimMisc
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRo
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRoRoot
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec

/-!
# Forgetful Step Simulation for One-Key `Auth` Gap-DH and EUF-CMA Reductions

Assembles the per-arm `FgArmSim` contracts into handler step simulations for `a1g2KindProg` and
`a1s2KindProg`, yielding `a1g2KindProg_forgetSim` and `a1s2KindProg_forgetSim`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimA

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Expr Comp Env Iface CostedReduction pqAtomicSig pqAtomicOps PB bundleV)
open _root_.Computational.Proofs.ReductionDsl.StepSim (ForgetSim bumpPred)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal embedEnv projVal embedVal_projVal projVal_embedVal
   exprRename exprRename_eval compRename compRename_eval
   mapExpr mapExpr_eval mapComp mapComp_eval comp_queries_zero_of_zero
   tlAuthSigDdh liftAuthHandle liftAuthHandle_eval liftAuth1Stage authQenc_eq)
open _root_.SignalPqxdh
  (Setup QueryBudget AuthQuery PreKeyBundleInput PreKeyMsg Bytes)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface pqSigAndDdhIface)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface authCodec preKeyMsgV)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy authQueryTy authRespTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext v letV bindV caseSumV
   eCaseSum eCaseOpt eFind natEq isSomeE stPrin peCorrupted aNone
   sendQTy recvQTy fgSimTy a1gParams2Ty a1g2StTy a1sStTy a1sRS
   fsBase pa2Role
   fgSend2C fgRecvB a1gPre2C fgStep2C a1gStep2C a1g2HandleDsl
   a1sG a1sTp a1sTpk a1sFg a1sMk a1sCaseAPa2
   a1sSendCheckC a1sPreC a1sDelegate2C a1sStep2C a1sHandle2Dsl
   fgAuth1KeyGapDhProg sigAuth1KeyDslProg)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (aop avlTy avlRootE avlShapeE avlKvE orBoolE
   avlSearchB192C avlSearchPair32C avlInsertAtPathC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec
  (avlInsertAtPathC_eval_congr)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels authSendQAtomicTy authRecvQAtomicTy authRespAtomicTy authQueryAtomicTy
   aNoneAtomicE aDrKeyAtomicE aRootKdfAtomicE wk1 wk2 liftExpr1 liftExpr2 dispatchAuthQ)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthBaseAtomOnlineBounded dispatchAuthQEval dispatchAuthQ_eval_qenc)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (fgAuthShadowAuxTy a1g2ShadowStTy a1s2ShadowStTy fgCoreOutTy
   auxFgSessE auxFgCtrE auxFgRoAvlE auxFgRootSessE auxFgRootCtrE auxFgRootRoAvlE auxRawAvlE fgAuxMkE
   auxSessSliceE auxPutSessSliceE
   wk0 liftCs0 liftCs1 liftGdh0 liftGdh1 a1sSendCheckLegC
   simPrependLogE simPrependRawAndLogE simPrependFgAndLogE simPrependRootE
   a1gHaltGuard2E
   fgCoreArm_roQuery fgCoreArm_roRootQuery fgCoreArm_initPrin fgCoreArm_corrupt
   fgCoreArm_genSPK fgCoreArm_genOPK fgCoreArm_send fgCoreArm_recv
   fgCoreArm_revealDh fgCoreArm_registerKey
   a1gWrapCoreArm a1gArm_initPrin a1gArm_corrupt a1gArm_genSPK a1gArm_genOPK
   a1gArm_send a1gArm_recv a1gArm_roQuery a1gArm_roRootQuery a1gArm_revealDh a1gArm_registerKey
   a1sIsFrozenE a1sCaseAPa2AtomicE a1sSimAtomicE a1sSigBAtomicE a1sPutSimSigBE
   a1sDelegateCoreArm a1sWrapNonSendArm
   a1sArm_initPrin a1sArm_corrupt a1sArm_genSPK a1sArm_genOPK a1sArm_send a1sArm_recv
   a1sArm_roQuery a1sArm_roRootQuery a1sArm_revealDh a1sArm_registerKey
   a1g2KindHandle a1s2KindHandle a1g2KindProg a1s2KindProg)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
  (forgetGdh forgetSig gdhOldAtomicProg sigOldAtomicProg
   legacyCoreArmComp FgSimShadowInv GdhAuthInv SigAuthInv
   AuthSigDdhSpec legacyCoreArmEval
   armEval_initPrin armEval_corruptIK armEval_genSPK armEval_genOPK
   armEval_sendOPK armEval_sendNoOPK armEval_recvOPK armEval_recvNoOPK
   armEval_roQuery armEval_roRootQuery armEval_revealDhSecrets armEval_registerKey
   FgArmSim AllFgArmsSim SigSendCheckSim)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimMisc
  (a1g2KindProg_init_sim a1s2KindProg_init_sim a1g2KindProg_finish_sim a1s2KindProg_finish_sim
   fgArmSim_initPrin fgArmSim_corruptIK fgArmSim_genSPK fgArmSim_genOPK
   fgArmSim_revealDhSecrets fgArmSim_registerKey)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRecv
  (fgArmSim_recvOPK fgArmSim_recvNoOPK)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRo
  (fgArmSim_roQuery)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRoRoot
  (fgArmSim_roRootQuery)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimSend
  (sigSendCheckK_sim fgArmSim_sendOPK fgArmSim_sendNoOPK)

private theorem liftExpr1_eval {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] b) (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftExpr1 e argE).eval ρ =
      embedVal b (e.eval (.cons (projVal a (argE.eval ρ)) .nil)) := by
  simp only [liftExpr1, Expr.eval]
  rw [exprRename_eval (mapExpr e) wk1 (.cons (argE.eval ρ) .nil) (.cons (argE.eval ρ) ρ)
    (fun v => by cases v with | zero => rfl | succ w => cases w)]
  have hx : argE.eval ρ = embedVal a (projVal a (argE.eval ρ)) :=
    (embedVal_projVal a (argE.eval ρ)).symm
  conv_lhs => rw [hx]
  exact mapExpr_eval e (.cons (projVal a (argE.eval ρ)) .nil)

private theorem liftExpr2_eval {a b c : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a, b] c)
    (arg0 : Expr pqAtomicOps Γ (embedTy a))
    (arg1 : Expr pqAtomicOps Γ (embedTy b)) (ρ : Env Γ) :
    (liftExpr2 e arg0 arg1).eval ρ =
      embedVal c (e.eval (.cons (projVal a (arg0.eval ρ))
        (.cons (projVal b (arg1.eval ρ)) .nil))) := by
  simp only [liftExpr2, Expr.eval]
  have harg0 : (exprRename Var.succ arg0).eval (.cons (arg1.eval ρ) ρ) = arg0.eval ρ :=
    exprRename_eval arg0 Var.succ ρ (.cons (arg1.eval ρ) ρ) (fun _ => rfl)
  rw [harg0]
  rw [exprRename_eval (mapExpr e) wk2 (.cons (arg0.eval ρ) (.cons (arg1.eval ρ) .nil))
    (.cons (arg0.eval ρ) (.cons (arg1.eval ρ) ρ))
    (fun v => by
      cases v with
      | zero => rfl
      | succ w => cases w with | zero => rfl | succ u => cases u)]
  have hx0 : arg0.eval ρ = embedVal a (projVal a (arg0.eval ρ)) :=
    (embedVal_projVal a (arg0.eval ρ)).symm
  have hx1 : arg1.eval ρ = embedVal b (projVal b (arg1.eval ρ)) :=
    (embedVal_projVal b (arg1.eval ρ)).symm
  conv_lhs => rw [hx0, hx1]
  exact mapExpr_eval e (.cons (projVal a (arg0.eval ρ)) (.cons (projVal b (arg1.eval ρ)) .nil))

private abbrev legHaltGuardE (K : ℕ) : Expr pqxdhOps [a1gParams2Ty, fgSimTy] .bool :=
  eCaseSum (pa2Role (v (.vz : Var [a1gParams2Ty, fgSimTy] a1gParams2Ty)))
    (fun uT =>
      eCaseOpt
        (eFind K (stPrin (fsBase (v (.vs .vz : Var [a1gParams2Ty, fgSimTy] fgSimTy))))
          fun e => natEq (.fst (v e)) (v uT))
        (.litBool false) fun e => peCorrupted (.snd (v e)))
    (fun _ => .litBool false)

private theorem a1gHaltGuard2E_eval_eq (S : Setup) (b : QueryBudget)
    {c : Fin 4 → ℕ} {Γ : List (Ty pqAtomicSig)}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (ρ : Env Γ) {aux : fgAuthShadowAuxTy.denote}
    (hInv : FgSimShadowInv S b c (simE.eval ρ) aux) :
    (a1gHaltGuard2E (AuthKindFuels.ofBudget S b).K_on paE simE).eval ρ =
      (legHaltGuardE b.q_total).eval
        (.cons (projVal a1gParams2Ty (paE.eval ρ))
          (.cons (projVal fgSimTy (simE.eval ρ)) .nil)) := by
  simp only [a1gHaltGuard2E, legHaltGuardE, liftExpr2_eval]
  have hid : (embedVal .bool : Bool → Bool) = id := rfl
  rw [hid, id]
  have hBaseVal : _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.AuthBaseValOnlineBounded
      (c 0) (projVal authStateTy (simE.eval ρ).1) := by
    rw [← AuthBaseAtomOnlineBounded.iff_embedVal, embedVal_projVal]
    exact hInv.base_online
  have hPrinLen := hBaseVal.principals_le
  have hOnLe := hInv.counter_inv.on_le
  have hKon : c 0 ≤ (AuthKindFuels.ofBudget S b).K_on := by
    dsimp only [AuthKindFuels.ofBudget]; omega
  have hQt : c 0 ≤ b.q_total := by omega
  have hProj1 : (projVal fgSimTy (simE.eval ρ)).1 = projVal authStateTy (simE.eval ρ).1 := rfl
  have hTake1 : List.take (AuthKindFuels.ofBudget S b).K_on (projVal authStateTy (simE.eval ρ).1).2.2.1 =
      (projVal authStateTy (simE.eval ρ).1).2.2.1 :=
    List.take_of_length_le (hPrinLen.trans hKon)
  have hTake2 : List.take b.q_total (projVal authStateTy (simE.eval ρ).1).2.2.1 =
      (projVal authStateTy (simE.eval ρ).1).2.2.1 :=
    List.take_of_length_le (hPrinLen.trans hQt)
  simp only [eCaseSum, eCaseOpt, eFind, Expr.findBounded, pa2Role, stPrin, fsBase,
    natEq, peCorrupted, v, Var.vz, Var.vs, Ext.wk, Expr.eval, Env.get, hProj1, hTake1, hTake2]

private theorem compRename_liftGdhComp {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    ∀ {Δ : List (Ty pqSig)} (ξ : ∀ {a}, Var Γ a → Var Δ a),
      compRename ξ (liftGdhComp c) = liftGdhComp (compRename ξ c) := by
  induction c <;> intro Δ ξ <;> simp only [liftGdhComp, compRename, *]
  · rfl
  · rename_i g _
    rcases g with _ | ⟨⟩ <;> rfl

private def gdhGuardRen {Δ : List (Ty pqSig)} {a : Ty pqSig}
    (x : Var [a1gParams2Ty, fgSimTy] a) :
    Var (.nat :: fgSimTy :: a1gParams2Ty :: Δ) a :=
  match x with
  | .zero => .succ (.succ .zero)
  | .succ x => match x with
    | .zero => .succ .zero

private theorem legHaltGuardE_ren (K : ℕ) {Δ : List (Ty pqSig)} :
    exprRename (gdhGuardRen (Δ := Δ)) (legHaltGuardE K) =
    (eCaseSum (pa2Role (v (.zero : Var (a1gParams2Ty :: Δ) _)))
      (fun uT =>
        eCaseOpt
          (eFind K (stPrin (fsBase (v (.zero : Var (fgSimTy :: a1gParams2Ty :: Δ) _))))
            fun e => natEq (.fst (v e)) (v uT))
          (.litBool false) fun e => peCorrupted (.snd (v e)))
      (fun _ => .litBool false) :
        Expr pqxdhOps (.nat :: fgSimTy :: a1gParams2Ty :: Δ) .bool) := rfl

private def gdhStepRen {Γq Δ : List (Ty pqSig)} [hq : Ext Γq Δ] (q : Var Γq authQueryTy)
    {a : Ty pqSig} (x : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] a) :
    Var (.nat :: fgSimTy :: a1gParams2Ty :: Δ) a :=
  match x with
  | .zero => .succ (.succ .zero)
  | .succ x => match x with
    | .zero => .succ .zero
    | .succ x => match x with
      | .zero => .zero
      | .succ x => match x with
        | .zero => .succ (.succ (.succ (hq.wk q)))

private theorem a1gPre2C_ren (K : ℕ) {Γq Δ : List (Ty pqSig)} [hq : Ext Γq Δ]
    (q : Var Γq authQueryTy) :
    let pa₀   : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] a1gParams2Ty := .zero
    let sim₀  : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] fgSimTy := .succ .zero
    let sigB₀ : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] .nat := .succ (.succ .zero)
    let q₀    : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] authQueryTy := .succ (.succ (.succ .zero))
    compRename (gdhStepRen q)
      (a1gPre2C K (Δ := [a1gParams2Ty, fgSimTy, .nat, authQueryTy]) pa₀ sim₀ sigB₀ q₀) =
    a1gPre2C K (Δ := .nat :: fgSimTy :: a1gParams2Ty :: Δ)
      (.zero : Var (a1gParams2Ty :: Δ) _)
      (.zero : Var (fgSimTy :: a1gParams2Ty :: Δ) _)
      (.zero : Var (.nat :: fgSimTy :: a1gParams2Ty :: Δ) _)
      q := rfl

private abbrev a1gPreOutTy : Ty pqSig :=
  .sum (.prod authRespTy (.prod fgSimTy .nat)) .unit

private def gdhStepRen2 {Γq Δ : List (Ty pqSig)} [hq : Ext Γq Δ] (q : Var Γq authQueryTy)
    {a : Ty pqSig}
    (x : Var (.unit :: a1gPreOutTy :: [a1gParams2Ty, fgSimTy, .nat, authQueryTy]) a) :
    Var (.unit :: a1gPreOutTy :: .nat :: fgSimTy :: a1gParams2Ty :: Δ) a :=
  match x with
  | .zero => .zero
  | .succ x => match x with
    | .zero => .succ .zero
    | .succ x => .succ (.succ (gdhStepRen q x))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
private theorem fgStep2C_ren (S : Setup) (K : ℕ) {Γq Δ : List (Ty pqSig)} [hq : Ext Γq Δ]
    (q : Var Γq authQueryTy) :
    let pa₀  : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] a1gParams2Ty := .zero
    let sim₀ : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] fgSimTy := .succ .zero
    let q₀   : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] authQueryTy := .succ (.succ (.succ .zero))
    compRename (gdhStepRen2 q)
      (fgStep2C S K (Δ := .unit :: a1gPreOutTy :: [a1gParams2Ty, fgSimTy, .nat, authQueryTy])
        pa₀ sim₀ q₀) =
    fgStep2C S K (Δ := .unit :: a1gPreOutTy :: .nat :: fgSimTy :: a1gParams2Ty :: Δ)
      (.zero : Var (a1gParams2Ty :: Δ) _)
      (.zero : Var (fgSimTy :: a1gParams2Ty :: Δ) _)
      q := rfl

private theorem a1gStep2C_eval_split (S : Setup) (b : QueryBudget)
    {Γs Γq Δ : List (Ty pqSig)} [hst : Ext Γs Δ] [hq : Ext Γq Δ]
    (st : Var Γs a1g2StTy) (q : Var Γq authQueryTy) (env : Env Δ) :
    let stv := env.get (hst.wk st)
    let qv  := env.get (hq.wk q)
    (a1gStep2C S b.q_total (Δ := Δ) st q).eval env =
      if (legHaltGuardE b.q_total).eval (.cons stv.1.1 (.cons stv.1.2 .nil)) = true then
        pure ((aNone (Γ := [a1g2StTy])).eval (.cons stv .nil), stv)
      else
        (fun out => (out.1, ((stv.1.1, out.2.1), out.2.2))) <$>
          (legacyCoreArmComp S b).eval
            (.cons stv.1.1 (.cons stv.1.2 (.cons stv.2 (.cons qv .nil)))) := by
  intro stv qv
  simp only [a1gStep2C, letV, Comp.letC, Comp.eval, pure_bind]
  let env' : Env (.nat :: fgSimTy :: a1gParams2Ty :: Δ) :=
    .cons stv.2 (.cons stv.1.2 (.cons stv.1.1 env))
  have hEnv :
      Env.cons (((Expr.snd (v st)).eval (Env.cons (((Expr.snd (Expr.fst (v st))).eval
        (Env.cons (((Expr.fst (Expr.fst (v st))).eval env)) env)))
        (Env.cons (((Expr.fst (Expr.fst (v st))).eval env)) env))))
        (Env.cons (((Expr.snd (Expr.fst (v st))).eval
          (Env.cons (((Expr.fst (Expr.fst (v st))).eval env)) env)))
          (Env.cons (((Expr.fst (Expr.fst (v st))).eval env)) env)) = env' := rfl
  rw [hEnv]
  have hGuard :
      (eCaseSum (pa2Role (v (.zero : Var (a1gParams2Ty :: Δ) _)))
        (fun uT =>
          eCaseOpt
            (eFind b.q_total (stPrin (fsBase (v (.zero : Var (fgSimTy :: a1gParams2Ty :: Δ) _))))
              fun e => natEq (.fst (v e)) (v uT))
            (.litBool false) fun e => peCorrupted (.snd (v e)))
        (fun _ => .litBool false)).eval env' =
      (legHaltGuardE b.q_total).eval (.cons stv.1.1 (.cons stv.1.2 .nil)) := by
    rw [← legHaltGuardE_ren b.q_total (Δ := Δ)]
    exact exprRename_eval (legHaltGuardE b.q_total) (gdhGuardRen (Δ := Δ))
      (.cons stv.1.1 (.cons stv.1.2 .nil)) env'
      (fun w => by cases w with | zero => rfl | succ u => cases u with | zero => rfl | succ z => nomatch z)
  rw [hGuard]
  split
  · simp only [Expr.eval, aNone, v, Ext.wk]; rfl
  · let ρ₀ : Env [a1gParams2Ty, fgSimTy, .nat, authQueryTy] :=
      .cons stv.1.1 (.cons stv.1.2 (.cons stv.2 (.cons qv .nil)))
    let pa₀   : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] a1gParams2Ty := .zero
    let sim₀  : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] fgSimTy := .succ .zero
    let sigB₀ : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] .nat := .succ (.succ .zero)
    let q₀    : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] authQueryTy := .succ (.succ (.succ .zero))
    have hPre :
        (a1gPre2C b.q_total (Δ := .nat :: fgSimTy :: a1gParams2Ty :: Δ)
          (.zero : Var (a1gParams2Ty :: Δ) _)
          (.zero : Var (fgSimTy :: a1gParams2Ty :: Δ) _)
          (.zero : Var (.nat :: fgSimTy :: a1gParams2Ty :: Δ) _) q).eval env' =
        (a1gPre2C b.q_total (Δ := [a1gParams2Ty, fgSimTy, .nat, authQueryTy])
          pa₀ sim₀ sigB₀ q₀).eval ρ₀ := by
      rw [← a1gPre2C_ren b.q_total q]
      exact compRename_eval _ (gdhStepRen q) ρ₀ env' (fun w => by
        cases w with
        | zero => rfl
        | succ w => cases w with
          | zero => rfl
          | succ w => cases w with
            | zero => rfl
            | succ w => cases w with | zero => rfl | succ z => nomatch z)
    simp only [legacyCoreArmComp, bindV, caseSumV, Comp.caseSumC, Comp.eval, map_bind]
    rw [hPre]
    refine bind_congr fun pre => ?_
    cases pre with
    | inl r =>
      simp only [Expr.eval, v, Ext.wk, Env.get, map_pure]; rfl
    | inr u =>
      simp only [Expr.eval, v, Ext.wk, Env.get, map_bind]
      have hStep :
          (liftGdhComp (fgStep2C S b.q_total
            (Δ := .unit :: a1gPreOutTy :: .nat :: fgSimTy :: a1gParams2Ty :: Δ)
            (.zero : Var (a1gParams2Ty :: Δ) _)
            (.zero : Var (fgSimTy :: a1gParams2Ty :: Δ) _) q)).eval
            (.cons u (.cons (Sum.inr u) env')) =
          (liftGdhComp (fgStep2C S b.q_total
            (Δ := .unit :: a1gPreOutTy :: [a1gParams2Ty, fgSimTy, .nat, authQueryTy])
            pa₀ sim₀ q₀)).eval (.cons u (.cons (Sum.inr u) ρ₀)) := by
        rw [← fgStep2C_ren S b.q_total q, ← compRename_liftGdhComp]
        exact compRename_eval _ (gdhStepRen2 q)
          (.cons u (.cons (Sum.inr u) ρ₀)) (.cons u (.cons (Sum.inr u) env'))
          (fun w => by
            cases w with
            | zero => rfl
            | succ w => cases w with
              | zero => rfl
              | succ w => cases w with
                | zero => rfl
                | succ w => cases w with
                  | zero => rfl
                  | succ w => cases w with
                    | zero => rfl
                    | succ w => cases w with | zero => rfl | succ z => nomatch z)
      rw [hStep]
      refine bind_congr fun r => ?_
      simp only [map_pure]; rfl

private theorem legacyCoreArmEval_eq_map (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (t : AuthQuery S) :
    legacyCoreArmEval S b pa sim sigB t =
      embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
        (legacyCoreArmComp S b).eval
          (.cons (projVal a1gParams2Ty pa)
            (.cons (projVal fgSimTy sim)
              (.cons sigB (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)))) := by
  dsimp only [legacyCoreArmEval]
  have hpa : pa = embedVal a1gParams2Ty (projVal a1gParams2Ty pa) :=
    (embedVal_projVal a1gParams2Ty pa).symm
  have hsim : sim = embedVal fgSimTy (projVal fgSimTy sim) :=
    (embedVal_projVal fgSimTy sim).symm
  have hsigB : sigB = embedVal .nat sigB := rfl
  conv_lhs => rw [hpa, hsim, hsigB, authQenc_eq t]
  exact mapComp_eval tlAuthSigDdh (legacyCoreArmComp S b)
    (comp_queries_zero_of_zero (fun _ => rfl) _)
    (.cons (projVal a1gParams2Ty pa) (.cons (projVal fgSimTy sim)
      (.cons sigB (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil))))

private theorem exprRename_succ_eval {a b : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ b) (x : a.denote) (ρ : Env Γ) :
    (exprRename Var.succ e).eval (.cons x ρ) = e.eval ρ :=
  exprRename_eval e Var.succ ρ (.cons x ρ) (fun _ => rfl)

private theorem liftCs0_eval {b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [] b) (ρ : Env Γ) :
    (liftCs0 c).eval ρ = (mapComp tlAuthSigDdh c).eval .nil :=
  compRename_eval (mapComp tlAuthSigDdh c) wk0 .nil ρ (fun v => nomatch v)

private theorem liftCs1_eval {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] b)
    (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftCs1 c e).eval ρ = (mapComp tlAuthSigDdh c).eval (.cons (e.eval ρ) .nil) := by
  simp only [liftCs1, Comp.eval, pure_bind]
  exact compRename_eval (mapComp tlAuthSigDdh c) wk1 (.cons (e.eval ρ) .nil) (.cons (e.eval ρ) ρ)
    (fun v => by cases v with | zero => rfl | succ w => nomatch w)

private theorem liftGdh0_eval {b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [] b) (ρ : Env Γ) :
    (liftGdh0 c).eval ρ = (mapComp tlAuthSigDdh (liftGdhComp c)).eval .nil :=
  liftCs0_eval (liftGdhComp c) ρ

private theorem liftGdh1_eval {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] b)
    (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftGdh1 c e).eval ρ = (mapComp tlAuthSigDdh (liftGdhComp c)).eval (.cons (e.eval ρ) .nil) :=
  liftCs1_eval (liftGdhComp c) e ρ

private theorem avlSearchB192C_eval_nil {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (_root_.ReductionDsl.B 192) V))
    (keyE : Expr pqAtomicOps Γ (_root_.ReductionDsl.B 192)) (ρ : Env Γ) :
    (avlSearchB192C (I := I) cap tblE keyE).eval ρ =
      (avlSearchB192C (I := I) cap (.var .zero) (.var (.succ .zero))).eval
        (.cons (tblE.eval ρ) (.cons (keyE.eval ρ) .nil)) := by
  simp only [avlSearchB192C, Comp.eval, Expr.eval, pure_bind, Env.get,
    Expr.v0, Expr.v1, Expr.v2, avlRootE, avlShapeE, avlKvE, aop]

private theorem avlSearchPair32C_eval_nil {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32))) (ρ : Env Γ) :
    (avlSearchPair32C (I := I) cap tblE keyE).eval ρ =
      (avlSearchPair32C (I := I) cap (.var .zero) (.var (.succ .zero))).eval
        (.cons (tblE.eval ρ) (.cons (keyE.eval ρ) .nil)) := by
  simp only [avlSearchPair32C, Comp.eval, Expr.eval, pure_bind, Env.get,
    Expr.v0, Expr.v1, Expr.v2, avlRootE, avlShapeE, avlKvE, aop, orBoolE]

private theorem fgCoreArm_roQuery_eval_congr (F : AuthKindFuels)
    {Γ₁ Γ₂ : List (Ty pqAtomicSig)}
    (simE₁ : Expr pqAtomicOps Γ₁ (embedTy fgSimTy)) (sigBE₁ : Expr pqAtomicOps Γ₁ .nat)
    (auxE₁ : Expr pqAtomicOps Γ₁ fgAuthShadowAuxTy) (secE₁ : Expr pqAtomicOps Γ₁ (PB 192))
    (ρ₁ : Env Γ₁)
    (simE₂ : Expr pqAtomicOps Γ₂ (embedTy fgSimTy)) (sigBE₂ : Expr pqAtomicOps Γ₂ .nat)
    (auxE₂ : Expr pqAtomicOps Γ₂ fgAuthShadowAuxTy) (secE₂ : Expr pqAtomicOps Γ₂ (PB 192))
    (ρ₂ : Env Γ₂)
    (hSim : simE₁.eval ρ₁ = simE₂.eval ρ₂) (hSigB : sigBE₁.eval ρ₁ = sigBE₂.eval ρ₂)
    (hAux : auxE₁.eval ρ₁ = auxE₂.eval ρ₂) (hSec : secE₁.eval ρ₁ = secE₂.eval ρ₂) :
    (fgCoreArm_roQuery F simE₁ sigBE₁ auxE₁ secE₁).eval ρ₁ =
      (fgCoreArm_roQuery F simE₂ sigBE₂ auxE₂ secE₂).eval ρ₂ := by
  simp only [fgCoreArm_roQuery, Comp.eval, Expr.eval, pure_bind, Env.get,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, aop,
    liftGdh1_eval, liftGdh0_eval, avlSearchB192C_eval_nil, avlInsertAtPathC_eval_congr,
    aDrKeyAtomicE, simPrependLogE, simPrependRawAndLogE, simPrependFgAndLogE,
    liftExpr1_eval, liftExpr2_eval,
    fgAuxMkE, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE, auxFgRootCtrE,
    auxFgRootRoAvlE, auxRawAvlE, hSim, hSigB, hAux, hSec]

private theorem fgCoreArm_roRootQuery_eval_congr (F : AuthKindFuels)
    {Γ₁ Γ₂ : List (Ty pqAtomicSig)}
    (simE₁ : Expr pqAtomicOps Γ₁ (embedTy fgSimTy)) (sigBE₁ : Expr pqAtomicOps Γ₁ .nat)
    (auxE₁ : Expr pqAtomicOps Γ₁ fgAuthShadowAuxTy)
    (inpE₁ : Expr pqAtomicOps Γ₁ (.prod (PB 32) (PB 32))) (ρ₁ : Env Γ₁)
    (simE₂ : Expr pqAtomicOps Γ₂ (embedTy fgSimTy)) (sigBE₂ : Expr pqAtomicOps Γ₂ .nat)
    (auxE₂ : Expr pqAtomicOps Γ₂ fgAuthShadowAuxTy)
    (inpE₂ : Expr pqAtomicOps Γ₂ (.prod (PB 32) (PB 32))) (ρ₂ : Env Γ₂)
    (hSim : simE₁.eval ρ₁ = simE₂.eval ρ₂) (hSigB : sigBE₁.eval ρ₁ = sigBE₂.eval ρ₂)
    (hAux : auxE₁.eval ρ₁ = auxE₂.eval ρ₂) (hInp : inpE₁.eval ρ₁ = inpE₂.eval ρ₂) :
    (fgCoreArm_roRootQuery F simE₁ sigBE₁ auxE₁ inpE₁).eval ρ₁ =
      (fgCoreArm_roRootQuery F simE₂ sigBE₂ auxE₂ inpE₂).eval ρ₂ := by
  simp only [fgCoreArm_roRootQuery, Comp.eval, Expr.eval, pure_bind, Env.get,
    Expr.v0, Expr.v1, Expr.v2, Expr.v4, Expr.v5, aop,
    liftGdh1_eval, liftGdh0_eval, avlSearchPair32C_eval_nil, avlInsertAtPathC_eval_congr,
    aRootKdfAtomicE, simPrependRootE, liftExpr1_eval, liftExpr2_eval,
    fgAuxMkE, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE, auxFgRootCtrE,
    auxFgRootRoAvlE, auxRawAvlE, hSim, hSigB, hAux, hInp]

private theorem fgCoreArm_send_eval_congr (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ₁ Γ₂ : List (Ty pqAtomicSig)}
    (paE₁ : Expr pqAtomicOps Γ₁ (embedTy a1gParams2Ty))
    (simE₁ : Expr pqAtomicOps Γ₁ (embedTy fgSimTy)) (sigBE₁ : Expr pqAtomicOps Γ₁ .nat)
    (auxE₁ : Expr pqAtomicOps Γ₁ fgAuthShadowAuxTy) (xE₁ : Expr pqAtomicOps Γ₁ authSendQAtomicTy)
    (ρ₁ : Env Γ₁)
    (paE₂ : Expr pqAtomicOps Γ₂ (embedTy a1gParams2Ty))
    (simE₂ : Expr pqAtomicOps Γ₂ (embedTy fgSimTy)) (sigBE₂ : Expr pqAtomicOps Γ₂ .nat)
    (auxE₂ : Expr pqAtomicOps Γ₂ fgAuthShadowAuxTy) (xE₂ : Expr pqAtomicOps Γ₂ authSendQAtomicTy)
    (ρ₂ : Env Γ₂)
    (hPa : paE₁.eval ρ₁ = paE₂.eval ρ₂) (hSim : simE₁.eval ρ₁ = simE₂.eval ρ₂)
    (hSigB : sigBE₁.eval ρ₁ = sigBE₂.eval ρ₂) (hAux : auxE₁.eval ρ₁ = auxE₂.eval ρ₂)
    (hX : xE₁.eval ρ₁ = xE₂.eval ρ₂) :
    (fgCoreArm_send S F opk paE₁ simE₁ sigBE₁ auxE₁ xE₁).eval ρ₁ =
      (fgCoreArm_send S F opk paE₂ simE₂ sigBE₂ auxE₂ xE₂).eval ρ₂ := by
  dsimp only [fgCoreArm_send]
  simp only [Comp.eval, Expr.eval, pure_bind, Env.get, Expr.v0, Expr.v1,
    exprRename_succ_eval, liftGdh1_eval, auxSessSliceE, auxPutSessSliceE,
    fgAuxMkE, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE, auxFgRootCtrE,
    auxFgRootRoAvlE, auxRawAvlE, hPa, hSim, hSigB, hAux, hX]

private theorem fgCoreArm_recv_eval_congr (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ₁ Γ₂ : List (Ty pqAtomicSig)}
    (simE₁ : Expr pqAtomicOps Γ₁ (embedTy fgSimTy)) (sigBE₁ : Expr pqAtomicOps Γ₁ .nat)
    (auxE₁ : Expr pqAtomicOps Γ₁ fgAuthShadowAuxTy) (xE₁ : Expr pqAtomicOps Γ₁ authRecvQAtomicTy)
    (ρ₁ : Env Γ₁)
    (simE₂ : Expr pqAtomicOps Γ₂ (embedTy fgSimTy)) (sigBE₂ : Expr pqAtomicOps Γ₂ .nat)
    (auxE₂ : Expr pqAtomicOps Γ₂ fgAuthShadowAuxTy) (xE₂ : Expr pqAtomicOps Γ₂ authRecvQAtomicTy)
    (ρ₂ : Env Γ₂)
    (hSim : simE₁.eval ρ₁ = simE₂.eval ρ₂) (hSigB : sigBE₁.eval ρ₁ = sigBE₂.eval ρ₂)
    (hAux : auxE₁.eval ρ₁ = auxE₂.eval ρ₂) (hX : xE₁.eval ρ₁ = xE₂.eval ρ₂) :
    (fgCoreArm_recv S F opk simE₁ sigBE₁ auxE₁ xE₁).eval ρ₁ =
      (fgCoreArm_recv S F opk simE₂ sigBE₂ auxE₂ xE₂).eval ρ₂ := by
  dsimp only [fgCoreArm_recv]
  simp only [Comp.eval, Expr.eval, pure_bind, Env.get, Expr.v0, Expr.v1,
    exprRename_succ_eval, liftGdh1_eval, auxSessSliceE, auxPutSessSliceE,
    fgAuxMkE, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE, auxFgRootCtrE,
    auxFgRootRoAvlE, auxRawAvlE, hSim, hSigB, hAux, hX]

private theorem a1gWrapCoreArm_sim (S : Setup) (b : QueryBudget)
    {Payload : Type} {X : Ty pqAtomicSig}
    {mkQ : Payload → AuthQuery S}
    {armEvalNew : (embedTy a1gParams2Ty).denote → (embedTy fgSimTy).denote → ℕ →
      fgAuthShadowAuxTy.denote → Payload → OracleComp AuthSigDdhSpec fgCoreOutTy.denote}
    (hArm : FgArmSim S b mkQ armEvalNew)
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface [X, a1g2ShadowStTy, authQueryAtomicTy] fgCoreOutTy)
    (c : Fin 4 → ℕ) (s' : a1g2ShadowStTy.denote) (x : Payload) (xVal : X.denote)
    (q : AuthQuery S) (hq : q = mkQ x)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j q → c j + 1 ≤ authSimBounds b j)
    (hInv : GdhAuthInv S b c s')
    (hCore : core.eval (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil))) =
      armEvalNew s'.1.1.1 s'.1.1.2 s'.1.2 s'.2 x) :
    Prod.map id forgetGdh <$>
        (a1gWrapCoreArm (AuthKindFuels.ofBudget S b) .v1 core).eval
          (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil))) =
      (gdhOldAtomicProg S b).handle.eval (.cons (forgetGdh s') (.cons ((authCodec S).qenc q) .nil)) ∧
    ∀ p ∈ support ((a1gWrapCoreArm (AuthKindFuels.ofBudget S b) .v1 core).eval
        (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil)))),
      GdhAuthInv S b (bumpPred (authSimPred S) c q) p.2 := by
  subst hq
  let ρ : Env [X, a1g2ShadowStTy, authQueryAtomicTy] :=
    .cons xVal (.cons s' (.cons ((authCodec S).qenc (mkQ x)) .nil))
  have hs1 : forgetGdh s' = embedVal a1g2StTy (projVal a1g2StTy s'.1) :=
    (embedVal_projVal a1g2StTy s'.1).symm
  have hOld :
      (gdhOldAtomicProg S b).handle.eval
        (.cons (forgetGdh s') (.cons ((authCodec S).qenc (mkQ x)) .nil)) =
      embedVal (.prod authRespTy a1g2StTy) <$>
        (a1g2HandleDsl S b.q_total).eval
          (.cons (projVal a1g2StTy s'.1)
            (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (mkQ x)) .nil)) := by
    dsimp only [gdhOldAtomicProg, liftAuth1Stage, fgAuth1KeyGapDhProg]
    rw [hs1]
    exact liftAuthHandle_eval tlAuthSigDdh S (fun _ => rfl) (a1g2HandleDsl S b.q_total)
      (projVal a1g2StTy s'.1) (mkQ x)
  rw [hOld]
  dsimp only [a1g2HandleDsl]
  rw [a1gStep2C_eval_split S b]
  have hGet0 :
      ((Env.cons (projVal a1g2StTy s'.1)
        (Env.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (mkQ x)) Env.nil) :
          Env [a1g2StTy, authQueryTy]).get Var.zero) = projVal a1g2StTy s'.1 := rfl
  have hGet1 :
      ((Env.cons (projVal a1g2StTy s'.1)
        (Env.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (mkQ x)) Env.nil) :
          Env [a1g2StTy, authQueryTy]).get Var.zero.succ) =
        (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (mkQ x) := rfl
  have hProjPa : (projVal a1g2StTy s'.1).1.1 = projVal a1gParams2Ty s'.1.1.1 := rfl
  have hProjSim : (projVal a1g2StTy s'.1).1.2 = projVal fgSimTy s'.1.1.2 := rfl
  have hProjSigB : (projVal a1g2StTy s'.1).2 = s'.1.2 := rfl
  have hGuardEq :
      (a1gHaltGuard2E (AuthKindFuels.ofBudget S b).K_on
        (.fst (.fst (.fst (.v1 : Expr pqAtomicOps [X, a1g2ShadowStTy, authQueryAtomicTy] a1g2ShadowStTy))))
        (.snd (.fst (.fst .v1)))).eval
          (.cons xVal (.cons s' (.cons ((authCodec S).qenc (mkQ x)) .nil))) =
      (legHaltGuardE b.q_total).eval
        (.cons (projVal a1gParams2Ty s'.1.1.1) (.cons (projVal fgSimTy s'.1.1.2) .nil)) :=
    a1gHaltGuard2E_eval_eq S b _ _ ρ hInv
  dsimp only [Ext.wk, Var.vz, Var.vs, a1gWrapCoreArm]
  simp only [hGet0, hGet1, hProjPa, hProjSim, hProjSigB, Comp.eval, hGuardEq]
  split
  · refine ⟨?_, ?_⟩
    · simp only [Expr.eval, Expr.v1, Env.get, aNoneAtomicE, aNone, map_pure, Prod.map, id]
      rw [hs1]; rfl
    · intro p hp
      simp only [Expr.eval, Expr.v1, Env.get, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hInv.bump_unchanged (mkQ x) hroom
  · let ρ₁ : Env (Ty.prod a1g2ShadowStTy .unit :: [X, a1g2ShadowStTy, authQueryAtomicTy]) :=
      .cons (s', ()) ρ
    have hRen :
        (compRename Var.succ core).eval ρ₁ =
          armEvalNew s'.1.1.1 s'.1.1.2 s'.1.2 s'.2 x := by
      rw [compRename_eval core Var.succ ρ ρ₁ (fun _ => rfl)]
      exact hCore
    obtain ⟨hMapArm, hSupArm⟩ := hArm c s'.1.1.1 s'.1.1.2 s'.1.2 s'.2 x hc hroom hInv
    change Prod.map id forgetGdh <$>
        ((compRename Var.succ core).eval ρ₁ >>= fun r =>
          pure (r.1, ((s'.1.1.1, r.2.1.1), r.2.1.2), r.2.2)) = _ ∧
      ∀ p ∈ support ((compRename Var.succ core).eval ρ₁ >>= fun r =>
        pure (r.1, ((s'.1.1.1, r.2.1.1), r.2.1.2), r.2.2)), _
    rw [hRen]
    refine ⟨?_, ?_⟩
    · have hFactor :
          (Prod.map id forgetGdh <$>
            (armEvalNew s'.1.1.1 s'.1.1.2 s'.1.2 s'.2 x >>= fun r =>
              pure (r.1, ((s'.1.1.1, r.2.1.1), r.2.1.2), r.2.2))) =
          (fun q => (q.1, ((s'.1.1.1, q.2.1), q.2.2))) <$>
            (Prod.map id Prod.fst <$> armEvalNew s'.1.1.1 s'.1.1.2 s'.1.2 s'.2 x) := by
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
          Prod.map, id, forgetGdh]
      rw [hFactor, hMapArm, legacyCoreArmEval_eq_map]
      erw [Functor.map_map, Functor.map_map]
      congr 1; funext out
      have hpa : embedVal a1gParams2Ty (projVal a1gParams2Ty s'.1.1.1) = s'.1.1.1 :=
        embedVal_projVal a1gParams2Ty s'.1.1.1
      exact congrArg (fun p => (embedVal authRespTy out.1, ((p, embedVal fgSimTy out.2.1), out.2.2)))
        hpa.symm
    · intro p hp
      rw [mem_support_bind_iff] at hp
      rcases hp with ⟨out, hout, hp⟩
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hSupArm out hout

private theorem a1g2KindHandle_step_of_arms (S : Setup) (b : QueryBudget)
    (hArms : AllFgArmsSim S b)
    (c : Fin 4 → ℕ) (s' : a1g2ShadowStTy.denote) (t : AuthQuery S)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : GdhAuthInv S b c s') :
    Prod.map id forgetGdh <$>
        (a1g2KindProg S b).handle.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (gdhOldAtomicProg S b).handle.eval
        (.cons (forgetGdh s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((a1g2KindProg S b).handle.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))),
      GdhAuthInv S b (bumpPred (authSimPred S) c t) p.2 := by
  have hDisp :
      (a1g2KindProg S b).handle.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
        dispatchAuthQEval (.cons s' (.cons ((authCodec S).qenc t) .nil)) t
          (a1gArm_initPrin (AuthKindFuels.ofBudget S b))
          (a1gArm_corrupt (AuthKindFuels.ofBudget S b))
          (a1gArm_genSPK (AuthKindFuels.ofBudget S b))
          (a1gArm_genOPK (AuthKindFuels.ofBudget S b))
          (a1gArm_send S (AuthKindFuels.ofBudget S b) true)
          (a1gArm_send S (AuthKindFuels.ofBudget S b) false)
          (a1gArm_recv S (AuthKindFuels.ofBudget S b) true)
          (a1gArm_recv S (AuthKindFuels.ofBudget S b) false)
          (a1gArm_roQuery (AuthKindFuels.ofBudget S b))
          (a1gArm_roRootQuery (AuthKindFuels.ofBudget S b))
          (a1gArm_revealDh (AuthKindFuels.ofBudget S b))
          (a1gArm_registerKey (AuthKindFuels.ofBudget S b)) :=
    dispatchAuthQ_eval_qenc .v1 (.cons s' (.cons ((authCodec S).qenc t) .nil)) t rfl
      _ _ _ _ _ _ _ _ _ _ _ _
  rw [hDisp]
  generalize hρ :
    (Env.cons s' (Env.cons ((authCodec S).qenc t) Env.nil) :
      Env [a1g2ShadowStTy, authQueryAtomicTy]) = ρ
  cases t with
  | initPrin u =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_initPrin]
    subst hρ
    refine a1gWrapCoreArm_sim (X := .nat) S b hArms.initPrin
      (fgCoreArm_initPrin (AuthKindFuels.ofBudget S b)
        (.fst (.fst (.fst .v1))) (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' u u.val (.initPrin u) rfl hc hroom hInv ?_
    simp only [fgCoreArm_initPrin, armEval_initPrin, Comp.eval, Expr.eval, pure_bind,
      Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]
  | corruptIK u =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_corrupt]
    subst hρ
    refine a1gWrapCoreArm_sim (X := .nat) S b hArms.corruptIK
      (fgCoreArm_corrupt (AuthKindFuels.ofBudget S b)
        (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' u u.val (.corruptIK u) rfl hc hroom hInv ?_
    simp only [fgCoreArm_corrupt, armEval_corruptIK, Comp.eval, Expr.eval, pure_bind,
      Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]
  | genSPK u j =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_genSPK]
    subst hρ
    refine a1gWrapCoreArm_sim (X := .prod .nat .nat) S b hArms.genSPK
      (fgCoreArm_genSPK (AuthKindFuels.ofBudget S b)
        (.fst (.fst (.fst .v1))) (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' (u, j) (u.val, j.val) (.genSPK u j) rfl hc hroom hInv ?_
    simp only [fgCoreArm_genSPK, armEval_genSPK, Comp.eval, Expr.eval, pure_bind,
      Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftCs1_eval]
  | genOPK u j o =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_genOPK]
    subst hρ
    refine a1gWrapCoreArm_sim (X := .prod .nat (.prod .nat .nat)) S b hArms.genOPK
      (fgCoreArm_genOPK (AuthKindFuels.ofBudget S b)
        (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' (u, j, o) (u.val, (j.val, o.val)) (.genOPK u j o) rfl hc hroom hInv ?_
    simp only [fgCoreArm_genOPK, armEval_genOPK, Comp.eval, Expr.eval, pure_bind,
      Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]
  | sendOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_send]
    subst hρ
    exact a1gWrapCoreArm_sim (X := authSendQAtomicTy) S b hArms.sendOPK
      (fgCoreArm_send S (AuthKindFuels.ofBudget S b) true
        (.fst (.fst (.fst .v1))) (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' (u, i, bu, m0, m1)
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1))))
      (.sendOPK u i bu m0 m1) rfl hc hroom hInv
      (fgCoreArm_send_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl)
  | sendNoOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_send]
    subst hρ
    exact a1gWrapCoreArm_sim (X := authSendQAtomicTy) S b hArms.sendNoOPK
      (fgCoreArm_send S (AuthKindFuels.ofBudget S b) false
        (.fst (.fst (.fst .v1))) (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' (u, i, bu, m0, m1)
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1))))
      (.sendNoOPK u i bu m0 m1) rfl hc hroom hInv
      (fgCoreArm_send_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl)
  | recvOPK k j o msg =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_recv]
    subst hρ
    exact a1gWrapCoreArm_sim (X := authRecvQAtomicTy) S b hArms.recvOPK
      (fgCoreArm_recv S (AuthKindFuels.ofBudget S b) true
        (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' (k, j, o, msg) (k.val, (j.val, (o.val, preKeyMsgV msg)))
      (.recvOPK k j o msg) rfl hc hroom hInv
      (fgCoreArm_recv_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | recvNoOPK k j n msg =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_recv]
    subst hρ
    exact a1gWrapCoreArm_sim (X := authRecvQAtomicTy) S b hArms.recvNoOPK
      (fgCoreArm_recv S (AuthKindFuels.ofBudget S b) false
        (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' (k, j, n, msg) (k.val, (j.val, (n.val, preKeyMsgV msg)))
      (.recvNoOPK k j n msg) rfl hc hroom hInv
      (fgCoreArm_recv_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | roQuery sec =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_roQuery]
    subst hρ
    exact a1gWrapCoreArm_sim (X := PB 192) S b hArms.roQuery
      (fgCoreArm_roQuery (AuthKindFuels.ofBudget S b)
        (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' sec sec (.roQuery sec) rfl hc hroom hInv
      (fgCoreArm_roQuery_eval_congr _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | roRootQuery rk dh =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc,
      a1gArm_roRootQuery]
    subst hρ
    exact a1gWrapCoreArm_sim (X := .prod (PB 32) (PB 32)) S b hArms.roRootQuery
      (fgCoreArm_roRootQuery (AuthKindFuels.ofBudget S b)
        (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' (rk, dh) (rk, dh) (.roRootQuery rk dh) rfl hc hroom hInv
      (fgCoreArm_roRootQuery_eval_congr _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | revealDhSecrets =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1gArm_revealDh]
    subst hρ
    exact a1gWrapCoreArm_sim (X := .unit) S b hArms.revealDhSecrets
      (fgCoreArm_revealDh (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1))
      c s' () () .revealDhSecrets rfl hc hroom hInv rfl
  | registerKey sk =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc,
      a1gArm_registerKey]
    subst hρ
    refine a1gWrapCoreArm_sim (X := PB 32) S b hArms.registerKey
      (fgCoreArm_registerKey (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
      c s' sk sk (.registerKey sk) rfl hc hroom hInv ?_
    simp only [fgCoreArm_registerKey, armEval_registerKey, Comp.eval, Expr.eval, pure_bind,
      Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]

private theorem a1sIsFrozenE_eval_eq {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) (ρ : Env Γ) :
    (a1sIsFrozenE sLegE).eval ρ =
      (isSomeE (a1sFg (.var .vz))).eval (.cons (projVal a1sStTy (sLegE.eval ρ)) .nil) := by
  dsimp only [a1sIsFrozenE]
  rw [liftExpr1_eval]; rfl

private theorem a1sIsFrozenE_false_imp_none {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) (ρ : Env Γ)
    (s1 : (embedTy a1sStTy).denote) (hs : sLegE.eval ρ = s1)
    (hFalse : (a1sIsFrozenE sLegE).eval ρ = false) :
    s1.2.2.2 = none := by
  rw [a1sIsFrozenE_eval_eq, hs] at hFalse
  rcases s1 with ⟨g, tp, tpk, fg⟩
  cases fg with
  | none => rfl
  | some fv =>
    have hTrue : (isSomeE (a1sFg (.var .vz))).eval
        (.cons (projVal a1sStTy (g, tp, tpk, some fv)) .nil) = true := rfl
    rw [hTrue] at hFalse
    cases hFalse

private theorem a1sPutSimSigBE_eval_eq {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy))
    (simSigBE : Expr pqAtomicOps Γ (.prod (embedTy fgSimTy) .nat)) (ρ : Env Γ) :
    (a1sPutSimSigBE sLegE simSigBE).eval ρ =
      embedVal a1sStTy
        ((((projVal a1sStTy (sLegE.eval ρ)).1.1.1, projVal fgSimTy (simSigBE.eval ρ).1),
          (simSigBE.eval ρ).2),
          (projVal a1sStTy (sLegE.eval ρ)).2) := by
  dsimp only [a1sPutSimSigBE]
  rw [liftExpr2_eval]
  rfl

private theorem a1sDelegateCoreArm_sim (S : Setup) (b : QueryBudget)
    {Payload : Type} {Γ : List (Ty pqAtomicSig)} {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    {mkQ : Payload → AuthQuery S}
    {armEvalNew : (embedTy a1gParams2Ty).denote → (embedTy fgSimTy).denote → ℕ →
      fgAuthShadowAuxTy.denote → Payload → OracleComp AuthSigDdhSpec fgCoreOutTy.denote}
    (hArm : FgArmSim S b mkQ armEvalNew)
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy)
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy)
    (ρ : Env Γ) (env : Env Δ)
    (s : Var Γ₁ a1sStTy) (qv : Var Γ₂ authQueryTy)
    (c : Fin 4 → ℕ) (s' : a1s2ShadowStTy.denote) (x : Payload) (q : AuthQuery S)
    (hq : q = mkQ x) (hst : stE.eval ρ = s')
    (hsLeg : env.get (Ext.wk s) = projVal a1sStTy s'.1)
    (hqLeg : env.get (Ext.wk qv) = (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc q)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j q → c j + 1 ≤ authSimBounds b j)
    (hInv : SigAuthInv S b c s')
    (hCore : core.eval ρ =
      armEvalNew ((a1sCaseAPa2AtomicE (.fst stE)).eval ρ) s'.1.1.1.2 s'.1.1.2 s'.2 x) :
    Prod.map id forgetSig <$>
        (a1sDelegateCoreArm (AuthKindFuels.ofBudget S b) stE core).eval ρ =
      embedVal a1sRS <$> (a1sDelegate2C S b.q_total (Δ := Δ) s qv).eval env ∧
    ∀ p ∈ support ((a1sDelegateCoreArm (AuthKindFuels.ofBudget S b) stE core).eval ρ),
      SigAuthInv S b (bumpPred (authSimPred S) c q) p.2 := by
  subst hq
  have hPaProj0 :
      projVal a1gParams2Ty ((a1sCaseAPa2AtomicE (.fst stE)).eval ρ) =
        (a1sCaseAPa2 (a1sTpk (v s)) (a1sTp (v s))).eval env := by
    dsimp only [a1sCaseAPa2AtomicE]
    rw [liftExpr1_eval, projVal_embedVal]
    dsimp only [a1sCaseAPa2, a1sTpk, a1sTp, v, Var.vz, Ext.wk]
    simp only [Expr.eval, Env.get, hst, hsLeg]
  have hInvSim : FgSimShadowInv S b c ((a1sSimAtomicE (.fst stE)).eval ρ) s'.2 := by
    have hSimEval : (a1sSimAtomicE (.fst stE)).eval ρ = s'.1.1.1.2 := by
      simp only [a1sSimAtomicE, Expr.eval, hst]
    rw [hSimEval]; exact hInv
  have hGuardEq0 :
      (a1gHaltGuard2E (AuthKindFuels.ofBudget S b).K_on
        (a1sCaseAPa2AtomicE (.fst stE)) (a1sSimAtomicE (.fst stE))).eval ρ =
      (legHaltGuardE b.q_total).eval
        (.cons (projVal a1gParams2Ty ((a1sCaseAPa2AtomicE (.fst stE)).eval ρ))
          (.cons (projVal fgSimTy s'.1.1.1.2) .nil)) := by
    have hSimEval : (a1sSimAtomicE (.fst stE)).eval ρ = s'.1.1.1.2 := by
      simp only [a1sSimAtomicE, Expr.eval, hst]
    simpa only [hSimEval] using
      a1gHaltGuard2E_eval_eq S b (a1sCaseAPa2AtomicE (.fst stE)) (a1sSimAtomicE (.fst stE)) ρ hInvSim
  dsimp only [a1sDelegateCoreArm]
  generalize hPaVal : (a1sCaseAPa2AtomicE (.fst stE)).eval ρ = paVal at hPaProj0 hGuardEq0 hCore
  let g2Val : a1g2StTy.denote :=
    ((projVal a1gParams2Ty paVal, projVal fgSimTy s'.1.1.1.2), s'.1.1.2)
  have hLetG2 :
      (Expr.pair (.pair (a1sCaseAPa2 (a1sTpk (v s)) (a1sTp (v s))) (.snd (.fst (a1sG (v s)))))
        (.snd (a1sG (v s)))).eval env = g2Val := by
    have h1 : (a1sCaseAPa2 (a1sTpk (v s)) (a1sTp (v s))).eval env = projVal a1gParams2Ty paVal :=
      hPaProj0.symm
    have h2 : (Expr.snd (.fst (a1sG (v s)))).eval env = projVal fgSimTy s'.1.1.1.2 := by
      dsimp only [a1sG, v, Ext.wk]; simp only [Expr.eval, hsLeg]; rfl
    have h3 : (Expr.snd (a1sG (v s))).eval env = s'.1.1.2 := by
      dsimp only [a1sG, v, Ext.wk]; simp only [Expr.eval, hsLeg]; rfl
    exact Prod.ext (Prod.ext h1 h2) h3
  have hDelRhs :
      (a1sDelegate2C S b.q_total (Δ := Δ) s qv).eval env =
        (a1gStep2C S b.q_total (Δ := a1g2StTy :: Δ)
          (.zero : Var (a1g2StTy :: Δ) a1g2StTy) qv).eval (.cons g2Val env) >>= fun r =>
          pure (r.1,
            ((((projVal a1sStTy s'.1).1.1.1, r.2.1.2), r.2.2), (projVal a1sStTy s'.1).2)) := by
    dsimp only [a1sDelegate2C, letV, Comp.letC, bindV]
    simp only [Comp.eval, hLetG2, pure_bind]
    exact bind_congr fun r => by
      simp only [v, Ext.wk, Expr.eval, Env.get, hsLeg]
  rw [hDelRhs, a1gStep2C_eval_split S b (.zero : Var (a1g2StTy :: Δ) a1g2StTy) qv (.cons g2Val env)]
  have hGetG2 : (Env.cons g2Val env).get (Ext.wk (.zero : Var (a1g2StTy :: Δ) a1g2StTy)) = g2Val := rfl
  have hGetQv : (Env.cons g2Val env).get (Ext.wk (Δ := a1g2StTy :: Δ) qv) =
      (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (mkQ x) := hqLeg
  simp only [hGetG2, hGetQv, Comp.eval, hGuardEq0]
  split
  · refine ⟨?_, ?_⟩
    · simp only [Expr.eval, aNoneAtomicE, aNone, hst, forgetSig, pure_bind, map_pure, Prod.map, id]
      have hs1 : embedVal a1sStTy (projVal a1sStTy s'.1) = s'.1 := embedVal_projVal a1sStTy s'.1
      exact congrArg pure (congrArg (Prod.mk (Sum.inl ())) hs1.symm)
    · intro p hp
      simp only [Expr.eval, hst, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hInv.bump_unchanged (mkQ x) hroom
  · let ρ₁ : Env (Ty.prod a1s2ShadowStTy .unit :: Γ) := .cons (s', ()) ρ
    have hRen :
        (compRename Var.succ core).eval ρ₁ =
          armEvalNew paVal s'.1.1.1.2 s'.1.1.2 s'.2 x := by
      rw [compRename_eval core Var.succ ρ ρ₁ (fun _ => rfl)]
      exact hCore
    obtain ⟨hMapArm, hSupArm⟩ := hArm c paVal s'.1.1.1.2 s'.1.1.2 s'.2 x hc hroom hInv
    simp only [Expr.eval, pure_bind, hst]
    change Prod.map id forgetSig <$>
        ((compRename Var.succ core).eval ρ₁ >>= fun r =>
          pure (r.1,
            ((a1sPutSimSigBE (.fst (.fst .v1)) (.fst (.snd .v0))).eval (.cons r ρ₁),
              r.2.2))) = _ ∧
      ∀ p ∈ support ((compRename Var.succ core).eval ρ₁ >>= fun r =>
        pure (r.1,
          ((a1sPutSimSigBE (.fst (.fst .v1)) (.fst (.snd .v0))).eval (.cons r ρ₁),
            r.2.2))), _
    rw [hRen]
    refine ⟨?_, ?_⟩
    · have hPut : ∀ r : fgCoreOutTy.denote,
          (a1sPutSimSigBE (.fst (.fst .v1)) (.fst (.snd .v0))).eval (.cons r ρ₁) =
            embedVal a1sStTy
              ((((projVal a1sStTy s'.1).1.1.1, projVal fgSimTy r.2.1.1), r.2.1.2),
                (projVal a1sStTy s'.1).2) := fun r =>
        a1sPutSimSigBE_eval_eq _ _ (.cons r ρ₁)
      simp_rw [hPut]
      have hFactor :
          (Prod.map id forgetSig <$>
            (armEvalNew paVal s'.1.1.1.2 s'.1.1.2 s'.2 x >>= fun r =>
              pure (r.1,
                (embedVal a1sStTy
                  ((((projVal a1sStTy s'.1).1.1.1, projVal fgSimTy r.2.1.1), r.2.1.2),
                    (projVal a1sStTy s'.1).2), r.2.2)))) =
          (fun q => (q.1,
            embedVal a1sStTy
              ((((projVal a1sStTy s'.1).1.1.1, projVal fgSimTy q.2.1), q.2.2),
                (projVal a1sStTy s'.1).2))) <$>
            (Prod.map id Prod.fst <$> armEvalNew paVal s'.1.1.1.2 s'.1.1.2 s'.2 x) := by
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
          Prod.map, id, forgetSig]
      rw [hFactor, hMapArm, legacyCoreArmEval_eq_map]
      have hRhsCollapse :
          ∀ {M : Type → Type} [Monad M] [LawfulMonad M]
            (m : M (authRespTy.prod (fgSimTy.prod .nat)).denote),
            ((fun out => (out.1, (projVal a1gParams2Ty paVal, out.2.1), out.2.2)) <$> m >>= fun r =>
              pure (r.1,
                ((((projVal a1sStTy s'.1).1.1.1, r.2.1.2), r.2.2), (projVal a1sStTy s'.1).2))) =
            (fun out => (out.1,
              ((((projVal a1sStTy s'.1).1.1.1, out.2.1), out.2.2), (projVal a1sStTy s'.1).2))) <$> m := by
        intro M _ _ m
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        rfl
      dsimp only [g2Val]
      rw [hRhsCollapse]
      erw [Functor.map_map, Functor.map_map]
      congr 1; funext out
      have hSimRT : projVal fgSimTy (embedVal fgSimTy out.2.1) = out.2.1 :=
        projVal_embedVal fgSimTy out.2.1
      exact congrArg (fun x =>
        (embedVal authRespTy out.1,
          embedVal a1sStTy ((((projVal a1sStTy s'.1).1.1.1, x), out.2.2), (projVal a1sStTy s'.1).2)))
        hSimRT
    · intro p hp
      rw [mem_support_bind_iff] at hp
      rcases hp with ⟨r, hr, hp⟩
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      have hPutSim :
          ((a1sPutSimSigBE (.fst (.fst .v1)) (.fst (.snd .v0))).eval (.cons r ρ₁)).1.1.2 =
            r.2.1.1 := by
        rw [a1sPutSimSigBE_eval_eq]
        exact embedVal_projVal fgSimTy r.2.1.1
      dsimp only [SigAuthInv]
      rw [hPutSim]
      exact hSupArm r hr

private theorem sigOldAtomicProg_handle_eval (S : Setup) (b : QueryBudget)
    (s' : a1s2ShadowStTy.denote) (q : AuthQuery S) :
    (sigOldAtomicProg S b).handle.eval
      (.cons (forgetSig s') (.cons ((authCodec S).qenc q) .nil)) =
    embedVal a1sRS <$>
      (a1sStep2C S b.q_total (Δ := [a1sStTy, authQueryTy])
        (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
        (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)).eval
        (.cons (projVal a1sStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc q) .nil)) := by
  have hs1 : forgetSig s' = embedVal a1sStTy (projVal a1sStTy s'.1) :=
    (embedVal_projVal a1sStTy s'.1).symm
  dsimp only [sigOldAtomicProg, liftAuth1Stage, sigAuth1KeyDslProg, a1sHandle2Dsl]
  rw [hs1]
  exact liftAuthHandle_eval tlAuthSigDdh S (fun _ => rfl)
    (a1sStep2C S b.q_total (Δ := [a1sStTy, authQueryTy])
      (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
      (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy))
    (projVal a1sStTy s'.1) q

private def isNonSendAuthQ {S : Setup} : AuthQuery S → Bool
  | .sendOPK .. | .sendNoOPK .. => false
  | _ => true

private theorem a1sPreC_eval_nonSend (S : Setup) (K : ℕ)
    (sLeg : a1sStTy.denote) (q : AuthQuery S) (hNS : isNonSendAuthQ q = true) :
    (a1sPreC S K (Δ := [a1sStTy, authQueryTy])
      (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
      (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)).eval
      (.cons sLeg (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc q) .nil)) =
    pure (Sum.inr ()) := by
  cases q <;> try cases hNS
  all_goals rfl

private theorem a1sWrapNonSendArm_sim (S : Setup) (b : QueryBudget)
    {Payload : Type} {X : Ty pqAtomicSig}
    {mkQ : Payload → AuthQuery S}
    {armEvalNew : (embedTy a1gParams2Ty).denote → (embedTy fgSimTy).denote → ℕ →
      fgAuthShadowAuxTy.denote → Payload → OracleComp AuthSigDdhSpec fgCoreOutTy.denote}
    (hArm : FgArmSim S b mkQ armEvalNew)
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface [X, a1s2ShadowStTy, authQueryAtomicTy] fgCoreOutTy)
    (c : Fin 4 → ℕ) (s' : a1s2ShadowStTy.denote) (x : Payload) (xVal : X.denote)
    (q : AuthQuery S) (hq : q = mkQ x) (hNS : isNonSendAuthQ q = true)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j q → c j + 1 ≤ authSimBounds b j)
    (hInv : SigAuthInv S b c s')
    (hCore : core.eval (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil))) =
      armEvalNew ((a1sCaseAPa2AtomicE (.fst .v1)).eval
        (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil)))) s'.1.1.1.2 s'.1.1.2 s'.2 x) :
    Prod.map id forgetSig <$>
        (a1sWrapNonSendArm (AuthKindFuels.ofBudget S b) .v1 core).eval
          (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil))) =
      (sigOldAtomicProg S b).handle.eval (.cons (forgetSig s') (.cons ((authCodec S).qenc q) .nil)) ∧
    ∀ p ∈ support ((a1sWrapNonSendArm (AuthKindFuels.ofBudget S b) .v1 core).eval
        (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil)))),
      SigAuthInv S b (bumpPred (authSimPred S) c q) p.2 := by
  let ρ : Env [X, a1s2ShadowStTy, authQueryAtomicTy] :=
    .cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil))
  let ρLeg : Env [a1sStTy, authQueryTy] :=
    .cons (projVal a1sStTy s'.1) (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc q) .nil)
  let s₀ : Var [a1sStTy, authQueryTy] a1sStTy := .vz
  let q₀ : Var [a1sStTy, authQueryTy] authQueryTy := .vs .vz
  rw [sigOldAtomicProg_handle_eval S b s' q]
  have hFrzEq :
      (a1sIsFrozenE (.fst (.v1 : Expr pqAtomicOps [X, a1s2ShadowStTy, authQueryAtomicTy] a1s2ShadowStTy))).eval ρ =
      (isSomeE (a1sFg (v s₀))).eval ρLeg := by
    rw [a1sIsFrozenE_eval_eq]
    rfl
  have hIteL : (a1sWrapNonSendArm (AuthKindFuels.ofBudget S b) .v1 core).eval ρ =
      if (a1sIsFrozenE (.fst .v1)).eval ρ = true then
        (Comp.ret (.pair aNoneAtomicE .v1)).eval ρ
      else
        (a1sDelegateCoreArm (AuthKindFuels.ofBudget S b) .v1 core).eval ρ := rfl
  have hIteR : (a1sStep2C S b.q_total (Δ := [a1sStTy, authQueryTy]) s₀ q₀).eval ρLeg =
      if (isSomeE (a1sFg (v s₀))).eval ρLeg = true then
        (Comp.ret (.pair aNone (v s₀))).eval ρLeg
      else
        (bindV (a1sPreC S b.q_total s₀ q₀) fun pre =>
          caseSumV (v pre) (fun r => .ret (v r)) fun _ =>
            a1sDelegate2C S b.q_total s₀ q₀).eval ρLeg := rfl
  change Prod.map id forgetSig <$> (a1sWrapNonSendArm (AuthKindFuels.ofBudget S b) .v1 core).eval ρ =
      embedVal a1sRS <$> (a1sStep2C S b.q_total (Δ := [a1sStTy, authQueryTy]) s₀ q₀).eval ρLeg ∧
    ∀ p ∈ support ((a1sWrapNonSendArm (AuthKindFuels.ofBudget S b) .v1 core).eval ρ),
      SigAuthInv S b (bumpPred (authSimPred S) c q) p.2
  rw [hIteL, hIteR, hFrzEq]
  split
  · refine ⟨?_, ?_⟩
    · dsimp only [Comp.eval, Expr.eval, Expr.v1, v, Ext.wk, s₀, Var.vz, Env.get,
        aNoneAtomicE, aNone, forgetSig, Prod.map, id, ρ, ρLeg]
      rw [map_pure, map_pure]
      have hs1 : embedVal a1sStTy (projVal a1sStTy s'.1) = s'.1 := embedVal_projVal a1sStTy s'.1
      exact congrArg pure (congrArg (Prod.mk (Sum.inl ())) hs1.symm)
    · intro p hp
      dsimp only [Comp.eval, Expr.eval, Expr.v1, Env.get, ρ] at hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hInv.bump_unchanged q hroom
  · let ρLeg₂ : Env (.unit :: .sum a1sRS .unit :: [a1sStTy, authQueryTy]) :=
      .cons () (.cons (Sum.inr ()) ρLeg)
    have hPre := a1sPreC_eval_nonSend S b.q_total (projVal a1sStTy s'.1) q hNS
    have hStepRhs :
        (bindV (a1sPreC S b.q_total s₀ q₀) fun pre =>
          caseSumV (v pre) (fun r => .ret (v r)) fun _ =>
            a1sDelegate2C S b.q_total s₀ q₀).eval ρLeg =
        (a1sDelegate2C S b.q_total
          (Δ := .unit :: .sum a1sRS .unit :: [a1sStTy, authQueryTy]) s₀ q₀).eval ρLeg₂ := by
      dsimp only [bindV, caseSumV, Comp.caseSumC, Comp.eval, ρLeg, ρLeg₂]
      erw [hPre, pure_bind]
      rfl
    rw [hStepRhs]
    exact a1sDelegateCoreArm_sim S b hArm .v1 core ρ ρLeg₂ s₀ q₀
      c s' x q hq rfl rfl rfl hc hroom hInv hCore

private def sigSendRen {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy)
    {τ : Ty pqSig} (w : Var [a1sStTy, sendQTy] τ) : Var Δ τ :=
  match w with
  | .zero => h₁.wk s
  | .succ w => match w with
    | .zero => h₂.wk x

private theorem a1sSendCheckC_ren (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy) :
    compRename (sigSendRen s x)
      (a1sSendCheckC (Δ := [a1sStTy, sendQTy]) S K
        (.vz : Var [a1sStTy, sendQTy] a1sStTy)
        (.vs .vz : Var [a1sStTy, sendQTy] sendQTy)) =
      a1sSendCheckC S K (Δ := Δ) s x := rfl

private theorem a1sPreC_eval_send (S : Setup) (K : ℕ) (opk : Bool)
    (sLeg : a1sStTy.denote) (u : Fin S.N_id)
    (i : if opk then Fin S.N_send_opk else Fin S.N_send_no_opk)
    (bu : PreKeyBundleInput) (m0 m1 : Bytes) :
    let q : AuthQuery S := match opk, i with
      | true, i => .sendOPK u i bu m0 m1
      | false, i => .sendNoOPK u i bu m0 m1
    let xLeg : sendQTy.denote :=
      (u.val, ((match opk, i with | true, i => i.val | false, i => i.val),
        (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
    (a1sPreC S K (Δ := [a1sStTy, authQueryTy])
      (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
      (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)).eval
      (.cons sLeg (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc q) .nil)) =
    (a1sSendCheckC (Δ := [a1sStTy, sendQTy]) S K
      (.vz : Var [a1sStTy, sendQTy] a1sStTy)
      (.vs .vz : Var [a1sStTy, sendQTy] sendQTy)).eval
      (.cons sLeg (.cons xLeg .nil)) := by
  cases opk <;>
  · dsimp only [a1sPreC, caseSumV, Comp.caseSumC,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc]
    simp only [Comp.eval, Expr.eval, v, Ext.wk, Var.vz, Var.vs, Env.get]
    rw [← a1sSendCheckC_ren S K]
    exact compRename_eval _ _ _ _ (fun w => by
      cases w with
      | zero => rfl
      | succ y => cases y with | zero => rfl | succ z => nomatch z)

private theorem map_bind_eq_of_ptwise {ι : Type} {spec : OracleSpec ι} {α β γ δ ε : Type}
    (pL : γ → ε) (pR : δ → ε) (emb : α → β)
    (m : OracleComp spec α) (kL : β → OracleComp spec γ) (kR : α → OracleComp spec δ)
    (h : ∀ a, pL <$> kL (emb a) = pR <$> kR a) :
    pL <$> ((emb <$> m) >>= kL) = pR <$> (m >>= kR) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun a => ?_
  have ha := h a
  simp only [map_eq_bind_pure_comp] at ha
  exact ha

private theorem eval_bind_caseSum {Γ : List (Ty pqAtomicSig)} {α β γ : Ty pqAtomicSig}
    (c1 : Comp pqAtomicOps pqAuthSigAndDdhIface Γ (.sum α β))
    (eInl : Expr pqAtomicOps (α :: .sum α β :: Γ) γ)
    (cInr : Comp pqAtomicOps pqAuthSigAndDdhIface (β :: .sum α β :: Γ) γ)
    (ρ : Env Γ) :
    (Comp.bind c1 (.caseSum .v0 (.ret eInl) cInr)).eval ρ =
      c1.eval ρ >>= fun pre => match pre with
        | .inl a => pure (eInl.eval (.cons a (.cons (.inl a) ρ)))
        | .inr b => cInr.eval (.cons b (.cons (.inr b) ρ)) := by
  change (c1.eval ρ >>= fun pre => _) = _
  refine bind_congr fun pre => ?_
  cases pre <;> rfl

private theorem eval_bindV_caseSumV {Δ : List (Ty pqSig)} {α β : Ty pqSig}
    (c1 : Comp pqxdhOps pqSigAndDdhIface Δ (.sum α β))
    (cInr : Comp pqxdhOps pqSigAndDdhIface (β :: .sum α β :: Δ) α)
    (ρ : Env Δ) :
    (bindV c1 fun pre => caseSumV (v pre) (fun r => .ret (v r)) fun _ => cInr).eval ρ =
      c1.eval ρ >>= fun pre => match pre with
        | .inl a => pure a
        | .inr b => cInr.eval (.cons b (.cons (.inr b) ρ)) := by
  change (c1.eval ρ >>= fun pre => _) = _
  refine bind_congr fun pre => ?_
  cases pre <;> rfl

private theorem a1sArm_send_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    (hArms : AllFgArmsSim S b) (hSendChk : SigSendCheckSim S b)
    (c : Fin 4 → ℕ) (s' : a1s2ShadowStTy.denote)
    (u : Fin S.N_id) (i : if opk then Fin S.N_send_opk else Fin S.N_send_no_opk)
    (bu : PreKeyBundleInput) (m0 m1 : Bytes)
    (q : AuthQuery S)
    (hq : q = match opk, i with
      | true, i => .sendOPK u i bu m0 m1
      | false, i => .sendNoOPK u i bu m0 m1)
    (xVal : authSendQAtomicTy.denote)
    (hxVal : xVal = (u.val, ((match opk, i with | true, i => i.val | false, i => i.val),
      (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))))
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j q → c j + 1 ≤ authSimBounds b j)
    (hInv : SigAuthInv S b c s') :
    Prod.map id forgetSig <$>
        (a1sArm_send S (AuthKindFuels.ofBudget S b) opk).eval
          (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil))) =
      (sigOldAtomicProg S b).handle.eval (.cons (forgetSig s') (.cons ((authCodec S).qenc q) .nil)) ∧
    ∀ p ∈ support ((a1sArm_send S (AuthKindFuels.ofBudget S b) opk).eval
        (.cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil)))),
      SigAuthInv S b (bumpPred (authSimPred S) c q) p.2 := by
  cases opk <;>
  · dsimp only at i hq hxVal
    let ρ : Env [authSendQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy] :=
      .cons xVal (.cons s' (.cons ((authCodec S).qenc q) .nil))
    let ρLeg : Env [a1sStTy, authQueryTy] :=
      .cons (projVal a1sStTy s'.1) (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc q) .nil)
    let xLeg : sendQTy.denote := (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
    let s₀ : Var [a1sStTy, authQueryTy] a1sStTy := .vz
    let q₀ : Var [a1sStTy, authQueryTy] authQueryTy := .vs .vz
    rw [sigOldAtomicProg_handle_eval S b s' q]
    have hIteL : ∀ (opk' : Bool),
        (a1sArm_send S (AuthKindFuels.ofBudget S b) opk').eval ρ =
        if (a1sIsFrozenE (.fst .v1)).eval ρ = true then (Comp.ret (.pair aNoneAtomicE .v1)).eval ρ
        else (Comp.bind (liftCs1 (a1sSendCheckLegC S (AuthKindFuels.ofBudget S b)) (.pair (.fst .v1) .v0))
          (.caseSum .v0 (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v3))))
            (a1sDelegateCoreArm (AuthKindFuels.ofBudget S b) .v3
              (fgCoreArm_send S (AuthKindFuels.ofBudget S b) opk' (a1sCaseAPa2AtomicE (.fst .v3))
                (a1sSimAtomicE (.fst .v3)) (a1sSigBAtomicE (.fst .v3)) (.snd .v3) .v2)))).eval ρ :=
      fun _ => rfl
    have hIteR :
        (a1sStep2C S b.q_total (Δ := [a1sStTy, authQueryTy]) s₀ q₀).eval ρLeg =
        if (isSomeE (a1sFg (v s₀))).eval ρLeg = true then (Comp.ret (.pair aNone (v s₀))).eval ρLeg
        else (bindV (a1sPreC S b.q_total s₀ q₀) fun pre =>
          caseSumV (v pre) (fun r => .ret (v r)) fun _ =>
            a1sDelegate2C S b.q_total s₀ q₀).eval ρLeg := rfl
    have hFrzEq :
        (a1sIsFrozenE (.fst (.v1 : Expr pqAtomicOps [authSendQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy] a1s2ShadowStTy))).eval ρ =
        (isSomeE (a1sFg (v s₀))).eval ρLeg := by
      rw [a1sIsFrozenE_eval_eq]; rfl
    change (Prod.map id forgetSig <$> (a1sArm_send S (AuthKindFuels.ofBudget S b) _).eval ρ =
        embedVal a1sRS <$> (a1sStep2C S b.q_total (Δ := [a1sStTy, authQueryTy]) s₀ q₀).eval ρLeg) ∧
      ∀ p ∈ support ((a1sArm_send S (AuthKindFuels.ofBudget S b) _).eval ρ),
        SigAuthInv S b (bumpPred (authSimPred S) c q) p.2
    rw [hIteL, hIteR, hFrzEq]
    split
    · refine ⟨?_, ?_⟩
      · simp only [Comp.eval, Expr.eval, Expr.v1, v, Ext.wk, s₀, Var.vz, Env.get,
          aNoneAtomicE, aNone, forgetSig, map_pure, Prod.map, id, ρ, ρLeg]
        exact congrArg pure (congrArg (Prod.mk (Sum.inl ())) (embedVal_projVal a1sStTy s'.1).symm)
      · intro p hp
        simp only [Comp.eval, Expr.eval, Expr.v1, Env.get,
          support_pure, Set.mem_singleton_iff, ρ] at hp
        subst hp
        exact hInv.bump_unchanged q hroom
    · rename_i hFrzFalse
      have hFrzFalseL : (a1sIsFrozenE (.fst (.v1 : Expr pqAtomicOps [authSendQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy] a1s2ShadowStTy))).eval ρ = true ↔ False := by
        rw [hFrzEq]; exact ⟨hFrzFalse, False.elim⟩
      have hFrzNone : s'.1.2.2.2 = none :=
        a1sIsFrozenE_false_imp_none
          (.fst (.v1 : Expr pqAtomicOps [authSendQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy] a1s2ShadowStTy))
          ρ s'.1 rfl (Bool.eq_false_iff.mpr hFrzFalseL.mp)
      have hEnvEmb :
          (Env.cons s'.1 (Env.cons xVal Env.nil) : Env [embedTy a1sStTy, embedTy sendQTy]) =
          embedEnv (.cons (projVal a1sStTy s'.1) (.cons xLeg .nil)) := by
        subst hxVal
        have hs1 : s'.1 = embedVal a1sStTy (projVal a1sStTy s'.1) := (embedVal_projVal a1sStTy s'.1).symm
        have hx1 : (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) = embedVal sendQTy xLeg := by
          rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl
        conv_lhs => rw [hs1, hx1]
      have hMapChk :
          (mapComp tlAuthSigDdh
            (a1sSendCheckC (Δ := [a1sStTy, sendQTy]) S b.q_total
              (.zero : Var [a1sStTy, sendQTy] a1sStTy)
              (.succ .zero : Var [a1sStTy, sendQTy] sendQTy))).eval (.cons s'.1 (.cons xVal .nil)) =
          embedVal (.sum a1sRS .unit) <$>
            (a1sSendCheckC (Δ := [a1sStTy, sendQTy]) S b.q_total
              (.vz : Var [a1sStTy, sendQTy] a1sStTy)
              (.vs .vz : Var [a1sStTy, sendQTy] sendQTy)).eval
              (.cons (projVal a1sStTy s'.1) (.cons xLeg .nil)) := by
        rw [hEnvEmb]
        exact mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _) _
      let ρ₂ : Env [.unit, embedTy (.sum a1sRS .unit), authSendQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy] :=
        .cons () (.cons (Sum.inr ()) ρ)
      let ρLeg₂ : Env [.unit, .sum a1sRS .unit, a1sStTy, authQueryTy] :=
        .cons () (.cons (Sum.inr ()) ρLeg)
      subst hq; subst hxVal
      first
      | (obtain ⟨hChkEq, hChkSup⟩ := hSendChk false c s' u i bu m0 m1 hc hroom hInv hFrzNone
         have hPreLeg := a1sPreC_eval_send S b.q_total false (projVal a1sStTy s'.1) u i bu m0 m1
         have hDelBoth := a1sDelegateCoreArm_sim S b hArms.sendNoOPK .v3
           (fgCoreArm_send S (AuthKindFuels.ofBudget S b) false
             (a1sCaseAPa2AtomicE (.fst .v3)) (a1sSimAtomicE (.fst .v3))
             (a1sSigBAtomicE (.fst .v3)) (.snd .v3) .v2)
           ρ₂ ρLeg₂ s₀ q₀
           c s' (u, i, bu, m0, m1) (.sendNoOPK u i bu m0 m1) rfl rfl rfl rfl hc hroom hInv
           (fgCoreArm_send_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl))
      | (obtain ⟨hChkEq, hChkSup⟩ := hSendChk true c s' u i bu m0 m1 hc hroom hInv hFrzNone
         have hPreLeg := a1sPreC_eval_send S b.q_total true (projVal a1sStTy s'.1) u i bu m0 m1
         have hDelBoth := a1sDelegateCoreArm_sim S b hArms.sendOPK .v3
           (fgCoreArm_send S (AuthKindFuels.ofBudget S b) true
             (a1sCaseAPa2AtomicE (.fst .v3)) (a1sSimAtomicE (.fst .v3))
             (a1sSigBAtomicE (.fst .v3)) (.snd .v3) .v2)
           ρ₂ ρLeg₂ s₀ q₀
           c s' (u, i, bu, m0, m1) (.sendOPK u i bu m0 m1) rfl rfl rfl rfl hc hroom hInv
           (fgCoreArm_send_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl))
      dsimp only at hChkEq hChkSup hPreLeg
      have hChkAll :
          (liftCs1 (a1sSendCheckLegC S (AuthKindFuels.ofBudget S b)) (.pair (.fst .v1) .v0)).eval ρ =
          embedVal (.sum a1sRS .unit) <$>
            (a1sPreC S b.q_total (Δ := [a1sStTy, authQueryTy]) s₀ q₀).eval ρLeg :=
        (hChkEq.trans hMapChk).trans
          (congrArg (Functor.map (embedVal (.sum a1sRS .unit))) hPreLeg.symm)
      refine ⟨?_, ?_⟩
      · rw [eval_bind_caseSum, eval_bindV_caseSumV, hChkAll]
        refine map_bind_eq_of_ptwise _ _ _ _ _ _ fun preLeg => ?_
        cases preLeg with
        | inl rsLeg => rfl
        | inr uUnit =>
          cases uUnit
          exact hDelBoth.1
      · intro p hp
        rw [eval_bind_caseSum, mem_support_bind_iff] at hp
        rcases hp with ⟨pre, hPreMem, hp⟩
        cases pre with
        | inl rs =>
          dsimp only [Expr.eval, Expr.v0, Expr.v3, Env.get, ρ] at hp
          rw [support_pure, Set.mem_singleton_iff] at hp
          subst hp
          exact hChkSup rs hPreMem
        | inr uUnit =>
          cases uUnit
          exact hDelBoth.2 p hp

private theorem a1s2KindHandle_step_of_arms (S : Setup) (b : QueryBudget)
    (hArms : AllFgArmsSim S b) (hSendChk : SigSendCheckSim S b)
    (c : Fin 4 → ℕ) (s' : a1s2ShadowStTy.denote) (t : AuthQuery S)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : SigAuthInv S b c s') :
    Prod.map id forgetSig <$>
        (a1s2KindProg S b).handle.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (sigOldAtomicProg S b).handle.eval
        (.cons (forgetSig s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((a1s2KindProg S b).handle.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))),
      SigAuthInv S b (bumpPred (authSimPred S) c t) p.2 := by
  have hDisp :
      (a1s2KindProg S b).handle.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
        dispatchAuthQEval (.cons s' (.cons ((authCodec S).qenc t) .nil)) t
          (a1sArm_initPrin (AuthKindFuels.ofBudget S b))
          (a1sArm_corrupt (AuthKindFuels.ofBudget S b))
          (a1sArm_genSPK (AuthKindFuels.ofBudget S b))
          (a1sArm_genOPK (AuthKindFuels.ofBudget S b))
          (a1sArm_send S (AuthKindFuels.ofBudget S b) true)
          (a1sArm_send S (AuthKindFuels.ofBudget S b) false)
          (a1sArm_recv S (AuthKindFuels.ofBudget S b) true)
          (a1sArm_recv S (AuthKindFuels.ofBudget S b) false)
          (a1sArm_roQuery (AuthKindFuels.ofBudget S b))
          (a1sArm_roRootQuery (AuthKindFuels.ofBudget S b))
          (a1sArm_revealDh (AuthKindFuels.ofBudget S b))
          (a1sArm_registerKey (AuthKindFuels.ofBudget S b)) :=
    dispatchAuthQ_eval_qenc .v1 (.cons s' (.cons ((authCodec S).qenc t) .nil)) t rfl
      _ _ _ _ _ _ _ _ _ _ _ _
  rw [hDisp]
  generalize hρ :
    (Env.cons s' (Env.cons ((authCodec S).qenc t) Env.nil) :
      Env [a1s2ShadowStTy, authQueryAtomicTy]) = ρ
  cases t with
  | initPrin u =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_initPrin]
    subst hρ
    refine a1sWrapNonSendArm_sim (X := .nat) S b hArms.initPrin
      (fgCoreArm_initPrin (AuthKindFuels.ofBudget S b) (a1sCaseAPa2AtomicE (.fst .v1))
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' u u.val (.initPrin u) rfl rfl hc hroom hInv ?_
    simp only [fgCoreArm_initPrin, armEval_initPrin, a1sSimAtomicE, a1sSigBAtomicE, Comp.eval,
      Expr.eval, pure_bind, Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]
    rfl
  | corruptIK u =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_corrupt]
    subst hρ
    refine a1sWrapNonSendArm_sim (X := .nat) S b hArms.corruptIK
      (fgCoreArm_corrupt (AuthKindFuels.ofBudget S b)
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' u u.val (.corruptIK u) rfl rfl hc hroom hInv ?_
    simp only [fgCoreArm_corrupt, armEval_corruptIK, a1sSimAtomicE, a1sSigBAtomicE, Comp.eval,
      Expr.eval, pure_bind, Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]
  | genSPK u j =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_genSPK]
    subst hρ
    refine a1sWrapNonSendArm_sim (X := .prod .nat .nat) S b hArms.genSPK
      (fgCoreArm_genSPK (AuthKindFuels.ofBudget S b) (a1sCaseAPa2AtomicE (.fst .v1))
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' (u, j) (u.val, j.val) (.genSPK u j) rfl rfl hc hroom hInv ?_
    simp only [fgCoreArm_genSPK, armEval_genSPK, a1sSimAtomicE, a1sSigBAtomicE, Comp.eval,
      Expr.eval, pure_bind, Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftCs1_eval]
    rfl
  | genOPK u j o =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_genOPK]
    subst hρ
    refine a1sWrapNonSendArm_sim (X := .prod .nat (.prod .nat .nat)) S b hArms.genOPK
      (fgCoreArm_genOPK (AuthKindFuels.ofBudget S b)
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' (u, j, o) (u.val, (j.val, o.val)) (.genOPK u j o) rfl rfl hc hroom hInv ?_
    simp only [fgCoreArm_genOPK, armEval_genOPK, a1sSimAtomicE, a1sSigBAtomicE, Comp.eval,
      Expr.eval, pure_bind, Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]
  | sendOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc]
    subst hρ
    exact a1sArm_send_sim S b true hArms hSendChk c s' u i bu m0 m1
      (.sendOPK u i bu m0 m1) rfl
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) rfl hc hroom hInv
  | sendNoOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc]
    subst hρ
    exact a1sArm_send_sim S b false hArms hSendChk c s' u i bu m0 m1
      (.sendNoOPK u i bu m0 m1) rfl
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) rfl hc hroom hInv
  | recvOPK k j o msg =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_recv]
    subst hρ
    exact a1sWrapNonSendArm_sim (X := authRecvQAtomicTy) S b hArms.recvOPK
      (fgCoreArm_recv S (AuthKindFuels.ofBudget S b) true
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' (k, j, o, msg) (k.val, (j.val, (o.val, preKeyMsgV msg)))
      (.recvOPK k j o msg) rfl rfl hc hroom hInv
      (fgCoreArm_recv_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | recvNoOPK k j n msg =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_recv]
    subst hρ
    exact a1sWrapNonSendArm_sim (X := authRecvQAtomicTy) S b hArms.recvNoOPK
      (fgCoreArm_recv S (AuthKindFuels.ofBudget S b) false
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' (k, j, n, msg) (k.val, (j.val, (n.val, preKeyMsgV msg)))
      (.recvNoOPK k j n msg) rfl rfl hc hroom hInv
      (fgCoreArm_recv_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | roQuery sec =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_roQuery]
    subst hρ
    exact a1sWrapNonSendArm_sim (X := PB 192) S b hArms.roQuery
      (fgCoreArm_roQuery (AuthKindFuels.ofBudget S b)
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' sec sec (.roQuery sec) rfl rfl hc hroom hInv
      (fgCoreArm_roQuery_eval_congr _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | roRootQuery rk dh =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_roRootQuery]
    subst hρ
    exact a1sWrapNonSendArm_sim (X := .prod (PB 32) (PB 32)) S b hArms.roRootQuery
      (fgCoreArm_roRootQuery (AuthKindFuels.ofBudget S b)
        (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' (rk, dh) (rk, dh) (.roRootQuery rk dh) rfl rfl hc hroom hInv
      (fgCoreArm_roRootQuery_eval_congr _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl)
  | revealDhSecrets =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_revealDh]
    subst hρ
    exact a1sWrapNonSendArm_sim (X := .unit) S b hArms.revealDhSecrets
      (fgCoreArm_revealDh (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1))
      c s' () () .revealDhSecrets rfl rfl hc hroom hInv rfl
  | registerKey sk =>
    dsimp only [dispatchAuthQEval, authCodec, _root_.SignalPqxdh.Costed.authQenc, a1sArm_registerKey]
    subst hρ
    refine a1sWrapNonSendArm_sim (X := PB 32) S b hArms.registerKey
      (fgCoreArm_registerKey (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
      c s' sk sk (.registerKey sk) rfl rfl hc hroom hInv ?_
    simp only [fgCoreArm_registerKey, armEval_registerKey, a1sSimAtomicE, a1sSigBAtomicE,
      Comp.eval, Expr.eval, pure_bind, Env.get, Expr.v0, Expr.v1, exprRename_succ_eval, liftGdh1_eval]

private theorem allFgArmsSim (S : Setup) (b : QueryBudget) : AllFgArmsSim S b where
  initPrin        := fgArmSim_initPrin S b
  corruptIK       := fgArmSim_corruptIK S b
  genSPK          := fgArmSim_genSPK S b
  genOPK          := fgArmSim_genOPK S b
  sendOPK         := fgArmSim_sendOPK S b
  sendNoOPK       := fgArmSim_sendNoOPK S b
  recvOPK         := fgArmSim_recvOPK S b
  recvNoOPK       := fgArmSim_recvNoOPK S b
  roQuery         := fgArmSim_roQuery S b
  roRootQuery     := fgArmSim_roRootQuery S b
  revealDhSecrets := fgArmSim_revealDhSecrets S b
  registerKey     := fgArmSim_registerKey S b

/-- Forgetful simulation between `a1g2KindProg` and `gdhOldAtomicProg`. -/
theorem a1g2KindProg_forgetSim (S : Setup) (b : QueryBudget)
    (uv : (Ty.prod (PB 32) (PB 32)).denote) :
    ForgetSim (a1g2KindProg S b) (gdhOldAtomicProg S b) forgetGdh
      (authSimPred S) (authSimBounds b) uv (GdhAuthInv S b) where
  hInit   := a1g2KindProg_init_sim S b uv
  hHandle := a1g2KindHandle_step_of_arms S b (allFgArmsSim S b)
  hFinish := a1g2KindProg_finish_sim S b

/-- Forgetful simulation between `a1s2KindProg` and `sigOldAtomicProg`. -/
theorem a1s2KindProg_forgetSim (S : Setup) (b : QueryBudget)
    (pk : (PB 32).denote) :
    ForgetSim (a1s2KindProg S b) (sigOldAtomicProg S b) forgetSig
      (authSimPred S) (authSimBounds b) pk (SigAuthInv S b) where
  hInit   := a1s2KindProg_init_sim S b pk
  hHandle := a1s2KindHandle_step_of_arms S b (allFgArmsSim S b) (sigSendCheckK_sim S b)
  hFinish := a1s2KindProg_finish_sim S b

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimA
