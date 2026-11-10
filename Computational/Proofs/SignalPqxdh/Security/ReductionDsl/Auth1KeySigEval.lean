/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySig
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhStepEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhGrow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSigStep
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStep
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSmall
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepRecv

/-!
# Handler Evaluation for the One-Key `Auth` `GapSigEufCma` DSL Program

**Checked by Lean.** Proves that `a1sHandleDsl` and the clamped `a1sHandle2Dsl` evaluate to the
shallow step `sigAuth1KeyStep`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open Proofs.SignalPqxdh.Security
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

@[simp] def a1sStToVal {S : Setup} (st : SigAuth1KeySimState S) : a1sStTy.denote :=
  (((paVal st.targetPk st.targetPk true st.targetParty S.N_spk_tot, fgSimToVal st.fg.sim),
      st.fg.sigBudget),
    (st.targetParty, (st.targetPk, st.forgery)))

@[simp] def a1sRSVal {S : Setup} (r : AuthResponse × SigAuth1KeySimState S) : a1sRS.denote :=
  (authRespToVal r.1, a1sStToVal r.2)

def a1sSendBundle? {S : Setup} : AuthQuery S → Option PreKeyBundleInput
  | .sendOPK _ _ bu _ _ => some bu
  | .sendNoOPK _ _ bu _ _ => some bu
  | _ => none

def a1sSendCheckShallow (S : Setup) (bu : PreKeyBundleInput) (st : SigAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (a1sRS.denote ⊕ Unit) := do
  let fg' ← _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec)
    (extractBundleForgeryPrim S st.targetParty st.targetPk
      st.fg.sim.base.principals st.fg.sim.base.spkBundles bu st.forgery)
  if fg'.isSome then pure (.inl (a1sRSVal (.noneResp, { st with forgery := fg' })))
  else pure (.inr ())

section Branches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ)

theorem a1sSendCheckC_eval (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy)
    (st : SigAuth1KeySimState S) (bu : PreKeyBundleInput) (n1 n2 : Nat) (b1 b2 : Bytes)
    (hs : Env.get env (h₁.wk s) = a1sStToVal st)
    (hx : Env.get env (h₂.wk x) = (n1, (n2, (preKeyBundleToVal bu, (b1, b2)))))
    (hfg : st.forgery = none) (hK : st.fg.sim.base.spkBundles.length ≤ K)
    (hPrin : st.fg.sim.base.principals.length ≤ K) :
    (a1sSendCheckC S K s x).eval env = a1sSendCheckShallow S bu st := by
  unfold a1sSendCheckC a1sSendCheckShallow
  simp only [letV, bindV, Comp.eval_letC, Comp.eval, KeyIndGapDh.liftBase_eval]
  rw [extractC_eval S K _ st.fg.sim.base _ _ _ _ st.targetParty st.targetPk bu
    ?_ ?_ ?_ ?_ hK hPrin]
  rw [hfg]
  refine bind_congr fun fg' => ?_
  cases fg' <;> simp [isSomeE, Expr.eval, aNone]
  all_goals simp [Expr.eval, v, hs, hx, Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk]

theorem a1sDelegateC_eval (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy)
    (st : SigAuth1KeySimState S) (qv : AuthQuery S)
    (hs : Env.get env (h₁.wk s) = a1sStToVal st)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv) (hB : AgBnd K st.fg.sim) :
    (a1sDelegateC S K s q).eval env = a1sRSVal <$> sigAuth1KeyDelegate S K qv st := by
  unfold a1sDelegateC sigAuth1KeyDelegate
  simp only [letV, bindV, Comp.eval_letC, Comp.eval]
  rw [a1gStepC_eval S K _ st.fg st.targetPk st.targetPk true st.targetParty S.N_spk_tot _ _ qv
    ?_ ?_ hB]
  · simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    simp [Expr.eval, v, hs, Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk]
  · simp [Expr.eval, v, hs, Env.get_vz, Ext.refl_wk]
  · simp [Expr.eval, v, hq, Env.get_vs, Ext.step_wk]

theorem a1sPreC_eval (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy)
    (st : SigAuth1KeySimState S) (qv : AuthQuery S)
    (hs : Env.get env (h₁.wk s) = a1sStToVal st)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv)
    (hfg : st.forgery = none) (hK : st.fg.sim.base.spkBundles.length ≤ K)
    (hPrin : st.fg.sim.base.principals.length ≤ K) :
    (a1sPreC S K s q).eval env =
      match a1sSendBundle? qv with
      | some bu => a1sSendCheckShallow S bu st
      | none => pure (Sum.inr ()) := by
  cases qv <;>
    simp only [a1sPreC, caseSumV, v, Comp.eval_caseSumC_elim, Comp.eval, Expr.eval, hq,
      authQueryToVal, authQenc, Sum.elim_inl, Sum.elim_inr, a1sSendBundle?,
      Ext.refl_wk, Env.get_vz]
  case sendOPK a b bu c d =>
    exact a1sSendCheckC_eval S K _ s .vz st bu _ _ _ _
      (by simp only [Ext.step_wk, Env.get_vs, hs]) rfl hfg hK hPrin
  case sendNoOPK a b bu c d =>
    exact a1sSendCheckC_eval S K _ s .vz st bu _ _ _ _
      (by simp only [Ext.step_wk, Env.get_vs, hs]) rfl hfg hK hPrin

end Branches

theorem sigAuth1KeyStep_of_bundle_none (S : Setup) (K : Nat) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) (hfg : st.forgery = none) (hb : a1sSendBundle? q = none) :
    sigAuth1KeyStep S K q st = sigAuth1KeyDelegate S K q st := by
  cases q <;> simp_all [a1sSendBundle?, sigAuth1KeyStep]

theorem sigAuth1KeyStep_of_bundle_some (S : Setup) (K : Nat) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) (bu : PreKeyBundleInput) (hfg : st.forgery = none)
    (hb : a1sSendBundle? q = some bu) :
    sigAuth1KeyStep S K q st = sigAuth1KeySend S K q bu st := by
  cases q <;> simp only [a1sSendBundle?, reduceCtorEq, Option.some.injEq] at hb <;>
    subst hb <;> simp [sigAuth1KeyStep, hfg]

/-- Handler agreement: `a1sHandleDsl` evaluates to the shallow `sigAuth1KeyStep`. -/
theorem a1sHandleDsl_eval (S : Setup) (K : Nat) (q : AuthQuery S) (st : SigAuth1KeySimState S)
    (hB : AgBnd K st.fg.sim) :
    (a1sHandleDsl S K).eval (.cons (a1sStToVal st) (.cons (authQueryToVal q) .nil)) =
      a1sRSVal <$> sigAuth1KeyStep S K q st := by
  let env0 : Env [a1sStTy, authQueryTy] := .cons (a1sStToVal st) (.cons (authQueryToVal q) .nil)
  change (a1sHandleDsl S K).eval env0 = _
  rcases hfg : st.forgery with _ | fgVal
  · simp only [a1sHandleDsl, a1sStepC, bindV, caseSumV, Comp.iteC, Comp.caseSumC, Comp.eval,
      isSomeE, a1sFg, v, Expr.eval, env0, a1sStToVal, hfg]
    rw [a1sPreC_eval S K _ .vz (.vs .vz) st q (by simp [Ext.refl_wk, Env.get_vz, hfg])
      (by simp [Ext.refl_wk, Env.get_vz, Env.get_vs]) hfg hB.base.spkBundles_le
      hB.base.principals_le]
    let envD : Env (Ty.unit :: Ty.sum a1sRS Ty.unit :: [a1sStTy, authQueryTy]) :=
      Env.cons () (Env.cons (Sum.inr ()) env0)
    have hDel : (a1sDelegateC S K (Var.vz : Var [a1sStTy, authQueryTy] a1sStTy)
        (Var.vs Var.vz : Var [a1sStTy, authQueryTy] authQueryTy)).eval
        envD =
        a1sRSVal <$> sigAuth1KeyDelegate S K q st :=
      a1sDelegateC_eval S K _ (Var.vz : Var [a1sStTy, authQueryTy] a1sStTy)
        (Var.vs Var.vz : Var [a1sStTy, authQueryTy] authQueryTy) st q
        rfl
        rfl hB
    simp only [envD, env0, a1sStToVal, hfg] at hDel
    rcases hb : a1sSendBundle? q with _ | bu
    · simp only [pure_bind]
      have hs := sigAuth1KeyStep_of_bundle_none S K q st hfg hb
      rw [hs]
      simp only [Ext.refl_wk, Env.get_vz]
      exact hDel
    · have hs := sigAuth1KeyStep_of_bundle_some S K q st bu hfg hb
      rw [hs]
      simp only [a1sSendCheckShallow, sigAuth1KeySend, bind_assoc, map_bind]
      refine bind_congr fun fg' => ?_
      cases hf' : fg'.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
        simp only [Ext.refl_wk, Env.get_vz]
        exact hDel
      · simp [Env.get_vz, a1sRSVal]
  · simp [a1sHandleDsl, a1sStepC, Comp.iteC, Comp.eval, isSomeE, a1sFg, Expr.eval, v, env0, hfg,
      Env.get_vz, sigAuth1KeyStep, aNone]

/-! ## Clamped evaluation -/

@[simp] def a1sSt2ToVal {S : Setup} (K : Nat) (st : SigAuth1KeySimState S) : a1sStTy.denote :=
  (((paVal st.targetPk st.targetPk true st.targetParty 0, fgSimToVal st.fg.sim),
      a1gClampedSigB S K st.fg),
    (st.targetParty, (st.targetPk, st.forgery)))

@[simp] def a1sRS2Val {S : Setup} (K : Nat) (r : AuthResponse × SigAuth1KeySimState S) :
    a1sRS.denote :=
  (authRespToVal r.1, a1sSt2ToVal K r.2)

def a1sSendCheckShallow2 (S : Setup) (K : Nat) (bu : PreKeyBundleInput)
    (st : SigAuth1KeySimState S) : OracleComp GdhSignSimSpec (a1sRS.denote ⊕ Unit) := do
  let fg' ← _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec)
    (extractBundleForgeryPrim S st.targetParty st.targetPk
      st.fg.sim.base.principals st.fg.sim.base.spkBundles bu st.forgery)
  if fg'.isSome then pure (.inl (a1sRS2Val K (.noneResp, { st with forgery := fg' })))
  else pure (.inr ())

section Branches2

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ)

theorem a1sSendCheckC_eval2 (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy)
    (st : SigAuth1KeySimState S) (bu : PreKeyBundleInput) (n1 n2 : Nat) (b1 b2 : Bytes)
    (hs : Env.get env (h₁.wk s) = a1sSt2ToVal K st)
    (hx : Env.get env (h₂.wk x) = (n1, (n2, (preKeyBundleToVal bu, (b1, b2)))))
    (hfg : st.forgery = none) (hK : st.fg.sim.base.spkBundles.length ≤ K)
    (hPrin : st.fg.sim.base.principals.length ≤ K) :
    (a1sSendCheckC S K s x).eval env = a1sSendCheckShallow2 S K bu st := by
  unfold a1sSendCheckC a1sSendCheckShallow2
  simp only [letV, bindV, Comp.eval_letC, Comp.eval, KeyIndGapDh.liftBase_eval]
  rw [extractC_eval S K _ st.fg.sim.base _ _ _ _ st.targetParty st.targetPk bu
    ?_ ?_ ?_ ?_ hK hPrin]
  rw [hfg]
  refine bind_congr fun fg' => ?_
  cases fg' <;> simp [isSomeE, Expr.eval, aNone]
  all_goals simp [Expr.eval, v, hs, hx, Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk]

theorem a1sPreC_eval2 (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy)
    (st : SigAuth1KeySimState S) (qv : AuthQuery S)
    (hs : Env.get env (h₁.wk s) = a1sSt2ToVal K st)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv)
    (hfg : st.forgery = none) (hK : st.fg.sim.base.spkBundles.length ≤ K)
    (hPrin : st.fg.sim.base.principals.length ≤ K) :
    (a1sPreC S K s q).eval env =
      match a1sSendBundle? qv with
      | some bu => a1sSendCheckShallow2 S K bu st
      | none => pure (Sum.inr ()) := by
  cases qv <;>
    simp only [a1sPreC, caseSumV, v, Comp.eval_caseSumC_elim, Comp.eval, Expr.eval, hq,
      authQueryToVal, authQenc, Sum.elim_inl, Sum.elim_inr, a1sSendBundle?,
      Ext.refl_wk, Env.get_vz]
  case sendOPK a b bu c d =>
    exact a1sSendCheckC_eval2 S K _ s .vz st bu _ _ _ _
      (by simp only [Ext.step_wk, Env.get_vs, hs]) rfl hfg hK hPrin
  case sendNoOPK a b bu c d =>
    exact a1sSendCheckC_eval2 S K _ s .vz st bu _ _ _ _
      (by simp only [Ext.step_wk, Env.get_vs, hs]) rfl hfg hK hPrin

theorem a1sDelegate2C_eval (k : Nat) (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy)
    (st : SigAuth1KeySimState S) (qv : AuthQuery S)
    (hs : Env.get env (h₁.wk s) = a1sSt2ToVal K st)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv) (hInv : AgInv2 K (k + 1) st.fg) :
    (a1sDelegate2C S K s q).eval env = a1sRS2Val K <$> sigAuth1KeyDelegate S K qv st := by
  unfold a1sDelegate2C sigAuth1KeyDelegate
  simp only [letV, bindV, Comp.eval_letC, Comp.eval]
  rw [a1gStep2C_eval S K _ st.fg st.targetPk st.targetPk true st.targetParty S.N_spk_tot _ _ qv
    ?_ ?_ hInv]
  · simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    simp [Expr.eval, v, hs, Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk, a1g2StToVal]
  · simp [Expr.eval, v, hs, Env.get_vz, Ext.refl_wk, a1g2StToVal, pa2Val, pa2RoleVal, paSpkOpt]
  · simp [Expr.eval, v, hq, Env.get_vs, Ext.step_wk]

end Branches2

/-- Clamped handler agreement: `a1sHandle2Dsl` evaluates to the shallow `sigAuth1KeyStep`
    under `AgInv2`. -/
theorem a1sHandle2Dsl_eval (S : Setup) (K k : Nat) (q : AuthQuery S) (st : SigAuth1KeySimState S)
    (hInv : AgInv2 K (k + 1) st.fg) :
    (a1sHandle2Dsl S K).eval (.cons (a1sSt2ToVal K st) (.cons (authQueryToVal q) .nil)) =
      a1sRS2Val K <$> sigAuth1KeyStep S K q st := by
  have hB := AgInv2.bnd K (k + 1) st.fg hInv
  let env0 : Env [a1sStTy, authQueryTy] := .cons (a1sSt2ToVal K st) (.cons (authQueryToVal q) .nil)
  change (a1sHandle2Dsl S K).eval env0 = _
  rcases hfg : st.forgery with _ | fgVal
  · simp only [a1sHandle2Dsl, a1sStep2C, bindV, caseSumV, Comp.iteC, Comp.caseSumC, Comp.eval,
      isSomeE, a1sFg, v, Expr.eval, env0, a1sSt2ToVal, hfg]
    rw [a1sPreC_eval2 S K _ .vz (.vs .vz) st q (by simp [Ext.refl_wk, Env.get_vz, hfg])
      (by simp [Ext.refl_wk, Env.get_vz, Env.get_vs]) hfg hB.base.spkBundles_le
      hB.base.principals_le]
    let envD : Env (Ty.unit :: Ty.sum a1sRS Ty.unit :: [a1sStTy, authQueryTy]) :=
      Env.cons () (Env.cons (Sum.inr ()) env0)
    have hDel : (a1sDelegate2C S K (Var.vz : Var [a1sStTy, authQueryTy] a1sStTy)
        (Var.vs Var.vz : Var [a1sStTy, authQueryTy] authQueryTy)).eval envD =
        a1sRS2Val K <$> sigAuth1KeyDelegate S K q st :=
      a1sDelegate2C_eval S K _ k (Var.vz : Var [a1sStTy, authQueryTy] a1sStTy)
        (Var.vs Var.vz : Var [a1sStTy, authQueryTy] authQueryTy) st q rfl rfl hInv
    simp only [envD, env0, a1sSt2ToVal, hfg] at hDel
    rcases hb : a1sSendBundle? q with _ | bu
    · simp only [pure_bind]
      have hs := sigAuth1KeyStep_of_bundle_none S K q st hfg hb
      rw [hs]
      simp only [Ext.refl_wk, Env.get_vz]
      exact hDel
    · have hs := sigAuth1KeyStep_of_bundle_some S K q st bu hfg hb
      rw [hs]
      simp only [a1sSendCheckShallow2, sigAuth1KeySend, bind_assoc, map_bind]
      refine bind_congr fun fg' => ?_
      cases hf' : fg'.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
        simp only [Ext.refl_wk, Env.get_vz]
        exact hDel
      · simp [Env.get_vz, a1sRS2Val]
  · simp [a1sHandle2Dsl, a1sStep2C, Comp.iteC, Comp.eval, isSomeE, a1sFg, Expr.eval, v, env0, hfg,
      Env.get_vz, sigAuth1KeyStep, aNone]

end SignalPqxdh.Security.ReductionDsl.AuthHs
