/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhGrow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhEvalEq
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSmall
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhFinish
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# Step-Level Evaluation of the One-Key `Auth` Gap-DH Handler

**Checked by Lean.** Proves that `a1gStepC` and its tuple-keyed variant `a1gStep2C` evaluate to
the shallow `fgAuth1KeyStepHalt` in an arbitrary context.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open SignalPqxdh.Security.FgGapDh1Key Proofs.SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

@[simp] def a1gStToVal {S : Setup} (pa : paramsTy.denote) (st : FgAuth1KeySimState S) :
    a1gStTy.denote :=
  ((pa, fgSimToVal st.sim), st.sigBudget)

@[simp] def a1gRSBVal {S : Setup} (r : AuthResponse × FgAuth1KeySimState S) : RSB.denote :=
  (authRespToVal r.1, (fgSimToVal r.2.sim, r.2.sigBudget))

theorem a1g_embedPrim_unif {α : Type} (p : ProbComp α) :
    _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhOracle.spec)
      (_root_.SignalPqxdh.Security.embedUnif p) = unifGdhSign p := by
  rw [← pqChalIface_liftP (C := sigAndDdhOracle), pqSigAndDdhIface_liftP_eq,
    pqChalIface_liftP]
  rfl

section Branches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ) (st : FgAuth1KeySimState S) (U V : Bytes)
  (useDh1 : Bool) (t sIdx : Nat)

theorem a1gInitPrinC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    (uf : Fin S.N_id)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st.sim)
    (hu : Env.get env (h₃.wk u) = uf.val) (hB : AgBnd K st.sim) :
    (liftGdhToSign ((a1gInitPrinC K pa sim u).eval env) >>= fun r =>
        pure (r.1, (r.2, st.sigBudget))) =
      a1gRSBVal <$> fgAuthInitPrin1KeyGdh useDh1 t U uf st := by
  simp only [a1gInitPrinC]
  ag_unfold
  simp only [hpa, hsim, hu, fgSimToVal, paVal, authStateToVal]
  rw [take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthInitPrin1KeyGdh, List.any_map, Function.comp_def, Prod.map_fst, id_eq]
  cases ha : st.sim.base.principals.any (fun x => x.1 == (uf : Nat))
  · simp only [Bool.false_eq_true, ↓reduceIte, map_bind, map_pure, liftGdhToSign_bind,
      liftGdhToSign_pure, bind_assoc, pure_bind]
    cases hb : (useDh1 && (uf : Nat) == t) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl
  · simp only [↓reduceIte, map_pure, liftGdhToSign_pure, pure_bind]; rfl

theorem a1gGenSpkC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (x : Var Γ₄ (.prod .nat .nat)) (uf : Fin S.N_id) (jf : Fin S.N_recv)
    (hpa : Env.get env (h₁.wk pa) = paVal U V true t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st.sim)
    (hsig : Env.get env (h₃.wk sigB) = st.sigBudget)
    (hx : Env.get env (h₄.wk x) = (uf.val, jf.val)) (hB : AgBnd K st.sim) (ht : (uf : Nat) = t) :
    (a1gGenSpkC S K pa sim sigB x).eval env =
      a1gRSBVal <$> fgAuthGenSPK1KeyGdh true t true t sIdx S K U V uf jf st := by
  simp only [a1gGenSpkC]
  ag_unfold
  simp only [hpa, hsim, hx, hsig, fgSimToVal, paVal, authStateToVal, nRecvEff_mul_fin]
  rw [take_map_of_le _ _ hB.base.spkBundles_le, take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthGenSPK1KeyGdh, ht, beq_self_eq_true, Bool.true_and, ↓reduceIte,
    List.any_map, List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  have hp : (fun x : (Nat × Nat) × SpkBundleEntry => x.1.1 == t && x.1.2 == (jf : Nat)) =
      (fun x => x.1 == (t, (jf : Nat))) := funext fun _ => rfl
  rw [hp]
  cases ha : st.sim.base.spkBundles.any (fun x => x.1 == (t, (jf : Nat)))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hf : List.find? (fun x => x.1 == t) st.sim.base.principals with _ | ⟨i, e⟩
    · simp only [hf, Option.map_none, map_pure]; rfl
    · simp only [hf, Option.map_some]
      cases hz : (st.sigBudget == 0)
      · simp only [Bool.false_eq_true, ↓reduceIte, map_bind, map_pure, sigChalQ_dsl_eval,
          encEC_eval, encKEM_eval, Expr.eval, Env.get_vz, a1g_embedPrim_unif,
          FgGapDh.spkBundleFlatIdx, ht]
        rfl
      · simp only [↓reduceIte, map_pure]; rfl
  · simp only [↓reduceIte, map_pure]; rfl

def a1gPreShallow (useDh1 : Bool) (t sIdx : Nat) (S : Setup) (K : Nat) (U V : Bytes)
    (qv : AuthQuery S) (st : FgAuth1KeySimState S) :
    Option (OracleComp GdhSignSimSpec (AuthResponse × FgAuth1KeySimState S)) :=
  match qv with
  | .initPrin u => some (fgAuthInitPrin1KeyGdh useDh1 t U u st)
  | .genSPK u j =>
    if useDh1 && (u : Nat) == t then
      some (fgAuthGenSPK1KeyGdh useDh1 t useDh1 t sIdx S K U V u j st)
    else none
  | _ => none

theorem a1gPreC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (q : Var Γ₄ authQueryTy) (qv : AuthQuery S)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st.sim)
    (hsig : Env.get env (h₃.wk sigB) = st.sigBudget)
    (hq : Env.get env (h₄.wk q) = authQueryToVal qv) (hB : AgBnd K st.sim) :
    (a1gPreC S K pa sim sigB q).eval env =
      match a1gPreShallow useDh1 t sIdx S K U V qv st with
      | some c => (fun r => Sum.inl (a1gRSBVal r)) <$> c
      | none => pure (Sum.inr ()) := by
  cases qv <;>
    simp only [a1gPreC, caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq, authQueryToVal,
      authQenc, Sum.elim_inl, Sum.elim_inr, a1gPreShallow]
  case initPrin u =>
    have h := congrArg (fun m => (Sum.inl <$> m : OracleComp GdhSignSimSpec
      (RSB.denote ⊕ Unit))) (a1gInitPrinC_eval S K
      (Env.cons ((u : Nat) : Ty.denote .nat) env : Env (.nat :: Δ)) st U V useDh1 t sIdx pa sim
      (.vz : Var (.nat :: Δ) .nat) u (by simp only [Ext.step_wk, Env.get_vs, hpa])
      (by simp only [Ext.step_wk, Env.get_vs, hsim]) rfl hB)
    simp only [bindV, Comp.eval, liftGdhComp_eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_vs, Env.get_vz, hsig]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at h ⊢
    exact h
  case genSPK u j =>
    ag_unfold
    simp only [Sum.elim_inl, Sum.elim_inr, hpa, paVal]
    cases useDh1
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · by_cases ht : (u : Nat) = t
      · rw [a1gGenSpkC_eval S K _ st U V t sIdx pa sim sigB .vz u j ?_ ?_ ?_ ?_ hB ht]
        · simp only [ht, beq_self_eq_true, Bool.true_and, ↓reduceIte, map_eq_bind_pure_comp,
            Function.comp_def, bind_assoc, pure_bind]
        · simp only [Ext.step_wk, Env.get_vs, hpa]
        · simp only [Ext.step_wk, Env.get_vs, hsim]
        · simp only [Ext.step_wk, Env.get_vs, hsig]
        · rfl
      · have hf : ((u : Nat) == t) = false := by simpa using ht
        simp only [hf, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

end Branches

theorem fgAuth1KeyStep_eq_pre (useDh1 : Bool) (t sIdx : Nat) (S : Setup) (K : Nat) (U V : Bytes)
    (qv : AuthQuery S) (st : FgAuth1KeySimState S) :
    fgAuth1KeyStep useDh1 t sIdx S K U V qv st =
      match a1gPreShallow useDh1 t sIdx S K U V qv st with
      | some c => c
      | none => liftAuthSimStep1Key (fgAuthStep useDh1 t sIdx S K U V qv) st := by
  cases qv <;> simp only [fgAuth1KeyStep, a1gPreShallow]
  case genSPK u j =>
    cases h : (useDh1 && (u : Nat) == t)
    · simp only [fgAuthGenSPK1KeyGdh, h, Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]

theorem a1gStepC_eval {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (S : Setup) (K : Nat) (env : Env Δ) (st : FgAuth1KeySimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (stv : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy)
    (qv : AuthQuery S)
    (hst : Env.get env (h₁.wk stv) = a1gStToVal (paVal U V useDh1 t sIdx) st)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv) (hB : AgBnd K st.sim) :
    (a1gStepC S K stv q).eval env =
      (fun r => (authRespToVal r.1, a1gStToVal (paVal U V useDh1 t sIdx) r.2)) <$>
        fgAuth1KeyStepHalt useDh1 t sIdx S K U V qv st := by
  simp only [a1gStepC]
  ag_unfold
  simp only [hst, a1gStToVal]
  rw [a1gPreC_eval S K _ st U V useDh1 t sIdx _ _ _ _ qv ?_ ?_ ?_ ?_ hB]
  · simp only [fgAuth1KeyStepHalt]
    rw [apply_ite (Functor.map _)]
    refine ite_congr ?_ (fun _ => ?_) (fun _ => ?_)
    · simp only [fgSimToVal, paVal, authStateToVal, take_map_of_le _ _ hB.base.principals_le,
        isTargetPrinCorrupted, List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
      rcases hf : List.find? (fun x => x.1 == t) st.sim.base.principals with _ | ⟨i, e⟩
      · simp only [hf, Option.map_none]
      · simp only [hf, Option.map_some]
        rfl
    · simp only [map_pure]
      rfl
    · rw [fgAuth1KeyStep_eq_pre]
      rcases hp : a1gPreShallow useDh1 t sIdx S K U V qv st with _ | c
      · simp only [pure_bind]
        rw [liftGdhComp_eval, fgStepC_eval S K _ st.sim U V useDh1 t sIdx _ _ _ qv ?_ ?_ ?_ hB]
        · simp only [liftAuthSimStep1Key, liftGdhToSign_bind, liftGdhToSign_pure,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        all_goals first | rfl | simp only [Ext.step_wk, Env.get_vs, hq]
      · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, a1gRSBVal]
  all_goals first | rfl | simp only [Ext.step_wk, Env.get_vs, hq]

/-! ## Tuple-keyed evaluation -/

/-- Decodes `(useDh1, t)` into `a1gRole2Ty.denote` with out-of-range sentinel `S.N_id`. -/
def pa2RoleVal (S : Setup) (useDh1 : Bool) (t : Nat) : a1gRole2Ty.denote :=
  if useDh1 then .inl t
  else if t < S.N_send_opk_tot then .inr (.inl (t / S.N_send_opk, t % S.N_send_opk))
  else if t < S.N_send_tot then
    let r := t - S.N_send_opk_tot
    .inr (.inr (r / S.N_send_no_opk, r % S.N_send_no_opk))
  else .inr (.inl (S.N_id, 0))

@[simp] def pa2Val (S : Setup) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat) :
    a1gParams2Ty.denote :=
  (U, (V, (pa2RoleVal S useDh1 t, paSpkOpt S sIdx)))

/-- `K`-clamped signing budget matching `a1g2InitDsl`. -/
def a1gClampedSigB (S : Setup) (K : Nat) (st : FgAuth1KeySimState S) : Nat :=
  min K (min S.N_spk_tot S.N_recv) - (min S.N_spk_tot S.N_recv - st.sigBudget)

@[simp] def a1g2StToVal (S : Setup) (K : Nat) (pa : a1gParams2Ty.denote)
    (st : FgAuth1KeySimState S) : a1g2StTy.denote :=
  ((pa, fgSimToVal st.sim), a1gClampedSigB S K st)

@[simp] def a1g2RSBVal (S : Setup) (K : Nat) (r : AuthResponse × FgAuth1KeySimState S) :
    RSB.denote :=
  (authRespToVal r.1, (fgSimToVal r.2.sim, a1gClampedSigB S K r.2))

private theorem pa2RoleVal_eq_inr (S : Setup) (t : Nat) :
    pa2RoleVal S false t = .inr
      (if t < S.N_send_opk_tot then .inl (t / S.N_send_opk, t % S.N_send_opk)
       else if t < S.N_send_tot then
         .inr ((t - S.N_send_opk_tot) / S.N_send_no_opk, (t - S.N_send_opk_tot) % S.N_send_no_opk)
       else .inl (S.N_id, 0)) := by
  unfold pa2RoleVal
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

private theorem pa2RoleVal_eq_inl (S : Setup) (t : Nat) :
    pa2RoleVal S true t = .inl t := rfl

private theorem a1g_take_min_of_le (K N : Nat) {α : Type} (L : List α) (h : L.length ≤ K) :
    L.take (min K N) = L.take N := by
  have h1 : (L.take K).take N = L.take N := by rw [List.take_of_length_le h]
  rw [List.take_take, Nat.min_comm] at h1
  exact h1

private theorem eval_eCaseSum_elim {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) (env : Env Γ) :
    (eCaseSum s kl kr).eval env =
      Sum.elim (fun a => (kl .vz).eval (.cons a env)) (fun b => (kr .vz).eval (.cons b env))
        (s.eval env) := by
  dsimp only [eCaseSum, Expr.eval]; cases s.eval env <;> rfl

private theorem pa2RoleVal_elim_opk (S : Setup) (useDh1 : Bool) (t : Nat)
    (uf : Fin S.N_id) (i : Fin S.N_send_opk) :
    Sum.elim (fun _ => false)
      (fun b => Sum.elim (fun x : Nat × Nat => (uf : Nat) == x.1 && (i : Nat) == x.2)
        (fun _ => false) b)
      (pa2RoleVal S useDh1 t) = (!useDh1 && (uf : Nat) * S.N_send_opk + (i : Nat) == t) := by
  have hbeq := paTargetChoice_opk_beq S useDh1 t uf i
  cases useDh1
  · rw [pa2RoleVal_eq_inr]
    by_cases ht : t < S.N_send_opk_tot
    · simp only [paTargetChoice, ht, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.true_and, Sum.elim_inr, Sum.elim_inl] at hbeq ⊢
      exact hbeq
    · by_cases ht2 : t < S.N_send_tot
      · simp only [paTargetChoice, ht, ht2, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.true_and, Bool.false_and, Bool.and_false, Sum.elim_inr] at hbeq ⊢
        exact hbeq
      · have hne : ((uf : Nat) == S.N_id) = false := beq_false_of_ne (Nat.ne_of_lt uf.isLt)
        simp only [paTargetChoice, ht, ht2, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.true_and, Bool.false_and, Bool.and_false, Sum.elim_inr, Sum.elim_inl, hne] at hbeq ⊢
        exact hbeq
  · simp only [pa2RoleVal_eq_inl, Sum.elim_inl, Bool.not_true, Bool.false_and]

private theorem pa2RoleVal_elim_noopk (S : Setup) (useDh1 : Bool) (t : Nat)
    (uf : Fin S.N_id) (i : Fin S.N_send_no_opk) :
    Sum.elim (fun _ => false)
      (fun b => Sum.elim (fun _ => false)
        (fun y : Nat × Nat => (uf : Nat) == y.1 && (i : Nat) == y.2) b)
      (pa2RoleVal S useDh1 t) =
      (!useDh1 && S.N_send_opk_tot + ((uf : Nat) * S.N_send_no_opk + (i : Nat)) == t) := by
  have hbeq := paTargetChoice_noopk_beq S useDh1 t uf i
  cases useDh1
  · rw [pa2RoleVal_eq_inr]
    by_cases ht : t < S.N_send_opk_tot
    · simp only [paTargetChoice, ht, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.not_true, Bool.true_and, Bool.false_and, Bool.and_false, Sum.elim_inr, Sum.elim_inl] at hbeq ⊢
      exact hbeq
    · by_cases ht2 : t < S.N_send_tot
      · simp only [paTargetChoice, ht, ht2, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.true_and, Sum.elim_inr] at hbeq ⊢
        exact hbeq
      · simp only [paTargetChoice, ht, ht2, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.true_and, Sum.elim_inr, Sum.elim_inl] at hbeq ⊢
        have hne : ((uf : Nat) == S.N_id) = false := beq_false_of_ne (Nat.ne_of_lt uf.isLt)
        rw [hne, Bool.false_and] at hbeq
        exact hbeq
  · simp only [pa2RoleVal_eq_inl, Sum.elim_inl, Bool.not_true, Bool.false_and]

private theorem a1gClampedSigB_beq_zero {S : Setup} {K k : Nat} {st : FgAuth1KeySimState S}
    (h : AgInv2 K (k + 1) st) :
    (a1gClampedSigB S K st == 0) = (st.sigBudget == 0) := by
  unfold a1gClampedSigB
  have hle := h.2.2.1
  have hrem := h.2.2.2
  by_cases hz : st.sigBudget = 0
  · simp [hz]
  · simp [hz]; omega

private theorem a1gClampedSigB_sub_one {S : Setup} {K k : Nat} {st : FgAuth1KeySimState S}
    (h : AgInv2 K (k + 1) st) (hz : (st.sigBudget == 0) = false) :
    a1gClampedSigB S K st - 1 =
      min K (min S.N_spk_tot S.N_recv) - (min S.N_spk_tot S.N_recv - (st.sigBudget - 1)) := by
  unfold a1gClampedSigB
  have hle := h.2.2.1
  have hpos : st.sigBudget ≠ 0 := by simpa using hz
  omega

section TupleEval

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)

private theorem fgInitPrin2C_eval (st : FgAuthSimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat) (uf : Fin S.N_id)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hu : Env.get env (h₃.wk u) = uf.val) (hB : AgBnd K st) :
    (fgInitPrin2C K pa sim u).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.initPrin uf) st := by
  simp only [fgInitPrin2C, eCaseSum, pa2U, pa2Role]
  ag_unfold
  simp only [hpa, hsim, hu, fgSimToVal, pa2Val, authStateToVal]
  rw [take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthStep, List.any_map, Function.comp_def, Prod.map_fst, id_eq]
  cases ha : st.base.principals.any (fun x => x.1 == (uf : Nat))
  · simp only [Bool.false_eq_true, ↓reduceIte, map_bind, map_pure]
    cases useDh1
    · simp only [pa2RoleVal_eq_inr, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
    · simp only [pa2RoleVal_eq_inl, Bool.true_and]
      by_cases hb : (uf : Nat) = t
      · simp only [hb, beq_self_eq_true, ↓reduceIte]; rfl
      · simp only [beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [↓reduceIte, map_pure]; rfl

private theorem fgGenSpk2C_eval (st : FgAuthSimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    (uf : Fin S.N_id) (jf : Fin S.N_recv)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, jf.val)) (hB : AgBnd K st) :
    (fgGenSpk2C K pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.genSPK uf jf) st := by
  simp only [fgGenSpk2C, pa2V, pa2TS]
  ag_unfold
  simp only [hpa, hsim, hx, fgSimToVal, pa2Val, authStateToVal]
  rw [take_map_of_le _ _ hB.base.spkBundles_le, take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthStep, List.any_map, List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  have hp : (fun x : (Nat × Nat) × SpkBundleEntry => x.1.1 == (uf : Nat) && x.1.2 == (jf : Nat)) =
      (fun x => x.1 == ((uf : Nat), (jf : Nat))) := funext fun _ => rfl
  rw [hp]
  cases ha : st.base.spkBundles.any (fun x => x.1 == ((uf : Nat), (jf : Nat)))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hf : List.find? (fun x => x.1 == (uf : Nat)) st.base.principals with _ | ⟨i, e⟩
    · simp only [hf, Option.map_none, map_pure]; rfl
    · simp only [hf, Option.map_some, map_bind, map_pure]
      rw [hx, hpa]
      simp only [pa2Val]
      have hts := paSpkOpt_beq S sIdx uf jf
      refine bind_congr' rfl fun x => bind_congr' rfl fun x_1 => bind_congr' rfl fun x_2 => ?_
      have hSig {sk1 sk2 m1 m2 r : Bytes} (hsk : sk1 = sk2) (hm : m1 = m2) :
          (query (spec := PrimBaseSpec + gapDhOracleSpec)
            (Sum.inl (Sum.inr (PrimQuery.sigSign sk1 m1 r))) :
            OracleComp _ Bytes) =
          FgGapDh.primGdhQ (.sigSign sk2 m2 r) := by subst hsk hm; rfl
      refine bind_congr' (hSig rfl ?_) fun x_3 => ?_
      · congr 1
        by_cases hs : sIdx < S.N_spk_tot <;>
          simp only [paSpkOpt, FgGapDh.spkBundleFlatIdx, hs, ↓reduceIte] at hts ⊢ <;>
          simp only [hts] <;>
          (by_cases heq : (uf : Nat) * S.N_recv + (jf : Nat) = sIdx
           · simp only [heq, beq_self_eq_true, ↓reduceIte]
           · simp only [beq_false_of_ne heq, Bool.false_eq_true, ↓reduceIte])
      · by_cases hs : sIdx < S.N_spk_tot <;>
          simp only [paSpkOpt, FgGapDh.spkBundleFlatIdx, hs, ↓reduceIte] at hts ⊢ <;>
          simp only [hts] <;> rfl
  · simp only [↓reduceIte, map_pure]; rfl

set_option maxHeartbeats 4000000 in
private theorem fgSend2C_eval_opk (st : FgAuthSimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    (uf : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AgBnd K st) :
    (fgSend2C S K true pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.sendOPK uf i b m0 m1) st := by
  rw [agS_step_opk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [fgSend2C, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE, buOpkB, hx,
      preKeyBundleToVal, bundleV, hb, Bool.not_false, Option.isNone_none, map_pure, aNone, hsim]
    rfl
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  simp only [fgSend2C, sendGuardE, ↓reduceIte, v, bindV, letV, caseOptV, eCaseOpt, eFind, eAny,
    eval_natEq, sidEq, eLet2, eLet, eval_eCaseSum_elim, nat2Eq, fsBase, fsPows, fsL, fsRootL, fsUpd, fsMk,
    pa2U, pa2Role, q4, stSecb, stPrin, stSpks, stSess,
    stUsedS, stUpd, stMk, buIkB, buSpkB, buSpkSig, buSpkId, buOpkB, buPqspkB, buPqspkSig, buPqspkId,
    peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, encEC_eval, encKEM_eval, firstMsgADE_evalHs,
    seMk, hdMk, optFst, optSnd, aNone, aSendFresh, aSendUnfresh, isSomeE,
    Comp.eval_letC, Comp.eval_liftChal, eval_sampleBytes32C, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, Sum.elim_inl,
    hx, hsim, hpa, hb, pa2Val, preKeyBundleToVal, bundleV,
    PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_sigVerify, PTag.dec_kemEncaps,
    PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend,
    PTag.dec_aeadEnc, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    agS_base, agS_pows, agS_fgL, agS_rootL, agS_usedS, agS_prin, agS_spks, agS_secb,
    twoSideC_eval, twoSideOptC_eval, patchC_eval, mkSecretPosC_eval, rootPatchC_eval]
  rw [pa2RoleVal_elim_opk S useDh1 t uf i]
  simp only [fgRunSendAuthGdh, initSessionSlotIdx, take_map_of_le _ _ hB.base.usedSendSessions_le,
    take_map_of_le _ _ hB.base.principals_le, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]; rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [any_sid_iff _ _ (SessionId.sendOPK uf i)]
  swap
  · intro x; cases x with
    | sendOPK u i' =>
      dsimp only [sessionIdToVal, sidV, Sum.elim]
      by_cases h1 : u = uf
      · subst h1
        by_cases h2 : i' = i
        · subst h2; simp
        · have h3 : ¬ (i'.val = i.val) := fun e => h2 (Fin.ext e)
          rw [beq_false_of_ne h3,
            beq_false_of_ne (a := SessionId.sendOPK u i) (b := SessionId.sendOPK u i')
              (fun e => h2 (SessionId.sendOPK.inj e).2.symm)]; simp
      · have h3 : ¬ (u.val = uf.val) := fun e => h1 (Fin.ext e)
        rw [beq_false_of_ne h3,
          beq_false_of_ne (a := SessionId.sendOPK uf i) (b := SessionId.sendOPK u i')
            (fun e => h1 (SessionId.sendOPK.inj e).1.symm)]; simp
    | _ => simp [sessionIdToVal, sidV]
  by_cases hsid : st.base.usedSendSessions.contains (SessionId.sendOPK uf i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑uf) st.base.principals = none
  · simp only [hp, Option.map_none, map_pure]; rfl
  obtain ⟨⟨idx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq]
  refine agS_peel _ (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agFindHonest_eq, embedPrim_map, agS_embedPrim_eq]
  refine agS_ite _ ?_ (fun _ => agS_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine agS_peelS _ ?_ (fun ok => ?_)
  · rw [koskBundleOkPowsC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ b
      (by simp [preKeyBundleToVal, bundleV, hb]) hB.base]; rfl
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ rfl (fun ekASkRaw => ?_)
  refine agS_peelS _ rfl (fun kemCoins => ?_)
  refine agS_peelS _ rfl (fun ephASk => ?_)
  refine agS_peelS _ rfl (fun spqrCoins => ?_)
  refine agS_peelS _ ?_ (fun sigPk => ?_)
  · rw [resolveSigPkC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agResolveSigPk_eq, agS_embedPrim_eq]
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v1 => ?_)
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v2 => ?_)
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ (agS_kem_congr rfl rfl) (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peelS _ rfl (fun ekAPkRaw => ?_)
  refine agS_peelS _ ?_ (fun spkSk => ?_)
  · rw [lookupSpkSkC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ hB.base.spkBundles_le]
    rfl
  refine agS_peel _ fgPosToVal rfl (fun p1 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p2 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p3 => ?_)
  refine agS_peel _ (Option.map fgPosToVal) ?_ (fun p4 => ?_)
  · simp only [hb, Option.map_some, computeOptPos]; rfl
  refine agS_peel _ (fun r => (drKeyToVal r.1, List.map fgPatchEntryToVal r.2)) ?_ (fun pr => ?_)
  · rw [agS_optRT, agList_fgPatchEntry_roundtrip', valToFgPos_fgPosToVal, valToFgPos_fgPosToVal,
      valToFgPos_fgPosToVal]
  refine agS_peelS _ rfl (fun ephAPk => ?_)
  refine agS_peelS _ (agS_x25519_congr rfl rfl) (fun dhR => ?_)
  refine agS_peel _ fgPosToVal rfl (fun posR => ?_)
  refine agS_peel _ (fun r => (r.1, List.map rootEntryToVal r.2)) ?_ (fun rr => ?_)
  · rw [valToFgPos_fgPosToVal, agList_rootEntry_roundtrip']; rfl
  refine agS_peelS _ rfl (fun mkSeed => ?_)
  refine agS_peelS _ rfl (fun ck1 => ?_)
  refine agS_peelS _ rfl (fun sp => ?_)
  rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peel _ msgKeysToVal rfl (fun mk => ?_)
  refine agS_peelS _ (agS_aead_congr rfl ?_ ?_) (fun ct => ?_)
  · simp [firstMsgAD, encodeEC, pbBytesField, principalEntryToVal]
  · rcases peer with _ | ⟨k, pE⟩ <;> (simp [principalEntryToVal]; try rfl)
  refine agS_pure_ite _ ?_
  rw [take_map_of_le _ _ hB.base.spkBundles_le]
  rcases peer with _ | ⟨k, pE⟩
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal]
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal, List.any_map, Function.comp_def, spkBundleEntryToVal, bne]

set_option maxHeartbeats 4000000 in
private theorem fgSend2C_eval_noopk (st : FgAuthSimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    (uf : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AgBnd K st) :
    (fgSend2C S K false pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.sendNoOPK uf i b m0 m1) st := by
  rw [agS_step_noopk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  swap
  · simp only [fgSend2C, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE, buOpkB, hx,
      preKeyBundleToVal, bundleV, hb, Option.isSome_some, map_pure, aNone, hsim, Bool.false_eq_true]
    rfl
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [fgSend2C, sendGuardE, Bool.false_eq_true, ↓reduceIte, v, bindV, letV, caseOptV,
    eCaseOpt, eFind, eAny, eval_natEq, sidEq, eLet2, eLet, eval_eCaseSum_elim, nat2Eq, fsBase, fsPows,
    fsL, fsRootL, fsUpd, fsMk, pa2U, pa2Role, q4, stSecb, stPrin, stSpks, stSess, stUsedS,
    stUpd, stMk, buIkB, buSpkB, buSpkSig, buSpkId, buOpkB, buPqspkB, buPqspkSig, buPqspkId,
    peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, encEC_eval, encKEM_eval,
    firstMsgADE_evalHs, seMk, hdMk, optFst, optSnd, aNone, aSendFresh, aSendUnfresh, isSomeE,
    Comp.eval_letC, Comp.eval_liftChal, eval_sampleBytes32C, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, Sum.elim_inl, Sum.elim_inr,
    hx, hsim, hpa, hb, pa2Val, preKeyBundleToVal, bundleV,
    PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_sigVerify, PTag.dec_kemEncaps,
    PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend,
    PTag.dec_aeadEnc, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    agS_base, agS_pows, agS_fgL, agS_rootL, agS_usedS, agS_prin, agS_spks, agS_secb,
    twoSideC_eval, twoSideOptC_eval, patchC_eval, mkSecretPosC_eval, rootPatchC_eval]
  rw [pa2RoleVal_elim_noopk S useDh1 t uf i]
  simp only [fgRunSendAuthGdh, initSessionSlotIdx, take_map_of_le _ _ hB.base.usedSendSessions_le,
    take_map_of_le _ _ hB.base.principals_le]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]; rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [any_sid_iff _ _ (SessionId.sendNoOPK uf i)]
  swap
  · intro x; cases x with
    | sendNoOPK u i' =>
      dsimp only [sessionIdToVal, sidV, Sum.elim]
      by_cases h1 : u = uf
      · subst h1
        by_cases h2 : i' = i
        · subst h2; simp
        · have h3 : ¬ (i'.val = i.val) := fun e => h2 (Fin.ext e)
          rw [beq_false_of_ne h3,
            beq_false_of_ne (a := SessionId.sendNoOPK u i) (b := SessionId.sendNoOPK u i')
              (fun e => h2 (SessionId.sendNoOPK.inj e).2.symm)]; simp
      · have h3 : ¬ (u.val = uf.val) := fun e => h1 (Fin.ext e)
        rw [beq_false_of_ne h3,
          beq_false_of_ne (a := SessionId.sendNoOPK uf i) (b := SessionId.sendNoOPK u i')
            (fun e => h1 (SessionId.sendNoOPK.inj e).1.symm)]; simp
    | _ => simp [sessionIdToVal, sidV]
  by_cases hsid : st.base.usedSendSessions.contains (SessionId.sendNoOPK uf i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑uf) st.base.principals = none
  · simp only [hp, Option.map_none, map_pure]; rfl
  obtain ⟨⟨idx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq]
  refine agS_peel _ (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agFindHonest_eq, embedPrim_map, agS_embedPrim_eq]
  refine agS_ite _ ?_ (fun _ => agS_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine agS_peelS _ ?_ (fun ok => ?_)
  · rw [koskBundleOkPowsC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ b
      (by simp [preKeyBundleToVal, bundleV, hb]) hB.base]; rfl
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ rfl (fun ekASkRaw => ?_)
  refine agS_peelS _ rfl (fun kemCoins => ?_)
  refine agS_peelS _ rfl (fun ephASk => ?_)
  refine agS_peelS _ rfl (fun spqrCoins => ?_)
  refine agS_peelS _ ?_ (fun sigPk => ?_)
  · rw [resolveSigPkC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agResolveSigPk_eq, agS_embedPrim_eq]
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v1 => ?_)
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v2 => ?_)
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ (agS_kem_congr rfl rfl) (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peelS _ rfl (fun ekAPkRaw => ?_)
  refine agS_peelS _ ?_ (fun spkSk => ?_)
  · rw [lookupSpkSkC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ hB.base.spkBundles_le]
    rfl
  refine agS_peel _ fgPosToVal rfl (fun p1 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p2 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p3 => ?_)
  refine agS_peel _ (Option.map fgPosToVal) ?_ (fun p4 => ?_)
  · simp only [hb, Option.map_none, computeOptPos, map_pure]; try rfl
  refine agS_peel _ (fun r => (drKeyToVal r.1, List.map fgPatchEntryToVal r.2)) ?_ (fun pr => ?_)
  · rw [agS_optRT, agList_fgPatchEntry_roundtrip', valToFgPos_fgPosToVal, valToFgPos_fgPosToVal,
      valToFgPos_fgPosToVal]
  refine agS_peelS _ rfl (fun ephAPk => ?_)
  refine agS_peelS _ (agS_x25519_congr rfl rfl) (fun dhR => ?_)
  refine agS_peel _ fgPosToVal rfl (fun posR => ?_)
  refine agS_peel _ (fun r => (r.1, List.map rootEntryToVal r.2)) ?_ (fun rr => ?_)
  · rw [valToFgPos_fgPosToVal, agList_rootEntry_roundtrip']; rfl
  refine agS_peelS _ rfl (fun mkSeed => ?_)
  refine agS_peelS _ rfl (fun ck1 => ?_)
  refine agS_peelS _ rfl (fun sp => ?_)
  rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peel _ msgKeysToVal rfl (fun mk => ?_)
  refine agS_peelS _ (agS_aead_congr rfl ?_ ?_) (fun ct => ?_)
  · simp [firstMsgAD, encodeEC, pbBytesField, principalEntryToVal]
  · rcases peer with _ | ⟨k, pE⟩ <;> (simp [principalEntryToVal]; try rfl)
  refine agS_pure_ite _ ?_
  rw [take_map_of_le _ _ hB.base.spkBundles_le]
  rcases peer with _ | ⟨k, pE⟩
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal]
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal, List.any_map, Function.comp_def, spkBundleEntryToVal, bne]

theorem fgStep2C_eval (st : FgAuthSimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    (qv : AuthQuery S)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hq : Env.get env (h₃.wk q) = authQueryToVal qv) (hB : AgBnd K st) :
    (fgStep2C S K pa sim q).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V qv st := by
  cases qv <;>
    simp only [fgStep2C, caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq, authQueryToVal,
      authQenc, Sum.elim_inl, Sum.elim_inr]
  case initPrin u =>
    exact fgInitPrin2C_eval S K _ U V useDh1 t sIdx st pa sim .vz u hpa hsim rfl hB
  case corruptIK u =>
    exact fgCorruptC_eval (hsim := hsim) (uf := u) (hu := rfl) (hB := hB) ..
  case genSPK u j =>
    exact fgGenSpk2C_eval S K _ U V useDh1 t sIdx st pa sim .vz u j hpa hsim rfl hB
  case genOPK u j o =>
    exact fgGenOpkC_eval (hsim := hsim) (uf := u) (jf := j) (of := o) (hx := rfl) (hB := hB) ..
  case sendOPK u i b m0 m1 =>
    exact fgSend2C_eval_opk S K _ U V useDh1 t sIdx st pa sim .vz u i b m0 m1 hpa hsim rfl hB
  case sendNoOPK u i b m0 m1 =>
    exact fgSend2C_eval_noopk S K _ U V useDh1 t sIdx st pa sim .vz u i b m0 m1 hpa hsim rfl hB
  case recvOPK k j o msg =>
    exact fgRecvB_eval_opk (hsim := hsim) (hx := rfl) (hB := hB) ..
  case recvNoOPK k j l msg =>
    exact fgRecvB_eval_noopk (hsim := hsim) (hx := rfl) (hB := hB) ..
  case roQuery sec =>
    exact fgRoC_eval (hsim := hsim) (hsec := rfl) (hB := hB) ..
  case roRootQuery rk dh =>
    exact fgRoRootC_eval (hsim := hsim) (hx := rfl) ..
  case revealDhSecrets =>
    simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, Sum.elim_inl, Sum.elim_inr,
      Comp.eval, Expr.eval, aNone, hsim, fgAuthStep, map_pure, authRespToVal, authRenc]
  case registerKey sk =>
    exact fgRegisterC_eval (hsim := hsim) (hsk := rfl) ..

theorem a1gInitPrin2C_eval (st : FgAuth1KeySimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat) (uf : Fin S.N_id)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st.sim)
    (hu : Env.get env (h₃.wk u) = uf.val) (hB : AgBnd K st.sim) :
    (liftGdhToSign ((a1gInitPrin2C K pa sim u).eval env) >>= fun r =>
        pure (r.1, (r.2, a1gClampedSigB S K st))) =
      a1g2RSBVal S K <$> fgAuthInitPrin1KeyGdh useDh1 t U uf st := by
  simp only [a1gInitPrin2C, eCaseSum, pa2U, pa2Role]
  ag_unfold
  simp only [hpa, hsim, hu, fgSimToVal, pa2Val, authStateToVal]
  rw [take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthInitPrin1KeyGdh, List.any_map, Function.comp_def, Prod.map_fst, id_eq]
  cases ha : st.sim.base.principals.any (fun x => x.1 == (uf : Nat))
  · simp only [Bool.false_eq_true, ↓reduceIte, map_bind, map_pure, liftGdhToSign_bind,
      liftGdhToSign_pure, bind_assoc, pure_bind]
    cases useDh1
    · simp only [pa2RoleVal_eq_inr, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
    · simp only [pa2RoleVal_eq_inl, Bool.true_and]
      by_cases hb : (uf : Nat) = t
      · simp only [hb, beq_self_eq_true, ↓reduceIte]; rfl
      · simp only [beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [↓reduceIte, map_pure, liftGdhToSign_pure, pure_bind]; rfl

theorem a1gGenSpk2C_eval {k : Nat} (st : FgAuth1KeySimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (x : Var Γ₄ (.prod .nat .nat)) (uf : Fin S.N_id) (jf : Fin S.N_recv)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V true t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st.sim)
    (hsig : Env.get env (h₃.wk sigB) = a1gClampedSigB S K st)
    (hx : Env.get env (h₄.wk x) = (uf.val, jf.val))
    (hI : AgInv2 K (k + 1) st) (ht : (uf : Nat) = t) :
    (a1gGenSpk2C K pa sim sigB x).eval env =
      a1g2RSBVal S K <$> fgAuthGenSPK1KeyGdh true t true t sIdx S K U V uf jf st := by
  have hB := hI.bnd
  simp only [a1gGenSpk2C, pa2V, pa2TS]
  ag_unfold
  simp only [hpa, hsim, hx, hsig, fgSimToVal, pa2Val, authStateToVal, a1gClampedSigB_beq_zero hI]
  rw [take_map_of_le _ _ hB.base.spkBundles_le, take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthGenSPK1KeyGdh, ht, beq_self_eq_true, Bool.true_and, ↓reduceIte,
    List.any_map, List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  have hp : (fun x : (Nat × Nat) × SpkBundleEntry => x.1.1 == t && x.1.2 == (jf : Nat)) =
      (fun x => x.1 == (t, (jf : Nat))) := funext fun _ => rfl
  rw [hp]
  cases ha : st.sim.base.spkBundles.any (fun x => x.1 == (t, (jf : Nat)))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hf : List.find? (fun x => x.1 == t) st.sim.base.principals with _ | ⟨i, e⟩
    · simp only [hf, Option.map_none, map_pure]; rfl
    · simp only [hf, Option.map_some]
      cases hz : (st.sigBudget == 0)
      · have hts := paSpkOpt_beq S sIdx uf jf
        simp only [ht] at hts
        simp only [Bool.false_eq_true, ↓reduceIte, map_bind, map_pure, sigChalQ_dsl_eval,
          encEC_eval, encKEM_eval, Expr.eval, Env.get_vz, a1g_embedPrim_unif,
          FgGapDh.spkBundleFlatIdx, ht, a1gClampedSigB_sub_one hI hz]
        refine bind_congr' rfl fun x_1 => bind_congr' rfl fun x_2 => ?_
        have hSc {m1 m2 : Bytes} (hm : m1 = m2) :
            sigChalQ m1 = sigChalQ m2 := by subst hm; rfl
        refine bind_congr' (hSc ?_) fun sig1 =>
          bind_congr' rfl fun seed => bind_congr' rfl fun kp => bind_congr' rfl fun sig2 => ?_
        · congr 1
          by_cases hs : sIdx < S.N_spk_tot <;>
            simp only [paSpkOpt, hs, ↓reduceIte] at hts ⊢ <;> simp only [hts]
        · by_cases hs : sIdx < S.N_spk_tot <;>
            simp only [paSpkOpt, hs, ↓reduceIte] at hts ⊢ <;> simp only [hts] <;> rfl
      · simp only [↓reduceIte, map_pure]; rfl
  · simp only [↓reduceIte, map_pure]; rfl

theorem a1gPre2C_eval {k : Nat} (st : FgAuth1KeySimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (q : Var Γ₄ authQueryTy) (qv : AuthQuery S)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st.sim)
    (hsig : Env.get env (h₃.wk sigB) = a1gClampedSigB S K st)
    (hq : Env.get env (h₄.wk q) = authQueryToVal qv) (hI : AgInv2 K (k + 1) st) :
    (a1gPre2C K pa sim sigB q).eval env =
      match a1gPreShallow useDh1 t sIdx S K U V qv st with
      | some c => (fun r => Sum.inl (a1g2RSBVal S K r)) <$> c
      | none => pure (Sum.inr ()) := by
  have hB := hI.bnd
  cases qv <;>
    simp only [a1gPre2C, caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq, authQueryToVal,
      authQenc, Sum.elim_inl, Sum.elim_inr, a1gPreShallow]
  case initPrin u =>
    have h := congrArg (fun m => (Sum.inl <$> m : OracleComp GdhSignSimSpec
      (RSB.denote ⊕ Unit))) (a1gInitPrin2C_eval S K
      (Env.cons ((u : Nat) : Ty.denote .nat) env : Env (.nat :: Δ)) U V useDh1 t sIdx st pa sim
      (.vz : Var (.nat :: Δ) .nat) u (by simp only [Ext.step_wk, Env.get_vs, hpa])
      (by simp only [Ext.step_wk, Env.get_vs, hsim]) rfl hB)
    simp only [bindV, Comp.eval, liftGdhComp_eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_vs, Env.get_vz, hsig]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at h ⊢
    exact h
  case genSPK u j =>
    simp only [eCaseSum, pa2Role]
    ag_unfold
    simp only [Sum.elim_inl, Sum.elim_inr, hpa, pa2Val]
    cases useDh1
    · simp only [pa2RoleVal_eq_inr, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · simp only [pa2RoleVal_eq_inl]
      by_cases ht : (u : Nat) = t
      · rw [a1gGenSpk2C_eval S K _ U V t sIdx st pa sim sigB .vz u j ?_ ?_ ?_ ?_ hI ht]
        · simp only [ht, beq_self_eq_true, Bool.true_and, ↓reduceIte, map_eq_bind_pure_comp,
            Function.comp_def, bind_assoc, pure_bind]
        · simp only [Ext.step_wk, Env.get_vs, hpa]
        · simp only [Ext.step_wk, Env.get_vs, hsim]
        · simp only [Ext.step_wk, Env.get_vs, hsig]
        · rfl
      · have hf : ((u : Nat) == t) = false := by simpa using ht
        simp only [hf, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private theorem findMap2C_eval (pa : Var Γ₁ a1gParams2Ty) (N : Nat) {τ : Ty pqSig} {α : Type}
    (g : α → τ.denote) (L : List α) (xs : Expr pqxdhOps Δ (.list τ))
    (f : (x : Var (τ :: .opt (B 32) :: Δ) τ) → CG (τ :: .opt (B 32) :: Δ) (B 32))
    (fS : α → OracleComp GdhSimSpec Bytes)
    (hU : (pa2U (v pa)).eval env = U)
    (hV : (pa2V (v pa)).eval env = V)
    (hxs : xs.eval env = L.map g)
    (hf : ∀ x : α, (f .vz).eval (.cons (g x) (.cons none env)) = fS x) :
    (findMap2C pa N xs f).eval env = FgGapDh.findMapMGdh fS U V (L.take N) := by
  dsimp only [findMap2C, foldMV, Comp.eval, Expr.eval]
  rw [hxs]
  apply agFoldML_findMap_take
  · intro x
    dsimp only [caseOptV, bindV, v, pa2U, pa2V, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]
    rw [hf x]
    simp only [v, Expr.eval] at hU hV
    simp only [eval_queryDdh, Expr.eval, Env.get_vs, Env.get_vz, hU, hV]
    rfl
  · intro _ _
    rfl

private theorem logScan2C_eval (st : FgAuthSimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (off : Nat)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st) :
    (logScan2C K pa sim off).eval env =
      FgGapDh.findMGdh (fun cand => FgGapDh.ddhGdhQ U V cand)
        ((st.advRoLog.take K).map (fun s => List.take 32 (List.drop off s))) := by
  simp only [logScan2C, findMV, eMap, fsLog, slice32, pa2U, pa2V, v,
    eval_queryDdh, Comp.eval, Expr.eval_bytesTakeK, PNat.val_ofNat, Expr.eval_bytesDrop, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hpa, hsim, fgSimToVal, pa2Val, ← List.map_take, List.take_take, min_self, agFindML_eq_findMGdh]

theorem fgExtract2C_eval (st : FgAuthSimState S)
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy)
    (hpa : Env.get env (h₁.wk pa) = pa2Val S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hB : AgBnd K st) (hresp : st.respRecs.length ≤ K) :
    (fgExtract2C S K pa sim).eval env = extractCdhFromAuthSimState S useDh1 K U V st := by
  have hdh1 : (pa2Dh1 (v pa)).eval env = useDh1 := by
    cases useDh1 <;>
      simp [pa2Dh1, eCaseSum, pa2Role, v, hpa, pa2Val, pa2RoleVal_eq_inr, pa2RoleVal_eq_inl,
        Expr.eval]
  dsimp only [fgExtract2C, Comp.eval]
  rw [hdh1]
  simp only [extractCdhFromAuthSimState]
  cases useDh1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [eval_bindV_caseOpt_ret, logScan2C_eval S K _ U V false t sIdx st pa sim 96 hpa hsim]
    refine bind_congr' rfl (fun o => ?_)
    rcases o with _ | z; swap; · rfl
    rw [eval_bindV_caseOpt_ret,
      findMap2C_eval (U := U) (V := V) (g := authSessionEntryToVal) (L := st.base.sessions)
        (fS := initAuthDh3CandGdh),
      a1g_take_min_of_le K S.N_dh st.base.sessions hB.base.sessions_le]
    · refine bind_congr' rfl (fun o => ?_)
      rcases o with _ | z; swap; · rfl
      rw [eval_bindV, findMap2C_eval (U := U) (V := V) (g := respRecToVal) (L := st.respRecs)
        (fS := respAuthDh3CandGdh S st.base.spkBundles),
        a1g_take_min_of_le K S.N_sess_tot st.respRecs hresp]
      · refine bind_congr' rfl (fun o => ?_)
        rcases o with _ | z <;> rfl
      · simp [v, hpa, pa2Val, Expr.eval]
      · simp [v, hpa, pa2Val, Expr.eval]
      · simp [v, hsim, fgSimToVal, Expr.eval]
      · intro r
        exact fg2RespCandC_eval (rv := r) (hsim := by simp [hsim]) (hr := rfl) (hB := hB) ..
    · simp [v, hpa, pa2Val, Expr.eval]
    · simp [v, hpa, pa2Val, Expr.eval]
    · simp [v, hsim, fgSimToVal, authStateToVal, Expr.eval]
    · rintro ⟨_, _, _, _, _, _, _, _, _ | ⟨_, _⟩, _, _, _⟩
      · rfl
      · dsimp only [Comp.eval]; rw [queryPrimC_x25519_eval]; rfl
  · simp only [↓reduceIte]
    rw [eval_bindV_caseOpt_ret, logScan2C_eval S K _ U V true t sIdx st pa sim 32 hpa hsim]
    refine bind_congr' rfl (fun o => ?_)
    rcases o with _ | z; swap; · rfl
    rw [eval_bindV, fg2SpkPowsC_eval (st := st) (hB := hB)]
    swap; · simp [hsim]
    refine bind_congr_of_forall_mem_support _ (fun pows hpows => ?_)
    rw [agSpkPows_eq] at hpows
    have hlen := agMemSupport_mapML_length _ _ _ hpows
    simp only [List.length_map, List.length_take] at hlen
    have hBspk := hB.base.spkBundles_le
    have hplen : pows.length ≤ min K S.N_dh := by omega
    rw [eval_bindV_caseOpt_ret,
      findMap2C_eval (U := U) (V := V) (g := authSessionEntryToVal) (L := st.base.sessions)
        (fS := initAuthDh1CandWithPowsGdh st.base.principals pows st.advKeyPows),
      a1g_take_min_of_le K S.N_dh st.base.sessions hB.base.sessions_le]
    · refine bind_congr' rfl (fun o => ?_)
      rcases o with _ | z; swap; · rfl
      rw [eval_bindV, findMap2C_eval (U := U) (V := V) (g := respRecToVal) (L := st.respRecs)
        (fS := respAuthDh1CandGdh S st.base.spkBundles),
        a1g_take_min_of_le K S.N_sess_tot st.respRecs hresp]
      · refine bind_congr' rfl (fun o => ?_)
        rcases o with _ | z <;> rfl
      · simp [v, hpa, pa2Val, Expr.eval]
      · simp [v, hpa, pa2Val, Expr.eval]
      · simp [v, hsim, fgSimToVal, Expr.eval]
      · intro r
        exact fg2RespCandC_eval (rv := r) (hsim := by simp [hsim]) (hr := rfl) (hB := hB) ..
    · simp [v, hpa, pa2Val, Expr.eval]
    · simp [v, hpa, pa2Val, Expr.eval]
    · simp [v, hsim, fgSimToVal, authStateToVal, Expr.eval]
    · intro s
      exact fg2InitDh1CandC_eval (pows := pows) (sv := s)
        (hsim := by simp [hsim]) (hpows := rfl) (hs := rfl) (hplen := hplen) (hB := hB) ..

end TupleEval

theorem a1gStep2C_eval {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (S : Setup) (K : Nat) {k : Nat} (env : Env Δ) (st : FgAuth1KeySimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (stv : Var Γ₁ a1g2StTy) (q : Var Γ₂ authQueryTy)
    (qv : AuthQuery S)
    (hst : Env.get env (h₁.wk stv) = a1g2StToVal S K (pa2Val S U V useDh1 t sIdx) st)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv) (hI : AgInv2 K (k + 1) st) :
    (a1gStep2C S K stv q).eval env =
      (fun r => (authRespToVal r.1, a1g2StToVal S K (pa2Val S U V useDh1 t sIdx) r.2)) <$>
        fgAuth1KeyStepHalt useDh1 t sIdx S K U V qv st := by
  have hB := hI.bnd
  simp only [a1gStep2C, eCaseSum, pa2Role]
  ag_unfold
  simp only [hst, a1g2StToVal]
  rw [a1gPre2C_eval S K _ U V useDh1 t sIdx st _ _ _ _ qv ?_ ?_ ?_ ?_ hI]
  · simp only [fgAuth1KeyStepHalt]
    rw [apply_ite (Functor.map _)]
    refine ite_congr ?_ (fun _ => ?_) (fun _ => ?_)
    · cases useDh1
      · simp only [pa2Val, pa2RoleVal_eq_inr, Bool.false_and]
      · simp only [fgSimToVal, pa2Val, pa2RoleVal_eq_inl, Bool.true_and, authStateToVal,
          take_map_of_le _ _ hB.base.principals_le, isTargetPrinCorrupted,
          List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
        rcases hf : List.find? (fun x => x.1 == t) st.sim.base.principals with _ | ⟨i, e⟩ <;>
          rw [hf] <;> rfl
    · simp only [map_pure]; rfl
    · rw [fgAuth1KeyStep_eq_pre]
      rcases hp : a1gPreShallow useDh1 t sIdx S K U V qv st with _ | c
      · simp only [pure_bind]
        rw [liftGdhComp_eval, fgStep2C_eval S K _ U V useDh1 t sIdx st.sim _ _ _ qv ?_ ?_ ?_ hB]
        · simp only [liftAuthSimStep1Key, liftGdhToSign_bind, liftGdhToSign_pure,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]; rfl
        all_goals first | rfl | simp only [Ext.step_wk, Env.get_vs, hq]
      · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, a1g2RSBVal]
  all_goals first | rfl | simp only [Ext.step_wk, Env.get_vs, hq]

end SignalPqxdh.Security.ReductionDsl.AuthHs
