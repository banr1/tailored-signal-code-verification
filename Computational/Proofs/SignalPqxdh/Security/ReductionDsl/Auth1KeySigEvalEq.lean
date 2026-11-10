/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhGrow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import VCVio.EvalDist.Monad.Basic

/-!
# End-to-End Evaluation of the One-Key `Auth` `GapSigEufCma` DSL Program

**Checked by Lean.** Proves that evaluating `sigAuth1KeyProg` agrees pointwise with the shallow
reduction `sigReductionAuth1Key`, preserving the list-length invariant `AgInv` across steps.
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

theorem sigAuth1KeyDelegate_agInv (S : Setup) (K k : Nat) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) (h : AgInv K (k + 1) st.fg.sim) :
    ∀ x ∈ support (sigAuth1KeyDelegate S K q st), AgInv K k x.2.fg.sim := by
  intro x hx
  unfold sigAuth1KeyDelegate at hx
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨out, fg'⟩, hmem, rfl⟩
  exact fgAuth1KeyStepHalt_agInv true st.targetParty S.N_spk_tot K k st.targetPk st.targetPk q
    st.fg h (out, fg') hmem

theorem sigAuth1KeySend_agInv (S : Setup) (K k : Nat) (q : AuthQuery S) (bu : PreKeyBundleInput)
    (st : SigAuth1KeySimState S) (h : AgInv K (k + 1) st.fg.sim) :
    ∀ x ∈ support (sigAuth1KeySend S K q bu st), AgInv K k x.2.fg.sim := by
  intro x hx
  unfold sigAuth1KeySend at hx
  simp only [support_bind, Set.mem_iUnion] at hx
  rcases hx with ⟨fg', _, hx⟩
  split at hx
  · simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact AgInv.mono K k st.fg.sim h
  · exact sigAuth1KeyDelegate_agInv S K k q st h x hx

theorem sigAuth1KeyStep_agInv (S : Setup) (K k : Nat) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) (h : AgInv K (k + 1) st.fg.sim) :
    ∀ x ∈ support (sigAuth1KeyStep S K q st), AgInv K k x.2.fg.sim := by
  unfold sigAuth1KeyStep
  split
  · intro x hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact AgInv.mono K k st.fg.sim h
  · split
    · exact sigAuth1KeySend_agInv S K k _ _ st h
    · exact sigAuth1KeySend_agInv S K k _ _ st h
    · exact sigAuth1KeyDelegate_agInv S K k _ st h

private theorem sigAuth1KeyDelegate_agInv2 (S : Setup) (K k : Nat) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) (h : AgInv2 K (k + 1) st.fg) :
    ∀ x ∈ support (sigAuth1KeyDelegate S K q st), AgInv2 K k x.2.fg := by
  intro x hx
  unfold sigAuth1KeyDelegate at hx
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨out, fg'⟩, hmem, rfl⟩
  exact fgAuth1KeyStepHalt_agInv2 true st.targetParty S.N_spk_tot K k st.targetPk st.targetPk
    q st.fg h (out, fg') hmem

private theorem sigAuth1KeySend_agInv2 (S : Setup) (K k : Nat) (q : AuthQuery S)
    (bu : PreKeyBundleInput) (st : SigAuth1KeySimState S) (h : AgInv2 K (k + 1) st.fg) :
    ∀ x ∈ support (sigAuth1KeySend S K q bu st), AgInv2 K k x.2.fg := by
  intro x hx
  unfold sigAuth1KeySend at hx
  simp only [support_bind, Set.mem_iUnion] at hx
  rcases hx with ⟨fg', _, hx⟩
  split at hx
  · simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact AgInv2.mono K k st.fg h
  · exact sigAuth1KeyDelegate_agInv2 S K k q st h x hx

private theorem sigAuth1KeyStep_agInv2 (S : Setup) (K k : Nat) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) (h : AgInv2 K (k + 1) st.fg) :
    ∀ x ∈ support (sigAuth1KeyStep S K q st), AgInv2 K k x.2.fg := by
  unfold sigAuth1KeyStep
  split
  · intro x hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact AgInv2.mono K k st.fg h
  · split
    · exact sigAuth1KeySend_agInv2 S K k _ _ st h
    · exact sigAuth1KeySend_agInv2 S K k _ _ st h
    · exact sigAuth1KeyDelegate_agInv2 S K k _ st h

theorem a1sInitDsl_eval (S : Setup) (pk : Bytes) :
    (a1sInitDsl S).eval (.cons pk .nil) =
      (unifGdhSign (RoKem.sampleIndexRange S.N_id) >>= fun k =>
        unifGdhSign ($ᵗ Bool) >>= fun secb =>
          pure ((), a1sStToVal (SigAuth1KeySimState.empty S secb k pk))) := by
  simp only [a1sInitDsl, bindV, letV, v, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk,
    Comp.eval_letC, eval_sampleIndexC, eval_sampleBoolC, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, a1g_embedPrim_unif]
  refine bind_congr fun k => bind_congr fun secb => ?_
  rfl

private theorem a1sInit2Dsl_eval (S : Setup) (K : Nat) (pk : Bytes) :
    (a1sInit2Dsl S K).eval (.cons pk .nil) =
      (unifGdhSign (RoKem.sampleIndexRange S.N_id) >>= fun k =>
        unifGdhSign ($ᵗ Bool) >>= fun secb =>
          pure ((), a1sSt2ToVal K (SigAuth1KeySimState.empty S secb k pk))) := by
  simp only [a1sInit2Dsl, a1sDummyPa, bindV, letV, v, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk,
    Comp.eval_letC, eval_sampleIndexC, eval_sampleBoolC, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, a1g_embedPrim_unif]
  refine bind_congr fun k => bind_congr fun secb => ?_
  have hSub : a1gClampedSigB S K (FgAuth1KeySimState.empty S secb) =
      min K (min S.N_spk_tot S.N_recv) := by
    unfold a1gClampedSigB FgAuth1KeySimState.empty; dsimp only; omega
  dsimp only [a1sSt2ToVal, SigAuth1KeySimState.empty]
  rw [hSub]; rfl

theorem a1sFinishDsl_eval {S : Setup} (st : SigAuth1KeySimState S) (a : Bool) :
    a1sFinishDsl.eval (.cons (a1sStToVal st) (.cons a .nil)) =
      (pure (st.forgery.getD ([], [])) : OracleComp GdhSignSimSpec (Bytes × Bytes)) := by
  rcases hfg : st.forgery with _ | fgVal <;>
    simp [a1sFinishDsl, eCaseOpt, a1sFg, a1sStToVal, hfg, Comp.eval, Expr.eval, v,
      Env.get_vz]

private theorem a1sFinishDsl_eval2 {S : Setup} (K : Nat) (st : SigAuth1KeySimState S) (a : Bool) :
    a1sFinishDsl.eval (.cons (a1sSt2ToVal K st) (.cons a .nil)) =
      (pure (st.forgery.getD ([], [])) : OracleComp GdhSignSimSpec (Bytes × Bytes)) := by
  rcases hfg : st.forgery with _ | fgVal <;>
    simp [a1sFinishDsl, eCaseOpt, a1sFg, a1sSt2ToVal, hfg, Comp.eval, Expr.eval, v,
      Env.get_vz]

/-- General evaluation equivalence for `sigAuth1KeyProg S K` at any `K`-bounded adversary. -/
theorem sigAuth1KeyProg_eval_eq_of_queryBound (S : Setup) (K : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : IsQueryBoundP (A ()) (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) K)
    (pk : Bytes) :
    (sigAuth1KeyProg S K).eval A pk =
      (do
        let k ← unifGdhSign (RoKem.sampleIndexRange S.N_id)
        let secb ← unifGdhSign ($ᵗ Bool)
        let (_, finalSt) ← runWithGdhSignStep (sigAuth1KeyStep S K) (A ())
          (SigAuth1KeySimState.empty S secb k pk)
        return finalSt.forgery.getD ([], [])) := by
  have hfun : A = (fun _ => A ()) := funext fun ⟨⟩ => rfl
  rw [hfun]
  unfold CostedReduction.eval CostedReduction.impl
  dsimp only [sigAuth1KeyProg]
  rw [a1sInit2Dsl_eval]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun k => bind_congr fun secb => ?_
  refine simulateQ_handlerImpl_bind_eq_runWithGdhSignStep_bind
    (C := authCodec S) (σ := a1sStTy) (α := Bool) (a1sHandle2Dsl S K) (sigAuth1KeyStep S K)
    (a1sSt2ToVal K) (fun n st => AgInv2 K n st.fg)
    (fun n st h => AgInv2.mono K n st.fg h)
    (fun n q st h => ?_)
    (fun n q st h x hx => sigAuth1KeyStep_agInv2 S K n q st h x hx)
    _ (fun p => pure (p.2.forgery.getD ([], [])))
    (fun a st _ => a1sFinishDsl_eval2 K st a)
    (A ()) K hA _ (AgInv2.empty S K secb)
  dsimp only [authCodec]
  rw [a1sHandle2Dsl_eval S K n q st h]
  simp only [a1sRS2Val, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
    agValToAuthResp_authRespToVal]

/-- Evaluating `sigAuth1KeyProg S b.q_total` agrees pointwise with the shallow
    `sigReductionAuth1Key S b A`. -/
theorem sigAuth1KeyProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (pk : Bytes) :
    (sigAuth1KeyProg S b.q_total).eval (fun _ => A.1.run) pk =
      (sigReductionAuth1Key S b A).run pk := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1
    funext q; cases q <;> rfl
  rw [sigAuth1KeyProg_eval_eq_of_queryBound S b.q_total (fun _ => A.1.run) hA pk]
  rfl

end SignalPqxdh.Security.ReductionDsl.AuthHs
