/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsInit
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim
import Computational.Proofs.ReductionDsl.Size

/-!
# Responder and Handler `DdhStep` Lemmas for `fgKeyIndGapDhProg`

Establishes `DdhStep` contracts for the responder branches (`acceptOpkGdhB`, `acceptNoOpkGdhB`)
and the full `gdhHandle` dispatcher on session and non-RO/non-session queries.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd


private theorem ddhStep_ret_none {Γ₂ Δ : List PT} [Ext Γ₂ Δ] {m : ℕ}
    {L0 : List fgPatchEntryTy.denote} (sm : Var Γ₂ simTy) (env : Env Δ)
    (hL : ((v sm).eval env).2.1 = L0) :
    DdhStep m (fun p => SessPost L0 p.2.2.1)
      ((Comp.ret (I := pqGapDhIface) (.pair rNone (v sm))).eval env) := by
  refine ddhStep_mono (Nat.zero_le m) (fun _ hx => hx) (ddhStep_ret _ _ ?_)
  dsimp only [Expr.eval]
  rw [hL]
  exact sessPost_refl L0

private theorem ddhStep_bindV_tail {Γ : List PT} {τ₁ τ₂ : PT} {m₁ m₂ : ℕ}
    {Q₁ : τ₁.denote → Prop} {Q₂ : τ₂.denote → Prop}
    (c : Comp pqxdhOps pqGapDhIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ) (hm : m₁ ≤ m₂)
    (hc : DdhStep m₁ Q₁ (c.eval env))
    (hk : ∀ x, Q₁ x → DdhStep 0 Q₂ ((k .zero).eval (.cons x env))) :
    DdhStep m₂ Q₂ ((bindV c k).eval env) :=
  ddhStep_mono (m₁ := m₁ + 0) (by omega) (fun _ h => h) (ddhStep_bindV (m₂ := 0) c k env hc hk)

theorem acceptOpkGdhB_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
      ((acceptOpkGdhB S K pa sm bSt x).eval env) := by
  unfold acceptOpkGdhB
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval]))
    (fun _ => ?_)
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval]))
    (fun _ => ?_)
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ite _ _ _ _
      (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
      (fun _ => ?_)
    refine ddhStep_caseOptV _ _ _ _
      (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
      (fun _ _ => ?_)
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_bindV_tail _ _ _ ?_ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hpatch => ?_
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · refine finishAcceptGdhC_ddhStep (Q := SessPost ((v sm).eval env).2.1)
        S K _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
      simpa only [SessPost, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hpatch
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ite _ _ _ _
      (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
      (fun _ => ?_)
    refine ddhStep_caseOptV _ _ _ _
      (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
      (fun _ _ => ?_)
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (mkSecretPosC_chal _) fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_bindV_tail _ _ _ ?_ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hpatch => ?_
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · refine finishAcceptGdhC_ddhStep (Q := SessPost ((v sm).eval env).2.1)
        S K _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
      simpa only [SessPost, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hpatch

theorem acceptNoOpkGdhB_ddhStep (S : Setup) (K : Nat) {Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
      ((acceptNoOpkGdhB S K sm bSt x).eval env) := by
  unfold acceptNoOpkGdhB
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval]))
    (fun _ => ?_)
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval]))
    (fun _ => ?_)
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_bindV_tail _ _ _ ?_ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hpatch => ?_
  · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
  · refine finishAcceptGdhC_ddhStep (Q := SessPost ((v sm).eval env).2.1)
      S K _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    simpa only [SessPost, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
      Env.get_zero', Env.get_succ'] using hpatch


/-- Session-query `DdhStep` contract for `gdhHandle`: at most `4 * (fgRDone + fgSDone)` `ddhQ`
    queries, adding at most one entry to `fgL`. -/
theorem gdhHandle_ddhStep_sess (S : Setup) (K : Nat) (st : gdhStateTy.denote) (gq : KeyIndQuery S)
    (hSess : isSessQ gq = true) :
    DdhStep (4 * (fgRDone st.2.2.1 + fgSDone st.2.2.1))
      (fun p =>
        let r := fgRDone st.2.2.1
        let s := fgSDone st.2.2.1
        (fgRDone p.2.2.2.1 = r ∧ fgSDone p.2.2.2.1 = s) ∨
        (fgRDone p.2.2.2.1 = r + 1 ∧ fgSDone p.2.2.2.1 = s) ∨
        (fgRDone p.2.2.2.1 = r ∧ fgSDone p.2.2.2.1 = s + 1))
      ((gdhHandle S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try simp [isSessQ] at hSess
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono (le_rfl) (fun p hp => hp)
      (wrapSim_ddhStep (Q := SessPost st.2.2.1) _ _ _ (initiateGdhB_ddhStep S K _ _ _ true _ _))
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono (le_rfl) (fun p hp => hp)
      (wrapSim_ddhStep (Q := SessPost st.2.2.1) _ _ _ (initiateGdhB_ddhStep S K _ _ _ false _ _))
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono (le_rfl) (fun p hp => hp)
      (wrapSim_ddhStep (Q := SessPost st.2.2.1) _ _ _ (acceptOpkGdhB_ddhStep S K _ _ _ _ _))
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono (le_rfl) (fun p hp => hp)
      (wrapSim_ddhStep (Q := SessPost st.2.2.1) _ _ _ (acceptNoOpkGdhB_ddhStep S K _ _ _ _))

/-- Non-RO, non-session `DdhStep` contract for `gdhHandle`: `0` `ddhQ` queries and `fgL` unchanged. -/
theorem gdhHandle_ddhStep_other (S : Setup) (K : Nat) (st : gdhStateTy.denote) (gq : KeyIndQuery S)
    (hRo : isRoQ gq = false) (hSess : isSessQ gq = false) :
    DdhStep 0 (fun p => p.2.2.2.1 = st.2.2.1)
      ((gdhHandle S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try (simp [isRoQ, isSessQ] at hRo hSess; done)
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (initPrinGdhB_ddhStep K _ _ _ _ _)
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase_ddhStep _ _ _ _
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (genSpkGdhB_ddhStep S K _ _ _ _ _)
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (genOpkGdhB_ddhStep S K _ _ _ _ _)
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase_ddhStep _ _ _ _
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_pure _ rfl
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase_ddhStep _ _ _ _
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (registerGdhB_ddhStep _ _ _ _)
  · unfold gdhHandle
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase_ddhStep _ _ _ _


end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
