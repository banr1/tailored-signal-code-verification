/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim
import Computational.Proofs.ReductionDsl.Size

/-!
# RO and Initiator `DdhStep` Lemmas for `fgKeyIndGapDhProg`

Establishes `DdhStep` contracts for `genSpkGdhB`, `roParsedC`, `initiateGdhB`, and the RO-query
dispatch of `gdhHandle`.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd


theorem genSpkGdhB_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((genSpkGdhB S K pa sm bSt x).eval env) := by
  unfold genSpkGdhB; ddh_step_auto <;>
    simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']


theorem roParsedC_ddhStep (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (B 192)) (env : Env Δ) :
    DdhStep (4 * fgSDone ((v sm).eval env).2.1)
      (fun p => fgRDone p.2.2.1 ≤ fgRDone ((v sm).eval env).2.1 + 1 ∧
        fgSDone p.2.2.1 = fgSDone ((v sm).eval env).2.1)
      ((roParsedC K sm sec).eval env) := by
  unfold roParsedC
  refine ddhStep_ite _ _ _ _ (fun _ => roRawFallbackC_ddhStep K sm sec env) (fun _ => ?_)
  refine ddhStep_ite _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · refine ddhStep_bindV_0 _ _ _ (mkSecretPosC_step _ _) fun p1 hp1 => ?_
    refine ddhStep_bindV_0 _ _ _ (mkSecretPosC_step _ _) fun p2 hp2 => ?_
    refine ddhStep_bindV_0 _ _ _ (mkSecretPosC_step _ _) fun p3 hp3 => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_mono ?_ (fun _ h => h)
      (ddhStep_bindV _ _ _ (fgPatchC_sec_step K _ _ _ _ _ _ _ ?_ ?_ ?_ ?_) fun res hres =>
        ddhStep_ret _ _ ?_)
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · simpa only [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] using hp1
    · simpa only [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] using hp2
    · simpa only [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] using hp3
    · simp only [isSecOptPos, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
    · simpa only [smFgL, smUpd, smMk, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hres
  · refine ddhStep_ite _ _ _ _ (fun _ => ?_) (fun _ => roRawFallbackC_ddhStep K sm sec env)
    refine ddhStep_bindV_0 _ _ _ (mkSecretPosC_step _ _) fun p1 hp1 => ?_
    refine ddhStep_bindV_0 _ _ _ (mkSecretPosC_step _ _) fun p2 hp2 => ?_
    refine ddhStep_bindV_0 _ _ _ (mkSecretPosC_step _ _) fun p3 hp3 => ?_
    refine ddhStep_bindV_0 _ _ _ (mkSecretPosC_step _ _) fun p4Raw hp4 => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_mono ?_ (fun _ h => h)
      (ddhStep_bindV _ _ _ (fgPatchC_sec_step K _ _ _ _ _ _ _ ?_ ?_ ?_ ?_) fun res hres =>
        ddhStep_ret _ _ ?_)
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · simpa only [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] using hp1
    · simpa only [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] using hp2
    · simpa only [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] using hp3
    · simpa only [isSecOptPos, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] using hp4
    · simpa only [smFgL, smUpd, smMk, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hres


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

theorem initiateGdhB_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
      ((initiateGdhB S K pa sm bSt hasOpk x).eval env) := by
  unfold initiateGdhB
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ => ?_)
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _
    (fun _ => ddhStep_ret_none sm _ (by simp only [v, Expr.eval, Ext.step_wk', Env.get_succ']))
    (fun _ _ => ?_)
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computeOptPosInitC_chal _ _ _) fun _ => ?_
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_bindV_tail _ _ _ ?_ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hpatch => ?_
  · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
  · refine ddhStep_letV _ _ _ ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_bindV_zero _ _ _ (chooseInitRandC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_letV _ _ _ ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ret _ _ ?_
    simp only [eCaseOpt, Expr.eval]
    split <;> {
      simpa only [SessPost, smFgL, smUpd, smMk, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hpatch
    }


/-- RO-query `DdhStep` contract for `gdhHandle`: at most `4 * fgSDone` `ddhQ` queries, incrementing
    `fgRDone` by at most `1` and preserving `fgSDone`. -/
theorem gdhHandle_ddhStep_ro (S : Setup) (K : Nat) (st : gdhStateTy.denote) (gq : KeyIndQuery S)
    (hRo : isRoQ gq = true) :
    DdhStep (4 * fgSDone st.2.2.1)
      (fun p => fgRDone p.2.2.2.1 ≤ fgRDone st.2.2.1 + 1 ∧ fgSDone p.2.2.2.1 = fgSDone st.2.2.1)
      ((gdhHandle S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try simp [isRoQ] at hRo
  rename_i sec
  unfold gdhHandle
  dsimp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
    Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
  exact wrapSim_ddhStep (Q := fun L' => fgRDone L' ≤ fgRDone st.2.2.1 + 1 ∧ fgSDone L' = fgSDone st.2.2.1)
    _ _ _ (roParsedC_ddhStep K _ _ _)


end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
