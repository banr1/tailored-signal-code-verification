/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigSessionSplit
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsInit
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsAccept
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs

/-!
# One-Key `GapSigEufCma` Reduction Wiring

**Checked by Lean.** Packages the costed `ReductionDsl` one-key `GapSigEufCma` reduction
`sigKeyInd1KeyDslProg` as `sigKeyInd1KeyDslAdv` and proves its block-size bounds, semantic query
bounds, and advantage equality with `sigReductionKeyInd1Key`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp

/-- The `ReductionDsl` one-key `GapSigEufCma` reduction adversary matching
    `(KeyIndCostedReductionFamily.eval R).sig b A` when `R.sig = sigKeyInd1KeyDslProg S`. -/
def sigKeyInd1KeyDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapSigEufCmaAdv where
  run pk := (sigKeyInd1KeyDslProg S b).eval (fun _ => A.1.run) pk
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_ddh := gdhQueryBudget S b
  q_prim := gdhPrimQueryBudget S b

/-- Output block-size bound for `sigKeyInd1KeyDslProg S b`. -/
theorem sigKeyInd1KeyDslProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    SignalPqxdh.LegacyCosted.GRedBlockBounded S b ℓ (sigKeyInd1KeyDslProg S b) :=
  gredBlockBounded_of_totalCost_le pqSamplers_sizeHonest
    one_le_pqChalIface_qCost one_le_pqSamplers_sCost S b ℓ (sigKeyInd1KeyDslProg S b)
    (sigKeyInd1KeyDslProg_totalCost_le_stepCostBudget S b)

section SemanticSig1KeyDdhBound

open SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

set_option allowUnsafeReducibility true
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Env.get Ext.wk pqChalIface pqPrimIface pqSigAndDdhIface
  gapDhDdhOracle sigAndDdhOracle sigAndDdhSpec pqSamplers keyIndCodec

private def SigDdhStep {α : Type} (m : ℕ) (Q : α → Prop)
    (oa : OracleComp (PrimBaseSpec + sigAndDdhSpec) α) : Prop :=
  oa.IsQueryBoundP (fun q => isDdhChalQuery q = true) m ∧ ∀ x ∈ support oa, Q x

private theorem hwSig1KeyDdh : ∀ g x,
    (fun q : (PrimBaseSpec + sigAndDdhSpec).Domain => isDdhChalQuery q = true)
      (pqSigAndDdhIface.enc g x) →
    1 ≤ SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight g := by
  intro g x hx
  rcases g with t | (m | ⟨⟩)
  · simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
  · simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
  · simp [SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]

private theorem hUSig1KeyDdh : ∀ n,
    (pqSigAndDdhIface.fwdU n).IsQueryBoundP (fun q => isDdhChalQuery q = true) 0 := by
  intro n
  change IsQueryBoundP
    (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) :
      OracleComp (PrimBaseSpec + sigAndDdhSpec) _)
    (fun q => isDdhChalQuery q = true) 0
  rw [isQueryBoundP_query_iff]
  simp [isDdhChalQuery]

private theorem mem_support_embedGdhSigDdh {α : Type}
    (oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α) (y : α) :
    y ∈ support (embedGdhSigDdh oa) ↔ y ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    rcases q with pq | dq
    · change y ∈ support (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl pq)) >>=
          fun u => embedGdhSigDdh (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u
    · change y ∈ support (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => embedGdhSigDdh (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u

private theorem isQueryBoundP_embedGdhSigDdh {α : Type}
    (oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α) :
    ∀ {m : ℕ}, oa.IsQueryBoundP (fun q => q.isRight = true) m →
      (embedGdhSigDdh oa).IsQueryBoundP (fun q => isDdhChalQuery q = true) m := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m _
    simp [embedGdhSigDdh_pure]
  | query_bind q r ih =>
    intro m h
    rw [isQueryBoundP_query_bind_iff] at h
    rcases q with pq | dq
    · change IsQueryBoundP
        (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl pq)) >>=
          fun u => embedGdhSigDdh (r u))
        (fun q => isDdhChalQuery q = true) m
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by simp [isDdhChalQuery]), fun u => ?_⟩
      simp only [isDdhChalQuery, Bool.false_eq_true, ↓reduceIte]
      exact ih u (by simpa using h.2 u)
    · change IsQueryBoundP
        (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => embedGdhSigDdh (r u))
        (fun q => isDdhChalQuery q = true) m
      rw [isQueryBoundP_query_bind_iff]
      have hPos : 0 < m := h.1.resolve_left (by simp)
      refine ⟨Or.inr hPos, fun u => ?_⟩
      simp only [isDdhChalQuery, ↓reduceIte]
      exact ih u (by simpa using h.2 u)

private theorem embedGdhSigDdh_sigDdhStep {α : Type} {m : ℕ} {Q : α → Prop}
    {oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α}
    (h : DdhStep m Q oa) :
    SigDdhStep m Q (embedGdhSigDdh oa) :=
  ⟨isQueryBoundP_embedGdhSigDdh oa h.1,
   fun x hx => h.2 x ((mem_support_embedGdhSigDdh oa x).mp hx)⟩

private theorem sig1KeyInitPrinB_fgL_eq (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (u : Var Γ₂ .nat) (env : Env Δ) :
    ∀ r ∈ support ((sig1KeyInitPrinB K s u).eval env),
      r.2.1.2.1 = ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env).1.2.1 := by
  unfold sig1KeyInitPrinB
  simp only [Comp.eval]
  split
  · intro r hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl
  · intro r hr
    simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨s0, _, ik, _, rfl⟩ := hr
    simp [s1Upd, s1Mk, smUpd, smMk, smFgL, s1Fg, v, Expr.eval, Env.get_succ', Ext.step_wk']

private theorem sig1KeyTargetGenSpkB_fgL_eq (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ) :
    ∀ r ∈ support ((sig1KeyTargetGenSpkB K s x).eval env),
      r.2.1.2.1 = ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env).1.2.1 := by
  unfold sig1KeyTargetGenSpkB
  simp only [Comp.eval]
  split
  · intro r hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · simp only [caseOptV, Comp.eval]
    cases (eFind K (stPrin (s1Base (v s))) fun e => natEq (.fst (v e)) (.fst (v x))).eval env with
    | none =>
      intro r hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    | some uE =>
      simp only [Comp.eval]
      split
      · intro r hr
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr; simp [v, Expr.eval, Env.get_succ', Ext.step_wk']
      · intro r hr
        simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
        obtain ⟨spkSk, _, spkPk, _, sig1, _, seed, _, kp, _, sig2, _, rfl⟩ := hr
        simp [s1Upd, s1Mk, smUpd, smMk, smFgL, s1Fg, v, Expr.eval, Env.get_succ', Ext.step_wk']

private theorem sig1KeyInitiateCheckC_fgL_eq (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ initQTy) (env : Env Δ) :
    ∀ pre ∈ support ((sig1KeyInitiateCheckC S K s x).eval env),
      ∀ res, pre = .inl res →
        res.2.1.2.1 = ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env).1.2.1 := by
  unfold sig1KeyInitiateCheckC
  rw [letV_eval]
  simp only [bindV, Comp.eval, mem_support_bind_iff]
  rintro _ ⟨fg, _, hpre⟩ res rfl
  split at hpre
  · simp only [Expr.eval, support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hpre
    subst hpre
    simp [s1Upd, s1Mk, s1Fg, v, Expr.eval]
  · simp only [Expr.eval, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hpre

private theorem v_zero_eval_cons {Γ : List PT} {τ : PT} (x : τ.denote) (env : Env Γ) :
    (v (.zero : Var (τ :: Γ) τ)).eval (.cons x env) = x := rfl

private theorem sig1KeyPreDispatchC_sigDdhStep (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) (env : Env Δ) :
    SigDdhStep 0
      (fun pre => ∀ res, pre = .inl res →
        res.2.1.2.1 = ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env).1.2.1)
      ((sig1KeyPreDispatchC S K s q).eval env) := by
  refine ⟨?_, ?_⟩
  · have hq := Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      hwSig1KeyDdh hUSig1KeyDdh (sig1KeyPreDispatchC S K s q) env
    rwa [sig1KeyPreDispatchC_ddhQueries] at hq
  · unfold sig1KeyPreDispatchC
    dsimp only [Comp.eval]
    split
    · intro pre hpre res hEq
      simp only [Expr.eval, support_pure, Set.mem_singleton_iff] at hpre
      subst hpre; cases hEq; rfl
    · dsimp only [caseSumV, Comp.eval]
      rcases ((v q : Expr pqxdhOps Δ keyIndQueryTy).eval env) with u | q1
      · intro pre hpre res hEq
        simp only [bindV, Comp.eval, Expr.eval, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hpre
        obtain ⟨r, hr, hpre⟩ := hpre; subst hpre; cases hEq
        simpa [v, Expr.eval] using sig1KeyInitPrinB_fgL_eq K s .zero _ r hr
      · dsimp only
        rw [v_zero_eval_cons]
        rcases q1 with _ | q2
        · intro pre hpre res hEq
          simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hpre
          subst hpre; cases hEq
        · dsimp only
          rw [v_zero_eval_cons]
          rcases q2 with x | q3
          · dsimp only [Comp.eval]
            split
            · intro pre hpre res hEq
              simp only [bindV, Comp.eval, Expr.eval, mem_support_bind_iff, support_pure,
                Set.mem_singleton_iff] at hpre
              obtain ⟨r, hr, hpre⟩ := hpre; subst hpre; cases hEq
              simpa [v, Expr.eval] using sig1KeyTargetGenSpkB_fgL_eq K s .zero _ r hr
            · intro pre hpre res hEq
              simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hpre
              subst hpre; cases hEq
          · dsimp only
            rw [v_zero_eval_cons]
            rcases q3 with _ | q4
            · intro pre hpre res hEq
              simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hpre
              subst hpre; cases hEq
            · dsimp only
              rw [v_zero_eval_cons]
              rcases q4 with x | q5
              · intro pre hpre res hEq
                simpa [v, Expr.eval] using sig1KeyInitiateCheckC_fgL_eq S K s .zero _ pre hpre res hEq
              · dsimp only
                rw [v_zero_eval_cons]
                rcases q5 with x | _
                · intro pre hpre res hEq
                  simpa [v, Expr.eval] using sig1KeyInitiateCheckC_fgL_eq S K s .zero _ pre hpre res hEq
                · intro pre hpre res hEq
                  simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hpre
                  subst hpre; cases hEq

private theorem ddhStep_letV_any {Γ : List PT} {τ₁ τ₂ : PT} {m : ℕ} {Q : τ₂.denote → Prop}
    (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ) (hk : ∀ y, DdhStep m Q ((k .zero).eval (.cons y env))) :
    DdhStep m Q ((letV e k).eval env) :=
  ddhStep_letV e k env (hk (e.eval env))

private theorem wrapBase2_ddhStep {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.2.1 = ((v sm).eval env).2.1) ((wrapBase2 pa sm c).eval env) := by
  unfold wrapBase2
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ddhStep_ret _ _ rfl

private theorem wrapSim2_ddhStep {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {m : ℕ}
    {Q : List fgPatchEntryTy.denote → Prop} (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) (env : Env Δ)
    (hc : DdhStep m (fun p => Q p.2.2.1) (c.eval env)) :
    DdhStep m (fun p => Q p.2.2.2.1) ((wrapSim2 pa c).eval env) := by
  unfold wrapSim2
  exact ddhStep_mono (m₁ := m + 0) (by omega) (fun _ hx => hx)
    (ddhStep_bindV _ _ _ hc fun _ hr => ddhStep_ret _ _ hr)

private theorem initPrinGdh2B_ddhStep (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((initPrinGdh2B K pa sm bSt u).eval env) := by
  unfold initPrinGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_; refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ret _ _ ?_
  simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

private theorem genSpkGdh2B_ddhStep (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((genSpkGdh2B K pa sm bSt x).eval env) := by
  unfold genSpkGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_; refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ret _ _ ?_
  simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

private theorem genOpkGdh2B_ddhStep (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((genOpkGdh2B K pa sm bSt x).eval env) := by
  unfold genOpkGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => ddhStep_ret _ _ rfl) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_; refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ret _ _ ?_
  simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

private theorem initiateGdh2B_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
      ((initiateGdh2B S K pa sm bSt hasOpk x).eval env) := by
  have hRet0 : ∀ {Δ' : List PT} [Ext Γ₂ Δ'] (env' : Env Δ'),
      ((v sm).eval env').2.1 = ((v sm).eval env).2.1 →
      DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
        (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
        ((Comp.ret (.pair rNone (v sm)) : Comp pqxdhOps pqGapDhIface Δ' _).eval env') := by
    intro Δ' _ env' hEq
    exact ddhStep_mono (m₁ := 0) (Nat.zero_le _) (fun _ h => h)
      (ddhStep_ret _ _ (by simpa [Expr.eval, hEq] using sessPost_refl ((v sm).eval env).2.1))
  unfold initiateGdh2B
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_; refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (computeOptPosInitC_chal _ _ _) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_mono ?_ (fun _ h => h)
    (ddhStep_bindV (m₂ := 0) _ _ _ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hPatch => ?_)
  · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
  · refine ddhStep_letV_any _ _ _ fun _ => ?_; refine ddhStep_letV _ _ _ ?_; refine ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_letV_any _ _ _ fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (chooseInitRandC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_letV _ _ _ ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ret _ _ ?_
    simp only [eCaseOpt, Expr.eval]
    split <;> simpa only [SessPost, smFgL, smUpd, smMk, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
      Env.get_zero', Env.get_succ'] using hPatch

private theorem acceptOpkGdh2B_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) (env : Env Δ) :
    DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
      (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
      ((acceptOpkGdh2B S K pa sm bSt x).eval env) := by
  have hRet0 : ∀ {Δ' : List PT} [Ext Γ₂ Δ'] (env' : Env Δ'),
      ((v sm).eval env').2.1 = ((v sm).eval env).2.1 →
      DdhStep (4 * (fgRDone ((v sm).eval env).2.1 + fgSDone ((v sm).eval env).2.1))
        (fun p => SessPost ((v sm).eval env).2.1 p.2.2.1)
        ((Comp.ret (.pair rNone (v sm)) : Comp pqxdhOps pqGapDhIface Δ' _).eval env') := by
    intro Δ' _ env' hEq
    exact ddhStep_mono (m₁ := 0) (Nat.zero_le _) (fun _ h => h)
      (ddhStep_ret _ _ (by simpa [Expr.eval, hEq] using sessPost_refl ((v sm).eval env).2.1))
  unfold acceptOpkGdh2B
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ rfl) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ rfl) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
  refine ddhStep_letV_any _ _ _ fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
  refine ddhStep_ite _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
    refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_mono ?_ (fun _ h => h)
      (ddhStep_bindV (m₂ := 0) _ _ _ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hPatch => ?_)
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · dsimp only []; apply finishAcceptGdhC_ddhStep
      simpa only [SessPost, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hPatch
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun _ => ?_
    refine ddhStep_ite _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ => ?_
    refine ddhStep_caseOptV _ _ _ _ (fun _ => hRet0 _ (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ'])) fun _ _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_
    refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) fun _ => ?_; refine ddhStep_bindV_zero _ _ _ (mkSecretPosC_chal _) fun _ => ?_
    refine ddhStep_letV_any _ _ _ fun _ => ?_
    refine ddhStep_mono ?_ (fun _ h => h)
      (ddhStep_bindV (m₂ := 0) _ _ _ (fgPatchC_any_step K _ _ _ _ _ _ _) fun patchR hPatch => ?_)
    · simp only [smFgL, v, Expr.eval, Ext.step_wk', Env.get_succ']; omega
    · dsimp only []; apply finishAcceptGdhC_ddhStep
      simpa only [SessPost, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ'] using hPatch

private theorem gdhHandle2_ddhStep_ro (S : Setup) (K : Nat) (st : gdhState2Ty.denote)
    (gq : KeyIndQuery S) (hRo : isRoQ gq = true) :
    DdhStep (4 * fgSDone st.2.2.1)
      (fun p => fgRDone p.2.2.2.1 ≤ fgRDone st.2.2.1 + 1 ∧ fgSDone p.2.2.2.1 = fgSDone st.2.2.1)
      ((gdhHandle2 S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try simp [isRoQ] at hRo
  rename_i sec
  unfold gdhHandle2
  simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
    Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
  exact wrapSim2_ddhStep (Q := fun L' => fgRDone L' ≤ fgRDone st.2.2.1 + 1 ∧ fgSDone L' = fgSDone st.2.2.1)
    _ _ _ (KeyIndGapDh.roParsedC_ddhStep K _ _ _)

private theorem gdhHandle2_ddhStep_sess (S : Setup) (K : Nat) (st : gdhState2Ty.denote)
    (gq : KeyIndQuery S) (hSess : isSessQ gq = true) :
    DdhStep (4 * (fgRDone st.2.2.1 + fgSDone st.2.2.1))
      (fun p =>
        let r := fgRDone st.2.2.1
        let s := fgSDone st.2.2.1
        (fgRDone p.2.2.2.1 = r ∧ fgSDone p.2.2.2.1 = s) ∨
        (fgRDone p.2.2.2.1 = r + 1 ∧ fgSDone p.2.2.2.1 = s) ∨
        (fgRDone p.2.2.2.1 = r ∧ fgSDone p.2.2.2.1 = s + 1))
      ((gdhHandle2 S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try simp [isSessQ] at hSess
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (initiateGdh2B_ddhStep S K _ _ _ true _ _))
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (initiateGdh2B_ddhStep S K _ _ _ false _ _))
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (acceptOpkGdh2B_ddhStep S K _ _ _ _ _))
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_mono le_rfl (fun _ hp => hp)
      (wrapSim2_ddhStep (Q := SessPost st.2.2.1) _ _ _ (KeyIndGapDh.acceptNoOpkGdhB_ddhStep S K _ _ _ _))

private theorem gdhHandle2_ddhStep_other (S : Setup) (K : Nat) (st : gdhState2Ty.denote)
    (gq : KeyIndQuery S) (hRo : isRoQ gq = false) (hSess : isSessQ gq = false) :
    DdhStep 0 (fun p => p.2.2.2.1 = st.2.2.1)
      ((gdhHandle2 S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq <;> try (simp [isRoQ, isSessQ] at hRo hSess; done)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (initPrinGdh2B_ddhStep K _ _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase2_ddhStep _ _ _ _
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (genSpkGdh2B_ddhStep K _ _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (genOpkGdh2B_ddhStep K _ _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase2_ddhStep _ _ _ _
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact ddhStep_pure _ rfl
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase2_ddhStep _ _ _ _
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapSim2_ddhStep (Q := fun L' => L' = st.2.2.1) _ _ _ (registerGdhB_ddhStep _ _ _ _)
  · unfold gdhHandle2
    simp only [keyIndCodec, keyIndQenc, letV_eval, caseSumV, Comp.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval, smBase]
    exact wrapBase2_ddhStep _ _ _ _

private theorem delegateFgC_sigDdhStep (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) (env : Env Δ)
    {m : ℕ} {Q : List fgPatchEntryTy.denote → Prop}
    (hGdh : ∀ pa : params2Ty.denote,
      DdhStep m (fun p => Q p.2.2.2.1)
        ((gdhHandle2 S K).eval
          (.cons (pa, ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env).1)
            (.cons ((v q : Expr pqxdhOps Δ keyIndQueryTy).eval env) .nil)))) :
    SigDdhStep m (fun r : S1RS.denote => Q r.2.1.2.1) ((delegateFgC S K s q).eval env) := by
  unfold delegateFgC
  rw [letV_eval]
  simp only [bindV, Comp.eval, liftGdhToSigDdh_eval, Comp.rename_eval]
  set paVal : params2Ty.denote := (pa2Zero (s1Pk (v s))).eval env
  have hEnvEq :
      Env.ofRename (renamePair .zero (.succ (Ext.wk q)))
        (Env.cons (t := gdhState2Ty) (((pa2Zero (s1Pk (v s))).pair (s1Fg (v s))).eval env) env) =
      Env.cons (t := gdhState2Ty) (paVal, ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env).1)
        (Env.cons (t := keyIndQueryTy) ((v q : Expr pqxdhOps Δ keyIndQueryTy).eval env) .nil) := by
    simp [Env.ofRename, renamePair, paVal, s1Fg, v, Expr.eval]
  rw [hEnvEq]
  have hStep := embedGdhSigDdh_sigDdhStep (hGdh paVal)
  refine ⟨?_, ?_⟩
  · exact (isQueryBoundP_bind (n := m) (m := 0) hStep.1
      (fun r _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  · intro y hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    simpa [s1Upd, s1Mk, s1Fg, v, Expr.eval] using hStep.2 r hr

private theorem sig1KeyHandleC_sigDdhStep (S : Setup) (K : ℕ)
    (st : sig1KeyStTy.denote) (gq : KeyIndQuery S)
    {m : ℕ} {Q : List fgPatchEntryTy.denote → Prop}
    (hRefl : Q st.1.2.1)
    (hGdh : ∀ pa : params2Ty.denote,
      DdhStep m (fun p => Q p.2.2.2.1)
        ((gdhHandle2 S K).eval (.cons (pa, st.1) (.cons ((keyIndCodec S).qenc gq) .nil)))) :
    SigDdhStep m (fun r : S1RS.denote => Q r.2.1.2.1)
      ((sig1KeyHandleC S K).eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  unfold sig1KeyHandleC
  simp only [bindV, caseSumV, Comp.eval]
  have hPre := sig1KeyPreDispatchC_sigDdhStep S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
    (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))
  refine ⟨?_, ?_⟩
  · refine (isQueryBoundP_bind (n := 0) (m := m) hPre.1 (fun pre _ => ?_)).mono (by omega)
    rcases pre with res | u
    · simp only [Comp.eval, v, Expr.eval]
      exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le m)
    · have hDel := delegateFgC_sigDdhStep S K
        (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
        (Δ := .unit :: .sum S1RS .unit :: [sig1KeyStTy, keyIndQueryTy])
        .zero (.succ .zero)
        (.cons u (.cons (.inr u) (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
        hGdh
      exact hDel.1
  · intro y hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨pre, hpre, hy⟩ := hy
    rcases pre with res | u
    · simp only [Comp.eval, v, Expr.eval, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      have hEq := hPre.2 (.inl y) hpre y rfl
      exact hEq.symm ▸ hRefl
    · have hDel := delegateFgC_sigDdhStep S K
        (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
        (Δ := .unit :: .sum S1RS .unit :: [sig1KeyStTy, keyIndQueryTy])
        .zero (.succ .zero)
        (.cons u (.cons (.inr u) (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
        hGdh
      exact hDel.2 y hy

private theorem simulateQ_handlerImpl_sigDdhPhi {S : Setup} {σ : PT} {α : Type}
    (fgLOf : σ.denote → List fgPatchEntryTy.denote)
    (h : Comp pqxdhOps pqSigAndDdhIface [σ, (keyIndCodec S).Q] (.prod (keyIndCodec S).R σ))
    (hStepRo : ∀ st gq, isRoQ gq = true →
      SigDdhStep (4 * fgSDone (fgLOf st))
        (fun p => fgRDone (fgLOf p.2) ≤ fgRDone (fgLOf st) + 1 ∧
          fgSDone (fgLOf p.2) = fgSDone (fgLOf st))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepSess : ∀ st gq, isSessQ gq = true →
      SigDdhStep (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
        (fun p =>
          let r := fgRDone (fgLOf st)
          let s := fgSDone (fgLOf st)
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r + 1 ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s + 1))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepOther : ∀ st gq, isRoQ gq = false → isSessQ gq = false →
      SigDdhStep 0 (fun p => fgLOf p.2 = fgLOf st)
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (oa : OracleComp (unifSpec + keyIndSpec S) α) :
    ∀ (r_rem s_rem : ℕ) (st : σ.denote),
      oa.IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_rem →
      oa.IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_rem →
      ((simulateQ (handlerImpl (C := keyIndCodec S) h) oa).run st).IsQueryBoundP
        (fun q => isDdhChalQuery q = true)
        (fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro r_rem s_rem st _ _
    simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro r_rem s_rem st hRo hSess
    rw [isQueryBoundP_query_bind_iff] at hRo hSess
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases t with uq | gq
    · have hStep0 : (((handlerImpl (C := keyIndCodec S) h) (.inl uq)).run st).IsQueryBoundP
          (fun q => isDdhChalQuery q = true) 0 := by
        have hb := isQueryBoundP_bind (n := 0) (m := 0) (hUSig1KeyDdh uq)
          (fun u _ => isQueryBoundP_pure
            (fun q : (PrimBaseSpec + sigAndDdhSpec).Domain => isDdhChalQuery q = true) (u, st) 0)
        simpa [handlerImpl] using hb
      refine (isQueryBoundP_bind (n := 0)
        (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
        hStep0 fun x hx => ?_).mono (by omega)
      have hst : x.2 = st := by
        simp only [handlerImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨_, _, rfl⟩ := hx; rfl
      rw [← hst]
      exact ih x.1 r_rem s_rem x.2
        (by simpa [_root_.ReductionDsl.onGame] using hRo.2 x.1)
        (by simpa [_root_.ReductionDsl.onGame] using hSess.2 x.1)
    · cases hR : isRoQ gq
      · cases hS : isSessQ gq
        · have hs := hStepOther st gq hR hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => isDdhChalQuery q = true) 0 := by
            have hb := isQueryBoundP_bind (n := 0) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            exact hb
          refine (isQueryBoundP_bind (n := 0)
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
            hRun fun x hx => ?_).mono (by omega)
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          have hEq := hs.2 p hp
          have hCont := ih ((keyIndCodec S).rdec gq p.1) r_rem s_rem p.2
            (by simpa [_root_.ReductionDsl.onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [_root_.ReductionDsl.onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
          rwa [hEq] at hCont
        · have hPos : 0 < s_rem := hSess.1.resolve_left (by simp [_root_.ReductionDsl.onGame, hS])
          obtain ⟨s', rfl⟩ : ∃ s', s_rem = s' + 1 := ⟨s_rem - 1, by omega⟩
          have hs := hStepSess st gq hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => isDdhChalQuery q = true) (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) := by
            have hb := isQueryBoundP_bind
              (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            exact hb
          refine (isQueryBoundP_bind
            (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st) + 1) r_rem s')
            hRun fun x hx => ?_).mono (by rw [fgDdhPhi_sess_step])
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact (ih ((keyIndCodec S).rdec gq p.1) r_rem s' p.2
            (by simpa [_root_.ReductionDsl.onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [_root_.ReductionDsl.onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))).mono
            (fgDdhPhi_le_sess_inc (hs.2 p hp) r_rem s')
      · have hS : isSessQ gq = false := by cases gq <;> simp_all [isRoQ, isSessQ]
        have hPos : 0 < r_rem := hRo.1.resolve_left (by simp [_root_.ReductionDsl.onGame, hR])
        obtain ⟨r', rfl⟩ : ∃ r', r_rem = r' + 1 := ⟨r_rem - 1, by omega⟩
        have hs := hStepRo st gq hR
        have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
            (fun q => isDdhChalQuery q = true) (4 * fgSDone (fgLOf st)) := by
          have hb := isQueryBoundP_bind (n := 4 * fgSDone (fgLOf st)) (m := 0) hs.1
            (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
          exact hb
        refine (isQueryBoundP_bind
          (n := 4 * fgSDone (fgLOf st))
          (m := fgDdhPhi (fgRDone (fgLOf st) + 1) (fgSDone (fgLOf st)) r' s_rem)
          hRun fun x hx => ?_).mono (by rw [fgDdhPhi_ro_step])
        simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨hr_le, hs_eq⟩ := hs.2 p hp
        have hCont := ih ((keyIndCodec S).rdec gq p.1) r' s_rem p.2
          (by simpa [_root_.ReductionDsl.onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
          (by simpa [_root_.ReductionDsl.onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
        rw [hs_eq] at hCont
        exact hCont.mono (fgDdhPhi_mono hr_le le_rfl le_rfl)

private theorem sigKeyInd1KeyProg_ddhBounded_bilinear (S : Setup) (K r_max s_max : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hRo : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_max)
    (hSess : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_max)
    (pk : Bytes) :
    ((sigKeyInd1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true)
      (4 * r_max * s_max + 2 * s_max * (s_max - 1)) := by
  have hInitQ : (((sigKeyInd1KeyProg S K).init).eval (.cons pk .nil)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) 0 := by
    have hq := Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      hwSig1KeyDdh hUSig1KeyDdh (sigKeyInd1KeyProg S K).init (.cons pk .nil)
    dsimp only [sigKeyInd1KeyProg, bindV, s1Prim, liftBase, sIndex, sBool, Comp.queries,
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight] at hq
    exact hq
  have hInitEmpty : ∀ as : (Ty.prod .unit sig1KeyStTy).denote,
      as ∈ support (((sigKeyInd1KeyProg S K).init).eval (.cons pk .nil)) →
      as.2.1.2.1 = [] := by
    intro as has
    change as ∈ support
      ((bindV (s1Prim (sIndex S.N_id)) fun k =>
        bindV (s1Prim sBool) fun secb =>
        Comp.ret (.pair .unit
          (s1Mk (emptySimE (v secb)) (v k) (.var (.succ (.succ .zero)))
            (.nat (min K (min S.N_spk_tot S.N_recv))) .none))).eval (.cons pk .nil)) at has
    simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at has
    obtain ⟨k, _, secb, _, rfl⟩ := has
    simp [emptySimE, smMk, Expr.eval]
  unfold CostedReduction.eval CostedReduction.impl
  refine (isQueryBoundP_bind (n := 0)
    (m := 4 * r_max * s_max + 2 * s_max * (s_max - 1))
    hInitQ fun as has => ?_).mono (by omega)
  have hEmpty := hInitEmpty as has
  have hSim := simulateQ_handlerImpl_sigDdhPhi (fun s : sig1KeyStTy.denote => s.1.2.1)
    (sig1KeyHandleC S K)
    (fun st gq hR => sig1KeyHandleC_sigDdhStep
      (Q := fun L => fgRDone L ≤ fgRDone st.1.2.1 + 1 ∧ fgSDone L = fgSDone st.1.2.1)
      S K st gq ⟨Nat.le_succ _, rfl⟩
      (fun pa => gdhHandle2_ddhStep_ro S K (pa, st.1) gq hR))
    (fun st gq hS => sig1KeyHandleC_sigDdhStep
      (Q := fun L =>
        let r := fgRDone st.1.2.1
        let s := fgSDone st.1.2.1
        (fgRDone L = r ∧ fgSDone L = s) ∨
        (fgRDone L = r + 1 ∧ fgSDone L = s) ∨
        (fgRDone L = r ∧ fgSDone L = s + 1))
      S K st gq (Or.inl ⟨rfl, rfl⟩)
      (fun pa => gdhHandle2_ddhStep_sess S K (pa, st.1) gq hS))
    (fun st gq hR hS => sig1KeyHandleC_sigDdhStep
      (Q := fun L => L = st.1.2.1)
      S K st gq rfl
      (fun pa => gdhHandle2_ddhStep_other S K (pa, st.1) gq hR hS))
    (A as.1) r_max s_max as.2 (hRo as.1) (hSess as.1)
  rw [hEmpty, show fgRDone [] = 0 from rfl, show fgSDone [] = 0 from rfl,
    fgDdhPhi_zero_done] at hSim
  refine (isQueryBoundP_bind
    (n := 4 * r_max * s_max + 2 * s_max * (s_max - 1)) (m := 0)
    hSim fun bs _ => ?_).mono (by omega)
  have hFin := Comp.queryBound_eval (fun q => isDdhChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    hwSig1KeyDdh hUSig1KeyDdh (sigKeyInd1KeyProg S K).finish (.cons bs.2 (.cons bs.1 .nil))
  exact hFin

private theorem sigKeyInd1KeyProg_ddhBounded_gdhQueryBudget (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    ((sigKeyInd1KeyDslProg S b).eval (fun _ => A.1.run) pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (gdhQueryBudget S b) := by
  obtain ⟨hRoRaw, hSend, hRecv, hTotRaw, hOnRaw⟩ := A.2
  have hTot : A.1.run.IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
    convert hTotRaw using 1
    funext q; cases q
    · exact propext ⟨False.elim, Bool.noConfusion⟩
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  let M_ro := min b.q_ro b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  by_cases hLe : 4 * b.q_total ^ 2 ≤ 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)
  · refine (sigKeyInd1KeyProg_ddhBounded S b.q_total b.q_total (fun _ => A.1.run)
      (fun _ => hTot) pk).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * b.q_total * b.q_total ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [Nat.min_eq_left hLe]
    nlinarith
  · have hMin : min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) =
        4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) :=
      Nat.min_eq_right (Nat.le_of_not_le hLe)
    have hRoOn : A.1.run.IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) b.q_ro := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hRoRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isRoQ, isKeyIndRoQuery]
    have hSessOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) S.N_sess_tot := by
      refine isQueryBoundP_or_add (p₁ := isKeyIndSendQuery) (p₂ := isKeyIndRecvQuery) ?_ hSend hRecv
      intro t ht
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isSessQ, isKeyIndSendQuery, isKeyIndRecvQuery]
    have hSessQOn : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) b.q_on := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hOnRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [_root_.ReductionDsl.onGame, isSessQ, isKeyIndOnlineQuery]
    have hRoM : A.1.run.IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) M_ro := by
      by_cases h1 : b.q_ro ≤ b.q_total
      · simpa [M_ro, Nat.min_eq_left h1] using hRoOn
      · simpa [M_ro, Nat.min_eq_right (Nat.le_of_not_le h1)] using isQueryBoundP_of_imp
          (fun t (ht : _root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isRoQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessOnTot : A.1.run.IsQueryBoundP
        (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) (min b.q_on b.q_total) := by
      by_cases hOn : b.q_on ≤ b.q_total
      · simpa [Nat.min_eq_left hOn] using hSessQOn
      · simpa [Nat.min_eq_right (Nat.le_of_not_le hOn)] using isQueryBoundP_of_imp
          (fun t (ht : _root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessM : A.1.run.IsQueryBoundP (_root_.ReductionDsl.onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) M_sess := by
      by_cases h2 : min b.q_on b.q_total ≤ S.N_sess_tot
      · simpa [M_sess, Nat.min_eq_left h2] using hSessOnTot
      · simpa [M_sess, Nat.min_eq_right (Nat.le_of_not_le h2)] using hSessOn
    refine (sigKeyInd1KeyProg_ddhBounded_bilinear S b.q_total M_ro M_sess
      (fun _ => A.1.run) (fun _ => hRoM) (fun _ => hSessM) pk).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [hMin]
    omega

set_option allowUnsafeReducibility true in
attribute [local semireducible] Env.get Ext.wk
end SemanticSig1KeyDdhBound

/-- Semantic query-budget compliance (`q_sig`, `q_ddh`, `q_prim`) for `sigKeyInd1KeyDslAdv`. -/
theorem sigKeyInd1KeyDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigKeyInd1KeyDslAdv S b A).Bounded :=
  ⟨fun pk => sigKeyInd1KeyProg_sigBounded S b.q_total (fun _ => A.1.run) pk,
   fun pk => sigKeyInd1KeyProg_ddhBounded_gdhQueryBudget S b A pk,
   fun pk => sigKeyInd1KeyProg_primBounded_gdhPrimQueryBudget S b.q_total b A pk⟩

/-- Exact equality between `sigKeyInd1KeyDslAdv` and the shallow `sigReductionKeyInd1Key`, whose
    declared primitive budget is the coarser `primQueryBudget S b`. -/
theorem sigKeyInd1KeyDslAdv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    sigKeyInd1KeyDslAdv S b A =
      { sigReductionKeyInd1Key S b A with q_prim := gdhPrimQueryBudget S b } := by
  unfold sigKeyInd1KeyDslAdv sigKeyInd1KeyDslProg
  have hrun : (fun pk => (sigKeyInd1KeyProg S b.q_total).eval (fun _ => A.1.run) pk) =
      (sigReductionKeyInd1Key S b A).run := by
    funext pk
    exact sigKeyInd1KeyProg_eval_eq S b A pk
  rw [hrun]
  rfl

/-- `GapSigEufCma` advantage equality between `sigKeyInd1KeyDslAdv` and `sigReductionKeyInd1Key`. -/
theorem GapSigEufCma_sigKeyInd1KeyDslAdv (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapSigEufCma P isValidDhTriple (sigKeyInd1KeyDslAdv S b A) =
      GapSigEufCma P isValidDhTriple (sigReductionKeyInd1Key S b A) := by
  rw [sigKeyInd1KeyDslAdv_eq]
  rfl

theorem GapSigEufCmaReal_sigKeyInd1KeyDslAdv (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapSigEufCmaReal P isValidDhTriple (sigKeyInd1KeyDslAdv S b A) =
      GapSigEufCmaReal P isValidDhTriple (sigReductionKeyInd1Key S b A) :=
  congrArg ENNReal.toReal (GapSigEufCma_sigKeyInd1KeyDslAdv P isValidDhTriple S b A)

/-! ## Syntactic Program-Size Bounds (`.size`) and Run-Local Output Block-Size Bound -/

section Sig1KeySizeAndWhen

open SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle

private theorem expr_rename_size_aux {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ), (e.rename ρ).size = e.size := by
  induction e <;> intro Δ ρ <;> simp [Expr.rename, Expr.size, *]

@[simp] private theorem expr_rename_size {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (e : Expr O Γ t) :
    (e.rename ρ).size = e.size :=
  expr_rename_size_aux e ρ

private theorem comp_rename_size_aux {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ), (c.rename ρ).size = c.size := by
  induction c <;> intro Δ ρ <;> simp [Comp.rename, Comp.size, *]

@[simp] private theorem comp_rename_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (c : Comp O I Γ t) :
    (c.rename ρ).size = c.size :=
  comp_rename_size_aux c ρ

@[simp] private theorem s1Prim_size {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqPrimIface Γ τ) : (s1Prim c).size = c.size := by
  unfold s1Prim; exact liftBase_size c

@[simp] private theorem liftGdhToSigDdh_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) : (liftGdhToSigDdh c).size = c.size := by
  induction c with
  | query g e =>
    cases g with
    | inl g => rfl
    | inr u => cases u; rfl
  | _ => simp [liftGdhToSigDdh, Comp.size, *]

@[simp] private theorem s1_widenEC_size {Γ : List PT} (e : Expr pqxdhOps Γ (B 33)) :
    (widenEC e).size = e.size + 1 := rfl
@[simp] private theorem s1_qSigDdhSign_size {Γ : List PT} (m : ℕ+) (e : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m e).size = e.size + 1 := rfl

@[simp] private theorem s1_partnerC_size {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).size = 211 := by
  simp only [partnerC, bindV_size, qPow8_size, getDBytes, optBytesEq, eLet2, eLet_size,
    eCaseOpt_size, eqB_size, litB_size, v_size, Comp.size, Expr.size]

@[simp] private theorem s1_chooseRespRandC_size (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K (Δ := Δ) st r).size = _root_.ReductionDsl.bits (min K S.N_dh) + 238 := by
  simp only [chooseRespRandC, bindV_size, gPrim_size, findMV_size, s1_partnerC_size,
    caseOptV_size, sDrKey96_size, v_size, Comp.size, Expr.size]; omega

@[simp] private theorem s1_chooseInitRandC_size (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K (Δ := Δ) st s).size = _root_.ReductionDsl.bits (min K S.N_sess_tot) + 235 := by
  simp only [chooseInitRandC, bindV_size, gPrim_size, findMV_size, s1_partnerC_size,
    caseOptV_size, sDrKey96_size, v_size, Comp.size, Expr.size]; omega

@[simp] private theorem s1_fgPatchC_size (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).size = fgL.size + _root_.ReductionDsl.bits K + 474 := by
  simp only [fgPatchC, entryMatchesC, ddhEqOptC, ddhEqC, fePos1, fePos2, fePos3, fePos4,
    feSs, feDk, feMk, orE, letV_size, bindV_size, findMV_size, caseOptV_size, caseSumV_size,
    gPrim_size, sDrKey96_size, ddhQ_size, eqB_size, v_size, Comp.size, Expr.size]; omega

@[simp] private theorem s1_finishAcceptGdhC_size (S : Setup) (K : Nat) {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    (finishAcceptGdhC S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).size =
      opkPkOpt.size + opks'.size + usedN'.size + usedO'.size + kyb'.size +
        2 * _root_.ReductionDsl.bits (min K S.N_dh) + 530 := by
  cases hasOpk <;> {
    simp only [finishAcceptGdhC, findHonestC, s1_chooseRespRandC_size, isSomeE, qHdr, qKJO, qK, qJ, qO,
      smRaw, smLog, smPows, smMk, smUpd, rDrKey, rAccFresh, eqB_size,
      letV_size, bindV_size, findMV_size, eCaseOpt_size, gPrim_size, qPow8_size,
      v_size, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]; omega }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
private theorem s1_gdhHandle2_size_le_min (S : Setup) (K : Nat) :
    (gdhHandle2 S K).size ≤
      55 * _root_.ReductionDsl.bits K + 30 * _root_.ReductionDsl.bits (min K S.N_dh) +
        3 * _root_.ReductionDsl.bits (min K S.N_sess_tot) + 15000 := by
  simp (config := { maxSteps := 500000 }) only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B,
    genOpkGdh2B, initiateGdh2B, s1_finishAcceptGdhC_size, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase2, wrapSim2, pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget, pa2SpkTarget,
    pa2OpkMode, pa2OpkTarget, ephSidMatchesE, smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    qKJO, qK, qJ, qO, qHdr, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rDrKey, rSpkSk,
    initSidE, natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_size, encKEM_size,
    orE, eLet2, isAdvPowsE,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC, s1_fgPatchC_size,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, s1_chooseInitRandC_size,
    letV_size, bindV_size, caseOptV_size, caseSumV_size, findMV_size, anyMV_size,
    eLet_size, eCaseOpt_size, eCaseSum_size, eFind_size, eAny_size, eMap_size,
    gPrim_size, litB_size, takeKB_size, dropB_size, lenB_size, eqB_size, u32OfNat_size, eqU32_size,
    sBytes32_size, sRandom64_size, sDrKey96_size,
    qX25519_size, qX25519Base_size, qIsCanonical_size, qPow8_size,
    qSigPkGen_size, qSigSign_size, qSigVerify_size,
    qKemKeyGen_size, qKemEncaps_size, qKemDecaps_size, v_size, Comp.size, Expr.size,
    bits_0, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true]
  have : K.min S.N_dh = min K S.N_dh := rfl
  have : K.min S.N_sess_tot = min K S.N_sess_tot := rfl
  omega

private theorem sig1KeyPreDispatchC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyPreDispatchC S K (Δ := Δ) s q).size ≤
      12 * _root_.ReductionDsl.bits K + 5 * _root_.ReductionDsl.bits (min K S.N_dh) + 3000 := by
  simp only [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyInitiateCheckC, extract1KeyC, honestPeerC, findHonestC,
    s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd,
    peIkAPk, peMk, sbSpkPk, sbPqspkPk, sbMk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig, buMk,
    rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq,
    encEC_size, encKEM_size, s1_widenEC_size,
    letV_size, bindV_size, caseOptV_size, caseSumV_size, findMV_size,
    s1Prim_size, s1_qSigDdhSign_size, qSigVerify_size, qPow8_size,
    sBytes32_size, sRandom64_size, qX25519Base_size, qKemKeyGen_size,
    eCaseOpt_size, eAny_size, eFind_size, eqB_size, litB_size, u32OfNat_size,
    v_size, Comp.size, Expr.size, bits_0, bits_1]
  have : K.min S.N_dh = min K S.N_dh := rfl
  omega

private theorem delegateFgC_size_le_min (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (delegateFgC S K (Δ := Δ) s q).size ≤
      55 * _root_.ReductionDsl.bits K + 30 * _root_.ReductionDsl.bits (min K S.N_dh) +
        3 * _root_.ReductionDsl.bits (min K S.N_sess_tot) + 15100 := by
  have hH := s1_gdhHandle2_size_le_min S K
  simp only [delegateFgC, pa2Zero, pa2Mk, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery,
    s1Mk, s1Upd, letV_size, bindV_size, liftGdhToSigDdh_size, comp_rename_size,
    litB_size, v_size, Comp.size, Expr.size, bits_1]
  omega

private theorem delegateFgC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (delegateFgC S K (Δ := Δ) s q).size ≤
      55 * _root_.ReductionDsl.bits K + 46 * _root_.ReductionDsl.bits S.N_dh +
        3 * _root_.ReductionDsl.bits S.N_sess_tot + 15100 := by
  have hM := delegateFgC_size_le_min S K (Δ := Δ) s q
  have b1 := _root_.ReductionDsl.bits_mono (Nat.min_le_right K S.N_dh)
  have b2 := _root_.ReductionDsl.bits_mono (Nat.min_le_right K S.N_sess_tot)
  omega

private theorem sigKeyInd1KeyProg_finish_size_le (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).finish.size ≤ 100 := by
  dsimp only [sigKeyInd1KeyProg]
  simp only [s1Forgery, eCaseOpt_size, litB_size, v_size, Comp.size, Expr.size]; omega

theorem sigKeyInd1KeyProg_size_le (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).size ≤
      67 * _root_.ReductionDsl.bits K + 55 * _root_.ReductionDsl.bits S.N_dh +
        3 * _root_.ReductionDsl.bits S.N_sess_tot + 18500 := by
  have hPre := sig1KeyPreDispatchC_size_le S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  have bPre := _root_.ReductionDsl.bits_mono (Nat.min_le_right K S.N_dh)
  have hDel := delegateFgC_size_le S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := .unit :: (.sum S1RS .unit) :: [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hH : (sig1KeyHandleC S K).size ≤
      67 * _root_.ReductionDsl.bits K + 51 * _root_.ReductionDsl.bits S.N_dh +
        3 * _root_.ReductionDsl.bits S.N_sess_tot + 18200 := by
    simp only [sig1KeyHandleC, bindV_size, caseSumV_size, v_size, Comp.size]; omega
  have hI : (sigKeyInd1KeyProg S K).init.size ≤ 4 * _root_.ReductionDsl.bits S.N_dh + 100 := by
    have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
    have bMin : _root_.ReductionDsl.bits (min K (min S.N_spk_tot S.N_recv)) ≤
        _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono
        (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_left _ _) (by omega)))
    dsimp only [sigKeyInd1KeyProg]
    simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
      bindV_size, s1Prim_size, sIndex_size, sBool_size, v_size, Comp.size, Expr.size]; omega
  have hF := sigKeyInd1KeyProg_finish_size_le S K
  change (sigKeyInd1KeyProg S K).init.size + (sig1KeyHandleC S K).size +
    (sigKeyInd1KeyProg S K).finish.size ≤ _; omega

private theorem sigKeyInd1KeyProg_size_le_K (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).size ≤ 106 * _root_.ReductionDsl.bits K + 18400 := by
  have hPre := sig1KeyPreDispatchC_size_le S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hDelM := delegateFgC_size_le_min S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := .unit :: (.sum S1RS .unit) :: [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  have b1 := _root_.ReductionDsl.bits_mono (Nat.min_le_left K S.N_dh)
  have b2 := _root_.ReductionDsl.bits_mono (Nat.min_le_left K S.N_sess_tot)
  have hH : (sig1KeyHandleC S K).size ≤ 105 * _root_.ReductionDsl.bits K + 18200 := by
    simp only [sig1KeyHandleC, bindV_size, caseSumV_size, v_size, Comp.size]; omega
  have hI : (sigKeyInd1KeyProg S K).init.size ≤ _root_.ReductionDsl.bits K + 100 := by
    have bMin : _root_.ReductionDsl.bits (min K (min S.N_spk_tot S.N_recv)) ≤
        _root_.ReductionDsl.bits K :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    dsimp only [sigKeyInd1KeyProg]
    simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
      bindV_size, s1Prim_size, sIndex_size, sBool_size, v_size, Comp.size, Expr.size]; omega
  have hF := sigKeyInd1KeyProg_finish_size_le S K
  change (sigKeyInd1KeyProg S K).init.size + (sig1KeyHandleC S K).size +
    (sigKeyInd1KeyProg S K).finish.size ≤ _; omega

theorem sigKeyInd1KeyDslProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyDslProg S b).size ≤
      18500 + 125 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hK := sigKeyInd1KeyProg_size_le_K S b.q_total
  have hq : _root_.ReductionDsl.bits b.q_total ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
    apply _root_.ReductionDsl.bits_mono
    unfold _root_.SignalPqxdh.Security.stepCostBudget
    dsimp only
    have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  unfold sigKeyInd1KeyDslProg
  omega

/-- Run-local output block-size bound for `sigKeyInd1KeyDslProg` under `AllGameQueriesFit`. -/
theorem sigKeyInd1KeyDslProg_blocks_when (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) b.q_total)
    (hfit : ∀ u, AllGameQueriesFit ℓ (keyIndCodec S) (A u))
    (x : (B 32).denote)
    (hx : ValFits ℓ (B 32) x)
    (y : (Ty.prod (B 1569) (B 64)).denote)
    (hy : y ∈ supportWhen (pqSigAndDdhIface.AnswerFits ℓ)
      ((sigKeyInd1KeyDslProg S b).eval A x)) :
    ValFits (SignalPqxdh.LegacyCosted.outputSizeBudget S b ℓ) (Ty.prod (B 1569) (B 64)) y := by
  rw [valFits_iff_fits]
  have hx' : (B 32).Fits ℓ x := (valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP
      (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [_root_.ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := (sigKeyInd1KeyDslProg S b).fits_eval_when
    pqO_sizeHonest pqSamplers_sizeHonest ℓ ℓ 0 (fun _ => trivial)
    A b.q_total ℓ hA' hfit x hx' y hy
  have hCost := sigKeyInd1KeyDslProg_totalCost_le_stepCostBudget S b
  have hNq := le_trans
    (gred_nq_le_totalCost one_le_pqChalIface_qCost one_le_pqSamplers_sCost
      (sigKeyInd1KeyDslProg S b) b.q_total)
    hCost
  refine Ty.fits_mono ?_ (Ty.prod (B 1569) (B 64)) y hEval
  unfold SignalPqxdh.LegacyCosted.outputSizeBudget
  have hMul := Nat.mul_le_mul_right ℓ hNq
  nlinarith

end Sig1KeySizeAndWhen

end SignalPqxdh.Security.ReductionDsl.KeyInd
