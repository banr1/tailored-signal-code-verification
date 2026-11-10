/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSigStep
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SigBudgetSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SigNoQuery
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Equivalence for `sigReductionAuthProg` and `sigReductionAuthProg2`

Defines the `ReductionDsl` `SigEufCma` adversaries `sigReductionAuthDslAdv` and
`sigReductionAuthDslAdv2`, and proves that both match the `SigEufCma` experiment distribution and
advantage of the shallow reduction `sigReductionAuth`.
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] eufCmaSignOracle

/-- Encoding of the reduction state together with the remaining signing budget. -/
def sigStToVal {S : Setup} (p : SigReductionState (AuthState S) × Nat) : sigStTy.denote :=
  (p.2, sigCoreToVal p.1)

/-- Encoding of a non-`signTwo` step result (the `signTwo` case is a dummy). -/
def resDone {S : Setup} (s : SigReductionState (AuthState S)) :
    SigStepResultPrim (SigReductionState (AuthState S)) AuthResponse → sigStepTy.denote
  | .done r s' => doneVal (r, s')
  | .signTwo .. => doneVal (.noneResp, s)

theorem sigStepC_eval_done (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (s : SigReductionState (AuthState S))
    (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (q : Var Γ₄ authQueryTy) (qv : AuthQuery S) (hf : s.forgery = none)
    (htp : Env.get env (h₁.wk tp) = s.targetParty) (htpk : Env.get env (h₂.wk tpk) = s.targetPk)
    (hst : Env.get env (h₃.wk st) = authStateToVal s.gameState)
    (hq : Env.get env (h₄.wk q) = authQueryToVal qv)
    (hK : AuthBaseListsBounded K s.gameState)
    (hb : ∀ u j, qv = .genSPK u j → u.val ≠ s.targetParty) :
    (sigStepC S K tp tpk st q).eval env = resDone s <$> stepAuthForSigPrim S qv s := by
  obtain ⟨α, D, g, h1, h2⟩ := sigStepC_base S K env s tp tpk st q qv hf htp htpk hst hq hK hb
  rw [h1, h2, Functor.map_map]; rfl

theorem stepAuth_factor (S : Setup) (K : Nat) (s : SigReductionState (AuthState S))
    (qv : AuthQuery S) (hf : s.forgery = none) (hK : AuthBaseListsBounded K s.gameState)
    (hb : ∀ u j, qv = .genSPK u j → u.val ≠ s.targetParty) :
    ∃ (α : Type) (D : OracleComp PrimBaseSpec α)
      (g : α → AuthResponse × SigReductionState (AuthState S)),
      stepAuthForSigPrim S qv s = (fun a => SigStepResultPrim.done (g a).1 (g a).2) <$> D := by
  obtain ⟨α, D, g, -, h2⟩ := sigStepC_base S K (Γ₁ := [Ty.nat]) (Γ₂ := [B 32, Ty.nat])
    (Γ₃ := [authStateTy, B 32, Ty.nat])
    (Γ₄ := [authQueryTy, authStateTy, B 32, Ty.nat])
    (Δ := [authQueryTy, authStateTy, B 32, Ty.nat])
    (Env.cons (authQueryToVal qv) (Env.cons (authStateToVal s.gameState) (Env.cons s.targetPk
      (Env.cons s.targetParty .nil)))) s .vz .vz .vz .vz qv hf rfl rfl rfl rfl hK hb
  exact ⟨α, D, g, h2⟩

def signReqC (u j : Nat) (ik : Bytes) : OracleComp PrimBaseSpec sigStepTy.denote := do
  let sk ← embedUnif sampleScalar32
  let pk ← primQ (.x25519Base sk)
  pure (.inr (sk, (pk, (u, (j, ik)))))

theorem sigStepC_genSpkTarget (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (s : SigReductionState (AuthState S))
    (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (q : Var Γ₄ authQueryTy) (u : Fin S.N_id) (j : Fin S.N_recv) (hf : s.forgery = none)
    (htp : Env.get env (h₁.wk tp) = s.targetParty) (htpk : Env.get env (h₂.wk tpk) = s.targetPk)
    (hst : Env.get env (h₃.wk st) = authStateToVal s.gameState)
    (hq : Env.get env (h₄.wk q) = authQueryToVal (.genSPK u j))
    (hK : AuthBaseListsBounded K s.gameState) (ht : u.val = s.targetParty) :
    (sigStepC S K tp tpk st q).eval env =
      if s.gameState.spkBundles.any (fun x => x.1.1 == u.val && x.1.2 == j.val) then
        pure (doneVal (.noneResp, s))
      else (s.gameState.principals.find? (fun x => x.1 == u.val)).elim
        (pure (doneVal (.noneResp, s))) (fun e => signReqC u.val j.val e.2.ikAPk) := by
  sig_unfold
  rw [ite_eq_left (by simp [natEq, Expr.eval, htp, ht])]
  by_cases hc : (s.gameState.spkBundles.any fun x => x.1.1 == u.val && x.1.2 == j.val) = true
  · rw [ite_eq_left hc, ite_eq_left (by
      simp only [eAny, Expr.eval, nat2Eq, eval_natEq, stSpks, Env.get_vs, Env.get_vz,
        hst, authStateToVal]
      rw [List.take_of_length_le (by simpa using hK.spkBundles_le)]
      simpa [List.any_map, Function.comp_def] using hc)]
    simp [htp, htpk, hst, hf, doneVal, sigCoreToVal, aNone, Expr.eval]
  · rw [ite_eq_right hc, ite_eq_right (by
      simp only [eAny, Expr.eval, nat2Eq, eval_natEq, stSpks, Env.get_vs, Env.get_vz,
        hst, authStateToVal]
      rw [List.take_of_length_le (by simpa using hK.spkBundles_le)]
      simpa [List.any_map, Function.comp_def] using hc)]
    have hfind : ∀ (X : authStateTy.denote) (hX : X = authStateToVal s.gameState),
        List.find? (fun x => x.1 == (u : Nat)) X.2.2.1 =
          (s.gameState.principals.find? (fun x => x.1 == (u : Nat))).map
            (Prod.map id principalEntryToVal) := by
      intro X hX; subst hX; simp [authStateToVal, List.find?_map]
    simp only [caseOptV, Comp.eval_caseOptC_elim, eFind, Expr.eval, stPrin, eval_natEq,
      Env.get_vs, Env.get_vz]
    rw [List.take_of_length_le (by simpa [hst, authStateToVal] using hK.principals_le)]
    rw [hfind _ hst]
    generalize s.gameState.principals.find? (fun x => x.1 == u.val) = F
    rcases F with _ | ⟨i, e⟩
    · simp [Comp.eval, Expr.eval, htp, htpk, hst, hf, doneVal, sigCoreToVal, aNone]
    · simp only [Option.map_some, Option.elim, eval_sampleBytes32, eval_queryPrim,
        PTag.dec_x25519Base, SignalPqxdh.LegacyCosted.PTag.enc, id_map, Comp.eval, Expr.eval, Env.get_vs, Env.get_vz,
        Prod.map, id, principalEntryToVal, signReqC, sampleScalar32]

theorem stepAuthForSigPrim_hol (S : Setup) (n : Nat) (q : AuthQuery S)
    (s : SigReductionState (AuthState S)) (hB : AuthBaseListsBounded n s.gameState) :
    HoldsOnLeaves (SigResInv (R := AuthResponse) (fun s' : SigReductionState (AuthState S) =>
        AuthBaseListsBounded (n + 1) s'.gameState))
      (stepAuthForSigPrim S q s) := by
  have hB1 : AuthBaseListsBounded (n + 1) s.gameState := hB.mono (Nat.le_succ n)
  have gen : ∀ (q : AuthQuery S) (fg : Option (Bytes × Bytes)),
      HoldsOnLeaves (SigResInv (R := AuthResponse) (fun s' : SigReductionState (AuthState S) =>
        AuthBaseListsBounded (n + 1) s'.gameState))
      (do
        let (out, gs') ← (pqxdhAuthSimImplPrim S q).run s.gameState
        return SigStepResultPrim.done out { s with gameState := gs', forgery := fg }) :=
    fun q _ => HoldsOnLeaves.bind (pqxdhAuthSimImplPrim_hol S n q s.gameState hB)
      fun _ hx => HoldsOnLeaves.pure hx
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hB
  unfold stepAuthForSigPrim
  split_ifs with hf
  · exact HoldsOnLeaves.pure hB1
  cases q <;> dsimp only
  case initPrin u =>
    split_ifs
    · exact HoldsOnLeaves.pure hB1
    · refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
        HoldsOnLeaves.pure ?_
      simp only [SigResInv]; hol_leaf
    · exact gen _ s.forgery
  case corruptIK u =>
    split_ifs
    · split
      · exact HoldsOnLeaves.pure hB1
      · refine HoldsOnLeaves.pure ?_
        simp only [SigResInv]; hol_leaf
    · exact gen _ s.forgery
  case genSPK u j =>
    split_ifs
    · exact HoldsOnLeaves.pure hB1
    · split
      · exact HoldsOnLeaves.pure hB1
      · refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.pure ⟨hB1, fun _ _ _ => ?_⟩
        hol_leaf
    · exact gen _ s.forgery
  case sendOPK =>
    exact HoldsOnLeaves.bind_const _ fun fg => gen _ fg
  case sendNoOPK =>
    exact HoldsOnLeaves.bind_const _ fun fg => gen _ fg
  all_goals exact gen _ s.forgery

abbrev sigH (S : Setup) (K : Nat) (q : AuthQuery S) (s : SigReductionState (AuthState S))
    (b : Nat) :=
  (sigHandleDsl S K).eval (.cons (sigStToVal (s, b)) (.cons (authQueryToVal q) .nil))

theorem sigH_eval (S : Setup) (K : Nat) (q : AuthQuery S) (s : SigReductionState (AuthState S))
    (b : Nat) (hB : AuthBaseListsBounded K s.gameState) :
    sigH S K q s b =
      Prod.map authRespToVal id <$> sigLiftStep sigStToVal (stepAuthForSigPrim S q) s b := by
  rcases s with ⟨g, tp, tpk, _ | fg⟩
  · by_cases ht : ∃ u j, q = .genSPK u j ∧ u.val = tp
    · obtain ⟨u, j, rfl, ht⟩ := ht
      simp only [sigH, sigHandleDsl, letV, bindV, caseOptV, caseSumV, v,
        Comp.eval_letC, Comp.eval_liftChal, Comp.eval, Expr.eval,
        Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk, sigStToVal, sigCoreToVal]
      rw [sigStepC_genSpkTarget S K _ ⟨g, tp, tpk, none⟩ _ _ _ _ u j rfl rfl rfl rfl rfl hB ht]
      subst ht
      have hc' : (g.spkBundles.any fun x => x.1 == (u.val, j.val)) =
          (g.spkBundles.any fun x => x.1.1 == u.val && x.1.2 == j.val) := by
        congr 1
      simp only [sigLiftStep, stepAuthForSigPrim, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, beq_self_eq_true, hc']
      by_cases h3 : (g.spkBundles.any fun x => x.1.1 == u.val && x.1.2 == j.val) = true
      · simp only [h3, ↓reduceIte, embedPrim_pure, pure_bind, sigLiftK, map_pure, doneVal,
          sigCoreToVal, Prod.map, id]
        rfl
      simp only [h3, Bool.false_eq_true, ↓reduceIte]
      have hfdE : g.principals.find? (fun (idx, _) => idx == u.val) =
          g.principals.find? (fun x => x.1 == u.val) := rfl
      rw [hfdE]
      rcases hfd : g.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
      · simp only [hfd, Option.elim, embedPrim_pure, pure_bind, sigLiftK, map_pure, doneVal,
          sigCoreToVal, Prod.map, id]
        rfl
      · simp only [hfd, Option.elim, signReqC, embedPrim_bind, embedPrim_pure, bind_assoc,
          pure_bind, sampleScalar32]
        cases b with
        | zero =>
          simp only [sigLiftK, eval_natEq, Expr.eval, Env.get_vs, Env.get_vz,
            beq_self_eq_true, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def, pure_bind,
            bind_assoc, Prod.map, id, aNone]
          rfl
        | succ b' =>
          simp only [sigLiftK, eval_natEq, eufCmaSignOracle, Expr.eval, Env.get_vs, Env.get_vz,
            sampleKemKeyGenPrim, embedPrim_bind, bind_assoc,
            pure_bind, map_eq_bind_pure_comp, Function.comp_def, Prod.map, id]
          have hb0 : (b' + 1 == 0) = false := rfl
          simp only [hb0, Bool.false_eq_true, ↓reduceIte]
          rfl
    have hb : ∀ u j, q = .genSPK u j → u.val ≠ tp := fun u j h1 h2 => ht ⟨u, j, h1, h2⟩
    obtain ⟨α, D, gg, hD⟩ := stepAuth_factor S K ⟨g, tp, tpk, none⟩ q rfl hB hb
    simp only [sigH, sigHandleDsl, letV, bindV, caseOptV, caseSumV, v,
      Comp.eval_letC, Comp.eval_liftChal, Comp.eval, Expr.eval,
      Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk, sigStToVal, sigCoreToVal]
    rw [sigStepC_eval_done S K _ ⟨g, tp, tpk, none⟩ _ _ _ _ q rfl rfl rfl rfl rfl hB hb, hD]
    simp only [sigLiftStep, hD, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def, resDone, doneVal, sigLiftK,
      Prod.map, id, embedPrim_bind, embedPrim_pure]
    rfl
  · simp only [sigH, sigHandleDsl, letV, bindV, caseOptV, caseSumV, v,
      Comp.eval_letC, Comp.eval_liftChal, Comp.eval, Expr.eval,
      Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk, sigStToVal, sigCoreToVal,
      embedPrim_pure, pure_bind]
    simp only [sigLiftStep, stepAuthForSigPrim, Option.isSome_some, ↓reduceIte, embedPrim_pure,
      pure_bind, sigLiftK, map_pure]
    rfl

theorem sigReductionAuthProg_eval_eq_of_bound (S : Setup) (K : Nat) (A : AuthAdversary S)
    (pk : Bytes) (hN : 0 < S.N_id) (rem : Nat)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) rem) (hK : rem ≤ K) :
    (sigReductionAuthProg S K).eval (fun _ => A.run) pk = sigReductionAuthRun S A pk := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  have hstep : ∀ (q : AuthQuery S) (st : SigReductionState (AuthState S)) (b : Nat),
      AuthBaseListsBounded K st.gameState →
      (do
          let x ← (sigReductionAuthProg S K).handle.eval
            (.cons (sigStToVal (st, b)) (.cons ((authCodec S).qenc q) .nil))
          return ((authCodec S).rdec q x.1, x.2) :
          OracleComp (PrimBaseSpec + sigOracleSpec) ((authSpec S).Range q × _)) =
        sigLiftStep sigStToVal (stepAuthForSigPrim S q) st b := by
    intro q st b hB
    show (do let x ← sigH S K q st b; pure (valToAuthResp x.1, x.2)) = _
    rw [sigH_eval S K q st b hB, map_eq_bind_pure_comp]
    dsimp only [eufCmaSignOracle]
    rw [bind_assoc]
    simp only [Function.comp_def, pure_bind, Prod.map, id, hr, Prod.mk.eta, bind_pure]
  have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
  have hinit : (sigReductionAuthProg S K).init.eval (.cons pk .nil) =
      (do
        let k ← embedPrim (spec := eufCmaSignOracle.spec) (embedUnif ($ᵗ (Fin S.N_id)))
        let secb ← embedPrim (spec := eufCmaSignOracle.spec) (embedUnif ($ᵗ Bool))
        pure ((), sigStToVal (⟨AuthState.empty S secb, k.val, pk, none⟩, S.N_spk_tot))) := by
    simp only [sigReductionAuthProg, sigInitDsl, bindV, eval_sampleIndexC, eval_sampleBoolC,
      Comp.eval, Expr.eval, v, emptyAuthStE, stMk, authStateToVal, AuthState.empty, List.map_nil,
      sigStToVal, sigCoreToVal, FgGapDh.sampleIndexRange, hN, dite_true,
      _root_.SignalPqxdh.Security.embedUnif, liftComp_bind, liftComp_pure,
      embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind,
      Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk]
  have hfin : ∀ (st : sigStTy.denote) (a : Bool),
      (sigReductionAuthProg S K).finish.eval (.cons st (.cons a .nil)) =
        pure (st.2.1.getD ([], [])) := by
    intro st a
    have hN0 : (S.N_id == 0) = false := by simp; omega
    rcases st with ⟨b, _ | fg, rest⟩
    · simp [sigReductionAuthProg, sigFinishDsl, Comp.eval, Expr.eval, eval_natEq,
        eCaseOpt, hN0]
    · simp [sigReductionAuthProg, sigFinishDsl, Comp.eval, Expr.eval, eval_natEq,
        eCaseOpt, hN0]
      rfl
  rw [GRed_eval_pqSigIface, hinit]
  simp only [sigReductionAuthRun, hN, dite_true, simulateAuthForSigPrim,
    simulateForSigPrim, bind_assoc, pure_bind]
  refine bind_congr fun k => bind_congr fun secb => ?_
  have hsim := runWithIfaceStep_sig_map_state_bounded sigStToVal
    (fun s : SigReductionState (AuthState S) => s.forgery.getD ([], []))
    (fun st : sigStTy.denote => st.2.1.getD ([], [])) (fun _ _ => rfl)
    (fun n st => AuthBaseListsBounded n st.gameState) (fun h hB => hB.mono h)
    (stepAuthForSigPrim S)
    (fun q st => do
      let x ← (sigReductionAuthProg S K).handle.eval
        (.cons st (.cons ((authCodec S).qenc q) .nil))
      return ((authCodec S).rdec q x.1, x.2)) K hstep
    (fun n q st hB => stepAuthForSigPrim_hol S n q st hB) A.run rem hA 0
    ⟨AuthState.empty S secb, k.val, pk, none⟩ S.N_spk_tot
    (authBaseListsBounded_empty S secb) (by omega)
  have := congrArg (fun m => Prod.snd <$> m) hsim
  simp only [Prod.map, id, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    pure_bind] at this
  refine Eq.trans ?_ this
  refine bind_congr fun x => ?_
  exact hfin x.2 x.1

/-- For `0 < S.N_id`, `sigReductionAuthProg S b.q_total` evaluates to `(sigReductionAuth S b A).run`. -/
theorem sigReductionAuthProg_eval_eq_of_pos (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (pk : Bytes) (hN : 0 < S.N_id) :
    (sigReductionAuthProg S b.q_total).eval (fun _ => A.1.run) pk =
      (sigReductionAuth S b A).run pk := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  exact sigReductionAuthProg_eval_eq_of_bound S b.q_total A.1 pk hN b.q_total hA le_rfl

/-- The `SigEufCma` adversary obtained by running `sigReductionAuthProg S b.q_total` with
    `primQueryBudget S b`. -/
def sigReductionAuthDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : SigEufCmaAdv where
  run pk := (sigReductionAuthProg S b.q_total).eval (fun _ => A.1.run) pk
  q_sig := (sigReductionAuth S b A).q_sig
  q_prim := primQueryBudget S b

/-- `sigReductionAuthDslAdv` and the shallow `sigReductionAuth` have the same `SigEufCma`
    experiment distribution for all `S`. -/
theorem sigReductionAuthProg_evalDist_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[sigEufCmaExp P (sigReductionAuthDslAdv S b A)] =
      𝒟[sigEufCmaExp P (sigReductionAuth S b A)] := by
  by_cases hN : 0 < S.N_id
  · have hrun : sigReductionAuthDslAdv S b A =
        { sigReductionAuth S b A with q_prim := primQueryBudget S b } := by
      have h := fun pk => sigReductionAuthProg_eval_eq_of_pos S b A pk hN
      simp only [sigReductionAuthDslAdv, h]
    rw [hrun]; rfl
  · have hN0 : S.N_id = 0 := by omega
    refine sigEufCmaExp_evalDist_noSig P _ _
      (fun pk => do
        let p ← (sigReductionAuthProg S b.q_total).init.eval (.cons pk .nil)
        (simulateQ (sigReductionAuthProg S b.q_total).impl A.1.run).run p.2) ([], []) ?_ ?_ ?_
    · intro pk
      change (do
        let p ← (sigReductionAuthProg S b.q_total).init.eval (.cons pk .nil)
        let y ← (simulateQ (sigReductionAuthProg S b.q_total).impl A.1.run).run p.2
        (sigReductionAuthProg S b.q_total).finish.eval (.cons y.2 (.cons y.1 .nil))) = _
      rw [bind_assoc]
      refine bind_congr fun ⟨_, st0⟩ => bind_congr fun ⟨aOut, st1⟩ => ?_
      have hN0' : (S.N_id == 0) = true := by simp [hN0]
      simp [sigReductionAuthProg, sigFinishDsl, Comp.eval, Expr.eval, eval_natEq,
        Expr.eval_litBytes, hN0']
    · intro pk
      simp [sigReductionAuth, sigReductionAuthRun, hN]
    · intro pk
      have h := sigReductionAuthProg_chalBounded S b.q_total (fun _ => A.1.run) pk
      have h2 : 2 * S.N_spk_tot = 0 := by simp [Setup.N_spk_tot, hN0]
      rw [h2] at h
      exact h

theorem sigReductionAuthProg_sigEufCma_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    SigEufCma P (sigReductionAuthDslAdv S b A) = SigEufCma P (sigReductionAuth S b A) := by
  unfold SigEufCma; rw [sigReductionAuthProg_evalDist_eq]

private theorem runWithSigBudgetPrim_eq_of_clamped {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (mx : OracleComp (unifSpec + GSpec) α) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) rem)
    (st : St) (b₁ b₂ : Nat) (h1 : min rem b₂ ≤ b₁) (h2 : b₁ ≤ b₂) :
    runWithSigBudgetPrim step mx st b₁ = runWithSigBudgetPrim step mx st b₂ := by
  induction mx using OracleComp.inductionOn generalizing rem st b₁ b₂ with
  | pure a => rfl
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · have hCont : ∀ u, IsQueryBoundP (k u) (fun q : ℕ ⊕ ιI => q.isRight = true) rem :=
        fun u => by simpa using hMx.2 u
      change (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec)
          (Sum.inl (Sum.inl uq))) >>= fun u => runWithSigBudgetPrim step (k u) st b₁) =
        (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec)
          (Sum.inl (Sum.inl uq))) >>= fun u => runWithSigBudgetPrim step (k u) st b₂)
      exact congrArg _ (funext fun u => ih u rem (hCont u) st b₁ b₂ h1 h2)
    · have hPos : 0 < rem := hMx.1.resolve_left (by simp)
      have hCont : ∀ r, IsQueryBoundP (k r) (fun q : ℕ ⊕ ιI => q.isRight = true) (rem - 1) :=
        fun r => by simpa using hMx.2 r
      change (_root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) (step gq st) >>= _) =
        (_root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) (step gq st) >>= _)
      refine congrArg _ (funext fun sr => ?_)
      rcases sr with ⟨res, st'⟩ | ⟨msg1, k1, fb⟩
      · exact ih res (rem - 1) (hCont res) st' b₁ b₂ (by omega) h2
      · rcases b₂ with _ | b₂'
        · have hb1 : b₁ = 0 := by omega
          subst hb1; rfl
        · obtain ⟨b₁', rfl⟩ : ∃ b₁', b₁ = b₁' + 1 := ⟨b₁ - 1, by omega⟩
          dsimp only
          refine congrArg _ (funext fun sig1 => congrArg _ (funext fun pq => ?_))
          rcases k1 pq sig1 with ⟨msg2, k2⟩
          dsimp only
          refine congrArg _ (funext fun sig2 => ?_)
          exact ih (k2 sig2).1 (rem - 1) (hCont (k2 sig2).1) (k2 sig2).2 b₁' b₂'
            (by omega) (by omega)

private theorem sigInit2_potOK (S : Setup) (K : Nat) (pk : (B 32).denote) :
    PotOK isSigChalQ (fun p : (Ty.prod .unit sigStTy).denote => sigPot p.2)
      ((sigInit2Dsl S K).eval (.cons pk .nil)) (2 * S.N_spk_tot) := by
  unfold sigInit2Dsl
  split_ifs with h0
  · refine potC_ret _ _ ?_
    simp [sigPot, Expr.eval]
  · unfold bindV
    refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := 2 * S.N_spk_tot)
      (fun x => ?_) (by simp [Comp.sampleIndexC, Comp.queries, sigWS])
    refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := 2 * S.N_spk_tot)
      (fun y => ?_) (by simp [Comp.sampleBoolC, Comp.queries, sigWS])
    refine potC_ret _ _ ?_
    simp only [sigPot, Expr.eval]
    have := Nat.min_le_right K S.N_spk_tot
    omega

private theorem sigReductionAuthProg2_chalBounded (S : Setup) (K : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool) (pk : Bytes) :
    ((sigReductionAuthProg2 S K).eval A pk).IsQueryBoundP isSigChalQ (2 * S.N_spk_tot) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine PotOK.toQueryBound (B := fun _ => 0) ?_ (fun _ => rfl)
  refine PotOK.bindPot (sigInit2_potOK S K pk) (fun as => ?_)
  refine PotOK.bindPot (B₁ := fun x : Bool × sigStTy.denote => sigPot x.2)
    (potOK_simulateQ_handlerImpl sigPot hUSigChal (sigReductionAuthProg2 S K).handle
      (fun q s => sigHandle_potOK S K s q) (A as.1) as.2)
    (fun bs => ?_)
  dsimp only [sigReductionAuthProg2, sigFinish2Dsl]
  split_ifs <;> exact potC_ret _ _ (Nat.zero_le _)

theorem sigReductionAuthProg2_eval_eq_of_bound (S : Setup) (K : Nat) (A : AuthAdversary S)
    (pk : Bytes) (hN : 0 < S.N_id) (rem : Nat)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) rem) (hK : rem ≤ K) :
    (sigReductionAuthProg2 S K).eval (fun _ => A.run) pk = sigReductionAuthRun S A pk := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  have hstep : ∀ (q : AuthQuery S) (st : SigReductionState (AuthState S)) (b : Nat),
      AuthBaseListsBounded K st.gameState →
      (do
          let x ← (sigReductionAuthProg2 S K).handle.eval
            (.cons (sigStToVal (st, b)) (.cons ((authCodec S).qenc q) .nil))
          return ((authCodec S).rdec q x.1, x.2) :
          OracleComp (PrimBaseSpec + sigOracleSpec) ((authSpec S).Range q × _)) =
        sigLiftStep sigStToVal (stepAuthForSigPrim S q) st b := by
    intro q st b hB
    show (do let x ← sigH S K q st b; pure (valToAuthResp x.1, x.2)) = _
    rw [sigH_eval S K q st b hB, map_eq_bind_pure_comp]
    dsimp only [eufCmaSignOracle]
    rw [bind_assoc]
    simp only [Function.comp_def, pure_bind, Prod.map, id, hr, Prod.mk.eta, bind_pure]
  have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
  have hNne : S.N_id ≠ 0 := Nat.ne_of_gt hN
  have hinit : (sigReductionAuthProg2 S K).init.eval (.cons pk .nil) =
      (do
        let k ← embedPrim (spec := eufCmaSignOracle.spec) (embedUnif ($ᵗ (Fin S.N_id)))
        let secb ← embedPrim (spec := eufCmaSignOracle.spec) (embedUnif ($ᵗ Bool))
        pure ((), sigStToVal (⟨AuthState.empty S secb, k.val, pk, none⟩, min K S.N_spk_tot))) := by
    simp only [sigReductionAuthProg2, sigInit2Dsl, hNne, ↓reduceIte, bindV,
      eval_sampleIndexC, eval_sampleBoolC,
      Comp.eval, Expr.eval, v, emptyAuthStE, stMk, authStateToVal, AuthState.empty, List.map_nil,
      sigStToVal, sigCoreToVal, FgGapDh.sampleIndexRange, hN, dite_true,
      _root_.SignalPqxdh.Security.embedUnif, liftComp_bind, liftComp_pure,
      embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind,
      Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk]
  have hfin : ∀ (st : sigStTy.denote) (a : Bool),
      (sigReductionAuthProg2 S K).finish.eval (.cons st (.cons a .nil)) =
        pure (st.2.1.getD ([], [])) := by
    intro st a
    rcases st with ⟨b, _ | fg, rest⟩
    · simp [sigReductionAuthProg2, sigFinish2Dsl, hNne, Comp.eval, Expr.eval, eCaseOpt]
    · simp [sigReductionAuthProg2, sigFinish2Dsl, hNne, Comp.eval, Expr.eval, eCaseOpt]
      rfl
  rw [GRed_eval_pqSigIface, hinit]
  simp only [sigReductionAuthRun, hN, dite_true, simulateAuthForSigPrim,
    simulateForSigPrim, bind_assoc, pure_bind]
  refine bind_congr fun k => bind_congr fun secb => ?_
  have hsim := runWithIfaceStep_sig_map_state_bounded sigStToVal
    (fun s : SigReductionState (AuthState S) => s.forgery.getD ([], []))
    (fun st : sigStTy.denote => st.2.1.getD ([], [])) (fun _ _ => rfl)
    (fun n st => AuthBaseListsBounded n st.gameState) (fun h hB => hB.mono h)
    (stepAuthForSigPrim S)
    (fun q st => do
      let x ← (sigReductionAuthProg2 S K).handle.eval
        (.cons st (.cons ((authCodec S).qenc q) .nil))
      return ((authCodec S).rdec q x.1, x.2)) K hstep
    (fun n q st hB => stepAuthForSigPrim_hol S n q st hB) A.run rem hA 0
    ⟨AuthState.empty S secb, k.val, pk, none⟩ (min K S.N_spk_tot)
    (authBaseListsBounded_empty S secb) (by omega)
  have hClamp := runWithSigBudgetPrim_eq_of_clamped (stepAuthForSigPrim S) A.run rem hA
    ⟨AuthState.empty S secb, k.val, pk, none⟩ (min K S.N_spk_tot) S.N_spk_tot
    (by omega) (Nat.min_le_right K S.N_spk_tot)
  rw [hClamp] at hsim
  have := congrArg (fun m => Prod.snd <$> m) hsim
  simp only [Prod.map, id, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    pure_bind] at this
  refine Eq.trans ?_ this
  refine bind_congr fun x => ?_
  exact hfin x.2 x.1

theorem sigReductionAuthProg2_eval_eq_of_pos (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (pk : Bytes) (hN : 0 < S.N_id) :
    (sigReductionAuthProg2 S b.q_total).eval (fun _ => A.1.run) pk =
      (sigReductionAuth S b A).run pk := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  exact sigReductionAuthProg2_eval_eq_of_bound S b.q_total A.1 pk hN b.q_total hA le_rfl

/-- Clamped `SigEufCma` adversary running `sigReductionAuthProg2 S b.q_total`. -/
def sigReductionAuthDslAdv2 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : SigEufCmaAdv where
  run pk := (sigReductionAuthProg2 S b.q_total).eval (fun _ => A.1.run) pk
  q_sig := (sigReductionAuth S b A).q_sig
  q_prim := primQueryBudget S b

theorem sigReductionAuthProg2_evalDist_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[sigEufCmaExp P (sigReductionAuthDslAdv2 S b A)] =
      𝒟[sigEufCmaExp P (sigReductionAuth S b A)] := by
  by_cases hN : 0 < S.N_id
  · have hrun : sigReductionAuthDslAdv2 S b A =
        { sigReductionAuth S b A with q_prim := primQueryBudget S b } := by
      have h := fun pk => sigReductionAuthProg2_eval_eq_of_pos S b A pk hN
      simp only [sigReductionAuthDslAdv2, h]
    rw [hrun]; rfl
  · have hN0 : S.N_id = 0 := by omega
    refine sigEufCmaExp_evalDist_noSig P _ _
      (fun pk => do
        let p ← (sigReductionAuthProg2 S b.q_total).init.eval (.cons pk .nil)
        (simulateQ (sigReductionAuthProg2 S b.q_total).impl A.1.run).run p.2) ([], []) ?_ ?_ ?_
    · intro pk
      change (do
        let p ← (sigReductionAuthProg2 S b.q_total).init.eval (.cons pk .nil)
        let y ← (simulateQ (sigReductionAuthProg2 S b.q_total).impl A.1.run).run p.2
        (sigReductionAuthProg2 S b.q_total).finish.eval (.cons y.2 (.cons y.1 .nil))) = _
      rw [bind_assoc]
      refine bind_congr fun ⟨_, st0⟩ => bind_congr fun ⟨aOut, st1⟩ => ?_
      simp [sigReductionAuthProg2, sigFinish2Dsl, hN0, Comp.eval, Expr.eval, Expr.eval_litBytes]
    · intro pk
      simp [sigReductionAuth, sigReductionAuthRun, hN]
    · intro pk
      have h := sigReductionAuthProg2_chalBounded S b.q_total (fun _ => A.1.run) pk
      have h2 : 2 * S.N_spk_tot = 0 := by simp [Setup.N_spk_tot, hN0]
      rw [h2] at h
      exact h

theorem sigReductionAuthProg2_sigEufCma_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    SigEufCma P (sigReductionAuthDslAdv2 S b A) = SigEufCma P (sigReductionAuth S b A) := by
  unfold SigEufCma; rw [sigReductionAuthProg2_evalDist_eq]

end SignalPqxdh.Security.ReductionDsl.AuthHs
