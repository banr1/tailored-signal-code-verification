/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCk
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost

/-!
# One-Key `PrfChainKey` `ReductionDsl` Program

Defines `prfCkRedProg1Key`, obtained from `prfCkRedProg` by replacing `.initPrin` with
`initPrin1KeyFixedB`, and proves semantic equivalence with `prfCkReductionAuthFixed1Key` along with
static cost and query-count bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open RoKem
open FgGapDh
open OracleSpec OracleComp

section PrfCk1KeyBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

def authCkStep1KeyC (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  caseSumV (v q) (fun u => initPrin1KeyFixedB K fhst u) fun q =>
  caseSumV (v q) (fun u => corruptFixedB K fhst u) fun q =>
  caseSumV (v q) (fun x => genSpkFixedB K fhst x) fun q =>
  caseSumV (v q) (fun x => genOpkFixedB K fhst x) fun q =>
  caseSumV (v q) (fun x => authCkSendB S K true idx chalP fhst x) fun q =>
  caseSumV (v q) (fun x => authCkSendB S K false idx chalP fhst x) fun q =>
  caseSumV (v q) (fun x => authCkRecvB S K true idx chalP fhst x) fun q =>
  caseSumV (v q) (fun x => authCkRecvB S K false idx chalP fhst x) fun q =>
  caseSumV (v q) (fun sec => roFixedB K fhst sec) fun q =>
  caseSumV (v q) (fun x => roRootFixedB K fhst x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v fhst))) fun sk =>
  registerFixedB fhst sk

end PrfCk1KeyBranches

def prfCkHandle1KeyDsl (S : Setup) (K : Nat) :
    Comp pqxdhOps pqPrimIface [prfCkStTy, authQueryTy] (.prod authRespTy prfCkStTy) :=
  letV (.var .zero : Expr pqxdhOps [prfCkStTy, authQueryTy] prfCkStTy) fun s =>
  letV (ckSecb (v s)) fun secb =>
  letV (ckIdx (v s)) fun idx =>
  letV (ckChal (v s)) fun chalP =>
  letV (ckFhst (v s)) fun fhst =>
  bindV (authCkStep1KeyC S K idx chalP fhst
    (.succ .zero : Var [prfCkStTy, authQueryTy] authQueryTy)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (v secb) (.pair (v idx) (.pair (v chalP) (.snd (v r))))))

/-- `ReductionDsl` program for `prfCkReductionAuthFixed1Key S b` at list bound `K`. -/
def prfCkRedProg1Key (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqPrimIface (authSpec S) (authCodec S)
      (.prod (B 32) (B 32)) .unit .bool .bool where
  σ      := prfCkStTy
  init   := prfCkInitDslK S K
  handle := prfCkHandle1KeyDsl S K
  finish := prfCkFinishDsl S K

section PrfCk1KeyEval

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

theorem authCkStep1KeyC_eval_inr
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (y : _) (hq : Env.get env (h₄.wk q) = Sum.inr y) :
    (authCkStep1KeyC S K idx chalP fhst q).eval env =
      (authCkStepC S K idx chalP fhst q).eval env := by
  simp only [authCkStep1KeyC, authCkStepC, caseSumV, v, Comp.eval, Expr.eval, hq]

theorem authCkStep1KeyC_eval
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S) (qv : AuthQuery S)
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hq : Env.get env (h₄.wk q) = authQueryToVal qv)
    (hB : AuthListsBounded K s) :
    (authCkStep1KeyC S K idx chalP fhst q).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.authCkStepWithPrim1Key S (AuthSubHops1to3.sampAtCkPrim idxv pv) qv s := by
  by_cases hI : AuthQuery.NotInitPrin qv
  · obtain ⟨y, hy⟩ : ∃ y, authQueryToVal qv = Sum.inr y := by
      cases qv with
      | initPrin u => exact absurd rfl (hI u)
      | _ => exact ⟨_, rfl⟩
    rw [authCkStep1KeyC_eval_inr S K idx chalP fhst q env y (hq.trans hy),
      authCkStepC_eval S K idx chalP fhst q env idxv pv s qv hidx hchal hfhst hq hB,
      authCkStepWithPrim1Key_eq_of_ne _ qv hI s]
  · obtain ⟨u, rfl⟩ : ∃ u, qv = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    unfold authCkStep1KeyC AuthSubHops1to3.authCkStepWithPrim1Key
    simp only [caseSumV, v, Comp.eval, Expr.eval, hq, authQueryToVal, authQenc]
    exact initPrin1KeyFixedB_eval S K fhst .zero _ s u
      (by simp [Ext.step_wk, hfhst]) rfl hB

theorem prfCkHandle1KeyDsl_eval (secb : Bool) (idx : Nat) (p : Bytes × Bytes)
    (s : AuthHybridStateFixed S) (q : AuthQuery S) (hB : AuthListsBounded K s) :
    (prfCkHandle1KeyDsl S K).eval
      (.cons (prfCkStateToVal secb idx p s) (.cons (authQueryToVal q) .nil)) =
      Prod.map authRespToVal (prfCkStateToVal secb idx p) <$>
        AuthSubHops1to3.authCkStepWithPrim1Key S (AuthSubHops1to3.sampAtCkPrim idx p) q s := by
  unfold prfCkHandle1KeyDsl
  repeat' (rw [letV_eval]; simp only [ckSecb, ckIdx, ckChal, ckFhst, v,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, prfCkStateToVal])
  rw [bindV_eval]
  rw [authCkStep1KeyC_eval S K _ _ _ _ _ idx p s q rfl rfl rfl rfl hB]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
  apply bind_congr; intro ⟨resp, s'⟩
  rfl

theorem authCkStepWithPrim1Key_bounded {n : Nat}
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hB : AuthListsBounded n hst) :
    HoldsOnLeaves (fun x => AuthListsBounded (n + 1) x.2)
      (AuthSubHops1to3.authCkStepWithPrim1Key S sampAt q hst) := by
  by_cases hI : AuthQuery.NotInitPrin q
  · rw [authCkStepWithPrim1Key_eq_of_ne sampAt q hI hst]
    exact authCkStepWithPrim_bounded sampAt q hst hB
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    exact (stepAuthOtherPrim1Key_bounded (.initPrin u) hst hB).toHoldsOnLeaves

theorem prfCkRedProg1Key_eval_eq_of_bound
    (A : AuthAdversary S) (mkSeedChal ck1_1Chal : Bytes)
    (rem : Nat) (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) rem)
    (hK : rem ≤ K) :
    (prfCkRedProg1Key S K).eval (fun _ => A.run) (mkSeedChal, ck1_1Chal) =
    ( do
        let idx ← embedUnif (RoKem.sampleIndexRange (min K S.N_sess_tot))
        AuthSubHops1to3.authCkPreSampleRunPrim1Key S idx (mkSeedChal, ck1_1Chal) A ) := by
  have hInit :
      (prfCkInitDslK S K).eval (.cons (mkSeedChal, ck1_1Chal) .nil) =
      ( do
          let idx ← embedUnif (RoKem.sampleIndexRange (min K S.N_sess_tot))
          let secb ← embedUnif ($ᵗ Bool)
          pure ((), prfCkStateToVal secb idx (mkSeedChal, ck1_1Chal)
            (AuthHybridStateFixed.empty S secb)) ) := by
    simp only [prfCkInitDslK, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, samplePrim_index_eval, samplePrim_bool_eval]
    rfl
  unfold CostedReduction.eval CostedReduction.impl prfCkRedProg1Key
    AuthSubHops1to3.authCkPreSampleRunPrim1Key
  dsimp only [id_eq]
  rw [hInit]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro idx
  apply bind_congr; intro secb
  let p := (mkSeedChal, ck1_1Chal)
  have hSim := simulateQ_prim_map_state_bounded
    (prfCkStateToVal secb idx p)
    AuthListsBounded
    (fun h hB => hB.mono h)
    (AuthSubHops1to3.authCkStepWithPrim1Key S (AuthSubHops1to3.sampAtCkPrim idx p))
    (prfCkHandle1KeyDsl S K)
    K
    (fun q s hB => prfCkHandle1KeyDsl_eval S K secb idx p s q hB)
    (fun n q s hB => authCkStepWithPrim1Key_bounded S (AuthSubHops1to3.sampAtCkPrim idx p) q s hB)
    A.run rem hA 0 (AuthHybridStateFixed.empty S secb)
    (authListsBounded_empty S secb) (by omega)
  rw [hSim.2, bind_map_left]
  refine hSim.1.bind_congr _ _ (fun ⟨b', finalSt⟩ hFinB => ?_)
  have hFinK : AuthListsBounded K finalSt := hFinB.mono (by omega)
  simp only [prfCkFinishDsl, letV_eval, ckSecb, ckFhst, ahsfHybrid, Expr.eval,
    Env.get_succ, Env.get_zero, prfCkStateToVal, authHybridStateFixedToVal,
    Prod.map, id_eq]
  exact finalizeAuthFixedDsl_eval S K secb b' finalSt.toAuthHybridState _
    hFinK.toAuthHybridListsBounded

/-- Evaluating `prfCkRedProg1Key S b.q_total` against a bounded adversary equals
    `(prfCkReductionAuthFixed1Key S b A).dist`. -/
theorem prfCkRedProg1Key_eval_eq (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (mkSeedChal ck1_1Chal : Bytes) :
    (prfCkRedProg1Key S b.q_total).eval (fun _ => A.1.run) (mkSeedChal, ck1_1Chal) =
    (prfCkReductionAuthFixed1Key S b A).dist mkSeedChal ck1_1Chal := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  exact prfCkRedProg1Key_eval_eq_of_bound S b.q_total A.1 mkSeedChal ck1_1Chal b.q_total hA le_rfl

end PrfCk1KeyEval

/-- `PrfChainKey` adversary obtained by running `prfCkRedProg1Key S b.q_total`. -/
def prfCkReductionAuthFixed1KeyDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfCkAdv where
  dist mkSeedChal ck1_1Chal :=
    (prfCkRedProg1Key S b.q_total).eval (fun _ => A.1.run) (mkSeedChal, ck1_1Chal)
  q_prf  := (prfCkReductionAuthFixed1Key S b A).q_prf
  q_prim := (prfCkReductionAuthFixed1Key S b A).q_prim

theorem prfCkReductionAuthFixed1KeyDslAdv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    prfCkReductionAuthFixed1KeyDslAdv S b A = prfCkReductionAuthFixed1Key S b A := by
  unfold prfCkReductionAuthFixed1KeyDslAdv
  congr 1
  funext mkSeedChal ck1_1Chal
  exact prfCkRedProg1Key_eval_eq S b A mkSeedChal ck1_1Chal

/-- `prfCkReductionAuthFixed1KeyDslAdv` and `prfCkReductionAuthFixed1Key` have equal `PrfChainKey`
    advantage. -/
theorem prfCkRedProg1Key_prfCk_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfChainKey P (prfCkReductionAuthFixed1KeyDslAdv S b A) =
      PrfChainKey P (prfCkReductionAuthFixed1Key S b A) := by
  rw [prfCkReductionAuthFixed1KeyDslAdv_eq]

section PrfCk1KeyCost

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

theorem authCkStep1KeyC_cost_le (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkStep1KeyC (Δ := Δ) S K idx chalP fhst q).cost ≤
      (authCkStepC (Δ := Δ) S K idx chalP fhst q).cost := by
  simp only [authCkStep1KeyC, authCkStepC, caseSumV, Comp.cost]
  gcongr
  exact initPrin1KeyFixedB_cost_le K fhst _

theorem authCkStep1KeyC_queries_le (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (authCkStep1KeyC (Δ := Δ) S K idx chalP fhst q).queries w ws ≤
      (authCkStepC (Δ := Δ) S K idx chalP fhst q).queries w ws := by
  simp only [authCkStep1KeyC, authCkStepC, caseSumV, Comp.queries]
  gcongr
  exact initPrin1KeyFixedB_queries_le K fhst _ w ws

theorem prfCkHandle1KeyDsl_cost_le :
    (prfCkHandle1KeyDsl S K).cost ≤ (prfCkHandleDsl S K).cost := by
  simp only [prfCkHandle1KeyDsl, prfCkHandleDsl, letV, bindV, Comp.letC, Comp.cost]
  gcongr
  exact authCkStep1KeyC_cost_le S K _ _ _ _

theorem prfCkHandle1KeyDsl_queries_le (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (prfCkHandle1KeyDsl S K).queries w ws ≤ (prfCkHandleDsl S K).queries w ws := by
  simp only [prfCkHandle1KeyDsl, prfCkHandleDsl, letV, bindV, Comp.letC, Comp.queries]
  gcongr
  exact authCkStep1KeyC_queries_le S K _ _ _ _ w ws

theorem prfCkRedProg1Key_totalCost_le (q : Nat) :
    (prfCkRedProg1Key S K).totalCost q ≤ (prfCkRedProg S K).totalCost q := by
  have h := prfCkHandle1KeyDsl_cost_le S K
  simp only [CostedReduction.totalCost, prfCkRedProg1Key, prfCkRedProg]
  gcongr
  exact h

theorem prfCkRedProg1Key_totalQueries_le (w : pqPrimIface.Tag → ℕ)
    (ws : pqPrimIface.smp.Samp → ℕ) (q : Nat) :
    (prfCkRedProg1Key S K).totalQueries w ws q ≤ (prfCkRedProg S K).totalQueries w ws q := by
  have h := prfCkHandle1KeyDsl_queries_le S K w ws
  simp only [CostedReduction.totalQueries, prfCkRedProg1Key, prfCkRedProg]
  gcongr
  exact h

end PrfCk1KeyCost

end SignalPqxdh.Security.ReductionDsl.AuthPrf
