/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# `Ops` Homomorphisms and `simulateQ` Commutation for `ReductionDsl`

Defines semantics- and cost-preserving `OpsHom` maps and commutes `simulateQ` through
`ReductionDsl` monadic loops and `Comp.eval` via `compSubstCalls`.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.ReductionDsl.MapIface

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Env Ops Samplers Iface Expr Comp GameCodec CostedReduction
  iterM findML anyML mapML consumeFirstML foldML handlerImpl)

section OpsHom

variable {S : Sig}

/-- Semantics- and cost-preserving homomorphism between `Ops` tables over the same `Sig`. -/
structure OpsHom (O₁ O₂ : Ops S) where
  mapOp : O₁.Op → O₂.Op
  dom_eq : ∀ o, O₂.dom (mapOp o) = O₁.dom o
  cod_eq : ∀ o, O₂.cod (mapOp o) = O₁.cod o
  eval_eq : ∀ o x, O₂.eval (mapOp o) (cast (congrArg Ty.denote (dom_eq o).symm) x) =
    cast (congrArg Ty.denote (cod_eq o).symm) (O₁.eval o x)
  cost_le : ∀ o, O₂.cost (mapOp o) ≤ O₁.cost o

def OpsHom.inl (O₁ O₂ : Ops S) : OpsHom O₁ (O₁.sum O₂) where
  mapOp := Sum.inl
  dom_eq _ := rfl
  cod_eq _ := rfl
  eval_eq _ _ := rfl
  cost_le _ := Nat.le_refl _

def OpsHom.inr (O₁ O₂ : Ops S) : OpsHom O₂ (O₁.sum O₂) where
  mapOp := Sum.inr
  dom_eq _ := rfl
  cod_eq _ := rfl
  eval_eq _ _ := rfl
  cost_le _ := Nat.le_refl _

def OpsHom.id (O : Ops S) : OpsHom O O where
  mapOp o := o
  dom_eq _ := rfl
  cod_eq _ := rfl
  eval_eq _ _ := rfl
  cost_le _ := Nat.le_refl _

end OpsHom

section SimulateQLoops

variable {κ₁ κ₂ : Type} {spec₁ : OracleSpec.{0, 0} κ₁} {spec₂ : OracleSpec.{0, 0} κ₂}

theorem simulateQ_iterM (qi : QueryImpl spec₁ (OracleComp spec₂)) {α : Type}
    (f : α → OracleComp spec₁ α) (n : ℕ) (a : α) :
    simulateQ qi (iterM f n a) = iterM (fun x => simulateQ qi (f x)) n a := by
  induction n generalizing a with
  | zero => simp [iterM]
  | succ n ih => simp [iterM, simulateQ_bind, ih]

theorem simulateQ_findML (qi : QueryImpl spec₁ (OracleComp spec₂)) {α : Type}
    (p : α → OracleComp spec₁ Bool) (l : List α) :
    simulateQ qi (findML p l) = findML (fun x => simulateQ qi (p x)) l := by
  induction l with
  | nil => simp [findML]
  | cons x xs ih =>
    simp only [findML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [ih]

theorem simulateQ_anyML (qi : QueryImpl spec₁ (OracleComp spec₂)) {α : Type}
    (p : α → OracleComp spec₁ Bool) (l : List α) :
    simulateQ qi (anyML p l) = anyML (fun x => simulateQ qi (p x)) l := by
  induction l with
  | nil => simp [anyML]
  | cons x xs ih =>
    simp only [anyML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [ih]

theorem simulateQ_mapML (qi : QueryImpl spec₁ (OracleComp spec₂)) {α β : Type}
    (f : α → OracleComp spec₁ β) (l : List α) :
    simulateQ qi (mapML f l) = mapML (fun x => simulateQ qi (f x)) l := by
  induction l with
  | nil => simp [mapML]
  | cons x xs ih => simp [mapML, simulateQ_bind, ih]

theorem simulateQ_consumeFirstML (qi : QueryImpl spec₁ (OracleComp spec₂)) {α : Type}
    (p : α → OracleComp spec₁ Bool) (mark : α → α) (l : List α) :
    simulateQ qi (consumeFirstML p mark l) =
      consumeFirstML (fun x => simulateQ qi (p x)) mark l := by
  induction l with
  | nil => simp [consumeFirstML]
  | cons x xs ih =>
    simp only [consumeFirstML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [ih]

theorem simulateQ_foldML (qi : QueryImpl spec₁ (OracleComp spec₂)) {α β : Type}
    (f : α → β → OracleComp spec₁ β) (b : β) (l : List α) :
    simulateQ qi (foldML f b l) = foldML (fun x acc => simulateQ qi (f x acc)) b l := by
  induction l generalizing b with
  | nil => simp [foldML]
  | cons x xs ih => simp [foldML, simulateQ_bind, ih]

end SimulateQLoops

section SimulateQCompEval

variable {S : Sig} {O : Ops S}
  {ι₁ ι₂ : Type} {T₁ : OracleSpec.{0, 0} ι₁} {T₂ : OracleSpec.{0, 0} ι₂}

theorem simulateQ_liftP (I : Iface S T₁) (qi : QueryImpl T₁ (OracleComp T₂))
    (fwdU₂ : QueryImpl unifSpec (OracleComp T₂))
    (hfwd : ∀ n, simulateQ qi (I.fwdU n) = fwdU₂ n)
    {α : Type} (p : ProbComp α) :
    simulateQ qi (I.liftP p) = simulateQ fwdU₂ p := by
  unfold Iface.liftP
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, hfwd n]
    exact bind_congr ih

theorem simulateQ_liftP_eq_self (I : Iface S T₁) (qi : QueryImpl T₁ ProbComp)
    (hfwd : ∀ n, simulateQ qi (I.fwdU n) = liftM (unifSpec.query n))
    {α : Type} (p : ProbComp α) :
    simulateQ qi (I.liftP p) = p := by
  rw [simulateQ_liftP I qi (QueryImpl.ofLift unifSpec ProbComp) hfwd p]
  exact simulateQ_id' p

/-- Translates `Comp O I₁` into `Comp O I₂` by substituting `.sample` and `.query` calls. -/
def compSubstCalls {I₁ : Iface S T₁} {I₂ : Iface S T₂}
    (onSample : ∀ {Γ : List (Ty S)} (s : I₁.smp.Samp),
      Expr O Γ (I₁.smp.sDom s) → Comp O I₂ Γ (I₁.smp.sTy s))
    (onQuery : ∀ {Γ : List (Ty S)} (g : I₁.Tag),
      Expr O Γ (I₁.dom g) → Comp O I₂ Γ (I₁.cod g)) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I₁ Γ t → Comp O I₂ Γ t
  | _, _, .ret e => .ret e
  | _, _, .bind c k => .bind (compSubstCalls onSample onQuery c) (compSubstCalls onSample onQuery k)
  | _, _, .ite b c d =>
    .ite b (compSubstCalls onSample onQuery c) (compSubstCalls onSample onQuery d)
  | _, _, .caseOpt e n s =>
    .caseOpt e (compSubstCalls onSample onQuery n) (compSubstCalls onSample onQuery s)
  | _, _, .caseSum e l r =>
    .caseSum e (compSubstCalls onSample onQuery l) (compSubstCalls onSample onQuery r)
  | _, _, .sample s e => onSample s e
  | _, _, .query g e => onQuery g e
  | _, _, .iter n e body => .iter n e (compSubstCalls onSample onQuery body)
  | _, _, .findM K l p => .findM K l (compSubstCalls onSample onQuery p)
  | _, _, .anyM K l p => .anyM K l (compSubstCalls onSample onQuery p)
  | _, _, .mapM K l f => .mapM K l (compSubstCalls onSample onQuery f)
  | _, _, .consumeFirstM K l p mk =>
    .consumeFirstM K l (compSubstCalls onSample onQuery p) mk
  | _, _, .foldM K l z f => .foldM K l z (compSubstCalls onSample onQuery f)

/-- Commutes `simulateQ qi` through `Comp.eval` via `compSubstCalls`. -/
theorem simulateQ_comp_eval_eq_substCalls {I₁ : Iface S T₁} {I₂ : Iface S T₂}
    (qi : QueryImpl T₁ (OracleComp T₂))
    (onSample : ∀ {Γ : List (Ty S)} (s : I₁.smp.Samp),
      Expr O Γ (I₁.smp.sDom s) → Comp O I₂ Γ (I₁.smp.sTy s))
    (onQuery : ∀ {Γ : List (Ty S)} (g : I₁.Tag),
      Expr O Γ (I₁.dom g) → Comp O I₂ Γ (I₁.cod g))
    (hSample : ∀ {Γ : List (Ty S)} (s : I₁.smp.Samp) (e : Expr O Γ (I₁.smp.sDom s)) (ρ : Env Γ),
      simulateQ qi ((Comp.sample (O := O) (I := I₁) s e).eval ρ) = (onSample s e).eval ρ)
    (hQuery : ∀ {Γ : List (Ty S)} (g : I₁.Tag) (e : Expr O Γ (I₁.dom g)) (ρ : Env Γ),
      simulateQ qi ((Comp.query (O := O) (I := I₁) g e).eval ρ) = (onQuery g e).eval ρ) :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I₁ Γ t) (ρ : Env Γ),
      simulateQ qi (c.eval ρ) = (compSubstCalls onSample onQuery c).eval ρ
  | _, _, .ret _, _ => by simp [compSubstCalls, Comp.eval]
  | _, _, .bind c k, ρ => by
    simp only [compSubstCalls, Comp.eval, simulateQ_bind,
      simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery c ρ]
    exact bind_congr fun x =>
      simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery k (.cons x ρ)
  | _, _, .ite b c d, ρ => by
    simp only [compSubstCalls, Comp.eval]
    cases b.eval ρ <;> simp [simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery]
  | _, _, .caseOpt e n s, ρ => by
    simp only [compSubstCalls, Comp.eval]
    cases e.eval ρ <;> simp [simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery]
  | _, _, .caseSum e l r, ρ => by
    simp only [compSubstCalls, Comp.eval]
    cases e.eval ρ <;> simp [simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery]
  | _, _, .sample s e, ρ => hSample s e ρ
  | _, _, .query g e, ρ => hQuery g e ρ
  | _, _, .iter n e body, ρ => by
    simp only [compSubstCalls, Comp.eval, simulateQ_iterM]
    congr 1; funext a
    exact simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery body (.cons a ρ)
  | _, _, .findM K l p, ρ => by
    simp only [compSubstCalls, Comp.eval, simulateQ_findML]
    congr 1; funext x
    exact simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery p (.cons x ρ)
  | _, _, .anyM K l p, ρ => by
    simp only [compSubstCalls, Comp.eval, simulateQ_anyML]
    congr 1; funext x
    exact simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery p (.cons x ρ)
  | _, _, .mapM K l f, ρ => by
    simp only [compSubstCalls, Comp.eval, simulateQ_mapML]
    congr 1; funext x
    exact simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery f (.cons x ρ)
  | _, _, .consumeFirstM K l p mk, ρ => by
    simp only [compSubstCalls, Comp.eval, simulateQ_consumeFirstML]
    congr 1; funext x
    exact simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery p (.cons x ρ)
  | _, _, .foldM K l z f, ρ => by
    simp only [compSubstCalls, Comp.eval, simulateQ_foldML]
    congr 1; funext x; funext acc
    exact simulateQ_comp_eval_eq_substCalls qi onSample onQuery hSample hQuery f
      (.cons x (.cons acc ρ))

theorem compSubstCalls_cost_le {I₁ : Iface S T₁} {I₂ : Iface S T₂}
    (onSample : ∀ {Γ : List (Ty S)} (s : I₁.smp.Samp),
      Expr O Γ (I₁.smp.sDom s) → Comp O I₂ Γ (I₁.smp.sTy s))
    (onQuery : ∀ {Γ : List (Ty S)} (g : I₁.Tag),
      Expr O Γ (I₁.dom g) → Comp O I₂ Γ (I₁.cod g))
    (hSampleCost : ∀ {Γ : List (Ty S)} (s : I₁.smp.Samp) (e : Expr O Γ (I₁.smp.sDom s)),
      (onSample s e).cost ≤ e.cost + I₁.smp.sCost s)
    (hQueryCost : ∀ {Γ : List (Ty S)} (g : I₁.Tag) (e : Expr O Γ (I₁.dom g)),
      (onQuery g e).cost ≤ e.cost + I₁.qCost g) :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I₁ Γ t),
      (compSubstCalls onSample onQuery c).cost ≤ c.cost
  | _, _, .ret _ => le_rfl
  | _, _, .bind c k => by
    have hc := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost c
    have hk := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost k
    simp only [compSubstCalls, Comp.cost]
    omega
  | _, _, .ite _ c d => by
    have hc := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost c
    have hd := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost d
    simp only [compSubstCalls, Comp.cost]
    omega
  | _, _, .caseOpt _ n s => by
    have hn := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost n
    have hs := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost s
    simp only [compSubstCalls, Comp.cost]
    omega
  | _, _, .caseSum _ l r => by
    have hl := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost l
    have hr := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost r
    simp only [compSubstCalls, Comp.cost]
    omega
  | _, _, .sample s e => hSampleCost s e
  | _, _, .query g e => hQueryCost g e
  | _, _, .iter n _ body => by
    have hb := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost body
    simp only [compSubstCalls, Comp.cost]
    exact Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left n (Nat.add_le_add_right hb 1)) _) 1
  | _, _, .findM K _ p => by
    have hp := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost p
    simp only [compSubstCalls, Comp.cost]
    exact Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left K (Nat.add_le_add_right hp 1)) _) 1
  | _, _, .anyM K _ p => by
    have hp := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost p
    simp only [compSubstCalls, Comp.cost]
    exact Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left K (Nat.add_le_add_right hp 1)) _) 1
  | _, _, .mapM K _ f => by
    have hf := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost f
    simp only [compSubstCalls, Comp.cost]
    exact Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left K (Nat.add_le_add_right hf 1)) _) 1
  | _, _, .consumeFirstM K _ p _ => by
    have hp := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost p
    simp only [compSubstCalls, Comp.cost]
    exact Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left K (by omega)) _) 1
  | _, _, .foldM K _ _ f => by
    have hf := compSubstCalls_cost_le onSample onQuery hSampleCost hQueryCost f
    simp only [compSubstCalls, Comp.cost]
    exact Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left K (Nat.add_le_add_right hf 1)) _) 1

end SimulateQCompEval

end Computational.Proofs.GameHop.ReductionDsl.MapIface
