/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.ReductionDsl.CostUB

/-!
# Additive Cost and Query Upper Bounds

Compatibility aliases forwarding `Expr.costUB`, `Comp.costUB`, and `Comp.queriesUB` from
`Computational.Proofs.GameHop.ReductionDsl.CostUB`.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open Computational.Proofs.GameHop.ReductionDsl

variable {S : Sig} {O : Ops S}

namespace Expr

/-- Upper bound on `Expr.cost` replacing every `max` with `+`. -/
def costUB : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ => 1
  | _, _, .unit => 1
  | _, _, .bool _ => 1
  | _, _, .nat n => bits n
  | _, _, .add a b => a.costUB + b.costUB + 1
  | _, _, .sub a b => a.costUB + b.costUB + 1
  | _, _, .mulK k a => a.costUB + bits k
  | _, _, .divK k a => a.costUB + bits k
  | _, _, .modK k a => a.costUB + bits k
  | _, _, .lt a b => a.costUB + b.costUB + 1
  | _, _, .eqN a b => a.costUB + b.costUB + 1
  | _, _, .not a => a.costUB + 1
  | _, _, .and a b => a.costUB + b.costUB + 1
  | _, _, .ite c a b => c.costUB + (a.costUB + b.costUB) + 1
  | _, _, .pair a b => a.costUB + b.costUB + 1
  | _, _, .fst a => a.costUB + 1
  | _, _, .snd a => a.costUB + 1
  | _, _, .inl a => a.costUB + 1
  | _, _, .inr a => a.costUB + 1
  | _, _, .none => 1
  | _, _, .some a => a.costUB + 1
  | _, _, .caseOpt e n s => e.costUB + (n.costUB + s.costUB) + 1
  | _, _, .caseSum e l r => e.costUB + (l.costUB + r.costUB) + 1
  | _, _, .letE e b => e.costUB + b.costUB + 1
  | _, _, .op o a => a.costUB + O.cost o
  | _, _, .nil => 1
  | _, _, .cons x l => x.costUB + l.costUB + 1
  | _, _, .len l => l.costUB + 1
  | _, _, .take n l => n.costUB + l.costUB + 1
  | _, _, .appendL K a b => a.costUB + b.costUB + K + 1
  | _, _, .findB K l p => l.costUB + K * (p.costUB + 1) + 1
  | _, _, .anyB K l p => l.costUB + K * (p.costUB + 1) + 1
  | _, _, .mapB K l f => l.costUB + K * (f.costUB + 1) + 1
  | _, _, .foldrB K l z f => l.costUB + z.costUB + K * (f.costUB + 1) + 1
  | _, _, .tconst a => a.costUB + 1
  | _, _, .tget m i => m.costUB + i.costUB + 64
  | _, _, .tset m i a => m.costUB + i.costUB + a.costUB + 128

theorem costUB_eq_exprCostUB {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    e.costUB = CostUB.exprCostUB e := by
  induction e <;> simp_all [costUB, CostUB.exprCostUB]

end Expr

namespace Comp

open OracleSpec

variable {ι : Type} {T : OracleSpec ι} {I : Iface S T}

/-- Upper bound on `Comp.cost` replacing every `max` with `+`. -/
def costUB : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => e.costUB + 1
  | _, _, .bind c k => c.costUB + k.costUB + 1
  | _, _, .ite b c d => b.costUB + (c.costUB + d.costUB) + 1
  | _, _, .caseOpt e n s => e.costUB + (n.costUB + s.costUB) + 1
  | _, _, .caseSum e l r => e.costUB + (l.costUB + r.costUB) + 1
  | _, _, .sample s e => e.costUB + I.smp.sCost s
  | _, _, .query g e => e.costUB + I.qCost g
  | _, _, .iter n e body => e.costUB + n * (body.costUB + 1) + 1
  | _, _, .findM K l p => l.costUB + K * (p.costUB + 1) + 1
  | _, _, .anyM K l p => l.costUB + K * (p.costUB + 1) + 1
  | _, _, .mapM K l f => l.costUB + K * (f.costUB + 1) + 1
  | _, _, .consumeFirstM K l p mk => l.costUB + K * (p.costUB + mk.costUB + 1) + 1
  | _, _, .foldM K l z f => l.costUB + z.costUB + K * (f.costUB + 1) + 1

theorem costUB_eq_compCostUB {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    c.costUB = CostUB.compCostUB c := by
  induction c <;> simp_all [costUB, CostUB.compCostUB, Expr.costUB_eq_exprCostUB]

theorem cost_le_costUB {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : c.cost ≤ c.costUB := by
  rw [costUB_eq_compCostUB]; exact CostUB.compCost_le_costUB c

/-- Upper bound on `Comp.queries` replacing every `max` with `+`. -/
def queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret _ => 0
  | _, _, .bind c k => c.queriesUB w ws + k.queriesUB w ws
  | _, _, .ite _ c d => c.queriesUB w ws + d.queriesUB w ws
  | _, _, .caseOpt _ n s => n.queriesUB w ws + s.queriesUB w ws
  | _, _, .caseSum _ l r => l.queriesUB w ws + r.queriesUB w ws
  | _, _, .sample s _ => ws s
  | _, _, .query g _ => w g
  | _, _, .iter n _ body => n * body.queriesUB w ws
  | _, _, .findM K _ p => K * p.queriesUB w ws
  | _, _, .anyM K _ p => K * p.queriesUB w ws
  | _, _, .mapM K _ f => K * f.queriesUB w ws
  | _, _, .consumeFirstM K _ p _ => K * p.queriesUB w ws
  | _, _, .foldM K _ _ f => K * f.queriesUB w ws

theorem queriesUB_eq_compQueriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ : List (Ty S)}
    {t : Ty S} (c : Comp O I Γ t) : c.queriesUB w ws = CostUB.compQueriesUB w ws c := by
  induction c <;> simp_all [queriesUB, CostUB.compQueriesUB]

theorem queries_le_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ : List (Ty S)} {t : Ty S}
    (c : Comp O I Γ t) : c.queries w ws ≤ c.queriesUB w ws := by
  rw [queriesUB_eq_compQueriesUB]; exact CostUB.compQueries_le_queriesUB w ws c

end Comp

end ReductionDsl
