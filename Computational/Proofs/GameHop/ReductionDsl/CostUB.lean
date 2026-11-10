/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.ReductionDsl.CostAttr
public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# Additive Cost and Query Upper Bounds for `ReductionDsl`

Defines `exprCostUB`, `compCostUB`, and `compQueriesUB` by replacing `max` with `+` in static
`ReductionDsl` cost and query counts, along with `@[dsl_cost]` `simp` lemmas and the `dsl_cost_le`
tactic.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.ReductionDsl.CostUB

open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp GameCodec
  CostedReduction TwoStageCostedReduction bits)

section ExprCostUB

variable {S : Sig} {O : Ops S}

/-- Upper bound on `Expr.cost` replacing every `max` with `+`. -/
def exprCostUB : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ => 1
  | _, _, .unit => 1
  | _, _, .bool _ => 1
  | _, _, .nat n => bits n
  | _, _, .add a b => exprCostUB a + exprCostUB b + 1
  | _, _, .sub a b => exprCostUB a + exprCostUB b + 1
  | _, _, .mulK k a => exprCostUB a + bits k
  | _, _, .divK k a => exprCostUB a + bits k
  | _, _, .modK k a => exprCostUB a + bits k
  | _, _, .lt a b => exprCostUB a + exprCostUB b + 1
  | _, _, .eqN a b => exprCostUB a + exprCostUB b + 1
  | _, _, .not a => exprCostUB a + 1
  | _, _, .and a b => exprCostUB a + exprCostUB b + 1
  | _, _, .ite c a b => exprCostUB c + (exprCostUB a + exprCostUB b) + 1
  | _, _, .pair a b => exprCostUB a + exprCostUB b + 1
  | _, _, .fst a => exprCostUB a + 1
  | _, _, .snd a => exprCostUB a + 1
  | _, _, .inl a => exprCostUB a + 1
  | _, _, .inr a => exprCostUB a + 1
  | _, _, .none => 1
  | _, _, .some a => exprCostUB a + 1
  | _, _, .caseOpt e n s => exprCostUB e + (exprCostUB n + exprCostUB s) + 1
  | _, _, .caseSum e l r => exprCostUB e + (exprCostUB l + exprCostUB r) + 1
  | _, _, .letE e b => exprCostUB e + exprCostUB b + 1
  | _, _, .op o a => exprCostUB a + O.cost o
  | _, _, .nil => 1
  | _, _, .cons x l => exprCostUB x + exprCostUB l + 1
  | _, _, .len l => exprCostUB l + 1
  | _, _, .take n l => exprCostUB n + exprCostUB l + 1
  | _, _, .appendL K a b => exprCostUB a + exprCostUB b + K + 1
  | _, _, .findB K l p => exprCostUB l + K * (exprCostUB p + 1) + 1
  | _, _, .anyB K l p => exprCostUB l + K * (exprCostUB p + 1) + 1
  | _, _, .mapB K l f => exprCostUB l + K * (exprCostUB f + 1) + 1
  | _, _, .foldrB K l z f => exprCostUB l + exprCostUB z + K * (exprCostUB f + 1) + 1
  | _, _, .tconst a => exprCostUB a + 1
  | _, _, .tget m i => exprCostUB m + exprCostUB i + 64
  | _, _, .tset m i a => exprCostUB m + exprCostUB i + exprCostUB a + 128

theorem exprCost_le_costUB : ∀ {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t),
    e.cost ≤ exprCostUB e
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .none | _, _, .nil =>
    Nat.le_refl _
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a | _, _, .op _ a =>
    Nat.add_le_add_right (exprCost_le_costUB a) _
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b | _, _, .and a b
  | _, _, .pair a b | _, _, .letE a b | _, _, .cons a b | _, _, .take a b =>
    Nat.add_le_add_right (Nat.add_le_add (exprCost_le_costUB a) (exprCost_le_costUB b)) 1
  | _, _, .tget a b =>
    Nat.add_le_add_right (Nat.add_le_add (exprCost_le_costUB a) (exprCost_le_costUB b)) 64
  | _, _, .appendL K a b =>
    Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add (exprCost_le_costUB a) (exprCost_le_costUB b)) K) 1
  | _, _, .tset m i a =>
    Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (exprCost_le_costUB m) (exprCost_le_costUB i))
        (exprCost_le_costUB a)) 128
  | _, _, .ite c a b => by
    have hc := exprCost_le_costUB c
    have ha := exprCost_le_costUB a
    have hb := exprCost_le_costUB b
    simp only [Expr.cost, exprCostUB]; omega
  | _, _, .caseOpt e n s => by
    have he := exprCost_le_costUB e
    have hn := exprCost_le_costUB n
    have hs := exprCost_le_costUB s
    simp only [Expr.cost, exprCostUB]; omega
  | _, _, .caseSum e l r => by
    have he := exprCost_le_costUB e
    have hl := exprCost_le_costUB l
    have hr := exprCost_le_costUB r
    simp only [Expr.cost, exprCostUB]; omega
  | _, _, .findB K l p => by
    have hl := exprCost_le_costUB l
    have hp := Nat.mul_le_mul_left K (Nat.add_le_add_right (exprCost_le_costUB p) 1)
    simp only [Expr.cost, exprCostUB]; omega
  | _, _, .anyB K l p => by
    have hl := exprCost_le_costUB l
    have hp := Nat.mul_le_mul_left K (Nat.add_le_add_right (exprCost_le_costUB p) 1)
    simp only [Expr.cost, exprCostUB]; omega
  | _, _, .mapB K l f => by
    have hl := exprCost_le_costUB l
    have hf := Nat.mul_le_mul_left K (Nat.add_le_add_right (exprCost_le_costUB f) 1)
    simp only [Expr.cost, exprCostUB]; omega
  | _, _, .foldrB K l z f => by
    have hl := exprCost_le_costUB l
    have hz := exprCost_le_costUB z
    have hf := Nat.mul_le_mul_left K (Nat.add_le_add_right (exprCost_le_costUB f) 1)
    simp only [Expr.cost, exprCostUB]; omega

@[dsl_cost, simp] theorem exprCostUB_var {Γ t} (v : Var Γ t) :
    exprCostUB (Expr.var (O := O) v) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_v0 {Γ t} :
    exprCostUB (Expr.v0 (O := O) (Γ := Γ) (t := t)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_v1 {Γ t a} :
    exprCostUB (Expr.v1 (O := O) (Γ := Γ) (t := t) (a := a)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_v2 {Γ t a b} :
    exprCostUB (Expr.v2 (O := O) (Γ := Γ) (t := t) (a := a) (b := b)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_v3 {Γ t a b c} :
    exprCostUB (Expr.v3 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_v4 {Γ t a b c d} :
    exprCostUB (Expr.v4 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_v5 {Γ t a b c d e} :
    exprCostUB (Expr.v5 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_v6 {Γ t a b c d e f} :
    exprCostUB (Expr.v6 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)) = 1 := rfl

@[dsl_cost, simp] theorem exprCost_v0 {Γ t} :
    (Expr.v0 (O := O) (Γ := Γ) (t := t)).cost = 1 := rfl
@[dsl_cost, simp] theorem exprCost_v1 {Γ t a} :
    (Expr.v1 (O := O) (Γ := Γ) (t := t) (a := a)).cost = 1 := rfl
@[dsl_cost, simp] theorem exprCost_v2 {Γ t a b} :
    (Expr.v2 (O := O) (Γ := Γ) (t := t) (a := a) (b := b)).cost = 1 := rfl
@[dsl_cost, simp] theorem exprCost_v3 {Γ t a b c} :
    (Expr.v3 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c)).cost = 1 := rfl
@[dsl_cost, simp] theorem exprCost_v4 {Γ t a b c d} :
    (Expr.v4 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)).cost = 1 := rfl
@[dsl_cost, simp] theorem exprCost_v5 {Γ t a b c d e} :
    (Expr.v5 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)).cost = 1 := rfl
@[dsl_cost, simp] theorem exprCost_v6 {Γ t a b c d e f} :
    (Expr.v6 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)).cost = 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_unit {Γ} : exprCostUB (Expr.unit (O := O) (Γ := Γ)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_bool {Γ} (b : Bool) : exprCostUB (Expr.bool (O := O) (Γ := Γ) b) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_nat {Γ} (n : ℕ) : exprCostUB (Expr.nat (O := O) (Γ := Γ) n) = bits n := rfl
@[dsl_cost, simp] theorem exprCostUB_add {Γ} (a b : Expr O Γ .nat) : exprCostUB (.add a b) = exprCostUB a + exprCostUB b + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_sub {Γ} (a b : Expr O Γ .nat) : exprCostUB (.sub a b) = exprCostUB a + exprCostUB b + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_mulK {Γ} (k : ℕ) (a : Expr O Γ .nat) : exprCostUB (.mulK k a) = exprCostUB a + bits k := rfl
@[dsl_cost, simp] theorem exprCostUB_divK {Γ} (k : ℕ) (a : Expr O Γ .nat) : exprCostUB (.divK k a) = exprCostUB a + bits k := rfl
@[dsl_cost, simp] theorem exprCostUB_modK {Γ} (k : ℕ) (a : Expr O Γ .nat) : exprCostUB (.modK k a) = exprCostUB a + bits k := rfl
@[dsl_cost, simp] theorem exprCostUB_lt {Γ} (a b : Expr O Γ .nat) : exprCostUB (.lt a b) = exprCostUB a + exprCostUB b + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_eqN {Γ} (a b : Expr O Γ .nat) : exprCostUB (.eqN a b) = exprCostUB a + exprCostUB b + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_not {Γ} (a : Expr O Γ .bool) : exprCostUB (.not a) = exprCostUB a + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_and {Γ} (a b : Expr O Γ .bool) : exprCostUB (.and a b) = exprCostUB a + exprCostUB b + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_ite {Γ t} (c : Expr O Γ .bool) (a b : Expr O Γ t) :
    exprCostUB (.ite c a b) = exprCostUB c + (exprCostUB a + exprCostUB b) + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_pair {Γ t u} (a : Expr O Γ t) (b : Expr O Γ u) :
    exprCostUB (.pair a b) = exprCostUB a + exprCostUB b + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_fst {Γ t u} (a : Expr O Γ (.prod t u)) : exprCostUB (.fst a) = exprCostUB a + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_snd {Γ t u} (a : Expr O Γ (.prod t u)) : exprCostUB (.snd a) = exprCostUB a + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_inl {Γ t u} (a : Expr O Γ t) : exprCostUB (Expr.inl (u := u) a) = exprCostUB a + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_inr {Γ t u} (a : Expr O Γ u) : exprCostUB (Expr.inr (t := t) a) = exprCostUB a + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_none {Γ t} : exprCostUB (Expr.none (O := O) (Γ := Γ) (t := t)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_some {Γ t} (a : Expr O Γ t) : exprCostUB (.some a) = exprCostUB a + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_caseOpt {Γ t u} (e : Expr O Γ (.opt t)) (n : Expr O Γ u) (s : Expr O (t :: Γ) u) :
    exprCostUB (.caseOpt e n s) = exprCostUB e + (exprCostUB n + exprCostUB s) + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_caseSum {Γ t u v} (e : Expr O Γ (.sum t u)) (l : Expr O (t :: Γ) v) (r : Expr O (u :: Γ) v) :
    exprCostUB (.caseSum e l r) = exprCostUB e + (exprCostUB l + exprCostUB r) + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_letE {Γ t u} (e : Expr O Γ t) (b : Expr O (t :: Γ) u) :
    exprCostUB (.letE e b) = exprCostUB e + exprCostUB b + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_op {Γ} (o : O.Op) (a : Expr O Γ (O.dom o)) :
    exprCostUB (.op o a) = exprCostUB a + O.cost o := rfl
@[dsl_cost, simp] theorem exprCostUB_nil {Γ t} : exprCostUB (Expr.nil (O := O) (Γ := Γ) (t := t)) = 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_cons {Γ t} (x : Expr O Γ t) (l : Expr O Γ (.list t)) :
    exprCostUB (.cons x l) = exprCostUB x + exprCostUB l + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_len {Γ t} (l : Expr O Γ (.list t)) : exprCostUB (.len l) = exprCostUB l + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_take {Γ t} (n : Expr O Γ .nat) (l : Expr O Γ (.list t)) :
    exprCostUB (.take n l) = exprCostUB n + exprCostUB l + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_appendL {Γ t} (K : ℕ) (a b : Expr O Γ (.list t)) :
    exprCostUB (.appendL K a b) = exprCostUB a + exprCostUB b + K + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_findB {Γ t} (K : ℕ) (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) :
    exprCostUB (.findB K l p) = exprCostUB l + K * (exprCostUB p + 1) + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_anyB {Γ t} (K : ℕ) (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) :
    exprCostUB (.anyB K l p) = exprCostUB l + K * (exprCostUB p + 1) + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_mapB {Γ t u} (K : ℕ) (l : Expr O Γ (.list t)) (f : Expr O (t :: Γ) u) :
    exprCostUB (.mapB K l f) = exprCostUB l + K * (exprCostUB f + 1) + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_foldrB {Γ t u} (K : ℕ) (l : Expr O Γ (.list t)) (z : Expr O Γ u) (f : Expr O (t :: u :: Γ) u) :
    exprCostUB (.foldrB K l z f) = exprCostUB l + exprCostUB z + K * (exprCostUB f + 1) + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_tconst {Γ t} (a : Expr O Γ t) : exprCostUB (.tconst a) = exprCostUB a + 1 := rfl
@[dsl_cost, simp] theorem exprCostUB_tget {Γ t} (m : Expr O Γ (.tbl t)) (i : Expr O Γ .nat) :
    exprCostUB (.tget m i) = exprCostUB m + exprCostUB i + 64 := rfl
@[dsl_cost, simp] theorem exprCostUB_tset {Γ t} (m : Expr O Γ (.tbl t)) (i : Expr O Γ .nat) (a : Expr O Γ t) :
    exprCostUB (.tset m i a) = exprCostUB m + exprCostUB i + exprCostUB a + 128 := rfl

@[dsl_cost, simp] theorem bits_zero : bits 0 = 1 := rfl
@[dsl_cost, simp] theorem bits_one : bits 1 = 1 := rfl
@[dsl_cost, simp] theorem bits_two : bits 2 = 2 := rfl
@[dsl_cost, simp] theorem bits_three : bits 3 = 2 := rfl
@[dsl_cost, simp] theorem bits_four : bits 4 = 3 := rfl
@[dsl_cost, simp] theorem bits_eight : bits 8 = 4 := rfl
@[dsl_cost, simp] theorem bits_sixteen : bits 16 = 5 := rfl
@[dsl_cost, simp] theorem bits_thirtyTwo : bits 32 = 6 := rfl
@[dsl_cost, simp] theorem bits_sixtyFour : bits 64 = 7 := rfl

end ExprCostUB

section CompCostUB

open OracleSpec

variable {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}

/-- Upper bound on `Comp.cost` replacing every `max` with `+`. -/
def compCostUB : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprCostUB e + 1
  | _, _, .bind c k => compCostUB c + compCostUB k + 1
  | _, _, .ite b c d => exprCostUB b + (compCostUB c + compCostUB d) + 1
  | _, _, .caseOpt e n s => exprCostUB e + (compCostUB n + compCostUB s) + 1
  | _, _, .caseSum e l r => exprCostUB e + (compCostUB l + compCostUB r) + 1
  | _, _, .sample s e => exprCostUB e + I.smp.sCost s
  | _, _, .query g e => exprCostUB e + I.qCost g
  | _, _, .iter n e body => exprCostUB e + n * (compCostUB body + 1) + 1
  | _, _, .findM K l p => exprCostUB l + K * (compCostUB p + 1) + 1
  | _, _, .anyM K l p => exprCostUB l + K * (compCostUB p + 1) + 1
  | _, _, .mapM K l f => exprCostUB l + K * (compCostUB f + 1) + 1
  | _, _, .consumeFirstM K l p mk => exprCostUB l + K * (compCostUB p + exprCostUB mk + 1) + 1
  | _, _, .foldM K l z f => exprCostUB l + exprCostUB z + K * (compCostUB f + 1) + 1

theorem compCost_le_costUB : ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t),
    c.cost ≤ compCostUB c
  | _, _, .ret e | _, _, .sample _ e | _, _, .query _ e =>
    Nat.add_le_add_right (exprCost_le_costUB e) _
  | _, _, .bind c k =>
    Nat.add_le_add_right (Nat.add_le_add (compCost_le_costUB c) (compCost_le_costUB k)) 1
  | _, _, .ite b c d => by
    have hb := exprCost_le_costUB b
    have hc := compCost_le_costUB c
    have hd := compCost_le_costUB d
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .caseOpt e n s => by
    have he := exprCost_le_costUB e
    have hn := compCost_le_costUB n
    have hs := compCost_le_costUB s
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .caseSum e l r => by
    have he := exprCost_le_costUB e
    have hl := compCost_le_costUB l
    have hr := compCost_le_costUB r
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .iter n e body => by
    have he := exprCost_le_costUB e
    have hb := Nat.mul_le_mul_left n (Nat.add_le_add_right (compCost_le_costUB body) 1)
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .findM K l p => by
    have hl := exprCost_le_costUB l
    have hp := Nat.mul_le_mul_left K (Nat.add_le_add_right (compCost_le_costUB p) 1)
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .anyM K l p => by
    have hl := exprCost_le_costUB l
    have hp := Nat.mul_le_mul_left K (Nat.add_le_add_right (compCost_le_costUB p) 1)
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .mapM K l f => by
    have hl := exprCost_le_costUB l
    have hf := Nat.mul_le_mul_left K (Nat.add_le_add_right (compCost_le_costUB f) 1)
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .consumeFirstM K l p mk => by
    have hl := exprCost_le_costUB l
    have hpm := Nat.mul_le_mul_left K
      (Nat.add_le_add_right (Nat.add_le_add (compCost_le_costUB p) (exprCost_le_costUB mk)) 1)
    simp only [Comp.cost, compCostUB]; omega
  | _, _, .foldM K l z f => by
    have hl := exprCost_le_costUB l
    have hz := exprCost_le_costUB z
    have hf := Nat.mul_le_mul_left K (Nat.add_le_add_right (compCost_le_costUB f) 1)
    simp only [Comp.cost, compCostUB]; omega

@[dsl_cost, simp] theorem compCostUB_ret {Γ t} (e : Expr O Γ t) :
    compCostUB (Comp.ret (I := I) e) = exprCostUB e + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_bind {Γ t u} (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) :
    compCostUB (.bind c k) = compCostUB c + compCostUB k + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_ite {Γ t} (b : Expr O Γ .bool) (c d : Comp O I Γ t) :
    compCostUB (.ite b c d) = exprCostUB b + (compCostUB c + compCostUB d) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_caseOpt {Γ t u} (e : Expr O Γ (.opt t)) (n : Comp O I Γ u) (s : Comp O I (t :: Γ) u) :
    compCostUB (.caseOpt e n s) = exprCostUB e + (compCostUB n + compCostUB s) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_caseSum {Γ t u v} (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v) :
    compCostUB (.caseSum e l r) = exprCostUB e + (compCostUB l + compCostUB r) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_sample {Γ} (s : I.smp.Samp) (e : Expr O Γ (I.smp.sDom s)) :
    compCostUB (Comp.sample (I := I) s e) = exprCostUB e + I.smp.sCost s := rfl
@[dsl_cost, simp] theorem compCostUB_query {Γ} (g : I.Tag) (e : Expr O Γ (I.dom g)) :
    compCostUB (Comp.query (I := I) g e) = exprCostUB e + I.qCost g := rfl
@[dsl_cost, simp] theorem compCostUB_iter {Γ t} (n : ℕ) (e : Expr O Γ t) (body : Comp O I (t :: Γ) t) :
    compCostUB (.iter n e body) = exprCostUB e + n * (compCostUB body + 1) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_findM {Γ t} (K : ℕ) (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) :
    compCostUB (.findM K l p) = exprCostUB l + K * (compCostUB p + 1) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_anyM {Γ t} (K : ℕ) (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) :
    compCostUB (.anyM K l p) = exprCostUB l + K * (compCostUB p + 1) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_mapM {Γ t u} (K : ℕ) (l : Expr O Γ (.list t)) (f : Comp O I (t :: Γ) u) :
    compCostUB (.mapM K l f) = exprCostUB l + K * (compCostUB f + 1) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_consumeFirstM {Γ t} (K : ℕ) (l : Expr O Γ (.list t))
    (p : Comp O I (t :: Γ) .bool) (mk : Expr O (t :: Γ) t) :
    compCostUB (.consumeFirstM K l p mk) = exprCostUB l + K * (compCostUB p + exprCostUB mk + 1) + 1 := rfl
@[dsl_cost, simp] theorem compCostUB_foldM {Γ t u} (K : ℕ) (l : Expr O Γ (.list t)) (z : Expr O Γ u)
    (f : Comp O I (t :: u :: Γ) u) :
    compCostUB (.foldM K l z f) = exprCostUB l + exprCostUB z + K * (compCostUB f + 1) + 1 := rfl

/-- Upper bound on `Comp.queries` replacing every `max` with `+`. -/
def compQueriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret _ => 0
  | _, _, .bind c k => compQueriesUB w ws c + compQueriesUB w ws k
  | _, _, .ite _ c d => compQueriesUB w ws c + compQueriesUB w ws d
  | _, _, .caseOpt _ n s => compQueriesUB w ws n + compQueriesUB w ws s
  | _, _, .caseSum _ l r => compQueriesUB w ws l + compQueriesUB w ws r
  | _, _, .sample s _ => ws s
  | _, _, .query g _ => w g
  | _, _, .iter n _ body => n * compQueriesUB w ws body
  | _, _, .findM K _ p => K * compQueriesUB w ws p
  | _, _, .anyM K _ p => K * compQueriesUB w ws p
  | _, _, .mapM K _ f => K * compQueriesUB w ws f
  | _, _, .consumeFirstM K _ p _ => K * compQueriesUB w ws p
  | _, _, .foldM K _ _ f => K * compQueriesUB w ws f

theorem compQueries_le_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t),
      c.queries w ws ≤ compQueriesUB w ws c
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => Nat.le_refl _
  | _, _, .bind c k =>
    Nat.add_le_add (compQueries_le_queriesUB w ws c) (compQueries_le_queriesUB w ws k)
  | _, _, .ite _ c d => by
    have hc := compQueries_le_queriesUB w ws c
    have hd := compQueries_le_queriesUB w ws d
    simp only [Comp.queries, compQueriesUB]; omega
  | _, _, .caseOpt _ n s => by
    have hn := compQueries_le_queriesUB w ws n
    have hs := compQueries_le_queriesUB w ws s
    simp only [Comp.queries, compQueriesUB]; omega
  | _, _, .caseSum _ l r => by
    have hl := compQueries_le_queriesUB w ws l
    have hr := compQueries_le_queriesUB w ws r
    simp only [Comp.queries, compQueriesUB]; omega
  | _, _, .iter n _ body =>
    Nat.mul_le_mul_left n (compQueries_le_queriesUB w ws body)
  | _, _, .findM K _ p =>
    Nat.mul_le_mul_left K (compQueries_le_queriesUB w ws p)
  | _, _, .anyM K _ p =>
    Nat.mul_le_mul_left K (compQueries_le_queriesUB w ws p)
  | _, _, .mapM K _ f =>
    Nat.mul_le_mul_left K (compQueries_le_queriesUB w ws f)
  | _, _, .consumeFirstM K _ p _ =>
    Nat.mul_le_mul_left K (compQueries_le_queriesUB w ws p)
  | _, _, .foldM K _ _ f =>
    Nat.mul_le_mul_left K (compQueries_le_queriesUB w ws f)

@[dsl_cost, simp] theorem compQueriesUB_ret (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t} (e : Expr O Γ t) :
    compQueriesUB w ws (Comp.ret (I := I) e) = 0 := rfl
@[dsl_cost, simp] theorem compQueriesUB_bind (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t u}
    (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) :
    compQueriesUB w ws (.bind c k) = compQueriesUB w ws c + compQueriesUB w ws k := rfl
@[dsl_cost, simp] theorem compQueriesUB_ite (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t}
    (b : Expr O Γ .bool) (c d : Comp O I Γ t) :
    compQueriesUB w ws (.ite b c d) = compQueriesUB w ws c + compQueriesUB w ws d := rfl
@[dsl_cost, simp] theorem compQueriesUB_caseOpt (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t u}
    (e : Expr O Γ (.opt t)) (n : Comp O I Γ u) (s : Comp O I (t :: Γ) u) :
    compQueriesUB w ws (.caseOpt e n s) = compQueriesUB w ws n + compQueriesUB w ws s := rfl
@[dsl_cost, simp] theorem compQueriesUB_caseSum (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t u v}
    (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v) :
    compQueriesUB w ws (.caseSum e l r) = compQueriesUB w ws l + compQueriesUB w ws r := rfl
@[dsl_cost, simp] theorem compQueriesUB_sample (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ}
    (s : I.smp.Samp) (e : Expr O Γ (I.smp.sDom s)) :
    compQueriesUB w ws (Comp.sample (I := I) s e) = ws s := rfl
@[dsl_cost, simp] theorem compQueriesUB_query (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ}
    (g : I.Tag) (e : Expr O Γ (I.dom g)) :
    compQueriesUB w ws (Comp.query (I := I) g e) = w g := rfl
@[dsl_cost, simp] theorem compQueriesUB_iter (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t}
    (n : ℕ) (e : Expr O Γ t) (body : Comp O I (t :: Γ) t) :
    compQueriesUB w ws (.iter n e body) = n * compQueriesUB w ws body := rfl
@[dsl_cost, simp] theorem compQueriesUB_findM (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t}
    (K : ℕ) (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) :
    compQueriesUB w ws (.findM K l p) = K * compQueriesUB w ws p := rfl
@[dsl_cost, simp] theorem compQueriesUB_anyM (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t}
    (K : ℕ) (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) :
    compQueriesUB w ws (.anyM K l p) = K * compQueriesUB w ws p := rfl
@[dsl_cost, simp] theorem compQueriesUB_mapM (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t u}
    (K : ℕ) (l : Expr O Γ (.list t)) (f : Comp O I (t :: Γ) u) :
    compQueriesUB w ws (.mapM K l f) = K * compQueriesUB w ws f := rfl
@[dsl_cost, simp] theorem compQueriesUB_consumeFirstM (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t}
    (K : ℕ) (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (mk : Expr O (t :: Γ) t) :
    compQueriesUB w ws (.consumeFirstM K l p mk) = K * compQueriesUB w ws p := rfl
@[dsl_cost, simp] theorem compQueriesUB_foldM (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ t u}
    (K : ℕ) (l : Expr O Γ (.list t)) (z : Expr O Γ u) (f : Comp O I (t :: u :: Γ) u) :
    compQueriesUB w ws (.foldM K l z f) = K * compQueriesUB w ws f := rfl

theorem totalCost_le_of_costUB {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    {bInit bHandle bFin : ℕ}
    (hInit : compCostUB R.init ≤ bInit)
    (hHandle : compCostUB R.handle ≤ bHandle)
    (hFin : compCostUB R.finish ≤ bFin) (q : ℕ) :
    R.totalCost q ≤ bInit + q * (I.uCost + bHandle + C.codecCost) + bFin := by
  unfold CostedReduction.totalCost
  have hi := (compCost_le_costUB R.init).trans hInit
  have hh := (compCost_le_costUB R.handle).trans hHandle
  have hf := (compCost_le_costUB R.finish).trans hFin
  have hmul : q * max I.uCost (R.handle.cost + C.codecCost) ≤
      q * (I.uCost + bHandle + C.codecCost) :=
    Nat.mul_le_mul_left q (by omega)
  omega

theorem totalQueries_le_of_queriesUB {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {bInit bHandle bFin : ℕ}
    (hInit : compQueriesUB w ws R.init ≤ bInit)
    (hHandle : compQueriesUB w ws R.handle ≤ bHandle)
    (hFin : compQueriesUB w ws R.finish ≤ bFin) (q : ℕ) :
    R.totalQueries w ws q ≤ bInit + q * bHandle + bFin := by
  unfold CostedReduction.totalQueries
  have hi := (compQueries_le_queriesUB w ws R.init).trans hInit
  have hh := (compQueries_le_queriesUB w ws R.handle).trans hHandle
  have hf := (compQueries_le_queriesUB w ws R.finish).trans hFin
  have hmul := Nat.mul_le_mul_left q hh
  omega

theorem twoStageTotalCost_le_of_costUB {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {bInit bPre bPost bDone bRes bFin : ℕ}
    (hInit : compCostUB R.init ≤ bInit)
    (hPre : compCostUB R.handlePre ≤ bPre)
    (hPost : compCostUB R.handlePost ≤ bPost)
    (hDone : compCostUB R.chDone ≤ bDone)
    (hRes : compCostUB R.resume ≤ bRes)
    (hFin : compCostUB R.finish ≤ bFin) (q : ℕ) :
    R.totalCost q ≤
      bInit + q * (I.uCost + bPre + bPost + C.codecCost) + (bDone + bRes) + bFin := by
  unfold TwoStageCostedReduction.totalCost
  have hi := (compCost_le_costUB R.init).trans hInit
  have hpre := (compCost_le_costUB R.handlePre).trans hPre
  have hpost := (compCost_le_costUB R.handlePost).trans hPost
  have hdone := (compCost_le_costUB R.chDone).trans hDone
  have hres := (compCost_le_costUB R.resume).trans hRes
  have hf := (compCost_le_costUB R.finish).trans hFin
  have hmul : q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) ≤
      q * (I.uCost + bPre + bPost + C.codecCost) :=
    Nat.mul_le_mul_left q (by omega)
  omega

theorem twoStageTotalQueries_le_of_queriesUB {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {bInit bPre bPost bDone bRes bFin : ℕ}
    (hInit : compQueriesUB w ws R.init ≤ bInit)
    (hPre : compQueriesUB w ws R.handlePre ≤ bPre)
    (hPost : compQueriesUB w ws R.handlePost ≤ bPost)
    (hDone : compQueriesUB w ws R.chDone ≤ bDone)
    (hRes : compQueriesUB w ws R.resume ≤ bRes)
    (hFin : compQueriesUB w ws R.finish ≤ bFin) (q : ℕ) :
    R.totalQueries w ws q ≤ bInit + q * (bPre + bPost) + (bDone + bRes) + bFin := by
  unfold TwoStageCostedReduction.totalQueries
  have hi := (compQueries_le_queriesUB w ws R.init).trans hInit
  have hpre := (compQueries_le_queriesUB w ws R.handlePre).trans hPre
  have hpost := (compQueries_le_queriesUB w ws R.handlePost).trans hPost
  have hdone := (compQueries_le_queriesUB w ws R.chDone).trans hDone
  have hres := (compQueries_le_queriesUB w ws R.resume).trans hRes
  have hf := (compQueries_le_queriesUB w ws R.finish).trans hFin
  have hmul : q * max (R.handlePre.queries w ws) (R.handlePost.queries w ws) ≤
      q * (bPre + bPost) :=
    Nat.mul_le_mul_left q (by omega)
  omega

end CompCostUB

/-- Discharges static `ReductionDsl` cost and query upper-bound goals via `*CostUB`, `dsl_cost`,
and `omega`. -/
macro "dsl_cost_le" : tactic =>
  `(tactic| (
      try (first
        | refine Nat.le_trans (exprCost_le_costUB _) ?_
        | refine Nat.le_trans (compCost_le_costUB _) ?_
        | refine Nat.le_trans (compQueries_le_queriesUB _ _ _) ?_);
      simp only [dsl_cost, Nat.reduceAdd, Nat.reduceMul];
      omega))

end Computational.Proofs.GameHop.ReductionDsl.CostUB
