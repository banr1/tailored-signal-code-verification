/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Nat.Log
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.ProbComp.Basic

/-!
# ReductionDsl: a costed deep embedding for game reductions

**Trusted in part.** Every definition in this file except the variable shorthands `Expr.v0` to
`Expr.v6` is part of the trusted base (`Computational/docs/TRUSTED_BASE.md`): a reduction named by
a headline statement is a `CostedReduction` or `TwoStageCostedReduction` value whose efficiency
claims use `totalCost`, `totalQueries`, `size`, and the per-query-kind cost definitions
(`Expr.costAt`, `Comp.pureEval?`, `Comp.costAt`, `ValidKindCosts`, `totalCostByKind`,
`CostBoundedByKind`). The auxiliary size, table-cost, and dual-fuel definitions (`Ty.BaseFits`,
`OpsBaseBounded`, `SampBaseBounded`, `Ty.listDepth`, `Ty.NoNestedLists`, `Ty.HasNoTbl`,
`Ty.treeBlocks`, `Expr.costWithTbl`, `Comp.costWithTbl`, `GameCodec.FitsOn`, `GameCodec.BaseFitsOn`,
`CostedReduction.totalCostBounded`, `TwoStageCostedReduction.run1Bounded`, `runFuelBounded`,
`TwoStageCostedReduction.eval1Bounded`, `TwoStageCostedReduction.eval2Bounded`,
`TwoStageCostedReduction.totalCostBounded`) are proof-support definitions outside every headline's
closure.

`ReductionDsl` is the first-order language in which security reductions of the computational proof
stack are written. It defines pure expressions (`Expr`) over inspectable data types (`unit`,
`bool`, `nat`, `opt`, `prod`, `sum`, `list`, `tbl`) and opaque abstract sorts `S.Base` accessed
solely through declared operation tables (`Ops`); monadic programs (`Comp`) with coin-only
`Samplers`, target-game oracle queries (`Iface`), and statically bounded loops; interpretation into
`VCVio` `OracleComp` (`Expr.eval`, `Comp.eval`); structural and input-specialized step-cost, query,
and syntax-size measures (`cost`, `costAt`, `queries`, `size`); and single- and two-stage
transducers (`CostedReduction`, `TwoStageCostedReduction`) over source-game codecs (`GameCodec`).
Shared operation tables, uniform samplers, and target codecs live in `AtomicOps.lean`,
`Samplers.lean`, and `Computational/Specifications/Reductions/ReductionDsl/TargetCodecs.lean`; see
`Computational/docs/REDUCTION_DSL_TUTORIAL.md`.

The efficiency model rests on five invariants:
1. *Sort opacity and table honesty.* `Expr` eliminates `.base b` only via `Expr.op`. Each table
   entry `O.cost o` bounds the work of `O.eval o` up to `O.cost o × (max input blocks)` under block
   measure `S.sz` and satisfies `OpsSizeHonest`; each query tag's `I.qCost` covers reading its
   argument and answer, `I.uCost` covers one forwarded uniform coin draw, and each coin-only
   sampler's constant `I.smp.sCost` bounds output width (`SampSizeHonest`). Reductions use only
   shared `Ops`, `Samplers`, `Iface`, and `GameCodec` tables.
2. *Bounded value growth.* Every value-growing constructor pays at least its output growth in
   blocks, bit-length, or list length, so run values stay within input size plus step cost plus a
   run-local oracle-answer bound (`Comp.fits_eval` in `Computational/Proofs/ReductionDsl/Size.lean`).
3. *Single-pass black-box execution.* `CostedReduction.eval` executes the adversary `A` once via
   `simulateQ` without rewinding (`TwoStageCostedReduction` pauses `A` at most once at a challenge
   query and resumes its continuation in stage 2), so `totalCost` and `totalQueries` bound work
   outside `A` and target queries (`Computational/Proofs/ReductionDsl/Soundness.lean`).
4. *Syntax-size bound.* Because branch cost takes `max` over arms, step cost alone allows a depth-`d`
   decision tree to embed a `2 ^ d`-entry non-uniform lookup table. Headline boundedness predicates
   therefore also require `size ≤ reductionSizeBudget` (`2 ^ 24` syntax nodes; both branch arms,
   numeric literal bit-lengths, `Ops.opSize` literal payloads, and each loop body count once).
5. *Input-specialized per-kind cost.* `Expr.costAt` and `Comp.costAt` charge branches only for the
   arm selected at `ρ` (computed via `Expr.eval`), and `Comp.bind` specializes its continuation
   only after an effect-free prefix (`Comp.pureEval?`), falling back to static `k.cost` after any
   sample, query, or monadic loop. `ValidKindCosts` quantifies over all states `s` and queries `t`,
   bounding per-query-kind work via `totalCostByKind`
   (`Computational/Proofs/ReductionDsl/KindedCost.lean`).
-/

@[expose] public section

namespace ReductionDsl

/-- Signature of abstract base sorts `Base` with carrier `den` and block-size measure `sz`
(e.g. `⌈len / w⌉` for byte strings of block width `w`, or `1` for fixed-width values). -/
structure Sig where
  Base : Type
  den : Base → Type
  sz : (b : Base) → den b → ℕ

variable {S : Sig}

/-- First-order value types over abstract sorts `S`: inspectable unit, booleans, naturals,
options, products, sums, finite lists, and total `ℕ`-indexed tables `tbl t`. -/
inductive Ty (S : Sig) where
  | base (b : S.Base)
  | unit | bool | nat
  | opt (t : Ty S)
  | prod (t u : Ty S)
  | sum (t u : Ty S)
  | list (t : Ty S)
  | tbl (t : Ty S)

/-- Carrier of a value type. -/
@[reducible] def Ty.denote : Ty S → Type
  | .base b => S.den b
  | .unit => Unit
  | .bool => Bool
  | .nat => ℕ
  | .opt t => Option t.denote
  | .prod t u => t.denote × u.denote
  | .sum t u => t.denote ⊕ u.denote
  | .list t => List t.denote
  | .tbl t => ℕ → t.denote

/-- Typed de Bruijn variables in context `Γ`. -/
inductive Var : List (Ty S) → Ty S → Type
  | zero {Γ t} : Var (t :: Γ) t
  | succ {Γ t u} : Var Γ t → Var (u :: Γ) t

/-- Evaluation environments for typed context `Γ`. -/
inductive Env : List (Ty S) → Type
  | nil : Env []
  | cons {Γ t} : t.denote → Env Γ → Env (t :: Γ)

def Env.get : {Γ : List (Ty S)} → {t : Ty S} → Env Γ → Var Γ t → t.denote
  | _, _, .cons x _, .zero => x
  | _, _, .cons _ ρ, .succ v => ρ.get v

/-- Table of primitive operations over `S` with semantics `eval`, step cost `cost`, and embedded
literal size `opSize` (charged in `Expr.size`; `0` by default). -/
structure Ops (S : Sig) where
  Op : Type
  dom : Op → Ty S
  cod : Op → Ty S
  eval : (o : Op) → (dom o).denote → (cod o).denote
  cost : Op → ℕ
  opSize : Op → ℕ := fun _ => 0

/-- Disjoint union of two operation tables over `S`. -/
def Ops.sum (O₁ O₂ : Ops S) : Ops S where
  Op := O₁.Op ⊕ O₂.Op
  dom := Sum.elim O₁.dom O₂.dom
  cod := Sum.elim O₁.cod O₂.cod
  eval := fun o => match o with
    | .inl o => O₁.eval o
    | .inr o => O₂.eval o
  cost := Sum.elim O₁.cost O₂.cost
  opSize := Sum.elim O₁.opSize O₂.opSize

/-- Bit-length cost `⌊log₂ n⌋ + 1` of a natural-number literal or constant operand `n`. -/
def bits (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Recursive size bound `B` on a value: `S.sz b x ≤ B` on base sorts, `bits n ≤ B` on `.nat`,
length and element bounds on `.list`, and pointwise bounds on `.tbl`. -/
def Ty.Fits (B : ℕ) : (t : Ty S) → t.denote → Prop
  | .base b, x => S.sz b x ≤ B
  | .unit, _ => True
  | .bool, _ => True
  | .nat, n => bits n ≤ B
  | .opt _, none => True
  | .opt t, some a => t.Fits B a
  | .prod t u, x => t.Fits B x.1 ∧ u.Fits B x.2
  | .sum t _, .inl a => t.Fits B a
  | .sum _ u, .inr b => u.Fits B b
  | .list t, l => l.length ≤ B ∧ ∀ x ∈ l, t.Fits B x
  | .tbl t, m => ∀ i, t.Fits B (m i)

abbrev ValFits {S : Sig} (B : ℕ) : (t : Ty S) → t.denote → Prop :=
  Ty.Fits B

/-- Size-honesty obligation on `O`: every operator `o` grows the `Ty.Fits` bound `B` by at most
`O.cost o`. -/
def OpsSizeHonest
    (O : Ops S) : Prop :=
  ∀ o x B, (O.dom o).Fits B x → (O.cod o).Fits (B + O.cost o) (O.eval o x)

/-- Leaf block bound: every `.base b` value inside `x` satisfies `S.sz b ≤ W`, independent of
list lengths and `.nat` bit-lengths. -/
def Ty.BaseFits (W : ℕ) : (t : Ty S) → t.denote → Prop
  | .base b, x => S.sz b x ≤ W
  | .unit, _ => True
  | .bool, _ => True
  | .nat, _ => True
  | .opt _, none => True
  | .opt t, some a => t.BaseFits W a
  | .prod t u, x => t.BaseFits W x.1 ∧ u.BaseFits W x.2
  | .sum t _, .inl a => t.BaseFits W a
  | .sum _ u, .inr b => u.BaseFits W b
  | .list t, l => ∀ x ∈ l, t.BaseFits W x
  | .tbl t, m => ∀ i, t.BaseFits W (m i)

/-- Uniform base-block bound on `O`: operators map `BaseFits W` inputs to `BaseFits (max W W_op)`
outputs, independent of accumulated step cost. -/
def OpsBaseBounded (O : Ops S) (W_op : ℕ) : Prop :=
  ∀ o x W, (O.dom o).BaseFits W x → (O.cod o).BaseFits (max W W_op) (O.eval o x)

/-- Maximum `.list` nesting depth of a type. -/
def Ty.listDepth : Ty S → ℕ
  | .base _ | .unit | .bool | .nat => 0
  | .opt t | .tbl t => t.listDepth
  | .prod t u | .sum t u => max t.listDepth u.listDepth
  | .list t => t.listDepth + 1

abbrev Ty.NoNestedLists (t : Ty S) : Prop := t.listDepth ≤ 1

/-- Whether `t` contains no functional `.tbl` nodes. -/
def Ty.HasNoTbl : Ty S → Bool
  | .base _ | .unit | .bool | .nat => true
  | .opt t | .list t => t.HasNoTbl
  | .prod t u | .sum t u => t.HasNoTbl && u.HasNoTbl
  | .tbl _ => false

/-- Total serialized block/bit weight across a value tree, summed across products and list elements
(`.tbl` contributes `0`; meaningful when `t.HasNoTbl`). -/
def Ty.treeBlocks : (t : Ty S) → t.denote → ℕ
  | .base b, x => S.sz b x + 1
  | .unit, _ => 1
  | .bool, _ => 1
  | .nat, n => bits n
  | .opt _, none => 1
  | .opt t, some a => 1 + t.treeBlocks a
  | .prod t u, x => 1 + t.treeBlocks x.1 + u.treeBlocks x.2
  | .sum t _, .inl a => 1 + t.treeBlocks a
  | .sum _ u, .inr b => 1 + u.treeBlocks b
  | .list t, l => 1 + (l.map t.treeBlocks).sum
  | .tbl _, _ => 0

/-- Pure expressions in context `Γ`. Multiplication, division, and modulus allow only constant
operands (`mulK`, `divK`, `modK`); bounded list combinators (`*B`) inspect at most the first `K`
entries. -/
inductive Expr (O : Ops S) : List (Ty S) → Ty S → Type
  | var {Γ t} : Var Γ t → Expr O Γ t
  | unit {Γ} : Expr O Γ .unit
  | bool {Γ} : Bool → Expr O Γ .bool
  | nat {Γ} : ℕ → Expr O Γ .nat
  | add {Γ} : Expr O Γ .nat → Expr O Γ .nat → Expr O Γ .nat
  | sub {Γ} : Expr O Γ .nat → Expr O Γ .nat → Expr O Γ .nat
  | mulK {Γ} : ℕ → Expr O Γ .nat → Expr O Γ .nat
  | divK {Γ} : ℕ → Expr O Γ .nat → Expr O Γ .nat
  | modK {Γ} : ℕ → Expr O Γ .nat → Expr O Γ .nat
  | lt {Γ} : Expr O Γ .nat → Expr O Γ .nat → Expr O Γ .bool
  | eqN {Γ} : Expr O Γ .nat → Expr O Γ .nat → Expr O Γ .bool
  | not {Γ} : Expr O Γ .bool → Expr O Γ .bool
  | and {Γ} : Expr O Γ .bool → Expr O Γ .bool → Expr O Γ .bool
  | ite {Γ t} : Expr O Γ .bool → Expr O Γ t → Expr O Γ t → Expr O Γ t
  | pair {Γ t u} : Expr O Γ t → Expr O Γ u → Expr O Γ (.prod t u)
  | fst {Γ t u} : Expr O Γ (.prod t u) → Expr O Γ t
  | snd {Γ t u} : Expr O Γ (.prod t u) → Expr O Γ u
  | inl {Γ t u} : Expr O Γ t → Expr O Γ (.sum t u)
  | inr {Γ t u} : Expr O Γ u → Expr O Γ (.sum t u)
  | none {Γ t} : Expr O Γ (.opt t)
  | some {Γ t} : Expr O Γ t → Expr O Γ (.opt t)
  | caseOpt {Γ t u} : Expr O Γ (.opt t) → Expr O Γ u → Expr O (t :: Γ) u → Expr O Γ u
  | caseSum {Γ t u v} : Expr O Γ (.sum t u) → Expr O (t :: Γ) v → Expr O (u :: Γ) v →
      Expr O Γ v
  | letE {Γ t u} : Expr O Γ t → Expr O (t :: Γ) u → Expr O Γ u
  | op {Γ} (o : O.Op) : Expr O Γ (O.dom o) → Expr O Γ (O.cod o)
  | nil {Γ t} : Expr O Γ (.list t)
  | cons {Γ t} : Expr O Γ t → Expr O Γ (.list t) → Expr O Γ (.list t)
  | len {Γ t} : Expr O Γ (.list t) → Expr O Γ .nat
  | take {Γ t} : Expr O Γ .nat → Expr O Γ (.list t) → Expr O Γ (.list t)
  /-- Concatenation truncated to the first `K` entries. -/
  | appendL {Γ t} (K : ℕ) : Expr O Γ (.list t) → Expr O Γ (.list t) → Expr O Γ (.list t)
  /-- First among the first `K` entries satisfying predicate `p` (entry bound at `v0`). -/
  | findB {Γ t} (K : ℕ) : Expr O Γ (.list t) → Expr O (t :: Γ) .bool → Expr O Γ (.opt t)
  | anyB {Γ t} (K : ℕ) : Expr O Γ (.list t) → Expr O (t :: Γ) .bool → Expr O Γ .bool
  | mapB {Γ t u} (K : ℕ) : Expr O Γ (.list t) → Expr O (t :: Γ) u → Expr O Γ (.list u)
  /-- Right fold over the first `K` entries (entry bound at `v0`, accumulator at `v1`). -/
  | foldrB {Γ t u} (K : ℕ) : Expr O Γ (.list t) → Expr O Γ u → Expr O (t :: u :: Γ) u →
      Expr O Γ u
  | tconst {Γ t} : Expr O Γ t → Expr O Γ (.tbl t)
  | tget {Γ t} : Expr O Γ (.tbl t) → Expr O Γ .nat → Expr O Γ t
  | tset {Γ t} : Expr O Γ (.tbl t) → Expr O Γ .nat → Expr O Γ t → Expr O Γ (.tbl t)

variable {O : Ops S}

-- De Bruijn variable shorthands (`Expr.v0` is the innermost binder).
def Expr.v0 {Γ t} : Expr O (t :: Γ) t := .var .zero
def Expr.v1 {Γ t a} : Expr O (a :: t :: Γ) t := .var (.succ .zero)
def Expr.v2 {Γ t a b} : Expr O (a :: b :: t :: Γ) t := .var (.succ (.succ .zero))
def Expr.v3 {Γ t a b c} : Expr O (a :: b :: c :: t :: Γ) t := .var (.succ (.succ (.succ .zero)))
def Expr.v4 {Γ t a b c d} : Expr O (a :: b :: c :: d :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ .zero))))
def Expr.v5 {Γ t a b c d e} : Expr O (a :: b :: c :: d :: e :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ (.succ .zero)))))
def Expr.v6 {Γ t a b c d e f} : Expr O (a :: b :: c :: d :: e :: f :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))

/-- Evaluates a pure expression in environment `ρ`. -/
def Expr.eval : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → Env Γ → t.denote
  | _, _, .var v, ρ => ρ.get v
  | _, _, .unit, _ => ()
  | _, _, .bool b, _ => b
  | _, _, .nat n, _ => n
  | _, _, .add a b, ρ => a.eval ρ + b.eval ρ
  | _, _, .sub a b, ρ => a.eval ρ - b.eval ρ
  | _, _, .mulK k a, ρ => k * a.eval ρ
  | _, _, .divK k a, ρ => a.eval ρ / k
  | _, _, .modK k a, ρ => a.eval ρ % k
  | _, _, .lt a b, ρ => decide (a.eval ρ < b.eval ρ)
  | _, _, .eqN a b, ρ => decide (a.eval ρ = b.eval ρ)
  | _, _, .not a, ρ => !a.eval ρ
  | _, _, .and a b, ρ => a.eval ρ && b.eval ρ
  | _, _, .ite c a b, ρ => if c.eval ρ then a.eval ρ else b.eval ρ
  | _, _, .pair a b, ρ => (a.eval ρ, b.eval ρ)
  | _, _, .fst a, ρ => (a.eval ρ).1
  | _, _, .snd a, ρ => (a.eval ρ).2
  | _, _, .inl a, ρ => Sum.inl (a.eval ρ)
  | _, _, .inr a, ρ => Sum.inr (a.eval ρ)
  | _, _, .none, _ => Option.none
  | _, _, .some a, ρ => Option.some (a.eval ρ)
  | _, _, .caseOpt e n s, ρ => match e.eval ρ with
    | Option.none => n.eval ρ
    | Option.some x => s.eval (.cons x ρ)
  | _, _, .caseSum e l r, ρ => match e.eval ρ with
    | Sum.inl x => l.eval (.cons x ρ)
    | Sum.inr y => r.eval (.cons y ρ)
  | _, _, .letE e b, ρ => b.eval (.cons (e.eval ρ) ρ)
  | _, _, .op o a, ρ => O.eval o (a.eval ρ)
  | _, _, .nil, _ => []
  | _, _, .cons x l, ρ => x.eval ρ :: l.eval ρ
  | _, _, .len l, ρ => (l.eval ρ).length
  | _, _, .take n l, ρ => (l.eval ρ).take (n.eval ρ)
  | _, _, .appendL K a b, ρ => (a.eval ρ ++ b.eval ρ).take K
  | _, _, .findB K l p, ρ => ((l.eval ρ).take K).find? fun x => p.eval (.cons x ρ)
  | _, _, .anyB K l p, ρ => ((l.eval ρ).take K).any fun x => p.eval (.cons x ρ)
  | _, _, .mapB K l f, ρ => ((l.eval ρ).take K).map fun x => f.eval (.cons x ρ)
  | _, _, .foldrB K l z f, ρ =>
    ((l.eval ρ).take K).foldr (fun x acc => f.eval (.cons x (.cons acc ρ))) (z.eval ρ)
  | _, _, .tconst a, ρ => fun _ => a.eval ρ
  | _, _, .tget m i, ρ => m.eval ρ (i.eval ρ)
  | _, _, .tset m i a, ρ => fun j => if j = i.eval ρ then a.eval ρ else m.eval ρ j

/-- Static step cost of an expression: branches charge `max` of their arms, loops charge `K`
times their body, and `.tget`/`.tset` charge `64`/`128`. -/
def Expr.cost : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ => 1
  | _, _, .unit => 1
  | _, _, .bool _ => 1
  | _, _, .nat n => bits n
  | _, _, .add a b => a.cost + b.cost + 1
  | _, _, .sub a b => a.cost + b.cost + 1
  | _, _, .mulK k a => a.cost + bits k
  | _, _, .divK k a => a.cost + bits k
  | _, _, .modK k a => a.cost + bits k
  | _, _, .lt a b => a.cost + b.cost + 1
  | _, _, .eqN a b => a.cost + b.cost + 1
  | _, _, .not a => a.cost + 1
  | _, _, .and a b => a.cost + b.cost + 1
  | _, _, .ite c a b => c.cost + max a.cost b.cost + 1
  | _, _, .pair a b => a.cost + b.cost + 1
  | _, _, .fst a => a.cost + 1
  | _, _, .snd a => a.cost + 1
  | _, _, .inl a => a.cost + 1
  | _, _, .inr a => a.cost + 1
  | _, _, .none => 1
  | _, _, .some a => a.cost + 1
  | _, _, .caseOpt e n s => e.cost + max n.cost s.cost + 1
  | _, _, .caseSum e l r => e.cost + max l.cost r.cost + 1
  | _, _, .letE e b => e.cost + b.cost + 1
  | _, _, .op o a => a.cost + O.cost o
  | _, _, .nil => 1
  | _, _, .cons x l => x.cost + l.cost + 1
  | _, _, .len l => l.cost + 1
  | _, _, .take n l => n.cost + l.cost + 1
  | _, _, .appendL K a b => a.cost + b.cost + K + 1
  | _, _, .findB K l p => l.cost + K * (p.cost + 1) + 1
  | _, _, .anyB K l p => l.cost + K * (p.cost + 1) + 1
  | _, _, .mapB K l f => l.cost + K * (f.cost + 1) + 1
  | _, _, .foldrB K l z f => l.cost + z.cost + K * (f.cost + 1) + 1
  | _, _, .tconst a => a.cost + 1
  | _, _, .tget m i => m.cost + i.cost + 64
  | _, _, .tset m i a => m.cost + i.cost + a.cost + 128

/-- Syntax-tree size of an expression: counts both branch arms, each loop body once, bit-lengths of
numeric literals and loop bounds, and `O.opSize o` for operator payloads. -/
def Expr.size : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ => 1
  | _, _, .unit => 1
  | _, _, .bool _ => 1
  | _, _, .nat n => bits n
  | _, _, .add a b => a.size + b.size + 1
  | _, _, .sub a b => a.size + b.size + 1
  | _, _, .mulK k a => a.size + bits k
  | _, _, .divK k a => a.size + bits k
  | _, _, .modK k a => a.size + bits k
  | _, _, .lt a b => a.size + b.size + 1
  | _, _, .eqN a b => a.size + b.size + 1
  | _, _, .not a => a.size + 1
  | _, _, .and a b => a.size + b.size + 1
  | _, _, .ite c a b => c.size + a.size + b.size + 1
  | _, _, .pair a b => a.size + b.size + 1
  | _, _, .fst a => a.size + 1
  | _, _, .snd a => a.size + 1
  | _, _, .inl a => a.size + 1
  | _, _, .inr a => a.size + 1
  | _, _, .none => 1
  | _, _, .some a => a.size + 1
  | _, _, .caseOpt e n s => e.size + n.size + s.size + 1
  | _, _, .caseSum e l r => e.size + l.size + r.size + 1
  | _, _, .letE e b => e.size + b.size + 1
  | _, _, .op o a => a.size + O.opSize o + 1
  | _, _, .nil => 1
  | _, _, .cons x l => x.size + l.size + 1
  | _, _, .len l => l.size + 1
  | _, _, .take n l => n.size + l.size + 1
  | _, _, .appendL K a b => a.size + b.size + bits K + 1
  | _, _, .findB K l p => l.size + p.size + bits K + 1
  | _, _, .anyB K l p => l.size + p.size + bits K + 1
  | _, _, .mapB K l f => l.size + f.size + bits K + 1
  | _, _, .foldrB K l z f => l.size + z.size + f.size + bits K + 1
  | _, _, .tconst a => a.size + 1
  | _, _, .tget m i => m.size + i.size + 1
  | _, _, .tset m i a => m.size + i.size + a.size + 1

/-- Syntax-tree size budget (`2 ^ 24` nodes) for headline-named reductions; bounds the non-uniform
lookup-table advice an existentially quantified reduction can embed. -/
def reductionSizeBudget : ℕ := 2 ^ 24

/-- Coin-only samplers (`ProbComp`, with no target queries) over typed domains and codomains with
constant per-sampler step cost `sCost`. -/
structure Samplers (S : Sig) where
  Samp : Type
  sDom : Samp → Ty S
  sTy : Samp → Ty S
  samp : (s : Samp) → (sDom s).denote → ProbComp (sTy s).denote
  sCost : Samp → ℕ

def Samplers.empty : Samplers S where
  Samp := Empty
  sDom := Empty.elim
  sTy := Empty.elim
  samp := fun s => s.elim
  sCost := Empty.elim

/-- Disjoint union of two sampler tables over `S`. -/
def Samplers.sum (X₁ X₂ : Samplers S) : Samplers S where
  Samp := X₁.Samp ⊕ X₂.Samp
  sDom := Sum.elim X₁.sDom X₂.sDom
  sTy := Sum.elim X₁.sTy X₂.sTy
  samp := fun s => match s with
    | .inl s => X₁.samp s
    | .inr s => X₂.samp s
  sCost := Sum.elim X₁.sCost X₂.sCost

/-- Size-honesty obligation on `X`: every sampled output grows the `Ty.Fits` bound `B` by at most
`X.sCost s`. -/
def SampSizeHonest (X : Samplers S) : Prop :=
  ∀ s x B, (X.sDom s).Fits B x →
    ∀ y ∈ support (X.samp s x), (X.sTy s).Fits (B + X.sCost s) y

/-- Uniform base-block bound on `X`: sampled outputs lie in `BaseFits (max W W_op)` whenever inputs
lie in `BaseFits W`. -/
def SampBaseBounded (X : Samplers S) (W_op : ℕ) : Prop :=
  ∀ s x W, (X.sDom s).BaseFits W x →
    ∀ y ∈ support (X.samp s x), (X.sTy s).BaseFits (max W W_op) y

/-- Parametric expression cost charging `cGet` per `.tget` and `cSet` per `.tset` (equal to
`Expr.cost` at `(64, 128)`). -/
def Expr.costWithTbl (cGet cSet : ℕ) : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ => 1
  | _, _, .unit => 1
  | _, _, .bool _ => 1
  | _, _, .nat n => bits n
  | _, _, .add a b => a.costWithTbl cGet cSet + b.costWithTbl cGet cSet + 1
  | _, _, .sub a b => a.costWithTbl cGet cSet + b.costWithTbl cGet cSet + 1
  | _, _, .mulK k a => a.costWithTbl cGet cSet + bits k
  | _, _, .divK k a => a.costWithTbl cGet cSet + bits k
  | _, _, .modK k a => a.costWithTbl cGet cSet + bits k
  | _, _, .lt a b => a.costWithTbl cGet cSet + b.costWithTbl cGet cSet + 1
  | _, _, .eqN a b => a.costWithTbl cGet cSet + b.costWithTbl cGet cSet + 1
  | _, _, .not a => a.costWithTbl cGet cSet + 1
  | _, _, .and a b => a.costWithTbl cGet cSet + b.costWithTbl cGet cSet + 1
  | _, _, .ite c a b =>
    c.costWithTbl cGet cSet + max (a.costWithTbl cGet cSet) (b.costWithTbl cGet cSet) + 1
  | _, _, .pair a b => a.costWithTbl cGet cSet + b.costWithTbl cGet cSet + 1
  | _, _, .fst a => a.costWithTbl cGet cSet + 1
  | _, _, .snd a => a.costWithTbl cGet cSet + 1
  | _, _, .inl a => a.costWithTbl cGet cSet + 1
  | _, _, .inr a => a.costWithTbl cGet cSet + 1
  | _, _, .none => 1
  | _, _, .some a => a.costWithTbl cGet cSet + 1
  | _, _, .caseOpt e n s =>
    e.costWithTbl cGet cSet + max (n.costWithTbl cGet cSet) (s.costWithTbl cGet cSet) + 1
  | _, _, .caseSum e l r =>
    e.costWithTbl cGet cSet + max (l.costWithTbl cGet cSet) (r.costWithTbl cGet cSet) + 1
  | _, _, .letE e b => e.costWithTbl cGet cSet + b.costWithTbl cGet cSet + 1
  | _, _, .op o a => a.costWithTbl cGet cSet + O.cost o
  | _, _, .nil => 1
  | _, _, .cons x l => x.costWithTbl cGet cSet + l.costWithTbl cGet cSet + 1
  | _, _, .len l => l.costWithTbl cGet cSet + 1
  | _, _, .take n l => n.costWithTbl cGet cSet + l.costWithTbl cGet cSet + 1
  | _, _, .appendL K a b => a.costWithTbl cGet cSet + b.costWithTbl cGet cSet + K + 1
  | _, _, .findB K l p => l.costWithTbl cGet cSet + K * (p.costWithTbl cGet cSet + 1) + 1
  | _, _, .anyB K l p => l.costWithTbl cGet cSet + K * (p.costWithTbl cGet cSet + 1) + 1
  | _, _, .mapB K l f => l.costWithTbl cGet cSet + K * (f.costWithTbl cGet cSet + 1) + 1
  | _, _, .foldrB K l z f =>
    l.costWithTbl cGet cSet + z.costWithTbl cGet cSet + K * (f.costWithTbl cGet cSet + 1) + 1
  | _, _, .tconst a => a.costWithTbl cGet cSet + 1
  | _, _, .tget m i => m.costWithTbl cGet cSet + i.costWithTbl cGet cSet + cGet
  | _, _, .tset m i a =>
    m.costWithTbl cGet cSet + i.costWithTbl cGet cSet + a.costWithTbl cGet cSet + cSet

/-- Oracle interface into target specification `T`: typed query tags encoded as single `T`-queries
with step cost `qCost`, uniform-coin forwarding `fwdU` of cost `uCost`, and samplers `smp`. -/
structure Iface (S : Sig) {ι : Type} (T : OracleSpec ι) where
  /-- Forwards an adversary uniform-coin draw `Fin (n + 1)` (`unifSpec`) into `OracleComp T`. -/
  fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))
  /-- Step cost of forwarding one uniform coin draw via `fwdU`. -/
  uCost : ℕ
  Tag : Type
  dom : Tag → Ty S
  cod : Tag → Ty S
  enc : (g : Tag) → (dom g).denote → ι
  dec : (g : Tag) → (x : (dom g).denote) → T (enc g x) → (cod g).denote
  qCost : Tag → ℕ
  smp : Samplers S

/-- Extends interface `I` with additional samplers `X`. -/
def Iface.withSamp {ι : Type} {T : OracleSpec ι} (I : Iface S T) (X : Samplers S) : Iface S T :=
  { I with smp := I.smp.sum X }

/-- Lifts a coin-only `ProbComp` into `OracleComp T` by forwarding coin draws via `I.fwdU`. -/
def Iface.liftP {ι : Type} {T : OracleSpec ι} (I : Iface S T) {α : Type} (p : ProbComp α) :
    OracleComp T α :=
  simulateQ (fun n => I.fwdU n : QueryImpl unifSpec (OracleComp T)) p

variable {ι : Type} {T : OracleSpec ι} {I : Iface S T}

/-- Monadic programs over `O` and `I`: pure returns, sequencing, branching, sampling, target
queries, and statically bounded loops (`n` iterations or at most the first `K` list entries). -/
inductive Comp (O : Ops S) (I : Iface S T) : List (Ty S) → Ty S → Type
  | ret {Γ t} : Expr O Γ t → Comp O I Γ t
  | bind {Γ t u} : Comp O I Γ t → Comp O I (t :: Γ) u → Comp O I Γ u
  | ite {Γ t} : Expr O Γ .bool → Comp O I Γ t → Comp O I Γ t → Comp O I Γ t
  | caseOpt {Γ t u} : Expr O Γ (.opt t) → Comp O I Γ u → Comp O I (t :: Γ) u → Comp O I Γ u
  | caseSum {Γ t u v} : Expr O Γ (.sum t u) → Comp O I (t :: Γ) v → Comp O I (u :: Γ) v →
      Comp O I Γ v
  | sample {Γ} (s : I.smp.Samp) : Expr O Γ (I.smp.sDom s) → Comp O I Γ (I.smp.sTy s)
  | query {Γ} (g : I.Tag) : Expr O Γ (I.dom g) → Comp O I Γ (I.cod g)
  /-- Runs `n` iterations of `body` from initial accumulator `init` (bound at `v0`). -/
  | iter {Γ t} (n : ℕ) : Expr O Γ t → Comp O I (t :: Γ) t → Comp O I Γ t
  /-- Short-circuiting monadic search over the first `K` entries. -/
  | findM {Γ t} (K : ℕ) : Expr O Γ (.list t) → Comp O I (t :: Γ) .bool → Comp O I Γ (.opt t)
  /-- Short-circuiting monadic existential check over the first `K` entries. -/
  | anyM {Γ t} (K : ℕ) : Expr O Γ (.list t) → Comp O I (t :: Γ) .bool → Comp O I Γ .bool
  | mapM {Γ t u} (K : ℕ) : Expr O Γ (.list t) → Comp O I (t :: Γ) u → Comp O I Γ (.list u)
  /-- Replaces the first among the first `K` entries passing the test with `mark` of it; yields
  `(found, updatedPrefix)`. -/
  | consumeFirstM {Γ t} (K : ℕ) : Expr O Γ (.list t) → Comp O I (t :: Γ) .bool →
      Expr O (t :: Γ) t → Comp O I Γ (.prod .bool (.list t))
  /-- Monadic left fold over the first `K` entries (entry bound at `v0`, accumulator at `v1`). -/
  | foldM {Γ t u} (K : ℕ) : Expr O Γ (.list t) → Expr O Γ u → Comp O I (t :: u :: Γ) u →
      Comp O I Γ u

def iterM {m : Type → Type} [Monad m] {α : Type} (f : α → m α) : ℕ → α → m α
  | 0, a => pure a
  | n + 1, a => f a >>= iterM f n

def findML {m : Type → Type} [Monad m] {α : Type} (p : α → m Bool) : List α → m (Option α)
  | [] => pure Option.none
  | x :: xs => do if ← p x then pure (Option.some x) else findML p xs

def anyML {m : Type → Type} [Monad m] {α : Type} (p : α → m Bool) : List α → m Bool
  | [] => pure false
  | x :: xs => do if ← p x then pure true else anyML p xs

def mapML {m : Type → Type} [Monad m] {α β : Type} (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do let y ← f x; let ys ← mapML f xs; pure (y :: ys)

/-- Short-circuiting replacement of the first entry passing `p` by `mark` of it. -/
def consumeFirstML {m : Type → Type} [Monad m] {α : Type} (p : α → m Bool) (mark : α → α) :
    List α → m (Bool × List α)
  | [] => pure (false, [])
  | x :: xs => do
    if ← p x then pure (true, mark x :: xs)
    else do let r ← consumeFirstML p mark xs; pure (r.1, x :: r.2)

def foldML {m : Type → Type} [Monad m] {α β : Type} (f : α → β → m β) : β → List α → m β
  | b, [] => pure b
  | b, x :: xs => do let b' ← f x b; foldML f b' xs

/-- Interprets a `Comp` program into `OracleComp T`. -/
def Comp.eval : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → Env Γ → OracleComp T t.denote
  | _, _, .ret e, ρ => pure (e.eval ρ)
  | _, _, .bind c k, ρ => c.eval ρ >>= fun x => k.eval (.cons x ρ)
  | _, _, .ite b c d, ρ => if b.eval ρ then c.eval ρ else d.eval ρ
  | _, _, .caseOpt e n s, ρ => match e.eval ρ with
    | Option.none => n.eval ρ
    | Option.some x => s.eval (.cons x ρ)
  | _, _, .caseSum e l r, ρ => match e.eval ρ with
    | Sum.inl x => l.eval (.cons x ρ)
    | Sum.inr y => r.eval (.cons y ρ)
  | _, _, .sample s e, ρ => I.liftP (I.smp.samp s (e.eval ρ))
  | _, _, .query g e, ρ =>
    let x := e.eval ρ
    I.dec g x <$> (liftM (T.query (I.enc g x)) : OracleComp T _)
  | _, _, .iter n e body, ρ => iterM (fun a => body.eval (.cons a ρ)) n (e.eval ρ)
  | _, _, .findM K l p, ρ => findML (fun x => p.eval (.cons x ρ)) ((l.eval ρ).take K)
  | _, _, .anyM K l p, ρ => anyML (fun x => p.eval (.cons x ρ)) ((l.eval ρ).take K)
  | _, _, .mapM K l f, ρ => mapML (fun x => f.eval (.cons x ρ)) ((l.eval ρ).take K)
  | _, _, .consumeFirstM K l p mk, ρ =>
    consumeFirstML (fun x => p.eval (.cons x ρ)) (fun x => mk.eval (.cons x ρ))
      ((l.eval ρ).take K)
  | _, _, .foldM K l z f, ρ =>
    foldML (fun x acc => f.eval (.cons x (.cons acc ρ))) (z.eval ρ) ((l.eval ρ).take K)

/-- Static step cost of a program: branches charge `max` of their arms and loops charge `n` or `K`
times their body. -/
def Comp.cost : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => e.cost + 1
  | _, _, .bind c k => c.cost + k.cost + 1
  | _, _, .ite b c d => b.cost + max c.cost d.cost + 1
  | _, _, .caseOpt e n s => e.cost + max n.cost s.cost + 1
  | _, _, .caseSum e l r => e.cost + max l.cost r.cost + 1
  | _, _, .sample s e => e.cost + I.smp.sCost s
  | _, _, .query g e => e.cost + I.qCost g
  | _, _, .iter n e body => e.cost + n * (body.cost + 1) + 1
  | _, _, .findM K l p => l.cost + K * (p.cost + 1) + 1
  | _, _, .anyM K l p => l.cost + K * (p.cost + 1) + 1
  | _, _, .mapM K l f => l.cost + K * (f.cost + 1) + 1
  | _, _, .consumeFirstM K l p mk => l.cost + K * (p.cost + mk.cost + 1) + 1
  | _, _, .foldM K l z f => l.cost + z.cost + K * (f.cost + 1) + 1

/-- Static weighted upper bound on target queries (`w`) and samples (`ws`). -/
def Comp.queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret _ => 0
  | _, _, .bind c k => c.queries w ws + k.queries w ws
  | _, _, .ite _ c d => max (c.queries w ws) (d.queries w ws)
  | _, _, .caseOpt _ n s => max (n.queries w ws) (s.queries w ws)
  | _, _, .caseSum _ l r => max (l.queries w ws) (r.queries w ws)
  | _, _, .sample s _ => ws s
  | _, _, .query g _ => w g
  | _, _, .iter n _ body => n * body.queries w ws
  | _, _, .findM K _ p => K * p.queries w ws
  | _, _, .anyM K _ p => K * p.queries w ws
  | _, _, .mapM K _ f => K * f.queries w ws
  | _, _, .consumeFirstM K _ p _ => K * p.queries w ws
  | _, _, .foldM K _ _ f => K * f.queries w ws

/-- Syntax-tree size of a program: counts both branch arms, each loop body once, and bit-lengths of
loop bounds `n` and `K`. -/
def Comp.size : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => e.size + 1
  | _, _, .bind c k => c.size + k.size + 1
  | _, _, .ite b c d => b.size + c.size + d.size + 1
  | _, _, .caseOpt e n s => e.size + n.size + s.size + 1
  | _, _, .caseSum e l r => e.size + l.size + r.size + 1
  | _, _, .sample _ e => e.size + 1
  | _, _, .query _ e => e.size + 1
  | _, _, .iter n e body => e.size + body.size + bits n + 1
  | _, _, .findM K l p => l.size + p.size + bits K + 1
  | _, _, .anyM K l p => l.size + p.size + bits K + 1
  | _, _, .mapM K l f => l.size + f.size + bits K + 1
  | _, _, .consumeFirstM K l p mk => l.size + p.size + mk.size + bits K + 1
  | _, _, .foldM K l z f => l.size + z.size + f.size + bits K + 1

/-- Encoding of source-game `G` queries into `Q` (`qenc`) and decoding of `R` values into `G`
answers (`rdec`), with per-query encoding/decoding overhead `codecCost`. -/
structure GameCodec (S : Sig) {κ : Type} (G : OracleSpec κ) where
  Q : Ty S
  R : Ty S
  qenc : (t : κ) → Q.denote
  rdec : (t : κ) → R.denote → G t
  codecCost : ℕ

variable {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}

/-- Simulates `unifSpec + G` in state `σ` by forwarding coins via `I.fwdU` and answering
`G`-queries with `h` (in context `[σ, C.Q]`). -/
def handlerImpl {σ : Ty S} (h : Comp O I [σ, C.Q] (.prod C.R σ)) :
    QueryImpl (unifSpec + G) (StateT σ.denote (OracleComp T)) := fun q => match q with
  | .inl n => StateT.lift (I.fwdU n)
  | .inr t => StateT.mk fun s => do
    let p ← h.eval (.cons s (.cons (C.qenc t) .nil))
    return (C.rdec t p.1, p.2)

/-- Single-stage black-box reduction against game `G` (codec `C`) with state `σ`: `init` maps
reduction input `rIn` to `(aIn, σ)`, `handle` maps `(σ, C.Q)` to `(C.R, σ)`, and `finish` maps
`(σ, aOut)` to `out`. -/
structure CostedReduction (O : Ops S) (I : Iface S T) {κ : Type} (G : OracleSpec κ) (C : GameCodec S G)
    (rIn aIn aOut out : Ty S) where
  σ : Ty S
  init : Comp O I [rIn] (.prod aIn σ)
  handle : Comp O I [σ, C.Q] (.prod C.R σ)
  finish : Comp O I [σ, aOut] out

variable {rIn aIn aOut out : Ty S}

def CostedReduction.impl (R : CostedReduction O I G C rIn aIn aOut out) :
    QueryImpl (unifSpec + G) (StateT R.σ.denote (OracleComp T)) :=
  handlerImpl R.handle

/-- Runs reduction `R` once around adversary `A` on input `x` in `OracleComp T`. -/
def CostedReduction.eval (R : CostedReduction O I G C rIn aIn aOut out)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    OracleComp T out.denote := do
  let (a, s) ← R.init.eval (.cons x .nil)
  let (b, s') ← (simulateQ R.impl (A a)).run s
  R.finish.eval (.cons s' (.cons b .nil))

/-- Upper bound on step cost outside `A` when `A` makes at most `q` total `unifSpec + G` queries. -/
def CostedReduction.totalCost (R : CostedReduction O I G C rIn aIn aOut out) (q : ℕ) : ℕ :=
  R.init.cost + q * (max I.uCost (R.handle.cost + C.codecCost)) + R.finish.cost

/-- Weighted upper bound on target queries and samples when `A` makes at most `q` `G`-queries. -/
def CostedReduction.totalQueries (R : CostedReduction O I G C rIn aIn aOut out) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (q : ℕ) : ℕ :=
  R.init.queries w ws + q * R.handle.queries w ws + R.finish.queries w ws

/-- Total syntax-tree size of `R` (`init`, `handle`, and `finish` counted once each). -/
def CostedReduction.size (R : CostedReduction O I G C rIn aIn aOut out) : ℕ :=
  R.init.size + R.handle.size + R.finish.size

/-! ## Two-stage reductions -/

/-- Stage-1 termination state: either `A` finished (`done`), or `A` paused (`paused`) at query `t`
with stage-1 challenge output `c`, saved pause data `p`, state `s`, and continuation `k`. -/
inductive Mid (G : OracleSpec κ) (α π σ χ : Type) where
  | done (a : α) (s : σ)
  | paused (t : κ) (c : χ) (p : π) (s : σ) (k : G t → OracleComp (unifSpec + G) α)

/-- Two-stage black-box reduction against `G` (codec `C`) for a target taking stage-1 output `ch`
and supplying stage-2 input `rIn2`. In stage 1, `handlePre` either answers a `G`-query (`inl`) or
pauses (`inr`) with `(c, p, σ')`, and `chDone` produces `c` if `A` finishes without pausing; in
stage 2, `resume` answers the paused query from `rIn2`, `handlePost` answers subsequent queries,
and `finish` computes the final output.

In `eval1` and `eval2`, `fuel` caps `G`-queries per stage (returning `dflt` on exhaustion) while
coin draws are forwarded without consuming fuel; setting `fuel := q` when `A` makes at most `q`
`G`-queries across both stages makes the fallback unreachable. See `eval1Bounded` and
`eval2Bounded` for explicit coin and game-query fuel. -/
structure TwoStageCostedReduction (O : Ops S) (I : Iface S T) {κ : Type} (G : OracleSpec κ) (C : GameCodec S G)
    (rIn aIn aOut ch rIn2 out : Ty S) where
  σ : Ty S
  π : Ty S
  init : Comp O I [rIn] (.prod aIn σ)
  handlePre : Comp O I [σ, C.Q] (.sum (.prod C.R σ) (.prod ch (.prod π σ)))
  chDone : Comp O I [σ, aOut] ch
  resume : Comp O I [σ, π, rIn2] (.prod C.R σ)
  handlePost : Comp O I [σ, C.Q] (.prod C.R σ)
  finish : Comp O I [σ, aOut, rIn2] out

variable {ch rIn2 : Ty S}

/-- Runs stage 1 on `oa` for at most `fuel` `G`-queries (coins forwarded via `I.fwdU`); returns
`.done dflt s` on fuel exhaustion. -/
def TwoStageCostedReduction.run1 (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + G) α) :
    ℕ → R.σ.denote → OracleComp T (Mid G α R.π.denote R.σ.denote ch.denote) :=
  OracleComp.construct
    (C := fun _ => ℕ → R.σ.denote → OracleComp T (Mid G α R.π.denote R.σ.denote ch.denote))
    (fun a _ s => pure (.done a s))
    (fun q k r f s => match q with
      | .inl n => do let u ← I.fwdU n; r u f s
      | .inr t => match f with
        | 0 => pure (.done dflt s)
        | f + 1 => do
          match ← R.handlePre.eval (.cons s (.cons (C.qenc t) .nil)) with
          | .inl (v, s') => r (C.rdec t v) f s'
          | .inr (c, p, s') => pure (.paused t c p s' k))
    oa

/-- Runs `oa` under handler `h` for at most `fuel` `G`-queries (coins forwarded via `I.fwdU`);
returns `(dflt, s)` on fuel exhaustion. -/
def runFuel {σ : Ty S} (h : Comp O I [σ, C.Q] (.prod C.R σ)) {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + G) α) : ℕ → σ.denote → OracleComp T (α × σ.denote) :=
  OracleComp.construct (C := fun _ => ℕ → σ.denote → OracleComp T (α × σ.denote))
    (fun a _ s => pure (a, s))
    (fun q _ r f s => match q with
      | .inl n => do let u ← I.fwdU n; r u f s
      | .inr t => match f with
        | 0 => pure (dflt, s)
        | f + 1 => do
          let p ← h.eval (.cons s (.cons (C.qenc t) .nil))
          r (C.rdec t p.1) f p.2)
    oa

/-- Executes stage 1 of `R` on adversary `A` and input `x` with `G`-query budget `fuel` and
fallback output `dflt`; yields the target's stage-1 input and `Mid` state. -/
def TwoStageCostedReduction.eval1 (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) (fuel : ℕ)
    (dflt : aOut.denote) :
    OracleComp T (ch.denote × Mid G aOut.denote R.π.denote R.σ.denote ch.denote) := do
  let (a, s) ← R.init.eval (.cons x .nil)
  let m ← R.run1 dflt (A a) fuel s
  match m with
  | .done b s' => do let c ← R.chDone.eval (.cons s' (.cons b .nil)); pure (c, m)
  | .paused _ c _ _ _ => pure (c, m)

/-- Resumes `m` with stage-2 target input `y` under `G`-query budget `fuel` and fallback `dflt`,
then runs `R.finish`. -/
def TwoStageCostedReduction.eval2 (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote) (y : rIn2.denote) (fuel : ℕ)
    (dflt : aOut.denote) : OracleComp T out.denote := do
  let (b, s) ← match m with
    | .done b s => pure (b, s)
    | .paused t _ p s k => do
      let (v, s') ← R.resume.eval (.cons s (.cons p (.cons y .nil)))
      runFuel R.handlePost dflt (k (C.rdec t v)) fuel s'
  R.finish.eval (.cons s (.cons b (.cons y .nil)))

/-- Upper bound on step cost outside `A` across both stages when `A` makes at most `q` total
`unifSpec + G` queries. -/
def TwoStageCostedReduction.totalCost (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) (q : ℕ) : ℕ :=
  R.init.cost + q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) +
    max R.chDone.cost R.resume.cost + R.finish.cost

/-- Weighted upper bound on target queries and samples across both stages when `A` makes at most
`q` `G`-queries. -/
def TwoStageCostedReduction.totalQueries (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) (w : I.Tag → ℕ)
    (ws : I.smp.Samp → ℕ) (q : ℕ) : ℕ :=
  R.init.queries w ws + q * max (R.handlePre.queries w ws) (R.handlePost.queries w ws) +
    max (R.chDone.queries w ws) (R.resume.queries w ws) + R.finish.queries w ws

/-- Total syntax-tree size of `R` across all six stage components, counted once each. -/
def TwoStageCostedReduction.size (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) : ℕ :=
  R.init.size + R.handlePre.size + R.chDone.size + R.resume.size + R.handlePost.size +
    R.finish.size

/-! ## Run-local size premises -/

open OracleSpec OracleComp in
/-- Run-local query-size bound: along every execution branch of `oa`, each game query `.inr t`
satisfies `C.Q.Fits B (C.qenc t)` (coin queries `.inl n` are unconstrained). Adapted from an
earlier definition by Swarat Chaudhuri. -/
def AllGameQueriesFit {κ : Type} {G : OracleSpec κ}
    (B : ℕ) (C : GameCodec S G) {α : Type}
    (oa : OracleComp (unifSpec + G) α) : Prop :=
  OracleComp.construct
    (C := fun _ => Prop)
    (fun _ => True)
    (fun q _ r => match q with
      | .inl _ => ∀ u, r u
      | .inr t => C.Q.Fits B (C.qenc t) ∧ ∀ u, r u)
    oa

open OracleSpec OracleComp in
/-- Outputs reachable by `oa` along execution branches where every oracle query `t` receives an
answer `u` satisfying `P t u` (equals `support oa` when `P` is `True`). -/
def supportWhen {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (P : (t : ι') → spec t → Prop) (oa : OracleComp spec α) : Set α :=
  OracleComp.construct
    (C := fun _ => Set α)
    (fun a => {a})
    (fun t _ r => {y | ∃ u, P t u ∧ y ∈ r u})
    oa

/-- Run-local answer-size predicate: target answer `u : T i` decodes within `Ty.Fits B` under
every tag `g` and input `x` with `I.enc g x = i`. -/
def Iface.AnswerFits (I : Iface S T) (B : ℕ) (i : ι) (u : T i) : Prop :=
  ∀ (g : I.Tag) (x : (I.dom g).denote) (h : I.enc g x = i),
    (I.cod g).Fits B (I.dec g x (cast (congrArg T h).symm u))

/-! ## Input-specialized per-query-kind cost bounds -/

/-- Input-specialized cost of evaluating `e` in `ρ`: matches `Expr.cost`, except `ite`, `caseOpt`,
`caseSum`, and `letE` charge their guard or bound expression plus only the branch taken at `ρ`
(bounded list loops still charge static body `.cost`). -/
def Expr.costAt : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → Env Γ → ℕ
  | _, _, .var _, _ => 1
  | _, _, .unit, _ => 1
  | _, _, .bool _, _ => 1
  | _, _, .nat n, _ => bits n
  | _, _, .add a b, ρ => a.costAt ρ + b.costAt ρ + 1
  | _, _, .sub a b, ρ => a.costAt ρ + b.costAt ρ + 1
  | _, _, .mulK k a, ρ => a.costAt ρ + bits k
  | _, _, .divK k a, ρ => a.costAt ρ + bits k
  | _, _, .modK k a, ρ => a.costAt ρ + bits k
  | _, _, .lt a b, ρ => a.costAt ρ + b.costAt ρ + 1
  | _, _, .eqN a b, ρ => a.costAt ρ + b.costAt ρ + 1
  | _, _, .not a, ρ => a.costAt ρ + 1
  | _, _, .and a b, ρ => a.costAt ρ + b.costAt ρ + 1
  | _, _, .ite c a b, ρ => c.costAt ρ + (if c.eval ρ then a.costAt ρ else b.costAt ρ) + 1
  | _, _, .pair a b, ρ => a.costAt ρ + b.costAt ρ + 1
  | _, _, .fst a, ρ => a.costAt ρ + 1
  | _, _, .snd a, ρ => a.costAt ρ + 1
  | _, _, .inl a, ρ => a.costAt ρ + 1
  | _, _, .inr a, ρ => a.costAt ρ + 1
  | _, _, .none, _ => 1
  | _, _, .some a, ρ => a.costAt ρ + 1
  | _, _, .caseOpt e n s, ρ =>
    e.costAt ρ + (match e.eval ρ with
      | Option.none => n.costAt ρ
      | Option.some x => s.costAt (.cons x ρ)) + 1
  | _, _, .caseSum e l r, ρ =>
    e.costAt ρ + (match e.eval ρ with
      | Sum.inl x => l.costAt (.cons x ρ)
      | Sum.inr y => r.costAt (.cons y ρ)) + 1
  | _, _, .letE e b, ρ => e.costAt ρ + b.costAt (.cons (e.eval ρ) ρ) + 1
  | _, _, .op o a, ρ => a.costAt ρ + O.cost o
  | _, _, .nil, _ => 1
  | _, _, .cons x l, ρ => x.costAt ρ + l.costAt ρ + 1
  | _, _, .len l, ρ => l.costAt ρ + 1
  | _, _, .take n l, ρ => n.costAt ρ + l.costAt ρ + 1
  | _, _, .appendL K a b, ρ => a.costAt ρ + b.costAt ρ + K + 1
  | _, _, .findB K l p, ρ => l.costAt ρ + K * (p.cost + 1) + 1
  | _, _, .anyB K l p, ρ => l.costAt ρ + K * (p.cost + 1) + 1
  | _, _, .mapB K l f, ρ => l.costAt ρ + K * (f.cost + 1) + 1
  | _, _, .foldrB K l z f, ρ => l.costAt ρ + z.costAt ρ + K * (f.cost + 1) + 1
  | _, _, .tconst a, ρ => a.costAt ρ + 1
  | _, _, .tget m i, ρ => m.costAt ρ + i.costAt ρ + 64
  | _, _, .tset m i a, ρ => m.costAt ρ + i.costAt ρ + a.costAt ρ + 128

/-- Evaluates an effect-free prefix of `c` in `ρ`; returns `none` if execution reaches a sample,
target query, or monadic loop. -/
def Comp.pureEval? : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → Env Γ → Option t.denote
  | _, _, .ret e, ρ => Option.some (e.eval ρ)
  | _, _, .bind c k, ρ => (c.pureEval? ρ).bind fun x => k.pureEval? (.cons x ρ)
  | _, _, .ite b c d, ρ => if b.eval ρ then c.pureEval? ρ else d.pureEval? ρ
  | _, _, .caseOpt e n s, ρ => match e.eval ρ with
    | Option.none => n.pureEval? ρ
    | Option.some x => s.pureEval? (.cons x ρ)
  | _, _, .caseSum e l r, ρ => match e.eval ρ with
    | Sum.inl x => l.pureEval? (.cons x ρ)
    | Sum.inr y => r.pureEval? (.cons y ρ)
  | _, _, .sample _ _, _ => Option.none
  | _, _, .query _ _, _ => Option.none
  | _, _, .iter _ _ _, _ => Option.none
  | _, _, .findM _ _ _, _ => Option.none
  | _, _, .anyM _ _ _, _ => Option.none
  | _, _, .mapM _ _ _, _ => Option.none
  | _, _, .consumeFirstM _ _ _ _, _ => Option.none
  | _, _, .foldM _ _ _ _, _ => Option.none

/-- Input-specialized cost of running `c` in `ρ`: branches charge only the arm taken at `ρ`, `bind`
specializes its continuation when `c.pureEval? ρ = some x` (and charges static `k.cost` otherwise),
and loops charge static body `.cost`. -/
def Comp.costAt : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → Env Γ → ℕ
  | _, _, .ret e, ρ => e.costAt ρ + 1
  | _, _, .bind c k, ρ =>
    c.costAt ρ + (match c.pureEval? ρ with
      | Option.some x => k.costAt (.cons x ρ)
      | Option.none => k.cost) + 1
  | _, _, .ite b c d, ρ => b.costAt ρ + (if b.eval ρ then c.costAt ρ else d.costAt ρ) + 1
  | _, _, .caseOpt e n s, ρ =>
    e.costAt ρ + (match e.eval ρ with
      | Option.none => n.costAt ρ
      | Option.some x => s.costAt (.cons x ρ)) + 1
  | _, _, .caseSum e l r, ρ =>
    e.costAt ρ + (match e.eval ρ with
      | Sum.inl x => l.costAt (.cons x ρ)
      | Sum.inr y => r.costAt (.cons y ρ)) + 1
  | _, _, .sample s e, ρ => e.costAt ρ + I.smp.sCost s
  | _, _, .query g e, ρ => e.costAt ρ + I.qCost g
  | _, _, .iter n e body, ρ => e.costAt ρ + n * (body.cost + 1) + 1
  | _, _, .findM K l p, ρ => l.costAt ρ + K * (p.cost + 1) + 1
  | _, _, .anyM K l p, ρ => l.costAt ρ + K * (p.cost + 1) + 1
  | _, _, .mapM K l f, ρ => l.costAt ρ + K * (f.cost + 1) + 1
  | _, _, .consumeFirstM K l p mk, ρ => l.costAt ρ + K * (p.cost + mk.cost + 1) + 1
  | _, _, .foldM K l z f, ρ => l.costAt ρ + z.costAt ρ + K * (f.cost + 1) + 1

/-- Per-kind handler cost bound: from any state `s`, handling game query `t` costs at most
`hCost (kind t)` under `costAt`. -/
def CostedReduction.ValidKindCosts (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (kind : κ → Fin n) (hCost : Fin n → ℕ) : Prop :=
  ∀ (s : R.σ.denote) (t : κ),
    R.handle.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ hCost (kind t)

/-- Step-cost bound outside `A` when `A`'s `G`-queries are partitioned into `n` kinds with at most
`qKind i` queries and handler cost `hCost i` for kind `i` (forwarded coin draws are not counted in
`qKind`). -/
def CostedReduction.totalCostByKind (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (hCost qKind : Fin n → ℕ) : ℕ :=
  R.init.cost +
    (List.ofFn fun i => qKind i * max I.uCost (hCost i + C.codecCost)).sum +
    R.finish.cost

/-- Existence of valid per-kind handler cost bounds `hCost` with `R.totalCostByKind hCost qKind ≤ B`. -/
def CostedReduction.CostBoundedByKind (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ) (B : ℕ) : Prop :=
  ∃ hCost : Fin n → ℕ, R.ValidKindCosts kind hCost ∧ R.totalCostByKind hCost qKind ≤ B

/-- Two-stage per-kind handler cost bound covering both `handlePre` and `handlePost`. -/
def TwoStageCostedReduction.ValidKindCosts
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (kind : κ → Fin n) (hCost : Fin n → ℕ) : Prop :=
  ∀ (s : R.σ.denote) (t : κ),
    R.handlePre.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ hCost (kind t) ∧
    R.handlePost.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ hCost (kind t)

/-- Step-cost bound outside `A` across both stages when `A` makes at most `qKind i` `G`-queries of
kind `i` in total (forwarded coin draws are not counted in `qKind`). -/
def TwoStageCostedReduction.totalCostByKind
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (hCost qKind : Fin n → ℕ) : ℕ :=
  R.init.cost +
    (List.ofFn fun i => qKind i * max I.uCost (hCost i + C.codecCost)).sum +
    max R.chDone.cost R.resume.cost + R.finish.cost

/-- Two-stage counterpart of `CostedReduction.CostBoundedByKind`. -/
def TwoStageCostedReduction.CostBoundedByKind
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ) (B : ℕ) : Prop :=
  ∃ hCost : Fin n → ℕ, R.ValidKindCosts kind hCost ∧ R.totalCostByKind hCost qKind ≤ B

/-! ## Parametric table cost, query-conditioned codecs, and dual-fuel runners -/

/-- Parametric program cost charging `cGet` per `.tget` and `cSet` per `.tset`. -/
def Comp.costWithTbl (cGet cSet : ℕ) : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => e.costWithTbl cGet cSet + 1
  | _, _, .bind c k => c.costWithTbl cGet cSet + k.costWithTbl cGet cSet + 1
  | _, _, .ite b c d =>
    b.costWithTbl cGet cSet + max (c.costWithTbl cGet cSet) (d.costWithTbl cGet cSet) + 1
  | _, _, .caseOpt e n s =>
    e.costWithTbl cGet cSet + max (n.costWithTbl cGet cSet) (s.costWithTbl cGet cSet) + 1
  | _, _, .caseSum e l r =>
    e.costWithTbl cGet cSet + max (l.costWithTbl cGet cSet) (r.costWithTbl cGet cSet) + 1
  | _, _, .sample s e => e.costWithTbl cGet cSet + I.smp.sCost s
  | _, _, .query g e => e.costWithTbl cGet cSet + I.qCost g
  | _, _, .iter n e body => e.costWithTbl cGet cSet + n * (body.costWithTbl cGet cSet + 1) + 1
  | _, _, .findM K l p => l.costWithTbl cGet cSet + K * (p.costWithTbl cGet cSet + 1) + 1
  | _, _, .anyM K l p => l.costWithTbl cGet cSet + K * (p.costWithTbl cGet cSet + 1) + 1
  | _, _, .mapM K l f => l.costWithTbl cGet cSet + K * (f.costWithTbl cGet cSet + 1) + 1
  | _, _, .consumeFirstM K l p mk =>
    l.costWithTbl cGet cSet + K * (p.costWithTbl cGet cSet + mk.costWithTbl cGet cSet + 1) + 1
  | _, _, .foldM K l z f =>
    l.costWithTbl cGet cSet + z.costWithTbl cGet cSet + K * (f.costWithTbl cGet cSet + 1) + 1

/-- Input-conditioned codec size bound: every query `t` satisfying `qPred t` encodes within
`C.Q.Fits qB`. -/
def GameCodec.FitsOn (C : GameCodec S G) (qPred : κ → Prop) (qB : ℕ) : Prop :=
  ∀ t, qPred t → C.Q.Fits qB (C.qenc t)

/-- Base-block counterpart of `GameCodec.FitsOn`. -/
def GameCodec.BaseFitsOn (C : GameCodec S G) (qPred : κ → Prop) (W : ℕ) : Prop :=
  ∀ t, qPred t → C.Q.BaseFits W (C.qenc t)

/-- Step-cost bound outside `A` when `A` makes at most `qU` coin draws and `qG` game queries. -/
def CostedReduction.totalCostBounded (R : CostedReduction O I G C rIn aIn aOut out)
    (qU qG : ℕ) : ℕ :=
  R.init.cost + qU * I.uCost + qG * (R.handle.cost + C.codecCost) + R.finish.cost

/-- Stage-1 runner with separate coin fuel `uFuel` and game-query fuel `gFuel`; returns
`.done dflt s` when either budget is exhausted. -/
def TwoStageCostedReduction.run1Bounded
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ℕ → ℕ → R.σ.denote → OracleComp T (Mid G α R.π.denote R.σ.denote ch.denote) :=
  OracleComp.construct
    (C := fun _ => ℕ → ℕ → R.σ.denote → OracleComp T (Mid G α R.π.denote R.σ.denote ch.denote))
    (fun a _ _ s => pure (.done a s))
    (fun q k r uf gf s => match q with
      | .inl n => match uf with
        | 0 => pure (.done dflt s)
        | uf + 1 => do let u ← I.fwdU n; r u uf gf s
      | .inr t => match gf with
        | 0 => pure (.done dflt s)
        | gf + 1 => do
          match ← R.handlePre.eval (.cons s (.cons (C.qenc t) .nil)) with
          | .inl (v, s') => r (C.rdec t v) uf gf s'
          | .inr (c, p, s') => pure (.paused t c p s' k))
    oa

/-- Handler loop with separate coin fuel `uFuel` and game-query fuel `gFuel`; returns `(dflt, s)`
when either budget is exhausted. -/
def runFuelBounded {σ : Ty S} (h : Comp O I [σ, C.Q] (.prod C.R σ)) {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + G) α) : ℕ → ℕ → σ.denote → OracleComp T (α × σ.denote) :=
  OracleComp.construct (C := fun _ => ℕ → ℕ → σ.denote → OracleComp T (α × σ.denote))
    (fun a _ _ s => pure (a, s))
    (fun q _ r uf gf s => match q with
      | .inl n => match uf with
        | 0 => pure (dflt, s)
        | uf + 1 => do let u ← I.fwdU n; r u uf gf s
      | .inr t => match gf with
        | 0 => pure (dflt, s)
        | gf + 1 => do
          let p ← h.eval (.cons s (.cons (C.qenc t) .nil))
          r (C.rdec t p.1) uf gf p.2)
    oa

/-- Stage 1 of `R` with explicit `(uFuel, gFuel)` coin and game-query budgets. -/
def TwoStageCostedReduction.eval1Bounded
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote)
    (uFuel gFuel : ℕ) (dflt : aOut.denote) :
    OracleComp T (ch.denote × Mid G aOut.denote R.π.denote R.σ.denote ch.denote) := do
  let (a, s) ← R.init.eval (.cons x .nil)
  let m ← R.run1Bounded dflt (A a) uFuel gFuel s
  match m with
  | .done b s' => do let c ← R.chDone.eval (.cons s' (.cons b .nil)); pure (c, m)
  | .paused _ c _ _ _ => pure (c, m)

/-- Stage 2 of `R` with explicit `(uFuel, gFuel)` coin and game-query budgets. -/
def TwoStageCostedReduction.eval2Bounded
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote) (y : rIn2.denote)
    (uFuel gFuel : ℕ) (dflt : aOut.denote) : OracleComp T out.denote := do
  let (b, s) ← match m with
    | .done b s => pure (b, s)
    | .paused t _ p s k => do
      let (v, s') ← R.resume.eval (.cons s (.cons p (.cons y .nil)))
      runFuelBounded R.handlePost dflt (k (C.rdec t v)) uFuel gFuel s'
  R.finish.eval (.cons s (.cons b (.cons y .nil)))

/-- Step-cost bound outside `A` across both stages when `A` makes at most `qU` coin draws and `qG`
game queries in total. -/
def TwoStageCostedReduction.totalCostBounded
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) (qU qG : ℕ) : ℕ :=
  R.init.cost + qU * I.uCost + qG * (max R.handlePre.cost R.handlePost.cost + C.codecCost) +
    max R.chDone.cost R.resume.cost + R.finish.cost

end ReductionDsl
