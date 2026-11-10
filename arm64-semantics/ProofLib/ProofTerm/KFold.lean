/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
import Arm64.Trusted.Spec.SepLogic

/-!
# Goal Subterm Sharing via `let`

Provides `kfold` and `kfold?` to greedily introduce local `let` bindings (`kf_i := t`) for repeated
closed subterms of the goal maximizing `(occurrences - 1) * size`, reducing goal and proof-term
tree size across subsequent tactics.
-/

namespace ProofLib.ProofTerm

public meta section

open Lean Meta Elab Tactic

/-- Saturating tree size and tree-occurrence count of every distinct sub-term. -/
structure SubtermStats where
  size : Std.HashMap Expr Nat := {}
  occ : Std.HashMap Expr Nat := {}

/-- Cap for tree sizes, so that exponentially shared terms do not overflow the heuristic. -/
def sizeCap : Nat := 1 <<< 40

/-- Children of a node (binder bodies keep their loose bound variables). -/
def children : Expr → Array Expr
  | .app f a => #[f, a]
  | .lam _ d b _ | .forallE _ d b _ => #[d, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

/-- Post-order list of the distinct subterms of `e` (children before parents). -/
partial def postOrder (e : Expr) : Array Expr := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut out : Array Expr := #[]
  let mut stack : Array (Expr × Bool) := #[(e, false)]
  while h : stack.size > 0 do
    let (t, expanded) := stack[stack.size - 1]
    stack := stack.pop
    if expanded then
      out := out.push t
    else if !seen.contains t then
      seen := seen.insert t
      stack := stack.push (t, true)
      for c in children t do
        unless seen.contains c do stack := stack.push (c, false)
  return out

/-- Tree sizes and tree-occurrence counts of the subterms of `e`. -/
def subtermStats (e : Expr) : SubtermStats := Id.run do
  let order := postOrder e
  let mut size : Std.HashMap Expr Nat := {}
  for t in order do
    let s := (children t).foldl (fun acc c => acc + size.getD c 1) 1
    size := size.insert t (min s sizeCap)
  let mut occ : Std.HashMap Expr Nat := {}
  occ := occ.insert e 1
  for i in [0:order.size] do
    let t := order[order.size - 1 - i]!
    let o := occ.getD t 0
    for c in children t do
      occ := occ.insert c (min (occ.getD c 0 + o) sizeCap)
  return { size, occ }

/-- A subterm `kfold` may bind: closed under the local context (no loose bound variables, no
    metavariables) and non-atomic. -/
def foldable (t : Expr) : Bool :=
  !t.hasLooseBVars && !t.hasMVar && !t.isFVar && !t.isConst && !t.isSort && !t.isLit &&
    !t.isMData && !t.isBVar

/-- The subterm with the largest saving `(occ - 1) * size` among those of at least `minSize`
    nodes that occur at least twice. -/
def bestCandidate (e : Expr) (minSize : Nat) : Option (Expr × Nat × Nat) := Id.run do
  let st := subtermStats e
  let mut best : Option (Expr × Nat × Nat) := none
  let mut bestSaving := 0
  for (t, s) in st.size do
    if s < minSize || !foldable t then continue
    let o := st.occ.getD t 0
    if o < 2 then continue
    let saving := (o - 1) * s
    if saving > bestSaving then
      best := some (t, s, o)
      bestSaving := saving
  return best

/-- Tree size of `e` (saturating). -/
def treeSize (e : Expr) : Nat := (subtermStats e).size.getD e 1

/-- One `kfold` step: bind `t` as `let kf_i := t` and replace it in the target. -/
def foldOnce (g : MVarId) (t : Expr) (i : Nat) : MetaM MVarId := g.withContext do
  let ty ← inferType t
  let name := Name.mkSimple s!"kf_{i}"
  let g ← g.define name ty t
  let (x, g) ← g.intro1P
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let xe := mkFVar x
    let target' := target.replace fun e => if e == t then some xe else none
    g.replaceTargetDefEq target'

/-- Run `kfold`; returns the new goal and, per folded term, `(size, occurrences, term)`. -/
def kfoldCore (g : MVarId) (minSize maxLets : Nat) :
    MetaM (MVarId × Array (Nat × Nat × Expr) × Nat × Nat) := do
  let before := treeSize (← instantiateMVars (← g.getType))
  let mut g := g
  let mut folded := #[]
  for i in [1:maxLets + 1] do
    let target ← instantiateMVars (← g.getType)
    match bestCandidate target minSize with
    | none => break
    | some (t, s, o) =>
      g ← foldOnce g t i
      folded := folded.push (s, o, t)
  let after := treeSize (← instantiateMVars (← g.getType))
  return (g, folded, before, after)

/-- Bind repeated closed subterms of the goal as `let` variables (`minSize` default 24, `maxLets` default 16). -/
syntax (name := kfoldTac) "kfold" (" (" &"minSize" " := " num ")")?
  (" (" &"maxLets" " := " num ")")? : tactic
/-- Run `kfold` and log folded subterms along with goal tree sizes before and after. -/
syntax (name := kfoldQTac) "kfold?" (" (" &"minSize" " := " num ")")?
  (" (" &"maxLets" " := " num ")")? : tactic

/-- Shared implementation of `kfold` / `kfold?`. -/
def evalKFold (minSize maxLets : Nat) (report : Bool) : TacticM Unit := do
  let g ← getMainGoal
  let (g', folded, before, after) ← kfoldCore g minSize maxLets
  replaceMainGoal [g']
  if report then
    if folded.isEmpty then
      logInfo m!"kfold: no closed sub-term of at least {minSize} nodes occurs twice"
    else
      let mut msg := m!"kfold: {folded.size} let-bindings, goal tree size {before} → {after}"
      let mut i : Nat := 0
      for (s, o, t) in folded do
        i := i + 1
        msg := msg ++ m!"\n  kf_{i}: {o} occurrences × {s} nodes: {t}"
      logInfo msg

@[tactic kfoldTac] def elabKFold : Tactic
  | `(tactic| kfold $[(minSize := $m)]? $[(maxLets := $k)]?) =>
    evalKFold ((m.map (·.getNat)).getD 24) ((k.map (·.getNat)).getD 16) false
  | _ => throwUnsupportedSyntax

@[tactic kfoldQTac] def elabKFoldQ : Tactic
  | `(tactic| kfold? $[(minSize := $m)]? $[(maxLets := $k)]?) =>
    evalKFold ((m.map (·.getNat)).getD 24) ((k.map (·.getNat)).getD 16) true
  | _ => throwUnsupportedSyntax

end

end ProofLib.ProofTerm
