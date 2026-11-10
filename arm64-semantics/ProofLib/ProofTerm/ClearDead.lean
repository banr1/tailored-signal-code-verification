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
# Dead-Hypothesis Elimination

Provides `clear_dead` (cone-of-influence pruning over free variables) and `clear_dead!`
(left-to-right rewrite reachability pruning closed under projection prefixes), along with
`clear_dead?`, `clear_dead!?`, and `keep` modifiers for protecting designated hypotheses.
-/

namespace ProofLib.ProofTerm

public meta section

open Lean Meta Elab Tactic

/-- Free variables occurring in `e`. -/
def fvarsOf (e : Expr) : Std.HashSet FVarId :=
  (Lean.collectFVars {} e).fvarIds.foldl (·.insert ·) {}

/-- Cone-of-influence liveness: the declarations to keep in the current local context.
    A propositional hypothesis is live when it mentions a live free variable or no free variable
    at all; the free variables of a live hypothesis become live. -/
def coneLive (goal : Expr) (keep : Array FVarId) : MetaM (Std.HashSet FVarId) := do
  let lctx ← getLCtx
  let mut live : Std.HashSet FVarId := fvarsOf goal
  for k in keep do
    live := live.insert k
    live := (fvarsOf (← instantiateMVars (← k.getType))).fold (·.insert ·) live
  let mut props : Array (FVarId × Std.HashSet FVarId) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then
      props := props.push (d.fvarId, fvarsOf (← instantiateMVars d.type))
  let mut changed := true
  while changed do
    changed := false
    for (fv, fvs) in props do
      if live.contains fv then continue
      if fvs.isEmpty || fvs.toList.any live.contains then
        live := live.insert fv
        live := fvs.fold (·.insert ·) live
        changed := true
  return live

/-- Term-level, directed liveness (left-to-right rewriting reachability, closed under projection
    prefixes). Returns the live equation hypotheses. -/
def directedLiveEqs (goal : Expr) (seeds : Array Expr) : MetaM (Std.HashSet FVarId) := do
  let lctx ← getLCtx
  let mut byLhs : Std.HashMap Expr (Array (FVarId × Expr)) := {}
  for d in lctx do
    if d.isImplementationDetail || d.value?.isSome then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, r) := ty.eq? then
      byLhs := byLhs.insert l ((byLhs.getD l #[]).push (d.fvarId, r))
  let mut live : Std.HashSet FVarId := {}
  let mut seen : Std.HashSet Expr := {}
  let mut work : Array Expr := seeds.push goal
  while h : work.size > 0 do
    let t := work[work.size - 1]
    work := work.pop
    if seen.contains t then continue
    seen := seen.insert t
    match t with
    | .app f a => work := (work.push f).push a
    | .proj _ _ b | .mdata _ b => work := work.push b
    | .lam _ ty b _ | .forallE _ ty b _ => work := (work.push ty).push b
    | .letE _ ty v b _ => work := ((work.push ty).push v).push b
    | _ => pure ()
    -- `t` and the prefixes of its projection chain (`f s`, `s.i`).
    let mut prefixes : Array Expr := #[t]
    let mut cur := t
    for _ in [0:8] do
      match cur with
      | .app f a => if f.isConst then cur := a; prefixes := prefixes.push cur else break
      | .proj _ _ b => cur := b; prefixes := prefixes.push cur
      | _ => break
    for p in prefixes do
      for (fv, rhs) in byLhs.getD p #[] do
        live := live.insert fv
        work := work.push rhs
        unless p == t do
          work := work.push (t.replace fun e => if e == p then some rhs else none)
  return live

/-- The declarations of the current context that `clear_dead` (or `clear_dead!` when
    `aggressive`) would clear, in context order. -/
def deadDecls (g : MVarId) (aggressive : Bool) (keep : Array FVarId) : MetaM (Array FVarId) :=
  g.withContext do
    let goal ← instantiateMVars (← g.getType)
    let mut used : Std.HashSet FVarId := {}
    if aggressive then
      let seeds ← keep.mapM fun k => do instantiateMVars (← k.getType)
      let liveEqs ← directedLiveEqs goal seeds
      used := fvarsOf goal
      for k in keep do
        used := (fvarsOf (← instantiateMVars (← k.getType))).fold (·.insert ·) (used.insert k)
      for fv in liveEqs do
        used := (fvarsOf (← instantiateMVars (← fv.getType))).fold (·.insert ·) (used.insert fv)
    else
      used ← coneLive goal keep
    let decls := (← getLCtx).decls.toArray.filterMap id
    let mut dead : Array FVarId := #[]
    for i in [0:decls.size] do
      let d := decls[decls.size - 1 - i]!
      if d.isImplementationDetail then continue
      if used.contains d.fvarId then
        used := (fvarsOf (← instantiateMVars d.type)).fold (·.insert ·) used
        if let some v := d.value? then
          used := (fvarsOf (← instantiateMVars v)).fold (·.insert ·) used
      else
        dead := dead.push d.fvarId
    return dead.reverse

/-- Clear the dead declarations of `g`; returns the new goal and the user names cleared. -/
def clearDead (g : MVarId) (aggressive : Bool) (keep : Array FVarId) :
    MetaM (MVarId × Array Name) := do
  let dead ← deadDecls g aggressive keep
  if dead.isEmpty then return (g, #[])
  let names ← g.withContext <| dead.mapM fun fv => return (← fv.getDecl).userName
  let g' ← g.tryClearMany dead
  let cleared ← g'.withContext do
    let lctx ← getLCtx
    return (dead.zip names).filterMap fun (fv, n) => if lctx.contains fv then none else some n
  return (g', cleared)

/-- Clear hypotheses outside the cone of influence of the goal's free variables.
    `clear_dead keep h₁ h₂` preserves `h₁` and `h₂`. -/
syntax (name := clearDeadTac) "clear_dead" (&" keep" (ppSpace colGt ident)+)? : tactic
/-- Clear hypotheses not reachable from the goal by left-to-right equation rewriting. -/
syntax (name := clearDeadBangTac) "clear_dead!" (&" keep" (ppSpace colGt ident)+)? : tactic
/-- Run `clear_dead` and log the equivalent `clear h₁ h₂ ...` command. -/
syntax (name := clearDeadQTac) "clear_dead?" (&" keep" (ppSpace colGt ident)+)? : tactic
/-- Run `clear_dead!` and log the equivalent `clear h₁ h₂ ...` command. -/
syntax (name := clearDeadBangQTac) "clear_dead!?" (&" keep" (ppSpace colGt ident)+)? : tactic

/-- Shared implementation of the four `clear_dead` spellings. -/
def evalClearDead (aggressive report : Bool) (keep : Array Ident) : TacticM Unit := do
  let g ← getMainGoal
  let keepFVars ← g.withContext <| keep.mapM fun id => return (← getLocalDeclFromUserName id.getId).fvarId
  let (g', cleared) ← clearDead g aggressive keepFVars
  replaceMainGoal [g']
  if report then
    if cleared.isEmpty then
      logInfo m!"clear_dead: nothing to clear"
    else
      let ids := cleared.map fun n => mkIdent n
      let stx ← `(tactic| clear $ids*)
      logInfo m!"Try this: {stx}"

@[tactic clearDeadTac] def elabClearDead : Tactic
  | `(tactic| clear_dead $[keep $ks*]?) => evalClearDead false false (ks.getD #[])
  | _ => throwUnsupportedSyntax

@[tactic clearDeadBangTac] def elabClearDeadBang : Tactic
  | `(tactic| clear_dead! $[keep $ks*]?) => evalClearDead true false (ks.getD #[])
  | _ => throwUnsupportedSyntax

@[tactic clearDeadQTac] def elabClearDeadQ : Tactic
  | `(tactic| clear_dead? $[keep $ks*]?) => evalClearDead false true (ks.getD #[])
  | _ => throwUnsupportedSyntax

@[tactic clearDeadBangQTac] def elabClearDeadBangQ : Tactic
  | `(tactic| clear_dead!? $[keep $ks*]?) => evalClearDead true true (ks.getD #[])
  | _ => throwUnsupportedSyntax

end

end ProofLib.ProofTerm
