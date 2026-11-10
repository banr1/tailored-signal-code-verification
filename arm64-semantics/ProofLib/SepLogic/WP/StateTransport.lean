/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.SepLogic.WP.Defs
public meta import ProofLib.SepLogic.WP.FrameTransportAttr

/-!
# State-Indexed Frame Atom Transport

Tactic automation (`wp_frame_transport`, `wp_frame_transport_discharge`, `wp_rel_close`) that
transports state-indexed spatial precondition atoms `f ... s0 ...` to the current `SepWP` / `SepWPp`
goal state `s'` using registered `@[frame_transport]` equations of the form
`forall ..., Rel s s' -> f ... s' ... = f ... s ...`. Invoked automatically after `wp_call` and
`wpp_call` unless `proofLib.wpCallFrameTransport` is set to `false`.
-/

@[expose] public section

namespace ProofLib

open Arm64
open Lean Elab Tactic Meta

/-- Discharger for the preservation side condition `Rel s0 s'` of a `@[frame_transport]` lemma.
    Extend with `macro_rules | `(tactic| wp_frame_transport_discharge) => `(tactic| ...)`. -/
syntax "wp_frame_transport_discharge" : tactic

macro_rules
  | `(tactic| wp_frame_transport_discharge) => `(tactic| first
      | assumption
      | (repeat' apply And.intro) <;>
          first
          | assumption
          | (apply Eq.symm; assumption)
          | rfl
          | (simp only [wp_norm, arm64_norm] <;> first
              | assumption | (apply Eq.symm; assumption) | rfl))

end ProofLib

public meta section

namespace ProofLib

open Arm64
open Lean Elab Tactic Meta

register_option proofLib.wpCallFrameTransport : Bool := {
  defValue := true
  descr := "After `wp_call` / `wpp_call`, move state-indexed spatial precondition atoms matching a `@[frame_transport]` lemma to the post-call state (see `wp_frame_transport`)."
}

/-- Flatten a right- or left-nested separating conjunction tree into its atoms. -/
partial def frameTransportAtoms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``SepProp.sepConj 2 then
    frameTransportAtoms e.appArg! (frameTransportAtoms e.appFn!.appArg! acc)
  else acc.push e

/-- Fallback discharger for `R x s'` (`R` a constant): given `h : R y s'`, unfold `R` in `h` and the
    goal, normalize with `wp_norm` / `arm64_norm`, and close the goal with `h`. -/
def frameTransportFromHyps (mv : MVarId) : TacticM Bool := mv.withContext do
  let goalTy ← instantiateMVars (← mv.getType)
  let R := goalTy.getAppFn
  unless R.isConst && goalTy.getAppNumArgs ≥ 1 do return false
  let σ := goalTy.appArg!
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.getAppFn.isConstOf R.constName! && t.getAppNumArgs == goalTy.getAppNumArgs do
      continue
    unless t.appArg! == σ do continue
    let saved ← saveState
    try
      let (_, mv2) ← mv.note `h_frame_rel d.toExpr
      let hId := mkIdent `h_frame_rel
      let rId := mkIdent R.constName!
      let rest ← Tactic.run mv2 (withoutRecover (evalTactic (← `(tactic|
        ((simp only [$rId:ident, wp_norm, arm64_norm] at $hId:ident ⊢) <;>
          first | exact $hId:ident | assumption)))))
      if rest.isEmpty then return true
      saved.restore
    catch _ =>
      saved.restore
  return false

/-- Index of the transported state in a `@[frame_transport]` equation `f ... s' ... = f ... s ...`:
    the unique argument position where the two sides differ as distinct metavariables, or `none`. -/
def frameTransportStateArg? (lhs rhs : Expr) : Option Nat := Id.run do
  let la := lhs.getAppArgs
  let ra := rhs.getAppArgs
  unless la.size == ra.size do return none
  let mut found : Option Nat := none
  for i in [0:la.size] do
    if la[i]! != ra[i]! then
      if found.isSome then return none
      unless la[i]!.isMVar && ra[i]!.isMVar do return none
      found := some i
  return found

/-- Close `R x s'` (`R` a constant) from a chain of local hypotheses `R x0 x1`, `R y1 x2`, ... by
    unfolding `R` in those hypotheses and the goal, normalizing with `wp_norm` / `arm64_norm`, and
    rewriting. -/
def relCloseFromHyps (mv : MVarId) : TacticM Bool := mv.withContext do
  let goalTy ← instantiateMVars (← mv.getType)
  let R := goalTy.getAppFn
  unless R.isConst && goalTy.getAppNumArgs ≥ 2 do return false
  let saved ← saveState
  let msgs := (← getThe Core.State).messages
  let orig := mv
  let mut hs : Array Ident := #[]
  let mut n := 0
  let mut mv := mv
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.getAppFn.isConstOf R.constName! && t.getAppNumArgs == goalTy.getAppNumArgs do
      continue
    let nm := Name.mkSimple s!"h_rel_chain_{n}"
    n := n + 1
    let (_, mv') ← mv.note nm d.toExpr
    mv := mv'
    hs := hs.push (mkIdent nm)
  if hs.isEmpty then return false
  try
    let rId := mkIdent R.constName!
    let rest ← Tactic.run mv (withoutRecover (evalTactic (← `(tactic|
      ((simp only [$rId:ident, wp_norm, arm64_norm] at $[$hs:ident]* ⊢);
        first
        | done
        | (simp only [$[$hs:ident],*]; done)
        | (simp only [$[$hs:ident],*, and_self, true_and, and_true]; done)
        | (simp_all only [and_self, true_and, and_true]; done))))))
    -- Reject admitted goals containing synthetic sorries or unassigned metavariables.
    let prf ← instantiateMVars (.mvar orig)
    if rest.isEmpty && !prf.hasSyntheticSorry && !prf.hasExprMVar then return true
    saved.restore
    modifyThe Core.State fun st => { st with messages := msgs }
    return false
  catch _ =>
    saved.restore
    modifyThe Core.State fun st => { st with messages := msgs }
    return false

/-- `wp_rel_close`: close a preservation goal `R x s'` from a chain of `R` hypotheses (see
    `relCloseFromHyps`). -/
elab "wp_rel_close" : tactic => do
  unless ← relCloseFromHyps (← getMainGoal) do
    throwError "wp_rel_close: could not close the goal from the hypotheses of the same relation"
  replaceMainGoal []

/-- Try to build `atom = f ... s' ...` from the `@[frame_transport]` lemma `lem`
    (`forall ..., Rel s s' -> f ... s' ... = f ... s ...`), returning `(newAtom, eqProof)`. -/
def frameTransportTryLemma (atom σ : Expr) (lem : Name) : TacticM (Option (Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
  let saved ← saveState
  try
    let lemE ← mkConstWithFreshMVarLevels lem
    let (xs, _, body) ← forallMetaTelescopeReducing (← inferType lemE)
    let some (_, lhs, rhs) := body.eq? | throwError "skip"
    unless lhs.getAppFn.isConst && atom.getAppFn.isConst &&
        lhs.getAppFn.constName! == atom.getAppFn.constName! &&
        lhs.getAppNumArgs == atom.getAppNumArgs &&
        rhs.getAppNumArgs == lhs.getAppNumArgs do
      throwError "skip"
    let some k := frameTransportStateArg? lhs rhs | throwError "skip"
    unless ← isDefEq rhs atom do throwError "skip"
    let sNew := lhs.getArg! k
    unless sNew.isMVar && !(← sNew.mvarId!.isAssigned) do throwError "skip"
    unless ← isDefEq sNew σ do throwError "skip"
    let newAtom ← instantiateMVars lhs
    if newAtom == atom then throwError "skip"
    for x in xs do
      let x ← instantiateMVars x
      unless x.isMVar do continue
      let mv := x.mvarId!
      if ← mv.isAssigned then continue
      unless ← isProp (← mv.getType) do throwError "skip"
      -- `withoutRecover` prevents a failing discharger from admitting the side condition.
      let savedD ← saveState
      let ok ← try
          let rest ← Tactic.run mv
            (withoutRecover (evalTactic (← `(tactic| wp_frame_transport_discharge))))
          pure rest.isEmpty
        catch _ => pure false
      unless ok do
        savedD.restore
        unless ← frameTransportFromHyps mv do
          unless ← relCloseFromHyps mv do throwError "skip"
    let prf ← instantiateMVars (mkAppN lemE xs)
    if prf.hasExprMVar || prf.hasSyntheticSorry then throwError "skip"
    return some (newAtom, ← mkEqSymm prf)
  catch _ =>
    saved.restore
    return none

/-- Run `wp_frame_transport` on the main goal; returns the number of atoms moved.
    Only the spatial precondition (argument 3 of `SepWP` / `SepWPp`) is rewritten;
    other goals are left unchanged. -/
def frameTransportMain : TacticM Nat := do
  let lems ← labelled `frame_transport
  if lems.isEmpty then return 0
  let mut moved := 0
  let mut progress := true
  while progress do
    progress := false
    let g ← getMainGoal
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    unless ty.isAppOfArity ``SepWP 6 || ty.isAppOfArity ``SepWPp 7 do return moved
    let σ := ty.getArg! 2
    let P := ty.getArg! 3
    for atom in frameTransportAtoms P do
      if progress then break
      for lem in lems do
        if let some (newAtom, eqPrf) ← frameTransportTryLemma atom σ lem then
          let g ← getMainGoal
          let newTy? ← g.withContext do
            let absP ← kabstract P atom
            unless absP.hasLooseBVars do return none
            let args := ty.getAppArgs
            let motive := Expr.lam `x (← inferType atom)
              (mkAppN ty.getAppFn (args.set! 3 absP)) .default
            let newTy := mkAppN ty.getAppFn (args.set! 3 (absP.instantiate1 newAtom))
            return some (newTy, ← mkCongrArg motive eqPrf)
          if let some (newTy, tyEq) := newTy? then
            let g' ← g.replaceTargetEq newTy tyEq
            replaceMainGoal [g']
            moved := moved + 1
            progress := true
            break
  return moved

/-- Apply frame transport to every open goal (silently; used by `wp_call` / `wpp_call`). -/
def frameTransportAllGoals : TacticM Unit := do
  unless proofLib.wpCallFrameTransport.get (← getOptions) do return
  if (← labelled `frame_transport).isEmpty then return
  let gs ← getUnsolvedGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    try
      let _ ← frameTransportMain
      out := out ++ (← getUnsolvedGoals)
    catch _ =>
      out := out.push g
  setGoals out.toList

/-- Move state-indexed spatial precondition atoms to the goal's current state using
    `@[frame_transport]` lemmas; fails if no atom was moved. -/
elab "wp_frame_transport" : tactic => do
  let n ← frameTransportMain
  if n == 0 then
    throwError "wp_frame_transport: no state-indexed atom could be moved to the current state (no matching `@[frame_transport]` lemma, or `wp_frame_transport_discharge` failed on its side condition)"

end ProofLib

end
