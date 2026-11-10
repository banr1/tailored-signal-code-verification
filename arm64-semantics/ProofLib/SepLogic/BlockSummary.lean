/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.WP
public meta import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.FrameInfer
import Arm64.Trusted.Spec.SepLogic

/-!
# Block Summaries

Reusable continuation-style `SepWP` summaries for straight-line instruction segments:
- `block_summary name binders : BlockSegment prog s P stop [using tac]` executes `prog` from state
  `s` and spatial context `P` until `pc = stop`, adding a kernel-checked theorem
  `name : forall binders {target post oom}, (forall ys, SepWP prog target s' P' post oom) -> SepWP prog target s P post oom`.
- `wp_block h` applies a summary `h` to a `SepWP` goal, framing the spatial precondition via
  `sep_frame` when needed, discharging side conditions, and introducing the segment's facts `ys`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Statement marker for `block_summary`: denotes the straight-line run of `prog` starting in state
    `s` with spatial context `P` and stopping at the first state with program counter `stop`. -/
def BlockSegment (_prog : Program) (_s : State) (_P : SepProp) (_stop : BitVec 64) : Prop := True

/-- Rewrite the spatial precondition of a `SepWP` judgement along an equality. -/
theorem SepWP.of_pre_eq {prog : Program} {target : BitVec 64} {s : State} {P Q : SepProp}
    {post : State → SepProp → Prop}
    (h : SepWP prog target s Q post) (hPQ : P = Q) : SepWP prog target s P post :=
  hPQ ▸ h

end ProofLib

end

public meta section

namespace ProofLib.BlockSummary

open Lean Meta Elab Term Command Tactic
open Arm64

register_option proofLib.blockSummary.maxSteps : Nat := {
  defValue := 4096
  descr := "maximum number of instructions `block_summary` executes before giving up"
}

/-- Step the main `SepWP` goal with `wp_step` until its program counter reaches `stop`, returning
    the number of instructions executed. -/
def stepTo (stop : Expr) (maxSteps : Nat) : TacticM Nat := do
  let mut n := 0
  for _ in [0:maxSteps] do
    let g ← getMainGoal
    let (_, _, pc) ← getSepWPStateAndPC
    if ← g.withContext (pcReachedTarget pc stop) then
      return n
    match ← tryTacticCatchRuntimeMsg wpStepCoreWithOutcome with
    | .ok _ => n := n + 1
    | .error msg =>
      throwError m!"block_summary: could not step at pc {pc} (after {n} instructions) before \
        reaching {stop}:{indentD msg}"
    let gs ← getGoals
    unless gs.length == 1 do
      throwError m!"block_summary: stepping at pc {pc} left {gs.length} goals; a segment must be \
        straight-line (use `wp_if`/`wp_call` outside the summary)"
  let g ← getMainGoal
  let (_, _, pc) ← getSepWPStateAndPC
  if ← g.withContext (pcReachedTarget pc stop) then
    return n
  throwError m!"block_summary: no state with pc = {stop} within {maxSteps} instructions \
    (set_option proofLib.blockSummary.maxSteps)"

def strayFVars (e : Expr) (allowed : Std.HashSet FVarId) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds.filter (!allowed.contains ·)

/-- Build and add the summary theorem for `BlockSegment prog s P stop` over binders `xs`. -/
def mkSummary (declName : Name) (xs : Array Expr) (T : Expr)
    (tac? : Option (TSyntax ``Parser.Tactic.tacticSeq)) (report : Bool) (ref : Syntax) :
    TermElabM Expr := do
  let T := (← instantiateMVars T).consumeMData
  unless T.isAppOfArity ``BlockSegment 4 do
    throwErrorAt ref m!"block_summary: expected a statement `BlockSegment prog s P stop`, got{indentExpr T}"
  let #[prog, s, P, stop] := T.getAppArgs | unreachable!
  let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let postTy ← mkArrow (mkConst ``Arm64.State) (← mkArrow (mkConst ``Arm64.SepProp) (mkSort 0))
  let oomTy ← mkArrow (mkConst ``Arm64.State) (mkConst ``Arm64.SepProp)
  withLocalDecl `target .implicit bv64 fun target => do
  withLocalDecl `post .implicit postTy fun post => do
  withLocalDecl `oom .implicit oomTy fun oom => do
    let lctx0 ← getLCtx
    let goalTy := mkAppN (mkConst ``SepWP) #[prog, target, s, P, post, oom]
    let g ← mkFreshExprSyntheticOpaqueMVar goalTy
    let maxSteps := proofLib.blockSummary.maxSteps.get (← getOptions)
    let gs ← Tactic.run g.mvarId! do
      match tac? with
      | some tac => evalTactic tac
      | none => discard <| stepTo stop maxSteps
    let r ← match gs with
      | [r] => pure r
      | [] => throwErrorAt ref "block_summary: the run closed the goal; nothing to summarize"
      | _ => throwErrorAt ref m!"block_summary: the run left {gs.length} goals, expected exactly \
          one residual `SepWP` goal:{indentD (MessageData.joinSep (gs.map MessageData.ofGoal) m!"\n")}"
    let (ys, hnextTy) ← r.withContext do
      let rTy := (← instantiateMVars (← r.getType)).consumeMData
      unless rTy.isAppOfArity ``SepWP 6 do
        throwErrorAt ref m!"block_summary: the residual goal is not a `SepWP` judgement:{indentExpr rTy}"
      let pcEnd ← extractSepWPPC (rTy.getArg! 2)
      unless ← pcReachedTarget pcEnd stop do
        throwErrorAt ref m!"block_summary: the run stopped at pc{indentExpr pcEnd}\nnot at{indentExpr stop}"
      -- Inline local `let` bindings and quantify over newly introduced assumptions and variables.
      let rTy ← zetaReduce rTy
      let mut ys := #[]
      for d in ← getLCtx do
        if !d.isAuxDecl && !d.isLet && !lctx0.contains d.fvarId then
          ys := ys.push d.toExpr
      let hnextTy ← instantiateMVars (← mkForallFVars ys rTy)
      if hnextTy.hasExprMVar then
        throwErrorAt ref m!"block_summary: the residual goal contains metavariables:{indentExpr hnextTy}"
      pure (ys, hnextTy)
    let allowed : Std.HashSet FVarId := lctx0.foldl (fun acc d => acc.insert d.fvarId) {}
    unless (strayFVars hnextTy allowed).isEmpty do
      throwErrorAt ref m!"block_summary: the residual goal depends on hypotheses the run removed \
        from the context:{indentExpr hnextTy}"
    withLocalDeclD `hnext hnextTy fun hnext => do
      r.assign (mkAppN hnext ys)
      let pf ← instantiateMVars g
      if pf.hasExprMVar then
        throwErrorAt ref "block_summary: the run left unassigned metavariables in the proof"
      -- Record binders referenced in `pf` in the info tree for the unused-variables linter.
      for x in xs do
        if pf.containsFVar x.fvarId! then
          Term.addTermInfo' ref x
      let vars := xs ++ #[target, post, oom, hnext]
      let type ← instantiateMVars (← mkForallFVars vars goalTy)
      let value ← instantiateMVars (← mkLambdaFVars vars pf)
      let type ← Term.levelMVarToParam type
      let levelParams := (collectLevelParams {} type).params.toList
      addDecl <| .thmDecl { name := declName, levelParams, type, value }
      if report then
        logInfoAt ref m!"{declName} : {type}"
      return type

/-- `block_summary name binders : BlockSegment prog s P stop [using tac]`: symbolically execute
    the straight-line segment of `prog` from state `s` (spatial context `P`) to `pc = stop`, saving
    the continuation-style `SepWP` lemma `name`. Apply with `wp_block name`. -/
syntax (name := blockSummaryCmd) (docComment)? "block_summary " ident (ppSpace bracketedBinder)*
  " : " term (" using " tacticSeq)? : command

/-- `block_summary?`: like `block_summary`, also logging the generated theorem type. -/
syntax (name := blockSummaryCmd?) (docComment)? "block_summary? " ident (ppSpace bracketedBinder)*
  " : " term (" using " tacticSeq)? : command

def elabBlockSummary (doc? : Option (TSyntax ``Parser.Command.docComment)) (id : Ident)
    (binders : Array Syntax) (ty : Term) (tac? : Option (TSyntax ``Parser.Tactic.tacticSeq))
    (report : Bool) (ref : Syntax) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ id.getId
  if (← getEnv).contains declName then
    throwErrorAt id m!"block_summary: '{declName}' has already been declared"
  liftTermElabM do
    Term.elabBinders binders fun xs => do
      let T ← Term.elabType ty
      Term.synthesizeSyntheticMVarsNoPostponing
      discard <| mkSummary declName xs T tac? report ref
  if let some doc := doc? then
    liftTermElabM <| addDocString declName (mkNullNode binders) doc
  addDeclarationRangesFromSyntax declName ref id

-- Match on syntax positions directly: with Mathlib loaded, `$[$doc]? block_summary ...` quotation
-- patterns are parsed as modified declarations and fail to match.
def elabBlockSummaryStx (report : Bool) (stx : Syntax) : CommandElabM Unit := do
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].isNone then none else some ⟨stx[0][0]⟩
  let id : Ident := ⟨stx[2]⟩
  let binders := stx[3].getArgs
  let ty : Term := ⟨stx[5]⟩
  let tac? : Option (TSyntax ``Parser.Tactic.tacticSeq) :=
    if stx[6].isNone then none else some ⟨stx[6][1]⟩
  elabBlockSummary doc? id binders ty tac? report stx

@[command_elab blockSummaryCmd] def elabBlockSummaryCmd : CommandElab := elabBlockSummaryStx false

@[command_elab blockSummaryCmd?] def elabBlockSummaryCmd? : CommandElab := elabBlockSummaryStx true

/-! ## `wp_block` -/

/-- Attempt to close a summary side condition without leaving synthetic sorries on failure.
    Goals containing metavariables are tried only with reducible `assumption`; closed goals are
    also tried with `rfl` and goal-only `simp only [wp_norm, arm64_norm]`. -/
def dischargeSide (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  let ty ← instantiateMVars (← g.getType)
  let saved ← saveState
  -- Match at reducible transparency to avoid `whnf` unfolding large concrete program/table terms.
  if ← (try withReducible g.assumptionCore catch _ => pure false) then return true
  saved.restore
  if ty.hasExprMVar then return false
  for tac in [← `(tactic| with_reducible rfl),
      ← `(tactic| (simp only [wp_norm, arm64_norm]; done)),
      ← `(tactic| (simp only [wp_norm, arm64_norm]; with_reducible assumption)),
      ← `(tactic| (simp only [wp_norm, arm64_norm, *]; done))] do
    try
      let gs ← withoutRecover <| Tactic.run g (evalTactic tac)
      if gs.isEmpty && !(← instantiateMVars (mkMVar g)).hasSyntheticSorry then return true
      saved.restore
    catch _ => saved.restore
  return false

def dischargeSides (sides : Array MVarId) : TacticM (Array MVarId) := do
  let mut open_ := sides
  let mut progress := true
  while progress do
    progress := false
    let mut next := #[]
    for sg in open_ do
      if ← sg.isAssigned then progress := true; continue
      let ty ← instantiateMVars (← sg.getType)
      if ty.hasExprMVar then next := next.push sg
      else if ← dischargeSide sg then progress := true
      else next := next.push sg
    open_ := next
    unless progress do
      -- Try equality goals first so `s.pc = ?base` pins `?base` before matching `prog.hasCode`.
      let mut eqs := #[]
      let mut others := #[]
      for sg in open_ do
        if (← instantiateMVars (← sg.getType)).isEq then eqs := eqs.push sg else others := others.push sg
      let mut later := #[]
      for sg in eqs ++ others do
        if progress then later := later.push sg
        else if ← dischargeSide sg then progress := true
        else later := later.push sg
      open_ := later
  open_.filterM fun m => return !(← m.isAssigned)

private partial def replaceSubexpr (e target replacement : Expr) : Expr :=
  if e == target then replacement
  else match e with
  | .app f a => e.updateApp! (replaceSubexpr f target replacement) (replaceSubexpr a target replacement)
  | .mdata _ b => replaceSubexpr b target replacement
  | _ => e

def wpBlockCore (h : Term) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let gTy := (← instantiateMVars (← g.getType)).consumeMData
    unless gTy.isAppOfArity ``SepWP 6 do
      throwError m!"wp_block: goal is not a `SepWP` judgement:{indentExpr gTy}"
    let hE ← elabTermForApply h (mayPostpone := false)
    let hTy ← inferType hE
    let (hargs, _, concl) ← forallMetaTelescope hTy
    let concl := concl.consumeMData
    unless concl.isAppOfArity ``SepWP 6 && hargs.size ≥ 1 do
      throwError m!"wp_block: {h} is not a block summary (`… → SepWP …`):{indentExpr hTy}"
    let hnext := hargs.back!
    let sides := hargs.pop
    let gArgs := gTy.getAppArgs
    let cArgs := concl.getAppArgs
    for i in [0, 1, 2, 4, 5] do
      unless ← isDefEq cArgs[i]! gArgs[i]! do
        throwError m!"wp_block: cannot unify the summary's conclusion{indentExpr concl}\nwith the \
          goal{indentExpr gTy}"
    -- Discharge side conditions before `sep_frame` to pin register/address binders, then run a
    -- second pass after `sep_frame` for side conditions depending on memory-bound values.
    let mut propSides := #[]
    for side in sides do
      if ← isProp (← inferType side) then propSides := propSides.push side.mvarId!
    propSides ← dischargeSides propSides
    let mut extra : Array MVarId := #[]
    let proof := mkAppN hE hargs
    let mut usedSepFrame := false
    if ← withReducible (isDefEq cArgs[3]! gArgs[3]!) then
      g.assign proof
    else
      usedSepFrame := true
      let eqTy ← instantiateMVars (← mkEq gArgs[3]! cArgs[3]!)
      let eqG ← mkFreshExprSyntheticOpaqueMVar eqTy
      let rest ← try Tactic.run eqG.mvarId! (evalTactic (← `(tactic| sep_frame)))
        catch e => throwError m!"wp_block: the goal's precondition does not contain the summary's \
          precondition (sep_frame failed):{indentD e.toMessageData}"
      unless rest.isEmpty do
        throwError m!"wp_block: sep_frame left goals for{indentExpr eqTy}"
      g.assign (← mkAppM ``SepWP.of_pre_eq #[proof, eqG])
    extra := extra ++ (← dischargeSides propSides)
    for side in sides do
      let side ← instantiateMVars side
      if side.isMVar && !(← isProp (← inferType side)) then
        throwError m!"wp_block: cannot determine the summary argument `{← inferType side}` from the \
          goal or the context; pass it explicitly (e.g. `wp_block {h} (name := …)`)"
    let mut ng' := hnext.mvarId!
    let nTy ← instantiateMVars (← ng'.getType)
    let binderInfos ← forallTelescope nTy fun ys _ =>
      ys.mapM fun y => return (← y.fvarId!.getUserName, ← isProp (← inferType y))
    for (uName, isP) in binderInfos do
      let lctx := (← ng'.getDecl).lctx
      if isP && !uName.hasMacroScopes && (lctx.findFromUserName? uName).isNone then
        let (_, g') ← ng'.intro1P
        ng' := g'
      else
        let (_, g') ← ng'.intro1
        ng' := g'
    -- When framing `Q = A * F` inside `P`, update `A` to `A'` in place to preserve atom order.
    if usedSepFrame then
      ng' ← ng'.withContext do
        let P := (← instantiateMVars gArgs[3]!).consumeMData
        let Q := (← instantiateMVars cArgs[3]!).consumeMData
        let nTy' := (← instantiateMVars (← ng'.getType)).consumeMData
        if nTy'.isAppOfArity ``SepWP 6 && Q.isAppOfArity ``sepConj 2 then
          let nArgs := nTy'.getAppArgs
          let Q' := nArgs[3]!.consumeMData
          let A := Q.getArg! 0
          let F := Q.getArg! 1
          if Q'.isAppOfArity ``sepConj 2 && Q'.getArg! 1 == F then
            let A' := Q'.getArg! 0
            let P' := replaceSubexpr P A A'
            if A == A' || P' != P then
              try
                let eqTy' ← instantiateMVars (← mkEq Q' P')
                let eqG' ← mkFreshExprSyntheticOpaqueMVar eqTy'
                let rest' ← Tactic.run eqG'.mvarId! (evalTactic (← `(tactic| sep_frame)))
                if rest'.isEmpty then
                  let newGoalTy := mkAppN nTy'.getAppFn (nArgs.set! 3 P')
                  let ng'' ← mkFreshExprSyntheticOpaqueMVar newGoalTy (← ng'.getTag)
                  ng'.assign (← mkAppM ``SepWP.of_pre_eq #[ng'', eqG'])
                  return ng''.mvarId!
              catch _ => pure ()
        return ng'
    let rest ← extra.filterM fun m => return !(← m.isAssigned)
    replaceMainGoal (ng' :: rest.toList)

/-- `wp_block h`: apply a continuation-style `SepWP` summary `h` (from `block_summary`), framing
    the precondition via `sep_frame` if needed, discharging side conditions via `assumption`,
    `rfl`, or `simp only [wp_norm, arm64_norm, *]`, and introducing the segment's output facts. -/
syntax (name := wpBlock) "wp_block " term : tactic

elab_rules : tactic
  | `(tactic| wp_block $h) => wpBlockCore h

end ProofLib.BlockSummary
