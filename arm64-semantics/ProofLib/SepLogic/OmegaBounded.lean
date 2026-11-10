/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.Frame
public import ProofLib.BV.Arith
import Arm64.Trusted.Spec.SepLogic

/-!
# Bounded Arithmetic Automation

Pre-filters and bounds arithmetic side goals handed to `omega` and `bv_omega` by the `wp_*` and
`sep_*` automation. Because `omega`'s core solver loop does not poll `checkSystem`, heartbeat caps
cannot interrupt an in-flight call; `proveOmegaBounded?` and `wp_omega_bounded` therefore prune the
local context into relevance tiers (`omegaPruneGoal`), drop `BitVec` wrap-around comparisons or skip
oversized `Nat`-subtraction goals (`omegaWrapFilter?`), and execute each attempt under
`withHeartbeatCap`, `tryTacticCatchRuntime`, and `runTacClosed`.
-/

namespace ProofLib

open Arm64
open Lean Elab Tactic Meta

public meta section

/-! ## Capped, runtime-guarded tactic runs -/

/-- Run `tac` catching both ordinary tactic exceptions and runtime exceptions (`maxRecDepth`,
    heartbeat timeouts), restoring tactic state and message log on failure. -/
def tryTacticCatchRuntime {α : Type} (tac : TacticM α) : TacticM (Option α) := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  try
    MonadRuntimeException.tryCatchRuntimeEx
      (do
        let res ← withoutRecover tac
        return some res)
      (fun _ => do
        restoreState saved
        Core.setMessageLog savedMsgs
        return none)
  catch _ =>
    restoreState saved
    Core.setMessageLog savedMsgs
    return none

/-- Boolean variant of `tryTacticCatchRuntime`. -/
def tryTacticCatchRuntimeBool (tac : TacticM Unit) : TacticM Bool := do
  return (← tryTacticCatchRuntime tac).isSome

/-- Run `tac` with a capped heartbeat budget (`maxOptHeartbeats` in units of 1000 raw heartbeats,
    matching Lean's `maxHeartbeats` option where 200000 is the default), never exceeding the
    enclosing `Core.Context.maxHeartbeats` limit. -/
def withHeartbeatCap {α : Type} (maxOptHeartbeats : Nat) (tac : TacticM α) : TacticM α := do
  let rawCap := maxOptHeartbeats * 1000
  withTheReader Core.Context (fun ctx =>
    let effMax := if ctx.maxHeartbeats == 0 then rawCap else Nat.min ctx.maxHeartbeats rawCap
    { ctx with maxHeartbeats := effMax }) do
    withCurrHeartbeats tac

/-- Run `tac` on the isolated goal `g` with error recovery disabled, and throw unless it closes
    `g` with a `sorry`-free proof. `Tactic.run` starts a fresh tactic context (error recovery on),
    in which a failing tactic, e.g. the last alternative of `first | ... | omega`, logs its error and
    admits the goal instead of failing. -/
def runTacClosed (g : MVarId) (tac : Syntax) : TacticM Unit := do
  let gs ← Tactic.run g (withoutRecover (evalTactic tac))
  unless gs.isEmpty do throwError "runTacClosed: {gs.length} goal(s) remain"
  if (← instantiateMVars (mkMVar g)).hasSorry then
    throwError "runTacClosed: proof contains sorry"

/-- `runTacClosed g tac` under `withHeartbeatCap cap`, runtime-guarded (`tryTacticCatchRuntime`):
    `true` iff `tac` closed `g`; on failure, state and messages are restored. -/
def runTacCapped (g : MVarId) (tac : Syntax) (cap : Nat) : TacticM Bool :=
  tryTacticCatchRuntimeBool <| withHeartbeatCap cap (runTacClosed g tac)

/-! ## Context pruning -/

/-- `e` with projections of constructor applications reduced (`(a, b).2` to `b`), so that
    relevance pruning sees the components as atoms (`omega`'s preprocessing reduces them too). -/
def omegaReduceCtorProjs (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun t => do
    let .const n _ := t.getAppFn | return .done t
    let some info := env.getProjectionFnInfo? n | return .done t
    let args := t.getAppArgs
    if args.size ≤ info.numParams then return .done t
    let major := args[info.numParams]!.consumeMData
    let .const c _ := major.getAppFn | return .done t
    if c != info.ctorName then return .done t
    let some (.ctorInfo ci) := env.find? c | return .done t
    if major.getAppNumArgs != ci.numParams + ci.numFields then return .done t
    return .visit (mkAppN (major.getArg! (ci.numParams + info.i)) (args.extract (info.numParams + 1))))

/-- Relevance atoms of `e` for `omega` pruning: `ProofLib.BV.Arith.collectAtoms` (maximal
    non-arithmetic subterms: locals, register reads, `bs.length`, ...), looking through
    non-dependent implications (which `omega` splits), defined `Prop` predicates (e.g.
    `@[wp_bv_omega]` abbreviations like `SmallLen n.toNat`), and projections of constructor
    applications (`omegaReduceCtorProjs`), and adding the atoms of the value of every `let`-bound
    local that occurs (its definition is visible to `omega`). -/
partial def omegaRelAtoms (e : Expr) : MetaM (Std.HashSet Expr) := do
  let rec go (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
    let e := e.consumeMData
    match e with
    | .forallE _ d b _ =>
      if b.hasLooseBVars then ProofLib.BV.Arith.collectAtoms e acc else go b (go d acc)
    | .app .. =>
      match e.getAppFn with
      | .const n _ =>
        if n == ``Not && e.getAppNumArgs == 1 then
          go (e.getArg! 0) acc
        else if (n == ``And || n == ``Or || n == ``Iff) && e.getAppNumArgs == 2 then
          go (e.getArg! 1) (go (e.getArg! 0) acc)
        else if ProofLib.BV.Arith.arithHeads.contains n then
          ProofLib.BV.Arith.collectAtoms e acc
        else
          e.getAppArgs.foldl (fun acc a => ProofLib.BV.Arith.collectAtoms a acc) acc
      | _ => ProofLib.BV.Arith.collectAtoms e acc
    | _ => ProofLib.BV.Arith.collectAtoms e acc
  let mut acc := go (← omegaReduceCtorProjs (← instantiateMVars e)) {}
  let mut work := acc.toArray
  let mut seen : Std.HashSet FVarId := {}
  while h : work.size > 0 do
    let a := work[work.size - 1]
    work := work.pop
    for fv in (collectFVars {} a).fvarIds do
      if seen.contains fv then continue
      seen := seen.insert fv
      let some decl := (← getLCtx).find? fv | continue
      let some v := decl.value? | continue
      for b in (ProofLib.BV.Arith.collectAtoms (← omegaReduceCtorProjs (← instantiateMVars v)) {}).toList do
        unless acc.contains b do
          acc := acc.insert b
          work := work.push b
  return acc

/-- Number of distinct `Nat` subtractions in `e`. `omega` splits each one (`a ≤ b` or not) when
    the problem is not solved without the split, so a failing attempt explores up to `2^k` cases;
    callers use this to skip speculative attempts on large problems. -/
def natSubCount (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut work := #[e]
  while h : work.size > 0 do
    let t := work[work.size - 1]
    work := work.pop
    if !t.hasFVar && !t.hasMVar then continue
    if t.isAppOfArity ``HSub.hSub 6 && (t.getArg! 0).consumeMData.isConstOf ``Nat then
      seen := seen.insert t
    match t with
    | .app f a => work := (work.push f).push a
    | .lam _ d b _ | .forallE _ d b _ => work := (work.push d).push b
    | .letE _ ty v b _ => work := ((work.push ty).push v).push b
    | .mdata _ b | .proj _ _ b => work := work.push b
    | _ => pure ()
  return seen.size

/-- Hypotheses to clear before any `omega`-family attempt: machine-state / memory /
    separation-logic hypotheses (unless `keepHeavy`) and non-numeric or heavy `let`-bindings.
    Returns `(toClear, candidates)`, the candidates being the remaining `Prop` hypotheses. -/
def omegaBaseClear (keepHeavy : Bool) : MetaM (Array FVarId × Array (FVarId × Expr)) := do
  let mut toClear : Array FVarId := #[]
  let mut cands : Array (FVarId × Expr) := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    let heavyVal := match decl.value? with
      | some v => isHeavyHypType v
      | none => false
    if decl.isLet && ((!ty.isAppOf ``BitVec && !ty.isConstOf ``Nat) || heavyVal) then
      toClear := toClear.push decl.fvarId
    else if ← Meta.isProp ty then
      if isHeavyHypType ty && !keepHeavy then toClear := toClear.push decl.fvarId
      else cands := cands.push (decl.fvarId, ty)
  return (toClear, cands)

/-- Pruning tiers of `omegaPruneGoal`, from the smallest context to the largest. -/
inductive OmegaTier where
  /-- No `Prop` hypotheses at all: the goal must hold on its own. -/
  | goalOnly
  /-- Hypotheses all of whose relevance atoms occur in the goal. -/
  | strict
  /-- Hypotheses connected to the goal's atoms through shared atoms (transitively), minus
      dangling definitions and equations that only define an unused atom. -/
  | transitive
  /-- As `transitive`, but machine-state hypotheses (e.g. `s.mem.read64 p = 8#64`) are
      relevance candidates too, so those connected to the goal survive. -/
  | heavy
  deriving BEq, Repr

/-- Prune the local context of `g` before a speculative `omega`-family attempt (see
    `OmegaTier`). Step 1 (all tiers) clears machine-state / memory / separation-logic hypotheses
    (except at `heavy`) and non-numeric `let`-bindings (`omegaBaseClear`). Step 2 keeps only the
    `Prop` hypotheses the tier allows; atom-free hypotheses are kept (except at `goalOnly`), and a
    goal without atoms (`False`, closed propositions) keeps every hypothesis that survives step 1.
    Hypotheses outside the goal's cone cannot help `omega` except through a contradiction of their
    own, and each one can add `% 2^64` atoms and case splits that make a failing attempt run for
    minutes without checking heartbeats. -/
def omegaPruneGoal (g : MVarId) (tier : OmegaTier) : MetaM MVarId := g.withContext do
  let goalTy ← instantiateMVars (← g.getType)
  let (toClear0, cands) ← omegaBaseClear (keepHeavy := tier == .heavy)
  let mut toClear := toClear0
  if tier == .goalOnly then
    return ← g.tryClearMany (toClear ++ cands.map (·.1))
  let seed ← omegaRelAtoms goalTy
  if !seed.isEmpty then
    let atomsOf ← cands.mapM fun (_, ty) => omegaRelAtoms ty
    let kept : Array FVarId ←
      if tier == .strict then
        pure <| (cands.zip atomsOf).filterMap fun ((fv, _), as) =>
          if as.toList.all seed.contains then some fv else none
      else
        -- transitive closure over shared atoms (`ProofLib.BV.Arith.relevantFilter`, on
        -- `omegaRelAtoms` instead of `collectAtoms`)
        let mut atoms := seed
        let mut keep := atomsOf.map (·.isEmpty)
        let mut changed := true
        while changed do
          changed := false
          for i in [:cands.size] do
            if !keep[i]! && atomsOf[i]!.toList.any atoms.contains then
              keep := keep.set! i true
              for a in atomsOf[i]!.toList do atoms := atoms.insert a
              changed := true
        let rel := (cands.zip keep).filterMap fun (c, k) => if k then some c else none
        pure <| (ProofLib.BV.Arith.pruneDangling seed rel).map (·.1)
    for (fv, _) in cands do
      unless kept.contains fv do toClear := toClear.push fv
  let g' ← g.tryClearMany toClear
  if tier == .strict then return g'
  g'.tryClearMany (← omegaDefinitionalHyps g')

/-- `natSubCount` of the goal and the `Prop` hypotheses of `g`. -/
def omegaGoalNatSubs (g : MVarId) : MetaM Nat := g.withContext do
  let mut e ← instantiateMVars (← g.getType)
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if ← Meta.isProp ty then e := mkApp e ty
  return natSubCount e

/-- Does `e` contain a `BitVec` order comparison (`ult` / `ule` / `slt` / `sle`, or `<` / `≤` at a
    `BitVec` type) with a non-atomic operand containing a local (e.g. `(x + y).ule z`)? Under
    `bv_omega` each such operand becomes a `% 2^w` wrap-around term, and the comparison a
    disjunction over the wrap cases. -/
def hasBvWrapCmp (e : Expr) : Bool :=
  let isArithOperand (a : Expr) : Bool :=
    let a := a.consumeMData
    a.isApp && a.hasFVar && ProofLib.BV.Arith.arithHeads.contains a.getAppFn.constName
  let isWrapCmp (t : Expr) : Bool :=
    let isCmp :=
      t.isAppOfArity ``BitVec.ult 3 || t.isAppOfArity ``BitVec.ule 3 ||
      t.isAppOfArity ``BitVec.slt 3 || t.isAppOfArity ``BitVec.sle 3 ||
      ((t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``LE.le 4) &&
        (t.getArg! 0).consumeMData.isAppOf ``BitVec)
    let n := t.getAppNumArgs
    isCmp && n ≥ 2 && (isArithOperand (t.getArg! (n - 2)) || isArithOperand (t.getArg! (n - 1)))
  (e.find? isWrapCmp).isSome

/-- Is `ty` a `BitVec` equality `lhs = rhs` without `Nat` subtractions whose two sides are both
    non-atomic arithmetic expressions containing a local (e.g.
    `base + BitVec.ofNat 64 o + BitVec.ofNat 64 a = base + BitVec.ofNat 64 (o + a)`)? When the
    goal has `Nat` subtractions, keeping such an identity adds multiple `% 2^w` quotient variables
    whose wrap cases multiply with the subtraction splits in `bv_omega`. -/
def isBvWrapEq (ty : Expr) : Bool :=
  let isArithOperand (a : Expr) : Bool :=
    let a := a.consumeMData
    a.isApp && a.hasFVar && ProofLib.BV.Arith.arithHeads.contains a.getAppFn.constName
  if natSubCount ty > 0 then false
  else match ty.consumeMData.eq? with
    | some (eqTy, lhs, rhs) =>
      eqTy.consumeMData.isAppOf ``BitVec && isArithOperand lhs && isArithOperand rhs
    | none => false

/-- Number of distinct `BitVec` sums, differences and products containing a local, plus
    `BitVec.ofNat w n` with a non-literal `n`, in `e`. Under `bv_omega` each one becomes a
    `% 2^w` term, i.e. a fresh quotient variable for `omega` to eliminate. -/
def bvModTermCount (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut work := #[e]
  while h : work.size > 0 do
    let t := work[work.size - 1]
    work := work.pop
    if !t.hasFVar then continue
    let isModTerm :=
      ((t.isAppOfArity ``HAdd.hAdd 6 || t.isAppOfArity ``HSub.hSub 6 ||
          t.isAppOfArity ``HMul.hMul 6) && (t.getArg! 0).consumeMData.isAppOf ``BitVec) ||
        (t.isAppOfArity ``BitVec.ofNat 2 && (t.getArg! 1).hasFVar)
    if isModTerm then seen := seen.insert t
    match t with
    | .app f a => work := (work.push f).push a
    | .lam _ d b _ | .forallE _ d b _ => work := (work.push d).push b
    | .letE _ ty v b _ => work := ((work.push ty).push v).push b
    | .mdata _ b | .proj _ _ b => work := work.push b
    | _ => pure ()
  return seen.size

/-- The goal of `g` applied to its `Prop` hypotheses: one expression for the size measures. -/
def omegaProblemExpr (g : MVarId) : MetaM Expr := g.withContext do
  let mut e ← instantiateMVars (← g.getType)
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if ← Meta.isProp ty then e := mkApp e ty
  return e

/-- Size budget of an `omega`-family problem with `Nat` subtractions: `2^k * t` for `k` `Nat`
    subtractions (`natSubCount`) and `t` wrap-around terms (`bvModTermCount`). -/
def omegaWrapBudget : Nat := 96

/-- Size filter applied to every pruned problem before an `omega`-family attempt (no heartbeat cap
    interrupts `omega`, see the module docstring). Problems without `Nat` subtractions pass
    unchanged. Otherwise, hypotheses with a `BitVec` wrap-around comparison (`hasBvWrapCmp`) or
    (when the goal itself has `Nat` subtractions) a compound `BitVec` wrap-around equality without
    `Nat` subtractions (`isBvWrapEq`) are cleared (their wrap cases multiply with the subtraction
    splits; such facts are not needed for a subtraction-offset equation), and the problem is skipped
    (`none`) when `2^k * t` (see `omegaWrapBudget`) still exceeds the budget. -/
def omegaWrapFilter? (g : MVarId) : MetaM (Option MVarId) := do
  let e ← omegaProblemExpr g
  if natSubCount e == 0 then return some g
  let goalHasNatSub ← g.withContext do return natSubCount (← instantiateMVars (← g.getType)) != 0
  let g ← g.withContext do
    let mut ids := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail || decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      if (← Meta.isProp ty) && (hasBvWrapCmp ty || (goalHasNatSub && isBvWrapEq ty)) then
        ids := ids.push decl.fvarId
    if ids.isEmpty then pure g else g.tryClearMany ids
  let e ← omegaProblemExpr g
  let k := natSubCount e
  if k > 0 && 2 ^ k * bvModTermCount e > omegaWrapBudget then return none
  return some g

/-- Largest `natSubCount` of a pruned problem that `proveOmegaBounded?` hands to the omega family
    beyond the `goalOnly` / `strict` tiers (each `Nat` subtraction can double the work of a failing
    attempt, and `omega` does not check heartbeats while it splits). -/
def omegaMaxNatSubs : Nat := 6

/-- Default heartbeat budget (thousands) of one `proveOmegaBounded?` attempt. -/
def omegaAttemptCap : Nat := 20000

/-- `bv_omega`, after rewriting `BitVec.ult` / `ule` facts to `toNat` comparisons. -/
def bvOmegaUltTac : MetaM Syntax := `(tactic| (
  try simp only [bitvec_ult_eq_true_to_nat, bitvec_ule_eq_true_to_nat,
                 bitvec_ult_eq_false_to_nat, bitvec_ule_eq_false_to_nat] at *
  bv_omega))

/-- Default tactic list of `proveOmegaBounded?`: `bv_omega` (with `ult`/`ule` rewriting), then
    plain `omega`. -/
def omegaDefaultTacs : MetaM (List Syntax) := do
  return [← bvOmegaUltTac, ← `(tactic| omega)]

/-- Bounded proof of the goal `g` (left unassigned on failure) by the omega family: for each
    tier in `tiers` (default: every `OmegaTier`, smallest context first), prune a fresh copy of
    `g` (`omegaPruneGoal`), filter it (`omegaWrapFilter?`), skip it if the filter rejects it, if it
    keeps the same hypotheses as the previous tier, or if (beyond `strict`) it has more than
    `omegaMaxNatSubs` `Nat` subtractions, and try each tactic of `tacs` under `cap` heartbeats
    (`runTacCapped`). The whole local context is never handed to `omega`. Returns `true` iff `g`
    was closed. -/
def proveOmegaBounded? (g : MVarId) (tacs : List Syntax)
    (tiers : List OmegaTier := [.goalOnly, .strict, .transitive, .heavy])
    (cap : Nat := omegaAttemptCap) : TacticM Bool := g.withContext do
  let mut prevHyps : Option (Array FVarId) := none
  for tier in tiers do
    let m ← mkFreshExprMVar (← g.getType)
    let some m' ← omegaWrapFilter? (← omegaPruneGoal m.mvarId! tier) | continue
    let hyps ← m'.withContext do return (← getLCtx).getFVarIds
    if prevHyps == some hyps then continue
    prevHyps := some hyps
    if tier != .goalOnly && tier != .strict && (← omegaGoalNatSubs m') > omegaMaxNatSubs then
      continue
    for tac in tacs do
      if ← runTacCapped m' tac cap then
        g.assign (← instantiateMVars m)
        return true
  return false

/-- `proveOmegaBounded?` on a fresh goal of type `ty` (in the current context); the proof on
    success. -/
def proveOmegaBoundedTerm? (ty : Expr) (tacs : List Syntax)
    (tiers : List OmegaTier := [.goalOnly, .strict, .transitive, .heavy])
    (cap : Nat := omegaAttemptCap) : TacticM (Option Expr) := do
  let m ← mkFreshExprMVar ty
  if ← proveOmegaBounded? m.mvarId! tacs tiers cap then return some (← instantiateMVars m)
  return none

/-- Bounded `bv_omega` / `omega` closer used by `wp_done`, `wp_call`, `wp_sep`, branch
    simplification, loop invariants, and `sep_entail`. Runs `proveOmegaBounded?` with
    `omegaDefaultTacs`: each attempt sees a pruned context, is capped at `omegaAttemptCap`
    heartbeats (or the enclosing budget, if smaller), and catches runtime exceptions so an
    intractable goal fails with an ordinary tactic error that `first | ...` can recover from. -/
elab "wp_omega_bounded" : tactic => do
  let g ← getMainGoal
  if ← proveOmegaBounded? g (← omegaDefaultTacs) then
    replaceMainGoal []
  else
    let lazyHint := MessageData.lazy fun ppCtx => do
      let checkMod : MetaM Bool := g.withContext do
        let m ← mkFreshExprMVar (← g.getType)
        let m' ← omegaPruneGoal m.mvarId! .strict
        let e ← omegaProblemExpr m'
        return bvModTermCount e != 0
      let res? ← (ppCtx.runMetaM checkMod).toBaseIO
      match res? with
      | .ok true =>
        return m!"\nhint: goal or context has modular BitVec arithmetic (2^64 wraparound); supply an overflow bound (or rewrite with BitVec.toNat_add_of_lt / BitVec.toNat_sub_of_le), or use bv_lin / bv_arith"
      | _ =>
        return m!""
    throwError "wp_omega_bounded: bv_omega / omega failed on every pruned context{lazyHint}"

end

end ProofLib
