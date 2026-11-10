/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import ProofLib.MaxRecDepthDiag
public meta import Arm64.Trusted.ISA.Syntax
public meta import Arm64.Trusted.ISA.Decode
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.Hoare.SubroutineOk
public import ProofLib.VCGen
public meta import ProofLib.SpecShape
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.CondClassify
public import ProofLib.BV.Arith
public import ProofLib.BV.ReflectROBDD
public import ProofLib.SepLogic.WP.StateNorm
public import ProofLib.SepLogic.WP.Access
public import ProofLib.SepLogic.WP.StepsCore
public import ProofLib.SepLogic.WP.StepsSimd
public import ProofLib.SepLogic.WP.StepsSubword
public import ProofLib.SepLogic.WP.Structural
public import ProofLib.SepLogic.WP.StateTransport
public import ProofLib.SepLogic.WP.TacticCore
public import ProofLib.SepLogic.WP.StepTactic
public import ProofLib.SepLogic.FrameInfer
public meta import ProofLib.SepLogic.CodeLookup

/-!
# Control-Flow and Completion Tactics

Interactive straight-line stepping (`wp_steps`), subroutine and tail-call discharge (`wp_call`,
`wpp_call`, `wp_tailcall`), branch and loop combinators (`wp_if`, `wp_cases`, `wp_loop`), and
goal completion (`wp_done`, `wp_auto`, `wp_compact`) for `SepWP` and `SepWPp`.
-/

namespace ProofLib

open Arm64
open Lean Elab Tactic Meta

public meta section

register_option proofLib.wpCallAutoStep : Bool := {
  defValue := true
  descr := "In `wp_call`, when the current PC precedes the callee entry, try a bounded straight-line `wp_steps` (or stepping a `BL` instruction) to reach the call target before failing."
}

register_option proofLib.wpCallRegistry : Bool := {
  defValue := true
  descr := "Resolve `wp_call` contracts from local `subroutine_ok` hypotheses and `@[callee_spec]`-registered theorems when called with no argument, and suggest matching contracts on PC mismatch."
}

register_option proofLib.wpDoneAutoDisjAndCalleeSaved : Bool := {
  defValue := true
  descr := "In `wp_done`, automatically select the PC-matching arm of an `Or` goal and destructure local `*CalleeSaved*` / `calleeSavedVRegs` hypotheses."
}

register_option proofLib.wpDoneAllowResidualGoals : Bool := {
  defValue := false
  descr := "Allow `wp_done` to leave residual or unfocused subgoals open instead of throwing a structured diagnostic error."
}

register_option proofLib.wpBranchAutoDecide : Bool := {
  defValue := true
  descr := "Before throwing an unresolved conditional branch error in `wp_call`, `wp_done`, or loop tactics, try a bounded arithmetic/BitVec decision on the branch condition."
}

register_option proofLib.wpCallAutoSpAlign : Bool := {
  defValue := true
  descr := "In `wp_call`, discharge 16-byte stack pointer alignment from local `s.sp = s0.sp ± k#64` (or `s.readReg64 .sp`) and `s0.spAligned = true` hypotheses."
}

/-- Scoped environment extension storing `@[callee_spec]` theorem names for `wp_call`. -/
initialize calleeSpecExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun arr nm => if arr.contains nm then arr else arr.push nm
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `callee_spec
  descr := "Register a `subroutine_ok` / `Program.subroutineOk` contract for automatic lookup by `wp_call`."
  applicationTime := .afterTypeChecking
  add := fun declName _stx kind => do
    calleeSpecExt.add declName kind
}

/-- Check whether `pcExpr` equals `targetPcExpr` without unfolding symbolic `HAdd.hAdd` (`base + off#64`)
    into unary `Nat.add` under default transparency. -/
def pcReachedTarget (pcExpr targetPcExpr : Expr) : MetaM Bool := do
  if pcExpr == targetPcExpr then return true
  if pcExpr.hasMVar || targetPcExpr.hasMVar then return false
  if let (some (w1, v1), some (w2, v2)) := (evalBitVecLitPure? pcExpr, evalBitVecLitPure? targetPcExpr) then
    if w1 == w2 then return v1 == v2
  if pcExpr.isAppOfArity ``HAdd.hAdd 6 || pcExpr.isAppOfArity ``HSub.hSub 6 ||
     targetPcExpr.isAppOfArity ``HAdd.hAdd 6 || targetPcExpr.isAppOfArity ``HSub.hSub 6 then
    let (b1, o1) ← sepAddrBaseOff pcExpr
    let (b2, o2) ← sepAddrBaseOff targetPcExpr
    if o1 == o2 && (b1 == b2 || (← withReducible (isDefEq b1 b2))) then
      return true
  if ← withReducible (isDefEq pcExpr targetPcExpr) then return true
  if pcExpr.isAppOfArity ``HAdd.hAdd 6 || pcExpr.isAppOfArity ``HSub.hSub 6 ||
     targetPcExpr.isAppOfArity ``HAdd.hAdd 6 || targetPcExpr.isAppOfArity ``HSub.hSub 6 then
    return false
  withReducibleAndInstances (isDefEq pcExpr targetPcExpr)

private partial def collectTableOffsetsCore (tbl : Expr) : MetaM (Array Nat) := do
  let tblWhnf ← whnf tbl
  if tblWhnf.isAppOfArity ``List.nil 1 then
    return #[]
  if tblWhnf.isAppOfArity ``List.cons 3 then
    let head ← whnf (tblWhnf.getArg! 1)
    let tail := tblWhnf.getArg! 2
    let mut rest ← collectTableOffsetsCore tail
    if head.isAppOfArity ``Prod.mk 4 then
      let offExpr ← whnf (head.getArg! 3)
      if let some n := offExpr.rawNatLit? then
        rest := rest.push n
      else if let some n ← evalNatLit? offExpr then
        rest := rest.push n
    return rest
  return #[]

register_option proofLib.tableOffsetsMemo : Bool := {
  defValue := true
  descr := "memoize the symbol/stub table offsets that `wp_sym_steps` / `wp_steps` collect \
    for function-boundary detection, for closed tables built from imported constants"
}

/-- Process-wide memo of `collectTableOffsetsCore` results. Only closed tables (no free or
    metavariables) whose constants all come from imported modules, collected at default
    transparency, are recorded: such a table and every definition it unfolds through are fixed
    for the lifetime of the process, so the collected offsets cannot change. The result only
    feeds the function-boundary heuristic, never a proof term. -/
initialize tableOffsetsMemoRef : IO.Ref (Std.HashMap Expr (Array Nat)) ← IO.mkRef {}

def collectTableOffsets (tbl : Expr) : MetaM (Array Nat) := do
  if !proofLib.tableOffsetsMemo.get (← getOptions) || tbl.hasFVar || tbl.hasMVar ||
      (← getTransparency) != .default then
    return ← collectTableOffsetsCore tbl
  if let some offs := (← tableOffsetsMemoRef.get).get? tbl then
    return offs
  let offs ← collectTableOffsetsCore tbl
  let env ← getEnv
  if tbl.getUsedConstants.all (env.getModuleIdxFor? · |>.isSome) then
    tableOffsetsMemoRef.modify (·.insert tbl offs)
  return offs

/-- Precomputed function-entry boundary information for a `wpStepsCore` loop so `LCtx` and
    ELF symbol/stub tables are not re-scanned on every instruction step. -/
structure WpStepsBoundaryCache where
  currNorms : Array Expr
  otherCandNorms : Array Expr
  tableOffs : Array Nat
  bBase : Expr
  oBase : Nat

def buildWpStepsBoundaryCache (progExpr : Expr) : TacticM WpStepsBoundaryCache := do
  let g ← getMainGoal
  g.withContext do
    let mut currNorms : Array Expr := #[]
    let addUniqueNorm (arr : Array Expr) (e : Expr) : MetaM (Array Expr) := do
      let (cn, _) ← SepSolver.normAddrMeta e
      for existing in arr do
        if cn == existing || (← withReducibleAndInstances (isDefEq cn existing)) then
          return arr
      return arr.push cn
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOfArity ``State.pc 1 && (lhs.getArg! 0).isFVar then
            currNorms ← addUniqueNorm currNorms rhs
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOfArity ``Program.fnAddr 2 then
            let (lhsNorm, _) ← SepSolver.normAddrMeta lhs
            let mut matchesCurr := false
            for cn in currNorms do
              if lhsNorm == cn || (← withReducibleAndInstances (isDefEq lhsNorm cn)) then
                matchesCurr := true
                break
            if matchesCurr then
              currNorms ← addUniqueNorm currNorms rhs
          if lhs.isAppOfArity ``Program.fnOff 2 then
            let fnAddrExpr := mkApp2 (mkConst ``Program.fnAddr) (lhs.getArg! 0) (lhs.getArg! 1)
            let (fnAddrNorm, _) ← SepSolver.normAddrMeta fnAddrExpr
            let mut matchesCurr := false
            for cn in currNorms do
              if fnAddrNorm == cn || (← withReducibleAndInstances (isDefEq fnAddrNorm cn)) then
                matchesCurr := true
                break
            if matchesCurr then
              if let some offNat ← evalNatLit? rhs then
                let candEntry ← mkAppM ``HAdd.hAdd #[mkApp (mkConst ``Program.base) progExpr, toExpr (BitVec.ofNat 64 offNat)]
                currNorms ← addUniqueNorm currNorms candEntry
    let isNotCurr (candNorm : Expr) : MetaM Bool := do
      for cn in currNorms do
        if candNorm == cn || (← withReducibleAndInstances (isDefEq candNorm cn)) then
          return false
      return true
    let mut otherCandNorms : Array Expr := #[]
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        -- Entry address of another function's contract / code hypothesis (binders looked up by
        -- name so a signature change cannot silently drop the hypothesis)
        let candEntry? : Option Expr ←
          if ← SpecShape.isFullApp? ty ``Arm64.subroutine_ok then
            SpecShape.namedArg? ty ``Arm64.subroutine_ok `entry_pc
          else if ← SpecShape.isFullApp? ty ``Program.subroutineOk then
            pure (some (mkApp2 (mkConst ``Program.fnAddr)
              (← SpecShape.namedArg! ty ``Program.subroutineOk `prog)
              (← SpecShape.namedArg! ty ``Program.subroutineOk `fnName)))
          else if ty.isAppOfArity ``Program.hasCode 3 || ty.isAppOfArity ``Program.hasWords 3 then
            pure (some (ty.getArg! 1))
          else
            pure none
        if let some candEntry := candEntry? then
          let (candNorm, _) ← SepSolver.normAddrMeta candEntry
          if ← isNotCurr candNorm then
            otherCandNorms ← addUniqueNorm otherCandNorms candNorm
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOfArity ``Program.fnAddr 2 then
            let (candNorm, _) ← SepSolver.normAddrMeta rhs
            if ← isNotCurr candNorm then
              otherCandNorms ← addUniqueNorm otherCandNorms candNorm
          if lhs.isAppOfArity ``Program.fnOff 2 then
            if let some offNat ← evalNatLit? rhs then
              let candEntry ← mkAppM ``HAdd.hAdd #[mkApp (mkConst ``Program.base) progExpr, toExpr (BitVec.ofNat 64 offNat)]
              let (candNorm, _) ← SepSolver.normAddrMeta candEntry
              if ← isNotCurr candNorm then
                otherCandNorms ← addUniqueNorm otherCandNorms candNorm
    let mut tableOffs : Array Nat := #[]
    let mut bBase : Expr := toExpr (0#64)
    let mut oBase : Nat := 0
    let progUnwrapped ← unwrapRebasedProgExpr progExpr
    if let some (syms, stubs) ← extractProgTables? progUnwrapped then
      tableOffs := (← collectTableOffsets syms) ++ (← collectTableOffsets stubs)
      if !tableOffs.isEmpty then
        let progBase ← whnf (mkApp (mkConst ``Program.base) progUnwrapped)
        let (bb, ob) ← sepAddrBaseOff progBase
        bBase := bb
        oBase := ob
    return { currNorms, otherCandNorms, tableOffs, bBase, oBase }

def isOtherFunctionEntryCached (bc : WpStepsBoundaryCache) (targetPcExpr pcExpr : Expr)
    (afterUncondB : Bool) : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    if ← pcReachedTarget pcExpr targetPcExpr then
      return false
    let (pcNorm, _) ← SepSolver.normAddrMeta pcExpr
    for cn in bc.currNorms do
      if pcNorm == cn || (← withReducibleAndInstances (isDefEq pcNorm cn)) then
        return false
    let (bPc, oPc) ← sepAddrBaseOff pcNorm
    for candNorm in bc.otherCandNorms do
      if pcNorm == candNorm || (← withReducibleAndInstances (isDefEq pcNorm candNorm)) then
        return true
    if bPc.isAppOfArity ``Program.fnAddr 2 && oPc == 0 then
      return true
    if !bc.tableOffs.isEmpty then
      if bPc == bc.bBase || (← withReducibleAndInstances (isDefEq bPc bc.bBase)) then
        let relOff := (oPc + 2 ^ 64 - bc.oBase) % (2 ^ 64)
        if bc.tableOffs.contains relOff then
          return true
    if afterUncondB then
      let zero64 := toExpr (0#64)
      if !bc.currNorms.isEmpty && bPc != zero64 && !(← withReducibleAndInstances (isDefEq bPc zero64)) then
        let mut allDifferent := true
        for cn in bc.currNorms do
          let (bCurr, _) ← sepAddrBaseOff cn
          if bCurr == zero64 || (← withReducibleAndInstances (isDefEq bCurr zero64)) ||
             bPc == bCurr || (← withReducibleAndInstances (isDefEq bPc bCurr)) then
            allDifferent := false
            break
        if allDifferent then
          return true
    return false

inductive WpIteTargetStop where
  /-- The PC is not an `ite` with an arm at the target: step normally. -/
  | notApplicable
  /-- The condition was decided towards the target arm; the goal's PC is now the target. -/
  | stopped
  /-- An arm is the target but the condition is undetermined by the context. -/
  | unresolved
  /-- The condition was decided towards the non-target arm: step normally. -/
  | otherArm
  deriving BEq, Inhabited

/-- If the goal's PC `pcExpr` is `if c then t else e` (left by a conditional branch) where `t` or
    `e` is the `SepWP` target PC `targetPcExpr`, decide `c` from the context and, when the decided
    arm is the target, select it with the decided condition as hypothesis `hcond`. Step loops call
    this before taking a step so that a conditional back-edge to a loop header stops at the header
    instead of resolving the branch and executing the header instruction. -/
def wpStopAtResolvedIteTarget (pcExpr targetPcExpr : Expr)
    (stepFailed : Option (IO.Ref (Array Expr)) := none) : TacticM WpIteTargetStop := do
  unless pcExpr.isAppOfArity ``ite 5 do return .notApplicable
  let g ← getMainGoal
  let (thenHit, elseHit) ← g.withContext do
    return (← pcReachedTarget (pcExpr.getArg! 3) targetPcExpr,
      ← pcReachedTarget (pcExpr.getArg! 4) targetPcExpr)
  unless thenHit || elseHit do return .notApplicable
  let some (condTrue, propTy, prf) ← resolveIteCondStep? (pcExpr.getArg! 1) stepFailed
    | return .unresolved
  unless (condTrue && thenHit) || (!condTrue && elseHit) do return .otherArm
  let saved ← saveState
  let ok ← tryTacticCatchRuntimeBool do
    if condTrue then
      evalTactic (← `(tactic| (apply SepWP.ite_true; wp_focus_close wp_norm_lhs)))
    else
      evalTactic (← `(tactic| (apply SepWP.ite_false; wp_focus_close wp_norm_lhs)))
    let gCond :: gsRest ← getGoals | throwError "expected condition subgoal"
    let typeOk ← gCond.withContext do isDefEq (← inferType prf) (← gCond.getType)
    unless typeOk do throwError "condition proof type mismatch"
    gCond.assign prf
    setGoals gsRest
  unless ok do
    restoreState saved
    return .notApplicable
  let hId ← freshIdent `hcond
  let g' ← (← getMainGoal).assert hId.getId propTy prf
  let (_, g'') ← g'.intro1P
  replaceMainGoal [g'']
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
    simp (config := { decide := true }) only [
      beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm] at $hId:ident)))
  return .stopped

/-- Step forward through up to `maxSteps` straight-line instructions until reaching `target_pc`,
    another function's entry (tail call via `B`), a subroutine call (`BL`/`BLR`), a return (`RET`),
    or an unresolved conditional branch (`ite` PC). A conditional branch whose decided arm is
    `target_pc` stops at the target (see `wpStopAtResolvedIteTarget`). Undetermined `step`-level PC
    conditions are recorded in `stepFailed` (`resolveIteCondFast?`). With `noteMaxRecDepth`, a step
    that fails with `maxRecDepth` logs an info message naming the step index, PC, and instruction. -/
def wpStepsCore (maxSteps : Nat) (quiet : Bool := false)
    (stepFailed : Option (IO.Ref (Array Expr)) := none)
    (warnOnBoundReached : Bool := false) (noteMaxRecDepth : Bool := false) :
    TacticM Unit := do
  let stepRemedy := "split the stepping block into smaller chunks (`wp_steps <n>` / `wp_compact`), focus the accessed memory atom with `wp_focus`, or discharge a branch/address side condition beforehand with `have h : ... := by bv_omega`"
  withWpHeartbeatDiag "wp_steps" "symbolic stepping" stepRemedy do
    let stopAtTarget := CondClassify.proofLib.wpStopAtBranchTarget.get (← getOptions)
    let verbose := !quiet && CondClassify.proofLib.wpVerbose.get (← getOptions)
    let mut boundaryCacheOpt : Option WpStepsBoundaryCache := none
    -- Set after a pair step (two instructions): the next iteration only consumes budget.
    let mut skipNext := false
    for i in [0:maxSteps] do
      if skipNext then
        skipNext := false
        continue
      let gs ← getGoals
      if gs.isEmpty then return
      if ← outerHeartbeatsExhausted then
        throwHeartbeatPhaseError "wp_steps" s!"stepping instruction #{i + 1}" stepRemedy
      let stateAndPc? ← withoutModifyingState do
        tryTacticCatchRuntime getSepWPStateAndPC
      let some (progExpr, targetPcExpr, pcExpr) := stateAndPc? | do
        if ← outerHeartbeatsExhausted then
          throwHeartbeatPhaseError "wp_steps" s!"extracting state and PC at step #{i + 1}" stepRemedy
        if i == 0 && !quiet then
          let g ← getMainGoal
          let wpp? ← g.withContext do
            let tgt := (← instantiateMVars (← g.getType)).consumeMData
            if tgt.isAppOfArity ``SepWPp 7 then
              pure (some (tgt.getArg! 1, tgt.getArg! 2))
            else
              pure none
          if let some (targetPc, sExpr) := wpp? then
            let pcE := mkApp (mkConst ``State.pc) sExpr
            logWpStopBeforeTarget "wp_steps" pcE targetPc
              m!"goal is `SepWPp`, which `wp_steps` does not step directly"
              m!"use `wpp_call <callee_spec>`, `wp_cut_call`, or `apply SepWPp.of_sepWP_ret` / `apply SepWPp.of_sepWP`"
              (quiet := quiet)
        return
      let bc ← match boundaryCacheOpt with
        | some c => Pure.pure c
        | none =>
          let c ← buildWpStepsBoundaryCache progExpr
          boundaryCacheOpt := some c
          Pure.pure c
      -- Also at `i = 0`: a goal left at an `ite` PC by an earlier stepping call whose decided arm is
      -- the target must stop there instead of resolving the branch and stepping the target instruction.
      if stopAtTarget then
        match ← wpStopAtResolvedIteTarget pcExpr targetPcExpr stepFailed with
        | .stopped =>
          if verbose then
            (← getMainGoal).withContext do
              logInfo <| MessageData.ofLazyM (es := #[targetPcExpr]) do
                return m!"wp_steps: stopped at target after a conditional branch (pc = {targetPcExpr})"
          return
        | .unresolved =>
          if i > 0 then
            let cond := if pcExpr.isAppOfArity ``ite 5 then pcExpr.getArg! 1 else pcExpr
            logWpStopBeforeTarget "wp_steps" pcExpr targetPcExpr
              m!"branch condition unresolved at pc (condition: {cond})"
              m!"use `wp_if hcond` (or prove `have hcond : ... := by bv_arith` before `wp_steps`)"
              (quiet := quiet)
            return
        | _ => Pure.pure ()
      if i > 0 then
        let atTarget ← withoutModifyingState do
          tryTacticCatchRuntimeBool do
            if ← pcReachedTarget pcExpr targetPcExpr then Pure.pure ()
            else throwError "not at target"
        if atTarget then
          if verbose then
            (← getMainGoal).withContext do
              logInfo <| MessageData.ofLazyM (es := #[pcExpr]) do
                return m!"wp_steps: stopped at return/target boundary (pc = {pcExpr})"
          return
        if ← isOtherFunctionEntryCached bc targetPcExpr pcExpr (afterUncondB := false) then
          logWpStopBeforeTarget "wp_steps" pcExpr targetPcExpr
            m!"stopped at function entry / tail-call boundary"
            m!"use `wp_tailcall <callee_spec>` (or `wp_step` to inline)"
            (quiet := quiet)
          return
      let resolvedItePcRef ← IO.mkRef (none : Option Expr)
      let stepped? ← tryTacticCatchRuntimeMsg
        (wpStepCoreWithOutcome stepFailed (resolvedItePcRef := some resolvedItePcRef))
      match stepped? with
      | .error detail =>
        if ← outerHeartbeatsExhausted then
          let pcStr ← (← getMainGoal).withContext (ppExprTruncated pcExpr 80 6)
          throwHeartbeatPhaseError "wp_steps" s!"stepping instruction #{i + 1} at pc = {pcStr}" stepRemedy
        if noteMaxRecDepth && MaxRecDepthDiag.msgIsMaxRecDepth detail then
          -- A recursion-depth failure is not a "no step rule applies" stop: without a note the
          -- next tactic fails on the same deep term with a bare Lean error. Stopping instead of
          -- throwing keeps proofs that continue with a different tactic at this point working.
          let first := ((← detail.toString).splitOn "\n").headD ""
          logInfo m!"wp_steps: stopped before instruction #{i + 1} ({i} stepped): it fails with `maxRecDepth`\n{first}\nrun `wp_step` here for the deepest term and remedies"
        let (_, targetNow, pcNow) ← getSepWPStateAndPC
        if let some resolvedPc ← resolvedItePcRef.get then
          reportStepStuck "wp_steps" resolvedPc detail (some targetNow) (quiet := quiet)
        else if pcNow.isAppOfArity ``ite 5 then
          let cond := pcNow.getArg! 1
          logWpStopBeforeTarget "wp_steps" pcNow targetNow
            m!"branch condition unresolved at pc (condition: {cond})"
            m!"use `wp_if hcond` (or prove `have hcond : ... := by bv_arith` before `wp_steps`)"
            (quiet := quiet)
        else
          reportStepStuck "wp_steps" pcNow detail (some targetNow) (quiet := quiet)
        return
      | .ok .steppedCall =>
        if !quiet then
          let (_, targetAfter, pcAfter) ← getSepWPStateAndPC
          let atTarget ← withoutModifyingState do
            tryTacticCatchRuntimeBool do
              if ← pcReachedTarget pcAfter targetAfter then Pure.pure ()
              else throwError "not at target"
          if atTarget then
            if verbose then
              (← getMainGoal).withContext do
                logInfo <| MessageData.ofLazyM (es := #[pcAfter]) do
                  return m!"wp_steps: stopped at subroutine call boundary (pc = {pcAfter})"
          else
            let callSitePc := (← resolvedItePcRef.get).getD pcExpr
            logWpStopBeforeTarget "wp_steps" pcAfter targetAfter
              m!"stopped at subroutine call boundary (`bl` at {callSitePc})"
              m!"use `wpp_call <callee_spec>` or `wp_call <callee_spec>` (or `wp_step` to inline)"
              (quiet := quiet)
        return
      | .ok .steppedRet =>
        if !quiet then
          let (_, targetAfter, pcAfter) ← getSepWPStateAndPC
          let atTarget ← withoutModifyingState do
            tryTacticCatchRuntimeBool do
              if ← pcReachedTarget pcAfter targetAfter then Pure.pure ()
              else throwError "not at target"
          if atTarget then
            if verbose then
              (← getMainGoal).withContext do
                logInfo <| MessageData.ofLazyM (es := #[pcAfter]) do
                  return m!"wp_steps: stopped at return/target boundary (pc = {pcAfter})"
          else
            logWpStopBeforeTarget "wp_steps" pcAfter targetAfter
              m!"stopped at return (`ret`), which does not match target pc"
              m!"check `target_pc` or `lr` (`x30`) preservation before `wp_done`"
              (quiet := quiet)
        return
      | .ok .steppedBranch =>
        let (_progAfter, targetAfter, pcAfter) ← getSepWPStateAndPC
        let atTarget ← withoutModifyingState do
          tryTacticCatchRuntimeBool do
            if ← pcReachedTarget pcAfter targetAfter then Pure.pure ()
            else throwError "not at target"
        if atTarget then
          if verbose then
            (← getMainGoal).withContext do
              logInfo <| MessageData.ofLazyM (es := #[pcAfter]) do
                return m!"wp_steps: stopped at return/target boundary (pc = {pcAfter})"
          return
        if (← isOtherFunctionEntryCached bc targetAfter pcAfter (afterUncondB := true)) ||
           (← withoutModifyingState (fastProgFetchNone? _progAfter pcAfter)) then
          logWpStopBeforeTarget "wp_steps" pcAfter targetAfter
            m!"stopped at function entry / tail-call boundary"
            m!"use `wp_tailcall <callee_spec>` (or `wp_step` to inline)"
            (quiet := quiet)
          return
      | .ok .steppedNormal =>
        continue
      | .ok .steppedPair =>
        skipNext := true
        continue
    if warnOnBoundReached && maxSteps > 0 then
      let gsEnd ← getGoals
      if !gsEnd.isEmpty then
        let stateAndPcEnd? ← withoutModifyingState do
          tryTacticCatchRuntime getSepWPStateAndPC
        if let some (_, targetEnd, pcEnd) := stateAndPcEnd? then
          let atTargetEnd ← withoutModifyingState do
            tryTacticCatchRuntimeBool do
              if ← pcReachedTarget pcEnd targetEnd then Pure.pure ()
              else throwError "not at target"
          if !atTargetEnd then
            logWpStopBeforeTarget "wp_steps" pcEnd targetEnd
              m!"reached default step bound ({maxSteps})"
              m!"pass an explicit bound (e.g. `wp_steps {maxSteps * 2}`) or another `wp_steps` to continue"
              (quiet := quiet)

/-- Step forward through straight-line instructions (default bound 128, or `wp_steps n`) until
    reaching `target_pc`, a tail-call function entry (`B`), a subroutine call (`BL`), or an
    unresolved conditional branch (`ite` PC). Under `set_option proofLib.wpVerbose true`, an
    `info` diagnostic is emitted with the stop reason and suggested next tactic. -/
syntax "wp_steps" (ppSpace colGt num)? : tactic
elab_rules : tactic
  | `(tactic| wp_steps $[$n?:num]?) => do
    let bound := match n? with
      | some n => n.getNat
      | none => 128
    let verbose := CondClassify.proofLib.wpVerbose.get (← getOptions)
    wpStepsCore bound (quiet := !verbose) (warnOnBoundReached := n?.isNone)
      (noteMaxRecDepth := true)

/-- Normalize a newly-introduced branch condition hypothesis `hId` in `wp_if`:
    skips `simp` altogether when `hId` is already a normalized relational inequality (`x.ule y = true`
    or `¬ x.ule y = true`), uses lightweight boolean/equality normalization when `hId` is free of
    `State` and bit-extraction terms, and falls back to `[wp_norm, arm64_norm]` only when needed. -/
def normWpIfHyp (hId : Ident) : TacticM Unit := do
  let g ← getMainGoal
  let (alreadyNormal, needsFullWpNorm) ← g.withContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? hId.getId | return (false, true)
    let ty ← instantiateMVars decl.type
    let hasStateOrBvExt := (ty.find? fun e =>
      if let .const nm _ := e then
        (`Arm64.State).isPrefixOf nm ||
        nm == ``BitVec.extractLsb || nm == ``BitVec.extractLsb' ||
        nm == ``BitVec.zeroExtend || nm == ``BitVec.signExtend || nm == ``BitVec.truncate ||
        nm == ``HAdd.hAdd || nm == ``HSub.hSub || nm == ``HAnd.hAnd
      else false).isSome
    if hasStateOrBvExt then
      return (false, true)
    let hasBoolOrBeq := (ty.find? fun e =>
      e.isConstOf ``BEq.beq || e.isConstOf ``bne ||
      e.isConstOf ``Decidable.decide || e.isConstOf ``Bool.not ||
      e.isConstOf ``Bool.false || e.isConstOf ``Bool.and || e.isConstOf ``Bool.or).isSome
    let isDoubleNeg := ty.isAppOfArity ``Not 1 && (ty.getArg! 0).isAppOfArity ``Not 1
    return (!hasBoolOrBeq && !isDoubleNeg, false)
  if alreadyNormal then
    return
  if needsFullWpNorm then
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [
        beq_iff_eq, bne_iff_ne, Classical.not_not,
        wp_norm, arm64_norm] at $hId:ident)))
  else
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [
        beq_iff_eq, bne_iff_ne, Classical.not_not,
        decide_eq_true_eq, bool_not_eq_true_iff] at $hId:ident)))

/-- Case-split on the current conditional branch (`if c then pc1 else pc2`) in `SepWP`. -/
syntax "wp_if" (ppSpace colGt ident)? : tactic
elab_rules : tactic
  | `(tactic| wp_if $[$h?:ident]?) => do
    let hId ← match h? with
      | some id => Pure.pure id
      | none => freshIdent `hcond
    evalTactic (← `(tactic| (
      apply SepWP.ite
      wp_focus_close wp_norm_lhs
    )))
    let gs ← getGoals
    match gs with
    | gThen :: gElse :: rest =>
      setGoals [gThen]
      evalTactic (← `(tactic| intro $hId:ident))
      normWpIfHyp hId
      evalTactic (← `(tactic| try wp_norm_state))
      let gsThen ← getGoals
      setGoals [gElse]
      evalTactic (← `(tactic| intro $hId:ident))
      normWpIfHyp hId
      evalTactic (← `(tactic| try wp_norm_state))
      let gsElse ← getGoals
      setGoals (gsThen ++ gsElse ++ rest)
    | _ => throwError "wp_if: unexpected subgoals"

/-- Step forward through straight-line instructions (`wpStepsCore`), splitting any unresolved
    conditional branch (`ite` PC) with `wp_if` and continuing to step both branches (up to
    `maxSplits` nested branch splits). -/
partial def wpStepsSplitCore (bound : Nat) (maxSplits : Nat := 8) : TacticM Unit := do
  let verbose := CondClassify.proofLib.wpVerbose.get (← getOptions)
  wpStepsCore bound (quiet := !verbose) (warnOnBoundReached := false)
  if maxSplits == 0 || (← getGoals).isEmpty then return
  let stateAndPc? ← withoutModifyingState do
    tryTacticCatchRuntime getSepWPStateAndPC
  let some (_, targetPcExpr, pcExpr) := stateAndPc? | return
  unless pcExpr.isAppOfArity ``ite 5 do return
  let atTarget ← withoutModifyingState do
    tryTacticCatchRuntimeBool do
      if ← pcReachedTarget pcExpr targetPcExpr then Pure.pure ()
      else throwError "not at target"
  if atTarget then return
  evalTactic (← `(tactic| wp_if))
  let gs ← getGoals
  match gs with
  | gThen :: gElse :: rest =>
    setGoals [gThen]
    wpStepsSplitCore bound (maxSplits - 1)
    let remThen ← getGoals
    setGoals [gElse]
    wpStepsSplitCore bound (maxSplits - 1)
    let remElse ← getGoals
    setGoals (remThen ++ remElse ++ rest)
  | _ => Pure.pure ()

/-- Variant of `wp_steps` that automatically case-splits unresolved conditional branches with
    `wp_if` and steps both branches: `wp_steps (split := true)` or `wp_steps n (split := true)`. -/
syntax "wp_steps" (ppSpace colGt num)? ppSpace atomic("(" &"split" " := " &"true" ")") : tactic
elab_rules : tactic
  | `(tactic| wp_steps $[$n?:num]? (split := true)) => do
    let bound := match n? with
      | some n => n.getNat
      | none => 128
    wpStepsSplitCore bound 8

/-- Eta-expand any unassigned metavariable of `Prod`, `Unit`, or user-defined `structure`
    type appearing in the current goal target so `dsimp` reduces projections before unifying
    leaf metavariables (without unpacking `BitVec`, `Fin`, or `Arm64` primitive structures).
    Returns `(fieldName, mvarId)` pairs for all leaf ghost metavariables. -/
partial def etaExpandGoalProdMVarsWithNames : TacticM (Array (Name × MVarId)) := do
  let g ← getMainGoal
  g.withContext do
    let env ← getEnv
    let ref ← IO.mkRef (#[] : Array (Name × MVarId))
    let recordLeaf (nm : Name) (m : MVarId) : MetaM Unit := do
      let arr ← ref.get
      if !arr.any (·.2 == m) then
        ref.set (arr.push (nm, m))
    let rec visit (prefixName : Name) (e : Expr) : MetaM Unit := do
      let e ← instantiateMVars e
      if e.isMVar then
        let mId := e.mvarId!
        let decl ← mId.getDecl
        let curName := if !prefixName.isAnonymous then prefixName
          else if !decl.userName.isAnonymous then decl.userName
          else `ghost
        let ty ← whnf (← inferType e)
        if ty.isAppOfArity ``Prod 2 then
          let n1 := curName.str "fst"
          let n2 := curName.str "snd"
          let m1 ← mkFreshExprMVar (ty.getArg! 0) (userName := n1)
          let m2 ← mkFreshExprMVar (ty.getArg! 1) (userName := n2)
          let pair ← mkAppM ``Prod.mk #[m1, m2]
          mId.assign pair
          visit n1 m1
          visit n2 m2
        else if ty.isConstOf ``Unit || ty.isConstOf ``PUnit then
          mId.assign (mkConst ``Unit.unit)
        else if let .const declName us := ty.getAppFn then
          let root := declName.getRoot
          let modRoot := match env.getModuleIdxFor? declName with
            | some idx =>
              if h : idx.toNat < env.header.moduleNames.size then
                env.header.moduleNames[idx.toNat].getRoot
              else root
            | none => root
          let isTestStruct := (`ProofLib.SepLogic.Tests).isPrefixOf declName
          if isStructure env declName &&
             declName != ``BitVec && declName != ``Fin &&
             (isTestStruct ||
              (root != `Init && root != `Std && root != `Lean && root != `Arm64 && root != `ProofLib &&
               modRoot != `Init && modRoot != `Std && modRoot != `Lean && modRoot != `Arm64 && modRoot != `ProofLib)) then
            if let some (.inductInfo indVal) := env.find? declName then
              if let [ctorName] := indVal.ctors then
                let fields := getStructureFields env declName
                let ctorApp := mkAppN (mkConst ctorName us) (ty.getAppArgs.extract 0 indVal.numParams)
                let ctorTy ← inferType ctorApp
                let (fieldMVars, _, _) ← forallMetaTelescopeReducing ctorTy
                let val := mkAppN ctorApp fieldMVars
                if ← isDefEq e val then
                  for idx in [:fieldMVars.size] do
                    let fm := fieldMVars[idx]!
                    let fn := if h : idx < fields.size then fields[idx] else curName.appendIndexAfter (idx + 1)
                    if fm.isMVar then
                      fm.mvarId!.setUserName fn
                    visit fn fm
                  return
          mId.setUserName curName
          recordLeaf curName mId
        else
          mId.setUserName curName
          recordLeaf curName mId
      else
        match e with
        | .app f a => visit .anonymous f; visit .anonymous a
        | .mdata _ b => visit prefixName b
        | .proj _ _ b => visit prefixName b
        | _ => Pure.pure ()
    visit .anonymous (← g.getType)
    ref.get

def etaExpandGoalProdMVars : TacticM Unit := do
  let _ ← etaExpandGoalProdMVarsWithNames

/-- Fold eta-expanded structure constructor applications `S.mk (proj₀ v) ... (projₙ₋₁ v)` back to `v`
    in the main goal target when they are reducibly defeq to `v`. -/
def foldStructEtaTarget : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let env ← getEnv
    let ty ← instantiateMVars (← g.getType)
    let ty' ← Core.transform ty (post := fun e => do
      let fn := e.getAppFn
      if let .const ctorName _ := fn then
        if let some (.ctorInfo cval) := env.find? ctorName then
          if isStructure env cval.induct && cval.numFields > 0 &&
             e.getAppNumArgs == cval.numParams + cval.numFields then
            let f0 := e.getArg! cval.numParams
            let cand? : Option Expr := match f0 with
              | .proj _ _ b => some b
              | .app _ b => some b
              | _ => none
            if let some v := cand? then
              if !v.hasMVar && !e.hasMVar then
                let ok ← withoutModifyingState do
                  if ← withReducible (isDefEq (← inferType v) (← inferType e)) then
                    withReducible (isDefEq e v)
                  else
                    Pure.pure false
                if ok then
                  return .done v
      return .continue)
    if ty' != ty then
      replaceMainGoal [← g.replaceTargetDefEq ty']

/-- Check whether `lhs` and `rhs` (after stripping mdata and normalizing 64-bit offsets) are
    syntactically distinct concrete values (distinct `BitVec`/`Nat`/`Bool` literals, or `base + c₁`
    vs `base + c₂` with `c₁ ≠ c₂`). -/
def checkPostValueMismatch (lhs rhs : Expr) : MetaM (Option (Expr × Expr)) := do
  let lhs := SepSolver.stripMData (← instantiateMVars lhs)
  let rhs := SepSolver.stripMData (← instantiateMVars rhs)
  if lhs.hasMVar || rhs.hasMVar then return none
  let (lNorm, _) ← SepSolver.normAddrMeta lhs
  let (rNorm, _) ← SepSolver.normAddrMeta rhs
  if let (some (w1, v1), some (w2, v2)) := (← evalBitVecLit? lNorm, ← evalBitVecLit? rNorm) then
    if w1 == w2 && v1 != v2 then
      return some (lNorm, rNorm)
  if let (some n1, some n2) := (← evalNatLit? lNorm, ← evalNatLit? rNorm) then
    if n1 != n2 then
      return some (lNorm, rNorm)
  if (lNorm.isConstOf ``Bool.true && rNorm.isConstOf ``Bool.false) ||
     (lNorm.isConstOf ``Bool.false && rNorm.isConstOf ``Bool.true) then
    return some (lNorm, rNorm)
  let (b1, o1) ← sepAddrBaseOff lNorm
  let (b2, o2) ← sepAddrBaseOff rNorm
  if o1 != o2 && (b1 == b2 || (← withReducibleAndInstances (isDefEq b1 b2))) then
    return some (lNorm, rNorm)
  return none

/-- Side-condition discharge for `wp_frame_split` / `wp_done`:
    - Strips `mdata`.
    - Fails fast if `φ` is a syntactic value mismatch (`checkPostValueMismatch`).
    - Caps defeq at `withReducibleAndInstances` (never unfolding `pointsTo64` or `SepProp` at
      default transparency).
    - Uses local hypotheses (`wp_assumption`, `with_reducible assumption`, `bv_omega`, `omega`,
      `bv_decide`) under a heartbeat cap. -/
def proveWpSepSide? (φ : Expr) : TacticM (Option Expr) := do
  let g0 ← getMainGoal
  g0.withContext do
    let φ := SepSolver.stripMData (← instantiateMVars φ)
    if let some (_, lhs, rhs) := φ.eq? then
      if (← checkPostValueMismatch lhs rhs).isSome then
        return none
      if ← withReducibleAndInstances (isDefEq lhs rhs) then
        return some (← mkEqRefl lhs)
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ← withReducibleAndInstances (isDefEq ty φ) then
          return some decl.toExpr
    let mvar ← mkFreshExprMVar φ
    let savedGoals ← getGoals
    setGoals [mvar.mvarId!]
    let ok ← tryTacticCatchRuntimeBool <| withHeartbeatCap 40000 do
      let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
        simp (config := { decide := true }) only [wp_norm, arm64_norm, *]))
      if !(← getGoals).isEmpty then
        let gCur ← getMainGoal
        let tyCur ← gCur.withContext (instantiateMVars (← gCur.getType))
        if let some (_, lhs', rhs') := tyCur.eq? then
          if (← gCur.withContext (checkPostValueMismatch lhs' rhs')).isSome then
            throwError "syntactic value mismatch"
        let closed1 ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
          first
            | done
            | with_reducible rfl
            | wp_assumption
            | with_reducible assumption
            | decide
            | (bv_omega_fast; done)
            | (wp_omega_bounded; done)
            | (bv_fallback; done)))
        if !closed1 then
          let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic| (
            try dsimp only [subsPState64, addsPState64, subsPState32, addsPState32, AddWithCarry64, AddWithCarry32, ConditionHolds, rev64, rev32_64, rev16_64] at *
            try simp (config := { decide := true }) only [wp_norm, arm64_norm, *] at *
            first
              | done
              | with_reducible rfl
              | wp_assumption
              | with_reducible assumption
              | decide
              | (wp_omega_bounded; done)
              | (bv_fallback; done))))
      if !(← getGoals).isEmpty then throwError "unsolved side condition"
    setGoals savedGoals
    if ok then return some (← instantiateMVars mvar) else return none

/-- Close a goal `m ⊨ A₁ ∗ ⋯ ∗ Aₖ ∗ (?F ∗ R)` from the latest hypothesis `m ⊨ B₁ ∗ ⋯ ∗ Bₙ ∗ R`,
    or close a `SepFrame sub full frame` goal:
    both sides are stripped of `mdata` and normalized with `wp_norm`, atoms are compared only at
    reducible/instances transparency, and failures report the unmatched atoms and candidates.
    When the greedy matcher fails (e.g. ghost metavariables that need backtracking, or a stack
    region that must be carved out of a larger one), the goal is retried with the backtracking
    frame procedure `SepFrameInfer.frameProc` (`sep_frame`). -/
elab "wp_frame_split" : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext (instantiateMVars (← g.getType))
  if (SepSolver.stripMData ty).isAppOfArity ``SepFrame 3 then
    try
      evalTactic (← `(tactic| wp_sep_access))
    catch e =>
      try
        evalTactic (← `(tactic| sep_frame))
      catch _ => throw e
  else
    try
      SepSolver.closeSat proveWpSepSide?
    catch e =>
      unless ← SepFrameInfer.closeSatBacktrack? proveWpSepSide? do throw e

private def formatGhostContext (ghostMVars : Array (Name × MVarId)) (e : Expr) :
    MetaM (Array Name × Array MessageData) := do
  let mut unassigned : Array Name := #[]
  let mut unified : Array MessageData := #[]
  let eInst ← instantiateMVars e
  for (nm, mId) in ghostMVars do
    if ← mId.isAssigned then
      let val ← instantiateMVars (mkMVar mId)
      if (e.find? (· == mkMVar mId)).isSome || (eInst.find? (· == val)).isSome || ghostMVars.size <= 6 then
        unified := unified.push m!"{nm} := {val}"
    else
      if (eInst.find? (· == mkMVar mId)).isSome then
        unassigned := unassigned.push nm
  if unassigned.isEmpty && eInst.hasMVar then
    let mvars ← getMVars eInst
    for mId in mvars do
      let decl ← mId.getDecl
      let nm := if decl.userName.isAnonymous then `ghost else decl.userName
      if !unassigned.contains nm then
        unassigned := unassigned.push nm
  return (unassigned, unified)

private def destructureSatHyps : TacticM Unit := do
  for _ in [0:16] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let lctx ← g.withContext getLCtx
    let mut progress := false
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
        let ty ← g.withContext (instantiateMVars decl.type)
        if (ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2) &&
           (ty.find? (·.isConstOf ``SepProp.Satisfies)).isSome then
          let id := mkIdent decl.userName
          let vId ← freshIdent `v_stk
          if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| rcases $id:ident with ⟨$vId:ident, $id:ident⟩))) then
            progress := true
            break
    if !progress then break

def wpDischargeCallSubgoalsCore (ghostMVars : Array (Name × MVarId) := #[])
    (hcallStx? : Option Term := none) : TacticM Unit := do
  let commaSep := m!", "
  let gs1 ← getGoals
  let totalConj := gs1.length
  let mut origTypes : Std.HashMap MVarId (Nat × Expr) := {}
  let mut conjCounter : Nat := 0
  for g in gs1 do
    conjCounter := conjCounter + 1
    let ty ← g.withContext (instantiateMVars (← g.getType))
    origTypes := origTypes.insert g (conjCounter, ty)
  let mut rem1 : List MVarId := []
  for g in gs1 do
    let isBindEq ← g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      match ty.eq? with
      | some (_, lhs, rhs) => return (!lhs.hasMVar && rhs.hasMVar)
      | none => return false
    if isBindEq then
      setGoals [g]
      let ok ← tryTacticCatchRuntimeBool do
        evalTactic (← `(tactic| wp_norm_lhs))
        unless (← getGoals).isEmpty do throwError "unsolved"
      if !ok then
        rem1 := rem1 ++ [g]
    else
      rem1 := rem1 ++ [g]
  let mut rem2 : List MVarId := []
  for g in rem1 do
    if ← g.isAssigned then continue
    let (isFrame, isSat) ← g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      return (ty.isAppOfArity ``SepFrame 3, ty.isAppOfArity ``SepProp.Satisfies 2)
    if isFrame then
      setGoals [g]
      let ok ← tryTacticCatchRuntimeBool do
        evalTactic (← `(tactic| wp_sep_access))
        unless (← getGoals).isEmpty do throwError "unsolved"
      if !ok then
        g.withContext do
          let ty := (← instantiateMVars (← g.getType)).consumeMData
          let msg ← SepSolver.explainFrameSplitFailure (ty.getArg! 0) (ty.getArg! 1)
          let (unassigned, unified) ← formatGhostContext ghostMVars (ty.getArg! 0)
          let ghostMsg := if !unassigned.isEmpty then
              m!"\nghost(s) being unified: {unassigned}"
            else if !unified.isEmpty then
              m!"\nwith unified ghost(s): {MessageData.joinSep unified.toList commaSep}"
            else m!""
          throwError "wp_call: {msg}{ghostMsg}"
    else if isSat then
      setGoals [g]
      destructureSatHyps
      let ok ← tryTacticCatchRuntimeBool do
        evalTactic (← `(tactic| first | wp_frame_split | (arm64_sep_close; done)))
        unless (← getGoals).isEmpty do throwError "unsolved"
      if !ok then
        g.withContext do
          let ty := (← instantiateMVars (← g.getType)).consumeMData
          let targetP := ty.getArg! 0
          let m := ty.getArg! 1
          let mut ctxP := mkConst ``SepProp.emp
          if let some (_, P) ← SepSolver.findSatHyp? m then
            ctxP := P
          let msg ← SepSolver.explainFrameSplitFailure targetP ctxP
          let (unassigned, unified) ← formatGhostContext ghostMVars targetP
          let ghostMsg := if !unassigned.isEmpty then
              m!"\nghost(s) being unified: {unassigned}"
            else if !unified.isEmpty then
              m!"\nwith unified ghost(s): {MessageData.joinSep unified.toList commaSep}"
            else m!""
          throwError "wp_call: {msg}{ghostMsg}"
    else
      rem2 := rem2 ++ [g]
  let rem3 ← rem2.filterM fun m => not <$> m.isAssigned
  for g in rem3 do
    if ← g.isAssigned then continue
    setGoals [g]
    let (conjIdx, origTy) := origTypes.getD g (1, ← g.withContext (instantiateMVars (← g.getType)))
    let _ ← tryTacticCatchRuntimeBool <| withHeartbeatCap 30000 do
      evalTactic (← `(tactic| simp (config := { decide := true }) only [wp_norm, arm64_norm, *]))
    if (← getGoals).isEmpty then continue
    let gCur ← getMainGoal
    let normTy ← gCur.withContext (instantiateMVars (← gCur.getType))
    if normTy.hasMVar then
      let closedMVar ← tryTacticCatchRuntimeBool <| withHeartbeatCap 25000 do
        evalTactic (← `(tactic| first | done | wp_norm_lhs | with_reducible rfl | wp_assumption | with_reducible assumption))
        unless (← getGoals).isEmpty do throwError "unsolved"
      if closedMVar then continue
      let gAfter ← getMainGoal
      let tyAfter ← gAfter.withContext (instantiateMVars (← gAfter.getType))
      if tyAfter.hasMVar then
        gAfter.withContext do
          let (unassigned, _) ← formatGhostContext ghostMVars tyAfter
          let hint := match hcallStx? with
            | some h => m!"`wp_call {h} <ghost_arg>`"
            | none => m!"`wp_call <hcall> <ghost_arg>`"
          throwError "wp_call: underdetermined ghost variable(s) {unassigned} in callee precondition conjunct:{indentExpr origTy}\n(normalized:{indentExpr tyAfter})\nhint: pass the ghost argument explicitly with {hint}"
    let closedPure ← tryTacticCatchRuntimeBool <| withHeartbeatCap 40000 do
      evalTactic (← `(tactic|
        first
          | done
          | with_reducible rfl
          | wp_assumption
          | with_reducible assumption
          | assumption
          | decide
          | (bv_omega_fast; done)
          | (wp_omega_bounded; done)
          | (bv_fallback; done)))
      unless (← getGoals).isEmpty do throwError "unsolved"
    if closedPure then continue
    let closedWithHyps ← tryTacticCatchRuntimeBool <| withHeartbeatCap 40000 do
      evalTactic (← `(tactic| (
        try simp (config := { decide := true }) only [wp_norm, arm64_norm, *] at *
        first
          | done
          | with_reducible rfl
          | wp_assumption
          | assumption
          | decide
          | (wp_omega_bounded; done)
          | (bv_fallback; done))))
      unless (← getGoals).isEmpty do throwError "unsolved"
    if closedWithHyps then continue
    let gFail ← getMainGoal
    gFail.withContext do
      let failTy ← instantiateMVars (← gFail.getType)
      let (_, unified) ← formatGhostContext ghostMVars origTy
      let mut unassignedAll : Array Name := #[]
      for (nm, mId) in ghostMVars do
        if !(← mId.isAssigned) then
          unassignedAll := unassignedAll.push nm
      let ghostMsg := if !unified.isEmpty then
          m!"\nwith unified ghost(s): {MessageData.joinSep unified.toList commaSep}"
        else m!""
      let hasToNat := (failTy.find? (·.isConstOf ``BitVec.toNat)).isSome
      let preHint := m!"\nhint: prove `have h_pre : {failTy} := by ...` before `wp_call`"
      let ghostHint := if !unassignedAll.isEmpty || (hasToNat && !ghostMVars.isEmpty) then
          let hint := match hcallStx? with
            | some h => m!"`wp_call {h} <ghost_arg>`"
            | none => m!"`wp_call <hcall> <ghost_arg>`"
          m!"; if ghost variables are underdetermined, pass them explicitly with {hint}"
        else m!""
      throwError "wp_call: failed to prove callee precondition conjunct: (conjunct {conjIdx}/{totalConj}){indentExpr origTy}\nnormalized:{indentExpr failTy}{ghostMsg}{preHint}{ghostHint}"
  setGoals []

/-- Discharge the conjunct subgoals of a `wp_call` precondition in dependency order:
    1. Instantiate register-passed ghost metavariables from `lhs = rhs` equalities (`wp_norm_lhs`).
    2. Discharge spatial `SepProp.Satisfies` (`m ⊨ ...`) and `SepFrame` subgoals (`wp_frame_split`,
       `wp_sep_access`), instantiating memory-value ghost fields and the frame `?F`.
    3. Discharge remaining pure side conditions from the local context. -/
elab "wp_discharge_call_subgoals" : tactic => wpDischargeCallSubgoalsCore

def betaReduceTarget : TacticM Unit := do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty' ← Core.betaReduce ty
  if ty' != ty then
    replaceMainGoal [← g.replaceTargetDefEq ty']

/-- Normalize the spatial context `P` of a `SepWP prog target_pc s P post` or
    `SepWPp prog ret s P Q Qp oom` goal (unfolding stack frames, rewriting with the equation `hEq`
    (e.g. `sf.sp = ...`), floating `∃∗` and `⌜_⌝` outwards), then eliminate leading existentials into
    fresh variables and leading pure assertions into (split, normalized) hypotheses. -/
def wpElimSpatialContext (hEq : Ident) (forWppCall : Bool := false) : TacticM Unit := do
  if forWppCall then
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
      conv =>
        arg 4
        simp (config := { decide := true }) only [
          Spec.inImage,
          stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          emp_sepConj, sepConj_emp,
          List.length_nil, List.length_cons, List.length_singleton,
          Nat.mul_zero, memRegion_zero, pointsToWords64_nil, BitVec.sub_self,
          wp_norm, arm64_norm, $hEq:ident]))))
  else
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
      conv =>
        arg 4
        simp (config := { decide := true }) only [
          Spec.inImage,
          stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          wp_norm, arm64_norm, $hEq:ident]))))
  for _ in [0:64] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    let isWP := ty.isAppOfArity ``SepWP 6
    let isWPp := ty.isAppOfArity ``SepWPp 7
    unless isWP || isWPp do return
    let P := (ty.getArg! 3).consumeMData
    if P.isAppOfArity ``SepProp.sepExists 2 then
      let wId ← freshIdent `w
      if isWP then
        evalTactic (← `(tactic| (apply SepWP.exists_elim; intro $wId:ident)))
      else
        evalTactic (← `(tactic| (apply SepWPp.exists_elim; intro $wId:ident)))
      betaReduceTarget
    else if P.isAppOfArity ``SepProp.sepConj 2 && (P.getArg! 0).isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      if isWP then
        evalTactic (← `(tactic| (apply SepWP.pure_elim; intro $hId:ident)))
      else
        evalTactic (← `(tactic| (apply SepWPp.pure_elim; intro $hId:ident)))
      wpNormAndSplitHyp hId
      if (← getGoals).isEmpty then return
      let gNow ← getMainGoal
      let isFalse ← gNow.withContext do
        match (← getLCtx).findFromUserName? hId.getId with
        | some d => Pure.pure ((← instantiateMVars d.type).isConstOf ``False)
        | none => Pure.pure false
      if isFalse then
        evalTactic (← `(tactic| exact False.elim $hId:ident))
        return
    else if P.isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      if isWP then
        evalTactic (← `(tactic| (apply SepWP.pure_elim_only; intro $hId:ident)))
      else
        evalTactic (← `(tactic| (apply SepWPp.pure_elim_only; intro $hId:ident)))
      wpNormAndSplitHyp hId
      if (← getGoals).isEmpty then return
      let gNow ← getMainGoal
      let isFalse ← gNow.withContext do
        match (← getLCtx).findFromUserName? hId.getId with
        | some d => Pure.pure ((← instantiateMVars d.type).isConstOf ``False)
        | none => Pure.pure false
      if isFalse then
        evalTactic (← `(tactic| exact False.elim $hId:ident))
        return
    else
      return

/-- True if `specExpr` is `Spec.split ...` after delta-unfolding head definitions one at a time
    (e.g. `Spec.rustSret` or a user-defined `def mySpec := Spec.split ...`). Unlike `whnf`, this
    stops at `Spec.split` itself instead of reducing it to its underlying `Spec` structure literal. -/
partial def specIsSplit (specExpr : Expr) : MetaM Bool := do
  let e ← whnfCore specExpr
  if e.isAppOfArity ``Arm64.Spec.split 5 then
    return true
  match ← unfoldDefinition? e with
  | some e' => specIsSplit e'
  | none => return false

/-- True when `nm` is an internal matcher, structure projection, arithmetic/list/string operator,
    or trusted object/placed/program table constructor or lookup that `extractRebase?`,
    `extractFnAddrSym?`, and `rebaseCodeArgs?` must never delta-unfold while searching for a
    `Program.rebase` or `Program.fnAddr` wrapper. -/
def isBlockedEntryUnfoldHead (env : Environment) (nm : Name) : MetaM Bool := do
  if isMatcherCore env nm || nm.isInternalDetail then
    return true
  if (← getProjectionFnInfo? nm).isSome then
    return true
  let pfx := nm.getPrefix
  if pfx == `BitVec || pfx == `Nat || pfx == `Int || pfx == `List || pfx == `String ||
     pfx == `HAdd || pfx == `HSub || pfx == `HMul || pfx == `OfNat ||
     pfx == `Arm64.Obj.Interned || pfx == `Arm64.Obj.MultiPlacedLib.SymIndex ||
     pfx == `Arm64.Obj.RelocFnIndex then
    return true
  return nm == ``Arm64.Program.mk ||
    nm == ``Arm64.Program.fnOff ||
    nm == ``Arm64.Program.findSymbol? ||
    nm == ``Arm64.Program.ofImage ||
    nm == ``Arm64.Program.ofImageWithSvc ||
    nm == ``Arm64.Program.ofWords ||
    nm == ``Arm64.Obj.lookup ||
    nm == ``Arm64.Obj.lookupUnique ||
    nm == ``Arm64.Obj.lookupBlockSym ||
    nm == ``Arm64.Obj.lookupBlockSymAux ||
    nm == `Arm64.Obj.lookupSymInLists ||
    nm == ``Arm64.Obj.LinkedImage.toProgram ||
    nm == ``Arm64.Obj.LinkedImage.toProgramWithSvc ||
    nm == ``Arm64.Obj.LinkedImage.fnAddr ||
    nm == ``Arm64.Obj.LinkedImage.resolveSym ||
    nm == ``Arm64.Obj.LinkedImage.resolveObjSym ||
    nm == ``Arm64.Obj.Image.symtab ||
    nm == ``Arm64.Obj.CodeBlock.patched ||
    nm == ``Arm64.Obj.CodeBlock.resolve ||
    nm == ``Arm64.Obj.CodeBlock.relocAt? ||
    nm == ``Arm64.Obj.CodeBlock.target ||
    nm == ``Arm64.Obj.CodeBlock.relocTarget ||
    nm == ``Arm64.Obj.PlacedLib.program ||
    nm == ``Arm64.Obj.PlacedLib.fnAddr ||
    nm == ``Arm64.Obj.MultiPlacedLib.blockProgram ||
    nm == ``Arm64.Obj.MultiPlacedLib.blockLib ||
    nm == ``Arm64.Obj.MultiPlacedLib.blockPlacement ||
    nm == ``Arm64.Obj.MultiPlacedLib.fnAddr ||
    nm == ``Arm64.Obj.MultiPlacedLib.resolve

/-- Extract `(codeConst, bExpr, hExpr, oExpr)` from a `Program.rebase` expression, unfolding
    reducible/program abbreviations (such as `VP b hooks`) without unfolding `Program.rebase` or
    concrete object/placed table definitions. -/
partial def extractRebase? (e : Expr) (fuel : Nat := 8) :
    MetaM (Option (Name × Expr × Expr × Expr)) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Program.rebase 4 then
    let args := e.getAppArgs
    let codeExpr := args[0]!.consumeMData
    let codeConst? ← match codeExpr.getAppFn.constName? with
      | some c => Pure.pure (some c)
      | none =>
        let codeWhnf ← withReducible (whnf codeExpr)
        Pure.pure codeWhnf.consumeMData.getAppFn.constName?
    if let some codeConst := codeConst? then
      return some (codeConst, args[1]!, args[2]!, args[3]!)
    return none
  match fuel with
  | 0 => return none
  | fuel' + 1 =>
    if let .const nm _ := e.getAppFn.consumeMData then
      if ← isBlockedEntryUnfoldHead (← getEnv) nm then
        return none
    if let some e' ← unfoldDefinition? e then
      return ← extractRebase? e' fuel'
    return none

/-- Extract the symbol string literal from a `Program.fnAddr prog "sym"` expression if present,
    without unfolding symbol-table lookup functions (`PlacedLib.fnAddr`, `MultiPlacedLib.fnAddr`,
    `Obj.lookup`, etc.). -/
partial def extractFnAddrSym? (e : Expr) (fuel : Nat := 8) : MetaM (Option String) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Program.fnAddr 2 then
    let symArg := (e.getArg! 1).consumeMData
    if let .lit (.strVal s) := symArg then
      return some s
    if let some (.lit (.strVal s)) ← Arm64.Program.reduceToStringLit? symArg then
      return some s
    return none
  if let some fnAddrSub := e.find? (·.isAppOfArity ``Program.fnAddr 2) then
    if fnAddrSub != e then
      return ← extractFnAddrSym? fnAddrSub fuel
  match fuel with
  | 0 => return none
  | fuel' + 1 =>
    if let .const nm _ := e.getAppFn.consumeMData then
      if ← isBlockedEntryUnfoldHead (← getEnv) nm then
        return none
    if let some e' ← unfoldDefinition? e then
      return ← extractFnAddrSym? e' fuel'
    return none

private def toHexNat (n : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 n)

-- Simplifies the LHS of a dummy `e = e` so `simp` cannot collapse an outer `Eq` to `False`.
private def normTermForDiff (e : Expr) : TacticM Expr := do
  let g0 ← getMainGoal
  let e ← g0.withContext do Pure.pure (SepSolver.stripMData (← instantiateMVars e))
  if e.isAtomic || (← g0.withContext (evalBitVecLit? e)).isSome || (← g0.withContext (evalNatLit? e)).isSome then
    return e
  let (_, hypIds) ← g0.withContext getLightweightSimpHyps
  let saved ← saveState
  let res? ← tryTacticCatchRuntime do
    let eqTy ← g0.withContext (mkEq e e)
    let m ← g0.withContext (mkFreshExprMVar eqTy)
    setGoals [m.mvarId!]
    let _ ← tryTacticCatchRuntimeBool <| withHeartbeatCap 15000 do
      evalTactic (← `(tactic| (
        conv =>
          lhs
          simp (config := { decide := true }) only [
            pure, bind, Functor.map, Seq.seq,
            Option.map, Option.bind, Option.getD, Option.isSome, Option.isNone,
            List.foldlM, wp_norm, arm64_norm, $[$hypIds:ident],*]
      )))
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    match ty.eq? with
    | some (_, lhs', _) => return lhs'
    | none => return e
  restoreState saved
  return res?.getD e

private def normAddrForDiag (e : Expr) : TacticM Expr := do
  let g0 ← getMainGoal
  let e0 ← g0.withContext do
    let e := SepSolver.stripMData (← instantiateMVars e)
    if e.isAppOfArity ``State.pc 1 then
      extractSepWPPC (e.getArg! 0)
    else
      Pure.pure e
  let (e1, _) ← g0.withContext do
    MonadRuntimeException.tryCatchRuntimeEx
      (SepSolver.normAddrMeta e0)
      (fun _ => Pure.pure (e0, none))
  let e2 ← normTermForDiff e1
  let (e3, _) ← g0.withContext do
    MonadRuntimeException.tryCatchRuntimeEx
      (SepSolver.normAddrMeta e2)
      (fun _ => Pure.pure (e2, none))
  if let some (64, v) ← g0.withContext (evalBitVecLit? e3) then
    return toExpr (BitVec.ofNat 64 v)
  return e3

/-- Format a 64-bit address `e` concisely with hexadecimal literals/offsets (or a truncated
    `ppExpr` fallback). -/
def formatShortHexAddr (e : Expr) : MetaM String := do
  let e := SepSolver.stripMData (← instantiateMVars e)
  if let some (64, v) ← evalBitVecLit? e then
    return s!"{toHexNat v}#64"
  let (base, offNat) ← sepAddrBaseOff e
  if base == toExpr (0#64) then
    return s!"{toHexNat offNat}#64"
  let baseStr ← ppExprTruncated base 80 10
  if offNat == 0 then
    return baseStr
  else if offNat >= 2 ^ 63 then
    return s!"{baseStr} + {toHexNat offNat}#64 (= {baseStr} - {toHexNat (2 ^ 64 - offNat)}#64)"
  else
    return s!"{baseStr} + {toHexNat offNat}#64"

private def throwUnresolvedBranchError (tacticName : String) (pcExpr : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let condExpr := pcExpr.getArg! 1
    let thenPcExpr := pcExpr.getArg! 3
    let elsePcExpr := pcExpr.getArg! 4
    let condStr ← ppExprTruncated condExpr (maxChars := 160) (maxDepth := 12)
    let thenStr ← formatShortHexAddr thenPcExpr
    let elseStr ← formatShortHexAddr elsePcExpr
    throwError "{tacticName}: current PC is an unresolved conditional branch:\n  condition: {condStr}\n  then PC:   {thenStr}\n  else PC:   {elseStr}\nhint: if both branches are reachable, split with `wp_if hcond` (or `wp_if_join <join_pc> <inv>` for diamond control flow); if only one branch is feasible, prove `have hcond : <cond> = true := by bv_omega` (or `= false`) before `wp_steps` / `wp_sym_steps`, or simplify the current PC with `wp_simp_pre [hcond]`"

/-- Bounded fallback branch-condition decision (`proofLib.wpBranchAutoDecide`) tried only when
    `resolveIteCondTerminal?` returns `none` and `wp_done` / `wp_call` / `loopDrive` would
    otherwise throw an unresolved conditional branch error. -/
def resolveIteCondAutoFallback? (c : Expr) : TacticM (Option (Bool × Expr × Expr)) := do
  if let some res ← resolveIteCondTerminal? c then
    return some res
  unless proofLib.wpBranchAutoDecide.get (← getOptions) do
    return none
  let g0 ← getMainGoal
  let tryProveProp (propTy : Expr) : TacticM (Option Expr) := do
    let res? ← withoutModifyingState do
      tryTacticCatchRuntime <| withHeartbeatCap 10000 do
        let mvar ← g0.withContext (mkFreshExprMVar propTy)
        setGoals [mvar.mvarId!]
        let (_, hypIds) ← g0.withContext getLightweightSimpHyps
        let ok ← tryTacticCatchRuntimeBool do
          evalTactic (← `(tactic| (
            try simp (config := { decide := true }) only [
              beq_iff_eq, bne_iff_ne, Classical.not_not,
              decide_eq_true_eq, bool_not_eq_true_iff,
              wp_norm, arm64_norm, $[$hypIds:ident],*]
            first
              | done
              | trivial
              | with_reducible rfl
              | wp_assumption
              | with_reducible assumption
              | decide
              | (bv_omega_fast; done)
              | (wp_omega_bounded; done))))
          unless (← getGoals).isEmpty do throwError "unsolved"
        if ok then
          return some (← g0.withContext (instantiateMVars mvar))
        else
          return none
    return res?.join
  if let some prf ← tryProveProp c then
    return some (true, c, prf)
  let nc := mkNot c
  if let some prf ← tryProveProp nc then
    return some (false, nc, prf)
  return none

/-- For a tactic (`tacticName`: `"wp_done"` / `"wp_call"` / `"loop tactic"`) that cannot proceed at an `ite` PC:
    if the main goal's PC `pcExpr` is `if c then t else e`, decide `c`
    (`resolveIteCondAutoFallback?`), select the decided arm (`SepWP.ite_true` / `ite_false`) and
    add the decided condition as a hypothesis; otherwise throw the unresolved-branch error.
    No-op if `pcExpr` is not an `ite`. -/
def resolveTerminalPcIte (tacticName : String) (pcExpr : Expr) : TacticM Unit := do
  unless pcExpr.isAppOfArity ``ite 5 do return
  let c := pcExpr.getArg! 1
  let some (condTrue, propTy, prf) ← resolveIteCondAutoFallback? c
    | throwUnresolvedBranchError tacticName pcExpr
  let hId ← freshIdent `hcond
  let detIte ← tryTacticCatchRuntimeBool do
    if condTrue then
      evalTactic (← `(tactic| (apply SepWP.ite_true; wp_focus_close wp_norm_lhs)))
    else
      evalTactic (← `(tactic| (apply SepWP.ite_false; wp_focus_close wp_norm_lhs)))
    let gCond :: gsRest ← getGoals | throwError "expected condition subgoal"
    if ← gCond.withContext do isDefEq (← inferType prf) (← gCond.getType) then
      gCond.assign prf
      setGoals gsRest
    else
      throwError "{tacticName}: condition proof type mismatch"
  unless detIte do throwUnresolvedBranchError tacticName pcExpr
  let g ← getMainGoal
  let g' ← g.assert hId.getId propTy prf
  let (_, g'') ← g'.intro1P
  replaceMainGoal [g'']
  normWpIfHyp hId
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| try wp_norm_state)))

/-- Maximum number of `ite` PCs `wp_done` decides (`resolveTerminalPcIte`) on the way to the
    target PC; between two of them it steps with `wp_steps`. -/
def wpDoneExitRounds : Nat := 4

private def wpDonePcMatches : TacticM Bool := do
  let saved ← saveState
  let ok ← tryTacticCatchRuntimeBool do
    evalTactic (← `(tactic| apply SepWP.done))
    let gPc :: _ ← getGoals | throwError "wp_done: unexpected subgoals after `SepWP.done`"
    setGoals [gPc]
    evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal)))
  saved.restore (restoreInfo := true)
  return ok

private def evalFetchDecodeDiag? (progExpr pcExpr : Expr) : TacticM (Option Expr) := do
  let res? ← withoutModifyingState do
    tryTacticCatchRuntime <| withHeartbeatCap 8000 do
      let g0 ← getMainGoal
      g0.withContext do
        let tryAt (pc : Expr) : TacticM (Option Expr) := do
          let savedGoals ← getGoals
          let instMVar ← mkFreshExprMVar (mkConst ``Instr)
          let someInst ← mkAppM ``Option.some #[instMVar]
          let fetchLhs := mkApp2 (mkConst ``Program.fetch) progExpr pc
          let fetchGoalTy ← mkEq fetchLhs someInst
          let fetchGoal ← mkFreshExprMVar fetchGoalTy
          setGoals [fetchGoal.mvarId!]
          -- Nested `else do` blocks keep the fallbacks lazy (the conditions of an `if ... else if ← c`
          -- term are hoisted and run before the `if`).
          let ok ←
            if ← tryCloseFetchFromHasCode then
              Pure.pure true
            else do
            if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_assumption))) then
              Pure.pure true
            else do
            if !(← fastProgFetchNone? progExpr pc) &&
                    ((← evalBitVecLit? pc).isSome || (← evalPCBaseOff? pc).isSome || pc.isFVar) then
              tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (
                (conv => lhs; simp (config := { decide := true }) only [arm64_norm]);
                rfl))))
            else
              Pure.pure false
          setGoals savedGoals
          if ok then
            return some (← instantiateMVars instMVar)
          else
            return none
        if let some inst ← tryAt pcExpr then
          return some inst
        let pcNorm ← normAddrForDiag pcExpr
        if pcNorm != pcExpr then
          if let some inst ← tryAt pcNorm then
            return some inst
        let progUnwrapped ← unwrapRebasedProgExpr progExpr
        let progBase ← whnf (mkApp (mkConst ``Program.base) progUnwrapped)
        let (bProg, oProg) ← sepAddrBaseOff progBase
        let (bPc, oPc) ← sepAddrBaseOff pcNorm
        if bPc == bProg || (← withReducibleAndInstances (isDefEq bPc bProg)) then
          let relOff := (oPc + 2 ^ 64 - oProg) % (2 ^ 64)
          let rawProgExpr :=
            if progUnwrapped.isAppOfArity ``Program.rebase 4 then progUnwrapped.getArg! 0
            else progUnwrapped
          if let some rawConst := rawProgExpr.consumeMData.getAppFn.constName? then
            let treeName := rawConst.appendAfter "_tree"
            if (← getEnv).contains treeName then
              let treeRes ← withHeartbeatCap 4000
                (whnf (mkApp2 (mkConst ``ProofLib.ProgramReflection.WordTree.fetchDecodeAt)
                  (mkConst treeName) (toExpr relOff)))
              if treeRes.isAppOfArity ``Option.some 2 then
                return some (treeRes.getArg! 1)
        return none
  return res?.join

private def isMemoryLoadStoreOp (instExpr : Expr) : Bool :=
  let c := instExpr.getAppFn.constName?.getD .anonymous
  c == ``Instr.ldr || c == ``Instr.ldrLit || c == ``Instr.str ||
  c == ``Instr.ldp || c == ``Instr.stp ||
  c == ``Instr.ldarStlr || c == ``Instr.ldxr || c == ``Instr.stxr ||
  c == ``Instr.ldpSimd || c == ``Instr.stpSimd ||
  c == ``Instr.ldrSimd || c == ``Instr.strSimd ||
  c == ``Instr.st1SinglePost || c == ``Instr.ldrSimdLit ||
  c == ``Instr.ldxp || c == ``Instr.stxp ||
  c == ``Instr.cas || c == ``Instr.casp || c == ``Instr.atomicRmw ||
  c == ``Instr.ldapr || c == ``Instr.ldapurStlur ||
  c == ``Instr.ldnp || c == ``Instr.stnp ||
  c == ``Instr.ldnpSimd || c == ``Instr.stnpSimd ||
  c == ``Instr.simdLdSt1Multi || c == ``Instr.simdLd1r

private partial def collectTableSymOffs (tbl : Expr) (fuel : Nat := 512) :
    MetaM (Array (String × Nat)) := do
  if fuel == 0 then return #[]
  let tblWhnf ← whnf tbl
  if tblWhnf.isAppOfArity ``List.nil 1 then
    return #[]
  if tblWhnf.isAppOfArity ``List.cons 3 then
    let head ← whnf (tblWhnf.getArg! 1)
    let tail := tblWhnf.getArg! 2
    let mut rest ← collectTableSymOffs tail (fuel - 1)
    if head.isAppOfArity ``Prod.mk 4 then
      let symExpr := (head.getArg! 2).consumeMData
      let sym? ← match symExpr with
        | .lit (.strVal s) => Pure.pure (some s)
        | _ =>
          match (← whnf symExpr).consumeMData with
          | .lit (.strVal s) => Pure.pure (some s)
          | _ => Pure.pure none
      if let some sym := sym? then
        let offExpr ← whnf (head.getArg! 3)
        if let some n := offExpr.rawNatLit? then
          rest := rest.push (sym, n)
        else if let some n ← evalNatLit? offExpr then
          rest := rest.push (sym, n)
    return rest
  return #[]

private partial def extractWordListNats (e : Expr) (acc : Array Nat := #[]) (fuel : Nat := 1024) :
    MetaM (Array Nat) := do
  if fuel == 0 then return acc
  let e := e.consumeMData
  if e.isAppOfArity ``List.cons 3 then
    if let some (_, w) ← evalBitVecLit? (e.getArg! 1) then
      return ← extractWordListNats (e.getArg! 2) (acc.push w) (fuel - 1)
    return acc
  else if e.isAppOfArity ``List.nil 1 then
    return acc
  else if e.isAppOfArity `Arm64.Obj.patchRelocs 4 then
    return ← extractWordListNats (e.getArg! 1) acc (fuel - 1)
  else if e.isConst then
    if let some e' ← unfoldDefinition? e then
      return ← extractWordListNats e' acc (fuel - 1)
    return acc
  else if e.isAppOfArity ``Arm64.FnCode.hex 1 then
    let inner := (e.getArg! 0).consumeMData
    if let some inner' ← (if inner.isConst then unfoldDefinition? inner else Pure.pure none) then
      let e' ← whnfCore (mkApp (mkConst ``Arm64.FnCode.hex) inner')
      if e' != e then
        return ← extractWordListNats e' acc (fuel - 1)
    let e' ← whnfCore e
    if e' != e then
      return ← extractWordListNats e' acc (fuel - 1)
    return acc
  else if let .proj ``Arm64.FnCode 1 inner := e then
    let inner := inner.consumeMData
    if let some inner' ← (if inner.isConst then unfoldDefinition? inner else Pure.pure none) then
      let e' ← whnfCore (.proj ``Arm64.FnCode 1 inner')
      if e' != e then
        return ← extractWordListNats e' acc (fuel - 1)
    return acc
  else
    if let some e' ← unfoldDefinition? e then
      return ← extractWordListNats e' acc (fuel - 1)
    let e' ← whnfCore e
    if e' != e then
      return ← extractWordListNats e' acc (fuel - 1)
    return acc

private structure CallDiagContext where
  codeConst? : Option Name := none
  bExpr? : Option Expr := none
  callerEntry? : Option (ProofLib.ProgramReflection.FnEntryInfo × Option Expr) := none
  lctxFnAddrs : Array (String × Expr) := #[]
  callerInitAddrs : Array Expr := #[]
  symTable : Array (String × Nat × Option Nat) := #[]
  lctxFnWords : Array (Option String × Option Expr × Option Nat × Array Nat) := #[]

private def stripAddrConstSuffix? (c : Name) : Option String := do
  let s := c.getString!
  if s.endsWith "_addr" && s.length > 5 then
    some ((s.take (s.length - 5)).toString)
  else if s.endsWith "_entry" && s.length > 6 then
    some ((s.take (s.length - 6)).toString)
  else
    none

private def buildCallDiagContext (progExpr : Expr) : TacticM CallDiagContext := do
  let g ← getMainGoal
  g.withContext do
    let env ← getEnv
    let imageConstToCodeConst? (imgConst : Name) : Option Name :=
      let s := imgConst.getString!
      if s.endsWith "Image" && s.length > 5 then
        let stem := (s.take (s.length - 5)).toString
        let cand := imgConst.getPrefix.str (stem ++ "Code")
        if env.contains cand then some cand else none
      else none
    let mut codeConst? : Option Name := none
    let mut bExpr? : Option Expr := none
    if let some (cConst, bExpr, _, _) ← extractRebase? progExpr then
      bExpr? := some bExpr
      if cConst != ``Obj.LinkedImage.toProgram then
        codeConst? := some cConst
      else
        let progUnw ← unwrapRebasedProgExpr progExpr
        if progUnw.isAppOfArity ``Program.rebase 4 then
          let codeExpr := (progUnw.getArg! 0).consumeMData
          if codeExpr.isAppOfArity ``Obj.LinkedImage.toProgram 1 then
            if let some imgConst := (codeExpr.getArg! 0).consumeMData.getAppFn.constName? then
              codeConst? := imageConstToCodeConst? imgConst
    else if let some c := progExpr.consumeMData.getAppFn.constName? then
      if env.contains c && c != ``Obj.LinkedImage.toProgram then
        codeConst? := some c
    let mut callerEntry? : Option (ProofLib.ProgramReflection.FnEntryInfo × Option Expr) := none
    let mut callerSymAndInit? : Option (String × Expr) := none
    let mut lctxFnAddrs : Array (String × Expr) := #[]
    let mut callerInitAddrs : Array Expr := #[]
    let mut rawFnWords : Array (Option String × Option Expr × Option Nat × Array Nat) := #[]
    for decl in (← getLCtx) do
      let ty ← instantiateMVars decl.type
      if codeConst?.isNone && ty.isAppOfArity ``Obj.Loads 2 then
        if let some imgConst := (ty.getArg! 0).consumeMData.getAppFn.constName? then
          if let some cand := imageConstToCodeConst? imgConst then
            codeConst? := some cand
      if let some (_, lhs, rhs) := ty.eq? then
        if let some sym ← extractFnAddrSym? lhs then
          lctxFnAddrs := lctxFnAddrs.push (sym, rhs)
        else if let some sym ← extractFnAddrSym? rhs then
          lctxFnAddrs := lctxFnAddrs.push (sym, lhs)
        if lhs.isAppOfArity ``State.pc 1 && (lhs.getArg! 0).isFVar then
          let rhsCons := rhs.consumeMData
          if rhsCons.isAppOf ``Program.fnAddr ||
             (rhsCons.isFVar && ((← getLCtx).find? rhsCons.fvarId!).any (·.userName == `entry)) then
            callerInitAddrs := callerInitAddrs.push rhsCons
          if callerEntry?.isNone then
            if let some sym ← extractFnAddrSym? rhsCons then
              if callerSymAndInit?.isNone then callerSymAndInit? := some (sym, rhsCons)
              if let some info := (ProofLib.ProgramReflection.lookupFnEntry? env sym codeConst?).orElse
                  (fun _ => ProofLib.ProgramReflection.lookupFnEntry? env sym none) then
                callerEntry? := some (info, some rhsCons)
                if codeConst?.isNone then codeConst? := some info.codeConst
      if ty.isAppOfArity ``Program.codeAt 3 then
        let sym? := match (ty.getArg! 1).consumeMData with
          | .lit (.strVal s) => some s
          | _ => none
        let ws ← extractWordListNats (ty.getArg! 2)
        if !ws.isEmpty then
          rawFnWords := rawFnWords.push (sym?, none, none, ws)
      else if ty.isAppOfArity ``Program.hasWords 3 || ty.isAppOfArity ``Program.hasCode 3 then
        let ws ← extractWordListNats (ty.getArg! 2)
        if !ws.isEmpty then
          let off? ← do
            if let some (64, v) ← evalBitVecLit? (ty.getArg! 1) then Pure.pure (some v)
            else Pure.pure none
          rawFnWords := rawFnWords.push (none, some (ty.getArg! 1), off?, ws)
      else if ty.isAppOfArity ``Program.hasWordsOff 3 then
        let ws ← extractWordListNats (ty.getArg! 2)
        if !ws.isEmpty then
          let off? ← evalNatLit? (ty.getArg! 1)
          rawFnWords := rawFnWords.push (none, none, off?, ws)
      if (ty.find? (·.isConstOf ``Arm64.subroutine_ok)).isSome ||
         (ty.find? (·.isConstOf ``Arm64.Program.subroutineOk)).isSome then
        let (_, _, body) ← forallMetaTelescope ty
        let bodyCons := body.consumeMData
        if bodyCons.isAppOfArity ``Arm64.subroutine_ok 4 then
          let addr := bodyCons.getArg! 2
          let spec := bodyCons.getArg! 3
          if let some sym ← extractFnAddrSym? addr then
            lctxFnAddrs := lctxFnAddrs.push (sym, addr)
          else if let some c := addr.consumeMData.getAppFn.constName? then
            if let some sym := stripAddrConstSuffix? c then
              lctxFnAddrs := lctxFnAddrs.push (sym, addr)
          else if let some sc := spec.consumeMData.getAppFn.constName? then
            if sc != ``Arm64.Spec.split && sc != ``Arm64.Spec.mk then
              lctxFnAddrs := lctxFnAddrs.push (sc.getString!, addr)
      if callerEntry?.isNone then
        if let some val := decl.value? then
          let val ← instantiateMVars val
          if let some sub := val.find? (·.isAppOfArity `ProofLib.fetch_eq_of_entry_eq_add 7) then
            let eFnAddr := sub.getArg! 1
            let entryFVar := sub.getArg! 2
            callerInitAddrs := callerInitAddrs.push entryFVar
            if let some sym ← extractFnAddrSym? eFnAddr then
              if callerSymAndInit?.isNone then callerSymAndInit? := some (sym, entryFVar)
              if let some info := (ProofLib.ProgramReflection.lookupFnEntry? env sym codeConst?).orElse
                  (fun _ => ProofLib.ProgramReflection.lookupFnEntry? env sym none) then
                callerEntry? := some (info, some entryFVar)
                if codeConst?.isNone then codeConst? := some info.codeConst
    let mut symTable : Array (String × Nat × Option Nat) := #[]
    if let some cConst := codeConst? then
      let codeEntries ← tryCatchRuntimeEx (do
        let fnEs ← ProofLib.CodeLookup.entries cConst .fnOff
        let stubEs ← ProofLib.CodeLookup.entries cConst .stubOff
        return fnEs ++ stubEs) (fun _ => Pure.pure #[])
      for entry in codeEntries do
        let sym := entry.sym
        let off := entry.val
        let sz? := (ProofLib.ProgramReflection.lookupFnEntryByOff? env cConst off).map
          ProofLib.ProgramReflection.FnEntryInfo.sizeBytes
        if !symTable.any (fun (s, o, _) => s == sym && o == off) then
          symTable := symTable.push (sym, off, sz?)
    let (tblPairs, progBaseOff?) ← tryCatchRuntimeEx (withHeartbeatCap 6000 do
      let progUnw ← unwrapRebasedProgExpr progExpr
      let mut pairs : Array (String × Nat) := #[]
      if let some (syms, stubs) ← extractProgTables? progUnw then
        pairs := (← collectTableSymOffs syms) ++ (← collectTableSymOffs stubs)
      let baseOff? ←
        if pairs.isEmpty then Pure.pure none
        else do
          let progBase ← whnf (mkApp (mkConst ``Program.base) progUnw)
          let (bb, ob) ← sepAddrBaseOff progBase
          if bb == toExpr (0#64) || (← evalBitVecLit? progBase).isSome then
            Pure.pure (some ob)
          else
            Pure.pure none
      return (pairs, baseOff?)) (fun _ => Pure.pure (#[], none))
    for (sym, off) in tblPairs do
      let sz? := codeConst?.bind fun cConst =>
        (ProofLib.ProgramReflection.lookupFnEntryByOff? env cConst off).map
          ProofLib.ProgramReflection.FnEntryInfo.sizeBytes
      if !symTable.any (fun (s, o, _) => s == sym && o == off) then
        symTable := symTable.push (sym, off, sz?)
      if bExpr?.isNone then
        if let some baseOff := progBaseOff? then
          if baseOff > 0 then
            let absOff := (baseOff + off) % (2 ^ 64)
            if !symTable.any (fun (s, o, _) => s == sym && o == absOff) then
              symTable := symTable.push (sym, absOff, sz?)
    let mut lctxFnWords : Array (Option String × Option Expr × Option Nat × Array Nat) := #[]
    for (sym?, addr?, off?, ws) in rawFnWords do
      let mut resolvedAddr? := addr?
      let mut resolvedOff? := off?
      if let some sym := sym? then
        if resolvedAddr?.isNone then
          if let some (_, rhs) := lctxFnAddrs.find? (fun (s, _) => s == sym) then
            let rhsNorm ← normAddrForDiag rhs
            resolvedAddr? := some rhsNorm
            if let some (64, v) ← evalBitVecLit? rhsNorm then
              resolvedOff? := some v
          else if let some (cSym, initExpr) := callerSymAndInit? then
            if cSym == sym then
              resolvedAddr? := some (← normAddrForDiag initExpr)
        if resolvedOff?.isNone then
          if let some (_, o, _) := symTable.find? (fun (s, _, _) => s == sym) then
            resolvedOff? := some o
      lctxFnWords := lctxFnWords.push (sym?, resolvedAddr?, resolvedOff?, ws)
    if callerEntry?.isNone then
      if let some (sym, initExpr) := callerSymAndInit? then
        if let some (_, off, sz?) := symTable.find? (fun (s, _, _) => s == sym) then
          callerEntry? := some ({
            sym := sym
            codeConst := codeConst?.getD .anonymous
            decPrefix := .anonymous
            fnOffLemma := .anonymous
            off := off
            sizeBytes := sz?.getD 0
          }, some initExpr)
    return { codeConst?, bExpr?, callerEntry?, lctxFnAddrs, callerInitAddrs, symTable, lctxFnWords }

private def describeCallAddress (ctx : CallDiagContext) (rawExpr normExpr : Expr)
    (extraSymHint? : Option String := none) :
    TacticM (String × Option Nat × Option (String × Nat) × Bool × Option String) := do
  let g ← getMainGoal
  let mut lctxMatchSym? : Option String := none
  for (sym, addrRhs) in ctx.lctxFnAddrs do
    let rhsNorm ← normAddrForDiag addrRhs
    let same ← g.withContext do
      Pure.pure (rhsNorm == normExpr) <||> withReducible (isDefEq rhsNorm normExpr)
    if same then
      lctxMatchSym? := some sym
      break
  g.withContext do
    let env ← getEnv
    let hexStr ← formatShortHexAddr normExpr
    let (base, offNat) ← sepAddrBaseOff normExpr
    let isZeroBase := base == toExpr (0#64) || (← evalBitVecLit? normExpr).isSome
    let canonOff? : Option Nat ← do
      if let some (64, v) ← evalBitVecLit? normExpr then
        Pure.pure (some v)
      else if isZeroBase then
        Pure.pure (some offNat)
      else
        let checkBExpr : MetaM (Option Nat) := do
          let some bExpr := ctx.bExpr? | return none
          if base == bExpr || (← withReducible (isDefEq base bExpr)) then
            return some offNat
          return none
        let checkCaller : MetaM (Option Nat) := do
          let some (cInfo, some entryFVar) := ctx.callerEntry? | return none
          if base == entryFVar || (← withReducible (isDefEq base entryFVar)) then
            return some ((cInfo.off + offNat) % (2 ^ 64))
          return none
        let checkBaseSym : MetaM (Option Nat) := do
          let some baseSym ← extractFnAddrSym? base | return none
          if let some baseInfo := (ProofLib.ProgramReflection.lookupFnEntry? env baseSym ctx.codeConst?).orElse
              (fun _ => ProofLib.ProgramReflection.lookupFnEntry? env baseSym none) then
            return some ((baseInfo.off + offNat) % (2 ^ 64))
          if let some (_, baseOff, _) := ctx.symTable.find? (fun (s, _, _) => s == baseSym) then
            return some ((baseOff + offNat) % (2 ^ 64))
          return none
        match ← checkBExpr with
        | some o => Pure.pure (some o)
        | none =>
          match ← checkCaller with
          | some o => Pure.pure (some o)
          | none => checkBaseSym
    let rawSym? ← do
      let (_, rawOff) ← sepAddrBaseOff rawExpr
      if rawOff == 0 then
        if let some s ← extractFnAddrSym? rawExpr then
          Pure.pure (some s)
        else if let some c := rawExpr.consumeMData.getAppFn.constName? then
          Pure.pure (stripAddrConstSuffix? c)
        else
          Pure.pure none
      else Pure.pure none
    let normSym? ← if offNat == 0 then extractFnAddrSym? normExpr else Pure.pure none
    let symHint? := rawSym?.orElse (fun _ => normSym?.orElse (fun _ => lctxMatchSym?.orElse (fun _ => extraSymHint?)))
    let regByOff? : Option ProofLib.ProgramReflection.FnEntryInfo :=
      match canonOff? with
      | some co =>
        match ctx.codeConst? with
        | some cConst =>
          (ProofLib.ProgramReflection.lookupFnEntryByOff? env cConst co).orElse fun _ =>
            (ProofLib.ProgramReflection.fnEntryExt.getState env).findRev? (·.off == co)
        | none =>
          (ProofLib.ProgramReflection.fnEntryExt.getState env).findRev? (·.off == co)
      | none => none
    let regInfo? : Option ProofLib.ProgramReflection.FnEntryInfo :=
      regByOff?.orElse fun _ =>
        match symHint? with
        | some s =>
          (ProofLib.ProgramReflection.lookupFnEntry? env s ctx.codeConst?).orElse
            (fun _ => ProofLib.ProgramReflection.lookupFnEntry? env s none)
        | none => none
    let tableByOff? : Option (String × Nat × Option Nat) :=
      match canonOff? with
      | some co => ctx.symTable.find? (fun (_, o, _) => o == co)
      | none => none
    let tableBySym? : Option (String × Nat × Option Nat) :=
      match symHint? with
      | some s => ctx.symTable.find? (fun (sym, _, _) => sym == s)
      | none => none
    let finalOff? : Option Nat :=
      canonOff?.orElse fun _ =>
        (regInfo?.map (·.off)).orElse fun _ =>
          (tableByOff?.map (·.2.1)).orElse fun _ =>
            tableBySym?.map (·.2.1)
    let resolvedSym? : Option String :=
      (regInfo?.map (·.sym)).orElse fun _ =>
        symHint?.orElse fun _ =>
          tableByOff?.map (·.1)
    let insideCaller? : Option (String × Nat) :=
      if regInfo?.isSome || tableByOff?.isSome then none
      else match canonOff? with
        | some co =>
          let foundReg? := (ProofLib.ProgramReflection.fnEntryExt.getState env).findRev? fun info =>
            ctx.codeConst?.all (· == info.codeConst) &&
            info.off < co && co < info.off + info.sizeBytes
          match foundReg?.map (fun info => (info.sym, co - info.off)) with
          | some r => some r
          | none =>
            match ctx.callerEntry? with
            | some (cInfo, _) =>
              if cInfo.off < co && (cInfo.sizeBytes == 0 || co < cInfo.off + cInfo.sizeBytes) &&
                 !ctx.symTable.any (fun (_, o, _) => cInfo.off < o && o <= co) then
                some (cInfo.sym, co - cInfo.off)
              else none
            | none => none
        | none => none
    let line := match regInfo? with
      | some info =>
        s!"{hexStr} (registered entry: \"{info.sym}\" at {toHexNat info.off})"
      | none =>
        match insideCaller? with
        | some (cSym, delta) =>
          let co := finalOff?.getD offNat
          s!"{hexStr} (offset {toHexNat co}, inside \"{cSym}\" + {toHexNat delta})"
        | none =>
          match symHint? with
          | some s =>
            match finalOff? with
            | some co =>
              if !isZeroBase then s!"{hexStr} (offset {toHexNat co}, callee: \"{s}\")"
              else s!"{hexStr} (callee: \"{s}\")"
            | none => s!"{hexStr} (callee: \"{s}\")"
          | none =>
            match tableByOff? with
            | some (tSym, co, _) =>
              s!"{hexStr} (symbol: \"{tSym}\" at {toHexNat co})"
            | none =>
              match finalOff? with
              | some co =>
                if !isZeroBase && co != offNat then s!"{hexStr} (offset {toHexNat co})"
                else hexStr
              | none => hexStr
    return (line, finalOff?, insideCaller?, regInfo?.isSome || tableByOff?.isSome, resolvedSym?)

private partial def lookupWordTreeAt? (t : Expr) (j : Nat) (fuel : Nat := 32) :
    MetaM (Option Nat) := do
  if fuel == 0 then return none
  let t := t.consumeMData
  if t.isAppOfArity ``ProofLib.ProgramReflection.WordTree.node 3 then
    let some lw ← evalNatLit? (t.getArg! 0) | return none
    if j < lw then
      lookupWordTreeAt? (t.getArg! 1) j (fuel - 1)
    else
      lookupWordTreeAt? (t.getArg! 2) (j - lw) (fuel - 1)
  else if t.isAppOfArity ``ProofLib.ProgramReflection.WordTree.leaf 4 && j == 0 then
    let some (_, b0) ← evalBitVecLit? (t.getArg! 0) | return none
    let some (_, b1) ← evalBitVecLit? (t.getArg! 1) | return none
    let some (_, b2) ← evalBitVecLit? (t.getArg! 2) | return none
    let some (_, b3) ← evalBitVecLit? (t.getArg! 3) | return none
    return some (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  else
    return none

private def isBlWord (w : Nat) : Bool :=
  (w &&& 0xfc000000) == 0x94000000 || (w &&& 0xfffffc1f) == 0xd63f0000

private def isRetWord (w : Nat) : Bool :=
  (w &&& 0xfffffc1f) == 0xd65f0000

private def lookupWordAtPc? (ctx : CallDiagContext) (lhsOff? : Option Nat) (lhsNorm : Expr) :
    MetaM (Option Nat) := do
  let (base, offNat) ← sepAddrBaseOff lhsNorm
  for (_, baseExpr?, fnOff?, ws) in ctx.lctxFnWords do
    let idx? : Option Nat ← do
      if let (some co, some fnOff) := (lhsOff?, fnOff?) then
        if fnOff <= co && (co - fnOff) % 4 == 0 && (co - fnOff) / 4 < ws.size then
          Pure.pure (some ((co - fnOff) / 4))
        else Pure.pure none
      else if let some bE := baseExpr? then
        if (base == bE || (← withReducible (isDefEq base bE))) &&
           offNat % 4 == 0 && offNat / 4 < ws.size then
          Pure.pure (some (offNat / 4))
        else Pure.pure none
      else Pure.pure none
    if let some idx := idx? then
      return some ws[idx]!
  if let (some co, some cConst) := (lhsOff?, ctx.codeConst?) then
    if co % 4 == 0 then
      if let some ci := (← getEnv).find? (cConst.appendAfter "_tree") then
        if let some treeVal := ci.value? then
          if let some w ← lookupWordTreeAt? treeVal (co / 4) then
            return some w
  return none

private def fmtAsmReg (w : RegWidth) : Reg → String
  | .gpr idx => (if w == .W64 then "x" else "w") ++ toString idx.toNat
  | .sp      => if w == .W64 then "sp" else "wsp"
  | .xzr     => if w == .W64 then "xzr" else "wzr"

private def fmtAsmSignedImm64 (off : BitVec 64) : String :=
  let sv := off.toInt
  let mag := sv.natAbs
  let sign := if sv < 0 then "-" else ""
  if mag < 1024 then s!"#{sign}{mag}" else s!"#{sign}{toHexNat mag}"

private def fmtAsmRelOff64 (off : BitVec 64) : String :=
  let sv := off.toInt
  let sign := if sv < 0 then "-" else "+"
  s!"{sign}{toHexNat sv.natAbs}"

private def fmtAsmCond : CondCode → String
  | .EQ => "eq" | .NE => "ne" | .CS => "cs" | .CC => "cc"
  | .MI => "mi" | .PL => "pl" | .VS => "vs" | .VC => "vc"
  | .HI => "hi" | .LS => "ls" | .GE => "ge" | .LT => "lt"
  | .GT => "gt" | .LE => "le" | .AL => "al" | .NV => "nv"

private def fmtAsmShift (sh : ShiftType) (amt : Nat) : String :=
  if amt == 0 then ""
  else
    let s := match sh with | .LSL => "lsl" | .LSR => "lsr" | .ASR => "asr" | .ROR => "ror"
    s!", {s} #{amt}"

private def fmtAsmAddrMode : AddrMode → String
  | .Offset base off | .UnscaledOffset base off =>
    if off == 0#64 then s!"[{fmtAsmReg .W64 base}]"
    else s!"[{fmtAsmReg .W64 base}, {fmtAsmSignedImm64 off}]"
  | .PreIndex base off =>
    s!"[{fmtAsmReg .W64 base}, {fmtAsmSignedImm64 off}]!"
  | .PostIndex base off =>
    s!"[{fmtAsmReg .W64 base}], {fmtAsmSignedImm64 off}"
  | .RegOffset base idx ext amt =>
    let idxW : RegWidth := match ext with
      | .UXTX | .SXTX => .W64
      | _ => .W32
    let extS := match ext with
      | .UXTB => "uxtb" | .UXTH => "uxth" | .UXTW => "uxtw" | .UXTX => "lsl"
      | .SXTB => "sxtb" | .SXTH => "sxth" | .SXTW => "sxtw" | .SXTX => "sxtx"
    if ext == .UXTX && amt == 0 then s!"[{fmtAsmReg .W64 base}, {fmtAsmReg .W64 idx}]"
    else if amt == 0 then s!"[{fmtAsmReg .W64 base}, {fmtAsmReg idxW idx}, {extS}]"
    else s!"[{fmtAsmReg .W64 base}, {fmtAsmReg idxW idx}, {extS} #{amt}]"

private def formatInstrAsm : Instr → String
  | .adr page rd off =>
    s!"{if page then "adrp" else "adr"} {fmtAsmReg .W64 rd}, {fmtAsmRelOff64 off}"
  | .addSubImm w op rd rn imm12 sh12 =>
    let immS := s!"#{if imm12.toNat < 1024 then toString imm12.toNat else toHexNat imm12.toNat}{if sh12 then ", lsl #12" else ""}"
    if op == .SUBS && rd == .xzr then s!"cmp {fmtAsmReg w rn}, {immS}"
    else if op == .ADDS && rd == .xzr then s!"cmn {fmtAsmReg w rn}, {immS}"
    else if op == .ADD && imm12 == 0#12 && !sh12 && (rd == .sp || rn == .sp) then
      s!"mov {fmtAsmReg w rd}, {fmtAsmReg w rn}"
    else
      let m := match op with | .ADD => "add" | .ADDS => "adds" | .SUB => "sub" | .SUBS => "subs"
      s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, {immS}"
  | .logicalImm w op rd rn mask =>
    let maskVal := if w == .W32 then mask.toNat % (2 ^ 32) else mask.toNat
    if op == .ANDS && rd == .xzr then s!"tst {fmtAsmReg w rn}, #{toHexNat maskVal}"
    else
      let m := match op with
        | .AND => "and" | .BIC => "bic" | .ORR => "orr" | .ORN => "orn"
        | .EOR => "eor" | .EON => "eon" | .ANDS => "ands" | .BICS => "bics"
      s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, #{toHexNat maskVal}"
  | .moveWide w op rd imm16 hw =>
    let m := match op with | .MOVN => "movn" | .MOVZ => "movz" | .MOVK => "movk"
    s!"{m} {fmtAsmReg w rd}, #{toHexNat imm16.toNat}{if hw == 0 then "" else s!", lsl #{hw}"}"
  | .bitfield w op rd rn immr imms =>
    if op == .UBFM && imms + 1 == w.bits then s!"lsr {fmtAsmReg w rd}, {fmtAsmReg w rn}, #{immr}"
    else if op == .SBFM && imms + 1 == w.bits then s!"asr {fmtAsmReg w rd}, {fmtAsmReg w rn}, #{immr}"
    else if op == .UBFM && immr == 0 && imms == 7 then s!"uxtb {fmtAsmReg .W32 rd}, {fmtAsmReg .W32 rn}"
    else if op == .UBFM && immr == 0 && imms == 15 then s!"uxth {fmtAsmReg .W32 rd}, {fmtAsmReg .W32 rn}"
    else if op == .SBFM && w == .W64 && immr == 0 && imms == 31 then s!"sxtw {fmtAsmReg .W64 rd}, {fmtAsmReg .W32 rn}"
    else
      let m := match op with | .SBFM => "sbfm" | .BFM => "bfm" | .UBFM => "ubfm"
      s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, #{immr}, #{imms}"
  | .extr w rd rn rm lsb =>
    if rn == rm then s!"ror {fmtAsmReg w rd}, {fmtAsmReg w rn}, #{lsb}"
    else s!"extr {fmtAsmReg w rd}, {fmtAsmReg w rn}, {fmtAsmReg w rm}, #{lsb}"
  | .b off => s!"b {fmtAsmRelOff64 off}"
  | .bl off => s!"bl {fmtAsmRelOff64 off}"
  | .bCond cond off => s!"b.{fmtAsmCond cond} {fmtAsmRelOff64 off}"
  | .cbz w nz rt off => s!"{if nz then "cbnz" else "cbz"} {fmtAsmReg w rt}, {fmtAsmRelOff64 off}"
  | .tbz w nz rt bit off => s!"{if nz then "tbnz" else "tbz"} {fmtAsmReg w rt}, #{bit}, {fmtAsmRelOff64 off}"
  | .br rn => s!"br {fmtAsmReg .W64 rn}"
  | .blr rn => s!"blr {fmtAsmReg .W64 rn}"
  | .ret rn => if rn == .gpr 30#5 then "ret" else s!"ret {fmtAsmReg .W64 rn}"
  | .nop => "nop"
  | .logicalShift w op rd rn rm sh amt =>
    if op == .ORR && rn == .xzr && amt == 0 then s!"mov {fmtAsmReg w rd}, {fmtAsmReg w rm}"
    else if op == .ANDS && rd == .xzr then s!"tst {fmtAsmReg w rn}, {fmtAsmReg w rm}{fmtAsmShift sh amt}"
    else
      let m := match op with
        | .AND => "and" | .BIC => "bic" | .ORR => "orr" | .ORN => "orn"
        | .EOR => "eor" | .EON => "eon" | .ANDS => "ands" | .BICS => "bics"
      s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, {fmtAsmReg w rm}{fmtAsmShift sh amt}"
  | .addSubShift w op rd rn rm sh amt =>
    if op == .SUBS && rd == .xzr then s!"cmp {fmtAsmReg w rn}, {fmtAsmReg w rm}{fmtAsmShift sh amt}"
    else if op == .ADDS && rd == .xzr then s!"cmn {fmtAsmReg w rn}, {fmtAsmReg w rm}{fmtAsmShift sh amt}"
    else if op == .SUB && rn == .xzr then s!"neg {fmtAsmReg w rd}, {fmtAsmReg w rm}{fmtAsmShift sh amt}"
    else
      let m := match op with | .ADD => "add" | .ADDS => "adds" | .SUB => "sub" | .SUBS => "subs"
      s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, {fmtAsmReg w rm}{fmtAsmShift sh amt}"
  | .addSubExt w op rd rn rm ext amt =>
    let idxW : RegWidth := match ext with | .UXTX | .SXTX => .W64 | _ => .W32
    let extS := match ext with
      | .UXTB => "uxtb" | .UXTH => "uxth" | .UXTW => "uxtw" | .UXTX => "uxtx"
      | .SXTB => "sxtb" | .SXTH => "sxth" | .SXTW => "sxtw" | .SXTX => "sxtx"
    let sfx := if amt == 0 then s!", {extS}" else s!", {extS} #{amt}"
    if op == .SUBS && rd == .xzr then s!"cmp {fmtAsmReg w rn}, {fmtAsmReg idxW rm}{sfx}"
    else
      let m := match op with | .ADD => "add" | .ADDS => "adds" | .SUB => "sub" | .SUBS => "subs"
      s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, {fmtAsmReg idxW rm}{sfx}"
  | .condSelect w op rd rn rm cond =>
    let m := match op with | .CSEL => "csel" | .CSINC => "csinc" | .CSINV => "csinv" | .CSNEG => "csneg"
    s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, {fmtAsmReg w rm}, {fmtAsmCond cond}"
  | .dataProc1 w op rd rn =>
    let m := match op with
      | .RBIT => "rbit" | .REV16 => "rev16" | .REV32 => "rev32"
      | .REV => "rev" | .CLZ => "clz" | .CLS => "cls"
    s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}"
  | .dataProc2 w op rd rn rm =>
    let m := match op with
      | .UDIV => "udiv" | .SDIV => "sdiv" | .LSLV => "lsl"
      | .LSRV => "lsr" | .ASRV => "asr" | .RORV => "ror"
    s!"{m} {fmtAsmReg w rd}, {fmtAsmReg w rn}, {fmtAsmReg w rm}"
  | .dataProc3 w op rd rn rm ra =>
    if op == .MADD && ra == .xzr then s!"mul {fmtAsmReg w rd}, {fmtAsmReg w rn}, {fmtAsmReg w rm}"
    else
      let m := match op with
        | .MADD => "madd" | .MSUB => "msub" | .SMADDL => "smaddl" | .SMSUBL => "smsubl"
        | .UMADDL => "umaddl" | .UMSUBL => "umsubl" | .SMULH => "smulh" | .UMULH => "umulh"
      let srcW := match op with | .SMADDL | .SMSUBL | .UMADDL | .UMSUBL => .W32 | _ => w
      if op == .SMULH || op == .UMULH then s!"{m} {fmtAsmReg .W64 rd}, {fmtAsmReg .W64 rn}, {fmtAsmReg .W64 rm}"
      else s!"{m} {fmtAsmReg w rd}, {fmtAsmReg srcW rn}, {fmtAsmReg srcW rm}, {fmtAsmReg w ra}"
  | .ldr w sz signed rt addr =>
    let unscaled := match addr with | .UnscaledOffset _ _ => true | _ => false
    let (m, rtW) : String × RegWidth := match sz, signed with
      | .B8,  false => (if unscaled then "ldurb" else "ldrb", .W32)
      | .B8,  true  => (if unscaled then "ldursb" else "ldrsb", w)
      | .H16, false => (if unscaled then "ldurh" else "ldrh", .W32)
      | .H16, true  => (if unscaled then "ldursh" else "ldrsh", w)
      | .W32, false => (if unscaled then "ldur" else "ldr", .W32)
      | .W32, true  => (if unscaled then "ldursw" else "ldrsw", .W64)
      | .X64, _     => (if unscaled then "ldur" else "ldr", .W64)
    s!"{m} {fmtAsmReg rtW rt}, {fmtAsmAddrMode addr}"
  | .ldrLit w signed rt off =>
    s!"{if signed then "ldrsw" else "ldr"} {fmtAsmReg (if signed then .W64 else w) rt}, {fmtAsmRelOff64 off}"
  | .str sz rt addr =>
    let unscaled := match addr with | .UnscaledOffset _ _ => true | _ => false
    let (m, rtW) : String × RegWidth := match sz with
      | .B8  => (if unscaled then "sturb" else "strb", .W32)
      | .H16 => (if unscaled then "sturh" else "strh", .W32)
      | .W32 => (if unscaled then "stur" else "str", .W32)
      | .X64 => (if unscaled then "stur" else "str", .W64)
    s!"{m} {fmtAsmReg rtW rt}, {fmtAsmAddrMode addr}"
  | .ldp w signed rt1 rt2 addr =>
    s!"{if signed then "ldpsw" else "ldp"} {fmtAsmReg w rt1}, {fmtAsmReg w rt2}, {fmtAsmAddrMode addr}"
  | .stp w rt1 rt2 addr =>
    s!"stp {fmtAsmReg w rt1}, {fmtAsmReg w rt2}, {fmtAsmAddrMode addr}"
  | .ldrSimd sz vt addr =>
    let pfx := match sz with | .B8 => "b" | .H16 => "h" | .S32 => "s" | .D64 => "d" | .Q128 => "q"
    s!"ldr {pfx}{vt.toNat}, {fmtAsmAddrMode addr}"
  | .strSimd sz vt addr =>
    let pfx := match sz with | .B8 => "b" | .H16 => "h" | .S32 => "s" | .D64 => "d" | .Q128 => "q"
    s!"str {pfx}{vt.toNat}, {fmtAsmAddrMode addr}"
  | .ldpSimd sz vt1 vt2 addr =>
    let pfx := match sz with | .B8 => "b" | .H16 => "h" | .S32 => "s" | .D64 => "d" | .Q128 => "q"
    s!"ldp {pfx}{vt1.toNat}, {pfx}{vt2.toNat}, {fmtAsmAddrMode addr}"
  | .stpSimd sz vt1 vt2 addr =>
    let pfx := match sz with | .B8 => "b" | .H16 => "h" | .S32 => "s" | .D64 => "d" | .Q128 => "q"
    s!"stp {pfx}{vt1.toNat}, {pfx}{vt2.toNat}, {fmtAsmAddrMode addr}"
  | .system isHalt imm =>
    s!"{if isHalt then "brk" else "svc"} #{toHexNat imm.toNat}"
  | .udf imm =>
    s!"udf #{toHexNat imm.toNat}"
  | other =>
    let r := reprStr other
    let tok := (r.splitOn " ").head?.getD r
    (tok.splitOn ".").getLast?.getD tok |>.toLower

private def countStepsToCall? (ctx : CallDiagContext) (lhsOff? : Option Nat) (lhsNorm : Expr)
    (isBlAtPc : Bool) : MetaM (Option Nat) := do
  if isBlAtPc then return some 1
  let (base, offNat) ← sepAddrBaseOff lhsNorm
  for (_, baseExpr?, fnOff?, ws) in ctx.lctxFnWords do
    let startIdx? : Option Nat ← do
      if let (some co, some fnOff) := (lhsOff?, fnOff?) then
        if fnOff <= co && (co - fnOff) % 4 == 0 && (co - fnOff) / 4 < ws.size then
          Pure.pure (some ((co - fnOff) / 4))
        else Pure.pure none
      else if let some bE := baseExpr? then
        if (base == bE || (← withReducible (isDefEq base bE))) &&
           offNat % 4 == 0 && offNat / 4 < ws.size then
          Pure.pure (some (offNat / 4))
        else Pure.pure none
      else Pure.pure none
    if let some startIdx := startIdx? then
      let maxK := Nat.min 64 (ws.size - 1 - startIdx)
      for k in [1:maxK + 1] do
        let w := ws[startIdx + k]!
        if isBlWord w then return some k
        if isRetWord w then break
  if let (some co, some cConst) := (lhsOff?, ctx.codeConst?) then
    if co % 4 == 0 then
      if let some ci := (← getEnv).find? (cConst.appendAfter "_tree") then
        if let some treeVal := ci.value? then
          let startWord := co / 4
          for k in [1:65] do
            let some w ← lookupWordTreeAt? treeVal (startWord + k) | break
            if isBlWord w then return some k
            if isRetWord w then break
  return none

private def extractRawCallAddr (e : Expr) : MetaM Expr := do
  let e := SepSolver.stripMData (← instantiateMVars e)
  if e.isAppOfArity ``State.pc 1 then
    let s := e.getArg! 0
    if let some (pc, _) ← provePcEq? s then
      return SepSolver.stripMData (← instantiateMVars pc)
    if s.isFVar then
      for decl in (← getLCtx) do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          let ty ← instantiateMVars decl.type
          if let some (_, lhs, rhs) := ty.eq? then
            if lhs.isAppOfArity ``State.pc 1 && lhs.getArg! 0 == s then
              return SepSolver.stripMData rhs
    extractSepWPPC s
  else
    Pure.pure e

private partial def openSubroutineOkType? (ty : Expr) (fuel : Nat := 6) :
    MetaM (Option (Array Expr × Array BinderInfo × Expr × Expr × Expr)) := do
  let (xs, bis, body) ← forallMetaTelescope ty
  let bodyCons := body.consumeMData
  if bodyCons.isAppOfArity ``Arm64.subroutine_ok 4 then
    return some (xs, bis, bodyCons.getArg! 1, bodyCons.getArg! 2, bodyCons.getArg! 3)
  if fuel == 0 then return none
  let bodyWhnf ← whnfCore (← instantiateMVars bodyCons)
  if bodyWhnf.isAppOfArity ``Arm64.subroutine_ok 4 then
    return some (xs, bis, bodyWhnf.getArg! 1, bodyWhnf.getArg! 2, bodyWhnf.getArg! 3)
  let some body' ← unfoldDefinition? bodyWhnf | return none
  let some (ys, bis', p, a, s) ← openSubroutineOkType? body' (fuel - 1) | return none
  return some (xs ++ ys, bis ++ bis', p, a, s)

private def findMatchingCalleeContract? (progExpr pcExpr : Expr)
    (excludeName? : Option Name := none) : TacticM (Option Ident) := do
  unless proofLib.wpCallRegistry.get (← getOptions) do
    return none
  let res? ← withoutModifyingState do
    tryTacticCatchRuntime <| withHeartbeatCap 10000 do
      let g ← getMainGoal
      let pcNorm ← normAddrForDiag pcExpr
      let checkType (ty : Expr) : TacticM Bool := do
        let ok? ← withoutModifyingState do
          tryTacticCatchRuntime <| withHeartbeatCap 4000 do
            let (xs, _, p, a, _) ← g.withContext do
              let some r ← openSubroutineOkType? ty | throwError "not sub_ok"
              Pure.pure r
            let progOk ← g.withContext do
              if ← isDefEq p progExpr then return true
              let pUnw ← unwrapRebasedProgExpr p
              let progUnw ← unwrapRebasedProgExpr progExpr
              isDefEq pUnw progUnw
            unless progOk do return false
            let mut candAddrs : Array Expr := #[]
            let aInst ← g.withContext (instantiateMVars a)
            if !aInst.hasMVar then
              candAddrs := candAddrs.push aInst
            else
              for x in xs do
                let xTy ← g.withContext (instantiateMVars (← inferType x))
                if let some (_, lhs, rhs) := xTy.eq? then
                  if lhs == aInst && !rhs.hasMVar then candAddrs := candAddrs.push rhs
                  else if rhs == aInst && !lhs.hasMVar then candAddrs := candAddrs.push lhs
            for ca in candAddrs do
              let caNorm ← normAddrForDiag ca
              let same ← g.withContext do
                if caNorm == pcNorm then return true
                if ← pcReachedTarget caNorm pcNorm then return true
                withReducible (isDefEq caNorm pcNorm)
              if same then return true
            return false
        return ok?.getD false
      let lctx ← g.withContext getLCtx
      for decl in lctx.decls.toList.reverse do
        let some decl := decl | continue
        if decl.isImplementationDetail || decl.isAuxDecl || decl.userName.hasMacroScopes then
          continue
        if excludeName? == some decl.userName then continue
        let dty ← g.withContext (instantiateMVars decl.type)
        if ← checkType dty then
          return some (mkIdent decl.userName)
      let env ← getEnv
      for declName in (calleeSpecExt.getState env).reverse do
        if excludeName? == some declName then continue
        if let some info := env.find? declName then
          if ← checkType info.type then
            return some (mkCIdent declName)
      return none
  return res?.join

private def throwCallTargetMismatchError (progExpr : Expr) (hcallStx? : Option Term)
    (gPc : MVarId) : TacticM Unit := do
  setGoals [gPc]
  let ty ← gPc.withContext (instantiateMVars (← gPc.getType))
  let some (_, lhsRaw, rhsRaw) := ty.eq?
    | do
      let s ← gPc.withContext (ppExprTruncated ty)
      throwError "wp_call: call target address does not match callee entry:\n  {s}\nhint: run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
  let hcallLabel : String :=
    match hcallStx? with
    | some hStx =>
      if hStx.raw.isIdent then hStx.raw.getId.toString
      else if hStx.raw.getNumArgs > 0 && hStx.raw[0]!.isIdent then hStx.raw[0]!.getId.toString
      else "h_callee"
    | none => "h_callee"
  let hcallSymHint? : Option String ← do
    match hcallStx? with
    | some hStx =>
      let res? ← tryTacticCatchRuntime do
        gPc.withContext do
          let hExpr ← elabTerm hStx none
          let hTy ← instantiateMVars (← inferType hExpr)
          if let some s ← extractFnAddrSym? hTy then
            return some s
          if let some strSub := hTy.find? (fun e => match e with | .lit (.strVal _) => true | _ => false) then
            if let .lit (.strVal s) := strSub then
              return some s
          return none
      Pure.pure res?.join
    | none => Pure.pure none
  let ctx ← buildCallDiagContext progExpr
  let lhsRawAddr ← gPc.withContext (extractRawCallAddr lhsRaw)
  let rhsRawAddr ← gPc.withContext (extractRawCallAddr rhsRaw)
  let lhsRawStr ← gPc.withContext (ppExprTruncated lhsRawAddr 160 12)
  let rhsRawStr ← gPc.withContext (ppExprTruncated rhsRawAddr 160 12)
  let rawLines :=
    if lhsRawStr == rhsRawStr && lhsRawAddr != rhsRawAddr then
      s!"\n  raw target PC:  {lhsRawStr} ({lhsRawAddr.dbgToString})\n  raw callee:     {rhsRawStr} ({rhsRawAddr.dbgToString})"
    else
      s!"\n  raw target PC:  {lhsRawStr}\n  raw callee:     {rhsRawStr}"
  let lhsNorm ← normAddrForDiag lhsRaw
  let rhsNorm ← normAddrForDiag rhsRaw
  let lhsHexStr ← gPc.withContext (formatShortHexAddr lhsNorm)
  let rhsHexStr ← gPc.withContext (formatShortHexAddr rhsNorm)
  let (lhsLine, lhsOff?, lhsInside?, lhsIsRegEntry, lhsSym?) ← describeCallAddress ctx lhsRaw lhsNorm none
  let (rhsLine0, rhsOff?, _, _, rhsSym?) ← describeCallAddress ctx rhsRaw rhsNorm hcallSymHint?
  let rhsHasMVar := rhsRawAddr.hasExprMVar || rhsNorm.hasExprMVar
  let rhsLine := if rhsHasMVar then s!"{rhsRawStr} (unresolved metavariable)" else rhsLine0
  let mut isAtCallerInit : Bool :=
    lhsNorm.isFVar && ((← gPc.withContext getLCtx).find? lhsNorm.fvarId!).any (·.userName == `entry)
  if !isAtCallerInit then
    for initAddr in ctx.callerInitAddrs do
      let initNorm ← normAddrForDiag initAddr
      let same ← gPc.withContext do
        Pure.pure (initNorm == lhsNorm) <||> withReducible (isDefEq initNorm lhsNorm)
      if same then
        isAtCallerInit := true
        break
  let instOpt ← evalFetchDecodeDiag? progExpr lhsRawAddr
  let wordDecodedInst? : Option Instr ← do
    let w? ← gPc.withContext (lookupWordAtPc? ctx lhsOff? lhsNorm)
    Pure.pure (w?.bind fun w => Arm64.decode (BitVec.ofNat 32 w))
  let haltedMnem? : Option String ← do
    if let some decInst := wordDecodedInst? then
      Pure.pure (some (formatInstrAsm decInst))
    else if let some instExpr := instOpt then
      let s ← gPc.withContext (ppExprTruncated instExpr 72 6)
      Pure.pure (some s)
    else
      Pure.pure none
  let mut callerInsnLine : String := ""
  let mut callerInsnHint? : Option String := none
  let mut isBlAtPc : Bool := false
  if let some instExpr := instOpt then
    let opExpr := instExpr
    let isBl := opExpr.isAppOfArity ``Instr.bl 1 || opExpr.isAppOfArity ``Instr.blr 1
    isBlAtPc := isBl
    if isBl || isAtCallerInit || lhsInside?.isSome || (!lhsIsRegEntry && lhsSym?.isNone) then
      let opStr ← gPc.withContext (ppExprTruncated opExpr 120 8)
      if opExpr.isAppOfArity ``Instr.bl 1 then
        let blTgtStr? ← tryTacticCatchRuntime do
          let addE ← gPc.withContext (mkAppM ``HAdd.hAdd #[lhsNorm, opExpr.getArg! 0])
          let tgtNorm ← normAddrForDiag addE
          gPc.withContext (formatShortHexAddr tgtNorm)
        match blTgtStr? with
        | some tgtStr =>
          callerInsnLine := s!"\n  caller insn:    {opStr} (branch target: {tgtStr})"
          callerInsnHint? := some s!"\nhint: execution is currently stopped at caller instruction `{opStr}` at `{lhsHexStr}` (`s.pc` is at the `BL` instruction itself targeting `{tgtStr}` rather than stepped into the call); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
        | none =>
          callerInsnLine := s!"\n  caller insn:    {opStr}"
          callerInsnHint? := some s!"\nhint: execution is currently stopped at caller instruction `{opStr}` at `{lhsHexStr}` (`s.pc` is at the `BL` instruction itself rather than stepped into the call); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
      else
        callerInsnLine := s!"\n  caller insn:    {opStr}"
        callerInsnHint? := some s!"\nhint: execution is currently stopped at caller instruction `{opStr}` at `{lhsHexStr}` (`wp_steps` / `wp_sym_steps` stopped early before reaching the call target); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
  else if let some decInst := wordDecodedInst? then
    let isBl := match decInst with | .bl _ | .blr _ => true | _ => false
    isBlAtPc := isBl
    if isBl || isAtCallerInit || lhsInside?.isSome || (!lhsIsRegEntry && lhsSym?.isNone) then
      let mnem := formatInstrAsm decInst
      callerInsnLine := s!"\n  caller insn:    {mnem}"
      if isBl then
        callerInsnHint? := some s!"\nhint: execution is currently stopped at caller instruction `{mnem}` at `{lhsHexStr}` (`s.pc` is at the call instruction itself rather than stepped into the call); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
      else
        callerInsnHint? := some s!"\nhint: execution is currently stopped at caller instruction `{mnem}` at `{lhsHexStr}` (`wp_steps` / `wp_sym_steps` stopped early before reaching the call target); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
  let excludeNm? := hcallStx?.bind fun h => if h.raw.isIdent then some h.raw.getId else none
  let matchContractId? ← findMatchingCalleeContract? progExpr lhsRawAddr excludeNm?
  let matchSuffix := match matchContractId? with
    | some mId => s!"; did you mean `wp_call {mId.getId}`?"
    | none => ""
  let isStoppedEarly := !rhsHasMVar && (callerInsnHint?.isSome || isAtCallerInit || lhsInside?.isSome)
  let stepsToCall? ←
    if isStoppedEarly then gPc.withContext (countStepsToCall? ctx lhsOff? lhsNorm isBlAtPc)
    else Pure.pure none
  let formatShortEndpoint (hexStr : String) (sym? : Option String) : String :=
    match sym? with
    | some s => s!"{hexStr} (\"{s}\")"
    | none => hexStr
  let expShort := formatShortEndpoint lhsHexStr lhsSym?
  let gotShort := formatShortEndpoint rhsHexStr rhsSym?
  let sameOff? : Option Nat :=
    match lhsOff?, rhsOff? with
    | some lo, some ro => if lo == ro then some lo else none
    | _, _ => none
  let verdict : String :=
    if rhsHasMVar then
      s!"callee entry is an unresolved metavariable ({rhsRawStr}); instantiate or pass the callee entry address explicitly"
    else if let some lo := sameOff? then
      s!"call target and {hcallLabel} both refer to offset {toHexNat lo}, but use different base expressions ({expShort} vs {gotShort})"
    else if isStoppedEarly then
      match haltedMnem?, stepsToCall? with
      | some mnem, some n =>
        let insnWord := if n == 1 then "instruction" else "instructions"
        s!"stepping stopped early (halted at {lhsHexStr} ({mnem}), {n} {insnWord} before the call)"
      | some mnem, none =>
        s!"stepping stopped early (halted at {lhsHexStr} ({mnem}) before the call)"
      | none, some n =>
        let insnWord := if n == 1 then "instruction" else "instructions"
        s!"stepping stopped early (pc is still {n} {insnWord} before the call)"
      | none, none =>
        s!"stepping stopped early (pc is still at {lhsHexStr} before the call)"
    else
      s!"{hcallLabel} is the wrong contract (expected entry {expShort} / got {gotShort})"
  let defaultCallerOrSiteHint :=
    if rhsHasMVar then
      s!"\nhint: the callee contract's entry address contains an unresolved metavariable (`{rhsRawStr}`); pass the entry address argument explicitly to `{hcallLabel}` (e.g. `wp_call ({hcallLabel} <entry_addr>)`) or supply a local `prog.fnAddr \"<callee>\" = ...` / `Obj.Loads` hypothesis{matchSuffix}"
    else
      match callerInsnHint? with
      | some h => h
      | none =>
        match lhsInside? with
        | some (cSym, delta) =>
          s!"\nhint: execution is currently stopped inside caller \"{cSym}\" (+{toHexNat delta}) at `{lhsHexStr}`, not at a callee entry (`wp_steps` / `wp_sym_steps` stopped early before reaching the call target); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
        | none =>
          if isAtCallerInit then
            s!"\nhint: execution is currently stopped at caller entry `{lhsHexStr}` (`wp_steps` / `wp_sym_steps` stopped early before reaching the call target); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped"
          else
            s!"\nhint: ensure execution has stepped to the `BL` call site (`wp_steps` / `wp_sym_steps`) and pass the contract matching the call target PC{matchSuffix}"
  let hint :=
    match sameOff? with
    | some lo =>
      s!"\nhint: both addresses refer to offset {toHexNat lo}, but `entry` was generalized by `wp_entry`; introduce the callee hypothesis before `wp_entry` (or rewrite its entry relative to `entry`)"
    | none =>
      defaultCallerOrSiteHint
  throwError "wp_call: call target address does not match callee entry: {verdict}\n  call target PC: {lhsLine}\n  callee entry:   {rhsLine}{rawLines}{callerInsnLine}{hint}"

-- Stage 1 evaluates ground `Nat`/`BitVec` subterms via default-transparency `whnf` under a
-- heartbeat cap so large table lookups fall through to `wp_norm_goal` equation rewrites.
private def closeCallAddrEqSubgoal (g : MVarId) (preferGoal : Bool) : TacticM Bool := do
  setGoals [g]
  let fast? ← tryTacticCatchRuntime <| withHeartbeatCap 5000 <| g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq? | return (false, false)
    if rhs.hasMVar then return (false, false)
    let (lhsAddr, hPc?) ← do
      if lhs.isAppOfArity ``State.pc 1 then
        let s := lhs.getArg! 0
        if let some (pc, prf) ← provePcEq? s then
          Pure.pure (pc, some prf)
        else if s.isFVar then
          let mut found : Option (Expr × Expr) := none
          for decl in (← getLCtx) do
            if !decl.isImplementationDetail && !decl.isAuxDecl then
              let dty ← instantiateMVars decl.type
              if let some (_, l, r) := dty.eq? then
                if l.isAppOfArity ``State.pc 1 && l.getArg! 0 == s then
                  found := some (r, decl.toExpr)
                  break
          match found with
          | some (pc, prf) => Pure.pure (pc, some prf)
          | none => Pure.pure (lhs, none)
        else
          Pure.pure (lhs, none)
      else
        Pure.pure (lhs, none)
    if let some hAddr ← proveSepAddrEqMeta? lhsAddr rhs then
      let prf ← match hPc? with
        | some hp => mkEqTrans hp hAddr
        | none => Pure.pure hAddr
      g.assign (← mkExpectedTypeHint prf ty)
      return (true, false)
    let (lhsNorm0, _) ← SepSolver.normAddrMeta lhsAddr
    let (rhsNorm0, _) ← SepSolver.normAddrMeta rhs
    -- Literal-offset-only decomposition: a ground non-numeral offset stays in the base instead of
    -- being evaluated by `whnf`, so this "definitely different" check never unfolds definitions.
    let (b1, o1) := sepAddrBaseOffPure lhsNorm0
    let (b2, o2) := sepAddrBaseOffPure rhsNorm0
    if o1 != o2 && (b1 == b2 || (← withReducible (isDefEq b1 b2))) then
      return (false, true)
    return (false, false)
  let (closedFastMeta, distinctFastMeta) := fast?.getD (false, false)
  if closedFastMeta then
    replaceMainGoal []
    return true
  if distinctFastMeta then
    return false
  let saved ← saveState
  let closer ← if preferGoal then
      `(tactic| wp_focus_close (first | wp_norm_goal | wp_norm_lhs))
    else
      `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  if ← tryTacticCatchRuntimeBool (evalTactic closer) then
    return true
  saved.restore
  setGoals [g]
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_norm_goal)))
  if (← getGoals).isEmpty then
    return true
  let g1 ← getMainGoal
  let closedAfterNorm ← g1.withContext do
    let ty ← instantiateMVars (← g1.getType)
    let some (_, lhs, rhs) := ty.eq? | return false
    if !rhs.hasMVar then
      if let some prf ← proveSepAddrEqMeta? lhs rhs then
        g1.assign (← mkExpectedTypeHint prf ty)
        return true
    let (lhsNorm, hLhs?) ← SepSolver.normAddrMeta lhs
    let (rhsNorm, hRhs?) ← SepSolver.normAddrMeta rhs
    if !rhs.hasMVar && (lhsNorm == rhsNorm || (← withReducibleAndInstances (isDefEq lhsNorm rhsNorm))) then
      let hLhs ← match hLhs? with | some p => Pure.pure p | none => mkEqRefl lhs
      let hRhs ← match hRhs? with | some p => Pure.pure p | none => mkEqRefl rhs
      let prf ← mkEqTrans hLhs (← mkEqSymm hRhs)
      g1.assign (← mkExpectedTypeHint prf ty)
      return true
    return false
  if closedAfterNorm then
    replaceMainGoal []
    return true
  saved.restore
  setGoals [g]
  return false

private def formatSpAlignFailHint (gSp : MVarId) : TacticM String := do
  let res? ← withoutModifyingState do
    tryTacticCatchRuntime <| withHeartbeatCap 8000 do
      let ty ← gSp.withContext (instantiateMVars (← gSp.getType))
      let mut spExpr? : Option Expr := none
      if let some (_, lhs, _) := ty.eq? then
        let lhs := lhs.consumeMData
        if lhs.isAppOfArity ``State.spAligned 1 then
          spExpr? := some (mkApp (mkConst ``State.sp) (lhs.getArg! 0))
        else if lhs.isAppOfArity ``BEq.beq 4 && (lhs.getArg! 2).consumeMData.isAppOfArity ``HAnd.hAnd 6 then
          spExpr? := some ((lhs.getArg! 2).consumeMData.getArg! 4)
        else if let some spSub := lhs.find? (·.isAppOfArity ``State.sp 1) then
          spExpr? := some spSub
      let some spExpr := spExpr? | return ""
      let spNorm ← normAddrForDiag spExpr
      let (baseExpr, offNat) ← gSp.withContext (sepAddrBaseOff spNorm)
      let signedMag := if offNat >= 2 ^ 63 then 2 ^ 64 - offNat else offNat
      let baseStateStr ← gSp.withContext do
        if baseExpr.isAppOfArity ``State.sp 1 then
          ppExprTruncated (baseExpr.getArg! 0) 40 4
        else
          Pure.pure "s0"
      if signedMag % 16 == 0 then
        return s!"\nhint: offset {signedMag} is 16-byte aligned, so initial alignment `hsp : {baseStateStr}.spAligned = true` (or `({baseStateStr}.sp &&& 15#64 == 0#64) = true`) is likely missing from local hypotheses / loop invariant"
      else
        return s!"\nhint: stack offset {signedMag} is not a multiple of 16"
  return res?.getD ""

private partial def collectSpAlignConjunctProofs (prf : Expr) (ty : Expr) (fuel : Nat := 8) :
    MetaM (Array (Expr × Expr)) := do
  if fuel == 0 then return #[]
  let ty := (← instantiateMVars ty).consumeMData
  if ty.isAppOfArity ``And 2 then
    let p1 := ty.getArg! 0
    let p2 := ty.getArg! 1
    let a1 ← collectSpAlignConjunctProofs (mkApp3 (mkConst ``And.left) p1 p2 prf) p1 (fuel - 1)
    let a2 ← collectSpAlignConjunctProofs (mkApp3 (mkConst ``And.right) p1 p2 prf) p2 (fuel - 1)
    return a1 ++ a2
  let mentionsSp := (ty.find? fun sub =>
    sub.isConstOf ``State.spAligned || sub.isConstOf ``State.sp || sub.isConstOf ``Reg.sp ||
    evalBitVecLitPure? sub == some (64, 15)).isSome
  if mentionsSp && ty.isAppOfArity ``Eq 3 then
    return #[(ty, prf)]
  return #[]

private def tryCloseSpAlignedAuto (gSp : MVarId) : TacticM Bool := do
  unless proofLib.wpCallAutoSpAlign.get (← getOptions) do
    return false
  let worthTrying ← withoutModifyingState do
    let res? ← tryTacticCatchRuntime <| withHeartbeatCap 6000 do
      let ty ← gSp.withContext (instantiateMVars (← gSp.getType))
      let mut spExpr? : Option Expr := none
      if let some (_, lhs, _) := ty.eq? then
        let lhs := lhs.consumeMData
        if lhs.isAppOfArity ``State.spAligned 1 then
          spExpr? := some (mkApp (mkConst ``State.sp) (lhs.getArg! 0))
        else if let some spSub := lhs.find? (·.isAppOfArity ``State.sp 1) then
          spExpr? := some spSub
      let some spExpr := spExpr? | return false
      let spNorm ← normAddrForDiag spExpr
      let (_, offNat) ← gSp.withContext (sepAddrBaseOff spNorm)
      if offNat % 16 != 0 then return false
      let hasBaseAlign ← gSp.withContext do
        for decl in ← getLCtx do
          if !decl.isImplementationDetail && !decl.isAuxDecl then
            let dty ← instantiateMVars decl.type
            if (dty.find? fun sub =>
                sub.isConstOf ``State.spAligned ||
                evalBitVecLitPure? sub == some (64, 15)).isSome then
              return true
        return false
      return hasBaseAlign
    return res?.getD false
  unless worthTrying do return false
  let saved ← saveState
  let ok ← tryTacticCatchRuntimeBool <| withHeartbeatCap 25000 do
    setGoals [gSp]
    let extraFacts ← gSp.withContext do
      let mut out : Array (Expr × Expr) := #[]
      for decl in ← getLCtx do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          let dty ← instantiateMVars decl.type
          if dty.consumeMData.isAppOfArity ``And 2 then
            out := out ++ (← collectSpAlignConjunctProofs decl.toExpr dty)
      return out
    let mut gCur := gSp
    for (fTy, fPrf) in extraFacts do
      let nm ← gCur.withContext do return (← getLCtx).getUnusedName `_h_sp_fact
      let g' ← gCur.assert nm fTy fPrf
      let (_, g'') ← g'.intro1P
      gCur := g''
    setGoals [gCur]
    let (_, hypIds) ← gCur.withContext getLightweightSimpHyps
    evalTactic (← `(tactic| (
      try simp (config := { decide := true }) only [
        State.spAligned, State.readReg64, beq_iff_eq,
        wp_norm, arm64_norm, $[$hypIds:ident],*] at *
      first
        | done
        | with_reducible rfl
        | assumption
        | decide
        | (bv_robdd; done)
        | (bv_bits; done)
        | (bv_omega_fast; done))))
    unless (← getGoals).isEmpty do throwError "unsolved"
  if ok then
    return true
  saved.restore (restoreInfo := true)
  setGoals [gSp]
  return false

private def closeCallSiteSetupSubgoals (progExpr : Expr) (hcallStx? : Option Term := none) :
    TacticM Unit := do
  let gs ← getGoals
  let gPc :: gRun :: gSp :: gLr :: rest := gs
    | throwError "wp_call: unexpected subgoals after applying call lemma"
  if !(← closeCallAddrEqSubgoal gPc (preferGoal := true)) then
    throwCallTargetMismatchError progExpr hcallStx? gPc
  setGoals [gRun]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_norm_lhs)))) then
    let s ← gRun.withContext do ppExprTruncated (← instantiateMVars (← gRun.getType))
    throwError "wp_call: failed to prove machine status is `.Running`:\n  {s}"
  setGoals [gSp]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) &&
     !(← tryCloseSpAlignedAuto gSp) then
    let s ← gSp.withContext do ppExprTruncated (← instantiateMVars (← gSp.getType))
    let spHint ← formatSpAlignFailHint gSp
    throwError "wp_call: failed to prove 16-byte stack pointer alignment (`s.spAligned = true`):\n  {s}{spHint}"
  if !(← closeCallAddrEqSubgoal gLr (preferGoal := false)) then
    let s ← gLr.withContext do ppExprTruncated (← instantiateMVars (← gLr.getType))
    throwError "wp_call: failed to resolve link register (`s.readReg64 .lr = ret_pc`):\n  {s}"
  setGoals (← rest.filterM fun m => not <$> m.isAssigned)

syntax wppCallNamedX := atomic("(" &"x" " := " term ")")
syntax wppCallNamedPanic := atomic("(" &"on_panic" " := " term ")")

/-- Optional arguments to `wpp_call`, `wpp_call_frozen`, and `wp_call`:
    - `(x := term)` or positional `term:max` for the callee ghost argument `x`,
    - `(on_panic := term)` for a custom panic obligation proof. -/
syntax wppCallOpt := wppCallNamedX <|> wppCallNamedPanic <|> term:max

private def parseWppCallOpts (opts : Array (TSyntax ``wppCallOpt)) :
    TacticM (Option Term × Option Term) := do
  let mut arg? : Option Term := none
  let mut onPanic? : Option Term := none
  for opt in opts do
    match opt with
    | `(wppCallOpt| $nx:wppCallNamedX) =>
      let `(wppCallNamedX| (x := $t:term)) := nx | Pure.pure ()
      if arg?.isSome then
        throwError "wpp_call: duplicate ghost argument `(x := ...)`"
      arg? := some t
    | `(wppCallOpt| $np:wppCallNamedPanic) =>
      let `(wppCallNamedPanic| (on_panic := $p:term)) := np | Pure.pure ()
      if onPanic?.isSome then
        throwError "wpp_call: duplicate `(on_panic := ...)` argument"
      onPanic? := some p
    | `(wppCallOpt| $t:term) =>
      if arg?.isSome then
        throwError "wpp_call: unexpected extra positional argument `{t}`"
      arg? := some t
    | _ => Pure.pure ()
  return (arg?, onPanic?)

private def isContinuationInvHypType (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``Obj.Image.FrozenLoaded 2 ||
     e.isAppOfArity ``Obj.Image.CallInv 2 ||
     e.isAppOfArity ``Memory.KeepsFrozen 2 then
    true
  else if let some (_, lhs, rhs) := e.eq? then
    lhs.isAppOfArity ``State.symtab 1 || rhs.isAppOfArity ``State.symtab 1 ||
    lhs.isAppOfArity ``Obj.Image.symtab 1 || rhs.isAppOfArity ``Obj.Image.symtab 1
  else
    false

/-- If the current goal is a `SepWP prog mid s P post oom` segment produced by `SepWPp.of_sepWP`,
    `SepWPp.of_sepWP_frozen`, or `SepWP.of_sepWP_frozen` whose continuation `post` enters `SepWPp`
    (or `SepWP` with frozen invariants) and `s.pc` has reached `mid` (or `mid` is an unassigned
    metavariable), automatically transition to the continuation via `SepWP.done` and introduce any
    leading `FrozenLoaded` / `symtab` / `CallInv` hypotheses. -/
def transitionToContinuationGoalIfReady (forWppCall : Bool := false) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  let shouldTransition ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    unless ty.isAppOfArity ``SepWP 6 do return false
    let midExpr := ty.getArg! 1
    let sExpr := ty.getArg! 2
    let postExpr := (ty.getArg! 4).consumeMData
    unless postExpr.isLambda do return false
    let body1 := postExpr.bindingBody!.consumeMData
    unless body1.isLambda do return false
    let body2 := body1.bindingBody!.consumeMData
    let retHead := body2.getForallBody.consumeMData
    let isWPpCont := retHead.isAppOfArity ``SepWPp 7
    let isWPContWithInv :=
      retHead.isAppOfArity ``SepWP 6 &&
      match body2 with
      | .forallE _ dom _ _ => isContinuationInvHypType dom
      | _ => false
    unless isWPpCont || isWPContWithInv do return false
    if forWppCall && isWPpCont then return true
    if midExpr.hasMVar then return true
    let pcExpr ← extractSepWPPC sExpr
    pcReachedTarget pcExpr midExpr
  if !shouldTransition then return
  let ok ← tryTacticCatchRuntimeBool do
    evalTactic (← `(tactic| (
      apply SepWP.done
      wp_focus_close (first | wp_norm_lhs | wp_norm_goal | rfl)
      wp_focus_close wp_norm_lhs
    )))
  if !ok then return
  betaReduceTarget
  for _ in [0:8] do
    if (← getGoals).isEmpty then return
    let gCur ← getMainGoal
    let introName? ← gCur.withContext do
      let ty := (← instantiateMVars (← gCur.getType)).consumeMData
      if let .forallE _ dom body _ := ty then
        if !body.hasLooseBVars && isContinuationInvHypType dom then
          let dom := dom.consumeMData
          if dom.isAppOfArity ``Obj.Image.FrozenLoaded 2 then
            return some `hfz_m
          else if dom.isAppOfArity ``Obj.Image.CallInv 2 then
            return some `hinv_m
          else if dom.isAppOfArity ``Memory.KeepsFrozen 2 then
            return some `hkeep_m
          else
            return some `hsym_m
      return none
    let some baseName := introName? | break
    let hId ← freshIdent baseName
    evalTactic (← `(tactic| intro $hId:ident))
    betaReduceTarget

private def stepBLInGoalIfAtBL : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let (isWP, isWPp, atBL) ← withoutModifyingState do
    let res? ← tryTacticCatchRuntime do
      let g ← getMainGoal
      let ty ← g.withContext (instantiateMVars (← g.getType))
      let ty := ty.consumeMData
      let isWP := ty.isAppOfArity ``SepWP 6
      let isWPp := ty.isAppOfArity ``SepWPp 7
      if !isWP && !isWPp then return (false, false, false)
      let (progExpr, _, pcExpr) ← getSepWPOrWPpStateAndPC
      let isBL ← g.withContext do
        let instMVar ← mkFreshExprMVar (mkConst ``Instr)
        let someInst ← mkAppM ``Option.some #[instMVar]
        let fetchGoalTy ← mkEq (mkApp2 (mkConst ``Program.fetch) progExpr pcExpr) someInst
        let fetchGoal ← mkFreshExprMVar fetchGoalTy
        setGoals [fetchGoal.mvarId!]
        -- Nested `else do` blocks keep the fallbacks lazy (the conditions of an `if ... else if ← c`
        -- term are hoisted and run before the `if`).
        let ok ←
          if ← tryCloseFetchFromHasCode then Pure.pure true
          else do
          if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_assumption))) then Pure.pure true
          else do
          if !(← fastProgFetchNone? progExpr pcExpr) then
            tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (
              (conv => lhs; simp (config := { decide := true }) only [arm64_norm]); rfl))))
          else Pure.pure false
        if !ok then return false
        let instExpr ← instantiateMVars instMVar
        return instExpr.isAppOfArity ``Instr.bl 1
      return (isWP, isWPp, isBL)
    return res?.getD (false, false, false)
  if !atBL then return
  if isWP then
    let _ ← tryTacticCatchRuntime (wpStepCoreWithOutcome none)
  else if isWPp then
    let _ ← tryTacticCatchRuntimeBool do
      evalTactic (← `(tactic| (
        apply SepWPp.step_pure
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal none
      evalTactic (← `(tactic| (
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))

private def resolveCallContractTerm (hcall : Term) (progExpr pcExpr : Expr) : TacticM Term := do
  let g ← getMainGoal
  let hInfo? ← tryTacticCatchRuntime do
    g.withContext do
      let e ← elabTerm hcall none
      let ty ← instantiateMVars (← inferType e)
      return (e, ty)
  let some (hExpr, hTy) := hInfo? | return hcall
  let isHookOk := hTy.isAppOfArity ``Arm64.HookOk 3
  let isHookSat := hTy.isAppOfArity ``Arm64.HookSat 4
  if isHookOk || isHookSat then
    let progUnwrapped ← unwrapRebasedProgExpr progExpr
    let rawProgIdentOpt : Option Ident :=
      if progUnwrapped.getAppFn.isConstOf ``Arm64.Program.rebase && progUnwrapped.getAppNumArgs ≥ 1 then
        let rawFn := (progUnwrapped.getArg! 0).getAppFn
        if rawFn.isConst then some (mkIdent rawFn.constName!) else none
      else if progUnwrapped.getAppFn.isConst then
        some (mkIdent progUnwrapped.getAppFn.constName!)
      else none
    let specExpr := if isHookSat then hTy.getArg! 3 else hTy.getArg! 2
    let subId ← freshIdent `_hcall_sub
    if isHookSat then
      evalTactic (← `(tactic| obtain ⟨_f_hook, _hf_hook, _hok_hook⟩ := $hcall))
      let gAfterObtain ← getMainGoal
      let (progStx, pcStx, specStx) ← gAfterObtain.withContext do
        pure (← Term.exprToSyntax (← instantiateMVars progExpr),
              ← Term.exprToSyntax (← instantiateMVars pcExpr),
              ← Term.exprToSyntax (← instantiateMVars specExpr))
      match rawProgIdentOpt with
      | some rawId =>
        evalTactic (← `(tactic| (
          have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
            apply ProofLib.subroutine_ok_outcome_intro
            intro _x _R _s0 _hpc _hrun _hpre _hsp
            obtain ⟨_hkeep, _hsym, _hout⟩ := _hok_hook _x _R _s0 _hrun _hpre _hsp
            refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
            rw [_hpc]
            try simp only [wp_unfold]
            try simp (config := { decide := true }) only [wp_norm, arm64_norm, _hf_hook]
            try simp (config := { decide := true }) only [
              Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
              BitVec.sub_self,
              $rawId:ident, wp_norm, arm64_norm, _hf_hook]
        )))
      | none =>
        evalTactic (← `(tactic| (
          have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
            apply ProofLib.subroutine_ok_outcome_intro
            intro _x _R _s0 _hpc _hrun _hpre _hsp
            obtain ⟨_hkeep, _hsym, _hout⟩ := _hok_hook _x _R _s0 _hrun _hpre _hsp
            refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
            rw [_hpc]
            try simp only [wp_unfold]
            try simp (config := { decide := true }) only [wp_norm, arm64_norm, _hf_hook]
            try simp (config := { decide := true }) only [
              Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
              BitVec.sub_self,
              wp_norm, arm64_norm, _hf_hook]
        )))
    else
      let (progStx, pcStx, specStx) ← g.withContext do
        pure (← Term.exprToSyntax (← instantiateMVars progExpr),
              ← Term.exprToSyntax (← instantiateMVars pcExpr),
              ← Term.exprToSyntax (← instantiateMVars specExpr))
      match rawProgIdentOpt with
      | some rawId =>
        evalTactic (← `(tactic| (
          have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
            apply ProofLib.subroutine_ok_outcome_intro
            intro _x _R _s0 _hpc _hrun _hpre _hsp
            obtain ⟨_hkeep, _hsym, _hout⟩ := ($hcall) _x _R _s0 _hrun _hpre _hsp
            refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
            rw [_hpc]
            try simp only [wp_unfold]
            try simp (config := { decide := true }) only [wp_norm, arm64_norm]
            try simp (config := { decide := true }) only [
              Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
              BitVec.sub_self,
              $rawId:ident, wp_norm, arm64_norm]
        )))
      | none =>
        evalTactic (← `(tactic| (
          have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
            apply ProofLib.subroutine_ok_outcome_intro
            intro _x _R _s0 _hpc _hrun _hpre _hsp
            obtain ⟨_hkeep, _hsym, _hout⟩ := ($hcall) _x _R _s0 _hrun _hpre _hsp
            refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
            rw [_hpc]
            try simp only [wp_unfold]
            try simp (config := { decide := true }) only [wp_norm, arm64_norm]
            try simp (config := { decide := true }) only [
              Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
              BitVec.sub_self,
              wp_norm, arm64_norm]
        )))
    (← getGoals).forM instantiateMVarDeclMVars
    return subId
  let hTyWhnf ← g.withContext (whnfR hTy)
  if hTyWhnf.isAppOfArity ``Arm64.subroutine_ok 4 && !hExpr.hasMVar then
    return hcall
  let instExpr? ← withoutModifyingState do
    tryTacticCatchRuntime do
      g.withContext do
        let eHead := if hExpr.hasMVar && (hExpr.getAppFn.isConst || hExpr.getAppFn.isFVar) then
          hExpr.getAppFn
        else
          hExpr
        let headTy ← instantiateMVars (← inferType eHead)
        let some (xs, bis, p, a, _) ← openSubroutineOkType? headTy | throwError "not quantifiable sub_ok"
        if xs.isEmpty then throwError "no binders"
        unless ← isDefEq p progExpr do
          let pUnw ← unwrapRebasedProgExpr p
          let progUnw ← unwrapRebasedProgExpr progExpr
          unless ← isDefEq pUnw progUnw do throwError "prog mismatch"
        let aInst ← instantiateMVars a
        if aInst.hasMVar then
          let _ ← isDefEq aInst pcExpr
        for x in xs, bi in bis do
          if (← instantiateMVars x).isMVar && bi.isInstImplicit then
            let ty ← instantiateMVars (← inferType x)
            if !ty.hasExprMVar then
              if let some inst ← synthInstance? ty then
                discard <| isDefEq x inst
        for _ in [0:2] do
          for x in xs do
            let x' ← instantiateMVars x
            if x'.isMVar then
              let xTy ← instantiateMVars (← inferType x)
              if ← isProp xTy then
                let xTyCore := if xTy.consumeMData.isAppOfArity ``autoParam 2 then
                  xTy.consumeMData.appFn!.appArg!
                else xTy
                let mut closed := false
                for decl in (← getLCtx).decls.toList.reverse do
                  let some decl := decl | continue
                  if !decl.isImplementationDetail then
                    let saved ← saveState
                    if ← withReducible (isDefEq decl.type xTyCore) then
                      if ← isDefEq x decl.toExpr then
                        closed := true
                        break
                    saved.restore
                if !closed && !xTyCore.hasMVar then
                  if let some prf ← proveWpSepSide? xTyCore then
                    discard <| isDefEq x prf
        let app ← instantiateMVars (mkAppN eHead xs)
        if app.hasMVar then throwError "unassigned mvars"
        return app
  match instExpr? with
  | some app => g.withContext (Term.exprToSyntax app)
  | none => return hcall

private partial def extractSpecImage? (specExpr : Expr) (fuel : Nat := 4) : MetaM (Option Expr) := do
  let e ← instantiateMVars specExpr
  if let some sub := e.find? (fun t =>
      t.isAppOfArity ``Spec.inImage 3 ||
      t.isAppOfArity ``Obj.Image.FrozenLoaded 2 ||
      t.isAppOfArity ``Obj.Image.CallInv 2) then
    if sub.isAppOfArity ``Spec.inImage 3 then
      return some (sub.getArg! 2)
    else
      return some (sub.getArg! 0)
  if fuel == 0 then return none
  let fn := e.getAppFn
  if fn.isConst then
    let nm := fn.constName!
    if nm != ``Arm64.Spec.mk then
      if let some e' ← unfoldDefinition? e then
        return ← extractSpecImage? e' (fuel - 1)
  return none

private def findFrozenProofs? (sExpr : Expr) (imgHint? : Option Expr := none) :
    TacticM (Option (Expr × Expr × Expr × Bool)) := do
  let g ← getMainGoal
  g.withContext do
    let mut candImgs : Array (Expr × Bool) := #[]
    let addCand (arr : Array (Expr × Bool)) (img : Expr) (isCallInv : Bool) : MetaM (Array (Expr × Bool)) := do
      if let some hint := imgHint? then
        if !(img == hint || (← withReducible (isDefEq img hint))) then
          return arr
      for (existing, oldInv) in arr do
        if existing == img || (← withReducible (isDefEq existing img)) then
          if isCallInv && !oldInv then
            return arr.map fun (e, b) => if e == existing then (e, true) else (e, b)
          return arr
      return arr.push (img, isCallInv)
    for decl in (← getLCtx).decls.toList.reverse do
      let some decl := decl | continue
      if decl.isImplementationDetail || decl.isAuxDecl then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.isAppOfArity ``Obj.Image.CallInv 2 then
        candImgs ← addCand candImgs (ty.getArg! 0) true
      else if ty.isAppOfArity ``Obj.Image.FrozenLoaded 2 then
        candImgs ← addCand candImgs (ty.getArg! 0) false
    if let some hint := imgHint? then
      if candImgs.isEmpty then
        candImgs := #[(hint, false)]
    for (img, hasCallInv) in candImgs do
      let fzGoalTy := mkApp2 (mkConst ``Obj.Image.FrozenLoaded) img sExpr
      let symGoalTy ← mkEq (mkApp (mkConst ``State.symtab) sExpr) (mkApp (mkConst ``Obj.Image.symtab) img)
      let mut fzPrf? : Option Expr := none
      for decl in (← getLCtx).decls.toList.reverse do
        let some decl := decl | continue
        if decl.isImplementationDetail || decl.isAuxDecl then continue
        let ty := (← instantiateMVars decl.type).consumeMData
        if ty.isAppOfArity ``Obj.Image.FrozenLoaded 2 then
          let dImg := ty.getArg! 0
          let s0 := ty.getArg! 1
          if dImg == img || (← withReducible (isDefEq dImg img)) then
            if s0 == sExpr then
              fzPrf? := some decl.toExpr
              break
            else if let some hmem ← proveMemEq? sExpr s0 then
              fzPrf? := some (mkApp5 (mkConst ``Obj.Image.FrozenLoaded.of_mem_eq) img s0 sExpr decl.toExpr hmem)
              break
        else if ty.isAppOfArity ``Obj.Image.CallInv 2 then
          let dImg := ty.getArg! 0
          let s0 := ty.getArg! 1
          if dImg == img || (← withReducible (isDefEq dImg img)) then
            let p1 := mkApp2 (mkConst ``Obj.Image.FrozenLoaded) img s0
            let p2 ← mkEq (mkApp (mkConst ``State.symtab) s0) (mkApp (mkConst ``Obj.Image.symtab) img)
            let hfz0 := mkApp3 (mkConst ``And.left) p1 p2 decl.toExpr
            if s0 == sExpr then
              fzPrf? := some hfz0
              break
            else if let some hmem ← proveMemEq? sExpr s0 then
              fzPrf? := some (mkApp5 (mkConst ``Obj.Image.FrozenLoaded.of_mem_eq) img s0 sExpr hfz0 hmem)
              break
      if fzPrf?.isNone then
        fzPrf? ← proveWpSepSide? fzGoalTy
      let some fzPrf := fzPrf? | continue
      let mut symPrf? : Option Expr := none
      for decl in (← getLCtx).decls.toList.reverse do
        let some decl := decl | continue
        if decl.isImplementationDetail || decl.isAuxDecl then continue
        let ty := (← instantiateMVars decl.type).consumeMData
        if ty == symGoalTy then
          symPrf? := some decl.toExpr
          break
        else if ty.isAppOfArity ``Obj.Image.CallInv 2 then
          let dImg := ty.getArg! 0
          let s0 := ty.getArg! 1
          if (dImg == img || (← withReducible (isDefEq dImg img))) && s0 == sExpr then
            let p1 := mkApp2 (mkConst ``Obj.Image.FrozenLoaded) img s0
            let p2 ← mkEq (mkApp (mkConst ``State.symtab) s0) (mkApp (mkConst ``Obj.Image.symtab) img)
            symPrf? := some (mkApp3 (mkConst ``And.right) p1 p2 decl.toExpr)
            break
      if symPrf?.isNone then
        symPrf? ← proveWpSepSide? symGoalTy
      let some symPrf := symPrf? | continue
      return some (img, fzPrf, symPrf, hasCallInv)
    return none

private def dischargeWppPanicSubgoal (gPanic : MVarId) (onPanic? : Option Term) :
    TacticM (List MVarId) := do
  let tryCloseClean (tac : TacticM Unit) : TacticM Bool :=
    tryTacticCatchRuntimeBool do
      tac
      unless (← getGoals).isEmpty do throwError "unsolved"
  setGoals [gPanic]
  if let some hpan := onPanic? then
    let c1 ← tryCloseClean do
      evalTactic (← `(tactic| (
        wp_unfold_specs
        intro _sf _hpan _hpan_ex _hm
        try dsimp only at _hm ⊢
        try simp only [Spec.inImage, Spec.allowPanicWhen, Spec.allowOomWhen, Spec.allowOom] at _hm ⊢
        refine allowPanic_frame ($hpan) _hm)))
    if c1 then return []
    let c2 ← tryCloseClean do
      evalTactic (← `(tactic| (
        wp_unfold_specs
        intro _sf _hpan _hpan_ex _hm
        try dsimp only at _hm ⊢
        try simp only [Spec.inImage, Spec.allowPanicWhen, Spec.allowOomWhen, Spec.allowOom] at _hm ⊢
        refine allowPanic_frame (fun _hφ => ($hpan) _sf _hpan _hφ) _hm)))
    if c2 then return []
    let c3 ← tryCloseClean do
      evalTactic (← `(tactic| (
        wp_unfold_specs
        intro _sf _hpan _hpan_ex _hm
        try dsimp only at _hm ⊢
        try simp only [Spec.inImage, Spec.allowPanicWhen, Spec.allowOomWhen, Spec.allowOom] at _hm ⊢
        exact ($hpan) _sf _hpan _hm)))
    if c3 then return []
    let c4 ← tryCloseClean do
      evalTactic (← `(tactic| exact (fun _sf _hpan _ => ($hpan) _sf _hpan)))
    if c4 then return []
    let c5 ← tryCloseClean do
      evalTactic (← `(tactic| exact ($hpan)))
    if c5 then return []
    let c6 ← tryCloseClean do
      evalTactic (← `(tactic| (intro _sf _hpan _hpan_ex; exact ($hpan) _sf _hpan)))
    if c6 then return []
    throwError "wpp_call: user-supplied `(on_panic := {hpan})` did not close the panic obligation"
  let closedNoPanic ← tryCloseClean do
    evalTactic (← `(tactic| (
      wp_unfold_specs
      intro _sf _hpan ⟨_R', _hpan_sat⟩
      try dsimp only at _hpan_sat
      try simp only [Spec.inImage, satisfies_pure_sepConj, sepConj_assoc] at _hpan_sat
      first
        | exact False.elim (not_satisfies_false_sepConj _hpan_sat)
        | exact False.elim _hpan_sat.1
        | exact False.elim _hpan_sat.2.1
    )))
  if closedNoPanic then
    return []
  let closedAllowPanic ← withHeartbeatCap 40000 do
    tryCloseClean do
      evalTactic (← `(tactic| (
        wp_unfold_specs
        intro _sf _hpan _hpan_ex _hm
        try dsimp only at _hm ⊢
        try simp only [Spec.inImage, Spec.allowPanicWhen, Spec.allowOomWhen, Spec.allowOom] at _hm ⊢
        refine allowPanic_frame ?_ _hm
        intro _hφ
        first
          | exact True.intro
          | exact _hφ
          | assumption
          | wp_assumption
          | (try simp (config := { decide := true }) only [
               ne_eq, true_and, and_true, false_and, and_false,
               not_true_eq_false, not_false_eq_true, imp_self,
               wp_norm, arm64_norm, *] at _hφ ⊢
             first
               | done
               | trivial
               | exact _hφ
               | with_reducible rfl
               | assumption
               | wp_assumption
               | decide
               | (bv_omega_fast; done)
               | (wp_bv_omega; done)
               | (bv_omega; done)
               | (omega; done)
               | (bv_fallback; done))
      )))
  if closedAllowPanic then
    return []
  let reducedAllowPanic ← tryTacticCatchRuntimeBool do
    evalTactic (← `(tactic| (
      wp_unfold_specs
      intro _sf _hpan _hpan_ex _hm
      try dsimp only at _hm ⊢
      try simp only [Spec.inImage, Spec.allowPanicWhen, Spec.allowOomWhen, Spec.allowOom] at _hm ⊢
      refine allowPanic_frame ?_ _hm
      intro _hφ
      try simp (config := { decide := true }) only [wp_norm, arm64_norm, *] at _hφ ⊢
    )))
  if reducedAllowPanic then
    return ← getGoals
  return [gPanic]

def wppCallCore (hcallOrig : Term) (arg? : Option Term) (onPanic? : Option Term)
    (requireFrozen : Bool := false) : TacticM Unit := do
  transitionToContinuationGoalIfReady (forWppCall := true)
  stepBLInGoalIfAtBL
  let g0 ← getMainGoal
  let ty0 ← g0.withContext (instantiateMVars (← g0.getType))
  unless ty0.consumeMData.isAppOfArity ``SepWPp 7 do
    throwError "wpp_call: goal is not a `SepWPp` judgment:{indentExpr ty0}"
  let (progExpr, targetPcExpr, pcExpr) ← getSepWPOrWPpStateAndPC
  if pcExpr.isAppOfArity ``ite 5 then
    throwUnresolvedBranchError "wpp_call" pcExpr
  let atTarget ← withoutModifyingState do
    tryTacticCatchRuntimeBool do
      let g ← getMainGoal
      let same ← g.withContext do
        if ← pcReachedTarget pcExpr targetPcExpr then return true
        let (pcNorm, _) ← SepSolver.normAddrMeta pcExpr
        let (targetNorm, _) ← SepSolver.normAddrMeta targetPcExpr
        return pcNorm == targetNorm || (← withReducibleAndInstances (isDefEq pcNorm targetNorm))
      if same then Pure.pure ()
      else throwError "not at target"
  if atTarget then
    let pcStr ← (← getMainGoal).withContext (formatShortHexAddr pcExpr)
    throwError "wpp_call: current PC `{pcStr}` is already at `target_pc`; use `SepWPp.done` or `wp_done` instead of `wpp_call`"
  let hcall ← resolveCallContractTerm hcallOrig progExpr pcExpr
  let g ← getMainGoal
  let sExpr ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    Pure.pure (ty.getArg! 2)
  let (isSep, specImgHint?) ← g.withContext do
    let hcallExpr ← elabTerm hcall none
    let hcallTy ← whnfR (← instantiateMVars (← inferType hcallExpr))
    if hcallTy.isAppOfArity ``Arm64.subroutine_ok 4 then
      let specE := hcallTy.getArg! 3
      let isS ← specIsSplit specE
      let img? ← extractSpecImage? specE
      return (isS, img?)
    else
      return (false, none)
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  if isSep && !requireFrozen then
    let hpostId ← freshIdent `hpost_sf
    let applySepStx ← match arg? with
      | some a => `(tactic| apply (SepWPp.call_sep $hcall (x := $a)))
      | none => `(tactic| apply (SepWPp.call_sep $hcall))
    evalTactic applySepStx
    closeCallSiteSetupSubgoals progExpr (some hcallOrig)
    let gsAfterSetup ← getGoals
    let gPreR :: gFrame :: gAssoc :: gCont :: rest := gsAfterSetup
      | throwError "wpp_call: unexpected subgoals after `SepWPp.call_sep`"
    setGoals [gPreR]
    let ghostMVars ← etaExpandGoalProdMVarsWithNames
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_unfold_specs)))
    if !(← getGoals).isEmpty then
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| dsimp only)))
    if !(← getGoals).isEmpty then
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| repeat' (apply And.intro))))
    let gsPreR ← getGoals
    setGoals [gFrame]
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| dsimp only)))
    let gsFrame ← getGoals
    setGoals (gsPreR ++ gsFrame)
    wpDischargeCallSubgoalsCore ghostMVars (some hcallOrig)
    setGoals [gAssoc]
    evalTactic (← `(tactic|
      wp_focus_close (
        try (conv => lhs; dsimp only; simp only [emp_sepConj, sepConj_emp, sepConj_assoc])
        try with_reducible rfl
      )))
    setGoals (gCont :: rest)
    evalTactic (← `(tactic| intro $sfId:ident $hpcId:ident $hrunId:ident $hpostId:ident))
    foldStructEtaTarget
    wpNormAndSplitHyp hpostId
    return
  let frozenInfo? ← findFrozenProofs? sExpr specImgHint?
  if (requireFrozen || specImgHint?.isSome) && frozenInfo?.isNone then
    throwError "wpp_call_frozen: could not prove `img.FrozenLoaded s` and `s.symtab = img.symtab` from the local context"
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  match frozenInfo? with
  | some (imgExpr, hfzPrf, hsymPrf, hasCallInv) =>
    let hfzStx ← g.withContext (Term.exprToSyntax hfzPrf)
    let hsymStx ← g.withContext (Term.exprToSyntax hsymPrf)
    let hfzSfId ← freshIdent `hfz_sf
    let hsymSfId ← freshIdent `hsym_sf
    let applyFrozenStx ← match arg? with
      | some a => `(tactic| apply (SepWPp.call_wpp_frozen $hcall (x := $a) $hfzStx $hsymStx))
      | none => `(tactic| apply (SepWPp.call_wpp_frozen $hcall $hfzStx $hsymStx))
    evalTactic applyFrozenStx
    closeCallSiteSetupSubgoals progExpr (some hcallOrig)
    let gsAfterSetup ← getGoals
    let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
      | throwError "wpp_call: unexpected subgoals after `SepWPp.call_wpp_frozen`"
    setGoals [gPre]
    evalTactic (← `(tactic| intro _R' _hmR'))
    let ghostMVars ← etaExpandGoalProdMVarsWithNames
    evalTactic (← `(tactic| (
      wp_unfold_specs
      try dsimp only
      try simp (config := { decide := true }) only [
        Spec.inImage,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc,
        satisfies_pure, satisfies_emp, sepConj_assoc, emp_sepConj, sepConj_emp,
        List.length_nil, List.length_cons, List.length_singleton,
        Nat.mul_zero, memRegion_zero, pointsToWords64_nil, BitVec.sub_self,
        wp_norm, arm64_norm] at _hmR' ⊢
    )))
    destructureSatHyps
    evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
    wpDischargeCallSubgoalsCore ghostMVars (some hcallOrig)
    setGoals [gExit]
    evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; (try simp only [Spec.inImage] at _he); exact not_satisfies_false_sepConj _he)))
    let panicRem ← dischargeWppPanicSubgoal gPanic onPanic?
    setGoals (gCont :: rest)
    evalTactic (← `(tactic| intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hfzSfId:ident $hsymSfId:ident))
    if hasCallInv then
      let gContNow ← getMainGoal
      let imgStx ← gContNow.withContext do Term.exprToSyntax (← instantiateMVars imgExpr)
      let hinvSfId ← freshIdent `hinv_sf
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
        have $hinvSfId:ident : Obj.Image.CallInv $imgStx $sfId:ident := ⟨$hfzSfId:ident, $hsymSfId:ident⟩)))
      (← getGoals).forM instantiateMVarDeclMVars
    foldStructEtaTarget
    wpNormAndSplitHyp hspId
    wpNormAndSplitHyp hcsId
    wpElimSpatialContext hspId (forWppCall := true)
    let contGoals ← getGoals
    setGoals (contGoals ++ panicRem)
  | none =>
    let applyWppStx ← match arg? with
      | some a => `(tactic| apply (SepWPp.call_wpp $hcall (x := $a)))
      | none => `(tactic| apply (SepWPp.call_wpp $hcall))
    evalTactic applyWppStx
    closeCallSiteSetupSubgoals progExpr (some hcallOrig)
    let gsAfterSetup ← getGoals
    let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
      | throwError "wpp_call: unexpected subgoals after `SepWPp.call_wpp`"
    setGoals [gPre]
    evalTactic (← `(tactic| intro _R' _hmR'))
    let ghostMVars ← etaExpandGoalProdMVarsWithNames
    evalTactic (← `(tactic| (
      wp_unfold_specs
      try dsimp only
      try simp (config := { decide := true }) only [
        Spec.inImage,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc,
        satisfies_pure, satisfies_emp, sepConj_assoc, emp_sepConj, sepConj_emp,
        List.length_nil, List.length_cons, List.length_singleton,
        Nat.mul_zero, memRegion_zero, pointsToWords64_nil, BitVec.sub_self,
        wp_norm, arm64_norm] at _hmR' ⊢
    )))
    destructureSatHyps
    evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
    wpDischargeCallSubgoalsCore ghostMVars (some hcallOrig)
    setGoals [gExit]
    evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; (try simp only [Spec.inImage] at _he); exact not_satisfies_false_sepConj _he)))
    let panicRem ← dischargeWppPanicSubgoal gPanic onPanic?
    setGoals (gCont :: rest)
    evalTactic (← `(tactic| intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident))
    foldStructEtaTarget
    wpNormAndSplitHyp hspId
    wpNormAndSplitHyp hcsId
    wpElimSpatialContext hspId (forWppCall := true)
    let contGoals ← getGoals
    setGoals (contGoals ++ panicRem)

private def classifyOomBody? (e : Expr) : MetaM (Option Bool) := do
  let e ← whnfR (← instantiateMVars e)
  lambdaTelescope e fun _ body => do
    let body ← whnfR body
    unless body.isAppOfArity ``SepProp.pure 1 do return none
    let φ := (body.getArg! 0).consumeMData
    if φ.isConstOf ``False then return some false
    if φ.isConstOf ``True then return some true
    return none

private def calleeSpecOfContract? (hcall : Term) : TacticM (Option Expr) := do
  let g ← getMainGoal
  g.withContext do
    let some ty ← tryTacticCatchRuntime (do instantiateMVars (← inferType (← elabTerm hcall none)))
      | return none
    let mut ty := ty.consumeMData
    for _ in [:6] do
      if ty.isAppOfArity ``subroutine_ok 4 || ty.isAppOfArity ``Arm64.HookOk 3 ||
          ty.isAppOfArity ``Arm64.HookSat 4 then
        return some ty.appArg!
      let some ty' ← unfoldDefinition? ty | return none
      ty := (← whnfR ty').consumeMData
    return none

-- When `h_oom` fails, the call rule leaves a synthetic `sorry` that causes Lean to suppress
-- errors; detect an `onOom` vs. goal `oom` mismatch so `withCallFailureDiagnostics` can report it.
private def oomMismatchMessage? (tac : String) (hcall : Term) : TacticM (Option MessageData) := do
  let g ← getMainGoal
  let some spec ← calleeSpecOfContract? hcall | return none
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let goalOom? :=
      if ty.isAppOfArity ``SepWP 6 then some (ty.getArg! 5)
      else if ty.isAppOfArity ``SepWPp 7 then some (ty.getArg! 6)
      else none
    let some goalOom := goalOom? | return none
    -- Reduce the spec to a `Spec.mk` application (unfolding `Spec.allowOom`, `Spec.split`, named
    -- spec constants, ...) so that the `onOom` projection reduces to the field itself.
    let specMk ← whnfD (← instantiateMVars spec)
    let calleeOom ← whnfR (← mkAppM ``Spec.onOom #[specMk])
    let calleeCls ← classifyOomBody? calleeOom
    let goalCls ← classifyOomBody? goalOom
    -- `⌜False⌝` on the callee side or `⌜True⌝` on the goal side is always discharged.
    if calleeCls == some false || goalCls == some true then return none
    return some m!"{tac}: callee `onOom` is not admitted by the goal's `oom`, so the call rule's \
      OOM side condition could not be discharged\
      \n  callee onOom:{indentExpr calleeOom}\
      \n  goal oom:{indentExpr goalOom}\
      \nhint: state the enclosing `SepWP` / `SepWPp` goal with an `oom` that admits the callee's \
      (e.g. `fun _ => ⌜True⌝`, and `Spec.allowOom` on the caller's contract), or call a contract \
      whose `onOom` is `⌜False⌝`"

-- Intercept errors mentioning a synthetic `sorry` (which Lean would suppress) and surface an
-- `onOom` mismatch diagnostic or plain-text error instead.
private def withCallFailureDiagnostics (tac : String) (hcall : Term) (k : TacticM Unit) :
    TacticM Unit := do
  let saved ← saveState
  try k
  catch e =>
    unless e.toMessageData.hasSyntheticSorry do throw e
    let text ← e.toMessageData.toString
    saved.restore (restoreInfo := true)
    if let some msg ← oomMismatchMessage? tac hcall then
      throwError msg
    throwError "{text}\n(the failed call rule left a `sorry` in the goal; a common cause is an \
      unprovable call-rule side condition such as `h_oom`)"

/-- Apply a `subroutine_ok` (or `Program.subroutineOk`, `Program.relocSubroutineOk`, `HookOk`,
    `HookSat`, or `Spec.inImage`) contract at a `SepWPp` call site (`bl`):
    - Automatically transitions a preceding `SepWPp.of_sepWP` / `SepWPp.of_sepWP_frozen` segment
      when `wp_steps` has stopped at the callee entry (no manual `apply SepWP.done` or `intro` needed).
    - Automatically infers `ret_pc` from `s.readReg64 .lr` and discharges `s.pc = entry`,
      `s.status = .Running`, `s.spAligned = true`, and `s.readReg64 .lr = ret_pc` (no `(ret_pc := ...)` needed).
    - Automatically infers the spatial frame `F` via `wp_frame_split` / `sep_frame` (no `(T := ...)` needed).
    - Automatically preserves `img.FrozenLoaded` and `symtab = img.symtab` across the call when
      present in the local context.
    - Automatically discharges the panic obligation for non-panicking callees (`Spec.noPanic`) and
      panic-propagating callees (`Spec.allowPanic`, `Spec.panicsOr`, `Spec.allowPanicWhen`), or uses
      `(on_panic := term)` if supplied.
    - Afterwards moves framed state-indexed atoms `f ... s_pre` to the post-call state using
      `@[frame_transport]` lemmas (`wp_frame_transport`; disable with
      `set_option proofLib.wpCallFrameTransport false`).
    - Supports `wpp_call hcall`, `wpp_call hcall arg`, `wpp_call hcall (x := arg)`, and
      `wpp_call hcall ... (on_panic := term)`. -/
syntax "wpp_call" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic
elab_rules : tactic
  | `(tactic| wpp_call $hcall:term $[$opts:wppCallOpt]*) => do
    let (arg?, onPanic?) ← parseWppCallOpts opts
    withCallFailureDiagnostics "wpp_call" hcall
      (wppCallCore hcall arg? onPanic? (requireFrozen := false))
    frameTransportAllGoals

/-- Variant of `wpp_call` that requires `img.FrozenLoaded` and `s.symtab = img.symtab` in the local
    context and preserves both invariants across the call. -/
syntax "wpp_call_frozen" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic
elab_rules : tactic
  | `(tactic| wpp_call_frozen $hcall:term $[$opts:wppCallOpt]*) => do
    let (arg?, onPanic?) ← parseWppCallOpts opts
    withCallFailureDiagnostics "wpp_call_frozen" hcall
      (wppCallCore hcall arg? onPanic? (requireFrozen := true))
    frameTransportAllGoals

private def wpCallCoreDirect (hcallOrig : Term) (arg? : Option Term) (onPanic? : Option Term) :
    TacticM Unit := do
    transitionToContinuationGoalIfReady (forWppCall := false)
    let g0 ← getMainGoal
    let isWPpGoal ← g0.withContext do
      let ty := (← instantiateMVars (← g0.getType)).consumeMData
      return ty.isAppOfArity ``SepWPp 7
    if isWPpGoal || onPanic?.isSome then
      wppCallCore hcallOrig arg? onPanic? (requireFrozen := false)
      return
    let (_, _, pcExpr0) ← getSepWPStateAndPC
    if pcExpr0.isAppOfArity ``ite 5 then
      resolveTerminalPcIte "wp_call" pcExpr0
    let (progExpr, targetPcExpr, pcExpr) ← getSepWPStateAndPC
    if pcExpr.isAppOfArity ``ite 5 then
      throwUnresolvedBranchError "wp_call" pcExpr
    let atTarget ← withoutModifyingState do
      tryTacticCatchRuntimeBool do
        let g ← getMainGoal
        let same ← g.withContext do
          if ← pcReachedTarget pcExpr targetPcExpr then return true
          let (pcNorm, _) ← SepSolver.normAddrMeta pcExpr
          let (targetNorm, _) ← SepSolver.normAddrMeta targetPcExpr
          return pcNorm == targetNorm || (← withReducibleAndInstances (isDefEq pcNorm targetNorm))
        if same then Pure.pure ()
        else throwError "not at target"
    if atTarget then
      let pcStr ← (← getMainGoal).withContext (formatShortHexAddr pcExpr)
      throwError "wp_call: current PC `{pcStr}` is already at `target_pc`; use `wp_done` instead of `wp_call`"
    let hcall ← resolveCallContractTerm hcallOrig progExpr pcExpr
    let sfId ← freshIdent `sf
    let hpcId ← freshIdent `hpc_sf
    let hrunId ← freshIdent `hrun_sf
    let hpostId ← freshIdent `hpost_sf
    let applySepStx ← match arg? with
      | some a => `(tactic| apply (SepWP.call_sep $hcall (x := $a)))
      | none => `(tactic| apply (SepWP.call_sep $hcall))
    let applySubStx ← match arg? with
      | some a => `(tactic| apply (SepWP.call_subroutine $hcall (x := $a)))
      | none => `(tactic| apply (SepWP.call_subroutine $hcall))
    let (isSep, specImgHint?, sExpr) ← (← getMainGoal).withContext do
      let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
      let sE := ty.getArg! 2
      let hcallExpr ← elabTerm hcall none
      let hcallTy ← whnfR (← instantiateMVars (← inferType hcallExpr))
      if hcallTy.isAppOfArity ``Arm64.subroutine_ok 4 then
        let specE := hcallTy.getArg! 3
        return (← specIsSplit specE, ← extractSpecImage? specE, sE)
      else
        return (false, none, sE)
    if isSep then
      evalTactic applySepStx
      closeCallSiteSetupSubgoals progExpr (some hcallOrig)
      let gsAfterSetup ← getGoals
      let gPreR :: gFrame :: gAssoc :: gCont :: rest := gsAfterSetup
        | throwError "wp_call: unexpected subgoals after `SepWP.call_sep`"
      setGoals [gPreR]
      let ghostMVars ← etaExpandGoalProdMVarsWithNames
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_unfold_specs)))
      if !(← getGoals).isEmpty then
        let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| dsimp only)))
      if !(← getGoals).isEmpty then
        let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| repeat' (apply And.intro))))
      let gsPreR ← getGoals
      setGoals [gFrame]
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| dsimp only)))
      let gsFrame ← getGoals
      setGoals (gsPreR ++ gsFrame)
      wpDischargeCallSubgoalsCore ghostMVars (some hcallOrig)
      setGoals [gAssoc]
      evalTactic (← `(tactic|
        wp_focus_close (
          try (conv => lhs; dsimp only; simp only [emp_sepConj, sepConj_emp, sepConj_assoc])
          try with_reducible rfl
        )))
      setGoals (gCont :: rest)
      evalTactic (← `(tactic| intro $sfId:ident $hpcId:ident $hrunId:ident $hpostId:ident))
      foldStructEtaTarget
      wpNormAndSplitHyp hpostId
    else
      let frozenInfo? ← findFrozenProofs? sExpr specImgHint?
      if frozenInfo?.isNone then
        let okPure ← tryTacticCatchRuntimeBool do
          evalTactic applySubStx
          closeCallSiteSetupSubgoals progExpr (some hcallOrig)
          let gsAfterSetup ← getGoals
          let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
            | throwError "wp_call: unexpected subgoals after `SepWP.call_subroutine`"
          setGoals [gPre]
          evalTactic (← `(tactic| (
            intro _R' _hmR'
            try simp only [satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc, satisfies_pure, satisfies_emp, sepConj_assoc, emp_sepConj, sepConj_emp] at _hmR'
          )))
          let ghostMVars ← etaExpandGoalProdMVarsWithNames
          evalTactic (← `(tactic| (
            wp_unfold_specs
            try dsimp only
            try simp only [Spec.inImage, satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc, satisfies_pure, satisfies_emp, sepConj_assoc, emp_sepConj, sepConj_emp]
            repeat' (apply And.intro)
          )))
          wpDischargeCallSubgoalsCore ghostMVars (some hcallOrig)
          setGoals ([gPanic, gErr, gCont] ++ rest)
          evalTactic (← `(tactic| (
            wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp)
            wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)
            intro $sfId:ident $hpcId:ident $hrunId:ident $hpostId:ident
          )))
          foldStructEtaTarget
          wpNormAndSplitHyp hpostId
        if okPure then return
      -- Framed call: the callee's precondition owns part of the current spatial context (or carries FrozenLoaded).
      let hspId ← freshIdent `hsp_sf
      let hcsId ← freshIdent `hcs_sf
      match frozenInfo? with
      | some (imgExpr, hfzPrf, hsymPrf, hasCallInv) =>
        let gCur ← getMainGoal
        let hfzStx ← gCur.withContext (Term.exprToSyntax hfzPrf)
        let hsymStx ← gCur.withContext (Term.exprToSyntax hsymPrf)
        let hfzSfId ← freshIdent `hfz_sf
        let hsymSfId ← freshIdent `hsym_sf
        let applyFrameFrozenStx ← match arg? with
          | some a => `(tactic| apply (SepWP.call_subroutine_frame_frozen $hcall (x := $a) $hfzStx $hsymStx))
          | none => `(tactic| apply (SepWP.call_subroutine_frame_frozen $hcall $hfzStx $hsymStx))
        evalTactic applyFrameFrozenStx
        closeCallSiteSetupSubgoals progExpr (some hcallOrig)
        let gsAfterSetup ← getGoals
        let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
          | throwError "wp_call: unexpected subgoals after `SepWP.call_subroutine_frame_frozen`"
        setGoals [gPre]
        evalTactic (← `(tactic| intro _R' _hmR'))
        let ghostMVars ← etaExpandGoalProdMVarsWithNames
        evalTactic (← `(tactic| (
          wp_unfold_specs
          try dsimp only
          try simp (config := { decide := true }) only [
            Spec.inImage,
            stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
            sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
            satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc,
            satisfies_pure, satisfies_emp, sepConj_assoc, emp_sepConj, sepConj_emp,
            wp_norm, arm64_norm] at _hmR' ⊢
        )))
        destructureSatHyps
        evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
        wpDischargeCallSubgoalsCore ghostMVars (some hcallOrig)
        setGoals (gPanic :: gErr :: gCont :: rest)
        evalTactic (← `(tactic| (
          wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; (try simp only [Spec.inImage] at _hp); exact not_satisfies_false_sepConj _hp)
          wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; (try simp only [Spec.inImage] at _he); exact not_satisfies_false_sepConj _he)
          intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hfzSfId:ident $hsymSfId:ident
        )))
        if hasCallInv then
          let gContNow ← getMainGoal
          let imgStx ← gContNow.withContext do Term.exprToSyntax (← instantiateMVars imgExpr)
          let hinvSfId ← freshIdent `hinv_sf
          let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
            have $hinvSfId:ident : Obj.Image.CallInv $imgStx $sfId:ident := ⟨$hfzSfId:ident, $hsymSfId:ident⟩)))
          (← getGoals).forM instantiateMVarDeclMVars
        foldStructEtaTarget
        wpNormAndSplitHyp hspId
        wpNormAndSplitHyp hcsId
        wpElimSpatialContext hspId
      | none =>
        let applyFrameStx ← match arg? with
          | some a => `(tactic| apply (SepWP.call_subroutine_frame $hcall (x := $a)))
          | none => `(tactic| apply (SepWP.call_subroutine_frame $hcall))
        evalTactic applyFrameStx
        closeCallSiteSetupSubgoals progExpr (some hcallOrig)
        let gsAfterSetup ← getGoals
        let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
          | throwError "wp_call: unexpected subgoals after `SepWP.call_subroutine_frame`"
        setGoals [gPre]
        evalTactic (← `(tactic| intro _R' _hmR'))
        let ghostMVars ← etaExpandGoalProdMVarsWithNames
        evalTactic (← `(tactic| (
          wp_unfold_specs
          try dsimp only
          try simp (config := { decide := true }) only [
            Spec.inImage,
            stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
            sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
            satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc,
            satisfies_pure, satisfies_emp, sepConj_assoc, emp_sepConj, sepConj_emp,
            wp_norm, arm64_norm] at _hmR' ⊢
        )))
        destructureSatHyps
        evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
        wpDischargeCallSubgoalsCore ghostMVars (some hcallOrig)
        setGoals (gPanic :: gErr :: gCont :: rest)
        evalTactic (← `(tactic| (
          wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp)
          wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)
          intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
        )))
        foldStructEtaTarget
        wpNormAndSplitHyp hspId
        wpNormAndSplitHyp hcsId
        wpElimSpatialContext hspId

private def wpCallCoreAuto (hcallOrig : Term) (arg? : Option Term) (onPanic? : Option Term) :
    TacticM Unit := do
  let autoStep := proofLib.wpCallAutoStep.get (← getOptions)
  let savedBefore ← saveState
  try
    wpCallCoreDirect hcallOrig arg? onPanic?
  catch e =>
    let msg ← e.toMessageData.toString
    if autoStep && msg.startsWith "wp_call: call target address does not match callee entry:" then
      let savedFirstErr ← saveState
      savedBefore.restore (restoreInfo := true)
      let pcBefore? ← withoutModifyingState do
        tryTacticCatchRuntime do
          let (_, _, pc) ← getSepWPOrWPpStateAndPC
          Pure.pure pc
      let _ ← tryTacticCatchRuntime (wpStepsCore 64 (quiet := true) (warnOnBoundReached := false))
      transitionToContinuationGoalIfReady (forWppCall := false)
      stepBLInGoalIfAtBL
      let pcAfter? ← withoutModifyingState do
        tryTacticCatchRuntime do
          let (_, _, pc) ← getSepWPOrWPpStateAndPC
          Pure.pure pc
      if pcBefore?.isSome && pcAfter?.isSome && pcBefore? != pcAfter? then
        try
          wpCallCoreDirect hcallOrig arg? onPanic?
          if CondClassify.proofLib.wpVerbose.get (← getOptions) then
            if let some pcAfter := pcAfter? then
              (← getMainGoal).withContext do
                logInfo m!"wp_call: auto-stepped to call target {pcAfter}"
        catch e2 =>
          let msg2 ← e2.toMessageData.toString
          if msg2.startsWith "wp_call: call target address does not match callee entry:" &&
             (msg2.splitOn "stepping stopped early").length ≤ 1 then
            savedFirstErr.restore (restoreInfo := true)
            throw e
          else
            throw e2
      else
        savedFirstErr.restore (restoreInfo := true)
        throw e
    else
      throw e

/-- Core implementation of `wp_call`: auto-step to the call target if needed, apply the callee
    contract, and turn failures hidden by a synthetic `sorry` into readable errors. -/
def wpCallCore (hcallOrig : Term) (arg? : Option Term) (onPanic? : Option Term) : TacticM Unit :=
  withCallFailureDiagnostics "wp_call" hcallOrig (wpCallCoreAuto hcallOrig arg? onPanic?)

syntax "wp_call" (ppSpace colGt term:max (ppSpace colGt wppCallOpt)*)? : tactic
elab_rules : tactic
  | `(tactic| wp_call $[$hcallOrig?:term $[$opts?:wppCallOpt]*]?) => do
    if let some hcallOrig := hcallOrig? then
      let opts := opts?.getD #[]
      let (arg?, onPanic?) ← parseWppCallOpts opts
      wpCallCore hcallOrig arg? onPanic?
      frameTransportAllGoals
    else
      unless proofLib.wpCallRegistry.get (← getOptions) do
        throwError "wp_call: expected a callee contract argument (or enable `set_option proofLib.wpCallRegistry true`)"
      let savedBefore ← saveState
      transitionToContinuationGoalIfReady (forWppCall := false)
      stepBLInGoalIfAtBL
      let (progExpr0, _, pcExpr0) ← getSepWPOrWPpStateAndPC
      if let some matchId ← findMatchingCalleeContract? progExpr0 pcExpr0 then
        wpCallCoreDirect matchId none none
        frameTransportAllGoals
        return
      if proofLib.wpCallAutoStep.get (← getOptions) then
        let _ ← tryTacticCatchRuntime (wpStepsCore 64 (quiet := true) (warnOnBoundReached := false))
        transitionToContinuationGoalIfReady (forWppCall := false)
        stepBLInGoalIfAtBL
        let (progExpr1, _, pcExpr1) ← getSepWPOrWPpStateAndPC
        if let some matchId ← findMatchingCalleeContract? progExpr1 pcExpr1 then
          wpCallCoreDirect matchId none none
          frameTransportAllGoals
          return
      savedBefore.restore (restoreInfo := true)
      let (_, _, pcOrig) ← getSepWPOrWPpStateAndPC
      let pcShort ← (← getMainGoal).withContext (formatShortHexAddr pcOrig)
      throwError "wp_call: no matching callee contract found in local context or `@[callee_spec]` registry for current PC `{pcShort}`"

/-- Discharge a tail call (`B target` or already stepped to `s.pc = target` with `s.readReg64 .lr = target_pc`)
    against a subroutine contract (`subroutine_ok prog target spec` / `Program.subroutineOk prog sym spec`),
    a hook contract (`HookOk f spec`), or a hook table entry (`HookSat hooks sym spec`). -/
syntax "wp_tailcall" ppSpace colGt term:max (ppSpace colGt term:max)? : tactic
elab_rules : tactic
  | `(tactic| wp_tailcall $hcall:term $[$arg?:term]?) => do
    -- If the current PC is still at the `B target` instruction itself, step `B target` once first
    -- so `s.pc = target` without modifying `s.readReg64 .lr`.
    let atUncondB ← withoutModifyingState do
      tryTacticCatchRuntimeBool do
        let (progExpr, _, pcExpr) ← getSepWPStateAndPC
        let g ← getMainGoal
        let isB ← g.withContext do
          let instMVar ← mkFreshExprMVar (mkConst ``Instr)
          let someInst ← mkAppM ``Option.some #[instMVar]
          let fetchGoalTy ← mkEq (mkApp2 (mkConst ``Program.fetch) progExpr pcExpr) someInst
          let fetchGoal ← mkFreshExprMVar fetchGoalTy
          setGoals [fetchGoal.mvarId!]
          -- Nested `else do` blocks keep the fallbacks lazy (the conditions of an `if ... else if ← c`
          -- term are hoisted and run before the `if`).
          let ok ←
            if ← tryCloseFetchFromHasCode then Pure.pure true
            else do
            if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_assumption))) then Pure.pure true
            else do
            if !(← fastProgFetchNone? progExpr pcExpr) then
              tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (
                (conv => lhs; simp (config := { decide := true }) only [arm64_norm]); rfl))))
            else Pure.pure false
          if !ok then return false
          let instExpr ← instantiateMVars instMVar
          return instExpr.isAppOfArity ``Instr.b 1
        unless isB do throwError "not B"
    if atUncondB then
      let _ ← wpStepCoreWithOutcome none
    let g ← getMainGoal
    let hTy ← g.withContext do
      let e ← elabTerm hcall none
      instantiateMVars (← inferType e)
    let isHookOk := hTy.isAppOfArity ``Arm64.HookOk 3
    let isHookSat := hTy.isAppOfArity ``Arm64.HookSat 4
    if isHookOk || isHookSat then
      let (progExpr, _, pcExpr) ← getSepWPStateAndPC
      let progUnwrapped ← unwrapRebasedProgExpr progExpr
      let rawProgIdentOpt : Option Ident :=
        if progUnwrapped.getAppFn.isConstOf ``Arm64.Program.rebase && progUnwrapped.getAppNumArgs ≥ 1 then
          let rawFn := (progUnwrapped.getArg! 0).getAppFn
          if rawFn.isConst then some (mkIdent rawFn.constName!) else none
        else if progUnwrapped.getAppFn.isConst then
          some (mkIdent progUnwrapped.getAppFn.constName!)
        else none
      let specExpr := if isHookSat then hTy.getArg! 3 else hTy.getArg! 2
      let subId ← freshIdent `_htail_sub
      if isHookSat then
        evalTactic (← `(tactic| obtain ⟨_f_hook, _hf_hook, _hok_hook⟩ := $hcall))
        let gAfterObtain ← getMainGoal
        let (progStx, pcStx, specStx) ← gAfterObtain.withContext do
          pure (← Term.exprToSyntax (← instantiateMVars progExpr),
                ← Term.exprToSyntax (← instantiateMVars pcExpr),
                ← Term.exprToSyntax (← instantiateMVars specExpr))
        match rawProgIdentOpt with
        | some rawId =>
          evalTactic (← `(tactic| (
            have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
              apply ProofLib.subroutine_ok_outcome_intro
              intro _x _R _s0 _hpc _hrun _hpre _hsp
              obtain ⟨_hkeep, _hsym, _hout⟩ := _hok_hook _x _R _s0 _hrun _hpre _hsp
              refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
              rw [_hpc]
              try simp only [wp_unfold]
              try simp (config := { decide := true }) only [wp_norm, arm64_norm, _hf_hook]
              try simp (config := { decide := true }) only [
                Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
                BitVec.sub_self,
                $rawId:ident, wp_norm, arm64_norm, _hf_hook]
          )))
        | none =>
          evalTactic (← `(tactic| (
            have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
              apply ProofLib.subroutine_ok_outcome_intro
              intro _x _R _s0 _hpc _hrun _hpre _hsp
              obtain ⟨_hkeep, _hsym, _hout⟩ := _hok_hook _x _R _s0 _hrun _hpre _hsp
              refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
              rw [_hpc]
              try simp only [wp_unfold]
              try simp (config := { decide := true }) only [wp_norm, arm64_norm, _hf_hook]
              try simp (config := { decide := true }) only [
                Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
                BitVec.sub_self,
                wp_norm, arm64_norm, _hf_hook]
          )))
      else
        let (progStx, pcStx, specStx) ← g.withContext do
          pure (← Term.exprToSyntax (← instantiateMVars progExpr),
                ← Term.exprToSyntax (← instantiateMVars pcExpr),
                ← Term.exprToSyntax (← instantiateMVars specExpr))
        match rawProgIdentOpt with
        | some rawId =>
          evalTactic (← `(tactic| (
            have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
              apply ProofLib.subroutine_ok_outcome_intro
              intro _x _R _s0 _hpc _hrun _hpre _hsp
              obtain ⟨_hkeep, _hsym, _hout⟩ := ($hcall) _x _R _s0 _hrun _hpre _hsp
              refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
              rw [_hpc]
              try simp only [wp_unfold]
              try simp (config := { decide := true }) only [wp_norm, arm64_norm]
              try simp (config := { decide := true }) only [
                Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
                BitVec.sub_self,
                $rawId:ident, wp_norm, arm64_norm]
          )))
        | none =>
          evalTactic (← `(tactic| (
            have $subId:ident : subroutine_ok $progStx $pcStx $specStx := by
              apply ProofLib.subroutine_ok_outcome_intro
              intro _x _R _s0 _hpc _hrun _hpre _hsp
              obtain ⟨_hkeep, _hsym, _hout⟩ := ($hcall) _x _R _s0 _hrun _hpre _hsp
              refine reaches_outcome_extern _hrun ?_ _hkeep (Arm64.reaches_outcome.of_outcome _hout) _hsym
              rw [_hpc]
              try simp only [wp_unfold]
              try simp (config := { decide := true }) only [wp_norm, arm64_norm]
              try simp (config := { decide := true }) only [
                Program.externAt?, Program.hookAtOff?, Program.rebase, List.findSome?, Option.or,
                BitVec.sub_self,
                wp_norm, arm64_norm]
          )))
      (← getGoals).forM instantiateMVarDeclMVars
      match arg? with
      | some a => evalTactic (← `(tactic| wp_call $subId:ident (x := $a)))
      | none   => evalTactic (← `(tactic| wp_call $subId:ident))
    else
      match arg? with
      | some a => evalTactic (← `(tactic| wp_call $hcall (x := $a)))
      | none   => evalTactic (← `(tactic| wp_call $hcall))

/-- Apply well-founded loop induction (`SepWP.loop` or `SepWP.loop_sep`) at the current loop header:
    - `wp_loop inv meas`: preserves the current spatial context `P` across iterations with state
      invariant `inv : State → Prop` and measure `meas : State → Nat`.
    - `wp_loop P_inv inv meas`: uses state-indexed spatial invariant `P_inv : State → SepProp`. -/
syntax "wp_loop" ppSpace colGt term:max ppSpace colGt term:max (ppSpace colGt term:max)? : tactic
elab_rules : tactic
  | `(tactic| wp_loop $t1:term $t2:term $[$t3?:term]?) => do
    let st1 ← freshIdent `st
    let hpc1 ← freshIdent `hpc_st
    let hrun1 ← freshIdent `hrun_st
    let hinv1 ← freshIdent `hinv_st
    let hzero ← freshIdent `hmeas_zero
    let st2 ← freshIdent `st
    let hpc2 ← freshIdent `hpc_st
    let hrun2 ← freshIdent `hrun_st
    let hinv2 ← freshIdent `hinv_st
    let hpos ← freshIdent `hmeas_pos
    match t3? with
    | none =>
      evalTactic (← `(tactic| (
        apply (SepWP.loop $t1 $t2)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close (
          try dsimp only
          try simp (config := { decide := true }) only [
            Arm64.CalleeSavedPreserved,
            wp_norm, arm64_norm, *]
          repeat' (apply And.intro)
          all_goals (first | done | with_reducible rfl | wp_assumption | (wp_omega_bounded; done))
        )
      )))
    | some t3 =>
      evalTactic (← `(tactic| (
        apply (SepWP.loop_sep $t1 $t2 $t3)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close (
          try dsimp only
          try simp (config := { decide := true }) only [
            sepConj_assoc, emp_sepConj, sepConj_emp,
            wp_norm, arm64_norm, *]
          exact Entails.of_eq
        )
        wp_focus_close (
          try dsimp only
          try simp (config := { decide := true }) only [
            Arm64.CalleeSavedPreserved,
            wp_norm, arm64_norm, *]
          repeat' (apply And.intro)
          all_goals (first | done | with_reducible rfl | wp_assumption | (wp_omega_bounded; done))
        )
      )))
    let gs ← getGoals
    match gs with
    | gBase :: gStep :: rest =>
      setGoals [gBase]
      evalTactic (← `(tactic| (
        intro $st1:ident $hpc1:ident $hrun1:ident $hinv1:ident $hzero:ident
        try dsimp only at $hzero:ident ⊢
        try simp (config := { decide := true }) only [
          wp_norm, arm64_norm] at $hzero:ident
        try simp only [$hzero:ident] at $hinv1:ident ⊢
      )))
      wpNormAndSplitHyp hinv1
      let gsBase ← getGoals
      setGoals [gStep]
      evalTactic (← `(tactic| (
        intro $st2:ident $hpc2:ident $hrun2:ident $hinv2:ident $hpos:ident
        try dsimp only at $hpos:ident ⊢
        try simp (config := { decide := true }) only [
          wp_norm, arm64_norm] at $hpos:ident
      )))
      wpNormAndSplitHyp hinv2
      let gsStep ← getGoals
      setGoals (gsBase ++ gsStep ++ rest)
    | _ => throwError "wp_loop: unexpected subgoals"

end

@[expose] public section

theorem Entails.of_eq_explicit {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

theorem pointsTo8_congr_val {a : BitVec 64} {v1 v2 : BitVec 8} (h : v1 = v2) :
    (a ↦₈ v1) = (a ↦₈ v2) :=
  h ▸ rfl

theorem pointsTo64_congr_val {a v1 v2 : BitVec 64} (h : v1 = v2) :
    (a ↦₆₄ v1) = (a ↦₆₄ v2) :=
  h ▸ rfl

theorem sepConj_congr {P1 P2 Q1 Q2 : SepProp} (hP : P1 = P2) (hQ : Q1 = Q2) :
    (P1 ∗ Q1) = (P2 ∗ Q2) :=
  hP ▸ hQ ▸ rfl

end

public meta section

/-- Rewrite raw memory reads `M.read8 a` / `M.read64 a` occurring in the goal and hypotheses to
    their owned values, whenever some hypothesis `h : M ⊨ P` owns `a` (the content facts of the
    blocks of `P`, `SepSolver.blockFacts`). This connects reads performed by instructions without a
    dedicated spatial step rule (e.g. sign-extending loads) on the entry memory to the ghost
    values of the precondition. -/
elab "wp_rewrite_reads" : tactic => do
  let g :: _ ← getGoals | return
  let facts ← g.withContext do
    let ref ← IO.mkRef (#[] : Array Expr)
    let collect (e : Expr) : MetaM Unit := e.forEach fun sub => do
      if (sub.isAppOfArity ``Memory.read8 2 || sub.isAppOfArity ``Memory.read64 2) &&
          !sub.hasLooseBVars && !sub.hasMVar then
        let arr ← ref.get
        if !arr.contains sub then ref.set (arr.push sub)
    collect (← instantiateMVars (← g.getType))
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        collect (← instantiateMVars decl.type)
    let reads ← ref.get
    if reads.isEmpty then return (#[] : Array Expr)
    let mut out : Array (Expr × Expr) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      unless ty.isAppOfArity ``SepProp.Satisfies 2 do continue
      let m := ty.getArg! 1
      let rs := reads.filter fun r => r.getArg! 0 == m && !out.any (·.1 == r)
      if rs.isEmpty then continue
      let (fs, _) ← SepSolver.blockFacts m (ty.getArg! 0) decl.toExpr (disj := false)
      for r in rs do
        for f in fs do
          let some (_, lhs, rhs) := (← instantiateMVars (← inferType f)).eq? | continue
          if lhs.getAppFn == r.getAppFn && !(rhs.find? (· == r)).isSome then
            if ← withReducible (isDefEq lhs r) then
              out := out.push (r, ← mkExpectedTypeHint f (← mkEq r rhs))
              break
    return out.map (·.2)
  if facts.isEmpty then return
  let mut g := g
  let mut ids : Array Ident := #[]
  for prf in facts do
    let ty ← g.withContext (inferType prf)
    let nm ← g.withContext do return (← getLCtx).getUnusedName `_h_read
    let g' ← g.assert nm ty prf
    let (_, g'') ← g'.intro1P
    g := g''
    ids := ids.push (mkIdent nm)
  replaceMainGoal [g]
  let _ ← tryTactic (evalTactic (← `(tactic| simp only [$[$ids:ident],*] at *)))
  for id in ids do
    let _ ← tryTactic (evalTactic (← `(tactic| clear $id:ident)))

/-- Top-most `if c then _ else _` conditions `c` in `e` (excluding `State` update spines and the
    branches of `ite`s whose condition has not yet been tried). -/
partial def collectTopIteConds (e : Expr) (triedArr : Array Expr) : MetaM (Array Expr) := do
  let ref ← IO.mkRef (#[] : Array Expr)
  let rec visit (sub : Expr) : MetaM Unit := do
    if sub.isAppOf ``State.writeReg64 ||
       sub.isAppOf ``State.writeReg32 ||
       sub.isAppOf ``State.writeReg ||
       sub.isAppOf ``State.writeVReg128 ||
       sub.isAppOf ``State.setPC ||
       sub.isAppOf ``State.setPState ||
       sub.isAppOf ``State.setFpsr ||
       sub.isAppOf ``State.orFpsr ||
       sub.isAppOf ``State.setMem then
      return
    if sub.isAppOfArity ``ite 5 then
      let args := sub.getAppArgs
      let c := args[1]!
      visit c
      if !c.hasLooseBVars && !c.hasMVar then
        let arr ← ref.get
        if !arr.contains c then ref.set (arr.push c)
      if triedArr.contains c then
        visit args[3]!
        visit args[4]!
      return
    match sub with
    | .app f a => visit f; visit a
    | .lam _ d b _ => visit d; visit b
    | .forallE _ d b _ => visit d; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ b => visit b
    | .proj _ _ b => visit b
    | _ => Pure.pure ()
  visit e
  ref.get

/-- Resolve `if c then _ else _` subterms of the main goal whose condition `c` (or `¬c`) follows
    from the local hypotheses (typically the path conditions accumulated by `wp_if`) by fast
    in-process normalization + `bv_omega_fast` / `omega` (or `bv_decide` as a fallback), rewriting
    them to the taken branch. Examining only top-most `ite` conditions avoids testing untaken
    nested `else if` branches before the outer `if` is simplified. -/
elab "wp_resolve_ites" : tactic => do
  let tried ← IO.mkRef (#[] : Array Expr)
  for _ in [0:64] do
    let g :: _ ← getGoals | return
    let triedArr ← tried.get
    let conds ← g.withContext do collectTopIteConds (← instantiateMVars (← g.getType)) triedArr
    let some c := conds.find? (!triedArr.contains ·) | return
    tried.set (triedArr.push c)
    let prf? ← match ← resolveIteCondFast? c with
      | some (_, ty, prf) => Pure.pure (some (ty, prf))
      | none =>
        if ← hasConstrainedFVar c then
          -- Run the fallback (`bv_decide`) decision under a heartbeat cap and runtime-exception catch.
          match (← tryTacticCatchRuntime (withHeartbeatCap 30000 (decideCond? c `slow))).join with
          | some (true, prf) => Pure.pure (some (c, prf))
          | some (false, prf) => Pure.pure (some (mkNot c, prf))
          | none => Pure.pure none
        else
          Pure.pure none
    let some (ty, prf) := prf? | continue
    let g' ← g.assert `_h_ite_cond ty prf
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hId := mkIdent `_h_ite_cond
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [$hId:ident, ↓reduceIte, Bool.false_eq_true,
        not_false_eq_true, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
        List.drop_succ_cons, List.drop_zero, arm64_norm])))
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| clear $hId:ident)))

private def checkSpatialPostMismatch (actualP expectedP : Expr) : TacticM (Option MessageData) := do
  let (actNorm, _) ← MonadRuntimeException.tryCatchRuntimeEx
    (SepSolver.normSepPropMeta (SepSolver.stripMData actualP))
    (fun _ => Pure.pure (SepSolver.stripMData actualP, none))
  let (expNorm, _) ← MonadRuntimeException.tryCatchRuntimeEx
    (SepSolver.normSepPropMeta (SepSolver.stripMData expectedP))
    (fun _ => Pure.pure (SepSolver.stripMData expectedP, none))
  let actAtoms := SepSolver.atoms actNorm
  let expAtoms := SepSolver.atoms expNorm
  for expAtom in expAtoms do
    let fn := expAtom.getAppFn.constName?.getD .anonymous
    if (fn == ``Arm64.pointsTo64 || fn == ``Arm64.pointsTo32 || fn == ``Arm64.pointsTo8) &&
       expAtom.getAppNumArgs == 2 then
      let aExp := expAtom.getArg! 0
      let vExp := expAtom.getArg! 1
      if !vExp.hasMVar then
        if let some (idx, _) ← findPointsToAtom fn actAtoms aExp then
          let vAct ← normTermForDiff (actAtoms[idx]!.getArg! 1)
          let vExpNorm ← normTermForDiff vExp
          if let some (actVal, expVal) ← checkPostValueMismatch vAct vExpNorm then
            return some m!"wp_done: postcondition memory mismatch at `{aExp}`:\n  actual:   {actVal}\n  expected: {expVal}"
  return none

/-- Unpack `CalleeSavedPreserved` / `CallingConventionPreserved` hypotheses (`split_callee_saved hcs`
    for a specific hypothesis or `split_callee_saved` for all matching hypotheses in context) into
    individual register equality hypotheses with state-spine reads normalized. -/
syntax "split_callee_saved" (ppSpace colGt ident)? : tactic
elab_rules : tactic
  | `(tactic| split_callee_saved $[$h?:ident]?) => do
    match h? with
    | some hId =>
      let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
        simp only [callee_saved_split, Arm64.CalleeSavedPreserved, Arm64.CallingConventionPreserved] at $hId:ident))
      wpNormAndSplitHyp hId
    | none =>
      let g ← getMainGoal
      let hyps ← g.withContext do
        let mut acc : Array Ident := #[]
        for decl in ← getLCtx do
          if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
            let ty ← instantiateMVars decl.type
            if (ty.find? fun e =>
                 e.isConstOf ``Arm64.CalleeSavedPreserved ||
                 e.isConstOf ``Arm64.CallingConventionPreserved).isSome then
              acc := acc.push (mkIdent decl.userName)
        return acc
      for hId in hyps do
        let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
          simp only [callee_saved_split, Arm64.CalleeSavedPreserved, Arm64.CallingConventionPreserved] at $hId:ident))
        wpNormAndSplitHyp hId

private def isCustomCalleeSavedConstName (c : Name) : Bool :=
  c != ``Arm64.CalleeSavedPreserved &&
  c != ``Arm64.CallingConventionPreserved &&
  c != ``Arm64.StackPreserved &&
  c != ``Arm64.SubroutinePost &&
  c != ``Arm64.calleeSavedVRegs &&
  c != ``Arm64.VRegFile.calleeSaved &&
  let s := c.toString
  (s.splitOn "CalleeSaved").length > 1 ||
  (s.splitOn "CallingConvention").length > 1 ||
  (s.splitOn "calleeSaved").length > 1 ||
  (s.splitOn "calleeRegsMatch").length > 1

private def unfoldPreservedHypsAndGoal : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
    dsimp only [
      Arm64.CalleeSavedPreserved,
      Arm64.CallingConventionPreserved,
      Arm64.StackPreserved,
      Arm64.SubroutinePost
    ] at *))
  if proofLib.wpDoneAutoDisjAndCalleeSaved.get (← getOptions) then
    let g0 ← getMainGoal
    let (customConsts, vregHyps, goalHasVRegRead) ← g0.withContext do
      let ref ← IO.mkRef (#[] : Array Name)
      let scan (e : Expr) : MetaM Unit := e.forEach fun sub => do
        if let some c := sub.constName? then
          if isCustomCalleeSavedConstName c then
            let arr ← ref.get
            if !arr.contains c then ref.set (arr.push c)
      let gTy ← instantiateMVars (← g0.getType)
      scan gTy
      let hasVRegRead := (gTy.find? fun sub =>
        sub.isConstOf ``State.readVReg128 || sub.isConstOf ``State.readVReg64 ||
        sub.isConstOf ``State.readVReg32 || sub.isConstOf ``VRegFile.read).isSome &&
        (gTy.find? fun sub => sub.isConstOf ``Arm64.calleeSavedVRegs).isNone
      let mut vh : Array Ident := #[]
      for decl in ← getLCtx do
        if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
          let ty ← instantiateMVars decl.type
          scan ty
          if hasVRegRead && (ty.find? fun sub =>
               sub.isConstOf ``Arm64.calleeSavedVRegs || sub.isConstOf ``Arm64.VRegFile.calleeSaved).isSome then
            vh := vh.push (mkIdent decl.userName)
      return (← ref.get, vh, hasVRegRead)
    if !customConsts.isEmpty then
      let customIds := customConsts.map mkCIdent
      let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
        try simp (config := { decide := true }) only [
          Arm64.CalleeSavedPreserved,
          Arm64.CallingConventionPreserved,
          Arm64.StackPreserved,
          Arm64.SubroutinePost,
          $[$customIds:ident],*
        ] at *))
    if goalHasVRegRead && !vregHyps.isEmpty then
      let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
        try dsimp only [State.readVReg128, State.readVReg64, State.readVReg32]))
      for hId in vregHyps do
        let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
          try simp (config := { decide := true }) only [
            Arm64.calleeSavedVRegs,
            Arm64.VRegFile.calleeSaved,
            Prod.mk.injEq
          ] at $hId:ident))
  for _ in [0:256] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let lctx ← g.withContext getLCtx
    let mut progress := false
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
        let ty ← g.withContext (instantiateMVars decl.type)
        if ty.isAppOfArity ``And 2 then
          let id := mkIdent decl.userName
          let h1 ← freshIdent `h_pres
          if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
              rcases $id:ident with ⟨$h1:ident, $id:ident⟩
              try simp (config := { decide := true }) only [wp_norm, arm64_norm] at $h1:ident)))) then
            progress := true
            break
    if !progress then break

private partial def isCalleeSavedRegExpr (r : Expr) : MetaM Bool := do
  let r := r.consumeMData
  if r.isConstOf ``Reg.sp || r.isConstOf ``Reg.fp || r.isConstOf ``Reg.lr ||
     r.isConstOf ``Reg.x19 || r.isConstOf ``Reg.x20 || r.isConstOf ``Reg.x21 ||
     r.isConstOf ``Reg.x22 || r.isConstOf ``Reg.x23 || r.isConstOf ``Reg.x24 ||
     r.isConstOf ``Reg.x25 || r.isConstOf ``Reg.x26 || r.isConstOf ``Reg.x27 ||
     r.isConstOf ``Reg.x28 || r.isConstOf ``Reg.x29 || r.isConstOf ``Reg.x30 then
    return true
  if r.isAppOfArity ``Reg.gpr 1 then
    if let some (5, n) ← evalBitVecLit? (r.getArg! 0) then
      return 19 ≤ n && n ≤ 30
  return false

private partial def isCalleeSavedStateRead? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``BitVec.truncate 3 || e.isAppOfArity ``BitVec.setWidth 3 ||
     e.isAppOfArity ``BitVec.zeroExtend 3 then
    return ← isCalleeSavedStateRead? (e.getArg! 2)
  if e.isAppOfArity ``Prod.mk 4 then
    return ← isCalleeSavedStateRead? (e.getArg! 2)
  if e.isAppOfArity ``State.sp 1 || e.isAppOfArity ``Arm64.calleeSavedVRegs 1 then
    return some (e.getArg! 0)
  if e.isAppOfArity ``Arm64.VRegFile.calleeSaved 1 then
    let vf := (e.getArg! 0).consumeMData
    return some (if vf.isAppOfArity ``State.vregs 1 then vf.getArg! 0 else vf)
  if e.isAppOfArity ``State.readReg64 2 || e.isAppOfArity ``State.readReg32 2 then
    if ← isCalleeSavedRegExpr (e.getArg! 1) then
      return some (e.getArg! 0)
  if e.isAppOfArity ``State.readReg 3 then
    if ← isCalleeSavedRegExpr (e.getArg! 2) then
      return some (e.getArg! 0)
  if e.isAppOfArity ``RegFile.read 2 then
    let rf := (e.getArg! 0).consumeMData
    if let some (5, n) ← evalBitVecLit? (e.getArg! 1) then
      if 19 ≤ n && n ≤ 30 then
        return some (if rf.isAppOfArity ``State.regs 1 then rf.getArg! 0 else rf)
  if e.isAppOfArity ``State.readVReg128 2 || e.isAppOfArity ``State.readVReg64 2 ||
     e.isAppOfArity ``State.readVReg32 2 then
    if let some (5, n) ← evalBitVecLit? (e.getArg! 1) then
      if 8 ≤ n && n ≤ 15 then
        return some (e.getArg! 0)
  if e.isAppOfArity ``VRegFile.read 2 then
    let vf := (e.getArg! 0).consumeMData
    if let some (5, n) ← evalBitVecLit? (e.getArg! 1) then
      if 8 ≤ n && n ≤ 15 then
        return some (if vf.isAppOfArity ``State.vregs 1 then vf.getArg! 0 else vf)
  return none

private def findLocalCalleeSavedHyp? : MetaM (Option Name) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl || decl.userName.hasMacroScopes then
      continue
    let ty ← instantiateMVars decl.type
    let hasCS := (ty.find? fun sub =>
      match sub.constName? with
      | some c =>
        let s := c.toString
        (s.splitOn "CalleeSaved").length > 1 ||
        (s.splitOn "CallingConvention").length > 1 ||
        (s.splitOn "calleeSaved").length > 1 ||
        (s.splitOn "calleeRegsMatch").length > 1
      | none => false).isSome
    if hasCS then
      return some decl.userName
  return none

private def isCondBranchInstr (instExpr : Expr) : Bool :=
  let c := instExpr.getAppFn.constName?.getD .anonymous
  c == ``Instr.bCond || c == ``Instr.cbz || c == ``Instr.tbz

private def classifyPureGoalTacticHint (ty : Expr) : MetaM (String × String) := do
  let ty ← instantiateMVars ty
  let hasBitwise : Bool := (ty.find? fun sub =>
    sub.isConstOf ``HAnd.hAnd || sub.isConstOf ``HOr.hOr || sub.isConstOf ``HXor.hXor ||
    sub.isConstOf ``HShiftLeft.hShiftLeft || sub.isConstOf ``HShiftRight.hShiftRight ||
    sub.isConstOf ``BitVec.sshiftRight || sub.isConstOf ``BitVec.extractLsb ||
    sub.isConstOf ``Complement.complement).isSome
  let hasSliceLen : Bool := (ty.find? fun sub =>
    sub.isConstOf ``List.length || sub.isConstOf ``Array.size || sub.isConstOf ``ByteArray.size).isSome
  let hasBitVec : Bool := (ty.find? fun sub =>
    sub.isConstOf ``BitVec || sub.isConstOf ``BitVec.ult || sub.isConstOf ``BitVec.ule ||
    sub.isConstOf ``BitVec.slt || sub.isConstOf ``BitVec.sle || sub.isConstOf ``BitVec.toNat ||
    sub.isConstOf ``BitVec.toInt).isSome
  if let some (eqSort, _, _) := ty.eq? then
    let sortNorm ← whnf eqSort
    if sortNorm.isAppOfArity ``BitVec 1 then
      if hasBitwise then
        return ("pure side condition (BitVec bitwise equality)", "`bv_bits` (or `bv_arith` / `bv_omega`)")
      else
        return ("pure side condition (BitVec equality)", "`bv_arith` (or `bv_omega` / `simp`)")
    if sortNorm.isAppOfArity ``List 1 then
      return ("pure side condition (byte/list slice equality)", "`byte_region_eq` (or `simp`)")
    if hasSliceLen then
      return ("pure side condition (slice length equality)", "`byte_region_len` (or `omega`)")
    if sortNorm.isConstOf ``Bool && hasBitVec then
      if hasBitwise then
        return ("pure side condition (BitVec bitwise condition)", "`bv_bits` (or `bv_omega`)")
      else
        return ("pure side condition (BitVec bound)", "`bv_arith` (or `bv_omega`)")
    return ("pure side condition (equality)", "`simp` (or `rfl` / `omega`)")
  if hasSliceLen then
    return ("pure side condition (slice/buffer length bound)", "`byte_region_len` (or `omega`)")
  if hasBitVec then
    if hasBitwise then
      return ("pure side condition (BitVec bitwise condition)", "`bv_bits` (or `bv_omega`)")
    else
      return ("pure side condition (BitVec bound)", "`bv_arith` (or `bv_omega`)")
  if (ty.find? fun sub =>
      sub.isConstOf ``LT.lt || sub.isConstOf ``LE.le ||
      sub.isConstOf ``GT.gt || sub.isConstOf ``GE.ge || sub.isConstOf ``Ne).isSome then
    return ("pure side condition (arithmetic bound)", "`omega`")
  return ("pure side condition", "`simp` (or `omega` / `bv_omega`)")

private inductive WpDoneStepDeltaDiag where
  | unknown
  | past (bytes : Nat)
  | beforeBytes (bytes : Nat) (steps? : Option Nat)
  | beforeRetOrTarget (steps : Nat) (destLabel : String)
  | beforeCall (steps : Nat)
  | beforeBranch (steps : Nat)

private def advanceDiagPcExpr (pcCur : Expr) (delta : Nat) : MetaM Expr := do
  if let some (64, v) ← evalBitVecLit? pcCur then
    return toExpr (BitVec.ofNat 64 ((v + delta) % (2 ^ 64)))
  let (b, o) ← sepAddrBaseOff pcCur
  let o' := (o + delta) % (2 ^ 64)
  if o' == 0 then
    return b
  mkAppM ``HAdd.hAdd #[b, toExpr (BitVec.ofNat 64 o')]

private def inspectStraightLineStepsDiag (progExpr pcExpr pcNorm targetNorm : Expr)
    (maxSteps : Nat := 16) : TacticM (Option Expr × WpDoneStepDeltaDiag) := do
  let g0 ← getMainGoal
  let mut delta : WpDoneStepDeltaDiag := .unknown
  let (b1, o1) ← g0.withContext (sepAddrBaseOff pcNorm)
  let (b2, o2) ← g0.withContext (sepAddrBaseOff targetNorm)
  if o1 != o2 && (b1 == b2 || (← g0.withContext (withReducible (isDefEq b1 b2)))) then
    let diff := (o1 + 2 ^ 64 - o2) % (2 ^ 64)
    if 0 < diff && diff <= 0x100000 then
      delta := .past diff
    else if diff >= 2 ^ 64 - 0x100000 then
      let back := 2 ^ 64 - diff
      delta := .beforeBytes back (if back % 4 == 0 then some (back / 4) else none)
  let instOpt ← evalFetchDecodeDiag? progExpr pcExpr
  if let .unknown := delta then
    if let some inst0 := instOpt then
      let op0 := inst0.getAppFn.constName?.getD .anonymous
      if op0 != ``Instr.bl && op0 != ``Instr.blr && op0 != ``Instr.ret &&
         op0 != ``Instr.br && !isMemoryLoadStoreOp inst0 && !isCondBranchInstr inst0 then
        let look? ← withoutModifyingState do
          tryTacticCatchRuntime <| withHeartbeatCap 10000 do
            let mut curPc := pcNorm
            let mut curInst := inst0
            for k in [1:maxSteps] do
              let curOp := curInst.getAppFn.constName?.getD .anonymous
              let stepBytes ←
                if curOp == ``Instr.b && curInst.getAppNumArgs == 1 then
                  match ← g0.withContext (evalBitVecLit? (curInst.getArg! 0)) with
                  | some (64, offNat) => Pure.pure (some offNat)
                  | _ => Pure.pure none
                else
                  Pure.pure (some 4)
              let some d := stepBytes | break
              curPc ← g0.withContext (advanceDiagPcExpr curPc d)
              if curPc == targetNorm || (← g0.withContext (withReducible (isDefEq curPc targetNorm))) then
                return some (WpDoneStepDeltaDiag.beforeRetOrTarget k "`target_pc`")
              let some nextInst ← evalFetchDecodeDiag? progExpr curPc | break
              let nextOp := nextInst.getAppFn.constName?.getD .anonymous
              if nextOp == ``Instr.ret then
                return some (WpDoneStepDeltaDiag.beforeRetOrTarget (k + 1) "`RET`")
              if nextOp == ``Instr.bl || nextOp == ``Instr.blr then
                return some (WpDoneStepDeltaDiag.beforeCall k)
              if isCondBranchInstr nextInst then
                return some (WpDoneStepDeltaDiag.beforeBranch k)
              if nextOp == ``Instr.br || isMemoryLoadStoreOp nextInst then
                break
              curInst := nextInst
            return none
        if let some (some found) := look? then
          delta := found
  return (instOpt, delta)

private def classifySingleGoalDiag (g : MVarId) (isResidual : Bool := true) : TacticM String := do
  let res? ← withoutModifyingState do
    tryTacticCatchRuntime <| withHeartbeatCap 15000 do
      setGoals [g]
      let decl ← g.getDecl
      let cleanTag := decl.userName.eraseMacroScopes
      let tagComps := cleanTag.components.map Name.toString
      let isBranchCase := tagComps.any fun s =>
        s == "pos" || s == "neg" || s == "isTrue" || s == "isFalse" || s == "hthen" || s == "helse"
      let tagStr := if cleanTag.isAnonymous then "" else cleanTag.toString
      let branchCondStr? ← g.withContext do
        if !isBranchCase then Pure.pure none else
          let mut found : Option String := none
          for ldecl in ← getLCtx do
            if !ldecl.isImplementationDetail && !ldecl.isAuxDecl && !ldecl.userName.hasMacroScopes then
              let lty ← instantiateMVars ldecl.type
              if ← isProp lty then
                let s ← ppExprTruncated lty 80 6
                found := some s
          Pure.pure found
      let casePrefix :=
        if tagStr.isEmpty then ""
        else match branchCondStr? with
          | some cStr => s!"[case {tagStr} ({cStr})] "
          | none => s!"[case {tagStr}] "
      let focusNote :=
        if isBranchCase then
          "focus each branch after `wp_if` / `by_cases` with `·`, then run "
        else ""
      let residualSuffix :=
        if isResidual then " (or use `wp_done?` to keep residual goals open)" else ""
      let ty ← g.withContext do Pure.pure (← instantiateMVars (← g.getType)).consumeMData
      if ty.isAppOfArity ``SepWP 6 || ty.isAppOfArity ``SepWPp 7 then
        let kindStr := if ty.isAppOfArity ``SepWPp 7 then "SepWPp" else "SepWP"
        let progExpr := ty.getArg! 0
        let targetPcExpr := ty.getArg! 1
        let sExpr := ty.getArg! 2
        let pcExpr ← g.withContext (extractSepWPPC sExpr)
        if pcExpr.isAppOfArity ``ite 5 then
          let condStr ← g.withContext (ppExprTruncated (pcExpr.getArg! 1) 120 10)
          let thenStr ← g.withContext (formatShortHexAddr (pcExpr.getArg! 3))
          let elseStr ← g.withContext (formatShortHexAddr (pcExpr.getArg! 4))
          return s!"{casePrefix}unresolved conditional branch ({kindStr}):\n     condition: {condStr} | then PC: {thenStr} | else PC: {elseStr}\n     try:  {focusNote}`wp_if hcond` (or `wp_if_join <join_pc> <inv>`){residualSuffix}"
        let pcNorm ← normAddrForDiag pcExpr
        let targetNorm ← normAddrForDiag targetPcExpr
        let pcShort ← g.withContext (formatShortHexAddr pcNorm)
        let targetShort ← g.withContext (formatShortHexAddr targetNorm)
        let atTarget ← g.withContext do
          Pure.pure (pcNorm == targetNorm) <||> withReducible (isDefEq pcNorm targetNorm)
        if atTarget then
          let cat := if isBranchCase then s!"unresolved branch subgoal (open {kindStr} goal at target PC)" else s!"open {kindStr} goal at target PC"
          return s!"{casePrefix}{cat}:\n     PC: {pcShort} (already at target PC {targetShort})\n     try:  {focusNote}`wp_done`{residualSuffix}"
        let (instOpt, delta) ← inspectStraightLineStepsDiag progExpr pcExpr pcNorm targetNorm
        let (stepNote, tacStr) ← do
          let instName := (instOpt.map (fun e => e.getAppFn.constName?.getD .anonymous)).getD .anonymous
          if instName == ``Instr.bl || instName == ``Instr.blr then
            Pure.pure (", stopped at call instruction", "`wp_call <callee_spec>` (then `wp_steps; wp_done`)")
          else if let some e := instOpt then
            if isCondBranchInstr e then
              Pure.pure (", at conditional branch", "`wp_steps` then `wp_if hcond`")
            else if isMemoryLoadStoreOp e then
              Pure.pure (", stopped at load/store", "`wp_step` to inspect missing spatial atom / bound")
            else
              match delta with
              | .beforeBytes back (some n) =>
                Pure.pure (s!" ({n} step(s) / {back} bytes remaining)", s!"`wp_steps` (or `wp_steps {n}`, then `wp_done`)")
              | .beforeBytes back none =>
                Pure.pure (s!" ({back} bytes remaining)", "`wp_steps` (then `wp_done`)")
              | .beforeRetOrTarget n dest =>
                Pure.pure (s!" ({n} step(s) remaining to {dest})", "`wp_steps` (then `wp_done`)")
              | .beforeCall n =>
                Pure.pure (s!" ({n} step(s) before call)", "`wp_steps` then `wp_call <callee_spec>`")
              | .beforeBranch n =>
                Pure.pure (s!" ({n} step(s) before conditional branch)", "`wp_steps` then `wp_if hcond`")
              | .past bytes =>
                Pure.pure (s!" (stepped +{bytes} bytes past target PC)", "`wp_steps_to_insn` or normalize `target_pc`")
              | .unknown =>
                Pure.pure ("", "`wp_steps` (then `wp_done`)")
          else
            match delta with
            | .beforeBytes back (some n) =>
              Pure.pure (s!" ({n} step(s) / {back} bytes remaining)", s!"`wp_steps` (or `wp_steps {n}`, then `wp_done`)")
            | .beforeBytes back none =>
              Pure.pure (s!" ({back} bytes remaining)", "`wp_steps` (then `wp_done`)")
            | .past bytes =>
              Pure.pure (s!" (stepped +{bytes} bytes past target PC)", "`wp_steps_to_insn` or normalize `target_pc`")
            | _ =>
              Pure.pure ("", "`wp_steps` (then `wp_done`)")
        let cat := if isBranchCase then s!"unresolved branch subgoal (open {kindStr} execution goal)" else s!"open {kindStr} execution goal"
        return s!"{casePrefix}{cat}:\n     current PC: {pcShort} | target PC: {targetShort}{stepNote}\n     try:  {focusNote}{tacStr}{residualSuffix}"
      if ty.isAppOfArity ``Or 2 && (ty.getArg! 0).consumeMData.isAppOf ``SepWP then
        let goalShort ← g.withContext (ppExprTruncated ty 140 8)
        return s!"{casePrefix}open disjunctive loop goal:\n     goal: ⊢ {goalShort}\n     try:  {focusNote}`wp_steps` (or select an arm with `left` / `right`, then `wp_steps; wp_done`){residualSuffix}"
      if ty.isAppOfArity ``SepProp.Entails 2 then
        let goalShort ← g.withContext (ppExprTruncated ty 150 8)
        return s!"{casePrefix}spatial entailment:\n     goal: ⊢ {goalShort}\n     try:  {focusNote}`sep_entail`{residualSuffix}"
      if ty.isAppOfArity ``SepProp.Satisfies 2 then
        let goalShort ← g.withContext (ppExprTruncated ty 150 8)
        return s!"{casePrefix}spatial postcondition:\n     goal: ⊢ {goalShort}\n     try:  {focusNote}`arm64_sep_close` (or `sep_frame`){residualSuffix}"
      if !(← g.withContext (isProp ty)) then
        let goalShort ← g.withContext (ppExprTruncated ty 150 10)
        return s!"{casePrefix}unassigned witness goal:\n     goal: ⊢ {goalShort}\n     try:  {focusNote}instantiate this witness explicitly (`exact <val>` / `use <val>`){residualSuffix}"
      let (pureKind, pureTac) ← g.withContext (classifyPureGoalTacticHint ty)
      let goalShort ← g.withContext (ppExprTruncated ty 150 10)
      let cat := if isBranchCase then s!"unresolved branch subgoal ({pureKind})" else pureKind
      return s!"{casePrefix}{cat}:\n     goal: ⊢ {goalShort}\n     try:  {focusNote}{pureTac}{residualSuffix}"
  match res? with
  | some msg => return msg
  | none =>
    let tyStr ← g.withContext (ppExprTruncated (← instantiateMVars (← g.getType)) 150 10)
    return s!"unsolved goal:\n     goal: ⊢ {tyStr}\n     try:  focus subgoals with `·` or use `wp_done?`"

private def throwWpDoneResidualGoalsError (gs : List MVarId) : TacticM Unit := do
  let n := gs.length
  let header :=
    if n == 1 then "wp_done: closed current goal, but 1 unfocused goal remains open:"
    else s!"wp_done: closed current goal, but {n} unfocused goals remain open:"
  let mut lines : Array String := #[header]
  let mut idx : Nat := 1
  for g in gs.take 5 do
    let item ← classifySingleGoalDiag g (isResidual := true)
    lines := lines.push s!"  {idx}. {item}"
    idx := idx + 1
  if n > 5 then
    lines := lines.push s!"  ... and {n - 5} more open goal(s)"
  throwError (String.intercalate "\n" lines.toList)

private def formatWpDoneValueMismatch (actVal expVal : Expr) : MetaM MessageData := do
  let hintStr ←
    try
      let actVal ← instantiateMVars actVal
      let expVal ← instantiateMVars expVal
      let mut csHint? : Option String := none
      if let (some sAct, some sExp) := (← isCalleeSavedStateRead? actVal, ← isCalleeSavedStateRead? expVal) then
        if sAct != sExp then
          if let some hcc ← findLocalCalleeSavedHyp? then
            csHint? := some s!"\nhint: destructure local callee-saved hypothesis `{hcc}` (e.g. `rcases {hcc} with ⟨...⟩`) before `wp_done`"
      if let some h := csHint? then
        Pure.pure h
      else
        let hasCond (e : Expr) : Bool :=
          (e.find? fun sub => sub.isConstOf ``ite || sub.isConstOf ``dite).isSome
        let hasCast (e : Expr) : Bool :=
          (e.find? fun sub =>
            sub.isConstOf ``BitVec.zeroExtend ||
            sub.isConstOf ``BitVec.truncate ||
            sub.isConstOf ``BitVec.setWidth).isSome
        let hasMatchOrBind (e : Expr) : Bool :=
          (e.find? fun sub =>
            match sub.constName? with
            | some c =>
              c == ``Option.bind || c == ``Option.map || c == ``Bind.bind ||
              (c.toString.splitOn "match_").length > 1 ||
              (c.toString.splitOn ".casesOn").length > 1
            | none => false).isSome
        if (hasCond actVal && !hasCond expVal) || hasCast actVal then
          Pure.pure "\nhint: actual value contains an unreduced conditional or width cast; use `wp_by_cases hc : <cond>` or `simp only [wp_norm, width_norm]` before `wp_done`"
        else if (!hasCond actVal && hasCond expVal) || hasMatchOrBind actVal || hasMatchOrBind expVal then
          Pure.pure "\nhint: expected value contains an unreduced conditional or `match`; prove the guard condition (`have h : <cond> := by bv_omega; simp only [h]`) or split with `wp_by_cases hc : <cond>` before `wp_done`"
        else
          Pure.pure ""
    catch _ =>
      Pure.pure ""
  return m!"wp_done: postcondition value mismatch:\n  actual:   {actVal}\n  expected: {expVal}{hintStr}"

private partial def checkGoalEqMismatches? (ty : Expr) : TacticM (Option MessageData) := do
  let g0 ← getMainGoal
  let ty ← g0.withContext do Pure.pure (SepSolver.stripMData (← instantiateMVars ty))
  if ty.isAppOfArity ``And 2 then
    if let some msg ← checkGoalEqMismatches? (ty.getArg! 0) then return some msg
    return ← checkGoalEqMismatches? (ty.getArg! 1)
  if ty.isAppOfArity ``SepProp.Satisfies 2 then
    return ← checkGoalEqMismatches? (ty.getArg! 0)
  if ty.isAppOfArity ``SepProp.sepConj 2 then
    if let some msg ← checkGoalEqMismatches? (ty.getArg! 0) then return some msg
    return ← checkGoalEqMismatches? (ty.getArg! 1)
  if ty.isAppOfArity ``SepProp.pure 1 then
    return ← checkGoalEqMismatches? (ty.getArg! 0)
  if let some (eqTy, lhs, rhs) := ty.eq? then
    if !lhs.hasMVar && !rhs.hasMVar && !(← g0.withContext (isProp eqTy)) then
      let lNorm ← normTermForDiff lhs
      let rNorm ← normTermForDiff rhs
      if let some (actVal, expVal) ← g0.withContext (checkPostValueMismatch lNorm rNorm) then
        return some (← g0.withContext (formatWpDoneValueMismatch actVal expVal))
  return none

private def closeWpDonePureSubgoal (preNormTyOpt : Option Expr := none) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let g0 ← getMainGoal
  let pureRemedy := "prove this postcondition conjunct beforehand with `have h : <prop> := by bv_omega` (or `wp_norm_lhs`), or compact the state with `wp_compact` before `wp_done`"
  withWpHeartbeatDiag "wp_done" "pure/register postcondition verification" pureRemedy (gOpt? := some g0) do
    let hbRef ← IO.mkRef (none : Option String)
    let ty0 ← g0.withContext (instantiateMVars (← g0.getType))
    if ty0.isConstOf ``True then
      g0.assign (mkConst ``True.intro)
      replaceMainGoal []
      return
    if !ty0.hasMVar then
      let closedTrivial ← tryTacticTrackHeartbeatBool hbRef "pure/register postcondition trivial check" <|
        withHeartbeatCap 20000 (evalTactic (← `(tactic|
          first | exact True.intro | with_reducible rfl | wp_assumption | with_reducible assumption | exact CalleeSavedPreserved.rfl _ | decide)))
      if closedTrivial then return
    else
      let closedRfl ← tryTacticTrackHeartbeatBool hbRef "pure/register postcondition reflexivity check" <|
        withHeartbeatCap 20000 (evalTactic (← `(tactic|
          first | exact True.intro | with_reducible rfl | exact CalleeSavedPreserved.rfl _)))
      if closedRfl then return
    if ← outerHeartbeatsExhausted then
      throwHeartbeatPhaseError "wp_done" ((← hbRef.get).getD "pure/register postcondition fast check") pureRemedy (some g0)
    let ty0' ← g0.withContext (instantiateMVars (← g0.getType))
    let (_, hypIds) ← g0.withContext getLightweightSimpHyps
    let _ ← tryTacticTrackHeartbeatBool hbRef "pure/register postcondition simplification (`wp_norm` / `arm64_norm`)" <|
      withHeartbeatCap 30000 (evalTactic (← `(tactic| (
        try simp (config := { decide := true }) only [
          ite_prop_eq, List.length_cons, List.length_nil,
          pure, bind, Functor.map, Seq.seq,
          Option.map, Option.bind, Option.getD, Option.isSome, Option.isNone,
          Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, List.foldlM,
          Arm64.CalleeSavedPreserved, Arm64.CallingConventionPreserved,
          wp_norm, arm64_norm, $[$hypIds:ident],*]
        try repeat' (first | apply And.intro | intro _)
      ))))
    if (← getGoals).isEmpty then return
    if ← outerHeartbeatsExhausted then
      throwHeartbeatPhaseError "wp_done" ((← hbRef.get).getD "pure/register postcondition simplification (`wp_norm` / `arm64_norm`)") pureRemedy (some g0)
    let closedFastAfterSimp ← tryTacticTrackHeartbeatBool hbRef "pure/register postcondition arithmetic (`wp_omega_bounded`)" <|
      withHeartbeatCap 30000 do
        evalTactic (← `(tactic|
          all_goals (
            first
              | done
              | exact True.intro
              | with_reducible rfl
              | wp_assumption
              | with_reducible assumption
              | decide
              | (bv_omega_fast; done)
              | (wp_omega_bounded; done))))
        unless (← getGoals).isEmpty do throwError "unsolved"
    if closedFastAfterSimp then return
    if ← outerHeartbeatsExhausted then
      throwHeartbeatPhaseError "wp_done" ((← hbRef.get).getD "pure/register postcondition arithmetic (`wp_omega_bounded`)") pureRemedy (some g0)
    for gSub in (← getGoals) do
      let ty1 ← gSub.withContext (instantiateMVars (← gSub.getType))
      if let some (_, lhs, rhs) := ty1.eq? then
        let lhsN ← normTermForDiff lhs
        let rhsN ← normTermForDiff rhs
        if let some (actVal, expVal) ← gSub.withContext (checkPostValueMismatch lhsN rhsN) then
          gSub.withContext do throwError (← formatWpDoneValueMismatch actVal expVal)
    let closedMain ← tryTacticTrackHeartbeatBool hbRef "pure/register postcondition arithmetic (`wp_omega_bounded` / `bv_fallback`)" <|
      withHeartbeatCap 50000 do
        let gCur ← getMainGoal
        let (_, curHypIds) ← gCur.withContext getLightweightSimpHyps
        evalTactic (← `(tactic|
          all_goals (
            try simp (config := { decide := true }) only [
              ite_prop_eq, List.length_cons, List.length_nil,
              pure, bind, Functor.map, Seq.seq,
              Option.map, Option.bind, Option.getD, Option.isSome, Option.isNone,
              Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, List.foldlM,
              Arm64.CalleeSavedPreserved, Arm64.CallingConventionPreserved,
              wp_norm, arm64_norm, $[$curHypIds:ident],*]
            first
              | done
              | exact True.intro
              | with_reducible rfl
              | wp_assumption
              | with_reducible assumption
              | decide
              | (bv_omega_fast; done)
              | (wp_omega_bounded; done)
              | (bv_fallback; done))))
        unless (← getGoals).isEmpty do throwError "unsolved"
    if closedMain then return
    if ← outerHeartbeatsExhausted then
      throwHeartbeatPhaseError "wp_done" ((← hbRef.get).getD "pure/register postcondition arithmetic (`wp_omega_bounded` / `bv_fallback`)") pureRemedy (some g0)
    if let some preTy := preNormTyOpt then
      if let some msg ← checkGoalEqMismatches? preTy then
        g0.withContext do throwError msg
    if let some msg ← checkGoalEqMismatches? ty0' then
      g0.withContext do throwError msg
    if let some phase ← hbRef.get then
      throwHeartbeatPhaseError "wp_done" phase pureRemedy (some g0)
    let gFail ← getMainGoal
    let failTy ← gFail.withContext (instantiateMVars (← gFail.getType))
    if failTy.consumeMData.isAppOfArity ``SepWP 6 || failTy.consumeMData.isAppOfArity ``SepWPp 7 then
      let diagStr ← classifySingleGoalDiag gFail (isResidual := false)
      throwError "wp_done: continuation execution goal is still open:\n  {diagStr}"
    if let some (_, lhs, rhs) := failTy.eq? then
      let lhsN ← normTermForDiff lhs
      let rhsN ← normTermForDiff rhs
      if ← gFail.withContext (isDefEq lhsN rhsN) then
        let closedNorm ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
          first | with_reducible rfl | decide | (simp (config := { decide := true }) only [pure, bind, Functor.map, Seq.seq, Option.map, Option.bind, Option.getD, Option.isSome, Option.isNone, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, List.foldlM, wp_norm, arm64_norm]; done))))
        if closedNorm then return
      gFail.withContext do throwError (← formatWpDoneValueMismatch lhsN rhsN)
    gFail.withContext do
      let (pureKind, pureTac) ← classifyPureGoalTacticHint failTy
      throwError "wp_done: failed to prove postcondition ({pureKind}):{indentExpr (← g0.getType)}\n(normalized:{indentExpr failTy})\nhint: prove this obligation beforehand with `have h : ... := by ...` using {pureTac} before `wp_done`"

private def throwWpDonePcMismatchError (progExpr pcExpr targetPcExpr : Expr) : TacticM Unit := do
  let hintStr ←
    try
      let res? ← tryTacticCatchRuntime do
        let g0 ← getMainGoal
        let pcNorm ← normAddrForDiag pcExpr
        let targetNorm ← normAddrForDiag targetPcExpr
        let pcShort ← g0.withContext (formatShortHexAddr pcNorm)
        let (instOpt, delta) ← inspectStraightLineStepsDiag progExpr pcExpr pcNorm targetNorm
        let deltaSuffix := match delta with
          | .past diff =>
            s!"; stepped {diff} bytes past target PC (+{diff} bytes) (use `wp_steps_to_insn` or normalize `target_pc` offsets)"
          | .beforeBytes back (some n) =>
            s!"; {n} step(s) ({back} bytes) remaining before target PC (-{back} bytes) (run `wp_steps` or `wp_steps {n}`)"
          | .beforeBytes back none =>
            s!"; {back} bytes before target PC (-{back} bytes) (run `wp_steps`)"
          | _ => ""
        match instOpt with
        | some instExpr =>
          let instStr ← g0.withContext (ppExprTruncated instExpr 100 8)
          let opConst := instExpr.getAppFn.constName?.getD .anonymous
          if opConst == ``Instr.bl || opConst == ``Instr.blr then
            return s!"\nhint: execution is stopped at call instruction `{instStr}` at `{pcShort}`; use `wp_call <callee_spec>` before `wp_done`{deltaSuffix}"
          else if opConst == ``Instr.ret then
            return s!"\nhint: `RET` (`{instStr}`) at `{pcShort}` was not stepped; check that `x30`/`lr` is restored and `status = .Running`, or run `wp_step`{deltaSuffix}"
          else if isMemoryLoadStoreOp instExpr then
            return s!"\nhint: `wp_steps` stopped early at `{instStr}` at `{pcShort}` due to a missing spatial points-to atom or slice bound (run `wp_step` to see the stuck load/store){deltaSuffix}"
          else if isCondBranchInstr instExpr then
            return s!"\nhint: execution is stopped at conditional branch `{instStr}` at `{pcShort}`; run `wp_steps` and split with `wp_if hcond` before `wp_done`"
          else
            match delta with
            | .past diff =>
              return s!"\nhint: stepped {diff} bytes past target PC (+{diff} bytes) (currently at `{instStr}` at `{pcShort}`); use `wp_steps_to_insn` or normalize `target_pc` offsets"
            | .beforeBytes back (some n) =>
              return s!"\nhint: {n} step(s) ({back} bytes) remaining before target PC (-{back} bytes, currently at `{instStr}` at `{pcShort}`); run `wp_steps` (or `wp_steps {n}`) before `wp_done`"
            | .beforeBytes back none =>
              return s!"\nhint: {back} bytes before target PC (-{back} bytes, currently at `{instStr}` at `{pcShort}`); run `wp_steps` before `wp_done`"
            | .beforeRetOrTarget n dest =>
              return s!"\nhint: execution is stopped at `{instStr}` at `{pcShort}` ({n} step(s) remaining to {dest}); run `wp_steps` before `wp_done`"
            | .beforeCall n =>
              return s!"\nhint: execution is stopped at `{instStr}` at `{pcShort}` ({n} step(s) before call instruction); run `wp_steps` then `wp_call <callee_spec>` before `wp_done`"
            | .beforeBranch n =>
              return s!"\nhint: execution is stopped at `{instStr}` at `{pcShort}` ({n} step(s) before conditional branch); run `wp_steps` and split with `wp_if hcond` before `wp_done`"
            | .unknown =>
              return s!"\nhint: execution is stopped at `{instStr}` at `{pcShort}`; run `wp_steps` (or `wp_step` to inspect why stepping stopped) before `wp_done`"
        | none =>
          match delta with
          | .past diff =>
            return s!"\nhint: stepped {diff} bytes past target PC (+{diff} bytes); use `wp_steps_to_insn` or normalize `target_pc` offsets"
          | .beforeBytes back (some n) =>
            return s!"\nhint: {n} step(s) ({back} bytes) remaining before target PC (-{back} bytes); run `wp_steps` (or `wp_steps {n}`) before `wp_done`"
          | .beforeBytes back none =>
            return s!"\nhint: {back} bytes before target PC (-{back} bytes); run `wp_steps` before `wp_done`"
          | _ =>
            return s!"\nhint: run `wp_step` to see why execution stopped at `{pcShort}`, or run `wp_steps` before `wp_done`"
      Pure.pure (res?.getD "")
    catch _ =>
      Pure.pure ""
  -- Format inside the goal's local context so free variables in the PCs (e.g. `s0`) print by
  -- name instead of as `_fvar.N`.
  let gCtx ← getMainGoal
  gCtx.withContext do
    throwError "wp_done: current PC `{pcExpr}` does not match target PC `{targetPcExpr}`{hintStr}"

private partial def findMatchingOrSepWPArm? (ty : Expr) (fuel : Nat := 8) :
    TacticM (Option (List Bool)) := do
  if fuel == 0 then return none
  let g ← getMainGoal
  let ty := (← g.withContext (instantiateMVars ty)).consumeMData
  if ty.isAppOfArity ``SepWP 6 then
    let leafTargetPc := ty.getArg! 1
    let sExpr := ty.getArg! 2
    let pcExpr ← g.withContext (extractSepWPPC sExpr)
    let matchesLeaf (pc : Expr) : TacticM Bool := do
      if ← g.withContext (pcReachedTarget pc leafTargetPc) then return true
      let pcNorm ← normAddrForDiag pc
      let targetNorm ← normAddrForDiag leafTargetPc
      g.withContext do
        Pure.pure (pcNorm == targetNorm) <||> withReducibleAndInstances (isDefEq pcNorm targetNorm)
    if ← matchesLeaf pcExpr then
      return some []
    if pcExpr.isAppOfArity ``ite 5 then
      if let some (condTrue, _, _) ← resolveIteCondAutoFallback? (pcExpr.getArg! 1) then
        let armPc := if condTrue then pcExpr.getArg! 3 else pcExpr.getArg! 4
        if ← matchesLeaf armPc then
          return some []
    return none
  if ty.isAppOfArity ``Or 2 then
    if let some path ← findMatchingOrSepWPArm? (ty.getArg! 0) (fuel - 1) then
      return some (false :: path)
    if let some path ← findMatchingOrSepWPArm? (ty.getArg! 1) (fuel - 1) then
      return some (true :: path)
  return none

private def trySelectWpDoneOrArm : TacticM Unit := do
  if (← getGoals).isEmpty then return
  unless proofLib.wpDoneAutoDisjAndCalleeSaved.get (← getOptions) do return
  let g0 ← getMainGoal
  let ty0 ← g0.withContext (instantiateMVars (← g0.getType))
  unless ty0.consumeMData.isAppOfArity ``Or 2 do return
  let path? ← withoutModifyingState do
    tryTacticCatchRuntime <| withHeartbeatCap 10000 (findMatchingOrSepWPArm? ty0)
  let some (some path) := path? | return
  for goRight in path do
    if goRight then
      evalTactic (← `(tactic| apply Or.inr))
    else
      evalTactic (← `(tactic| apply Or.inl))

/-- Core implementation of `wp_done` / `wp_done?`: closes a `SepWP` (or `SepWPp`) goal once
    execution has reached `target_pc`, failing fast with structured diagnostics on PC mismatches,
    postcondition diffs, or (unless `allowResidual` is set) open unfocused residual goals. -/
def wpDoneCore (allowResidual : Bool := false) : TacticM Unit := do
  let defaultDoneRemedy := "split or focus spatial containers with `wp_focus`, prove pure/address facts beforehand with `have h : ... := by bv_omega`, or compact a deep state with `wp_compact` before `wp_done`"
  withWpHeartbeatDiag "wp_done" "postcondition verification" defaultDoneRemedy do
    trySelectWpDoneOrArm
    let gMain0 ← getMainGoal
    let mainTy0 ← gMain0.withContext do Pure.pure (← instantiateMVars (← gMain0.getType)).consumeMData
    if mainTy0.isAppOfArity ``SepWPp 7 then
      evalTactic (← `(tactic| apply SepWPp.of_sepWP_ret))
    let gMain ← getMainGoal
    let mainTy ← gMain.withContext do Pure.pure (← instantiateMVars (← gMain.getType)).consumeMData
    if !mainTy.isAppOfArity ``SepWP 6 then
      let diagStr ← classifySingleGoalDiag gMain (isResidual := false)
      throwError "wp_done: current goal is not a `SepWP` postcondition:\n  {diagStr}"
    let (_, targetPcExpr, pcExpr0) ← getSepWPStateAndPC
    let mut pcCur := pcExpr0
    for _ in [0:wpDoneExitRounds] do
      unless pcCur.isAppOfArity ``ite 5 do break
      resolveTerminalPcIte "wp_done" pcCur
      if ← wpDonePcMatches then break
      -- The decided arm continues past the branch: step to the next stop and decide again.
      unless ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_steps))) do
        if ← outerHeartbeatsExhausted then
          throwHeartbeatPhaseError "wp_done" "stepping terminal conditional branch to target PC" defaultDoneRemedy
        break
      let (_, _, pcNext) ← getSepWPStateAndPC
      pcCur := pcNext
    let (progExpr, _, pcExpr) ← getSepWPStateAndPC
    if pcExpr.isAppOfArity ``ite 5 then
      throwUnresolvedBranchError "wp_done" pcExpr
    evalTactic (← `(tactic| apply SepWP.done))
    let gsDone ← getGoals
    let gPc :: gRun :: gPost :: restDone := gsDone
      | throwError "wp_done: unexpected subgoals after `SepWP.done`"
    setGoals [gPc]
    let hbPcRef ← IO.mkRef (none : Option String)
    if !(← tryTacticTrackHeartbeatBool hbPcRef "target PC equality check (`gPc`)"
        (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) then
      if (← hbPcRef.get).isSome || (← outerHeartbeatsExhausted) then
        throwHeartbeatPhaseError "wp_done" "target PC equality check (`gPc`)"
          "normalize the current/target PC before `wp_done` (e.g. `wp_simp_pre` or `have hpc : ... := by bv_omega`), or compact a deep `State` spine with `wp_compact`"
          (some gPc)
      throwWpDonePcMismatchError progExpr pcExpr targetPcExpr
    setGoals [gRun]
    let hbRunRef ← IO.mkRef (none : Option String)
    if !(← tryTacticTrackHeartbeatBool hbRunRef "machine status `.Running` check (`gRun`)"
        (evalTactic (← `(tactic| wp_focus_close wp_norm_lhs)))) then
      if (← hbRunRef.get).isSome || (← outerHeartbeatsExhausted) then
        throwHeartbeatPhaseError "wp_done" "machine status `.Running` check (`gRun`)"
          "compact a deep `State` update spine with `wp_compact` before `wp_done`"
          (some gRun)
      throwError "wp_done: failed to prove machine status is `.Running`"
    setGoals [gPost]
    evalTactic (← `(tactic| wp_unfold_specs))
    unfoldPreservedHypsAndGoal
    evalTactic (← `(tactic| repeat' (apply And.intro)))
    let subgoals ← getGoals
    let mut remaining : List MVarId := []
    for g in subgoals do
      setGoals [g]
      let ty ← g.withContext (instantiateMVars (← g.getType))
      match ty with
      | .forallE _ d _ _ =>
        if d.consumeMData.isAppOf ``SepProp.Satisfies then
          let hmId ← freshIdent `hm_final
          let (_, hypIds) ← g.withContext getLightweightSimpHyps
          withWpHeartbeatDiag "wp_done" "spatial hypothesis (`hm_final`) normalization"
            "compact the state/precondition with `wp_compact` or focus large spatial containers with `wp_focus` before `wp_done`"
            (gOpt? := some g) do
            evalTactic (← `(tactic| (
              intro $hmId:ident
              try simp (config := { decide := true }) only [wp_norm, arm64_norm, $[$hypIds:ident],*] at $hmId:ident
              try simp only [stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def]
            )))
            if ← outerHeartbeatsExhausted then
              throwHeartbeatPhaseError "wp_done" "spatial hypothesis (`hm_final`) normalization"
                "compact the state/precondition with `wp_compact` or focus large spatial containers with `wp_focus` before `wp_done`"
                (some g)
            destructureSatHyps
          let tyPreNormOpt : Option Expr ← do
            if !(← getGoals).isEmpty then
              let gPreNorm ← getMainGoal
              Pure.pure (some (← gPreNorm.withContext (instantiateMVars (← gPreNorm.getType))))
            else
              Pure.pure none
          withWpHeartbeatDiag "wp_done" "postcondition normalization and memory-read rewriting (`wp_norm_goal` / `wp_rewrite_reads`)"
            "supply the needed memory/register equality beforehand with `have h : ... := by ...`, or compact the state with `wp_compact` before `wp_done`"
            (gOpt? := some g) do
            evalTactic (← `(tactic| (
              try wp_norm_goal
              try wp_rewrite_reads
              try wp_resolve_ites
              repeat' (first | apply And.intro | arm64_instantiate_sep_exists)
            )))
            if ← outerHeartbeatsExhausted then
              throwHeartbeatPhaseError "wp_done" "postcondition normalization and memory-read rewriting (`wp_norm_goal` / `wp_rewrite_reads`)"
                "supply the needed memory/register equality beforehand with `have h : ... := by ...`, or compact the state with `wp_compact` before `wp_done`"
                (some g)
          let innerGoals ← getGoals
          let mut satGoals : List MVarId := []
          let mut pureGoals : List MVarId := []
          for ig in innerGoals do
            if ← ig.isAssigned then continue
            let igTy ← ig.withContext (instantiateMVars (← ig.getType))
            if igTy.consumeMData.isAppOfArity ``SepProp.Satisfies 2 then
              satGoals := satGoals ++ [ig]
            else
              pureGoals := pureGoals ++ [ig]
          for ig in satGoals do
            if ← ig.isAssigned then continue
            setGoals [ig]
            let igTy ← ig.withContext (instantiateMVars (← ig.getType))
            let targetFull := igTy.consumeMData.getArg! 0
            let mGoal := igTy.consumeMData.getArg! 1
            let hbSatRef ← IO.mkRef (none : Option String)
            let closedSat ←
              (tryTacticTrackHeartbeatBool hbSatRef "spatial postcondition framing (`arm64_sep_close`)" <| withHeartbeatCap 200000 do
                evalTactic (← `(tactic| (arm64_sep_close; done)))
                unless (← getGoals).isEmpty do throwError "unsolved") <||>
              (tryTacticTrackHeartbeatBool hbSatRef "spatial postcondition framing (`wp_frame_split`)" <| withHeartbeatCap 100000 do
                evalTactic (← `(tactic| wp_frame_split))
                unless (← getGoals).isEmpty do throwError "unsolved")
            if !closedSat then
              if let some phase ← hbSatRef.get then
                throwHeartbeatPhaseError "wp_done" phase
                  "focus or split the mismatched spatial container (`wp_focus` / `memRegion_split`), or supply the address offset equality with `have h : ... := by bv_omega`"
                  (some ig)
              ig.withContext do
                let mut actualFull := mkConst ``SepProp.emp
                if let some (_, P) ← SepSolver.findSatHyp? mGoal then
                  actualFull := P
                if let some msg ← checkSpatialPostMismatch actualFull targetFull then
                  throwError msg
                let msg ← SepSolver.explainFrameSplitFailure targetFull actualFull
                throwError "wp_done: spatial postcondition mismatch:\n{msg}"
          for ig in pureGoals do
            if ← ig.isAssigned then continue
            setGoals [ig]
            closeWpDonePureSubgoal tyPreNormOpt
        else
          let hId ← freshIdent `h_intro
          evalTactic (← `(tactic| intro $hId:ident))
          unfoldPreservedHypsAndGoal
          closeWpDonePureSubgoal
      | _ =>
        if ty.consumeMData.isAppOfArity ``SepProp.Entails 2 then
          let lhsP := ty.consumeMData.getArg! 0
          let rhsP := ty.consumeMData.getArg! 1
          let (_, hypIds) ← g.withContext getLightweightSimpHyps
          let hbEntRef ← IO.mkRef (none : Option String)
          let closedEnt ← tryTacticTrackHeartbeatBool hbEntRef "spatial entailment (`sep_entail`)" <| withHeartbeatCap 50000 do
            evalTactic (← `(tactic| (
              try simp (config := { decide := true }) only [
                sepConj_assoc, emp_sepConj, sepConj_emp,
                wp_norm, arm64_norm, $[$hypIds:ident],*]
              first
                | sep_entail
                | (apply Entails.of_eq_explicit;
                   try with_reducible rfl;
                   repeat' (first | with_reducible rfl | apply sepConj_congr | apply pointsTo64_congr_val | apply pointsTo8_congr_val | apply pointsToBytes_congr_bytes | apply pointsToBytesRO_congr_bytes);
                   all_goals (first | done | with_reducible rfl | wp_assumption | with_reducible assumption | (bv_omega_fast; done) | (wp_omega_bounded; done) | (byte_region_eq; done) | (bv_fallback; done)))
            )))
            unless (← getGoals).isEmpty do throwError "unsolved"
          if !closedEnt then
            if let some phase ← hbEntRef.get then
              throwHeartbeatPhaseError "wp_done" phase
                "focus or split the mismatched spatial container (`wp_focus` / `memRegion_split`), or supply the address/byte-slice equality with `have h : ... := by bv_omega`"
                (some g)
            g.withContext do
              if let some msg ← checkSpatialPostMismatch lhsP rhsP then
                throwError msg
              let msg ← SepSolver.explainFrameSplitFailure rhsP lhsP
              throwError "wp_done: spatial postcondition mismatch:\n{msg}"
        else
          closeWpDonePureSubgoal
      remaining := remaining ++ (← getGoals)
    setGoals (remaining ++ restDone)
    let unsolved ← getUnsolvedGoals
    setGoals unsolved
    if !allowResidual && !unsolved.isEmpty then
      throwWpDoneResidualGoalsError unsolved

/-- Close a `SepWP` (or `SepWPp`) goal once execution has reached `target_pc`:
    discharges register postconditions, `CalleeSavedPreserved`, spatial entailments (`P_f ⊢ postMem`),
    memory reads owned by the spatial context (`wp_rewrite_reads`), and separation-logic
    postconditions (`sf.mem ⊨ spec.post x sf ∗ R`) via `arm64_sep_close`.
    Throws structured diagnostics on PC mismatches, postcondition diffs, or open residual goals
    (use `wp_done?` or `set_option proofLib.wpDoneAllowResidualGoals true` to leave unfocused
    sibling goals open). -/
elab "wp_done" : tactic => do
  wpDoneCore (allowResidual := proofLib.wpDoneAllowResidualGoals.get (← getOptions))

/-- Variant of `wp_done` that closes the current `SepWP` / `SepWPp` goal and leaves any unfocused
    sibling subgoals open for subsequent tactics instead of throwing a residual-goal error. -/
elab "wp_done?" : tactic => do
  wpDoneCore (allowResidual := true)

/-- Automatically execute `wp_steps`, split conditional branches with `wp_if`, and discharge
    completed execution paths with `wp_done`. -/
partial def wpAutoCore (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then return
  let gs0 ← getGoals
  if gs0.isEmpty then return
  -- Run `wp_steps`, recording any undecided PC condition so `full`-level resolution below does
  -- not repeat the fast `omega` pass on it.
  let stepFailed ← IO.mkRef (#[] : Array Expr)
  wpStepsCore 128 (quiet := true) (stepFailed := some stepFailed)
  let gs1 ← getGoals
  if gs1.isEmpty then return
  let (_, targetPcExpr, pcExpr) ← getSepWPStateAndPC
  let atTarget ← withoutModifyingState do
    tryTacticCatchRuntimeBool do
      if ← pcReachedTarget pcExpr targetPcExpr then Pure.pure () else throwError "not at target"
  if atTarget then
    wpDoneCore (allowResidual := true)
  else if pcExpr.isAppOfArity ``ite 5 then
    let c := pcExpr.getArg! 1
    if let some (condTrue, propTy, prf) ← resolveIteCondFast? c (forStepPC := false) stepFailed then
      let hId ← freshIdent `hcond
      let detIte ← tryTacticCatchRuntimeBool do
        if condTrue then
          evalTactic (← `(tactic| (apply SepWP.ite_true; wp_focus_close wp_norm_lhs)))
        else
          evalTactic (← `(tactic| (apply SepWP.ite_false; wp_focus_close wp_norm_lhs)))
        let gCond :: gsRest ← getGoals | throwError "expected condition subgoal"
        if ← gCond.withContext do isDefEq (← inferType prf) (← gCond.getType) then
          gCond.assign prf
          setGoals gsRest
        else
          throwError "wp_auto: condition proof type mismatch"
      if detIte then
        let g ← getMainGoal
        let g' ← g.assert hId.getId propTy prf
        let (_, g'') ← g'.intro1P
        replaceMainGoal [g'']
        evalTactic (← `(tactic| (
          try simp (config := { decide := true }) only [
            beq_iff_eq, bne_iff_ne, Classical.not_not,
            wp_norm, arm64_norm] at $hId:ident
          try wp_norm_state
        )))
        wpAutoCore (fuel - 1)
        return
    evalTactic (← `(tactic| wp_if))
    let gs ← getGoals
    match gs with
    | gThen :: gElse :: rest =>
      setGoals [gThen]
      wpAutoCore (fuel - 1)
      let remThen ← getGoals
      setGoals [gElse]
      wpAutoCore (fuel - 1)
      let remElse ← getGoals
      setGoals (remThen ++ remElse ++ rest)
    | _ => Pure.pure ()

elab "wp_auto" : tactic => do
  wpAutoCore 64

/-- Rewrite the current `SepWP` / `SepWPp` state's hypotheses using equalities from earlier
    intermediate `State` variables, then clear those intermediate states and their equality
    hypotheses to keep the local context small across long subroutine proofs. -/
elab "wp_compact" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let curS := (ty.getArg! 2).consumeMData
    let some curFVar := curS.fvarId? | return
    let lctx ← getLCtx
    let mut oldStateFVars : Array FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let dty ← instantiateMVars decl.type
        if dty.isConstOf ``Arm64.State && decl.fvarId != curFVar && decl.userName != `s0 then
          oldStateFVars := oldStateFVars.push decl.fvarId
    let mut oldEqIdents : Array Ident := #[]
    let mut curHypIdents : Array Ident := #[]
    let mut toClear : Array FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let dty ← instantiateMVars decl.type
        if ← isProp dty then
          let mentionsCur := (dty.find? fun e => e.isFVar && e.fvarId! == curFVar).isSome
          let mentionsOld := (dty.find? fun e => e.isFVar && oldStateFVars.contains e.fvarId!).isSome
          if mentionsCur then
            curHypIdents := curHypIdents.push (mkIdent decl.userName)
          else if mentionsOld then
            let isNeZero := dty.isAppOf ``Not || dty.isAppOf ``Ne
            if !isNeZero then
              toClear := toClear.push decl.fvarId
              if dty.isAppOfArity ``Eq 3 then
                oldEqIdents := oldEqIdents.push (mkIdent decl.userName)
    if !oldEqIdents.isEmpty && !curHypIdents.isEmpty then
      evalTactic (← `(tactic| simp only [$[$oldEqIdents:ident],*] at $[$curHypIdents:ident]*))
    let g' ← getMainGoal
    let g'' ← g'.tryClearMany (toClear ++ oldStateFVars)
    replaceMainGoal [g'']

private def simplifyWpBranchGoal (h : Ident) (isBoolFalse : Bool) : TacticM Unit := do
  if isBoolFalse then
    evalTactic (← `(tactic| try (wp_conv_pre => simp (disch := first | decide | wp_omega_bounded) only [$h:ident, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, wp_branch])))
    evalTactic (← `(tactic| try (wp_conv_post => simp (disch := first | decide | wp_omega_bounded) only [$h:ident, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, wp_branch])))
    evalTactic (← `(tactic| try simp (disch := first | decide | wp_omega_bounded) only [$h:ident, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, wp_branch]))
  else
    evalTactic (← `(tactic| try (wp_conv_pre => simp (disch := first | decide | wp_omega_bounded) only [$h:ident, ↓reduceIte, ↓reduceDIte, wp_branch])))
    evalTactic (← `(tactic| try (wp_conv_post => simp (disch := first | decide | wp_omega_bounded) only [$h:ident, ↓reduceIte, ↓reduceDIte, wp_branch])))
    evalTactic (← `(tactic| try simp (disch := first | decide | wp_omega_bounded) only [$h:ident, ↓reduceIte, ↓reduceDIte, wp_branch]))

private def isHeadIteWpGoal : TacticM Bool := do
  let g ← getMainGoal
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if !(tgt.isAppOf ``SepWP || tgt.isAppOf ``SepWPp) then
    return false
  if tgt.getAppNumArgs < 3 then
    return false
  let s := tgt.getArg! 2
  let pc0 ← g.withContext do extractSepWPPC s
  let pc1 ← g.withContext do Lean.Meta.whnfR (Lean.mkApp (Lean.mkConst ``State.pc) s)
  return pc0.consumeMData.isAppOf ``ite || pc1.consumeMData.isAppOf ``ite

private def evalWpCasesHeadIte (h? : Option Ident) : TacticM Unit := do
  if !(← isHeadIteWpGoal) then
    throwError "wp_cases: expected a `SepWP` goal with an `ite` PC, or pass an explicit condition `wp_cases h : cond` / `wp_cases cond`"
  let hId ← match h? with
    | some id => Pure.pure id
    | none => freshIdent `hcond
  evalTactic (← `(tactic| wp_if $hId:ident))
  let gs ← getGoals
  match gs with
  | [gThen, gElse] =>
    setGoals [gThen]
    simplifyWpBranchGoal hId false
    let gsThen ← getGoals
    setGoals [gElse]
    simplifyWpBranchGoal hId false
    let gsElse ← getGoals
    setGoals (gsThen ++ gsElse)
  | _ => Pure.pure ()

private def evalWpCasesCond (h : Ident) (cond : Term) : TacticM Unit := do
  let condExpr ← elabTerm cond none false
  let condTy ← inferType condExpr
  if condTy.isConstOf ``Bool then
    evalTactic (← `(tactic| by_cases $h:ident : $cond = true))
    let goals ← getGoals
    match goals with
    | [gTrue, gFalse] =>
      setGoals [gTrue]
      simplifyWpBranchGoal h false
      let gTrueAfter ← getGoals
      setGoals [gFalse]
      evalTactic (← `(tactic| replace $h:ident : $cond = false := Bool.eq_false_iff.mpr $h:ident))
      simplifyWpBranchGoal h true
      let gFalseAfter ← getGoals
      setGoals (gTrueAfter ++ gFalseAfter)
    | _ => Pure.pure ()
  else
    evalTactic (← `(tactic| by_cases $h:ident : $cond))
    let goals ← getGoals
    match goals with
    | [gTrue, gFalse] =>
      setGoals [gTrue]
      simplifyWpBranchGoal h false
      let gTrueAfter ← getGoals
      setGoals [gFalse]
      simplifyWpBranchGoal h false
      let gFalseAfter ← getGoals
      setGoals (gTrueAfter ++ gFalseAfter)
    | _ => Pure.pure ()

/-- Unified conditional branch tactic for `SepWP`:
    - `wp_cases`: split the head `if c then pc1 else pc2` PC of the `SepWP` goal.
    - `wp_cases h : cond`: split on `Bool` or decidable `Prop` condition `cond` with hypothesis `h`.
    - `wp_cases cond`: split on `cond` with a fresh hypothesis (or name the head `ite` branch `h`
      when `cond` is a fresh identifier not in the local context). -/
syntax "wp_cases" : tactic
syntax "wp_cases" ppSpace colGt atomic(ident " : ") term : tactic
syntax "wp_cases" ppSpace colGt term : tactic

elab_rules : tactic
  | `(tactic| wp_cases) => evalWpCasesHeadIte none
  | `(tactic| wp_cases $h:ident : $cond:term) => evalWpCasesCond h cond
  | `(tactic| wp_cases $cond:term) => do
    if cond.raw.isIdent then
      let g ← getMainGoal
      let inLCtx ← g.withContext do
        return (← getLCtx).findFromUserName? cond.raw.getId |>.isSome
      if !inLCtx && (← isHeadIteWpGoal) then
        evalWpCasesHeadIte (some ⟨cond.raw⟩)
        return
    let hId ← freshIdent `hcond
    evalWpCasesCond hId cond

/-- Split on a `Bool` or decidable `Prop` condition `cond`, normalize both the true and false
    hypotheses in context (`h : cond = true` vs. `h : cond = false` when `cond : Bool`), and
    automatically simplify `if`/`dite` inside the `SepWP` precondition/postcondition across
    both branches. -/
macro "wp_by_cases " h:ident " : " cond:term : tactic =>
  `(tactic| wp_cases $h:ident : $cond)

/-! ## Symbol-Relative Step and Cut Tactics -/

/-- Infer the function `entry : Expr` (`BitVec 64`) and current state's function-relative byte
    offset `curOff : Nat` from the main `SepWP` or `SepWPp` goal and local `s0.pc = entry`
    hypotheses (or use `entryOverride?` when provided). -/
def getGoalEntryAndCurOff (entryOverride? : Option Expr := none) : TacticM (Expr × Nat) := do
  let g ← getMainGoal
  g.withContext do
    let tgt := (← instantiateMVars (← g.getType)).consumeMData
    let isWp := tgt.isAppOfArity ``SepWP 6
    let isWpp := tgt.isAppOfArity ``SepWPp 7
    unless isWp || isWpp do
      throwError "expected `SepWP` or `SepWPp` goal, got{indentExpr tgt}"
    let mut fnAddrEqs : Array (Expr × Option String × Expr) := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, l, r) := ty.eq? then
          let l := SepSolver.stripMData l
          let r := SepSolver.stripMData r
          if l.isAppOfArity ``Program.fnAddr 2 && !r.isAppOfArity ``State.pc 1 then
            fnAddrEqs := fnAddrEqs.push (l, ← extractFnAddrSym? l, r)
          else if r.isAppOfArity ``Program.fnAddr 2 && !l.isAppOfArity ``State.pc 1 then
            fnAddrEqs := fnAddrEqs.push (r, ← extractFnAddrSym? r, l)
        else
          let tyW ← whnf ty
          if tyW.isAppOfArity ``And 2 then
            if let some (_, l, r) := (← whnf (tyW.getArg! 0)).eq? then
              let l := SepSolver.stripMData l
              let r := SepSolver.stripMData r
              if l.isAppOfArity ``Program.fnAddr 2 then
                fnAddrEqs := fnAddrEqs.push (l, ← extractFnAddrSym? l, r)
    let resolveFnAddr (e : Expr) : MetaM Expr := do
      let e := SepSolver.stripMData e
      let sym? ← extractFnAddrSym? e
      for (l, lSym?, r) in fnAddrEqs do
        if l == e || (sym?.isSome && sym? == lSym?) then
          return r
      return e
    let decomposeAddr (e : Expr) : MetaM (Expr × Nat) := do
      let (b0, o0) ← sepAddrBaseOff e
      let b0' ← resolveFnAddr b0
      if b0' != b0 then
        let (b1, o1) ← sepAddrBaseOff b0'
        return (b1, (o1 + o0) % (2 ^ 64))
      return (b0, o0)
    let s := tgt.getArg! 2
    let pc ← extractRawCallAddr (mkApp (mkConst ``State.pc) s)
    let (pcBase, pcOff) ← decomposeAddr pc
    if let some entryExpr := entryOverride? then
      let (entryBase, entryOff) ← decomposeAddr entryExpr
      let curOff := if pcBase == entryBase && pcOff ≥ entryOff then pcOff - entryOff else 0
      return (entryExpr, curOff)
    -- Look for the earliest `s_init.pc = entryRhs` hypothesis sharing `pcBase` with `entryOff ≤ pcOff`:
    let mut bestEntry? : Option (Expr × Nat) := none
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOfArity ``State.pc 1 then
            let (eb, eo) ← decomposeAddr rhs
            if eb == pcBase && eo ≤ pcOff then
              match bestEntry? with
              | none => bestEntry? := some (rhs, eo)
              | some (_, prevEo) =>
                if eo < prevEo then bestEntry? := some (rhs, eo)
    if let some (entryExpr, entryOff) := bestEntry? then
      return (entryExpr, pcOff - entryOff)
    if pcOff == 0 then
      return (pc, 0)
    return (pcBase, pcOff)

/-- True if `ty` WHNF-reduces to a relocation-table type (`List/Array Obj.RelocEntry`,
    `List/Array (Nat × String)`, or `Obj.SymCodeInfo`). -/
def isRelocTableType (ty : Expr) : MetaM Bool := do
  let ty ← withTransparency .all (whnf ty)
  if ty.isConstOf ``Arm64.Obj.SymCodeInfo then return true
  if ty.isAppOfArity ``List 1 || ty.isAppOfArity ``Array 1 then
    let elemTy ← withTransparency .all (whnf (ty.getArg! 0))
    if elemTy.isConstOf ``Arm64.Obj.RelocEntry then return true
    if elemTy.isAppOfArity ``Prod 2 then
      let fstTy ← withTransparency .all (whnf (elemTy.getArg! 0))
      let sndTy ← withTransparency .all (whnf (elemTy.getArg! 1))
      if fstTy.isConstOf ``Nat && sndTy.isConstOf ``String then return true
  return false

def resolveCallTargetOff2 (srcStx targetStx : Term) (k : Nat := 0) :
    TacticM (Expr × Nat × Nat) := do
  let g ← getMainGoal
  let (srcExpr, targetExpr) ← g.withContext do
    let sE ← Term.elabTermAndSynthesize srcStx none
    let tE ← Term.elabTermAndSynthesize targetStx none
    pure (← instantiateMVars sE, ← instantiateMVars tE)
  let (entryExpr, curOff) ← getGoalEntryAndCurOff none
  let callOff ← g.withContext do
    let srcTy ← inferType srcExpr
    if ← isRelocTableType srcTy then
      let some sym ← CodeLookup.evalStringExpr? targetExpr
        | throwError "expected callee symbol string literal, got `{targetExpr}`"
      CodeLookup.lookupRelocCallOff srcExpr sym k
    else
      CodeLookup.lookupCodeCallOff srcExpr entryExpr targetExpr k
  return (entryExpr, callOff, curOff)

def resolveCallTargetOff3 (arg1Stx arg2Stx arg3Stx : Term) (k : Nat := 0) :
    TacticM (Expr × Nat × Nat) := do
  let g ← getMainGoal
  let (e1, e2, e3) ← g.withContext do
    let a1 ← Term.elabTermAndSynthesize arg1Stx none
    let a2 ← Term.elabTermAndSynthesize arg2Stx none
    let a3 ← Term.elabTermAndSynthesize arg3Stx none
    pure (← instantiateMVars a1, ← instantiateMVars a2, ← instantiateMVars a3)
  let e1Ty ← g.withContext do withTransparency .all (whnf (← inferType e1))
  if e1Ty.isAppOfArity ``BitVec 1 then
    let (entryExpr, curOff) ← getGoalEntryAndCurOff (some e1)
    let callOff ← g.withContext do
      let e2Ty ← inferType e2
      if ← isRelocTableType e2Ty then
        let some sym ← CodeLookup.evalStringExpr? e3
          | throwError "expected callee symbol string literal, got `{e3}`"
        CodeLookup.lookupRelocCallOff e2 sym k
      else
        CodeLookup.lookupCodeCallOff e2 entryExpr e3 k
    return (entryExpr, callOff, curOff)
  else
    let callOff ← g.withContext do CodeLookup.lookupCodeCallOff e1 e2 e3 k
    let e2Ty ← g.withContext do withTransparency .all (whnf (← inferType e2))
    let (entryExpr, curOff) ←
      if e2Ty.isAppOfArity ``BitVec 1 then getGoalEntryAndCurOff (some e2)
      else getGoalEntryAndCurOff none
    return (entryExpr, callOff, curOff)

def resolveCallTargetOffArgs (tag : String) (args : Array Term) : TacticM (Expr × Nat × Nat) := do
  if args.size == 2 then
    resolveCallTargetOff2 args[0]! args[1]! 0
  else if args.size == 3 then
    if let some k := args[2]!.raw.isNatLit? then
      resolveCallTargetOff2 args[0]! args[1]! k
    else
      resolveCallTargetOff3 args[0]! args[1]! args[2]! 0
  else if args.size == 4 then
    let some k := args[3]!.raw.isNatLit?
      | throwError "{tag}: expected natural number occurrence index as 4th argument, got `{args[3]!}`"
    resolveCallTargetOff3 args[0]! args[1]! args[2]! k
  else
    throwError "{tag}: expected 2, 3, or 4 arguments (`<relocs> \"<sym>\" [k]` or `<code> <entry> <target> [k]`), got {args.size}"

/-- Step a `SepWP` goal from the current PC up to byte offset `targetOff` (relative to function entry
    where current PC is at `curOff`), executing `(targetOff - curOff) / 4` instructions. -/
def stepWpToOffset (tag : String) (targetOff curOff : Nat) : TacticM Unit := do
  unless curOff ≤ targetOff do
    throwError "{tag}: target byte offset {targetOff} precedes current PC byte offset {curOff}"
  unless (targetOff - curOff) % 4 == 0 do
    throwError "{tag}: byte distance {targetOff - curOff} (from +{curOff} to +{targetOff}) is not 4-byte aligned"
  let nSteps := (targetOff - curOff) / 4
  if nSteps > 0 then
    let verbose := CondClassify.proofLib.wpVerbose.get (← getOptions)
    wpStepsCore nSteps (quiet := !verbose) (warnOnBoundReached := false)

/-- Cut a `SepWP` or `SepWPp` goal at `entryExpr + BitVec.ofNat 64 callOff` using `SepWP.cut` or
    `SepWPp.of_sepWP`. -/
def cutWpAtOffset (entryExpr : Expr) (callOff : Nat) : TacticM Unit := do
  let g ← getMainGoal
  let (isWpp, entryStx) ← g.withContext do
    let tgt := (← instantiateMVars (← g.getType)).consumeMData
    pure (tgt.isAppOfArity ``SepWPp 7, ← Term.exprToSyntax (← instantiateMVars entryExpr))
  let lit := Syntax.mkNumLit (toString callOff)
  if isWpp then
    let ofSepWpId := mkCIdent ``SepWPp.of_sepWP
    evalTactic (← `(tactic| apply $ofSepWpId (mid := ($entryStx : BitVec 64) + BitVec.ofNat 64 $lit)))
  else
    let cutId := mkCIdent ``SepWP.cut
    evalTactic (← `(tactic| apply $cutId (mid := ($entryStx : BitVec 64) + BitVec.ofNat 64 $lit)))
  (← getGoals).forM instantiateMVarDeclMVars

/-- Step a `SepWP` goal up to the `k`-th (0-indexed, default `0`) call site without hard-coding
    byte offsets or instruction counts:
    - `wp_steps_to_call <relocs> "<sym>" [k]`
    - `wp_steps_to_call <entry> <relocs> "<sym>" [k]`
    - `wp_steps_to_call <code> <entry> <target> [k]` -/
syntax "wp_steps_to_call" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| wp_steps_to_call $args:term*) => do
    let (_, callOff, curOff) ← resolveCallTargetOffArgs "wp_steps_to_call" args
    stepWpToOffset "wp_steps_to_call" callOff curOff

/-- Step a `SepWP` goal up to the `k`-th (0-indexed, default `0`) `RET` instruction in `<words>`:
    `wp_steps_to_ret <words> [k]`. -/
syntax "wp_steps_to_ret" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| wp_steps_to_ret $args:term*) => do
    unless args.size == 1 || args.size == 2 do
      throwError "wp_steps_to_ret: expected `<words> [k]`, got {args.size} arguments"
    let w := args[0]!
    let k ← if args.size == 2 then
        let some n := args[1]!.raw.isNatLit?
          | throwError "wp_steps_to_ret: expected occurrence index numeral, got `{args[1]!}`"
        pure n
      else pure 0
    let g ← getMainGoal
    let retOff ← g.withContext do
      let wE ← instantiateMVars (← Term.elabTermAndSynthesize w none)
      CodeLookup.lookupWordsRetOff wE k
    let (_, curOff) ← getGoalEntryAndCurOff none
    stepWpToOffset "wp_steps_to_ret" retOff curOff

/-- Step a `SepWP` goal up to the `k`-th (0-indexed, default `0`) instruction in `<words>`
    matching `<target>`: `wp_steps_to_insn <words> <target> [k]`. -/
syntax "wp_steps_to_insn" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| wp_steps_to_insn $args:term*) => do
    unless args.size == 2 || args.size == 3 do
      throwError "wp_steps_to_insn: expected `<words> <target> [k]`, got {args.size} arguments"
    let w := args[0]!
    let t := args[1]!
    let k ← if args.size == 3 then
        let some n := args[2]!.raw.isNatLit?
          | throwError "wp_steps_to_insn: expected occurrence index numeral, got `{args[2]!}`"
        pure n
      else pure 0
    let g ← getMainGoal
    let insnOff ← g.withContext do
      let wE ← instantiateMVars (← Term.elabTermAndSynthesize w none)
      let tE ← instantiateMVars (← Term.elabTermAndSynthesize t none)
      CodeLookup.lookupWordsInsnOff wE tE k
    let (_, curOff) ← getGoalEntryAndCurOff none
    stepWpToOffset "wp_steps_to_insn" insnOff curOff

/-- Cut a `SepWP` (via `SepWP.seq`) or `SepWPp` (via `SepWPp.of_sepWP`) goal at the `k`-th
    (0-indexed, default `0`) call site without hard-coding a numeric byte offset:
    - `wp_cut_call <relocs> "<sym>" [k]`
    - `wp_cut_call <entry> <relocs> "<sym>" [k]`
    - `wp_cut_call <code> <entry> <target> [k]` -/
syntax "wp_cut_call" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| wp_cut_call $args:term*) => do
    let (entryExpr, callOff, _) ← resolveCallTargetOffArgs "wp_cut_call" args
    cutWpAtOffset entryExpr callOff

/-- Cut a `SepWPp` (or `SepWP`) goal at a named call site (`sepWPp_cut_call`). -/
syntax "sepWPp_cut_call" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| sepWPp_cut_call $args:term*) => do
    let (entryExpr, callOff, _) ← resolveCallTargetOffArgs "sepWPp_cut_call" args
    cutWpAtOffset entryExpr callOff

end

end ProofLib
