/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.SepLogic.OmegaBounded
public import ProofLib.SepLogic.WP.ProjGuardAttr
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.VCGen
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.CondClassify
public import ProofLib.BV.Arith
public import ProofLib.SepLogic.WP.StateNorm
public import ProofLib.SepLogic.WP.Access
public import ProofLib.SepLogic.WP.StepsCore
public import ProofLib.SepLogic.WP.StepsSimd
public import ProofLib.SepLogic.WP.StepsSubword
public import ProofLib.SepLogic.WP.Structural

/-!
# Core WP Normalization, Spatial Access, and Branch Resolution

Defines the `wp_focus_close` subgoal combinator, spine-lifting spatial load/store/frame solvers
(`wp_sep_access`), cached `wp_norm_*` state and goal normalizers, hypothesis splitters, and
conditional branch decision procedures (`decideCond?`, `resolveIteCondFast?`).
-/

namespace ProofLib

open Arm64
open Lean Elab Tactic Meta

public meta section

initialize registerTraceClass `wp.pc

section TableProjGuards

private def internedSymDataAllowHeads : Array Name :=
  #[`Arm64.Obj.Interned.Data.toInfo]

private def codeBlockAllowHeads : Array Name :=
  #[`Arm64.Obj.Interned.Lib.block, `Arm64.Obj.Interned.Block.toCodeBlock]

private def placedLibAllowHeads : Array Name :=
  #[`Arm64.Obj.Interned.Lib.toLib, ``Arm64.Obj.MultiPlacedLib.blockLib]

private def multiPlacedLibAllowHeads : Array Name :=
  #[`Arm64.Obj.Interned.MultiLib.toMultiPlacedLib]

private def programAllowHeads : Array Name :=
  #[``Arm64.Program.rebase, ``Arm64.Program.ofImage, ``Arm64.Program.ofImageWithSvc,
    ``Arm64.Obj.LinkedImage.toProgram, ``Arm64.Obj.LinkedImage.toProgramWithSvc,
    ``Arm64.Obj.PlacedLib.program, ``Arm64.Obj.MultiPlacedLib.blockProgram]

declare_wp_proj_guard guardObjImageCode Arm64.Obj.Image code ``Arm64.Obj.Image.code ``Arm64.Obj.Image.mk
declare_wp_proj_guard guardObjImageData Arm64.Obj.Image data ``Arm64.Obj.Image.data ``Arm64.Obj.Image.mk
declare_wp_proj_guard guardObjImageRoData Arm64.Obj.Image roData ``Arm64.Obj.Image.roData ``Arm64.Obj.Image.mk
declare_wp_proj_guard guardObjImageExternData Arm64.Obj.Image externData ``Arm64.Obj.Image.externData ``Arm64.Obj.Image.mk
declare_wp_proj_guard guardObjImageGot Arm64.Obj.Image got ``Arm64.Obj.Image.got ``Arm64.Obj.Image.mk
declare_wp_proj_guard guardObjImageSymbols Arm64.Obj.Image symbols ``Arm64.Obj.Image.symbols ``Arm64.Obj.Image.mk
declare_wp_proj_guard guardObjImageObjSymbols Arm64.Obj.Image objSymbols ``Arm64.Obj.Image.objSymbols ``Arm64.Obj.Image.mk
declare_wp_proj_guard guardObjImageStubs Arm64.Obj.Image stubs ``Arm64.Obj.Image.stubs ``Arm64.Obj.Image.mk

declare_wp_proj_guard guardLinkedImageCode Arm64.Obj.LinkedImage code ``Arm64.Obj.LinkedImage.code ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageData Arm64.Obj.LinkedImage data ``Arm64.Obj.LinkedImage.data ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageRoData Arm64.Obj.LinkedImage roData ``Arm64.Obj.LinkedImage.roData ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageExternData Arm64.Obj.LinkedImage externData ``Arm64.Obj.LinkedImage.externData ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageGot Arm64.Obj.LinkedImage got ``Arm64.Obj.LinkedImage.got ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageRelocs Arm64.Obj.LinkedImage relocs ``Arm64.Obj.LinkedImage.relocs ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageSymbols Arm64.Obj.LinkedImage symbols ``Arm64.Obj.LinkedImage.symbols ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageObjSymbols Arm64.Obj.LinkedImage objSymbols ``Arm64.Obj.LinkedImage.objSymbols ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageStubs Arm64.Obj.LinkedImage stubs ``Arm64.Obj.LinkedImage.stubs ``Arm64.Obj.LinkedImage.mk
declare_wp_proj_guard guardLinkedImageObjects Arm64.Obj.LinkedImage objects ``Arm64.Obj.LinkedImage.objects ``Arm64.Obj.LinkedImage.mk

declare_wp_proj_guard guardObjectInfoFns Arm64.Obj.ObjectInfo fns ``Arm64.Obj.ObjectInfo.fns ``Arm64.Obj.ObjectInfo.mk
declare_wp_proj_guard guardObjectInfoCallFns Arm64.Obj.ObjectInfo callFns ``Arm64.Obj.ObjectInfo.callFns ``Arm64.Obj.ObjectInfo.mk
declare_wp_proj_guard guardObjectInfoRelocFns Arm64.Obj.ObjectInfo relocFns ``Arm64.Obj.ObjectInfo.relocFns ``Arm64.Obj.ObjectInfo.mk
declare_wp_proj_guard guardObjectInfoDataSyms Arm64.Obj.ObjectInfo dataSyms ``Arm64.Obj.ObjectInfo.dataSyms ``Arm64.Obj.ObjectInfo.mk
declare_wp_proj_guard guardSymCodeInfoCode Arm64.Obj.SymCodeInfo code ``Arm64.Obj.SymCodeInfo.code ``Arm64.Obj.SymCodeInfo.mk
declare_wp_proj_guard guardSymCodeInfoRelocs Arm64.Obj.SymCodeInfo relocs ``Arm64.Obj.SymCodeInfo.relocs ``Arm64.Obj.SymCodeInfo.mk
declare_wp_proj_guard guardSymDataInfoBytes Arm64.Obj.SymDataInfo bytes ``Arm64.Obj.SymDataInfo.bytes ``Arm64.Obj.SymDataInfo.mk internedSymDataAllowHeads
declare_wp_proj_guard guardSymDataInfoRelocs Arm64.Obj.SymDataInfo relocs ``Arm64.Obj.SymDataInfo.relocs ``Arm64.Obj.SymDataInfo.mk internedSymDataAllowHeads

declare_wp_proj_guard guardCodeBlockCode Arm64.Obj.CodeBlock code ``Arm64.Obj.CodeBlock.code ``Arm64.Obj.CodeBlock.mk codeBlockAllowHeads
declare_wp_proj_guard guardCodeBlockSymbols Arm64.Obj.CodeBlock symbols ``Arm64.Obj.CodeBlock.symbols ``Arm64.Obj.CodeBlock.mk codeBlockAllowHeads
declare_wp_proj_guard guardCodeBlockRelocs Arm64.Obj.CodeBlock relocs ``Arm64.Obj.CodeBlock.relocs ``Arm64.Obj.CodeBlock.mk codeBlockAllowHeads
declare_wp_proj_guard guardCodeBlockExterns Arm64.Obj.CodeBlock externs ``Arm64.Obj.CodeBlock.externs ``Arm64.Obj.CodeBlock.mk codeBlockAllowHeads

declare_wp_proj_guard guardPlacedLibText Arm64.Obj.PlacedLib text ``Arm64.Obj.PlacedLib.text ``Arm64.Obj.PlacedLib.mk placedLibAllowHeads
declare_wp_proj_guard guardPlacedLibData Arm64.Obj.PlacedLib data ``Arm64.Obj.PlacedLib.data ``Arm64.Obj.PlacedLib.mk placedLibAllowHeads
declare_wp_proj_guard guardPlacedLibExports Arm64.Obj.PlacedLib exports ``Arm64.Obj.PlacedLib.exports ``Arm64.Obj.PlacedLib.mk placedLibAllowHeads

declare_wp_proj_guard guardMultiPlacedLibBlocks Arm64.Obj.MultiPlacedLib blocks ``Arm64.Obj.MultiPlacedLib.blocks ``Arm64.Obj.MultiPlacedLib.mk multiPlacedLibAllowHeads
declare_wp_proj_guard guardMultiPlacedLibData Arm64.Obj.MultiPlacedLib data ``Arm64.Obj.MultiPlacedLib.data ``Arm64.Obj.MultiPlacedLib.mk multiPlacedLibAllowHeads
declare_wp_proj_guard guardMultiPlacedLibExports Arm64.Obj.MultiPlacedLib exports ``Arm64.Obj.MultiPlacedLib.exports ``Arm64.Obj.MultiPlacedLib.mk multiPlacedLibAllowHeads

declare_wp_proj_guard guardElfImageSegments Arm64.Process.ElfImage segments ``Arm64.Process.ElfImage.segments ``Arm64.Process.ElfImage.mk
declare_wp_proj_guard guardElfImageSymbols Arm64.Process.ElfImage symbols ``Arm64.Process.ElfImage.symbols ``Arm64.Process.ElfImage.mk

declare_wp_proj_guard guardProgramCode Arm64.Program code ``Arm64.Program.code ``Arm64.Program.mk programAllowHeads
declare_wp_proj_guard guardProgramSymbols Arm64.Program symbols ``Arm64.Program.symbols ``Arm64.Program.mk programAllowHeads
declare_wp_proj_guard guardProgramStubs Arm64.Program stubs ``Arm64.Program.stubs ``Arm64.Program.mk programAllowHeads

end TableProjGuards

/-- Like `tryTacticCatchRuntime`, but returns the failure message (`.error msg`) instead of `none`,
    so callers can report why a step failed. State and message log are restored on failure. -/
def tryTacticCatchRuntimeMsg {α : Type} (tac : TacticM α) : TacticM (Except MessageData α) := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  try
    MonadRuntimeException.tryCatchRuntimeEx
      (do
        let res ← withoutRecover tac
        return .ok res)
      (fun ex => do
        restoreState saved
        Core.setMessageLog savedMsgs
        return .error ex.toMessageData)
  catch ex =>
    restoreState saved
    Core.setMessageLog savedMsgs
    return .error ex.toMessageData

/-- Format `e` with `pp.deepTerms := false`, a shallow `pp.deepTerms.threshold`, and a bounded
    `pp.maxSteps` budget under an unlimited heartbeat guard (`maxHeartbeats := 0`), collapsing
    whitespace and truncating to `maxChars` characters so deep terms (such as `State` update
    spines) or exhausted outer heartbeat budgets never fail with `<failed to pretty print term>`. -/
def ppExprTruncated (e : Expr) (maxChars : Nat := 160) (maxDepth : Nat := 12) :
    MetaM String := do
  let fmt? ←
    try
      MonadRuntimeException.tryCatchRuntimeEx
        (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) <|
         withCurrHeartbeats <|
         withOptions (fun opts =>
          let opts := Lean.pp.deepTerms.set opts false
          let opts := Lean.pp.deepTerms.threshold.set opts maxDepth
          Lean.pp.maxSteps.set opts 500) do
          let e ← instantiateMVars e
          let fmt ← PrettyPrinter.ppExpr e
          return some (fmt.pretty (width := 10000)))
        (fun _ => return none)
    catch _ =>
      Pure.pure none
  let raw := match fmt? with
    | some s => s
    | none =>
      match e.getAppFn.constName? with
      | some c => s!"({c} …)"
      | none => "<expr>"
  let mut chars : Array Char := #[]
  let mut prevSpace := false
  for c in raw.toList do
    if c.isWhitespace then
      if !prevSpace && !chars.isEmpty then
        chars := chars.push ' '
        prevSpace := true
    else
      chars := chars.push c
      prevSpace := false
  if chars.size > maxChars then
    return String.ofList (chars.extract 0 maxChars).toList ++ "..."
  else
    return String.ofList chars.toList

/-- True when `ex` is a Lean heartbeat/timeout exception (`O(1)` via `Exception.isMaxHeartbeat`). -/
def isHeartbeatException (ex : Exception) : IO Bool := do
  return ex.isMaxHeartbeat

/-- True when the current `CoreM` heartbeat counter has reached or exceeded `maxHeartbeats`. -/
def outerHeartbeatsExhausted : CoreM Bool := do
  let maxHb := (← readThe Core.Context).maxHeartbeats
  if maxHb == 0 then return false
  let curHb ← IO.getNumHeartbeats
  let initHb := (← readThe Core.Context).initHeartbeats
  return (curHb - initHb) ≥ maxHb

/-- Format a phase-annotated heartbeat timeout error with the truncated current goal and a
    targeted remedy (never suggesting `set_option maxHeartbeats`). -/
def throwHeartbeatPhaseError {α : Type} (tacticName : String) (phase : String)
    (remedy : String) (gOpt? : Option MVarId := none) : TacticM α := do
  let goalStr ←
    try
      MonadRuntimeException.tryCatchRuntimeEx
        (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) <|
         withCurrHeartbeats do
          let g? ← match gOpt? with
            | some g => Pure.pure (some g)
            | none => do
              let gs ← getUnsolvedGoals
              Pure.pure gs.head?
          match g? with
          | some g => g.withContext do ppExprTruncated (← instantiateMVars (← g.getType)) 180 10
          | none => Pure.pure "<no active goal>")
        (fun _ => Pure.pure "<goal unavailable>")
    catch _ => Pure.pure "<goal unavailable>"
  throwError "{tacticName}: heartbeat timeout during {phase}\n  subgoal: {goalStr}\nhint: {remedy}"

/-- Run `act`, catching any heartbeat/timeout exception and converting it into a phase-annotated
    error via `throwHeartbeatPhaseError`.

    Note:
    (a) When tactic-scoped `set_option maxHeartbeats N in` sets `N * 1000` below the enclosing
        `Core.Context.maxHeartbeats`, this installs a fresh `N * 1000` heartbeat budget via
        `withCurrHeartbeats` (whereas Lean's default tactic `set_option` only updates `Options`).
    (b) Heartbeat timeouts are converted into a catchable `throwError` (`Exception.error`), which
        outer tactic combinators (`first`, `try`, `<|>`) will catch. -/
def withWpHeartbeatDiag {α : Type} (tacticName : String) (phase : String)
    (remedy : String) (act : TacticM α) (gOpt? : Option MVarId := none) : TacticM α := do
  let optHb := Lean.maxHeartbeats.get (← getOptions)
  let optRaw := if optHb == 1 then 10 else optHb * 1000
  let curMax := (← readThe Core.Context).maxHeartbeats
  let runAct : TacticM α :=
    if optRaw > 0 && optRaw < curMax then
      withCurrHeartbeats <|
        withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := optRaw }) act
    else
      act
  let handleEx (ex : Exception) : TacticM α := do
    if (← isHeartbeatException ex) || (← outerHeartbeatsExhausted) then
      throwHeartbeatPhaseError tacticName phase remedy gOpt?
    else
      throw ex
  try
    MonadRuntimeException.tryCatchRuntimeEx runAct handleEx
  catch ex =>
    handleEx ex

/-- Like `tryTacticCatchRuntimeBool`, but also records in `hbRef` if a heartbeat timeout occurred
    (or if the outer heartbeat budget is now exhausted). By default (`rethrowNonHb := false`),
    non-heartbeat runtime exceptions (such as `maxRecDepth`) are swallowed after restoring state
    so tiered tactics like `wp_done` can fall through to subsequent tiers; pass
    `rethrowNonHb := true` at `tryTactic` call sites that should still propagate non-heartbeat
    runtime exceptions. -/
def tryTacticTrackHeartbeatBool (hbRef : IO.Ref (Option String)) (phase : String)
    (tac : TacticM Unit) (rethrowNonHb : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  let onFail (ex : Exception) : TacticM Bool := do
    let isHb ← Pure.pure (← isHeartbeatException ex) <||> outerHeartbeatsExhausted
    if isHb then
      if (← hbRef.get).isNone then
        hbRef.set (some phase)
    restoreState saved
    Core.setMessageLog savedMsgs
    if rethrowNonHb && !isHb && ex.isRuntime then
      throw ex
    return false
  try
    MonadRuntimeException.tryCatchRuntimeEx
      (do
        withoutRecover tac
        return true)
      onFail
  catch ex =>
    onFail ex

/-- Report that a stepping loop (`tag` = `wp_steps` / `wp_sym_steps`) stopped at a non-branch `pc`
    before `target_pc` because no step rule applied or fetch/decode failed (`detail` = the step
    failure, which names the instruction and failing rule).
    Throws under `proofLib.wpStrict`; otherwise emits an `info` diagnostic at the tactic position
    with the PC, target PC, failing step-rule detail, and suggested next action (unless `quiet`). -/
def reportStepStuck (tag : String) (pc : Expr) (detail : MessageData)
    (targetPc? : Option Expr := none) (quiet : Bool := false) : TacticM Unit := do
  if CondClassify.proofLib.wpStrict.get (← getOptions) then
    throwError m!"{tag}: stuck at pc {pc}: no step rule applies (set_option proofLib.wpStrict false to stop silently instead)\n{detail}"
  else if !quiet then
    (← getMainGoal).withContext do
      let es := match targetPc? with | some t => #[pc, t] | none => #[pc]
      logInfo <| MessageData.ofLazyM (es := es) do
        let targetPart := match targetPc? with
          | some targetPc => m!" (target {targetPc})"
          | none => m!""
        let nextHint :=
          m!"\nnext: prove any missing side condition (e.g. `have h : ... := by bv_arith`), focus/split the accessed memory cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), check `*Fns`/`*Code` `HasCode` hypotheses, or apply a custom step lemma before `{tag}`"
        return m!"{tag}: stopped at pc {pc}{targetPart}: no step rule applies\n{detail}{nextHint}"

/-- Log why a stepping loop (`tag` = `wp_steps` / `wp_sym_steps`) stopped before `targetPc`
    without inspecting the spatial context (built lazily via `MessageData.ofLazyM`). -/
def logWpStopBeforeTarget (tag : String) (pc targetPc : Expr)
    (reason : MessageData) (nextHint : MessageData) (quiet : Bool := false) : TacticM Unit := do
  if !quiet then
    (← getMainGoal).withContext do
      logInfo <| MessageData.ofLazyM (es := #[pc, targetPc]) do
        return m!"{tag}: stopped at pc {pc} (target {targetPc}): {reason}; next: {nextHint}"

/-- Extract `(cond, thenBranch, elseBranch)` from an `@ite α c inst t e` expression. -/
def iteApp? (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``ite 5 then
    some (e.getArg! 1, e.getArg! 3, e.getArg! 4)
  else
    none

/-- Throw an actionable error when a single-step tactic (`tacticName` = `"wp_step"` or
    `"wp_sym_step"`) encounters an unresolved conditional branch `if c then t else e` at `pcExpr`. -/
def throwUnresolvedBranchStepError {α : Type} (tacticName : String) (pcExpr : Expr) : TacticM α := do
  let g ← getMainGoal
  g.withContext do
    if let some (cond, thenPC, elsePC) := iteApp? pcExpr then
      let condEqTrueMsg : MessageData :=
        if cond.isAppOfArity ``Eq 3 && (cond.getArg! 2).isConstOf ``true then
          m!"{cond}"
        else
          m!"{cond} = true"
      throwError "{tacticName}: current PC is an unresolved conditional branch:\n  condition: {cond}\n  then PC:   {thenPC}\n  else PC:   {elsePC}\nhint: split with `wp_if hcond` (if both branches are reachable) or prove `have hcond : {condEqTrueMsg} := by bv_omega` (or `= false`) before stepping (or `wp_simp_pre [hcond]`)"
    else
      throwError "{tacticName}: unresolved conditional branch at PC `{pcExpr}`; use `wp_if`"

/-- Throw an actionable error when `tacticName` (`"wp_step"` or `"wp_sym_step"`) cannot fetch or
    decode the instruction at `pcExpr`. -/
def throwCouldNotFetchDecodeError {α : Type} (tacticName : String) (pcExpr : Expr) : TacticM α := do
  let g ← getMainGoal
  g.withContext do
    throwError "{tacticName}: could not fetch/decode instruction at PC `{pcExpr}`\nhint: check (1) the `*Fns.lean` / `*Code.lean` decode module is imported or a `hasWords` / `hasCode` / `code_fetches` hypothesis is in context, (2) the PC offset is normalized (e.g. `entry + <off>#64`; try `wp_simp_pre` or `examples_generalize_entry`), or (3) execution did not step past function exit or into an un-inlined `BL` callee"

/-- When `true` (default), `wp_step` and `wp_sym_step` attempt the full normalized branch-condition
    decision procedure (`resolveIteCondFast? (forStepPC := false)` and bounded `bv_omega`) before
    throwing an unresolved-conditional-branch error on a single-step call. -/
register_option proofLib.wpDecideBranchOnStep : Bool := {
  defValue := true
  descr := "Decide conditional branch PCs from local context in single-step wp_step / wp_sym_step before failing."
}

/-- When `true` (default), `wp_step` automatically splits wider `↦₆₄` / `↦₃₂` / `↦₁₆` cells or
    `memRegion` / `stackFrameAt` containers at the accessed subword/slice offset when a load/store
    step would otherwise fail with 'no step rule succeeded'. -/
register_option proofLib.wpAutoSubwordFocus : Bool := {
  defValue := true
  descr := "Automatically focus subword or region cells on load/store step fallback in wp_step."
}

/-- When `true` (default), `wp_focus_close` tries a bounded default closer chain (`tryCloseFetchFromHasCode`,
    `arm64_norm`/`wp_norm` simp, `bv_lin`, bounded `bv_omega`, `decide`) when the inner tactic
    leaves an mvar-free side goal unsolved before throwing. -/
register_option proofLib.wpFocusCloseFallback : Bool := {
  defValue := true
  descr := "Try a bounded fallback closer chain in wp_focus_close when the inner tactic leaves a side goal unsolved."
}

private def tryFocusCloseFallback? (g0 : MVarId) : TacticM Bool := do
  let gTy ← g0.withContext do instantiateMVars (← g0.getType)
  if gTy.hasMVar then return false
  let isFetch := (gTy.find? (·.isConstOf ``Program.fetch)).isSome
  let isArithEq : Bool := match gTy.eq? with
    | some (eqTy, lhs, rhs) =>
      (lhs.hasFVar || rhs.hasFVar) &&
      (eqTy.isAppOfArity ``BitVec 1 || eqTy.isConstOf ``Nat || eqTy.isConstOf ``Int)
    | none => false
  let isBound : Bool :=
    gTy.hasFVar && (gTy.isAppOfArity ``LE.le 4 || gTy.isAppOfArity ``LT.lt 4)
  if !isFetch && !isArithEq && !isBound then
    return false
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  setGoals [g0]
  let ok ← tryTacticCatchRuntimeBool <| withHeartbeatCap 20000 do
    if isFetch then
      if ← tryCloseFetchFromHasCode then return
      let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
        (conv => lhs; simp (config := { decide := true }) only [arm64_norm, wp_norm])))
      if ← tryCloseFetchFromHasCode then return
    let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
      first
        | done
        | with_reducible rfl
        | with_reducible assumption
        | (decide; done)
        | (bv_lin; done)
        | (simp (config := { decide := true }) only [arm64_norm, wp_norm]; done)))
    if let [g'] ← getGoals then
      if ← proveOmegaBounded? g' [← `(tactic| (bv_omega; done)), ← `(tactic| (omega; done))]
          [.strict, .transitive] 15000 then
        setGoals []
    if !(← getGoals).isEmpty then throwError "unsolved"
  if ok && (← getGoals).isEmpty then
    return true
  restoreState saved
  Core.setMessageLog savedMsgs
  return false

/-- Focus on the first goal, run `tac`, require it to close the goal (`done`), and restore remaining goals.
    Unlike `·` (`cdot`), this does NOT perform IDE `sorryAx` recovery on failure, so `tryTactic` catches failures cleanly. -/
elab "wp_focus_close " tac:tacticSeq : tactic => do
  let gs ← getGoals
  let g :: rest := gs | throwError "wp_focus_close: no goals"
  setGoals [g]
  let gTy0 ← g.withContext do instantiateMVars (← g.getType)
  let useFb := !gTy0.hasMVar && proofLib.wpFocusCloseFallback.get (← getOptions)
  if useFb then
    let savedBeforeTac ← saveState
    let savedMsgsBeforeTac ← Core.getMessageLog
    let tacEx? : Option Exception ←
      try
        MonadRuntimeException.tryCatchRuntimeEx
          (do evalTactic tac; return none)
          (fun ex => return some ex)
      catch ex =>
        Pure.pure (some ex)
    let remAfterTac ← getGoals
    if tacEx?.isNone && remAfterTac.isEmpty then
      setGoals (← rest.filterM fun m => not <$> m.isAssigned)
      return
    let afterTacState ← saveState
    let afterTacMsgs ← Core.getMessageLog
    restoreState savedBeforeTac
    Core.setMessageLog savedMsgsBeforeTac
    if ← tryFocusCloseFallback? g then
      setGoals (← rest.filterM fun m => not <$> m.isAssigned)
      return
    restoreState afterTacState
    Core.setMessageLog afterTacMsgs
    if let some ex := tacEx? then
      throw ex
  else
    evalTactic tac
  let rem ← getGoals
  if !rem.isEmpty then
    let g0 := rem.head!
    g0.withContext do
      let gTy ← instantiateMVars (← g0.getType)
      let hint : MessageData :=
        if (gTy.find? (·.isConstOf ``Program.fetch)).isSome then
          m!"\nhint: instruction fetch side goal failed; ensure the function's `*Fns.lean` / `*Code.lean` decode theorem is imported/in scope and the PC offset is normalized"
        else if let some (_, lhs, rhs) := gTy.eq? then
          m!"\nhint: address/value equality side goal was not closed by `{tac}`; simplify or prove `{lhs} = {rhs}` before stepping"
        else
          m!""
      throwError "wp_focus_close (after running `{tac}`): unsolved side goal:{indentExpr gTy}{hint}"
  setGoals (← rest.filterM fun m => not <$> m.isAssigned)

/-- Decompose an address `base + c_1 - c_2 ...` with literal 64-bit offsets `c_i` into
    `(base, offset mod 2^64)`; a literal address `c` decomposes as `(0#64, c)`. Used to match an
    access address such as `(sp - 48#64) + 12#64` with an atom address such as `sp - 36#64`. -/
partial def sepAddrBaseOff (e : Expr) : MetaM (Expr × Nat) := do
  let e := e.consumeMData
  let isAdd := e.isAppOfArity ``HAdd.hAdd 6
  if isAdd || e.isAppOfArity ``HSub.hSub 6 then
    if let some (w, c) ← evalBitVecLit? (e.getArg! 5) then
      if w == 64 then
        let (b, o) ← sepAddrBaseOff (e.getArg! 4)
        return (b, if isAdd then (o + c) % 2 ^ 64 else (o + 2 ^ 64 - c) % 2 ^ 64)
    if isAdd then
      if let some (w, c) ← evalBitVecLit? (e.getArg! 4) then
        if w == 64 then
          let (b, o) ← sepAddrBaseOff (e.getArg! 5)
          return (b, (o + c) % 2 ^ 64)
  if let some (w, c) ← evalBitVecLit? e then
    if w == 64 then return (toExpr (0#64), c)
  return (e, 0)

/-- Proof-free, `whnf`-free variant of `sepAddrBaseOff`: decomposes `base + c_1 - c_2 ...` into
    `(base, offset mod 2^64)` only when every `c_i` is syntactically a 64-bit numeral
    `BitVec.ofNat 64 n` (`evalBitVecLitPure?`). Non-numeral ground offsets (e.g.
    `BitVec.ofNat 64 (f a - f b)`) stay in the base, keeping cost linear in the size of `e`. -/
partial def sepAddrBaseOffPure (e : Expr) : Expr × Nat :=
  let e := e.consumeMData
  let isAdd := e.isAppOfArity ``HAdd.hAdd 6
  let fallback : Expr × Nat :=
    match evalBitVecLitPure? e with
    | some (64, c) => (toExpr (0#64), c)
    | _ => (e, 0)
  if isAdd || e.isAppOfArity ``HSub.hSub 6 then
    match evalBitVecLitPure? (e.getArg! 5) with
    | some (64, c) =>
      let (b, o) := sepAddrBaseOffPure (e.getArg! 4)
      (b, if isAdd then (o + c) % 2 ^ 64 else (o + 2 ^ 64 - c) % 2 ^ 64)
    | _ =>
      if isAdd then
        match evalBitVecLitPure? (e.getArg! 4) with
        | some (64, c) =>
          let (b, o) := sepAddrBaseOffPure (e.getArg! 5)
          (b, (o + c) % 2 ^ 64)
        | _ => fallback
      else fallback
  else fallback

/-- Cache of `s.sp ↦ rhs` substitutions found in the local context (`s.sp ↦ s.sp` records that no
    usable hypothesis exists), shared across the atoms scanned by one access. -/
abbrev SpSubstCache := Std.HashMap Expr Expr

/-- The right-hand side `rhs` of a local hypothesis `s.sp = rhs` (with `rhs` not mentioning `s`),
    the same substitution `SepSolver.normAddrMeta` performs. -/
def findSpSubst? (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``State.sp 1 && (e.getArg! 0).isFVar do return none
  let s := (e.getArg! 0).fvarId!
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let ty := SepSolver.stripMData (← instantiateMVars decl.type)
    let some (_, lhs, rhs) := ty.eq? | continue
    if lhs == e && !rhs.containsFVar s then return some rhs
  return none

/-- Proof-free `(base, offset)` decomposition (`sepAddrBaseOff`) that also substitutes a local
    `s.sp = rhs` equation for an `s.sp` base, so atoms written against the entry stack pointer and
    accesses through a renamed `sp` decompose to the same base. Used only as a cheap pre-filter: a
    candidate found this way is confirmed by `proveSepAddrEqMeta?`. -/
partial def sepAddrBaseOffFast (e : Expr) (cache : SpSubstCache) (fuel : Nat := 4) :
    MetaM ((Expr × Nat) × SpSubstCache) := do
  let (b, o) ← sepAddrBaseOff e
  if fuel == 0 || !b.isAppOfArity ``State.sp 1 then return ((b, o), cache)
  let (rhs?, cache) ← match cache[b]? with
    | some r => Pure.pure ((if r == b then none else some r), cache)
    | none => do
      let r? ← findSpSubst? b
      Pure.pure (r?, cache.insert b (r?.getD b))
  let some rhs := rhs? | return ((b, o), cache)
  let ((b', o'), cache) ← sepAddrBaseOffFast rhs cache (fuel - 1)
  return ((b', (o + o') % 2 ^ 64), cache)

/-- Prove the address equation `a' = a` without tactics: by `rfl` when the two are reducibly
    defeq, by `SepSolver.normAddrMeta` offset folding, or by the certified linear normal form
    (`ProofLib.BV.Lin.proveEq?`). -/
def proveSepAddrEqMeta? (a' a : Expr) : MetaM (Option Expr) := do
  let eqTy ← mkEq a' a
  if a' == a then return some (← mkExpectedTypeHint (← mkEqRefl a) eqTy)
  if ← withReducibleAndInstances (isDefEq a' a) then
    return some (← mkExpectedTypeHint (← mkEqRefl a) eqTy)
  let (a'Norm, ha'Prf?) ← SepSolver.normAddrMeta a'
  let (aNorm, haPrf?) ← SepSolver.normAddrMeta a
  if a'Norm == aNorm || (← withReducibleAndInstances (isDefEq a'Norm aNorm)) then
    let ha'Prf ← match ha'Prf? with | some p => Pure.pure p | none => mkEqRefl a'
    let haPrf ← match haPrf? with | some p => Pure.pure p | none => mkEqRefl a
    let prf ← mkEqTrans ha'Prf (← mkEqSymm haPrf)
    return some (← mkExpectedTypeHint prf eqTy)
  ProofLib.BV.Lin.proveEq? a' a

/-- Hypotheses of `g` to clear before a `bv_omega` address-equation attempt: machine-state /
    memory / separation-logic hypotheses and non-numeric `let`-bindings (as in `wp_bv_omega`),
    plus either (`strict`) every `Prop` hypothesis mentioning a local outside the goal, or
    (otherwise) the equations that only define an unused atom (`omegaDefinitionalHyps`). Each
    `x = e` register or address equation becomes several `% 2^64` atoms under `bv_omega`, and a
    handful of unrelated ones can make `omega` run for minutes without checking heartbeats. -/
def sepAddrEqPruneGoal (g : MVarId) (strict : Bool) : MetaM MVarId := g.withContext do
  let goalTy ← instantiateMVars (← g.getType)
  let goalFVars := (collectFVars {} goalTy).fvarSet
  let mut toClear : Array FVarId := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    let heavyVal := match decl.value? with
      | some v => isHeavyHypType v
      | none => false
    if decl.isLet && ((!ty.isAppOf ``BitVec && !ty.isConstOf ``Nat) || heavyVal) then
      toClear := toClear.push decl.fvarId
    else if ← Meta.isProp ty then
      if isHeavyHypType ty || (strict && ty.hasAnyFVar (!goalFVars.contains ·)) then
        toClear := toClear.push decl.fvarId
  let g' ← g.tryClearMany toClear
  if strict then return g'
  g'.tryClearMany (← omegaDefinitionalHyps g')

/-- `bv_omega` proof of the address equation `eqTy` in a pruned local context, each attempt capped
    at `cap` heartbeats (thousands) and catching runtime exceptions: first `sepAddrEqPruneGoal`
    (strict), then the transitive relevance tier `omegaPruneGoal`, and with `keepHeavy` finally
    `omegaPruneGoal .heavy` (machine-state facts connected to the goal). The two transitive tiers
    are skipped when they keep more than `omegaMaxNatSubs` `Nat` subtractions, and every tier is
    filtered by `omegaWrapFilter?` first. -/
def proveSepAddrEqPruned? (eqTy : Expr) (cap : Nat := 30000) (keepHeavy : Bool := false) :
    TacticM (Option Expr) := do
  let tiers : List (Bool × (MVarId → MetaM MVarId)) :=
    [(false, (sepAddrEqPruneGoal · true)), (true, (omegaPruneGoal · .transitive))] ++
      (if keepHeavy then [(true, (omegaPruneGoal · .heavy))] else [])
  let tac ← `(tactic| bv_omega)
  let mut prevHyps : Option (Array FVarId) := none
  for (gated, prune) in tiers do
    let g ← mkFreshExprMVar eqTy
    let some g' ← omegaWrapFilter? (← prune g.mvarId!) | continue
    let hyps ← g'.withContext do return (← getLCtx).getFVarIds
    if prevHyps == some hyps then continue
    prevHyps := some hyps
    if gated && (← omegaGoalNatSubs g') > omegaMaxNatSubs then continue
    if ← runTacCapped g' tac cap then return some (← instantiateMVars g)
  return none

/-- Prove the address equation `a' = a` (atom address = access address) with
    `proveSepAddrEqMeta?`, then `bv_omega` in a pruned local context (`proveSepAddrEqPruned?`;
    with `allowFull`, also the tier that keeps machine-state facts connected to the goal). The
    whole local context is never handed to `bv_omega`. -/
def proveSepAddrEq (a' a : Expr) (allowFull : Bool := false) : TacticM Expr := do
  if let some prf ← proveSepAddrEqMeta? a' a then return prf
  let eqTy ← mkEq a' a
  if let some prf ← proveSepAddrEqPruned? eqTy (keepHeavy := allowFull) then return prf
  throwError "wp_sep_access: cannot prove address equation{indentExpr eqTy}"

/-- Fast path of `findPointsToAtom`: syntactic address equality, then a proof-free
    `(base, offset)` pre-filter (`sepAddrBaseOffFast`, at most one hypothesis scan) that confirms
    only the matching candidate with `proveSepAddrEqMeta?`. No per-atom `isDefEq` or
    `normAddrMeta`. -/
def findPointsToAtomFast (pt : Name) (as : Array Expr) (a : Expr) (arity : Nat := 2) :
    MetaM (Option (Nat × Option Expr)) := do
  let isPt (e : Expr) : Bool := e.isAppOfArity pt arity
  for hx : j in [:as.size] do
    if isPt as[j] && as[j].getArg! 0 == a then return some (j, none)
  let mut cache : SpSubstCache := {}
  let ((b, o), c) ← sepAddrBaseOffFast a cache
  cache := c
  for hx : j in [:as.size] do
    if isPt as[j] then
      let aj := as[j].getArg! 0
      let ((b', o'), c) ← sepAddrBaseOffFast aj cache
      cache := c
      if o == o' && b' == b then
        if let some prf ← proveSepAddrEqMeta? aj a then return some (j, some prf)
  return none

/-- Slow path of `findPointsToAtom`: reducible unification, normalized-address comparison, and
    the certified linear normal form, each tried against every atom of constructor `pt`. -/
def findPointsToAtomSlow (pt : Name) (as : Array Expr) (a : Expr) (arity : Nat := 2) :
    MetaM (Option (Nat × Option Expr)) := do
  let isPt (e : Expr) : Bool := e.isAppOfArity pt arity
  for hx : j in [:as.size] do
    if isPt as[j] then
      if ← withReducibleAndInstances (isDefEq (as[j].getArg! 0) a) then
        let eqTy ← mkEq (as[j].getArg! 0) a
        let prf ← mkExpectedTypeHint (← mkEqRefl a) eqTy
        return some (j, some prf)
  let (aNorm, haPrf?) ← SepSolver.normAddrMeta a
  let (b, o) ← sepAddrBaseOff aNorm
  for hx : j in [:as.size] do
    if isPt as[j] then
      let aj := as[j].getArg! 0
      let (ajNorm, hajPrf?) ← SepSolver.normAddrMeta aj
      if ajNorm == aNorm || (← withReducibleAndInstances (isDefEq ajNorm aNorm)) then
        let hajPrf ← match hajPrf? with | some p => Pure.pure p | none => mkEqRefl aj
        let haPrf ← match haPrf? with | some p => Pure.pure p | none => mkEqRefl a
        let eqTy ← mkEq aj a
        let prf ← mkExpectedTypeHint (← mkEqTrans hajPrf (← mkEqSymm haPrf)) eqTy
        return some (j, some prf)
      let (b', o') ← sepAddrBaseOff ajNorm
      if o == o' && (b' == b || (← withReducibleAndInstances (isDefEq b' b))) then
        return some (j, none)
  -- general path, certified linear normal form (`aj - a` normalizes to `0`); the proof is
  -- returned so `proveSepAddrEq` need not redo it
  for hx : j in [:as.size] do
    if isPt as[j] then
      if let some prf ← ProofLib.BV.Lin.proveEq? (as[j].getArg! 0) a then return some (j, some prf)
  return none

/-- Find an atom of constructor `pt` (`pointsTo8`, `pointsTo16`, `pointsTo32`, `pointsTo64`, or a
    read-only / lazy-free variant) in `as` owning address `a`, returning
    `(idx, optional_addr_eq_proof)` (`findPointsToAtomFast`, then `findPointsToAtomSlow`). -/
def findPointsToAtom (pt : Name) (as : Array Expr) (a : Expr) (arity : Nat := 2) :
    MetaM (Option (Nat × Option Expr)) := do
  if let some r ← findPointsToAtomFast pt as a arity then return some r
  findPointsToAtomSlow pt as a arity

/-! ## Spine Lifting of Leaf Witnesses -/

/-- `atom = atom ∗ emp`, turning an `of_eq`-style constructor (`h : P = atom ∗ F -> ...`) into a
    leaf witness for `atom` alone. -/
def sepLeafEq (atom : Expr) : MetaM Expr :=
  mkEqSymm (mkApp (mkConst ``ProofLib.sepConj_emp) atom)

/-- Path from the `i`-th atom (in `SepSolver.atoms` order) of a separating-conjunction tree up to
    the root, leaf first: for each `∗` level, whether the atom lies in the left operand and the
    sibling operand. -/
partial def sepSpinePath (e : Expr) (i : Nat) : Option (Array (Bool × Expr)) :=
  match go e 0 with
  | .inl path => some path
  | .inr _ => none
where
  go (e : Expr) (k : Nat) : Array (Bool × Expr) ⊕ Nat :=
    let e' := e.consumeMData.headBeta
    if e'.isAppOfArity ``SepProp.sepConj 2 then
      let l := e'.getArg! 0
      let r := e'.getArg! 1
      match go l k with
      | .inl path => .inl (path.push (true, r))
      | .inr nl =>
        match go r (k + nl) with
        | .inl path => .inl (path.push (false, l))
        | .inr nr => .inr (nl + nr)
    else if (SepSolver.stripMData e').headBeta.isConstOf ``SepProp.emp then .inr 0
    else if k == i then .inl #[]
    else .inr 1

/-- Lift `leaf : fam a atom_i v` (`fam` in `{SepLoad8, SepLoad16, SepLoad32, SepLoad64}`) to
    `fam a P v` along the `∗` spine of `P`. -/
def sepLiftLoad (fam : Name) (a v P : Expr) (i : Nat) (leaf : Expr) : MetaM Expr := do
  let some path := sepSpinePath P i
    | throwError "wp_sep_access: no atom {i} in{indentExpr P}"
  let mut prf := leaf
  let mut cur := (← instantiateMVars (← inferType leaf)).getArg! 1
  for (isLeft, sib) in path do
    if isLeft then
      prf := mkApp5 (mkConst (fam ++ `left)) a v cur sib prf
      cur := SepSolver.mkSep cur sib
    else
      prf := mkApp5 (mkConst (fam ++ `right)) a v sib cur prf
      cur := SepSolver.mkSep sib cur
  return prf

/-- Lift `leaf : fam a v' atom_i atom_i'` (`fam` in `{SepStore8, ..., SepStore64}`) to
    `fam a v' P P'` along the `∗` spine of `P`, returning `(P', proof)`. -/
def sepLiftStore (fam : Name) (a v' P : Expr) (i : Nat) (atom atom' leaf : Expr) :
    MetaM (Expr × Expr) := do
  let some path := sepSpinePath P i
    | throwError "wp_sep_access: no atom {i} in{indentExpr P}"
  let mut prf := leaf
  let mut cur := atom
  let mut cur' := atom'
  for (isLeft, sib) in path do
    if isLeft then
      prf := mkAppN (mkConst (fam ++ `left)) #[a, v', cur, cur', sib, prf]
      cur := SepSolver.mkSep cur sib
      cur' := SepSolver.mkSep cur' sib
    else
      prf := mkAppN (mkConst (fam ++ `right)) #[a, v', sib, cur, cur', prf]
      cur := SepSolver.mkSep sib cur
      cur' := SepSolver.mkSep sib cur'
  return (cur', prf)

/-! ## Byte-List Accesses at Symbolic Offsets -/

/-- Flatten a sum of 64-bit summands into `(terms, c mod 2^64)`, folding literal summands into `c`. -/
partial def sepAddrTerms (e : Expr) : MetaM (Array Expr × Nat) := do
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (t1, o1) ← sepAddrTerms (e.getArg! 4)
    let (t2, o2) ← sepAddrTerms (e.getArg! 5)
    return (t1 ++ t2, (o1 + o2) % 2 ^ 64)
  if let some (64, c) ← evalBitVecLit? e then return (#[], c)
  return (#[e], 0)

/-- Flatten a 64-bit address `root + t_1 + ... + c` into `(root, #[t_1, ...], c mod 2^64)`:
    literal summands and differences are folded into `c`, other right summands are collected as
    terms, and `x - t` with a non-literal `t` is kept whole as the root. -/
partial def sepAddrSpine (e : Expr) : MetaM (Expr × Array Expr × Nat) := do
  let e := e.consumeMData
  let isAdd := e.isAppOfArity ``HAdd.hAdd 6
  if isAdd || e.isAppOfArity ``HSub.hSub 6 then
    if let some (64, c) ← evalBitVecLit? (e.getArg! 5) then
      let (r, ts, o) ← sepAddrSpine (e.getArg! 4)
      return (r, ts, if isAdd then (o + c) % 2 ^ 64 else (o + 2 ^ 64 - c) % 2 ^ 64)
    if isAdd then
      let (r, ts, o) ← sepAddrSpine (e.getArg! 4)
      let (ts', o') ← sepAddrTerms (e.getArg! 5)
      return (r, ts ++ ts', (o + o') % 2 ^ 64)
  if let some (64, c) ← evalBitVecLit? e then return (toExpr (0#64), #[], c)
  return (e, #[], 0)

/-- The `Nat` value of a 64-bit summand: `k` for `BitVec.ofNat 64 k` / `(k : BitVec 64)`,
    otherwise `t.toNat`. -/
def sepBvTermNat (t : Expr) : MetaM Expr := do
  let t := t.consumeMData
  if t.isAppOfArity ``BitVec.ofNat 2 then return t.getArg! 1
  if t.isAppOfArity ``Nat.cast 3 then return t.getArg! 2
  mkAppM ``BitVec.toNat #[t]

/-- Symbolic byte offset of address `a` inside a byte-list atom based at `base` (see the section
    comment): `none` unless both flatten to the same root and every summand of `base` occurs in
    `a`. A negative constant difference is allowed only when some summand remains (`s - c`).
    Returns `(off, rest, d)`: the `Nat` offset, the summands `tᵢ` of `a` missing from `base` (in
    the order they are summed in `off`) and the signed constant difference `d`. -/
def sepBytesSymOffset? (base a : Expr) : MetaM (Option (Expr × Array Expr × Int)) := do
  let (rA, tsA, cA) ← sepAddrSpine a
  let (rB, tsB, cB) ← sepAddrSpine base
  unless rA == rB || (← withReducibleAndInstances (isDefEq rA rB)) do return none
  let mut rest := tsA.toList
  for t in tsB do
    let some j := rest.findIdx? (· == t) | return none
    rest := rest.eraseIdx j
  let d0 : Int := Int.ofNat ((cA + 2 ^ 64 - cB) % 2 ^ 64)
  let d : Int := if d0 ≥ 2 ^ 63 then d0 - 2 ^ 64 else d0
  let mut sum? : Option Expr := none
  for t in rest do
    let n ← sepBvTermNat t
    sum? := some (match sum? with | none => n | some s => mkNatAdd s n)
  let restA := rest.toArray
  match sum? with
  | none => return if d ≥ 0 then some (mkNatLit d.toNat, restA, d) else none
  | some s =>
    if d == 0 then return some (s, restA, d)
    else if d > 0 then return some (mkNatAdd s (mkNatLit d.toNat), restA, d)
    else return some (mkNatSub s (mkNatLit (-d).toNat), restA, d)

/-- `base + BitVec.ofNat 64 off`. -/
def sepBytesTarget (base off : Expr) : MetaM Expr :=
  mkAppM ``HAdd.hAdd #[base, mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) off]

/-- Close the `Nat` goal `goal` by `omega` on pruned copies of the context
    (`proveOmegaBoundedTerm?`: goal only, then the strict and transitive relevance tiers; never
    the machine-state facts or the whole context), each attempt capped at `cap` heartbeats. -/
def proveNatOmega? (goal : Expr) (cap : Nat := 20000) : TacticM (Option Expr) := do
  proveOmegaBoundedTerm? goal [← `(tactic| omega)] [.goalOnly, .strict, .transitive] cap

/-- Close the `Nat` goal `goal` by `omega`, or by `byte_region_len` (length lemmas for
    `List.replicate`, `ByteSlice.write` / `writeLE` / `unpackLE` and literal lists), capped. -/
def proveLenGoal? (goal : Expr) : TacticM (Option Expr) := do
  if let some p ← proveNatOmega? goal then return some p
  let m ← mkFreshExprMVar goal
  if ← runTacCapped m.mvarId! (← `(tactic| byte_region_len)) 20000 then
    return some (← instantiateMVars m)
  return none

/-- `(len, bs.length = len)`: peels `ByteSlice.write8/16/32/64` (each in-bounds side goal closed
    by `proveLenGoal?` against the inner length), `ByteSlice.copySet` and `ByteSlice.fillSet` off
    `bs`, ending at `L.length` for the innermost list `L`. `none` if a write is not provably in
    bounds. Linear in the depth of `bs`: one `omega` call per write. -/
partial def byteListLen? (bs : Expr) : TacticM (Option (Expr × Expr)) := do
  let bs := bs.consumeMData
  let writes : List (Name × Name × Nat) :=
    [(``ByteSlice.write8, ``sepBytesLen_write8, 1), (``ByteSlice.write16, ``sepBytesLen_write16, 2),
     (``ByteSlice.write32, ``sepBytesLen_write32, 4), (``ByteSlice.write64, ``sepBytesLen_write64, 8)]
  for (fn, thm, w) in writes do
    if bs.isAppOfArity fn 3 then
      let some (len, hlen) ← byteListLen? (bs.getArg! 0) | return none
      let some hb ← proveLenGoal? (← mkAppM ``LE.le #[mkNatAdd (bs.getArg! 1) (mkNatLit w), len])
        | return none
      return some (len, ← mkAppM thm #[bs.getArg! 2, hlen, hb])
  if bs.isAppOfArity ``ByteSlice.copySet 3 then
    let some (len, hlen) ← byteListLen? (bs.getArg! 0) | return none
    return some (len, ← mkAppM ``sepBytesLen_copySet #[bs.getArg! 1, bs.getArg! 2, hlen])
  if bs.isAppOfArity ``ByteSlice.fillSet 3 then
    let some (len, hlen) ← byteListLen? (bs.getArg! 0) | return none
    return some (len, ← mkAppM ``sepBytesLen_fillSet #[bs.getArg! 1, bs.getArg! 2, hlen])
  let len ← mkAppM ``List.length #[bs]
  return some (len, ← mkEqRefl len)

/-- Prove a byte-region bound `k ≤ bs.length` (`k = off + w`): normalize `bs.length` with
    `byteListLen?`, then close `k ≤ len` with `proveLenGoal?`. -/
def proveByteBound? (k bs : Expr) : TacticM (Option Expr) := do
  let some (len, hlen) ← byteListLen? bs | return none
  let some h ← proveLenGoal? (← mkAppM ``LE.le #[k, len]) | return none
  return some (← mkAppM ``sepBytesBound_of_len #[hlen, h])

/-- `(k, BitVec.ofNat 64 k = t)` for a 64-bit summand `t` (`k` as in `sepBvTermNat`). -/
def sepBvTermProof? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let k ← sepBvTermNat t
  let lhs := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) k
  if (t.consumeMData.isAppOfArity ``BitVec.ofNat 2 || t.consumeMData.isAppOfArity ``Nat.cast 3) then
    unless ← withReducibleAndInstances (isDefEq lhs t) do return none
    return some (k, ← mkExpectedTypeHint (← mkEqRefl t) (← mkEq lhs t))
  return some (k, ← mkAppM ``sepBytesOff_toNat #[t])

/-- Structural proof of `base + BitVec.ofNat 64 off = a` for a symbolic offset `(off, ts, d)` from
    `sepBytesSymOffset?`: rewrites `BitVec.ofNat 64 off` into `t_1 + ... + t_n` plus/minus `d`
    (`sepBytesOff_*`; for `d < 0` the side goal `-d <= k_1 + ... + k_n` is a plain `Nat` `omega`
    goal) and closes the resulting linear `BitVec` equation with `ProofLib.BV.Lin.proveEq?`. -/
def proveSepSymAddrEq? (base a off : Expr) (ts : Array Expr) (d : Int) :
    TacticM (Option Expr) := do
  if ts.isEmpty then return none
  let some (s0, h0) ← sepBvTermProof? ts[0]! | return none
  let mut s := s0
  let mut hs := h0
  for t in ts.extract 1 ts.size do
    let some (k, hk) ← sepBvTermProof? t | return none
    hs ← mkAppM ``sepBytesOff_termAdd #[hs, hk]
    s := mkNatAdd s k
  let hOff ←
    if d == 0 then Pure.pure hs
    else if d > 0 then mkAppM ``sepBytesOff_add #[mkNatLit d.toNat, hs]
    else do
      let dN := mkNatLit (-d).toNat
      let some hd ← proveNatOmega? (← mkAppM ``LE.le #[dN, s]) | return none
      mkAppM ``sepBytesOff_sub #[hs, hd]
  let some (_, _, t) := (← instantiateMVars (← inferType hOff)).eq? | return none
  let some ha ← ProofLib.BV.Lin.proveEq? (← mkAppM ``HAdd.hAdd #[base, t]) a | return none
  let prf ← mkAppM ``sepBytesAddr_of_off #[hOff, ha]
  let eqTy ← mkEq (← sepBytesTarget base off) a
  unless ← withReducibleAndInstances (isDefEq (← inferType prf) eqTy) do return none
  return some (← mkExpectedTypeHint prf eqTy)

/-- Proofs of `off + w ≤ bs.length` (`decide` for a ground `bs` and literal `off`, otherwise
    `proveByteBound?`) and `base + BitVec.ofNat 64 off = a` (`proveSepSymAddrEq?` for a symbolic
    offset `sym? = some (ts, d)`, then `proveSepAddrEq` without the whole-context fallback). -/
def sepBytesBoundAndAddr? (w : Nat) (base bs a off : Expr)
    (sym? : Option (Array Expr × Int) := none) : TacticM (Option (Expr × Expr)) := do
  let lenE ← mkAppM ``List.length #[bs]
  let leGoal ← mkAppM ``LE.le #[mkNatAdd off (mkNatLit w), lenE]
  let hLen? ← if !bs.hasFVar && !bs.hasMVar then do
      let some offN := off.nat? | Pure.pure none
      let lenWhnf ← withTransparency .default (whnf lenE)
      let lenVal? := lenWhnf.rawNatLit? <|>
        (if lenWhnf.isAppOfArity ``OfNat.ofNat 3 then (lenWhnf.getArg! 1).rawNatLit? else none)
      match lenVal? with
      | some lenVal => if offN + w ≤ lenVal then observing? (mkDecideProof leGoal) else Pure.pure none
      | none => Pure.pure none
    else proveByteBound? (mkNatAdd off (mkNatLit w)) bs
  let some hLen := hLen? | return none
  let symPrf? ← match sym? with
    | some (ts, d) => proveSepSymAddrEq? base a off ts d
    | none => Pure.pure none
  let ha? ← match symPrf? with
    | some p => Pure.pure (some p)
    | none => do
      let target ← sepBytesTarget base off
      tryTacticCatchRuntime <| withHeartbeatCap 50000 (proveSepAddrEq target a (allowFull := false))
  let some ha := ha? | return none
  return some (hLen, ha)

/-- Byte offset (literal when `a` and `base` agree up to literal summands, see
    `sepAddrBaseOffFast`; otherwise `sepBytesSymOffset?`) of access `a` inside the atom
    `base ↦ₛ bs`, with the proofs of `sepBytesBoundAndAddr?`. `(bAF, oAF)` is the decomposition
    of `a`. -/
def sepBytesOffset? (w : Nat) (base bs a bAF : Expr) (oAF : Nat) (cache : SpSubstCache) :
    TacticM (Option (Expr × Expr × Expr) × SpSubstCache) := do
  let ((bBF, oBF), cache) ← sepAddrBaseOffFast base cache
  let off? : Option (Expr × Option (Array Expr × Int)) ← if bAF == bBF then
      let off := (oAF + 2 ^ 64 - oBF) % 2 ^ 64
      Pure.pure (if off < 0x100000 then some (mkNatLit off, none) else none)
    else if !bs.hasFVar && !bs.hasMVar then Pure.pure none
    else Pure.pure ((← sepBytesSymOffset? base a).map fun (o, ts, d) => (o, some (ts, d)))
  let some (off, sym?) := off? | return (none, cache)
  let some (hLen, ha) ← sepBytesBoundAndAddr? w base bs a off sym? | return (none, cache)
  return (some (off, hLen, ha), cache)

/-- Indices of the byte-list atoms (`↦ₛ`, and `↦ᵣ` unless `rwOnly`) of `as`, those whose base
    flattens (`sepAddrSpine`) to the same root as the access address `a` first, so an access
    is matched against unrelated regions only when no related one owns it. -/
def sepBytesCandidates (as : Array Expr) (a : Expr) (rwOnly : Bool) : MetaM (Array Nat) := do
  let (rA, _, _) ← sepAddrSpine a
  let mut related : Array Nat := #[]
  let mut others : Array Nat := #[]
  for hi : i in [:as.size] do
    let atom := as[i]
    let ok := atom.isAppOfArity ``Arm64.pointsToBytes 2 ||
      (!rwOnly && atom.isAppOfArity ``Arm64.pointsToBytesRO 2)
    unless ok do continue
    let (rB, _, _) ← sepAddrSpine (atom.getArg! 0)
    if rB == rA then related := related.push i else others := others.push i
  return related ++ others

/-- `SepLoad*` witness for the byte-list atom `i` of `P` (`base ↦ₛ bs`, or `base ↦ᵣ bs` when
    `isRO`) at a byte offset with bound `hLen` and address equation `ha`, lifted along the `∗`
    spine. The value is `bs.getD off 0#8` (8-bit), `pack16` / `pack32` of the bytes (16/32-bit), or
    `ByteSlice.readLE bs off 8` (64-bit). -/
def sepBytesLoadLeaf (w : Nat) (isRO : Bool) (P : Expr) (i : Nat) (atom a hLen ha : Expr) :
    TacticM (Expr × Expr) := do
  let (fam, thmName) := match w, isRO with
    | 1, true  => (``SepLoad8, ``SepLoad8.of_pointsToBytesRO)
    | 1, false => (``SepLoad8, ``SepLoad8.of_pointsToBytes)
    | 2, true  => (``SepLoad16, ``SepLoad16.of_pointsToBytesRO)
    | 2, false => (``SepLoad16, ``SepLoad16.of_pointsToBytes)
    | 4, true  => (``SepLoad32, ``SepLoad32.of_pointsToBytesRO)
    | 4, false => (``SepLoad32, ``SepLoad32.of_pointsToBytes)
    | _, true  => (``SepLoad64, ``SepLoad64.of_pointsToBytes_readLE_RO)
    | _, false => (``SepLoad64, ``SepLoad64.of_pointsToBytes_readLE)
  let leaf ← mkAppM thmName #[← sepLeafEq atom, hLen, ha]
  let loadedVal := (← instantiateMVars (← inferType leaf)).getArg! 2
  return (loadedVal, ← sepLiftLoad fam a loadedVal P i leaf)

/-- Resolve `fam a val P ?P'` (`fam` in `{SepStore8, ..., SepStore64}` of byte width `w`) against a
    read-write byte-list atom `base ↦ₛ bs` of `P` containing `[a, a + w)` (`sepBytesOffset?`),
    replacing it by `base ↦ₛ ByteSlice.writeW bs off val`. -/
def proveSepStoreToBytes? (fam : Name) (w : Nat) (a val P : Expr) (as : Array Expr) :
    TacticM (Option (Expr × Expr)) := do
  let some (writeFn, leafThm) := (match w with
    | 1 => some (``ByteSlice.write8, ``SepStore8.of_pointsToBytes_here)
    | 2 => some (``ByteSlice.write16, ``SepStore16.of_pointsToBytes_here)
    | 4 => some (``ByteSlice.write32, ``SepStore32.of_pointsToBytes_here)
    | 8 => some (``ByteSlice.write64, ``SepStore64.of_pointsToBytes_here)
    | _ => none : Option (Name × Name)) | return none
  unless CondClassify.proofLib.wpSymbolicBytes.get (← getOptions) do return none
  let mut cache : SpSubstCache := {}
  let ((bAF, oAF), c) ← sepAddrBaseOffFast a cache
  cache := c
  for i in ← sepBytesCandidates as a (rwOnly := true) do
    let atom := as[i]!
    let base := atom.getArg! 0
    let bs := atom.getArg! 1
    let (r?, c) ← sepBytesOffset? w base bs a bAF oAF cache
    cache := c
    let some (off, hLen, ha) := r? | continue
    let leaf := mkAppN (mkConst leafThm) #[a, base, bs, off, val, hLen, ha]
    let atom' := mkApp2 (mkConst ``Arm64.pointsToBytes) base (mkApp3 (mkConst writeFn) bs off val)
    return some (← sepLiftStore fam a val P i atom atom' leaf)
  return none

/-- Resolve `SepStoreDcZva a P ?P'` against a read-write byte-list atom `base ↦ₛ bs` of `P`
    containing `[a, a + 64)` (`sepBytesOffset?`), replacing it by
    `base ↦ₛ ByteSlice.fillSet bs 0#8 (fun i => decide (off ≤ i) && decide (i < off + 64))`. -/
def proveSepStoreDcZvaToBytes? (a P : Expr) : TacticM (Option (Expr × Expr)) := do
  unless CondClassify.proofLib.wpSymbolicBytes.get (← getOptions) do return none
  let as := SepSolver.atoms P
  let mut cache : SpSubstCache := {}
  let ((bAF, oAF), c) ← sepAddrBaseOffFast a cache
  cache := c
  for i in ← sepBytesCandidates as a (rwOnly := true) do
    let atom := as[i]!
    let base := atom.getArg! 0
    let bs := atom.getArg! 1
    let (r?, c) ← sepBytesOffset? 64 base bs a bAF oAF cache
    cache := c
    let some (off, hLen, ha) := r? | continue
    let leaf := mkAppN (mkConst ``SepStoreDcZva.of_pointsToBytes_here) #[a, base, bs, off, hLen, ha]
    let atom' := (← instantiateMVars (← inferType leaf)).getArg! 2
    let some path := sepSpinePath P i
      | throwError "wp_sep_access: no atom {i} in{indentExpr P}"
    let mut prf := leaf
    let mut cur := atom
    let mut cur' := atom'
    for (isLeft, sib) in path do
      if isLeft then
        prf := mkAppN (mkConst ``SepStoreDcZva.left) #[a, cur, cur', sib, prf]
        cur := SepSolver.mkSep cur sib
        cur' := SepSolver.mkSep cur' sib
      else
        prf := mkAppN (mkConst ``SepStoreDcZva.right) #[a, sib, cur, cur', prf]
        cur := SepSolver.mkSep sib cur
        cur' := SepSolver.mkSep sib cur'
    return some (cur', prf)
  return none

/-- Try to resolve a `SepLoad8/16/32/64 a P ?v` goal of byte width `w ∈ {1, 2, 4, 8}` from a
    `pointsToBytesRO` (`base ↦ᵣ bs`) or `pointsToBytes` (`base ↦ₛ bs`) atom in `as`.
    When `bs` is a concrete byte list, reduces the loaded value to a canonical `BitVec` literal.
    Read-write atoms with symbolic contents, and read-only atoms at a symbolic offset, go through
    `sepBytesOffset?` / `sepBytesSymOffset?` (64-bit values as `ByteSlice.readLE bs off 8`).
    Atom bases are compared with the proof-free `sepAddrBaseOffFast` first; `normAddrMeta` and
    `isDefEq` run only for atoms whose base does not match syntactically. -/
def proveSepLoadFromBytes? (w : Nat) (P : Expr) (as : Array Expr) (a : Expr) :
    TacticM (Option (Expr × Expr)) := do
  let symOn := CondClassify.proofLib.wpSymbolicBytes.get (← getOptions)
  let mut cache : SpSubstCache := {}
  let ((bAF, oAF), c) ← sepAddrBaseOffFast a cache
  cache := c
  let mut slowA : Option (Expr × Nat) := none
  for i in ← sepBytesCandidates as a (rwOnly := false) do
    let atom := as[i]!
    let isRO := atom.isAppOfArity ``Arm64.pointsToBytesRO 2
    let isRW := atom.isAppOfArity ``Arm64.pointsToBytes 2
    if isRO || isRW then
      let base := atom.getArg! 0
      let bs := atom.getArg! 1
      let isGroundBs := !bs.hasFVar && !bs.hasMVar
      if isRW && !isGroundBs then
        unless symOn do continue
        let (r?, c) ← sepBytesOffset? w base bs a bAF oAF cache
        cache := c
        if let some (_, hLen, ha) := r? then
          return some (← sepBytesLoadLeaf w false P i atom a hLen ha)
      else
        let ((bBF, oBF), c) ← sepAddrBaseOffFast base cache
        cache := c
        let mut off? : Option Nat := none
        if bAF == bBF then
          off? := some ((oAF + 2 ^ 64 - oBF) % 2 ^ 64)
        else
          let (bA, oA) ← match slowA with
            | some r => Pure.pure r
            | none => do
              let (aNorm, _) ← SepSolver.normAddrMeta a
              sepAddrBaseOff aNorm
          slowA := some (bA, oA)
          let (baseNorm, _) ← SepSolver.normAddrMeta base
          let (bBase, oBase) ← sepAddrBaseOff baseNorm
          if bA == bBase || (← withReducibleAndInstances (isDefEq bA bBase)) then
            off? := some ((oA + 2 ^ 64 - oBase) % 2 ^ 64)
        if symOn && off?.isNone && isRO && !isGroundBs then
          if let some (offE, ts, d) ← sepBytesSymOffset? base a then
            if let some (hLen, ha) ← sepBytesBoundAndAddr? w base bs a offE (some (ts, d)) then
              return some (← sepBytesLoadLeaf w true P i atom a hLen ha)
        let some off := off? | continue
        if off < 0x100000 then
          let lenExpr ← mkAppM ``List.length #[bs]
          let leGoal ← mkAppM ``LE.le #[mkNatLit (off + w), lenExpr]
          let hLen? ← if isGroundBs then do
              let lenWhnf ← withTransparency .default (whnf lenExpr)
              let lenVal? := lenWhnf.rawNatLit? <|>
                (if lenWhnf.isAppOfArity ``OfNat.ofNat 3 then (lenWhnf.getArg! 1).rawNatLit? else none)
              if let some lenVal := lenVal? then
                if off + w ≤ lenVal then
                  observing? (mkDecideProof leGoal)
                else
                  Pure.pure none
              else
                Pure.pure none
            else
              Pure.pure none
          let hLen? ← match hLen? with
            | some p => Pure.pure (some p)
            | none =>
              if isRO then proveByteBound? (mkNatLit (off + w)) bs
              else Pure.pure none
          if let some hLen := hLen? then
            let targetAddr ← mkAppM ``HAdd.hAdd #[base, toExpr (BitVec.ofNat 64 off)]
            let ha ← proveSepAddrEq targetAddr a
            let (fam, thmName) := match w, isRO with
              | 1, true  => (``SepLoad8, ``SepLoad8.of_pointsToBytesRO)
              | 1, false => (``SepLoad8, ``SepLoad8.of_pointsToBytes)
              | 2, true  => (``SepLoad16, ``SepLoad16.of_pointsToBytesRO)
              | 2, false => (``SepLoad16, ``SepLoad16.of_pointsToBytes)
              | 4, true  => (``SepLoad32, ``SepLoad32.of_pointsToBytesRO)
              | 4, false => (``SepLoad32, ``SepLoad32.of_pointsToBytes)
              | _, true  => (``SepLoad64, ``SepLoad64.of_pointsToBytesRO)
              | _, false => (``SepLoad64, ``SepLoad64.of_pointsToBytes)
            let leaf ← mkAppM thmName #[← sepLeafEq atom, hLen, ha]
            let loadedVal := (← instantiateMVars (← inferType leaf)).getArg! 2
            let prf0 ← sepLiftLoad fam a loadedVal P i leaf
            if !loadedVal.hasFVar && !loadedVal.hasMVar then
              let loadedWhnf ← withTransparency .default (whnf loadedVal)
              if let some (bitW, litVal) ← evalBitVecLit? loadedWhnf then
                let vCanon := mkCanonBitVecLit bitW litVal
                let eqTy ← mkEq loadedVal vCanon
                let hv := mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl vCanon)
                let prf ← mkAppM (fam ++ `congr_val) #[prf0, hv]
                return some (vCanon, prf)
            return some (loadedVal, prf0)
  return none

/-- Byte width and read-write / read-only points-to constructors of a `SepLoad*` / `SepStore*`
    family. -/
def sepAccessFamilyInfo (fam : Name) : Option (Nat × Name × Name) :=
  if fam == ``SepLoad8 || fam == ``SepStore8 then
    some (1, ``Arm64.pointsTo8, ``Arm64.pointsTo8RO)
  else if fam == ``SepLoad16 || fam == ``SepStore16 then
    some (2, ``Arm64.pointsTo16, ``Arm64.pointsTo16RO)
  else if fam == ``SepLoad32 || fam == ``SepStore32 then
    some (4, ``Arm64.pointsTo32, ``Arm64.pointsTo32RO)
  else if fam == ``SepLoad64 || fam == ``SepStore64 then
    some (8, ``Arm64.pointsTo64, ``Arm64.pointsTo64RO)
  else none

/-- `"16-bit "` / `"32-bit "` (empty for 8- and 64-bit accesses), used in error messages. -/
def sepAccessWidthLabel (w : Nat) : String :=
  if w == 2 then "16-bit " else if w == 4 then "32-bit " else ""

/-- Leaf address argument `ha : a' = a` for `here` / `here_ro`. -/
def sepLeafAddrEq (a' a : Expr) (haOpt : Option Expr) : TacticM Expr := do
  if a' == a then return ← mkEqRefl a
  match haOpt with
  | some p => Pure.pure p
  | none => proveSepAddrEq a' a

/-- Direct proof builder for `fam a P ?v` (`fam ∈ {SepLoad8, SepLoad16, SepLoad32, SepLoad64}`),
    returning `(v, prf)`: finds the read-write, read-only, or byte-list atom owning `a` and lifts
    its leaf witness along the `∗` spine of `P` (`sepLiftLoad`). -/
def proveSepLoadIn (fam : Name) (a P : Expr) : TacticM (Expr × Expr) := do
  let some (w, pt, ptRO) := sepAccessFamilyInfo fam
    | throwError "wp_sep_access: unsupported load {fam}"
  let P := (← instantiateMVars P).consumeMData
  let as := SepSolver.atoms P
  let found? ← do
    if let some (i, h) ← findPointsToAtomFast pt as a then Pure.pure (some (i, h, false))
    else if let some (i, h) ← findPointsToAtomFast ptRO as a then Pure.pure (some (i, h, true))
    else if let some (i, h) ← findPointsToAtomSlow pt as a then Pure.pure (some (i, h, false))
    else if let some (i, h) ← findPointsToAtomSlow ptRO as a then Pure.pure (some (i, h, true))
    else Pure.pure none
  if let some (i, haOpt, isRO) := found? then
    let atom := as[i]!
    let a' := atom.getArg! 0
    let v := atom.getArg! 1
    let ha ← sepLeafAddrEq a' a haOpt
    let leaf := mkApp4 (mkConst (fam ++ (if isRO then `here_ro else `here))) a a' v ha
    return (v, ← sepLiftLoad fam a v P i leaf)
  if let some res ← proveSepLoadFromBytes? w P as a then
    return res
  throwError "wp_sep_access: no {sepAccessWidthLabel w}cell at {a} in{indentExpr P}"

/-- Lazy-free points-to constructor (`↦₈ₗ` .. `↦₆₄ₗ`) corresponding to store family `fam`. -/
def sepStoreLazyConstructor (fam : Name) : Option Name :=
  if fam == ``SepStore8 then some ``Arm64.pointsTo8Lazy
  else if fam == ``SepStore16 then some ``Arm64.pointsTo16Lazy
  else if fam == ``SepStore32 then some ``Arm64.pointsTo32Lazy
  else if fam == ``SepStore64 then some ``Arm64.pointsTo64Lazy
  else none

/-- Direct proof builder for `fam a val P ?P'` (`fam` in `{SepStore8, ..., SepStore64}`), returning
    `(P', prf)`: replaces the read-write or lazy-free atom owning `a` in place, lifting its leaf
    witness along the `∗` spine of `P` (`sepLiftStore`); falls back to a byte-list atom `base ↦ₛ bs`
    (`proveSepStoreToBytes?`). -/
def proveSepStoreIn (fam : Name) (a val P : Expr) : TacticM (Expr × Expr) := do
  let some (w, pt, _) := sepAccessFamilyInfo fam
    | throwError "wp_sep_access: unsupported store {fam}"
  let P := (← instantiateMVars P).consumeMData
  let as := SepSolver.atoms P
  if let some (i, haOpt) ← findPointsToAtom pt as a then
    let atom := as[i]!
    let a' := atom.getArg! 0
    let new := mkApp2 (mkConst pt) a' val
    let ha ← sepLeafAddrEq a' a haOpt
    let leaf := mkApp5 (mkConst (fam ++ `here)) a a' (atom.getArg! 1) val ha
    return ← sepLiftStore fam a val P i atom new leaf
  if let some ptLazy := sepStoreLazyConstructor fam then
    if let some (i, haOpt) ← findPointsToAtom ptLazy as a 1 then
      let atom := as[i]!
      let a' := atom.getArg! 0
      let new := mkApp2 (mkConst pt) a' val
      let ha ← sepLeafAddrEq a' a haOpt
      let leaf := mkApp4 (mkConst (fam ++ `here_lazy)) a a' val ha
      return ← sepLiftStore fam a val P i atom new leaf
  if let some res ← proveSepStoreToBytes? fam w a val P as then return res
  throwError "wp_sep_access: no {sepAccessWidthLabel w}cell at {a} in{indentExpr P}"

/-- Direct `TacticM` proof builder for `SepLoad8 a P ?v` or `SepLoad64 a P ?v`, returning `(v, prf)`.
    Supports read-write (`↦₈`, `↦₆₄`), read-only (`↦₈ᵣ`, `↦₆₄ᵣ`), and byte-list (`↦ᵣ`, `↦ₛ`) atoms. -/
def proveSepLoad (pt : Name) (a P : Expr) : TacticM (Expr × Expr) :=
  proveSepLoadIn (if pt == ``Arm64.pointsTo8 then ``SepLoad8 else ``SepLoad64) a P

/-- Direct `TacticM` proof builder for `SepStore8 a val P ?P'` or `SepStore64 a val P ?P'`, returning `(P', prf)`. -/
def proveSepStore (pt : Name) (a val P : Expr) : TacticM (Expr × Expr) :=
  proveSepStoreIn (if pt == ``Arm64.pointsTo8 then ``SepStore8 else ``SepStore64) a val P

/-- A proof of a `SepLoad8/16/32/64`, `SepStore8/16/32/64`, or `SepFrame` goal `ty` built with
    the separation-logic solver. Loads and stores lift the owning atom's leaf witness along the
    `∗` spine (stores replace the atom in place); frames split the spatial context
    (`SepSolver.frameSplit?`, instantiating the frame). -/
def sepAccessProof (ty : Expr) : TacticM Expr := do
  let ty := SepSolver.stripMData ty
  let fn := ty.getAppFn.constName?.getD .anonymous
  let args := ty.getAppArgs
  if fn == ``SepLoad8 || fn == ``SepLoad16 || fn == ``SepLoad32 || fn == ``SepLoad64 then
    let (v, prf) ← proveSepLoadIn fn args[0]! args[1]!
    unless ← isDefEq args[2]! v do
      throwError "wp_sep_access: cannot assign loaded value {v}"
    return prf
  if fn == ``SepStore8 || fn == ``SepStore16 || fn == ``SepStore32 || fn == ``SepStore64 then
    let (P', prf) ← proveSepStoreIn fn args[0]! args[1]! args[2]!
    unless ← isDefEq args[3]! P' do
      throwError "wp_sep_access: cannot assign {P'}"
    return prf
  if fn == ``SepStoreDcZva then
    let some (P', prf) ← proveSepStoreDcZvaToBytes? args[0]! args[1]!
      | throwError "wp_sep_access: no 64-byte slice in{indentExpr args[1]!} for{indentExpr args[0]!}"
    unless ← isDefEq args[2]! P' do
      throwError "wp_sep_access: cannot assign {P'}"
    return prf
  if fn == ``SepFrame then
    let some (frame, eq) ← SepSolver.frameSplit? args[0]! args[1]!
      | do
        let msg ← SepSolver.explainFrameSplitFailure args[0]! args[1]!
        throwError msg
    unless ← isDefEq args[2]! frame do throwError "wp_sep_access: cannot assign frame {frame}"
    return ← mkAppM ``SepFrame.mk #[eq]
  throwError "wp_sep_access: unsupported goal{indentExpr ty}"

/-- A proof of a `SepLoad16` / `SepStore16` goal `ty` (see `sepAccessProof`). -/
def sepAccess16Proof (ty : Expr) : TacticM Expr := sepAccessProof ty

/-- A proof of a `SepLoad32` / `SepStore32` goal `ty` (see `sepAccessProof`). -/
def sepAccess32Proof (ty : Expr) : TacticM Expr := sepAccessProof ty

/-- Find a `(a' ↦₃₂ v)` or `(a' ↦₃₂ᵣ v)` atom in `as` covering byte address `a` at sub-offset
    `k ∈ {0, 1, 2, 3}`, returning `(idx, k, isRO)`. -/
def findPointsTo32SubByte (as : Array Expr) (a : Expr) : MetaM (Option (Nat × Nat × Bool)) := do
  let (b, o) ← sepAddrBaseOff a
  for hx : j in [:as.size] do
    let isRW := as[j].isAppOfArity ``Arm64.pointsTo32 2
    let isRO := as[j].isAppOfArity ``Arm64.pointsTo32RO 2
    if isRW || isRO then
      let (b', o') ← sepAddrBaseOff (as[j].getArg! 0)
      let k := (o + 2 ^ 64 - o') % 2 ^ 64
      if k < 4 then
        if b' == b || (← withReducible (isDefEq b' b)) then
          return some (j, k, isRO)
  return none

/-- Resolve `SepLoad8 a P ?v` from a `(a' ↦₃₂ v32)` or `(a' ↦₃₂ᵣ v32)` atom at byte offset `0..3`. -/
def sepLoad8From32Proof (ty : Expr) : TacticM Expr := do
  let ty := SepSolver.stripMData ty
  let args := ty.getAppArgs
  let a := args[0]!
  let P := (← instantiateMVars args[1]!).consumeMData
  let as := SepSolver.atoms P
  let some (i, k, isRO) ← findPointsTo32SubByte as a
    | throwError "wp_sep_access: no 8-bit or 32-bit cell covering {a} in{indentExpr P}"
  let atom := as[i]!
  let a' := atom.getArg! 0
  let v32 := atom.getArg! 1
  let (thmName, bitOff, targetAddr) ← match k, isRO with
    | 0, false => Pure.pure (``SepLoad8.of_pointsTo32_0, 0, a')
    | 0, true  => Pure.pure (``SepLoad8.of_pointsTo32RO_0, 0, a')
    | 1, false => Pure.pure (``SepLoad8.of_pointsTo32_1, 8, ← mkAppM ``HAdd.hAdd #[a', toExpr (1#64)])
    | 1, true  => Pure.pure (``SepLoad8.of_pointsTo32RO_1, 8, ← mkAppM ``HAdd.hAdd #[a', toExpr (1#64)])
    | 2, false => Pure.pure (``SepLoad8.of_pointsTo32_2, 16, ← mkAppM ``HAdd.hAdd #[a', toExpr (2#64)])
    | 2, true  => Pure.pure (``SepLoad8.of_pointsTo32RO_2, 16, ← mkAppM ``HAdd.hAdd #[a', toExpr (2#64)])
    | _, false => Pure.pure (``SepLoad8.of_pointsTo32_3, 24, ← mkAppM ``HAdd.hAdd #[a', toExpr (3#64)])
    | _, true  => Pure.pure (``SepLoad8.of_pointsTo32RO_3, 24, ← mkAppM ``HAdd.hAdd #[a', toExpr (3#64)])
  let ha ← proveSepAddrEq targetAddr a
  let loadedVal ← mkAppM ``BitVec.extractLsb' #[toExpr bitOff, toExpr (8 : Nat), v32]
  unless ← isDefEq args[2]! loadedVal do
    throwError "wp_sep_access: cannot assign loaded byte {loadedVal}"
  let leaf ← mkAppM thmName #[← sepLeafEq atom, ha]
  let leafVal := (← instantiateMVars (← inferType leaf)).getArg! 2
  sepLiftLoad ``SepLoad8 a leafVal P i leaf

/-- Close a `SepLoad8/16/32/64`, `SepStore8/16/32/64`, or `SepFrame` goal (see `sepAccessProof`,
    `sepAccess16Proof`, `sepAccess32Proof`, and `sepLoad8From32Proof`). -/
elab "wp_sep_access" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let tyClean := ty.consumeMData
    let prf ←
      if tyClean.isAppOf ``SepLoad16 || tyClean.isAppOf ``SepStore16 then
        sepAccess16Proof ty
      else if tyClean.isAppOf ``SepLoad32 || tyClean.isAppOf ``SepStore32 then
        sepAccess32Proof ty
      else if tyClean.isAppOf ``SepLoad8 then
        try sepAccessProof ty
        catch _ => sepLoad8From32Proof ty
      else
        sepAccessProof ty
    unless ← isDefEq (← inferType prf) ty do throwError "wp_sep_access: type mismatch"
    g.assign prf
  replaceMainGoal []

/-- Alias for `wp_sep_access` (which uses linear `.consumeMData` spine traversal on large
    separation-logic frames). -/
macro "wp_sep_access_fast" : tactic => `(tactic| wp_sep_access)

/-- Focus `conv` on the spatial/pure precondition `P` (`arg 4`) of a `SepWP` or `SepWPp` goal,
    leaving the postcondition `post` untouched. -/
macro "wp_conv_pre" " => " cs:Lean.Parser.Tactic.Conv.convSeq : tactic =>
  `(tactic| conv => arg 4; ($cs))

/-- Focus `conv` on the postcondition slot `Q` (`arg 5`) of a `SepWP` or `SepWPp` goal,
    leaving the spatial/pure precondition `P` untouched. Fails if the target is not a `SepWP`
    or `SepWPp` goal. -/
elab "wp_conv_post" " => " cs:Lean.Parser.Tactic.Conv.convSeq : tactic => do
  let g ← getMainGoal
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if !(tgt.isAppOf ``SepWP || tgt.isAppOf ``SepWPp) then
    throwError "wp_conv_post: expected a `SepWP` or `SepWPp` goal, got{indentExpr tgt}"
  evalTactic (← `(tactic| conv => arg 5; ($cs)))

/-- Simplify only the spatial/pure precondition `P` (`arg 4`) of a `SepWP` or `SepWPp` goal,
    leaving postcondition definitions untouched by `simp`. -/
elab "wp_simp_pre" : tactic =>
  withWpHeartbeatDiag "wp_simp_pre" "precondition simplification (`conv => arg 4; simp only [wp_norm, arm64_norm]`)"
    "compact a deep state/precondition first with `wp_compact`, or restrict the lemma set with `wp_simp_pre only [...]`" do
    evalTactic (← `(tactic| conv => arg 4; simp only [wp_norm, arm64_norm]))

elab "wp_simp_pre" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  withWpHeartbeatDiag "wp_simp_pre" "precondition simplification (`conv => arg 4; simp [...]`)"
    "use `wp_simp_pre only [...]` instead of unrestricted `wp_simp_pre [...]`, or compact the state/precondition first with `wp_compact`" do
    evalTactic (← `(tactic| conv => arg 4; simp [$[$args:simpLemma],*]))

elab "wp_simp_pre" "only" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  withWpHeartbeatDiag "wp_simp_pre" "precondition simplification (`conv => arg 4; simp only [...]`)"
    "compact a deep state/precondition first with `wp_compact`, or discharge side conditions on simp lemmas with `have h : ... := by bv_omega` before `wp_simp_pre only [...]`" do
    evalTactic (← `(tactic| conv => arg 4; simp only [$[$args:simpLemma],*]))

/-- Close the main goal using a local hypothesis that matches at `.reducible` transparency
    (avoiding expensive WHNF unfolding of `Program.codeAt` / `Program.hasCode` / `DisjointRegions`). -/
elab "wp_assumption" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    for decl in (← getLCtx) do
      if !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ← withReducible (isDefEq ty target) then
          g.assign decl.toExpr
          replaceMainGoal []
          return
    throwError "wp_assumption: no matching hypothesis"

private def isMask64Compl63 (m : Expr) : Bool :=
  let m := m.consumeMData
  evalBitVecLitPure? m == some (64, 0xffffffffffffffc0) ||
  (m.isAppOfArity ``Complement.complement 3 &&
   evalBitVecLitPure? (m.getArg! 2) == some (64, 63)) ||
  (m.isAppOfArity ``BitVec.not 2 &&
   evalBitVecLitPure? (m.getArg! 1) == some (64, 63))

/-- Resolve `v &&& ~~~63#64 = ?ea` for `DC ZVA, Xt`, returning `(ea, proof)`:
    1. Direct local hypothesis `u &&& mask = ea` (with `mask` either `~~~63#64` or
       `0xffffffffffffffc0#64`, including unfolded user alignment predicates) where `u` matches `v`.
    2. 64-byte alignment of `v` or of a base address `u` from which `v = u + BitVec.ofNat 64 off`
       is offset by a multiple of 64 (`off % 64 = 0`), where `u`'s alignment comes from a local
       hypothesis (`u &&& mask = u`, `u &&& 63#64 = 0#64`, or `u.toNat % 64 = 0`) or from `u`
       itself being a masked expression `x &&& 0xffffffffffffffc0#64`. -/
def proveDcZvaEa? (v : Expr) : TacticM (Option (Expr × Expr)) := do
  let mut alignedBases : Array (Expr × Expr) := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let dty ← instantiateMVars decl.type
      let eqOpt ← match dty.eq? with
        | some eq => Pure.pure (some eq)
        | none =>
          if dty.consumeMData.getAppFn.isConst && !dty.isAppOf ``SepProp.Satisfies &&
             !dty.isAppOf ``Program.hasCode && !dty.isAppOf ``Program.hasWords &&
             !dty.isAppOf ``Program.codeAt && !dty.isAppOf ``Arm64.DisjointRegions then
            Pure.pure (← withTransparency .default (whnf dty)).eq?
          else
            Pure.pure none
      if let some (_, dlhs, drhs) := eqOpt then
        let dlhsC := dlhs.consumeMData
        if dlhsC.isAppOfArity ``HAnd.hAnd 6 then
          let u := dlhsC.getArg! 4
          let m := dlhsC.getArg! 5
          if isMask64Compl63 m then
            if u == v || (← withReducible (isDefEq u v)) then
              return some (drhs, mkApp3 (mkConst ``dcZva_ea_of_mask_eq) v drhs decl.toExpr)
            if u == drhs || (← withReducible (isDefEq u drhs)) then
              alignedBases := alignedBases.push (u, decl.toExpr)
          else if evalBitVecLitPure? m == some (64, 63) &&
                  evalBitVecLitPure? drhs == some (64, 0) then
            alignedBases := alignedBases.push
              (u, mkApp2 (mkConst ``dcZva_aligned_of_and63_zero) u decl.toExpr)
        else if dlhsC.isAppOfArity ``HMod.hMod 6 then
          let uNat := (dlhsC.getArg! 4).consumeMData
          let mNat := dlhsC.getArg! 5
          if uNat.isAppOfArity ``BitVec.toNat 2 && mNat.nat? == some 64 && drhs.nat? == some 0 then
            let u := uNat.getArg! 1
            alignedBases := alignedBases.push
              (u, mkApp2 (mkConst ``dcZva_aligned_of_toNat_mod64) u decl.toExpr)
  let (rV, _, _) ← sepAddrSpine v
  let rVC := rV.consumeMData
  if rVC.isAppOfArity ``HAnd.hAnd 6 && isMask64Compl63 (rVC.getArg! 5) then
    let x := rVC.getArg! 4
    let u ← mkAppM ``HAnd.hAnd #[x, toExpr (0xffffffffffffffc0#64)]
    alignedBases := alignedBases.push (u, mkApp (mkConst ``dcZva_aligned_of_and_mask) x)
  if alignedBases.isEmpty then return none
  let mut cache : SpSubstCache := {}
  let ((bVF, oVF), c) ← sepAddrBaseOffFast v cache
  cache := c
  for (u, hu) in alignedBases do
    if u == v || (← withReducible (isDefEq u v)) then
      return some (v, mkApp3 (mkConst ``dcZva_ea_of_mask_eq) v v hu)
    if let some heq ← ProofLib.BV.Lin.proveEq? u v then
      return some (v, mkApp4 (mkConst ``dcZva_ea_of_aligned_eq) u v hu heq)
    let ((bUF, oUF), c) ← sepAddrBaseOffFast u cache
    cache := c
    if bUF == bVF then
      let off := (oVF + 2 ^ 64 - oUF) % 2 ^ 64
      if off < 0x100000 && off % 64 == 0 then
        let offE := mkNatLit off
        let target ← sepBytesTarget u offE
        if let some hadd ← ProofLib.BV.Lin.proveEq? target v then
          let hmod ← mkEqRefl (mkNatLit 0)
          return some (v, mkAppN (mkConst ``dcZva_ea_of_aligned_add_ofNat) #[u, v, offE, hu, hmod, hadd])
    if let some (offE, ts, d) ← sepBytesSymOffset? u v then
      let modLhs ← mkAppM ``HMod.hMod #[offE, mkNatLit 64]
      let modGoal ← mkEq modLhs (mkNatLit 0)
      if let some hmod ← proveNatOmega? modGoal then
        if let some hadd ← proveSepSymAddrEq? u v offE ts d then
          return some (v, mkAppN (mkConst ``dcZva_ea_of_aligned_add_ofNat) #[u, v, offE, hu, hmod, hadd])
  return none

/-- Close a `v &&& ~~~63#64 = ?ea` subgoal of `step_dcZva_bytes` / `step_dcZva`. -/
elab "wp_dc_zva_ea" : tactic => do
  let g ← getMainGoal
  let ok ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq? | return false
    unless lhs.consumeMData.isAppOfArity ``HAnd.hAnd 6 do return false
    let v := lhs.consumeMData.getArg! 4
    let some (ea, prf) ← proveDcZvaEa? v | return false
    unless ← isDefEq rhs ea do return false
    unless ← isDefEq (← inferType prf) ty do return false
    g.assign prf
    return true
  if ok then
    replaceMainGoal []
  else
    throwError "wp_dc_zva_ea: could not resolve DC ZVA effective address"

/-- Prove `s.status = .Running` directly in `MetaM` using `extractStateStatusProof` and local hypotheses. -/
def proveStatusRunningExpr? (s : Expr) : MetaM (Option Expr) := do
  let lhs := mkApp (mkConst ``State.status) s
  let rhs := mkConst ``ExecStatus.Running
  let extract? ← extractStateStatusProof s
  let stExpr := (extract?.map (·.1)).getD lhs
  if stExpr.isConstOf ``ExecStatus.Running then
    match extract? with
    | some (_, prf) => return some prf
    | none => return some (← mkEqRefl rhs)
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let dty ← instantiateMVars decl.type
      if let some (_, dlhs, drhs) := dty.eq? then
        if dlhs == stExpr && drhs.isConstOf ``ExecStatus.Running then
          match extract? with
          | some (_, prf) => return some (← mkEqTrans prf decl.toExpr)
          | none => return some decl.toExpr
  return none

/-- Prove `lhs = rhs` between memory expressions (where either or both sides may be `State.mem s`
    projections over state-update spines) by peeling `State` spine constructors on both sides via
    `extractStateMemProof`, avoiding `isDefEq s1.mem s2.mem` (which unfolds the entire register-write
    spine via `isDefEqProj` and structure eta). -/
def proveMemEqExpr? (lhs rhs : Expr) : MetaM (Option Expr) := do
  if lhs == rhs then
    return some (← mkEqRefl lhs)
  let res1? ← if lhs.isAppOfArity ``State.mem 1 then extractStateMemProof (lhs.getArg! 0) else pure none
  let res2? ← if rhs.isAppOfArity ``State.mem 1 then extractStateMemProof (rhs.getArg! 0) else pure none
  let m1 := (res1?.map (·.1)).getD lhs
  let m2 := (res2?.map (·.1)).getD rhs
  if m1 == m2 then
    match res1?, res2? with
    | some (_, prf1), some (_, prf2) => return some (← mkEqTrans prf1 (← mkEqSymm prf2))
    | some (_, prf1), none => return some prf1
    | none, some (_, prf2) => return some (← mkEqSymm prf2)
    | none, none => return some (← mkEqRefl m1)
  return none

/-- Prove `s1.mem = s2.mem` by peeling state-update constructors off both `s1` and `s2` via
    `extractStateMemProof`, avoiding `isDefEq s1.mem s2.mem`. -/
def proveMemEq? (s1 s2 : Expr) : MetaM (Option Expr) :=
  proveMemEqExpr? (mkApp (mkConst ``State.mem) s1) (mkApp (mkConst ``State.mem) s2)

/-- Extract `(pc, prf : s.pc = pc)` by peeling state-update constructors off `s`. -/
def provePcEq? (s : Expr) : MetaM (Option (Expr × Expr)) :=
  extractStatePCProof s

end

@[expose] public section

theorem sp_and_15_of_spAligned {s : Arm64.State} (h : s.spAligned = true) :
    (s.sp &&& 0b1111#64) = 0#64 :=
  of_decide_eq_true h

theorem sp_and_15_of_beq_true {sp : BitVec 64} (h : ((sp &&& 0b1111#64) == 0#64) = true) :
    (sp &&& 0b1111#64) = 0#64 :=
  of_decide_eq_true h

theorem checkAddrSPAligned_of_sp_and_eq_zero (b : Bool) (s : Arm64.State) (sp : BitVec 64)
    (h_def : b = ((s.sp &&& 0b1111#64) == 0#64))
    (h_sp : s.sp = sp)
    (h_eq : (sp &&& 0b1111#64) = 0#64) : b = true := by
  rw [h_def, h_sp, h_eq]; rfl

theorem sp_and_15_of_eq {sp1 sp2 : BitVec 64} (heq : sp1 = sp2) (h : (sp2 &&& 0b1111#64) = 0#64) :
    (sp1 &&& 0b1111#64) = 0#64 :=
  heq ▸ h

end

public meta section

/-- Recursively prove `(spExpr &&& 0b1111#64) = 0#64` from local `hsp_align` hypotheses,
    local `sp` equality hypotheses (`s1.sp = sp - 64#64`, `sp = s0.sp`, etc.), and
    16-byte-aligned constant additions/subtractions (`sp_and_15_add_aligned`, `sp_and_15_sub_aligned`). -/
partial def proveSpAnd15EqZero? (spExpr : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let ty := decl.type
      if let some (_, lhs, rhs) := ty.eq? then
        if evalBitVecLitPure? rhs == some (64, 0) && lhs.isAppOfArity ``HAnd.hAnd 6 &&
           lhs.getArg! 4 == spExpr && evalBitVecLitPure? (lhs.getArg! 5) == some (64, 15) then
          return some decl.toExpr
        if rhs.isConstOf ``Bool.true then
          if lhs.isAppOfArity ``State.spAligned 1 &&
             spExpr.isAppOfArity ``State.sp 1 &&
             lhs.getArg! 0 == spExpr.getArg! 0 then
            return some (mkApp2 (mkConst ``sp_and_15_of_spAligned) (lhs.getArg! 0) decl.toExpr)
          if lhs.isAppOfArity ``BEq.beq 4 && evalBitVecLitPure? (lhs.getArg! 3) == some (64, 0) then
            let andSub := lhs.getArg! 2
            if andSub.isAppOfArity ``HAnd.hAnd 6 &&
               andSub.getArg! 4 == spExpr && evalBitVecLitPure? (andSub.getArg! 5) == some (64, 15) then
              return some (mkApp2 (mkConst ``sp_and_15_of_beq_true) spExpr decl.toExpr)
  if spExpr.isAppOfArity ``HSub.hSub 6 then
    let sp0 := spExpr.getArg! 4
    let kExpr := spExpr.getArg! 5
    if let some (64, k) := evalBitVecLitPure? kExpr then
      if k % 16 == 0 then
        if let some prf0 ← proveSpAnd15EqZero? sp0 (fuel - 1) then
          let hk := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
          let stepPrf := mkApp3 (mkConst ``sp_and_15_sub_aligned) sp0 kExpr hk
          return some (← mkEqTrans stepPrf prf0)
  if spExpr.isAppOfArity ``HAdd.hAdd 6 then
    let sp0 := spExpr.getArg! 4
    let kExpr := spExpr.getArg! 5
    if let some (64, k) := evalBitVecLitPure? kExpr then
      if k % 16 == 0 then
        if let some prf0 ← proveSpAnd15EqZero? sp0 (fuel - 1) then
          let hk := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
          let stepPrf := mkApp3 (mkConst ``sp_and_15_add_aligned) sp0 kExpr hk
          return some (← mkEqTrans stepPrf prf0)
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let ty := decl.type
      if let some (_, lhs, rhs) := ty.eq? then
        if lhs == spExpr && rhs != spExpr then
          if let some prfRhs ← proveSpAnd15EqZero? rhs (fuel - 1) then
            return some (mkApp4 (mkConst ``sp_and_15_of_eq) spExpr rhs decl.toExpr prfRhs)
        if rhs == spExpr && lhs != spExpr then
          if let some prfLhs ← proveSpAnd15EqZero? lhs (fuel - 1) then
            let hSymm ← mkEqSymm decl.toExpr
            return some (mkApp4 (mkConst ``sp_and_15_of_eq) spExpr lhs hSymm prfLhs)
  return none

/-- Prove `checkAddrSPAligned s amExpr = true` in `O(spine)` in `MetaM` without running `simp`,
    for both non-SP and SP-relative addressing modes. -/
def proveCheckAddrSPAligned? (target lhs rhs : Expr) : MetaM (Option Expr) := do
  if !rhs.isConstOf ``Bool.true || !lhs.isAppOfArity ``checkAddrSPAligned 2 then
    return none
  let s := lhs.getArg! 0
  let amExpr := lhs.getArg! 1
  if (amExpr.find? (fun e => e.isConstOf ``Reg.sp || e.isConstOf ``Reg.fromSPBits)).isNone then
    if (amExpr.find? (·.isFVar)).isNone then
      return some (mkApp2 (mkConst ``id [Level.zero]) target
        (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)))
    if ← isDefEq lhs rhs then
      return some (mkApp2 (mkConst ``id [Level.zero]) target
        (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)))
    return none
  let (spExpr, hSp) ← extractStateSPProofOrRefl s
  let some hEq0 ← proveSpAnd15EqZero? spExpr | return none
  let sSp := mkApp (mkConst ``State.sp) s
  let andExpr ← mkAppM ``HAnd.hAnd #[sSp, mkCanonBitVecLit 64 15]
  let beqExpr ← mkAppM ``BEq.beq #[andExpr, mkCanonBitVecLit 64 0]
  let defEqTy ← mkEq lhs beqExpr
  let hDef := mkApp2 (mkConst ``id [Level.zero]) defEqTy (← mkEqRefl beqExpr)
  return some (mkApp6 (mkConst ``checkAddrSPAligned_of_sp_and_eq_zero) lhs s spExpr hDef hSp hEq0)

/-- Prove `s.spAligned = true` in `O(spine)` in `MetaM` without running `simp`. -/
def proveStateSpAligned? (_target lhs rhs : Expr) : MetaM (Option Expr) := do
  if !rhs.isConstOf ``Bool.true || !lhs.isAppOfArity ``State.spAligned 1 then
    return none
  let s := lhs.getArg! 0
  let (spExpr, hSp) ← extractStateSPProofOrRefl s
  let some hEq0 ← proveSpAnd15EqZero? spExpr | return none
  let sSp := mkApp (mkConst ``State.sp) s
  let andExpr ← mkAppM ``HAnd.hAnd #[sSp, mkCanonBitVecLit 64 15]
  let beqExpr ← mkAppM ``BEq.beq #[andExpr, mkCanonBitVecLit 64 0]
  let defEqTy ← mkEq lhs beqExpr
  let hDef := mkApp2 (mkConst ``id [Level.zero]) defEqTy (← mkEqRefl beqExpr)
  return some (mkApp6 (mkConst ``checkAddrSPAligned_of_sp_and_eq_zero) lhs s spExpr hDef hSp hEq0)

/-- Prove `(applyWriteback s none).setPC (pc1 + 4#64) = s'` directly in `O(1)` for non-writeback store rules,
    returning `(s', proof)`. -/
def proveApplyWritebackNoneSetPCDirect? (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  if !lhs.isAppOfArity ``State.setPC 2 then return none
  let wbApp := lhs.getArg! 0
  let pcPlus4 := lhs.getArg! 1
  if !wbApp.isAppOfArity ``applyWriteback 2 then return none
  let s := wbApp.getArg! 0
  let wb := wbApp.getArg! 1
  if !wb.isAppOfArity ``Option.none 1 then return none
  if !pcPlus4.isAppOfArity ``HAdd.hAdd 6 then return none
  let pc1 := pcPlus4.getArg! 4
  let fourExpr := pcPlus4.getArg! 5
  if evalBitVecLitPure? fourExpr != some (64, 4) then return none
  let (pc2, hpc) ← do
    if let some (64, c) := evalBitVecLitPure? pc1 then
      let pc2 := mkCanonBitVecLit 64 ((c + 4) % (1 <<< 64))
      let eqTy ← mkEq pcPlus4 pc2
      let hpc := mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl pc2)
      pure (pc2, hpc)
    else if let some (pc2, hpc) ← SepSolver.foldBV64OffsetTop? pcPlus4 then
      pure (pc2, hpc)
    else
      pure (pcPlus4, ← mkEqRefl pcPlus4)
  if s.isAppOfArity ``State.setPC 2 then
    let s0 := s.getArg! 0
    let pc := s.getArg! 1
    let rhsTarget := mkApp2 (mkConst ``State.setPC) s0 pc2
    return some (rhsTarget, mkApp5 (mkConst ``State.applyWriteback_none_setPC) s0 pc pc1 pc2 hpc)
  if s.isAppOfArity ``State.setMem 2 && (s.getArg! 0).isAppOfArity ``State.setPC 2 then
    let sInner := s.getArg! 0
    let m := s.getArg! 1
    let s0 := sInner.getArg! 0
    let pc := sInner.getArg! 1
    let rhsTarget := mkApp2 (mkConst ``State.setMem) (mkApp2 (mkConst ``State.setPC) s0 pc2) m
    return some (rhsTarget, mkApp6 (mkConst ``State.applyWriteback_none_setMem_setPC) s0 pc pc1 pc2 m hpc)
  return none

/-- Prove `(applyWriteback s none).setPC (pc1 + 4#64) = ?s'` in `O(1)` for non-writeback store rules. -/
def proveApplyWritebackNoneSetPC? (lhs rhs : Expr) : MetaM (Option Expr) := do
  let some (rhsTarget, prf) ← proveApplyWritebackNoneSetPCDirect? lhs | return none
  if ← isDefEq rhs rhsTarget then
    return some prf
  return none

/-- Cached `Simp.Context`, `SimprocsArray`, and persistent `Simp.State` across `wp_norm_lhs` calls
    within the same basic block. -/
structure WpNormSimpCache where
  declName : Name
  lastDeclFVar? : Option FVarId := none
  numIndices : Nat := 0
  hasMVarInLCtx : Bool := false
  hypsKey : Array (FVarId × Expr)
  ctx : Simp.Context
  simprocs : Simp.SimprocsArray
  simpState : Simp.State

/-- Per-declaration `IO.Ref (Option WpNormSimpCache)` (`m_rc > 0`) stored in a `.local`
    environment extension. Unlike a persistent module-level `initialize` ref (`m_rc = 0`), a
    per-declaration ref takes the single-threaded fast path in `lean_st_ref_set` without calling
    `lean_mark_mt` on the growing `Simp.Cache` or the live symbolic state, while mutations inside
    backtracking `saveState`/`restore` scopes survive rollback. -/
initialize wpNormSimpCacheRefExt : EnvExtension (Option (IO.Ref (Option WpNormSimpCache))) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Obtain (or lazily allocate once for the current declaration) the per-declaration `IO.Ref`
    backing `WpNormSimpCache`, along with `VCGenDeclCache`. -/
def getOrCreateWpNormSimpCacheRef : CoreM (IO.Ref (Option WpNormSimpCache)) := do
  if let some ref := wpNormSimpCacheRefExt.getState (← getEnv) then
    return ref
  let _ ← getOrCreateVCGenDeclCacheRef
  let ref ← IO.mkRef none
  modify fun s => { s with env := wpNormSimpCacheRefExt.setState s.env (some ref) }
  return ref

/-- The cached `WpNormSimpCache` of declaration `declName`, if any. -/
def getWpNormSimpCache? (declName : Name) : CoreM (Option WpNormSimpCache) := do
  let ref ← getOrCreateWpNormSimpCacheRef
  match ← ref.get with
  | some c => return if c.declName == declName then some c else none
  | none => return none

/-- Replace the cached `WpNormSimpCache` (one entry, for `c.declName`) via single-threaded `IO.Ref.set`. -/
def setWpNormSimpCache (c : WpNormSimpCache) : CoreM Unit := do
  let ref ← getOrCreateWpNormSimpCacheRef
  ref.set (some c)

/-- Seed normalized `State` spine prefixes, register values, and `Prod.mk` components into `cache`
    so subsequent `simpCore` calls hit `cache` in `O(1)` without re-traversing normalized subterms. -/
partial def seedNormalizedInSimpCache (e : Expr) (cache : Simp.Cache) : Simp.Cache :=
  if e.hasMVar || cache.contains e then
    cache
  else
    let cache := cache.insert e { expr := e, proof? := none }
    if e.isAppOfArity ``State.setMem 2 then
      seedNormalizedInSimpCache (e.getArg! 0) cache
    else if e.isAppOfArity ``State.setPC 2 then
      let cache := seedNormalizedInSimpCache (e.getArg! 1) cache
      seedNormalizedInSimpCache (e.getArg! 0) cache
    else if e.isAppOfArity ``State.setPState 2 then
      let cache := seedNormalizedInSimpCache (e.getArg! 1) cache
      seedNormalizedInSimpCache (e.getArg! 0) cache
    else if e.isAppOfArity ``State.writeReg64 3 || e.isAppOfArity ``State.writeVReg128 3 then
      let cache := seedNormalizedInSimpCache (e.getArg! 2) cache
      seedNormalizedInSimpCache (e.getArg! 0) cache
    else if e.isAppOfArity ``Prod.mk 4 then
      let cache := seedNormalizedInSimpCache (e.getArg! 2) cache
      seedNormalizedInSimpCache (e.getArg! 3) cache
    else if e.isAppOfArity ``Option.some 2 then
      seedNormalizedInSimpCache (e.getArg! 1) cache
    else
      cache

/-- Check whether a local hypothesis type `ty` is a heavy spatial, code, or disjointness
    assertion that should never be unfolded/indexed by `SimpTheorems.addSimpTheorem` (`*`). -/
def isHeavyNonSimpHyp (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  ty.isAppOf ``SepProp.Satisfies ||
  ty.isAppOf ``Program.hasCode ||
  ty.isAppOf ``Program.hasWords ||
  ty.isAppOf ``Program.codeAt ||
  ty.isAppOf ``Arm64.DisjointRegions ||
  ty.isAppOf ``Arm64.Memory.Disjoint64 ||
  ty.isAppOf ``Arm64.Memory.Disjoint128 ||
  ty.isAppOf ``Arm64.CalleeSavedPreserved ||
  ty.isAppOf ``Arm64.CallingConventionPreserved ||
  ty.isAppOf ``Arm64.StackPreserved ||
  ty.isAppOf ``Arm64.SubroutinePost ||
  ty.isAppOf ``Arm64.subroutine_ok ||
  ty.isAppOf ``Program.subroutineOk ||
  match ty.eq? with
  | some (_, lhs, _) =>
    lhs.isAppOf ``Program.fetch || lhs.isAppOf ``Program.externAt? ||
    (lhs.find? (hasDeepListSpine · 64)).isSome
  | none =>
    if ty.isAppOfArity ``Iff 2 || ty.isAppOfArity ``Ne 3 then
      ((ty.getArg! (ty.getAppNumArgs - 2)).find? (hasDeepListSpine · 64)).isSome
    else if ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``LE.le 4 ||
            ty.isAppOfArity ``GT.gt 4 || ty.isAppOfArity ``GE.ge 4 then
      (ty.find? (hasDeepListSpine · 64)).isSome
    else
      false

/-- Check whether `ty` is a lightweight propositional hypothesis (equality, iff, negation,
    inequality, or conjunction thereof) that can be safely passed as an explicit `simp` argument
    without failing on `Prop` structures whose fields contain existentials. -/
partial def isLightweightSimpHyp (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  if isHeavyNonSimpHyp ty then false
  else if ty.isAppOfArity ``Eq 3 || ty.isAppOfArity ``Iff 2 || ty.isAppOfArity ``Ne 3 ||
          ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``LE.le 4 ||
          ty.isAppOfArity ``GT.gt 4 || ty.isAppOfArity ``GE.ge 4 then
    true
  else if ty.isAppOfArity ``Not 1 then
    !isHeavyNonSimpHyp (ty.getArg! 0)
  else if ty.isAppOfArity ``And 2 then
    isLightweightSimpHyp (ty.getArg! 0) && isLightweightSimpHyp (ty.getArg! 1)
  else
    false

/-- Collect lightweight propositional local hypotheses suitable for `simp` rewriting,
    excluding heavy spatial/code/disjointness and non-rewrite hypotheses. -/
def getLightweightSimpHypsWithMeta : MetaM (Array (FVarId × Expr) × Array Ident × Bool) := do
  let lctx ← getLCtx
  let mut key : Array (FVarId × Expr) := #[]
  let mut ids : Array Ident := #[]
  let mut hasMVarInLCtx := false
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
      if decl.type.hasMVar then
        hasMVarInLCtx := true
      let ty ← if decl.type.hasMVar then instantiateMVars decl.type else pure decl.type
      -- `<&&>` keeps the `isProp` / list-spine checks lazy for heavy hypotheses (a `(← c)` operand
      -- of `&&` is hoisted and run before the `if`).
      if ← pure (isLightweightSimpHyp ty) <&&> isProp ty <&&>
          (not <$> hasReducibleDeepListSpine ty) then
        if (lctx.findFromUserName? decl.userName).map (·.fvarId) == some decl.fvarId then
          key := key.push (decl.fvarId, ty)
          ids := ids.push (mkIdent decl.userName)
  return (key, ids, hasMVarInLCtx)

def getLightweightSimpHyps : MetaM (Array (FVarId × Expr) × Array Ident) := do
  let (key, ids, _) ← getLightweightSimpHypsWithMeta
  return (key, ids)

/-- Cached base `(Simp.Context, Simp.SimprocsArray)` for `[wp_norm, arm64_norm]` with no local
    hypotheses, keyed by `Environment.header.mainModule`. Built at most once per module. -/
initialize wpNormBaseSimpCacheRef :
    IO.Ref (Option (Name × Simp.Context × Simp.SimprocsArray)) ← IO.mkRef none

/-- Obtain or refresh the `WpNormSimpCache` for the current goal context. -/
def getOrInitWpNormSimpCache (preserveOnExtend : Bool := true) : TacticM WpNormSimpCache := do
  let _ := preserveOnExtend
  let declName := (← Term.getDeclName?).getD .anonymous
  let g ← getMainGoal
  let lctx ← g.withContext getLCtx
  let lastDeclFVar? := lctx.lastDecl.map (·.fvarId)
  let numIndices := lctx.numIndices
  let cached? ← getWpNormSimpCache? declName
  if let some cached := cached? then
    if !cached.hasMVarInLCtx && cached.lastDeclFVar? == lastDeclFVar? && cached.numIndices == numIndices then
      return cached
  let (hypsKey, hypIds, hasMVarInLCtx) ← g.withContext getLightweightSimpHypsWithMeta
  if let some cached := cached? then
    if cached.hypsKey == hypsKey then
      let updated := { cached with lastDeclFVar?, numIndices, hasMVarInLCtx }
      setWpNormSimpCache updated
      return updated
  let (ctx, simprocs) ←
    if hypIds.isEmpty then
      let envKey := (← getEnv).header.mainModule
      match ← wpNormBaseSimpCacheRef.get with
      | some (k, baseCtx, baseSimprocs) =>
        if k == envKey then
          pure (baseCtx, baseSimprocs)
        else
          let simpStx ← `(tactic| simp (config := { decide := true }) only [wp_norm, arm64_norm])
          let { ctx, simprocs, .. } ← mkSimpContext simpStx (eraseLocal := false)
          wpNormBaseSimpCacheRef.set (some (envKey, ctx, simprocs))
          pure (ctx, simprocs)
      | none =>
        let simpStx ← `(tactic| simp (config := { decide := true }) only [wp_norm, arm64_norm])
        let { ctx, simprocs, .. } ← mkSimpContext simpStx (eraseLocal := false)
        wpNormBaseSimpCacheRef.set (some (envKey, ctx, simprocs))
        pure (ctx, simprocs)
    else
      let simpStx ← `(tactic| simp (config := { decide := true }) only [wp_norm, arm64_norm, $[$hypIds:ident],*])
      let { ctx, simprocs, .. } ← mkSimpContext simpStx (eraseLocal := false)
      pure (ctx, simprocs)
  let entry : WpNormSimpCache := {
    declName
    lastDeclFVar?
    numIndices
    hasMVarInLCtx
    hypsKey
    ctx
    simprocs
    simpState := {}
  }
  setWpNormSimpCache entry
  return entry

end

@[expose] public section

theorem SepWP.congr_state {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {oom : Arm64.State → SepProp}
    (hs : s = s') (h : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  hs ▸ h

end

public meta section

/-- Normalize the LHS of an equality goal using `wp_norm` and `arm64_norm` rules,
    closing the goal by `rfl` if LHS and RHS become definitionally equal. -/
elab "wp_norm_lhs" : tactic => do
  let g ← getMainGoal
  let remedy := "isolate the equality subgoal (`wp_focus` / `have h : ... := by ...`) or compact a deep `State` update spine first with `wp_compact`"
  withWpHeartbeatDiag "wp_norm_lhs" "LHS `wp_norm` / `arm64_norm` normalization" remedy (gOpt? := some g) do
    let closedFast ← g.withContext do
      if ← tryCloseRunningStatus g then
        return true
      let target ← instantiateMVars (← g.getType)
      let isPcEq := match target.eq? with
        | some (_, lhs, _) => lhs.isAppOfArity ``State.pc 1
        | none => false
      if !target.hasMVar || isPcEq then
        for decl in (← getLCtx) do
          if !decl.isImplementationDetail && !decl.isAuxDecl then
            let ty ← instantiateMVars decl.type
            if ← withReducible (isDefEq ty target) then
              g.assign decl.toExpr
              return true
      if let some (_, lhs, rhs) := target.eq? then
        if (lhs.isAppOfArity ``State.mem 1 || rhs.isAppOfArity ``State.mem 1) && !rhs.hasMVar then
          if let some prf ← proveMemEqExpr? lhs rhs then
            g.assign prf
            return true
        if lhs.isAppOfArity ``State.pc 1 then
          if let some (pc, prf) ← provePcEq? (lhs.getArg! 0) then
            if ← isDefEq rhs pc then
              g.assign prf
              return true
        if let some prf ← proveCheckAddrSPAligned? target lhs rhs then
          g.assign prf
          return true
        if let some prf ← proveStateSpAligned? target lhs rhs then
          g.assign prf
          return true
        if let some prf ← proveApplyWritebackNoneSetPC? lhs rhs then
          g.assign prf
          return true
        if !rhs.hasMVar then
          if lhs == rhs ||
             (rhs.isConstOf ``Bool.true &&
              (lhs.find? (fun e => e.isConstOf ``Reg.sp || e.isConstOf ``Reg.fromSPBits)).isNone) then
            if ← isDefEq lhs rhs then
              g.assign (← mkEqRefl lhs)
              return true
        if (lhs.isAppOfArity ``HAdd.hAdd 6 || lhs.isAppOfArity ``HSub.hSub 6) &&
           (lhs.find? (fun e => e.isConstOf ``State.readReg64 || e.isConstOf ``State.readReg || e.isConstOf ``State.readReg32)).isNone then
          if let some (normExpr, prf) ← SepSolver.foldBV64OffsetTop? lhs then
            if ← isDefEq rhs normExpr then
              g.assign prf
              return true
      return false
    if closedFast then
      replaceMainGoal []
      return
    let closedByCachedSimp ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      let some (_, lhs, rhs) := target.eq? | return false
      let hasIte := (lhs.find? (·.isConstOf ``ite)).isSome
      let cached ← getOrInitWpNormSimpCache (preserveOnExtend := !hasIte)
      let initState : Simp.State := { cached.simpState with numSteps := 0 }
      let (res, simpState') ← Lean.Meta.simpCore lhs cached.ctx cached.simprocs none initState
      let seededCache := seedNormalizedInSimpCache res.expr simpState'.cache
      setWpNormSimpCache { cached with simpState := { simpState' with cache := seededCache } }
      let lhs' := res.expr
      let fastOrCappedDefEq (x y : Expr) : TacticM Bool := do
        if ← withReducible (isDefEq x y) then return true
        tryCatchRuntimeEx (withHeartbeatCap 5000 (isDefEq x y)) (fun _ => pure false)
      if rhs.hasMVar then
        if lhs'.getAppFn == rhs.getAppFn && lhs'.getAppNumArgs == rhs.getAppNumArgs then
          for a in lhs'.getAppArgs, b in rhs.getAppArgs do
            let _ ← fastOrCappedDefEq a b
        else if let (.proj s1 i1 a, .proj s2 i2 b) := (lhs', rhs) then
          if s1 == s2 && i1 == i2 then
            let _ ← fastOrCappedDefEq a b
      if ← fastOrCappedDefEq rhs lhs' then
        match res.proof? with
        | some prf => g.assign prf
        | none =>
          let eqTy ← mkEq lhs lhs'
          g.assign (mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl lhs'))
        return true
      if !rhs.hasMVar then
        let target' ← mkEq lhs' rhs
        for decl in (← getLCtx) do
          if !decl.isImplementationDetail && !decl.isAuxDecl then
            let ty ← instantiateMVars decl.type
            if ← withReducible (isDefEq ty target') then
              let prf ← match res.proof? with
                | some p => mkEqTrans p decl.toExpr
                | none => pure decl.toExpr
              g.assign prf
              return true
      return false
    if closedByCachedSimp then
      replaceMainGoal []
      return
    -- Slow path: re-gather the current local hypotheses and run `simp` with `decide := true` on
    -- the left-hand side, then close by `rfl` / `assumption` (reducible first, then a capped
    -- default-transparency attempt).
    let (_, hypIds) ← g.withContext getLightweightSimpHyps
    let hbRef ← IO.mkRef (none : Option String)
    let _ ← tryTacticTrackHeartbeatBool hbRef "LHS `wp_norm` / `arm64_norm` simplification"
      (evalTactic (← `(tactic| (
        conv =>
          lhs
          simp (config := { decide := true }) only [wp_norm, arm64_norm, $[$hypIds:ident],*]
      ))))
      (rethrowNonHb := true)
    if let some phase ← hbRef.get then
      throwHeartbeatPhaseError "wp_norm_lhs" phase remedy (some g)
    if !(← getGoals).isEmpty then
      let g' ← getMainGoal
      g'.withContext do
        let ty ← instantiateMVars (← g'.getType)
        if let some (_, lhs, rhs) := ty.eq? then
          if rhs.hasMVar then
            if lhs.getAppFn == rhs.getAppFn && lhs.getAppNumArgs == rhs.getAppNumArgs then
              for a in lhs.getAppArgs, b in rhs.getAppArgs do
                let _ ← tryCatchRuntimeEx (withHeartbeatCap 5000 (isDefEq a b)) (fun _ => pure false)
            else if let (.proj s1 i1 a, .proj s2 i2 b) := (lhs, rhs) then
              if s1 == s2 && i1 == i2 then
                let _ ← tryCatchRuntimeEx (withHeartbeatCap 5000 (isDefEq a b)) (fun _ => pure false)
      evalTactic (← `(tactic|
        first
          | with_reducible rfl
          | with_reducible assumption
          | (set_option maxHeartbeats 5000 in first | rfl | assumption)))

/-- Normalize the main goal using `wp_norm` and `arm64_norm` rules plus lightweight local hypotheses. -/
elab "wp_norm_goal" : tactic => do
  let g ← getMainGoal
  withWpHeartbeatDiag "wp_norm_goal" "goal `wp_norm` / `arm64_norm` simplification"
    "simplify only the precondition with `wp_simp_pre only [...]` or state with `wp_norm_state`, or compact a deep state first with `wp_compact`"
    (gOpt? := some g) do
    let cached ← getOrInitWpNormSimpCache
    let goalCtx ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      if ← hasGroundGuardedTableProp target then
        cached.ctx.setConfig { cached.ctx.config with decide := false }
      else
        pure cached.ctx
    let (res?, _) ← g.withContext (simpGoal g goalCtx cached.simprocs)
    match res? with
    | none => replaceMainGoal []
    | some (_, g') =>
      if g' == g then
        throwError "wp_norm_goal: simp made no progress"
      replaceMainGoal [g']

/-- Normalize only the state argument (`s`, argument 3) of a `SepWP prog target_pc s P post` goal,
    without traversing `prog`, `P`, or `post`. Uses `O(1)` spine rewrite lemmas when `s` is a
    store/branch update (`(s1.setMem m1).setMem m2`, `(s1.setPC pc1).setPC pc2`, etc.). -/
elab "wp_norm_state" : tactic => do
  let g ← getMainGoal
  withWpHeartbeatDiag "wp_norm_state" "state argument (`arg 3`) `wp_norm` / `arm64_norm` simplification"
    "compact a deep `State` update spine with `wp_compact` before normalizing state"
    (gOpt? := some g) do
    let handledFast ← g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      if !ty.isAppOfArity ``SepWP 6 then return false
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let s := ty.getArg! 2
      let P := ty.getArg! 3
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let isCleanSpine (st : Expr) : Bool :=
        !st.isAppOfArity ``State.setPC 2 && !st.isAppOfArity ``State.setMem 2 &&
        !st.isAppOfArity ``State.advancePC 1
      if s.isAppOfArity ``State.setMem 2 then
        let s1 := s.getArg! 0
        let m2 := s.getArg! 1
        if s1.isAppOfArity ``State.setPC 2 && isCleanSpine (s1.getArg! 0) then
          return true
        if s1.isAppOfArity ``State.setMem 2 then
          let s0 := s1.getArg! 0
          let m1 := s1.getArg! 1
          if !s0.isAppOfArity ``State.setMem 2 then
            let s' := mkApp2 (mkConst ``State.setMem) s0 m2
            let hs := mkApp3 (mkConst ``State.setMem_setMem) s0 m1 m2
            let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc s' P post oom
            let newMVar ← mkFreshExprMVar newGoalTy
            let prf := mkAppN (mkConst ``SepWP.congr_state) #[prog, targetPc, s, s', P, post, oom, hs, newMVar]
            g.assign prf
            replaceMainGoal [newMVar.mvarId!]
            return true
      if s.isAppOfArity ``State.setPC 2 then
        let s1 := s.getArg! 0
        let pc2 := s.getArg! 1
        if isCleanSpine s1 then
          return true
        if s1.isAppOfArity ``State.setPC 2 then
          let s0 := s1.getArg! 0
          let pc1 := s1.getArg! 1
          if isCleanSpine s0 then
            let s' := mkApp2 (mkConst ``State.setPC) s0 pc2
            let hs := mkApp3 (mkConst ``State.setPC_setPC) s0 pc1 pc2
            let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc s' P post oom
            let newMVar ← mkFreshExprMVar newGoalTy
            let prf := mkAppN (mkConst ``SepWP.congr_state) #[prog, targetPc, s, s', P, post, oom, hs, newMVar]
            g.assign prf
            replaceMainGoal [newMVar.mvarId!]
            return true
        if s1.isAppOfArity ``State.setMem 2 && (s1.getArg! 0).isAppOfArity ``State.setPC 2 then
          let sInner := s1.getArg! 0
          let m := s1.getArg! 1
          let s0 := sInner.getArg! 0
          let pc1 := sInner.getArg! 1
          if isCleanSpine s0 then
            let s' := mkApp2 (mkConst ``State.setMem) (mkApp2 (mkConst ``State.setPC) s0 pc2) m
            let hs := mkApp4 (mkConst ``State.setPC_setMem_setPC) s0 pc1 pc2 m
            let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc s' P post oom
            let newMVar ← mkFreshExprMVar newGoalTy
            let prf := mkAppN (mkConst ``SepWP.congr_state) #[prog, targetPc, s, s', P, post, oom, hs, newMVar]
            g.assign prf
            replaceMainGoal [newMVar.mvarId!]
            return true
      return false
    if handledFast then return
    evalTactic (← `(tactic| (
      conv =>
        arg 3
        simp only [wp_norm, arm64_norm]
    )))

register_option proofLib.dsimpAtStarMemo : Bool := {
  defValue := true
  descr := "in `wp_unfold_specs`, skip the hypotheses and the goal that an earlier \
    `dsimp only [...] at *` pass with the same lemma list left unchanged in the current declaration"
}

initialize registerTraceClass `proofLib.dsimpMemo

/-- Per-declaration memo of the `(pass, type)` pairs that a `dsimpOnlyAtStarMemo` pass left
    unchanged. -/
structure DsimpNormMemo where
  declName : Name
  seen : Std.HashSet (UInt64 × Expr) := {}

/-- Per-declaration `IO.Ref` backing `DsimpNormMemo` (see `wpNormSimpCacheRefExt`); updates survive
    `saveState`/`restore` rollback. -/
initialize dsimpNormMemoRefExt : EnvExtension (Option (IO.Ref (Option DsimpNormMemo))) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Obtain (or lazily allocate) the `IO.Ref` backing `DsimpNormMemo`. -/
def getDsimpNormMemoRef : CoreM (IO.Ref (Option DsimpNormMemo)) := do
  if let some ref := dsimpNormMemoRefExt.getState (← getEnv) then
    return ref
  let ref ← IO.mkRef none
  modify fun s => { s with env := dsimpNormMemoRefExt.setState s.env (some ref) }
  return ref

/-- `dsimp only [...] at *` (`stx`, a `dsimp` tactic) that skips every hypothesis type and goal that
    an earlier call with the same `passKey` in the current declaration left unchanged. `dsimp only`
    with a fixed lemma list is a deterministic function of the (instantiated) type and of the
    declarations of the free variables it mentions, which never change within a declaration, so
    skipping such a type is exactly what rerunning `dsimp` on it would do. Returns `false`, leaving
    the goal untouched, when nothing changed (where `dsimp` would fail with "no progress"). -/
def dsimpOnlyAtStarMemo (passKey : UInt64) (stx : Syntax) : TacticM Bool := withMainContext do
  if !proofLib.dsimpAtStarMemo.get (← getOptions) then
    return ← tryTactic (evalTactic stx)
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  let ctx ← ctx.setConfig { ctx.config with failIfUnchanged := false }
  let declName := (← Term.getDeclName?).getD .anonymous
  let ref ← getDsimpNormMemoRef
  let memo : DsimpNormMemo ← match ← ref.get with
    | some m => pure (if m.declName == declName && m.seen.size < 65536 then m else { declName })
    | none => pure { declName }
  let g ← getMainGoal
  let hyps ← g.getNondepPropHyps
  let mut todo : Array (FVarId × Expr) := #[]
  for fvarId in hyps do
    let ty ← instantiateMVars (← fvarId.getType)
    unless memo.seen.contains (passKey, ty) do
      todo := todo.push (fvarId, ty)
  let tgt ← instantiateMVars (← g.getType)
  let doTgt := !memo.seen.contains (passKey, tgt)
  trace[proofLib.dsimpMemo] "pass {passKey}: {todo.size}/{hyps.size} hyps, target {doTgt}"
  if todo.isEmpty && !doTgt then
    return false
  let (r?, _) ← dsimpGoal g ctx simprocs (simplifyTarget := doTgt) (fvarIdsToSimp := todo.map (·.1))
  let some g' := r? | replaceMainGoal []; return true
  let mut seen := memo.seen
  let lctx' := (← g'.getDecl).lctx
  for (fvarId, ty) in todo do
    if let some d := lctx'.find? fvarId then
      if (← instantiateMVars d.type) == ty then
        seen := seen.insert (passKey, ty)
  if doTgt && (← instantiateMVars (← g'.getType)) == tgt then
    seen := seen.insert (passKey, tgt)
  ref.set (some { memo with seen })
  if g' == g then
    return false
  replaceMainGoal [g']
  return true

/-- Unfold `Arm64.Spec` constants (including parameterized `Spec` functions and combinators)
    appearing in the goal or local context. -/
elab "wp_unfold_specs" : tactic => do
  for _ in [:3] do
    if (← getUnsolvedGoals).isEmpty then return
    let mvarId ← getMainGoal
    let ref ← IO.mkRef #[]
    mvarId.withContext do
      let collectFromExpr (e : Expr) : MetaM Unit := do
        e.forEach fun sub => do
          if sub.isConst then
            let nm := sub.constName!
            if nm != ``Arm64.Spec.mk then
              let ty ← inferType sub
              if ty.getForallBody.isAppOf ``Arm64.Spec then
                let arr ← ref.get
                if !arr.any (fun i => i.getId == nm) then
                  ref.set (arr.push (mkIdent nm))
      collectFromExpr (← instantiateMVars (← mvarId.getType))
      for decl in (← getLCtx) do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          collectFromExpr (← instantiateMVars decl.type)
    let ids ← ref.get
    if ids.isEmpty then break
    for id in ids do
      if (← getUnsolvedGoals).isEmpty then return
      let _ ← tryTactic (discard <| dsimpOnlyAtStarMemo (mixHash 0x5350 (hash id.getId))
        (← `(tactic| dsimp only [$id:ident, wp_proj_guard] at *)))
  if (← getUnsolvedGoals).isEmpty then return
  let _ ← tryTactic (discard <| dsimpOnlyAtStarMemo 0x5342 (← `(tactic|
    dsimp only [ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, Spec.inImage,
      Spec.allowPanicWhen, Spec.allowOomWhen, Spec.allowOom, wp_proj_guard] at *)))
  if (← getUnsolvedGoals).isEmpty then return
  let _ ← tryTactic (discard <| dsimpOnlyAtStarMemo 0x5047
    (← `(tactic| dsimp only [wp_proj_guard] at *)))

/-- Generate a fresh accessible identifier in the current local context. -/
def freshIdent (base : Name) : TacticM Ident := do
  let mvarId ← getMainGoal
  let lctx ← mvarId.withContext getLCtx
  Pure.pure (mkIdent (lctx.getUnusedName base))

/-- Normalize a single hypothesis `hId` and recursively split any `And` conjuncts (both left- and
    right-nested) into fresh accessible hypotheses. -/
def wpNormAndSplitHyp (hId : Ident) : TacticM Unit := do
  if (← getUnsolvedGoals).isEmpty then return
  evalTactic (← `(tactic| wp_unfold_specs))
  if (← getUnsolvedGoals).isEmpty then return
  let _ ← tryTactic (evalTactic (← `(tactic| dsimp only [wp_proj_guard] at $hId:ident)))
  if (← getUnsolvedGoals).isEmpty then return
  let hasTable ← do
    let mvarId ← getMainGoal
    mvarId.withContext do
      match (← getLCtx).findFromUserName? hId.getId with
      | some decl => hasGroundGuardedTableProp (← instantiateMVars decl.type)
      | none => return false
  if hasTable then
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := false }) only [
        ← disjointRegions_iff_disjoint64,
        ← disjointRegions_iff_disjoint128,
        Arm64.CalleeSavedPreserved,
        wp_norm, arm64_norm, wp_proj_guard] at $hId:ident)))
  else
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [
        ← disjointRegions_iff_disjoint64,
        ← disjointRegions_iff_disjoint128,
        Arm64.CalleeSavedPreserved,
        wp_norm, arm64_norm, wp_proj_guard] at $hId:ident)))
  if (← getUnsolvedGoals).isEmpty then return
  let mut worklist : List Ident := [hId]
  let mut leafIds : Array Ident := #[]
  while !worklist.isEmpty do
    if (← getUnsolvedGoals).isEmpty then break
    let currId :: rest := worklist | break
    worklist := rest
    let mvarId ← getMainGoal
    let lctx ← mvarId.withContext getLCtx
    if let some decl := lctx.findFromUserName? currId.getId then
      let ty ← mvarId.withContext (instantiateMVars decl.type)
      if ty.isAppOfArity ``And 2 then
        let rhs := (ty.getArg! 1).consumeMData
        let isVRegsRhs := match rhs.eq? with
          | some (_, lhs, _) => lhs.consumeMData.getAppFn.isConstOf ``Arm64.calleeSavedVRegs
          | none => false
        if isVRegsRhs then
          let hvId ← freshIdent `hvregs
          if ← tryTactic (evalTactic (← `(tactic| rcases $currId:ident with ⟨$currId:ident, $hvId:ident⟩))) then
            worklist := currId :: hvId :: worklist
          else
            leafIds := leafIds.push currId
        else
          let h1 ← freshIdent `h
          if ← tryTactic (evalTactic (← `(tactic| rcases $currId:ident with ⟨$h1:ident, $currId:ident⟩))) then
            worklist := h1 :: currId :: worklist
          else
            leafIds := leafIds.push currId
      else
        leafIds := leafIds.push currId
  if hasTable && leafIds.size > 1 then
    for leafId in leafIds do
      if (← getUnsolvedGoals).isEmpty then break
      let leafHasTable ← do
        let mvarId ← getMainGoal
        mvarId.withContext do
          match (← getLCtx).findFromUserName? leafId.getId with
          | some decl => hasGroundGuardedTableProp (← instantiateMVars decl.type)
          | none => return true
      if !leafHasTable then
        let _ ← tryTactic (evalTactic (← `(tactic|
          simp (config := { decide := true }) only [
            ← disjointRegions_iff_disjoint64,
            ← disjointRegions_iff_disjoint128,
            Arm64.CalleeSavedPreserved,
            wp_norm, arm64_norm, wp_proj_guard] at $leafId:ident)))

/-- Unpack `Prod`-typed local variables (when `unpackProds = true`), split conjunctive (`And`,
    `CodeBundle`, `FnCode.holds`, `codeAtAddr`) hypotheses using fresh accessible names, and
    normalize all local Prop hypotheses. -/
def wpSplitAndNormHyps (unpackProds : Bool := false) : TacticM Unit := do
  if unpackProds then
    let mut prodProgress := true
    while prodProgress do
      prodProgress := false
      let mvarId ← getMainGoal
      let lctx ← mvarId.withContext getLCtx
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
          let ty ← mvarId.withContext (whnf (← instantiateMVars decl.type))
          if ty.isAppOfArity ``Prod 2 then
            let id := mkIdent decl.userName
            let id1 ← freshIdent `a
            let id2 ← freshIdent `a_rest
            if ← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩))) then
              prodProgress := true
              break
          else if ty.isAppOfArity ``PUnit 0 then
            let id := mkIdent decl.userName
            if ← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨⟩))) then
              prodProgress := true
              break
  evalTactic (← `(tactic| wp_unfold_specs))
  if (← getUnsolvedGoals).isEmpty then return
  let mut progress := true
  while progress do
    progress := false
    let mvarId ← getMainGoal
    let lctx ← mvarId.withContext getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
        let ty ← mvarId.withContext (instantiateMVars decl.type)
        if ty.isAppOfArity ``And 2 then
          let id := mkIdent decl.userName
          let rhs := (ty.getArg! 1).consumeMData
          let isVRegsRhs := match rhs.eq? with
            | some (_, lhs, _) => lhs.consumeMData.getAppFn.isConstOf ``Arm64.calleeSavedVRegs
            | none => false
          if isVRegsRhs then
            let hvId ← freshIdent `hvregs
            if ← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$id:ident, $hvId:ident⟩))) then
              progress := true
              break
          else
            let h1 ← freshIdent `h
            if ← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$h1:ident, $id:ident⟩))) then
              progress := true
              break
        else if !ty.isAppOf ``Arm64.DisjointRegions &&
                !ty.isAppOf ``Arm64.Memory.Disjoint64 &&
                !ty.isAppOf ``Arm64.Memory.Disjoint128 &&
                !ty.isAppOf ``Arm64.CalleeSavedPreserved then
          if let some andTy ← mvarId.withContext (unfoldToAndIfPossible? ty) then
            let g' ← mvarId.changeLocalDecl decl.fvarId andTy
            replaceMainGoal [g']
            let id := mkIdent decl.userName
            let h1 ← freshIdent `h
            if ← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$h1:ident, $id:ident⟩))) then
              progress := true
              break
  let mvarId0 ← getMainGoal
  let lctx0 ← mvarId0.withContext getLCtx
  let mut hypNames : Array Name := #[]
  for decl in lctx0 do
    if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
      let ty ← mvarId0.withContext (instantiateMVars decl.type)
      if ← mvarId0.withContext (Meta.isProp ty) then
        let isFetchOrExternEq := match ty.eq? with
          | some (_, lhs, _) => lhs.isAppOf ``Program.externAt? || lhs.isAppOf ``Program.fetch
          | none => false
        if !isFetchOrExternEq &&
           !ty.isAppOfArity ``Program.hasCode 3 &&
           !ty.isAppOfArity ``Program.hasWords 3 &&
           !ty.isAppOfArity ``Program.codeAt 3 &&
           !ty.isAppOf ``Arm64.subroutine_ok &&
           !ty.isAppOf ``Program.subroutineOk then
          hypNames := hypNames.push decl.userName
  if !hypNames.isEmpty then
    let simpStx ← `(tactic|
      simp (config := { decide := true }) only [
        ← disjointRegions_iff_disjoint64,
        ← disjointRegions_iff_disjoint128,
        Arm64.CalleeSavedPreserved,
        wp_norm, arm64_norm, wp_proj_guard])
    let { ctx, simprocs, .. } ← mkSimpContext simpStx (eraseLocal := false)
    let ctxNoDecide ← ctx.setConfig { ctx.config with decide := false }
    for nm in hypNames do
      -- A previous hypothesis may have simplified to `False`, closing the goal.
      if (← getUnsolvedGoals).isEmpty then
        return
      let g ← getMainGoal
      let declInfo? ← g.withContext do
        match (← getLCtx).findFromUserName? nm with
        | some decl =>
          let ty ← instantiateMVars decl.type
          pure (some (decl.fvarId, ← hasGroundGuardedTableProp ty))
        | none => pure none
      if let some (fvarId, hasTable) := declInfo? then
        let hypCtx := if hasTable then ctxNoDecide else ctx
        let _ ← tryTactic do
          let (res?, _) ← g.withContext
            (simpGoal g hypCtx simprocs (simplifyTarget := false) (fvarIdsToSimp := #[fvarId]))
          match res? with
          | none => replaceMainGoal []
          | some (_, g') => replaceMainGoal [g']
    if (← getUnsolvedGoals).isEmpty then
      return
  let mut progress2 := true
  while progress2 do
    progress2 := false
    let mvarId ← getMainGoal
    let lctx ← mvarId.withContext getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
        let ty ← mvarId.withContext (instantiateMVars decl.type)
        if ty.isAppOfArity ``And 2 then
          let id := mkIdent decl.userName
          let h1 ← freshIdent `h
          if ← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$h1:ident, $id:ident⟩))) then
            progress2 := true
            break
        else if ty.isAppOfArity ``Exists 2 &&
                (ty.find? (·.isConstOf ``SepProp.Satisfies)).isSome then
          let id := mkIdent decl.userName
          let vId ← freshIdent `v_stk
          if ← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$vId:ident, $id:ident⟩))) then
            progress2 := true
            break

/-- If `progExpr` is an application of a defined wrapper constant whose body reduces to an
    application of `Arm64.Program.rebase` (such as a `declare_rebased_program` or user `def`
    wrapper), beta-reduce its definition body once so symbol/stub/fetch inspection sees
    `Program.rebase rawProg base hooks` without unfolding `rawProg`. -/
def unwrapRebasedProgExpr (progExpr : Expr) : MetaM Expr := do
  let progExpr ← instantiateMVars progExpr
  let fn := progExpr.getAppFn
  if fn.isConst then
    let nm := fn.constName!
    if nm != ``Arm64.Program.mk && nm != ``Arm64.Program.rebase &&
       nm != ``Arm64.Program.ofImage && nm != ``Arm64.Program.ofWords &&
       nm != ``Arm64.Obj.LinkedImage.toProgram then
      if let some info := (← getEnv).find? nm then
        if let some val := info.value? then
          let applied := val.beta progExpr.getAppArgs
          if applied.getAppFn.isConstOf ``Arm64.Program.rebase then
            return applied
  return progExpr

/-- Unfold `@[wp_unfold]` definitions and any `Program.rebase` wrapper abbreviations appearing as
    the program argument in the goal or local context so `wp_init` / `wp_start` / `wpp_init` never
    require a manual `unfold <ProgAbbr>` beforehand. -/
def wpUnfoldProgAbbrs : TacticM Unit := do
  let _ ← tryTactic (evalTactic (← `(tactic| simp only [wp_unfold, wp_proj_guard] at *)))
  if (← getUnsolvedGoals).isEmpty then return
  let g ← getMainGoal
  let names ← g.withContext do
    let env ← getEnv
    let ref ← IO.mkRef (#[] : Array Name)
    let visit (e : Expr) : MetaM Unit := do
      e.forEach fun sub => do
        if sub.isConst then
          let nm := sub.constName!
          if nm != ``Arm64.Program.mk && nm != ``Arm64.Program.rebase &&
             nm != ``Arm64.Program.ofImage && nm != ``Arm64.Program.ofWords &&
             nm != ``Arm64.Obj.LinkedImage.toProgram then
            if !(← isReducible nm) then
              if let some info := env.find? nm then
                if let some val := info.value? then
                  let body := val.getLambdaBody
                  if body.getAppFn.isConstOf ``Arm64.Program.rebase then
                    let cur ← ref.get
                    if !cur.contains nm then
                      ref.set (cur.push nm)
    visit (← instantiateMVars (← g.getType))
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        visit (← instantiateMVars decl.type)
    ref.get
  for nm in names do
    let id := mkIdent nm
    let _ ← tryTactic (evalTactic (← `(tactic| delta $id:ident at *)))

/-- Initialize a `subroutine_ok` proof using `SepWP`:
    supports `wp_init`, `wp_init a s0`, `wp_init P_init`, and `wp_init a s0 P_init`. -/
syntax "wp_init" (atomic(ppSpace colGt ident ppSpace colGt ident))? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| wp_init $[$a?:ident $s0?:ident]? $[$P_init?:term]?) => do
    wpUnfoldProgAbbrs
    let aId ← match a? with
      | some id => Pure.pure id
      | none => freshIdent `a
    let rId ← freshIdent `R
    let s0Id ← match s0? with
      | some id => Pure.pure id
      | none => freshIdent `s0
    let hpcId ← freshIdent `hpc
    let hrunId ← freshIdent `hrun
    let hpreId ← freshIdent `hpre
    let hspId ← freshIdent `hsp_align
    let _ ← tryTactic (evalTactic (← `(tactic|
      dsimp only [Program.relocSubroutineOk, Program.alignedSubroutineOk,
        Obj.LinkedImage.subroutineOk, Program.subroutineOk, fn_subroutine_ok,
        ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, wp_proj_guard])))
    if P_init?.isNone then
      evalTactic (← `(tactic| (
        wp_unfold_specs
        apply subroutine_ok_of_sepWP_init
        intro $aId:ident $rId:ident $s0Id:ident $hpcId:ident $hrunId:ident $hpreId:ident $hspId:ident
        try simp only [stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def, wp_proj_guard] at $hpreId:ident
      )))
    else
      evalTactic (← `(tactic| (
        wp_unfold_specs
        apply subroutine_ok_of_sepWP
        intro $aId:ident $rId:ident $s0Id:ident $hpcId:ident $hrunId:ident $hpreId:ident $hspId:ident
        try simp only [stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def, wp_proj_guard] at $hpreId:ident
      )))
    wpSplitAndNormHyps (unpackProds := a?.isNone)
    let g ← getMainGoal
    let (pInitExpr, frameInitExpr) ← g.withContext do
      let lctx ← getLCtx
      let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
      let mut fullPreOpt : Option Expr := none
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          let ty ← instantiateMVars decl.type
          if ty.isAppOfArity ``SepProp.Satisfies 2 then
            fullPreOpt := some (ty.getArg! 0)
            break
      let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
      let buildRightConj (arr : Array Expr) : Expr :=
        if arr.isEmpty then
          mkConst ``SepProp.emp
        else
          let n := arr.size
          (List.range (n - 1)).foldr
            (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) arr[i]! acc)
            arr[n - 1]!
      let defaultPair : Expr × Expr :=
        let atoms := SepSolver.atoms fullPre
        let spatial := atoms.filter (fun (a : Expr) => rFVar != some a)
        (buildRightConj spatial, rFVar.getD (mkConst ``SepProp.emp))
      match P_init? with
      | none => Pure.pure defaultPair
      | some pStx =>
        let pElab ← elabTerm pStx (some (mkConst ``Arm64.SepProp))
        let pElab ← instantiateMVars pElab
        let mentionsStackFrame :=
          (pElab.find? fun e =>
            e.isConstOf ``Arm64.stackFrame16 ||
            e.isConstOf ``Arm64.stackFrame16At ||
            e.isConstOf ``Arm64.stackFrame32 ||
            e.isConstOf ``Arm64.stackFrame32At).isSome
        if mentionsStackFrame then
          Pure.pure defaultPair
        else if let some (fExpr, _) ← SepSolver.frameSplit? pElab fullPre then
          let fAtoms := SepSolver.atoms fExpr
          Pure.pure (pElab, buildRightConj fAtoms)
        else
          Pure.pure defaultPair
    let pStx ← g.withContext do Term.exprToSyntax (← instantiateMVars pInitExpr)
    let fStx ← g.withContext do Term.exprToSyntax (← instantiateMVars frameInitExpr)
    if P_init?.isNone then
      evalTactic (← `(tactic| (
        refine ⟨$pStx, ?_, ?_⟩
        wp_focus_close arm64_sep_close
      )))
    else
      evalTactic (← `(tactic| (
        refine ⟨$pStx, $fStx, ?_, ?_⟩
        wp_focus_close arm64_sep_close
      )))
    (← getGoals).forM instantiateMVarDeclMVars

/-- Initialize a `subroutine_ok prog entry (Spec.split ...)` proof using `SepWP`:
    supports both `wp_start` and `wp_start a s0`. -/
syntax "wp_start" (atomic(ppSpace colGt ident ppSpace colGt ident))? : tactic
elab_rules : tactic
  | `(tactic| wp_start $[$a?:ident $s0?:ident]?) => do
    wpUnfoldProgAbbrs
    let aId ← match a? with
      | some id => Pure.pure id
      | none => freshIdent `a
    let s0Id ← match s0? with
      | some id => Pure.pure id
      | none => freshIdent `s0
    let hpcId ← freshIdent `hpc
    let hrunId ← freshIdent `hrun
    let hpreId ← freshIdent `hpre
    let hspId ← freshIdent `hsp_align
    evalTactic (← `(tactic| (
      apply Spec.split_of_sepWP
      intro $aId:ident $s0Id:ident $hpcId:ident $hrunId:ident $hpreId:ident $hspId:ident
    )))
    wpSplitAndNormHyps (unpackProds := a?.isNone)

private def isCanonicalSetPCArg (pcArg : Expr) : Bool :=
  if (evalBitVecLitPure? pcArg).isSome then true
  else if pcArg.isAppOfArity ``ite 5 then true
  else if pcArg.isAppOfArity ``State.readReg64 2 && (pcArg.getArg! 0).isFVar then true
  else if pcArg.isAppOfArity ``HAdd.hAdd 6 then
    let base := pcArg.getArg! 4
    let rhs := pcArg.getArg! 5
    (evalBitVecLitPure? rhs).isSome &&
    !base.isAppOfArity ``HAdd.hAdd 6 &&
    !(base.find? (fun e => e.isConstOf ``State.pc || e.isConstOf ``Program.fnAddr)).isSome
  else false

/-- Extract the current PC expression of `s` by walking its state-update spine and consulting
    local `s0.pc = ...` hypotheses for base state FVars. -/
partial def extractSepWPPC (s : Expr) : MetaM Expr := do
  let s ← instantiateMVars s
  if s.isAppOfArity ``State.setPC 2 then
    let pcArg := s.getArg! 1
    if isCanonicalSetPCArg pcArg then
      return pcArg
  if s.isAppOfArity ``State.setMem 2 && (s.getArg! 0).isAppOfArity ``State.setPC 2 then
    let pcArg := (s.getArg! 0).getArg! 1
    if isCanonicalSetPCArg pcArg then
      return pcArg
  if let some (w, v) ← evalSpinePCLit? s then
    return toExpr (BitVec.ofNat w v)
  if let some (base, off) ← evalSpinePCBaseOff? s then
    if off == 0 then
      return base
    return ← mkAppM ``HAdd.hAdd #[base, toExpr (BitVec.ofNat 64 off)]
  if s.isAppOfArity ``State.setPC 2 then
    let pcArg := s.getArg! 1
    if let some (w, v) ← evalBitVecLit? pcArg then
      return toExpr (BitVec.ofNat w v)
    return pcArg
  if s.isAppOfArity ``State.advancePC 1 then
    let inner ← extractSepWPPC (s.getArg! 0)
    let addExpr ← mkAppM ``HAdd.hAdd #[inner, toExpr (4#64)]
    if let some (w, v) ← evalBitVecLit? addExpr then
      return toExpr (BitVec.ofNat w v)
    return addExpr
  if s.isAppOfArity ``State.writeReg64 3 ||
     s.isAppOfArity ``State.writeReg32 3 ||
     s.isAppOfArity ``State.writeReg 4 ||
     s.isAppOfArity ``State.writeVReg128 3 ||
     s.isAppOfArity ``State.writeVReg64 3 ||
     s.isAppOfArity ``State.writeVReg32 3 ||
     s.isAppOfArity ``State.setMem 2 ||
     s.isAppOfArity ``State.setPState 2 ||
     s.isAppOfArity ``State.setBrk 2 ||
     s.isAppOfArity ``State.setPhysMemAvail 2 ||
     s.isAppOfArity ``State.setFs 2 ||
     s.isAppOfArity ``State.nextOracle 1 ||
     s.isAppOfArity ``State.stepExclOracle 1 ||
     s.isAppOfArity ``State.stepExclLoop 1 ||
     s.isAppOfArity ``State.appendTrace 2 ||
     s.isAppOfArity ``State.setStatus 2 ||
     s.isAppOfArity ``State.setFpsr 2 ||
     s.isAppOfArity ``State.orFpsr 2 ||
     s.isAppOfArity ``ProofLib.setTpidrEl0 2 ||
     s.isAppOfArity ``ProofLib.applyWriteback 2 then
    return ← extractSepWPPC (s.getArg! 0)
  if s.isFVar then
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOfArity ``State.pc 1 && lhs.getArg! 0 == s then
            if let some (w, v) ← evalBitVecLit? rhs then
              return toExpr (BitVec.ofNat w v)
            return rhs
  return mkApp (mkConst ``Arm64.State.pc) s

/-- Extract `(prog, target_pc, pc)` from a `SepWP prog target_pc s P post` goal. -/
def getSepWPStateAndPC : TacticM (Expr × Expr × Expr) := do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then
      throwError m!"wp_step: goal is not a `SepWP` judgment: {ty}"
    let progExpr := ty.getArg! 0
    let targetPcExpr := ty.getArg! 1
    let sExpr := ty.getArg! 2
    let pcExpr ← extractSepWPPC sExpr
    return (progExpr, targetPcExpr, pcExpr)

/-- Extract `(prog, target_pc, pc)` from either a `SepWP prog target_pc s P post oom` (arity 6)
    or a `SepWPp prog target_pc s P Q Qp oom` (arity 7) goal. -/
def getSepWPOrWPpStateAndPC : TacticM (Expr × Expr × Expr) := do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 && !ty.isAppOfArity ``SepWPp 7 then
      throwError m!"wp_call: goal is not a `SepWP` or `SepWPp` judgment: {ty}"
    let progExpr := ty.getArg! 0
    let targetPcExpr := ty.getArg! 1
    let sExpr := ty.getArg! 2
    let pcExpr ← extractSepWPPC sExpr
    return (progExpr, targetPcExpr, pcExpr)

/-- Close a fetch subgoal `prog.fetch pc = some ?inst` using a pre-computed proof `fetchPrf?`
    or falling back to `tryCloseFetchFromHasCode` / `wp_norm_lhs`. -/
def closeFetchSubgoal (fetchPrf? : Option Expr := none) : TacticM Unit := do
  let _ ← getOrCreateWpNormSimpCacheRef
  if let some prf := fetchPrf? then
    let g :: rest ← getGoals | return
    let assigned ← g.withContext do
      if ← isDefEq (← inferType prf) (← g.getType) then
        g.assign prf
        return true
      return false
    if assigned then
      setGoals rest
      return
  if ← tryCloseFetchFromHasCode then
    return
  let ok ← tryTactic (evalTactic (← `(tactic| wp_focus_close (first | wp_assumption | wp_norm_lhs | wp_norm_goal))))
  if !ok then
    if let some g := (← getGoals).head? then
      g.withContext do
        let goalTy := (← instantiateMVars (← g.getType)).consumeMData
        let pcMsg : MessageData ←
          if let some (_, lhs, _) := goalTy.eq? then
            let lhsCons := lhs.consumeMData
            if lhsCons.isAppOfArity ``Program.fetch 2 then
              let rawPc := lhsCons.getArg! 1
              let pcDisp ←
                if rawPc.consumeMData.isAppOfArity ``State.pc 1 then
                  try extractSepWPPC (rawPc.consumeMData.getArg! 0) catch _ => pure rawPc
                else
                  pure rawPc
              pure m!" at target PC `{pcDisp}` (subgoal: `{goalTy}`)"
            else
              pure m!" (subgoal: `{goalTy}`)"
          else
            pure m!" (subgoal: `{goalTy}`)"
        throwError "wp_step: failed to close instruction fetch subgoal{pcMsg}\nhint: check for a missing code-shard / `codeAt` / `hasWords` / `reloc` (`CodeRelocInRange` / `Lo12Aligned` / `BranchInRange`) hypothesis covering this PC, or simplify an unreduced `base + offset` PC term (`simp only [wp_norm, arm64_norm, addr_norm]`)"
    throwError "wp_step: failed to close instruction fetch subgoal\nhint: check for a missing code-shard / `codeAt` / `hasWords` / `reloc` hypothesis covering the target PC, or simplify an unreduced `base + offset` PC term"

private partial def isFVarProjChain (env : Environment) (e : Expr) : Bool :=
  match e with
  | .fvar _ => true
  | .proj _ _ b => isFVarProjChain env b
  | .mdata _ b => isFVarProjChain env b
  | _ =>
    if let .const declName _ := e.getAppFn then
      if let some info := env.getProjectionFnInfo? declName then
        if !info.fromClass && e.getAppNumArgs == info.numParams + 1 then
          isFVarProjChain env (e.getArg! info.numParams)
        else
          false
      else
        false
    else
      false

private partial def collectAtomicValueTerms (env : Environment) (e : Expr) : Array Expr :=
  let rec visit (t : Expr) (acc : Array Expr) : Array Expr :=
    let t := t.consumeMData
    if t.isAppOfArity ``State.readReg64 2 ||
       t.isAppOfArity ``State.readReg32 2 ||
       t.isAppOfArity ``State.readReg 3 ||
       t.isAppOfArity ``State.sp 1 ||
       isFVarProjChain env t then
      if acc.contains t then acc else acc.push t
    else
      match t with
      | .app f a => visit a (visit f acc)
      | .lam _ d b _ | .forallE _ d b _ => visit b (visit d acc)
      | .letE _ d v b _ => visit b (visit v (visit d acc))
      | .proj _ _ b => visit b acc
      | _ => acc
  visit e #[]

private def isBaseStateRegRead (e : Expr) : Bool :=
  let e := e.consumeMData
  (e.isAppOfArity ``State.readReg64 2 ||
   e.isAppOfArity ``State.readReg32 2 ||
   e.isAppOfArity ``State.readReg 3 ||
   e.isAppOfArity ``State.sp 1) &&
  (e.getArg! 0).consumeMData.isFVar

/-- Analyze whether `c`'s atomic symbolic terms (`a.field`, `s0.readReg64 r`, or scalar FVar)
    are constrained by non-heavy propositional hypotheses in `LCtx` (ignoring unconstrained
    initial-register definitions `s0.readReg64 r = val`).
    Returns `(anyConstrained, allConstrained, anyEqOrArithConstrained)`. -/
def analyzeConstrainedFVars (c : Expr) : TacticM (Bool × Bool × Bool) := do
  let g ← getMainGoal
  g.withContext do
    let env ← getEnv
    let cAtoms := collectAtomicValueTerms env c
    if cAtoms.isEmpty then return (true, true, true)
    let mut hypTys : Array (Expr × Array Expr) := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.isLet then
        let ty ← instantiateMVars decl.type
        if (← Meta.isProp ty) && !isHeavyHypType ty then
          hypTys := hypTys.push (ty, collectAtomicValueTerms env ty)
    let mut constrainedAtoms : Array Expr := #[]
    let mut eqOrArithAtoms : Array Expr := #[]
    for idx in [:hypTys.size] do
      let (ty, atoms) := hypTys[idx]!
      -- An equation `s0.readReg64 r = rhs` where `s0.readReg64 r` appears nowhere else in `c` or `LCtx`
      -- merely binds an unconstrained initial register and places no constraint on `rhs`.
      let isUnconstrainedRegDef : Bool :=
        match ty.eq? with
        | some (_, lhs, rhs) =>
          if isBaseStateRegRead lhs && !cAtoms.contains lhs then
            let rhsAtoms := collectAtomicValueTerms env rhs
            !rhsAtoms.contains lhs &&
            !(List.range hypTys.size).any (fun j => j != idx && hypTys[j]!.2.contains lhs)
          else
            false
        | none => false
      if !isUnconstrainedRegDef then
        let isPureRelIneq : Bool :=
          let body := if ty.isAppOfArity ``Not 1 then ty.getArg! 0 else ty
          match body.eq? with
          | some (_, lhs, rhs) =>
            (rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false) &&
            (lhs.isAppOfArity ``BitVec.ule 3 || lhs.isAppOfArity ``BitVec.ult 3 ||
             lhs.isAppOfArity ``BitVec.sle 3 || lhs.isAppOfArity ``BitVec.slt 3)
          | none => false
        for a in cAtoms do
          if atoms.contains a then
            if !constrainedAtoms.contains a then
              constrainedAtoms := constrainedAtoms.push a
            if !isPureRelIneq && !eqOrArithAtoms.contains a then
              eqOrArithAtoms := eqOrArithAtoms.push a
    let anyConstrained := !constrainedAtoms.isEmpty
    let allConstrained := cAtoms.all (fun a => constrainedAtoms.contains a)
    let anyEqOrArith := !eqOrArithAtoms.isEmpty
    return (anyConstrained, allConstrained, anyEqOrArith)

def hasConstrainedFVar (c : Expr) : TacticM Bool := do
  let (anyConstrained, _, _) ← analyzeConstrainedFVars c
  return anyConstrained

/-- Check whether `c` is a direct binary comparison between two distinct atomic terms (or an atomic
    term and a non-boundary literal) that cannot be a tautology or contradiction without hypotheses. -/
def isObviouslyUnresolvedCmp (env : Environment) (c : Expr) : Bool :=
  let isAtom (e : Expr) : Bool := isFVarProjChain env e || isBaseStateRegRead e
  let isNonBoundaryLit64 (e : Expr) : Bool :=
    match evalBitVecLitPure? e with
    | some (64, v) => v > 0 && v < (1 <<< 63) - 1
    | _ => false
  let isAnyLit (e : Expr) : Bool := (evalBitVecLitPure? e).isSome
  match c.eq? with
  | some (_, lhs, rhs) =>
    if rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false then
      if lhs.isAppOfArity ``BEq.beq 4 || lhs.isAppOfArity ``bne 4 then
        let x := lhs.getArg! 2
        let y := lhs.getArg! 3
        x != y && ((isAtom x && (isAtom y || isAnyLit y)) || (isAnyLit x && isAtom y))
      else if lhs.isAppOfArity ``BitVec.ule 3 || lhs.isAppOfArity ``BitVec.ult 3 ||
              lhs.isAppOfArity ``BitVec.sle 3 || lhs.isAppOfArity ``BitVec.slt 3 then
        let x := lhs.getArg! 1
        let y := lhs.getArg! 2
        x != y && ((isAtom x && (isAtom y || isNonBoundaryLit64 y)) || (isNonBoundaryLit64 x && isAtom y))
      else
        false
    else
      lhs != rhs && ((isAtom lhs && (isAtom rhs || isAnyLit rhs)) || (isAnyLit lhs && isAtom rhs))
  | none => false

/-- Heartbeat budget (thousands) of one branch-condition decision attempt (`proveCondWith?`). -/
def condAttemptCap : Nat := 50000

/-- Largest `natSubCount` of a pruned branch-condition problem that `proveCondWith?` still hands
    to the omega family after the strict tier failed (each `Nat` subtraction can double the work
    of a failing attempt). -/
def condMaxNatSubs : Nat := 6

/-- Run the decision procedure of `level` on the goal `p` (in the main goal's context), returning
    a proof of `p` on success. `level`:
    * `` `step``: `wp_step_bv_omega | omega | decide` (`wp_steps` PC branches);
    * `` `full``: `wp_bv_omega | omega | decide` (`wp_auto` / `wp_resolve_ites`; `decideCond?`
      tries `bv_decide` first for problems with bitwise hypotheses);
    * `` `slow``: `bv_fallback` (kernel-only `bv_kernel`; fallback of `wp_resolve_ites`).
    The omega-family `bv_omega` variants are skipped for goals with symbolic shift amounts.

    Every attempt runs on a pruned copy of the context (`omegaPruneGoal`), under
    `condAttemptCap` heartbeats and catching runtime exceptions: first the `strict` tier
    (hypotheses over the goal's own atoms), then, unless `strictOnly`, the transitive tier,
    which is skipped when it keeps the same hypotheses or has more than `condMaxNatSubs` `Nat`
    subtractions. The whole local context is never handed to `omega`. -/
def proveCondWith? (level : Name) (p : Expr) (strictOnly : Bool := false) :
    TacticM (Option Expr) := do
  let g ← getMainGoal
  g.withContext do
    let symShift := CondClassify.hasSymbolicShift (← instantiateMVars p)
    let bvDecideFb := ProofLib.BV.Arith.proofLib.bvDecideFallback.get (← getOptions)
    let tac ←
      if symShift && !bvDecideFb then
        `(tactic| first | (omega; done) | (decide; done))
      else if level == `slow then
        `(tactic| bv_fallback)
      else if symShift then
        `(tactic| first | (omega; done) | (decide; done))
      else if level == `step then
        `(tactic| first | (wp_step_bv_omega; done) | (omega; done) | (decide; done))
      else
        `(tactic| first | (wp_bv_omega; done) | (omega; done) | (decide; done))
    let t0 ← IO.monoMsNow
    let mut prevHyps : Option (Array FVarId) := none
    let mut result : Option Expr := none
    for strict in (if strictOnly then [true] else [true, false]) do
      let mvar ← mkFreshExprMVar p
      let some g' ← omegaWrapFilter? (← omegaPruneGoal mvar.mvarId! (if strict then .strict else .transitive))
        | continue
      let hyps ← g'.withContext do return (← getLCtx).getFVarIds
      if prevHyps == some hyps then continue
      prevHyps := some hyps
      if !strict && (← omegaGoalNatSubs g') > condMaxNatSubs then
        CondClassify.reportTiming (.str `condSkipNatSub (toString level)) false 0 p
        continue
      if ← runTacCapped g' tac condAttemptCap then
        result := some (← instantiateMVars mvar)
        break
    CondClassify.reportTiming level result.isSome ((← IO.monoMsNow) - t0) (← instantiateMVars p)
    return result

private def mentionsUltUle (p : Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  let has (e : Expr) : Bool :=
    (e.find? fun s => s.isConstOf ``BitVec.ult || s.isConstOf ``BitVec.ule).isSome
  let some ctx ← CondClassify.relevantCtx p | return true
  return has p || ctx.any has

private def decideCondOmega? (p : Expr) (level : Name) (skipOmega : Bool := false)
    (negFirst : Bool := false) (strictOnly : Bool := false) : TacticM (Option (Bool × Expr)) := do
  let g ← getMainGoal
  let both (lvl : Name) : TacticM (Option (Bool × Expr)) := do
    if negFirst then
      if let some prf ← proveCondWith? lvl (mkNot p) strictOnly then return some (false, prf)
      if let some prf ← proveCondWith? lvl p strictOnly then return some (true, prf)
    else
      if let some prf ← proveCondWith? lvl p strictOnly then return some (true, prf)
      if let some prf ← proveCondWith? lvl (mkNot p) strictOnly then return some (false, prf)
    return none
  let mut runOmega := !skipOmega
  if level == `full then
    let (bitwise, natish) ← g.withContext do CondClassify.classify p
    if bitwise then
      if let some r ← both `slow then return some r
      if !natish then runOmega := false
  if runOmega then
    if let some r ← both level then return some r
  return none

-- Routes `ground`, `linearEq`, and `linearArith` conditions through `ProofLib.BV.Arith.attempt`
-- (skipping `symbolicShift`, `unsupported`, `bitwise`, and `step`-level `ult`/`ule` goals).
private def arithRoute? (p : Expr) (level : Name) (hs : Array (FVarId × Expr))
    (c : ProofLib.BV.Arith.GoalClass) (v : ProofLib.BV.Arith.Verdict) :
    TacticM (Option (Option (Bool × Expr))) := do
  if c == .symbolicShift || c == .unsupported || c == .bitwise then return none
  if level == `step && (← mentionsUltUle p) then return none
  let t0 ← IO.monoMsNow
  let (tryPos, tryNeg) := match v with
    | .likely b => (b, !b)
    | _ => (true, true)
  let mut r := none
  if tryPos then
    if let some h ← ProofLib.BV.Arith.attempt p c hs then r := some (true, h)
  if r.isNone && tryNeg then
    if let some h ← ProofLib.BV.Arith.attempt (mkNot p) c hs then r := some (false, h)
  CondClassify.reportTiming (.str `arith (toString level)) r.isSome ((← IO.monoMsNow) - t0) p
  return some r

/-- Decide the (already normalized) branch condition `p`: `some (true, prf : p)`,
    `some (false, prf : ¬p)`, or `none`. Single swap-in point for the decision procedure:
    1. the concrete evaluator (`ProofLib.BV.Arith.evalVerdict`, on the relevant arithmetic
       hypotheses) looks for two models of the hypotheses that disagree on `p`; if it finds them,
       neither `p` nor `¬p` follows from those hypotheses, so only the strict pruning tier of
       `proveCondWith?` is attempted (with `proofLib.verdictSkip`, no solver is run at all, and
       with `proofLib.verdictAudit` the full chain still runs and its outcome is logged);
    2. `arithRoute?` (except at the `slow` level), heartbeat-capped and runtime-guarded;
    3. `decideCondOmega?`. -/
def decideCond? (p : Expr) (level : Name) (skipOmega : Bool := false) :
    TacticM (Option (Bool × Expr)) := do
  let opts ← getOptions
  unless CondClassify.proofLib.arithRoute.get opts do return ← decideCondOmega? p level skipOmega
  let g ← getMainGoal
  let t0 ← IO.monoMsNow
  let p ← instantiateMVars p
  let (hs, c, v) ← g.withContext do
    let hs ← ProofLib.BV.Arith.relevantFor p
    let hTys := hs.map (·.2)
    return (hs, ← ProofLib.BV.Arith.classify p hTys, ← ProofLib.BV.Arith.evalVerdict p hTys)
  let undet := v == .undetermined
  CondClassify.reportTiming (.str `verdict (toString level)) undet ((← IO.monoMsNow) - t0) p
  if undet && CondClassify.proofLib.verdictSkip.get opts then
    unless CondClassify.proofLib.verdictAudit.get opts do return none
    let t1 ← IO.monoMsNow
    let r ← decideCondOmega? p level skipOmega
    CondClassify.reportTiming (.str `audit (toString level)) r.isSome ((← IO.monoMsNow) - t1) p
    return r
  -- Undetermined: the relevant hypotheses have models on both sides, so `arithRoute?` and the
  -- transitive pruning tier (which see the same hypotheses) cannot succeed; only the cheap strict
  -- tier is attempted.
  if undet then return ← decideCondOmega? p level skipOmega (strictOnly := true)
  if level != `slow then
    let routed ← tryTacticCatchRuntime <| withHeartbeatCap condAttemptCap <|
      g.withContext (arithRoute? p level hs c v)
    if let some (some r) := routed then return r
  decideCondOmega? p level skipOmega (negFirst := v == .likely false)

/-- Try to resolve `c` to either `true` (`prf : c`) or `false` (`prf : ¬c`): one `simp` pass on
    `IteResolved c ?b` normalizes `c` to `c'` and cheap closers (`IteResolved.of_true/of_false`,
    `rfl`, `wp_assumption`) are tried; otherwise the normalized condition is decided once with
    `decideCond?`. Returns `some (condTrue, propTy, prf)`.
    When `forStepPC = true` (used in `wpStepCore`), uses the lightweight `arm64_norm` +
    `wp_step_bv_omega` rules so loop/equality conditions (`cbz`/`cbnz`) are resolved without
    eagerly collapsing `BitVec.ule`/`BitVec.ult` branches that have an explicit `wp_if`.

    `stepFailed` carries normalized conditions on which the `step`-level decision already failed
    for the current goal (recorded by `wpStepCore` when `forStepPC = true`; consulted otherwise,
    so `wpAutoCore` does not re-run the same omega chain, see `decideCond?`). -/
def resolveIteCondFast? (c : Expr) (forStepPC : Bool := false)
    (stepFailed : Option (IO.Ref (Array Expr)) := none) :
    TacticM (Option (Bool × Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let nc := mkNot c
    let bEqFalseOpt : Option (Expr × Expr) :=
      match c.eq? with
      | some (_, b, rhs) =>
        if rhs.isConstOf ``Bool.true then
          some (b, mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.false))
        else
          none
      | none => none
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ← withReducible (isDefEq ty c) then
          return some (true, c, decl.toExpr)
        if ← withReducible (isDefEq ty nc) then
          return some (false, nc, decl.toExpr)
        if let some (b, bEqFalse) := bEqFalseOpt then
          if ← withReducible (isDefEq ty bEqFalse) then
            return some (false, nc, mkApp2 (mkConst ``IteResolved.not_eq_true_of_eq_false) b decl.toExpr)
    let env ← getEnv
    let hasRelCmp :=
      (c.find? fun e =>
        e.isConstOf ``BitVec.ule || e.isConstOf ``BitVec.ult ||
        e.isConstOf ``BitVec.sle || e.isConstOf ``BitVec.slt).isSome
    let (constrained, allConstrained, anyEqOrArith) ← analyzeConstrainedFVars c
    if isObviouslyUnresolvedCmp env c then
      if !allConstrained then
        return none
      if forStepPC && hasRelCmp && !anyEqOrArith then
        return none
    let (_, hypIds) ← if constrained then getLightweightSimpHyps else pure (#[], #[])
    let bMVar ← mkFreshExprMVar (mkConst ``Bool)
    let goalTy := mkApp2 (mkConst ``IteResolved) c bMVar
    let mvar ← mkFreshExprMVar goalTy
    let saved ← getGoals
    let savedState ← saveState
    setGoals [mvar.mvarId!]
    let ok ←
      if forStepPC then
        if constrained then
          let _ ← tryTacticQuiet (evalTactic (← `(tactic|
            simp (config := { decide := true }) only [
              beq_iff_eq, bne_iff_ne, Classical.not_not,
              bitvec_add1_add_sub1, bitvec_toNat_eq_zero_iff, bool_not_eq_true_iff,
              arm64_norm, $[$hypIds:ident],*])))
          let _ ← tryTacticQuiet (evalTactic (← `(tactic|
            simp (config := { decide := true }) only [
              zeroExtend64_eq_zero_iff_32, zeroExtend64_eq_zero_iff_16,
              zeroExtend64_eq_zero_iff_8, zeroExtend32_eq_zero_iff_16,
              zeroExtend32_eq_zero_iff_8, Classical.not_not, $[$hypIds:ident],*])))
          resolveResidual `step stepFailed (← tryTacticQuiet (evalTactic (← `(tactic|
            first
              | exact IteResolved.of_true
              | exact IteResolved.of_false
              | (apply IteResolved.mk_true; first | done | rfl | wp_assumption)
              | (apply IteResolved.mk_false_not; first | done | rfl | wp_assumption)
              | (apply IteResolved.mk_false; first | done | wp_assumption)
              | (apply IteResolved.mk_true_of_beq_eq_true; first | done | wp_assumption)
              | (apply IteResolved.mk_false_of_beq_eq_false; first | done | wp_assumption)
              | (apply IteResolved.mk_false_not_of_beq_eq_true; first | done | wp_assumption)
              | (apply IteResolved.mk_true_not_of_beq_eq_false; first | done | wp_assumption)))))
        else
          tryTacticQuiet (evalTactic (← `(tactic| (
            try simp (config := { decide := true }) only [
              beq_iff_eq, bne_iff_ne, Classical.not_not,
              bitvec_add1_add_sub1, bitvec_toNat_eq_zero_iff, bool_not_eq_true_iff,
              zeroExtend64_eq_zero_iff_32, zeroExtend64_eq_zero_iff_16,
              zeroExtend64_eq_zero_iff_8, zeroExtend32_eq_zero_iff_16,
              zeroExtend32_eq_zero_iff_8, arm64_norm]
            first
              | exact IteResolved.of_true
              | exact IteResolved.of_false
              | (apply IteResolved.mk_true; rfl)
              | (apply IteResolved.mk_false_not; rfl)))))
      else if constrained then
        let _ ← tryTacticQuiet (evalTactic (← `(tactic|
          simp (config := { decide := true }) only [
            beq_iff_eq, bne_iff_ne, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq, Classical.not_not,
            bv8_and_128_bne_zero, bv8_and_128_beq_zero, bv8_and_128_eq_zero_iff,
            bv8_and_eq_iff_zext64, bv8_eq_iff_zext64, bv8_lt_iff_zext64_ult, bv8_le_iff_zext64_ule,
            bv8_and_zext64, bv8_zext32_eq_iff_zext64, bv8_zext32_eq_right_iff_zext64,
            bv8_zext32_ult_iff_zext64, bv8_zext32_ule_iff_zext64,
            bv8_zext32_ult_right_iff_zext64, bv8_zext32_ule_right_iff_zext64,
            bv8_zext64_and_192_eq_64_iff, bv8_zext64_and_224_eq_32_iff,
            bv64_ule_34_iff_not_ule_33, bv64_and_ult_self_iff_ne,
            wp_norm, arm64_norm, $[$hypIds:ident],*])))
        let _ ← tryTacticQuiet (evalTactic (← `(tactic|
          simp (config := { decide := true }) only [
            zeroExtend64_eq_zero_iff_32, zeroExtend64_eq_zero_iff_16,
            zeroExtend64_eq_zero_iff_8, zeroExtend32_eq_zero_iff_16,
            zeroExtend32_eq_zero_iff_8, Classical.not_not, $[$hypIds:ident],*])))
        resolveResidual `full stepFailed (← tryTacticQuiet (evalTactic (← `(tactic|
          first
            | exact IteResolved.of_true
            | exact IteResolved.of_false
            | (apply IteResolved.mk_true; first | done | rfl | wp_assumption)
            | (apply IteResolved.mk_false_not; first | done | rfl | wp_assumption)
            | (apply IteResolved.mk_true_beq; first | done | rfl | wp_assumption)
            | (apply IteResolved.mk_false_beq; first | done | wp_assumption)
            | (apply IteResolved.mk_true_bne; first | done | wp_assumption)
            | (apply IteResolved.mk_false_bne; first | done | rfl | wp_assumption)
            | (apply IteResolved.mk_false; first | done | wp_assumption)
            | (apply IteResolved.mk_true_of_beq_eq_true; first | done | wp_assumption)
            | (apply IteResolved.mk_false_of_beq_eq_false; first | done | wp_assumption)
            | (apply IteResolved.mk_false_not_of_beq_eq_true; first | done | wp_assumption)
            | (apply IteResolved.mk_true_not_of_beq_eq_false; first | done | wp_assumption)))))
      else
        tryTacticQuiet (evalTactic (← `(tactic| (
          try simp (config := { decide := true }) only [
            beq_iff_eq, bne_iff_ne, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq, Classical.not_not,
            bv8_and_128_bne_zero, bv8_and_128_beq_zero, bv8_and_128_eq_zero_iff,
            bv8_and_eq_iff_zext64, bv8_eq_iff_zext64, bv8_lt_iff_zext64_ult, bv8_le_iff_zext64_ule,
            bv8_and_zext64, bv8_zext32_eq_iff_zext64, bv8_zext32_eq_right_iff_zext64,
            bv8_zext32_ult_iff_zext64, bv8_zext32_ule_iff_zext64,
            bv8_zext32_ult_right_iff_zext64, bv8_zext32_ule_right_iff_zext64,
            bv8_zext64_and_192_eq_64_iff, bv8_zext64_and_224_eq_32_iff,
            bv64_ule_34_iff_not_ule_33, bv64_and_ult_self_iff_ne,
            zeroExtend64_eq_zero_iff_32, zeroExtend64_eq_zero_iff_16,
            zeroExtend64_eq_zero_iff_8, zeroExtend32_eq_zero_iff_16,
            zeroExtend32_eq_zero_iff_8, wp_norm, arm64_norm]
          first
            | exact IteResolved.of_true
            | exact IteResolved.of_false
            | (apply IteResolved.mk_true; rfl)
            | (apply IteResolved.mk_false_not; rfl)))))
    if !ok then
      restoreState savedState
      return none
    setGoals saved
    let bVal ← instantiateMVars bMVar
    let prf ← instantiateMVars mvar
    if bVal.isConstOf ``Bool.true then
      return some (true, c, mkApp2 (mkConst ``IteResolved.to_true) c prf)
    else if bVal.isConstOf ``Bool.false then
      return some (false, mkNot c, mkApp2 (mkConst ``IteResolved.to_false) c prf)
    else
      restoreState savedState
      return none
where
  resolveResidual (level : Name) (stepFailed : Option (IO.Ref (Array Expr))) (cheapOk : Bool) :
      TacticM Bool := do
    if cheapOk then return true
    let [r] ← getGoals | return false
    r.withContext do
      let rTy := (← instantiateMVars (← r.getType)).consumeMData
      unless rTy.isAppOfArity ``IteResolved 2 do return false
      let c' := rTy.getArg! 0
      let (x, neg) := if c'.isAppOfArity ``Not 1 then (c'.getArg! 0, true) else (c', false)
      let skipOmega ← match stepFailed with
        | some ref =>
          if level == `full && (← ref.get).contains x then
            Pure.pure !(← mentionsUltUle x)
          else Pure.pure false
        | none => Pure.pure false
      let some (b, prf) ← decideCond? x level (skipOmega := skipOmega)
        | if level == `step then
            if let some ref := stepFailed then ref.modify (·.push x)
          return false
      let term? ← observing? do
        match neg, b with
        | false, true => mkAppM ``IteResolved.mk_true #[prf]
        | false, false => mkAppM ``IteResolved.mk_false #[prf]
        | true, true => mkAppM ``IteResolved.mk_false_not #[prf]
        | true, false => mkAppM ``IteResolved.mk_true #[prf]
      let some term := term? | return false
      unless ← isDefEq (← inferType term) (← r.getType) do return false
      r.assign term
      setGoals []
      return true

end

end ProofLib
