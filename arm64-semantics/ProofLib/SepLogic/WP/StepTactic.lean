/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import ProofLib.MaxRecDepthDiag
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
public import ProofLib.SepLogic.WP.TacticCore
public import ProofLib.SepLogic.WP.PairStep

/-!
# Per-Instruction Symbolic Step Dispatch

Maps each decoded `Arm64.Instr` to its corresponding `SepWP.step_*` soundness theorem and defines
`wpStepCoreWithOutcome` and `wp_step`.
-/

public meta section

namespace ProofLib

open Arm64

open Lean Elab Tactic Meta

/-- Whether `e` is a `MemWidth` constant of `bytes` bytes (`8`: `X64`, `4`: `W32`, `2`: `H16`, `1`: `B8`). -/
def isMemSizeConst (e : Expr) (bytes : Nat) : Bool :=
  match bytes, e.constName? with
  | 8, some ``MemWidth.X64 => true
  | 4, some ``MemWidth.W32 => true
  | 2, some ``MemWidth.H16 => true
  | 1, some ``MemWidth.B8 => true
  | _, _ => false

/-- Whether the spatial context `P` of the main `SepWP prog target_pc s P post` goal has a `↦₃₂`
    atom, or (with `proofLib.wpSymbolicBytes`) a `↦ₛ` / `↦ᵣ` byte-list atom that `wp_sep_access`
    can serve a 32-bit access from (a cheap pre-check before trying the first-class 32-bit step
    rules). -/
def sepWPHasPointsTo32 (isSingleStep : Bool := false) : TacticM Bool := do
  let g ← getMainGoal
  let opts ← getOptions
  let symBytes := CondClassify.proofLib.wpSymbolicBytes.get opts
  let autoFocus := isSingleStep && proofLib.wpAutoSubwordFocus.get opts
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return false
    return (SepSolver.atoms (ty.getArg! 3)).any fun a =>
      a.isAppOfArity ``Arm64.pointsTo32 2 ||
        (autoFocus && a.isAppOfArity ``Arm64.pointsTo32RO 2) ||
        (symBytes && (a.isAppOfArity ``Arm64.pointsToBytes 2 ||
          a.isAppOfArity ``Arm64.pointsToBytesRO 2))

/-- Step a 32-bit access (`LDR/LDUR/STR/STUR/LDP/STP Wt`, `LDRSW Xt`) through first-class
    `↦₃₂` atoms (`SepWP.step_ldr32`, ..., `SepWP.step_stp32`). Fails (for the caller to fall back to
    the 64-bit-half rules) if the accessed cells are not `↦₃₂` atoms of the spatial context. -/
def wpStep32Core (instExpr fetchPrf : Expr) : TacticM Unit := do
  if instExpr.isAppOfArity ``Instr.ldr 5 && isMemSizeConst (instExpr.getArg! 1) 4 then
    if instExpr.getArg! 0 == mkConst ``RegWidth.W32 && instExpr.getArg! 2 == mkConst ``Bool.false then
      evalTactic (← `(tactic| apply SepWP.step_ldr32))
    else
      evalTactic (← `(tactic| apply SepWP.step_ldrsw32))
    evalTactic (← `(tactic| (
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
    )))
    closeFetchSubgoal (some fetchPrf)
    evalTactic (← `(tactic| (
      wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_sep_access
      wp_focus_close wp_norm_lhs
    )))
  else if instExpr.isAppOfArity ``Instr.str 3 && isMemSizeConst (instExpr.getArg! 0) 4 then
    let mId ← freshIdent `m
    evalTactic (← `(tactic| apply SepWP.step_str32))
    evalTactic (← `(tactic| (
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
    )))
    closeFetchSubgoal (some fetchPrf)
    evalTactic (← `(tactic| (
      wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_sep_access
      wp_focus_close wp_norm_lhs
      intro $mId:ident
      try wp_norm_state
    )))
  else if instExpr.isAppOfArity ``Instr.ldp 5 &&
          instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
          instExpr.getArg! 1 == mkConst ``Bool.false then
    evalTactic (← `(tactic| (
      apply SepWP.step_ldp32
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
    )))
    closeFetchSubgoal (some fetchPrf)
    evalTactic (← `(tactic| (
      wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_sep_access
      wp_focus_close wp_sep_access
      wp_focus_close wp_norm_lhs
    )))
  else if instExpr.isAppOfArity ``Instr.stp 4 && instExpr.getArg! 0 == mkConst ``RegWidth.W32 then
    let mId ← freshIdent `m
    evalTactic (← `(tactic| (
      apply SepWP.step_stp32
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
    )))
    closeFetchSubgoal (some fetchPrf)
    evalTactic (← `(tactic| (
      wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_norm_lhs
      wp_focus_close wp_sep_access
      wp_focus_close wp_sep_access
      wp_focus_close wp_norm_lhs
      intro $mId:ident
      try wp_norm_state
    )))
  else
    throwError "wp_step: not a 32-bit access"

/-- Extract the value of register `r` from the state-update spine of `s`, falling back to
    local `s.sp = ...` / `s.readReg64 r = ...` hypotheses or `s.readReg64 r`. -/
partial def evalSpineReg64 (s : Expr) (r : Expr) : MetaM Expr := do
  let s := (← instantiateMVars s).consumeMData
  if s.isAppOfArity ``State.writeReg64 3 then
    if s.getArg! 1 == r then return s.getArg! 2
    return ← evalSpineReg64 (s.getArg! 0) r
  if s.isAppOfArity ``State.writeReg32 3 then
    if s.getArg! 1 == r then
      return mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr 32) (toExpr 64) (s.getArg! 2)
    return ← evalSpineReg64 (s.getArg! 0) r
  if s.isAppOfArity ``State.writeReg 4 then
    if s.getArg! 2 == r then return s.getArg! 3
    return ← evalSpineReg64 (s.getArg! 0) r
  if s.isAppOfArity ``State.setPC 2 ||
     s.isAppOfArity ``State.setPState 2 ||
     s.isAppOfArity ``State.setMem 2 ||
     s.isAppOfArity ``State.advancePC 1 ||
     s.isAppOfArity ``State.writeVReg128 3 ||
     s.isAppOfArity ``State.writeVReg64 3 ||
     s.isAppOfArity ``State.writeVReg32 3 ||
     s.isAppOfArity ``State.setFpsr 2 ||
     s.isAppOfArity ``State.orFpsr 2 ||
     s.isAppOfArity ``State.stepExclOracle 1 ||
     s.isAppOfArity ``State.stepExclLoop 1 ||
     s.isAppOfArity ``State.setBrk 2 ||
     s.isAppOfArity ``State.setPhysMemAvail 2 ||
     s.isAppOfArity ``State.setFs 2 ||
     s.isAppOfArity ``State.nextOracle 1 ||
     s.isAppOfArity ``ProofLib.setTpidrEl0 2 ||
     s.isAppOfArity ``ProofLib.applyWriteback 2 then
    return ← evalSpineReg64 (s.getArg! 0) r
  if s.isFVar then
    let isSp := r == mkConst ``Reg.sp
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if isSp && lhs.isAppOfArity ``State.sp 1 && lhs.getArg! 0 == s then
            return rhs
          if lhs.isAppOfArity ``State.readReg64 2 && lhs.getArg! 0 == s && lhs.getArg! 1 == r then
            return rhs
  if r == mkConst ``Reg.sp then
    return mkApp (mkConst ``State.sp) s
  return mkApp2 (mkConst ``State.readReg64) s r

/-- Decide upfront whether a 32-bit access at `addrExpr` targets the high 32-bit half (`base + 4`)
    or low 32-bit half (`base`) of a `↦₆₄` cell in the current spatial context `P`. -/
def preferHi64ForAddr (addrExpr : Expr) : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return false
    let sExpr := ty.getArg! 2
    let P := SepSolver.stripMData (ty.getArg! 3)
    let am ← whnf addrExpr
    let mut eaOpt : Option Expr := none
    let mut immOffOpt : Option Nat := none
    if am.isAppOfArity ``AddrMode.Offset 2 ||
       am.isAppOfArity ``AddrMode.UnscaledOffset 2 ||
       am.isAppOfArity ``AddrMode.PreIndex 2 then
      let baseReg := am.getArg! 0
      let offExpr := am.getArg! 1
      if let some (w, c) ← evalBitVecLit? offExpr then
        if w == 64 then immOffOpt := some c
      let baseVal ← evalSpineReg64 sExpr baseReg
      eaOpt := some (← mkAppM ``HAdd.hAdd #[baseVal, offExpr])
    else if am.isAppOfArity ``AddrMode.PostIndex 2 then
      let baseReg := am.getArg! 0
      immOffOpt := some 0
      eaOpt := some (← evalSpineReg64 sExpr baseReg)
    if let some ea := eaOpt then
      let (eaNorm, _) ← SepSolver.normAddrMeta ea
      let (bEa, oEa) ← sepAddrBaseOff eaNorm
      for atom in SepSolver.atoms P do
        if atom.isAppOfArity ``Arm64.pointsTo64 2 then
          let (aNorm, _) ← SepSolver.normAddrMeta (atom.getArg! 0)
          let (bCell, oCell) ← sepAddrBaseOff aNorm
          if bEa == bCell || (← withReducibleAndInstances (isDefEq bEa bCell)) then
            let diff := (oEa + 2 ^ 64 - oCell) % (2 ^ 64)
            if diff == 4 then return true
            if diff == 0 then return false
    if let some c := immOffOpt then
      return (c % 8 == 4)
    return false

/-- Prove `p` (in the main goal's context) for `resolveIteCondStep?`, under 25000 heartbeats:
    `simp only` with `wp_norm`, `arm64_norm` and the lightweight hypotheses `hypIds`, then the
    cheap closers (`rfl`, `wp_assumption`, `assumption`, `decide`), then `bv_fallback` on the
    `strict` and `transitive` pruned contexts only (`proveOmegaBounded?`; `goalOnly` is subsumed by
    `strict`, and a failing attempt costs a large share of a small enclosing budget). The whole
    local context is never handed to `bv_omega`: a failing `omega` run does not respect the
    heartbeat cap. Returns `none` (restoring the goals)
    if `p` is not proved. -/
def tryProveIteCondStep? (hypIds : Array Ident) (p : Expr) : TacticM (Option Expr) := do
  let mvar ← mkFreshExprMVar p
  let saved ← getGoals
  setGoals [mvar.mvarId!]
  let ok ← tryTacticCatchRuntimeBool <| withHeartbeatCap 25000 do
    let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
      simp (config := { decide := true }) only [
        beq_iff_eq, bne_iff_ne, Classical.not_not, BitVec.truncate_and,
        wp_norm, arm64_norm, $[$hypIds:ident],*]))
    if !(← getGoals).isEmpty then
      let _ ← tryTacticCatchRuntimeBool <| evalTactic (← `(tactic|
        first | done | with_reducible rfl | wp_assumption | with_reducible assumption |
          (decide; done)))
    if let [g'] ← getGoals then
      if ← proveOmegaBounded? g' [← `(tactic| (bv_fallback; done))] [.strict, .transitive] then
        setGoals []
    if !(← getGoals).isEmpty then throwError "unsolved"
  setGoals saved
  if ok then return some (← instantiateMVars mvar) else return none

/-- Try to resolve `ite` condition `c` at `s.pc` for `wpStepCore` / `wp_steps`: first via
    `resolveIteCondFast? c (forStepPC := true)`, then via `tryProveIteCondStep?` on `c` and `¬c`
    when `c` is a non-relational condition with constrained free variables in context. -/
def resolveIteCondStep? (c : Expr) (stepFailed : Option (IO.Ref (Array Expr)) := none) :
    TacticM (Option (Bool × Expr × Expr)) := do
  if let some res ← resolveIteCondFast? c (forStepPC := true) stepFailed then
    return some res
  let g ← getMainGoal
  g.withContext do
    let hasRelCmp :=
      (c.find? fun e =>
        e.isConstOf ``BitVec.ule || e.isConstOf ``BitVec.ult ||
        e.isConstOf ``BitVec.sle || e.isConstOf ``BitVec.slt).isSome
    if hasRelCmp then return none
    let (constrained, allConstrained, _) ← analyzeConstrainedFVars c
    if !constrained then return none
    if isObviouslyUnresolvedCmp (← getEnv) c && !allConstrained then return none
    let (_, hypIds) ← getLightweightSimpHyps
    if let some prf ← tryProveIteCondStep? hypIds c then
      return some (true, c, prf)
    let nc := mkNot c
    if let some prf ← tryProveIteCondStep? hypIds nc then
      return some (false, nc, prf)
    return none

/-- Heartbeat budget (thousands) of the `full`-level retry in `resolveIteCondTerminal?`. -/
def terminalIteCap : Nat := 60000

/-- `resolveIteCondStep?`, then, if the `step` level leaves a relational condition `c`
    (`ult`/`ule`/`slt`/`sle`) undecided, prove `c` or `¬c` with the `full`-level omega chain
    (`proveCondWith? `full`, which rewrites `ult`/`ule` through `toNat`) on the strict pruning
    tier only (hypotheses over the condition's own atoms: the transitive tier can hand `omega`
    problems whose core loop ignores heartbeats), under `terminalIteCap` heartbeats and catching
    runtime exceptions. Other conditions
    are not retried: the `step` level already ran the same omega chain on them. For tactics that
    would otherwise fail at an `ite` PC (`wp_done`), e.g. a loop-exit compare after the last
    iteration. The step loops do not use it: there a `step`-level `ult`/`ule` miss stops at the
    `ite` PC for an explicit `wp_if`. -/
def resolveIteCondTerminal? (c : Expr) : TacticM (Option (Bool × Expr × Expr)) := do
  if let some res ← resolveIteCondStep? c then return some res
  let hasRelCmp := (c.find? fun e =>
    e.isConstOf ``BitVec.ule || e.isConstOf ``BitVec.ult ||
    e.isConstOf ``BitVec.sle || e.isConstOf ``BitVec.slt).isSome
  unless hasRelCmp do return none
  let r ← tryTacticCatchRuntime <| withHeartbeatCap terminalIteCap do
    if let some prf ← proveCondWith? `full c (strictOnly := true) then return some (true, c, prf)
    let nc := mkNot c
    if let some prf ← proveCondWith? `full nc (strictOnly := true) then
      return some (false, nc, prf)
    return none
  return r.join

/-- Fallback for `wp_step` / `wp_sym_step` on a single-step call (`stepFailed.isNone && !inStepLoop`)
    when `proofLib.wpDecideBranchOnStep` is `true` and `resolveIteCondStep?` leaves `c` undecided:
    tries `resolveIteCondFast? c (forStepPC := false)` (lifting the `forStepPC` relational guard),
    `resolveIteCondTerminal? c`, and `tryProveIteCondStep?` without the `!hasRelCmp` guard. -/
def resolveIteCondOnStepFallback? (c : Expr) : TacticM (Option (Bool × Expr × Expr)) := do
  if !proofLib.wpDecideBranchOnStep.get (← getOptions) then
    return none
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  let res? ← tryTacticCatchRuntime do
    if let some res ← resolveIteCondFast? c (forStepPC := false) then
      return res
    if let some res ← resolveIteCondTerminal? c then
      return res
    let g ← getMainGoal
    g.withContext do
      let (_, hypIds) ← getLightweightSimpHyps
      if let some prf ← tryProveIteCondStep? hypIds c then
        return (true, c, prf)
      let nc := mkNot c
      if let some prf ← tryProveIteCondStep? hypIds nc then
        return (false, nc, prf)
      throwError "undecided"
  if res?.isNone then
    restoreState saved
    Core.setMessageLog savedMsgs
  return res?

/-- Extract `s.pc = pcExpr` proof from `s`'s constructor spine or from the local context. -/
def provePcEqOrLocal? (s pcExpr : Expr) : MetaM (Option Expr) := do
  if let some (pcFound, p) ← provePcEq? s then
    if pcFound == pcExpr then return some p else return none
  let targetEq ← mkEq (mkApp (mkConst ``State.pc) s) pcExpr
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      if decl.type == targetEq || (← withReducible (isDefEq decl.type targetEq)) then
        return some decl.toExpr
  return none

/-- Fast direct `MetaM` step for pure instructions (`SepWP.step_pure_setPC`,
    `SepWP.step_pure_setMem_setPC`, `SepWP.step_pure`): constructs only 1 metavariable (`gNext`)
    and 0 `evalTactic` calls per instruction step. -/
def tryStepPureDirect? (pcExpr instExpr fetchPrf : Expr) : TacticM Bool := do
  let g ← getMainGoal
  let cached ← getOrInitWpNormSimpCache (preserveOnExtend := true)
  let nextGoal? ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return none
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let s := ty.getArg! 2
    let P := ty.getArg! 3
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    let some hrun ← proveStatusRunningExpr? s | return none
    let isSetPC := s.isAppOfArity ``State.setPC 2 && s.getArg! 1 == pcExpr
    let isSetMemSetPC := s.isAppOfArity ``State.setMem 2 &&
      (s.getArg! 0).isAppOfArity ``State.setPC 2 && (s.getArg! 0).getArg! 1 == pcExpr
    let execIn := if isSetPC || isSetMemSetPC then s else mkApp2 (mkConst ``State.setPC) s pcExpr
    let execLhs := mkApp3 (mkConst ``Program.evalInst) prog instExpr execIn
    let initState : Simp.State := { cached.simpState with numSteps := 0 }
    let (res, simpState') ← Lean.Meta.simpCore execLhs cached.ctx cached.simprocs none initState
    let seededCache := seedNormalizedInSimpCache res.expr simpState'.cache
    setWpNormSimpCache { cached with simpState := { simpState' with cache := seededCache } }
    let s' := res.expr
    let hexec ← match res.proof? with
      | some p => pure p
      | none =>
        let eqTy ← mkEq execLhs s'
        pure (mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl s'))
    let nextTy := mkApp6 (mkConst ``SepWP) prog targetPc s' P post oom
    if isSetPC then
      let s0 := s.getArg! 0
      let some hmem ← proveMemEqExpr? (mkApp (mkConst ``State.mem) s') (mkApp (mkConst ``State.mem) s0)
        | return none
      let gNext ← mkFreshExprMVar nextTy
      let prf := mkAppN (mkConst ``SepWP.step_pure_setPC)
        #[prog, targetPc, s0, s', P, post, oom, pcExpr, instExpr, hrun, fetchPrf, hexec, hmem, gNext]
      g.assign prf
      return some gNext.mvarId!
    if isSetMemSetPC then
      let s0 := (s.getArg! 0).getArg! 0
      let m := s.getArg! 1
      let some hmem ← proveMemEqExpr? (mkApp (mkConst ``State.mem) s') m
        | return none
      let gNext ← mkFreshExprMVar nextTy
      let prf := mkAppN (mkConst ``SepWP.step_pure_setMem_setPC)
        #[prog, targetPc, s0, s', P, post, oom, pcExpr, m, instExpr, hrun, fetchPrf, hexec, hmem, gNext]
      g.assign prf
      return some gNext.mvarId!
    let some hpc ← provePcEqOrLocal? s pcExpr | return none
    let some hmem ← proveMemEqExpr? (mkApp (mkConst ``State.mem) s') (mkApp (mkConst ``State.mem) s)
      | return none
    let gNext ← mkFreshExprMVar nextTy
    let prf := mkAppN (mkConst ``SepWP.step_pure)
      #[prog, targetPc, s, s', P, post, oom, pcExpr, instExpr, hpc, hrun, fetchPrf, hexec, hmem, gNext]
    g.assign prf
    return some gNext.mvarId!
  if let some nextGoal := nextGoal? then
    replaceMainGoal [nextGoal]
    return true
  return false

/-- Simplify `lhs` in `MetaM` using the cached `WpNormSimpCache`, returning `(rhs, proof)`. -/
def wpNormSimpLhsExpr (lhs : Expr) : TacticM (Expr × Expr) := do
  if let some (rhs, prf) ← proveApplyWritebackNoneSetPCDirect? lhs then
    return (rhs, prf)
  let hasIte := (lhs.find? (·.isConstOf ``ite)).isSome
  let cached ← getOrInitWpNormSimpCache (preserveOnExtend := !hasIte)
  let initState : Simp.State := { cached.simpState with numSteps := 0 }
  let (res, simpState') ← Lean.Meta.simpCore lhs cached.ctx cached.simprocs none initState
  let seededCache := seedNormalizedInSimpCache res.expr simpState'.cache
  setWpNormSimpCache { cached with simpState := { simpState' with cache := seededCache } }
  let rhs := res.expr
  let prf ← match res.proof? with
    | some p => pure p
    | none =>
      let eqTy ← mkEq lhs rhs
      pure (mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl rhs))
  return (rhs, prf)

/-- Direct `MetaM` fast path for 64-bit `LDR` (`SepWP.step_ldr64`) with 0 `evalTactic` calls. -/
def tryStepLdr64Direct? (pcExpr rt addr fetchPrf : Expr) : TacticM Bool := do
  let _ ← getOrCreateWpNormSimpCacheRef
  let g ← getMainGoal
  let nextGoal? ← tryTacticCatchRuntime do
    g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      if !ty.isAppOfArity ``SepWP 6 then throwError "not SepWP"
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let s := ty.getArg! 2
      let P := ty.getArg! 3
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let some hpc ← provePcEqOrLocal? s pcExpr | throwError "no pc"
      let some hrun ← proveStatusRunningExpr? s | throwError "no status"
      let amExpr := addr
      let spLhs := mkApp2 (mkConst ``checkAddrSPAligned) s amExpr
      let bTrue := mkConst ``Bool.true
      let spGoalTy ← mkEq spLhs bTrue
      let some hsp ← proveCheckAddrSPAligned? spGoalTy spLhs bTrue | throwError "no sp"
      let addrLhs := mkApp2 (mkConst ``evalAddrMode) s amExpr
      let (addrRhs, haddr) ← wpNormSimpLhsExpr addrLhs
      unless addrRhs.isAppOfArity ``Prod.mk 4 do throwError "evalAddrMode not a pair"
      let ea := addrRhs.getArg! 2
      let wb := addrRhs.getArg! 3
      let (v, hload) ← proveSepLoad ``Arm64.pointsTo64 ea P
      let rtReg := rt
      let pcPlus4 ← mkAppM ``HAdd.hAdd #[pcExpr, mkCanonBitVecLit 64 4]
      let execLhs := mkApp2 (mkConst ``State.setPC)
        (mkApp3 (mkConst ``State.writeReg64)
          (mkApp2 (mkConst ``applyWriteback) s wb) rtReg v)
        pcPlus4
      let (s', hexec) ← wpNormSimpLhsExpr execLhs
      let nextTy := mkApp6 (mkConst ``SepWP) prog targetPc s' P post oom
      let gNext ← mkFreshExprMVar nextTy
      let prf := mkAppN (mkConst ``SepWP.step_ldr64)
        #[prog, targetPc, s, s', P, post, oom, pcExpr, rt, addr, ea, wb, v,
          hpc, hrun, fetchPrf, hsp, haddr, hload, hexec, gNext]
      g.assign prf
      return gNext.mvarId!
  if let some nextGoal := nextGoal? then
    replaceMainGoal [nextGoal]
    return true
  return false

/-- Direct `MetaM` fast path for 64-bit `STR` (`SepWP.step_str64`) with 0 `evalTactic` calls. -/
def tryStepStr64Direct? (pcExpr rt addr fetchPrf : Expr) : TacticM Bool := do
  let _ ← getOrCreateWpNormSimpCacheRef
  let g ← getMainGoal
  let mId ← freshIdent `m
  let nextGoal? ← tryTacticCatchRuntime do
    g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      if !ty.isAppOfArity ``SepWP 6 then throwError "not SepWP"
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let s := ty.getArg! 2
      let P := ty.getArg! 3
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let some hpc ← provePcEqOrLocal? s pcExpr | throwError "no pc"
      let some hrun ← proveStatusRunningExpr? s | throwError "no status"
      let amExpr := addr
      let spLhs := mkApp2 (mkConst ``checkAddrSPAligned) s amExpr
      let bTrue := mkConst ``Bool.true
      let spGoalTy ← mkEq spLhs bTrue
      let some hsp ← proveCheckAddrSPAligned? spGoalTy spLhs bTrue | throwError "no sp"
      let addrLhs := mkApp2 (mkConst ``evalAddrMode) s amExpr
      let (addrRhs, haddr) ← wpNormSimpLhsExpr addrLhs
      unless addrRhs.isAppOfArity ``Prod.mk 4 do throwError "evalAddrMode not a pair"
      let ea := addrRhs.getArg! 2
      let wb := addrRhs.getArg! 3
      let rtReg := rt
      let valLhs := mkApp2 (mkConst ``State.readReg64) s rtReg
      let (val, hval) ← wpNormSimpLhsExpr valLhs
      let (P', hstore) ← proveSepStore ``Arm64.pointsTo64 ea val P
      let pcPlus4 ← mkAppM ``HAdd.hAdd #[pcExpr, mkCanonBitVecLit 64 4]
      let execLhs := mkApp2 (mkConst ``State.setPC) (mkApp2 (mkConst ``applyWriteback) s wb) pcPlus4
      let (s', hexec) ← wpNormSimpLhsExpr execLhs
      let memTy := mkConst ``Arm64.Memory
      let forallTy := Lean.mkForall mId.getId .default memTy
        (mkApp6 (mkConst ``SepWP) prog targetPc
          (mkApp2 (mkConst ``State.setMem) s' (mkBVar 0)) P' post oom)
      let gForall ← mkFreshExprMVar forallTy
      let prf := mkAppN (mkConst ``SepWP.step_str64)
        #[prog, targetPc, s, s', P, P', post, oom, pcExpr, rt, addr, ea, wb, val,
          hpc, hrun, fetchPrf, hsp, haddr, hval, hstore, hexec, gForall]
      g.assign prf
      let (mFVar, gIntro) ← gForall.mvarId!.intro mId.getId
      if s'.isAppOfArity ``State.setMem 2 then
        let sInner := s'.getArg! 0
        let mOld := s'.getArg! 1
        if !sInner.isAppOfArity ``State.setMem 2 then
          let mExpr := mkFVar mFVar
          let sOuter := mkApp2 (mkConst ``State.setMem) s' mExpr
          let sClean := mkApp2 (mkConst ``State.setMem) sInner mExpr
          let hs := mkApp3 (mkConst ``State.setMem_setMem) sInner mOld mExpr
          let cleanTy := mkApp6 (mkConst ``SepWP) prog targetPc sClean P' post oom
          let gClean ← gIntro.withContext (mkFreshExprMVar cleanTy)
          let congrPrf := mkAppN (mkConst ``SepWP.congr_state)
            #[prog, targetPc, sOuter, sClean, P', post, oom, hs, gClean]
          gIntro.assign congrPrf
          return gClean.mvarId!
      return gIntro
  if let some nextGoal := nextGoal? then
    replaceMainGoal [nextGoal]
    return true
  return false

/-- Classification of the instruction stepped by `wpStepCoreWithOutcome`. -/
inductive WpStepOutcome where
  | steppedNormal
  | steppedCall
  | steppedRet
  | steppedBranch
  /-- Two straight-line instructions stepped at once by a `C_pairStep_0x<off>` lemma
      (`ProofLib.SepLogic.WP.PairStep`); stepping loops count it as two steps. -/
  | steppedPair
  deriving BEq, Repr

/-- Check in `O(log N)` MetaM WHNF (using `<rawProg>_tree.fetchDecodeAt` binary tree descent of
    height `≤ 18` plus an iterative `for`-loop scan of `prog.stubs` so unary `List` spines are never
    traversed recursively inside `whnf`) whether `pcExpr` is an extern hook stub or outside `.text`. -/
def fastProgFetchNone? (progExpr pcExpr : Expr) : TacticM Bool := do
  try
    let progUnwrapped ← unwrapRebasedProgExpr progExpr
    let progBase ← whnf (mkApp (mkConst ``Program.base) progUnwrapped)
    let (bProg, oProg) ← sepAddrBaseOff progBase
    let (pcNorm, _) ← SepSolver.normAddrMeta pcExpr
    let (bPc, oPc) ← sepAddrBaseOff pcNorm
    if !(bPc == bProg || (← withReducibleAndInstances (isDefEq bPc bProg))) then
      return false
    let relOff := (oPc + 2 ^ 64 - oProg) % (2 ^ 64)
    let relOffExpr := toExpr relOff
    let rawProgExpr :=
      if progUnwrapped.isAppOfArity ``Program.rebase 4 then progUnwrapped.getArg! 0
      else progUnwrapped
    if let some rawConst := rawProgExpr.consumeMData.getAppFn.constName? then
      let treeName := rawConst.appendAfter "_tree"
      if (← getEnv).contains treeName then
        let treeRes ← withHeartbeatCap 4000
          (whnf (mkApp2 (mkConst ``ProofLib.ProgramReflection.WordTree.fetchDecodeAt)
            (mkConst treeName) relOffExpr))
        if treeRes.isAppOfArity ``Option.none 1 then
          return true
    let mut curStubs ← whnfCore (mkApp (mkConst ``Program.stubs) rawProgExpr)
    for _ in [0:4096] do
      if !curStubs.isAppOfArity ``List.cons 3 then
        curStubs ← whnf curStubs
      if curStubs.isAppOfArity ``List.cons 3 then
        let entry ← whnf (curStubs.getArg! 1)
        curStubs := curStubs.getArg! 2
        if entry.isAppOfArity ``Prod.mk 4 then
          let offExpr ← whnf (entry.getArg! 3)
          if let some stubOff ← evalNatLit? offExpr then
            if stubOff == relOff then
              return true
      else
        break
    return false
  catch _ =>
    return false

private def extractLoadStoreAddrMode? (instExpr : Expr) : Option Expr :=
  if instExpr.isAppOfArity ``Instr.ldr 5 then
    some (instExpr.getArg! 4)
  else if instExpr.isAppOfArity ``Instr.str 3 then
    some (instExpr.getArg! 2)
  else if instExpr.isAppOfArity ``Instr.ldp 5 then
    some (instExpr.getArg! 4)
  else if instExpr.isAppOfArity ``Instr.stp 4 then
    some (instExpr.getArg! 3)
  else
    none

private def evalLoadStoreEffAddrDiag? (sExpr amExpr : Expr) : TacticM (Option Expr) := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  let res? ← tryTacticCatchRuntime <| withHeartbeatCap 10000 do
    let addrLhs := mkApp2 (mkConst ``evalAddrMode) sExpr amExpr
    let (addrRhs, _) ← wpNormSimpLhsExpr addrLhs
    if addrRhs.isAppOfArity ``Prod.mk 4 then
      let ea := addrRhs.getArg! 2
      let (eaNorm, _) ← SepSolver.normAddrMeta ea
      return eaNorm
    let am ← whnf amExpr
    if am.isAppOfArity ``AddrMode.Offset 2 ||
       am.isAppOfArity ``AddrMode.UnscaledOffset 2 ||
       am.isAppOfArity ``AddrMode.PreIndex 2 then
      let baseVal ← evalSpineReg64 sExpr (am.getArg! 0)
      let offExpr := am.getArg! 1
      let ea ← if offExpr == toExpr (0#64) then pure baseVal
        else mkAppM ``HAdd.hAdd #[baseVal, offExpr]
      let (eaNorm, _) ← SepSolver.normAddrMeta ea
      return eaNorm
    if am.isAppOfArity ``AddrMode.PostIndex 2 then
      let baseVal ← evalSpineReg64 sExpr (am.getArg! 0)
      let (eaNorm, _) ← SepSolver.normAddrMeta baseVal
      return eaNorm
    throwError "no ea"
  restoreState saved
  Core.setMessageLog savedMsgs
  return res?

private def memSizeConstBytes? (szExpr : Expr) : Option Nat :=
  if isMemSizeConst szExpr 8 then some 8
  else if isMemSizeConst szExpr 4 then some 4
  else if isMemSizeConst szExpr 2 then some 2
  else if isMemSizeConst szExpr 1 then some 1
  else none

private def extractLoadStoreAccesses? (instExpr : Expr) :
    Option (Expr × Nat × Bool) :=
  if instExpr.isAppOfArity ``Instr.ldr 5 then
    match memSizeConstBytes? (instExpr.getArg! 1) with
    | some b => some (instExpr.getArg! 4, b, false)
    | none => none
  else if instExpr.isAppOfArity ``Instr.str 3 then
    match memSizeConstBytes? (instExpr.getArg! 0) with
    | some b => some (instExpr.getArg! 2, b, false)
    | none => none
  else if instExpr.isAppOfArity ``Instr.ldp 5 then
    let elemBytes :=
      if instExpr.getArg! 1 == mkConst ``Bool.true || instExpr.getArg! 0 == mkConst ``RegWidth.W32
      then 4 else 8
    some (instExpr.getArg! 4, elemBytes, true)
  else if instExpr.isAppOfArity ``Instr.stp 4 then
    let elemBytes := if instExpr.getArg! 0 == mkConst ``RegWidth.W32 then 4 else 8
    some (instExpr.getArg! 3, elemBytes, true)
  else
    none

private def splitAtomForTarget? (atom targetEa bTarget : Expr) (oTarget targetW : Nat) :
    TacticM (Option (Expr × Expr × Bool)) := do
  if atom.isAppOfArity ``Arm64.pointsTo64 2 && targetW < 8 then
    let a := atom.getArg! 0
    let v := atom.getArg! 1
    let (aNorm, _) ← SepSolver.normAddrMeta a
    let (bCell, oCell) ← sepAddrBaseOff aNorm
    if !(bTarget == bCell || (← withReducibleAndInstances (isDefEq bTarget bCell))) then
      return none
    let relOff := (oTarget + 2 ^ 64 - oCell) % (2 ^ 64)
    if relOff + targetW > 8 then return none
    let hSplit := mkApp2 (mkConst ``pointsTo64_split32') a v
    let eqTy ← inferType hSplit
    let some (_, _, splitRhs) := eqTy.eq? | return none
    return some (splitRhs, hSplit, false)
  if atom.isAppOfArity ``Arm64.pointsTo32 2 && targetW < 4 then
    let a := atom.getArg! 0
    let v := atom.getArg! 1
    let (aNorm, _) ← SepSolver.normAddrMeta a
    let (bCell, oCell) ← sepAddrBaseOff aNorm
    if !(bTarget == bCell || (← withReducibleAndInstances (isDefEq bTarget bCell))) then
      return none
    let relOff := (oTarget + 2 ^ 64 - oCell) % (2 ^ 64)
    if relOff + targetW > 4 then return none
    let thmName := if targetW == 2 && relOff % 2 == 0 then ``pointsTo32_split16 else ``pointsTo32_split8
    let hSplit := mkApp2 (mkConst thmName) a v
    let eqTy ← inferType hSplit
    let some (_, _, splitRhs) := eqTy.eq? | return none
    return some (splitRhs, hSplit, false)
  if atom.isAppOfArity ``Arm64.pointsTo16 2 && targetW == 1 then
    let a := atom.getArg! 0
    let v := atom.getArg! 1
    let (aNorm, _) ← SepSolver.normAddrMeta a
    let (bCell, oCell) ← sepAddrBaseOff aNorm
    if !(bTarget == bCell || (← withReducibleAndInstances (isDefEq bTarget bCell))) then
      return none
    let relOff := (oTarget + 2 ^ 64 - oCell) % (2 ^ 64)
    if relOff + 1 > 2 then return none
    let hSplit := mkApp2 (mkConst ``pointsTo16_split8) a v
    let eqTy ← inferType hSplit
    let some (_, _, splitRhs) := eqTy.eq? | return none
    return some (splitRhs, hSplit, false)
  if atom.isAppOfArity ``Arm64.stackFrameAt 2 || atom.isAppOfArity ``Arm64.memRegion 2 then
    let thmName? : Option Name := match targetW with
      | 1 => some ``memRegion_one
      | 2 => some ``memRegion_two
      | 4 => some ``memRegion_four
      | 8 => some ``memRegion_eight
      | _ => none
    let some thmName := thmName? | return none
    let disch := SepSolver.liftTacDisch (fun φ => do
      proveOmegaBoundedTerm? φ [← `(tactic| bv_omega), ← `(tactic| omega)] [.strict, .transitive] 20000)
    let (p, nExpr, hPrefix?) ←
      if atom.isAppOfArity ``Arm64.stackFrameAt 2 then
        let sp := atom.getArg! 0
        let nExpr := atom.getArg! 1
        let pow64 ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]
        let some hn ← disch (← mkAppM ``LE.le #[nExpr, pow64]) | return none
        let hStack := mkApp3 (mkConst ``stackFrameAt_eq_memRegion) sp nExpr hn
        let eqTy ← inferType hStack
        let some (_, _, memRegExpr) := eqTy.eq? | return none
        pure (memRegExpr.getArg! 0, nExpr, some hStack)
      else
        pure (atom.getArg! 0, atom.getArg! 1, none)
    let wExpr := toExpr targetW
    let some (subRhs, hSub) ← SepSolver.splitMemRegionSubblock? disch p nExpr targetEa wExpr
      | return none
    let hCell := mkApp (mkConst thmName) targetEa
    let cellEqTy ← inferType hCell
    let some (_, _, cellRhs) := cellEqTy.eq? | return none
    let some (finalRhs, hStep) ← SepSolver.rewriteAtomAtEq? subRhs 0 cellRhs hCell
      | return none
    let hSubCell ← mkEqTrans hSub hStep
    let hFinal ← match hPrefix? with
      | some hPre => mkEqTrans hPre hSubCell
      | none => pure hSubCell
    return some (finalRhs, hFinal, true)
  return none

private def tryAutoFocusCell? (targetEa : Expr) (targetW : Nat) : TacticM Bool := do
  let (eaNorm, _) ← SepSolver.normAddrMeta targetEa
  let (bTarget, oTarget) ← sepAddrBaseOff eaNorm
  let atomConsts : Array Name := match targetW with
    | 1 => #[``Arm64.pointsTo8]
    | 2 => #[``Arm64.pointsTo16]
    | 4 => #[``Arm64.pointsTo32, ``Arm64.pointsTo32RO]
    | 8 => #[``Arm64.pointsTo64, ``Arm64.pointsTo64RO]
    | _ => #[]
  let mut anyChanged := false
  for _ in [0:4] do
    let g ← getMainGoal
    let stepRes? : Option (MVarId × Bool) ← g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      if !ty.isAppOfArity ``SepWP 6 then return none
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let s := ty.getArg! 2
      let P := SepSolver.stripMData (ty.getArg! 3)
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let atoms := SepSolver.atoms P
      for atom in atoms do
        if atomConsts.any (fun c => atom.isAppOfArity c 2) then
          let (aNorm, _) ← SepSolver.normAddrMeta (atom.getArg! 0)
          let (bCell, oCell) ← sepAddrBaseOff aNorm
          if (bTarget == bCell || (← withReducibleAndInstances (isDefEq bTarget bCell))) &&
             oTarget == oCell then
            return none
      for h : i in [0:atoms.size] do
        let atom := atoms[i]
        if let some (splitRhs, hSplit, hasExists) ←
            splitAtomForTarget? atom eaNorm bTarget oTarget targetW then
          if let some (P1, h1) ← SepSolver.rewriteAtomAtEq? P i splitRhs hSplit then
            let (P2, h2?) ← SepSolver.normSepPropMeta P1
            let hEq ← match h2? with
              | some h2 => mkEqTrans h1 h2
              | none => pure h1
            let nextTy := mkApp6 (mkConst ``SepWP) prog targetPc s P2 post oom
            let gNext ← mkFreshExprMVar nextTy
            let prf := mkAppN (mkConst ``SepWP.congr_pre)
              #[prog, targetPc, s, P2, P, post, oom, (← mkEqSymm hEq), gNext]
            g.assign prf
            return some (gNext.mvarId!, hasExists)
      return none
    match stepRes? with
    | none => break
    | some (gNext, hasExists) =>
      replaceMainGoal [gNext]
      anyChanged := true
      if hasExists then
        let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_pull_exists)))
  return anyChanged

private def tryAutoFocusSubwordOrRegion? (instExpr : Expr) : TacticM Bool := do
  let some (amExpr, elemBytes, isPair) := extractLoadStoreAccesses? instExpr
    | return false
  let g ← getMainGoal
  let ea? ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return none
    evalLoadStoreEffAddrDiag? (ty.getArg! 2) amExpr
  let some ea0 := ea? | return false
  let c1 ← tryAutoFocusCell? ea0 elemBytes
  let c2 ←
    if isPair then
      let ea1 ← (← getMainGoal).withContext do
        mkAppM ``HAdd.hAdd #[ea0, mkCanonBitVecLit 64 elemBytes]
      tryAutoFocusCell? ea1 elemBytes
    else
      pure false
  return c1 || c2

set_option maxHeartbeats 400000 in
/-- Internal helper: take a single `SepWP` step, returning a `WpStepOutcome` classifying whether
    the instruction was straight-line, a subroutine call (`BL`/`BLR`), a return (`RET`), or an
    unconditional branch (`B`). -/
def wpStepCoreWithOutcome (stepFailed : Option (IO.Ref (Array Expr)) := none)
    (tacticName : String := "wp_step") (isSingleStep : Bool := false)
    (resolvedItePcRef : Option (IO.Ref (Option Expr)) := none) :
    TacticM WpStepOutcome := do
  let _ ← getOrCreateWpNormSimpCacheRef
  let (_, _, pcExpr0) ← getSepWPStateAndPC
  let wasIte0 := (iteApp? pcExpr0).isSome
  if let some (c, _, _) := iteApp? pcExpr0 then
    let resolved? ← match ← resolveIteCondStep? c stepFailed with
      | some res => pure (some res)
      | none =>
        if isSingleStep && stepFailed.isNone then
          resolveIteCondOnStepFallback? c
        else
          pure none
    let some (condTrue, propTy, prf) := resolved?
      | throwUnresolvedBranchStepError tacticName pcExpr0
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
        throwError "wp_step: condition proof type mismatch"
    if detIte then
      let g ← getMainGoal
      let g' ← g.assert hId.getId propTy prf
      let (_, g'') ← g'.intro1P
      replaceMainGoal [g'']
      let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
        try simp (config := { decide := true }) only [
          beq_iff_eq, bne_iff_ne, Classical.not_not,
          wp_norm, arm64_norm] at $hId:ident
        try wp_norm_state
      ))))
    else
      throwUnresolvedBranchStepError tacticName pcExpr0
  let (progExpr, _targetPcExpr, pcExpr) ← getSepWPStateAndPC
  if (iteApp? pcExpr).isSome then
    throwUnresolvedBranchStepError tacticName pcExpr
  if wasIte0 then
    if let some ref := resolvedItePcRef then
      ref.set (some pcExpr)
  let g0 ← getMainGoal
  let savedFetch ← saveState
  let fetchResOpt : Option (Expr × Expr) ← g0.withContext do
    let savedGoals ← getGoals
    let instMVar ← mkFreshExprMVar (mkConst ``Instr)
    let someInst ← mkAppM ``Option.some #[instMVar]
    let fetchLhs := mkApp2 (mkConst ``Program.fetch) progExpr pcExpr
    let fetchGoalTy ← mkEq fetchLhs someInst
    let fetchGoal ← mkFreshExprMVar fetchGoalTy
    setGoals [fetchGoal.mvarId!]
    -- Each fallback sits in its own `else do` block so it only runs when the previous ones failed
    -- (`else if ← c` would hoist `c` before the whole `if` chain and run it unconditionally).
    let ok ←
      if ← tryCloseFetchFromHasCode then
        Pure.pure true
      else do
      if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_assumption))) then
        Pure.pure true
      else do
      if ← skipNormFetchAt progExpr pcExpr then
        -- A pair-step or call-step site: skip the expensive `arm64_norm` fetch fallback.
        Pure.pure false
      else do
      if !(← fastProgFetchNone? progExpr pcExpr) &&
              ((← evalBitVecLit? pcExpr).isSome || (← evalPCBaseOff? pcExpr).isSome || pcExpr.isFVar) then
        tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (
          (conv => lhs; simp (config := { decide := true }) only [arm64_norm]);
          rfl))))
      else
        Pure.pure false
    setGoals savedGoals
    if ok then
      return some (← instantiateMVars instMVar, ← instantiateMVars fetchGoal)
    else
      return none
  let some (instExpr, fetchPrf) := fetchResOpt
    | do
      restoreState savedFetch
      if ← tryPairStepHook tacticName progExpr pcExpr then
        return .steppedPair
      if ← tryPairStepHook tacticName progExpr pcExpr "callStep" then
        return .steppedCall
      throwCouldNotFetchDecodeError tacticName pcExpr
  let opExpr := instExpr
  let isBl := instExpr.isAppOfArity ``Instr.bl 1 || instExpr.isAppOfArity ``Instr.blr 1
  let isRet := instExpr.isAppOfArity ``Instr.ret 1
  let isUncondB := instExpr.isAppOfArity ``Instr.b 1
  let outcome : WpStepOutcome :=
    if isBl then .steppedCall
    else if isRet then .steppedRet
    else if isUncondB then .steppedBranch
    else .steppedNormal
  trace[wp.pc] "WP_PC|decl={(← Term.getDeclName?).getD .anonymous}|prog={progExpr}|pc={pcExpr}|op={opExpr.getAppFn}|inst={instExpr}"
  -- First-class 32-bit cells: try the `↦₃₂` rules first; the 64-bit-half rules below are fallbacks.
  let isW32Access :=
    (instExpr.isAppOfArity ``Instr.ldr 5 && isMemSizeConst (instExpr.getArg! 1) 4) ||
    (instExpr.isAppOfArity ``Instr.str 3 && isMemSizeConst (instExpr.getArg! 0) 4) ||
    (instExpr.isAppOfArity ``Instr.ldp 5 &&
      instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
      instExpr.getArg! 1 == mkConst ``Bool.false) ||
    (instExpr.isAppOfArity ``Instr.stp 4 && instExpr.getArg! 0 == mkConst ``RegWidth.W32)
  let savedBeforeDispatch ← saveState
  let savedMsgsBeforeDispatch ← Core.getMessageLog
  let dispatchStep : TacticM Unit := do
    if ← pure isW32Access <&&> sepWPHasPointsTo32 isSingleStep then
      if ← tryTacticCatchRuntimeBool (wpStep32Core instExpr fetchPrf) then
        return
    if instExpr.isAppOfArity ``Instr.ldr 5 &&
       instExpr.getArg! 0 == mkConst ``RegWidth.W64 &&
       isMemSizeConst (instExpr.getArg! 1) 8 &&
       instExpr.getArg! 2 == mkConst ``Bool.false then
      let rt := instExpr.getArg! 3
      let addr := instExpr.getArg! 4
      if !(← tryStepLdr64Direct? pcExpr rt addr fetchPrf) then
        evalTactic (← `(tactic| (
          apply SepWP.step_ldr64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            isMemSizeConst (instExpr.getArg! 1) 1 &&
            instExpr.getArg! 2 == mkConst ``Bool.false then
      let runLdr8 : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldr8
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      let stepped8 ← tryTacticCatchRuntimeBool runLdr8
      if !stepped8 then
        let stepped8_64 ← tryTacticCatchRuntimeBool do
          evalTactic (← `(tactic| (
            apply SepWP.step_ldr8_64
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
          closeFetchSubgoal (some fetchPrf)
          evalTactic (← `(tactic| (
            wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_sep_access
            wp_focus_close wp_norm_lhs
          )))
        if !stepped8_64 then
          if !(← tryStepPureDirect? pcExpr instExpr fetchPrf) then
            evalTactic (← `(tactic| (
              apply SepWP.step_pure
              wp_focus_close wp_norm_lhs
              wp_focus_close wp_norm_lhs
            )))
            closeFetchSubgoal (some fetchPrf)
            evalTactic (← `(tactic| (
              wp_focus_close wp_norm_lhs
              wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
            )))
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            isMemSizeConst (instExpr.getArg! 1) 1 &&
            instExpr.getArg! 2 == mkConst ``Bool.true then
      let runLdrsb : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldrsb
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      let stepped8 ← tryTacticCatchRuntimeBool runLdrsb
      if !stepped8 then
        if !(← tryStepPureDirect? pcExpr instExpr fetchPrf) then
          evalTactic (← `(tactic| (
            apply SepWP.step_pure
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
          closeFetchSubgoal (some fetchPrf)
          evalTactic (← `(tactic| (
            wp_focus_close wp_norm_lhs
            wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          )))
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 1 then
      let mId ← freshIdent `m
      let stepped8 ← tryTacticCatchRuntimeBool do
        evalTactic (← `(tactic| (
          apply SepWP.step_str8
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      if !stepped8 then
        evalTactic (← `(tactic| (
          apply SepWP.step_str8_64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            isMemSizeConst (instExpr.getArg! 1) 2 &&
            instExpr.getArg! 2 == mkConst ``Bool.false then
      let runLdr16 : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldr16
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      let stepped16 ← tryTacticCatchRuntimeBool runLdr16
      if !stepped16 then
        let steppedBytes ← tryTacticCatchRuntimeBool do
          evalTactic (← `(tactic| (
            apply SepWP.step_ldrh_bytes
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
          closeFetchSubgoal (some fetchPrf)
          evalTactic (← `(tactic| (
            wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_sep_access
            wp_focus_close wp_sep_access
            wp_focus_close wp_norm_lhs
          )))
        if !steppedBytes then
          if !(← tryStepPureDirect? pcExpr instExpr fetchPrf) then
            evalTactic (← `(tactic| (
              apply SepWP.step_pure
              wp_focus_close wp_norm_lhs
              wp_focus_close wp_norm_lhs
            )))
            closeFetchSubgoal (some fetchPrf)
            evalTactic (← `(tactic| (
              wp_focus_close wp_norm_lhs
              wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
            )))
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            isMemSizeConst (instExpr.getArg! 1) 2 &&
            instExpr.getArg! 2 == mkConst ``Bool.true then
      let runLdrsh16 : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldrsh16
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      let stepped16 ← tryTacticCatchRuntimeBool runLdrsh16
      if !stepped16 then
        let steppedBytes ← tryTacticCatchRuntimeBool do
          evalTactic (← `(tactic| (
            apply SepWP.step_ldursh_bytes
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
          closeFetchSubgoal (some fetchPrf)
          evalTactic (← `(tactic| (
            wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_sep_access
            wp_focus_close wp_sep_access
            wp_focus_close wp_norm_lhs
          )))
        if !steppedBytes then
          if !(← tryStepPureDirect? pcExpr instExpr fetchPrf) then
            evalTactic (← `(tactic| (
              apply SepWP.step_pure
              wp_focus_close wp_norm_lhs
              wp_focus_close wp_norm_lhs
            )))
            closeFetchSubgoal (some fetchPrf)
            evalTactic (← `(tactic| (
              wp_focus_close wp_norm_lhs
              wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
            )))
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 2 then
      let mId ← freshIdent `m
      let stepped16 ← tryTacticCatchRuntimeBool do
        evalTactic (← `(tactic| (
          apply SepWP.step_str16
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      if !stepped16 then
        evalTactic (← `(tactic| (
          apply SepWP.step_strh_bytes
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 8 then
      let rt := instExpr.getArg! 1
      let addr := instExpr.getArg! 2
      if !(← tryStepStr64Direct? pcExpr rt addr fetchPrf) then
        let mId ← freshIdent `m
        evalTactic (← `(tactic| (
          apply SepWP.step_str64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
    else if instExpr.isAppOfArity ``Instr.stp 4 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W64 then
      let mId ← freshIdent `m
      evalTactic (← `(tactic| (
        apply SepWP.step_stp64
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
        intro $mId:ident
        try wp_norm_state
      )))
    else if instExpr.isAppOfArity ``Instr.ldp 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W64 &&
            instExpr.getArg! 1 == mkConst ``Bool.false then
      evalTactic (← `(tactic| (
        apply SepWP.step_ldp64
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.ldrSimd 3 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      evalTactic (← `(tactic| (
        apply SepWP.step_ldrSimd128
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.strSimd 3 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      let mId ← freshIdent `m
      evalTactic (← `(tactic| (
        apply SepWP.step_strSimd128
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
        intro $mId:ident
        try wp_norm_state
      )))
    else if instExpr.isAppOfArity ``Instr.ldpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      evalTactic (← `(tactic| (
        apply SepWP.step_ldpSimd128
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.stpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      let mId ← freshIdent `m
      evalTactic (← `(tactic| (
        apply SepWP.step_stpSimd128
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
        intro $mId:ident
        try wp_norm_state
      )))
    else if instExpr.isAppOfArity ``Instr.dcZva 1 then
      let mId ← freshIdent `m
      let g ← getMainGoal
      let (hasBytes, hasPt64) ← g.withContext do
        let ty ← instantiateMVars (← g.getType)
        let P := ty.getArg! 3
        return ((P.find? (·.isConstOf ``Arm64.pointsToBytes)).isSome,
                (P.find? (·.isConstOf ``Arm64.pointsTo64)).isSome)
      let runBytes : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_dcZva_bytes
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close (first | wp_dc_zva_ea | wp_assumption | wp_norm_lhs | with_reducible rfl)
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      let runWords : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_dcZva
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close (first | wp_dc_zva_ea | wp_assumption | wp_norm_lhs | with_reducible rfl)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      if hasBytes && !hasPt64 then
        runBytes
      else if !hasBytes then
        runWords
      else
        if !(← tryTactic runBytes) then
          runWords
    else if instExpr.isAppOfArity ``Instr.ldrSimd 3 &&
            (instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 ||
             instExpr.getArg! 0 == mkConst ``SimdMemSize.S32) then
      -- `LDR Dt` / `LDR St`: single `SepLoad64` / `SepLoad32` cell, zero-extended into `Vt`.
      let thm := mkIdent (if instExpr.getArg! 0 == mkConst ``SimdMemSize.D64
        then ``SepWP.step_ldrSimd64 else ``SepWP.step_ldrSimd32)
      evalTactic (← `(tactic| (
        apply $thm:ident
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.strSimd 3 &&
            (instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 ||
             instExpr.getArg! 0 == mkConst ``SimdMemSize.S32) then
      -- `STR Dt` / `STR St`: single `SepStore64` / `SepStore32` cell from the low bits of `Vt`.
      let mId ← freshIdent `m
      let thm := mkIdent (if instExpr.getArg! 0 == mkConst ``SimdMemSize.D64
        then ``SepWP.step_strSimd64 else ``SepWP.step_strSimd32)
      evalTactic (← `(tactic| (
        apply $thm:ident
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
        intro $mId:ident
        try wp_norm_state
      )))
    else if instExpr.isAppOfArity ``Instr.ldpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 then
      evalTactic (← `(tactic| (
        apply SepWP.step_ldpSimd64
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.stpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 then
      let mId ← freshIdent `m
      evalTactic (← `(tactic| (
        apply SepWP.step_stpSimd64
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
        intro $mId:ident
        try wp_norm_state
      )))
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            isMemSizeConst (instExpr.getArg! 1) 4 &&
            instExpr.getArg! 2 == mkConst ``Bool.false then
      let addrArg := instExpr.getArg! 4
      let hiFirst ← preferHi64ForAddr addrArg
      let runLo : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldr32_64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      let runHi : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldr32_hi64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      if hiFirst then
        if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runHi)) then
          runLo
      else
        if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runLo)) then
          runHi
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W64 &&
            isMemSizeConst (instExpr.getArg! 1) 4 &&
            instExpr.getArg! 2 == mkConst ``Bool.true then
      let addrArg := instExpr.getArg! 4
      let hiFirst ← preferHi64ForAddr addrArg
      let runLo : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldrsw32_64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      let runHi : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_ldrsw32_hi64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
        )))
      if hiFirst then
        if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runHi)) then
          runLo
      else
        if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runLo)) then
          runHi
    else if instExpr.isAppOfArity ``Instr.ldp 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            instExpr.getArg! 1 == mkConst ``Bool.false then
      evalTactic (← `(tactic| (
        apply SepWP.step_ldp32_64
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 4 then
      let addrArg := instExpr.getArg! 2
      let hiFirst ← preferHi64ForAddr addrArg
      let mId ← freshIdent `m
      let runLo : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_str32_64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      let runHi : TacticM Unit := do
        evalTactic (← `(tactic| (
          apply SepWP.step_str32_hi64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      if hiFirst then
        if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runHi)) then
          runLo
      else
        if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runLo)) then
          runHi
    else if instExpr.isAppOfArity ``Instr.stp 4 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 then
      let mId ← freshIdent `m
      let steppedAligned ← tryTacticCatchRuntimeBool do
        evalTactic (← `(tactic| (
          apply SepWP.step_stp32_64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      if !steppedAligned then
        evalTactic (← `(tactic| (
          apply SepWP.step_stp32_hi_lo64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
    else if instExpr.isAppOfArity ``Instr.ldarStlr 4 &&
            isMemSizeConst (instExpr.getArg! 0) 4 &&
            instExpr.getArg! 1 == mkConst ``Bool.true then
      evalTactic (← `(tactic| (
        apply SepWP.step_ldar32_64
        wp_focus_close wp_norm_lhs
        wp_focus_close wp_norm_lhs
      )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.ldxr 4 &&
            (isMemSizeConst (instExpr.getArg! 0) 8 || isMemSizeConst (instExpr.getArg! 0) 4) then
      -- `LDXR`/`LDAXR` (single-threaded model: plain load, `SepWP.step_ldxr64`/`step_ldxr32`).
      if isMemSizeConst (instExpr.getArg! 0) 8 then
        evalTactic (← `(tactic| (
          apply SepWP.step_ldxr64
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
      else
        evalTactic (← `(tactic| (
          apply SepWP.step_ldxr32
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
        )))
      closeFetchSubgoal (some fetchPrf)
      evalTactic (← `(tactic| (
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_norm_lhs
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
        wp_focus_close wp_sep_access
        wp_focus_close wp_norm_lhs
      )))
    else if instExpr.isAppOfArity ``Instr.stxr 5 &&
            (isMemSizeConst (instExpr.getArg! 0) 8 || isMemSizeConst (instExpr.getArg! 0) 4) then
      -- `STXR`/`STLXR`: try 4-instruction LL/SC retry loop (`step_stxr{64,32}_retry2`),
      -- then 3-instruction LL/SC retry loop (`step_stxr{64,32}_retry1`), then single-step
      -- `step_stxr{64,32}` (which requires `s.exclWillFail = false`).
      let mId ← freshIdent `m
      let is64 := isMemSizeConst (instExpr.getArg! 0) 8
      let runRetry2 : TacticM Unit := do
        if is64 then
          evalTactic (← `(tactic| (
            apply SepWP.step_stxr64_retry2
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
        else
          evalTactic (← `(tactic| (
            apply SepWP.step_stxr32_retry2
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| wp_focus_close wp_norm_lhs))
        closeFetchSubgoal none
        evalTactic (← `(tactic| wp_focus_close wp_norm_lhs))
        closeFetchSubgoal none
        evalTactic (← `(tactic| wp_focus_close wp_norm_lhs))
        closeFetchSubgoal none
        evalTactic (← `(tactic| (
          wp_focus_close wp_norm_lhs
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      let runRetry1 : TacticM Unit := do
        if is64 then
          evalTactic (← `(tactic| (
            apply SepWP.step_stxr64_retry1
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
        else
          evalTactic (← `(tactic| (
            apply SepWP.step_stxr32_retry1
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| wp_focus_close wp_norm_lhs))
        closeFetchSubgoal none
        evalTactic (← `(tactic| wp_focus_close wp_norm_lhs))
        closeFetchSubgoal none
        evalTactic (← `(tactic| (
          wp_focus_close wp_norm_lhs
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      let runSingle : TacticM Unit := do
        if is64 then
          evalTactic (← `(tactic| (
            apply SepWP.step_stxr64
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
        else
          evalTactic (← `(tactic| (
            apply SepWP.step_stxr32
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
        closeFetchSubgoal (some fetchPrf)
        evalTactic (← `(tactic| (
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          wp_focus_close wp_norm_lhs
          wp_focus_close wp_sep_access
          wp_focus_close wp_norm_lhs
          intro $mId:ident
          try wp_norm_state
        )))
      if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runRetry2)) then
        if !(← tryTacticCatchRuntimeBool (withHeartbeatCap 50000 runRetry1)) then
          runSingle
    else
      let condCmpRule? : Option Name :=
        if instExpr.isAppOfArity ``Instr.condCompareReg 6 then
          some (if instExpr.getArg! 1 == mkConst ``Bool.true
            then ``SepWP.step_ccmp_reg else ``SepWP.step_ccmn_reg)
        else if instExpr.isAppOfArity ``Instr.condCompareImm 6 then
          some (if instExpr.getArg! 1 == mkConst ``Bool.true
            then ``SepWP.step_ccmp_imm else ``SepWP.step_ccmn_imm)
        else none
      -- `CCMP`/`CCMN`: keep the symbolic condition inside the flags (`SepWP.step_ccmp_*`).
      let steppedCondCmp ← match condCmpRule? with
        | none => Pure.pure false
        | some rule => tryTacticCatchRuntimeBool do
          let ruleId := mkIdent rule
          evalTactic (← `(tactic| (
            apply $ruleId:ident
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
          closeFetchSubgoal (some fetchPrf)
          evalTactic (← `(tactic| wp_focus_close wp_norm_lhs))
      if !steppedCondCmp then
        if !(← tryStepPureDirect? pcExpr instExpr fetchPrf) then
          evalTactic (← `(tactic| (
            apply SepWP.step_pure
            wp_focus_close wp_norm_lhs
            wp_focus_close wp_norm_lhs
          )))
          closeFetchSubgoal (some fetchPrf)
          evalTactic (← `(tactic| (
            wp_focus_close wp_norm_lhs
            wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
          )))
  let stepRes? : Except Exception Unit ←
    try
      MonadRuntimeException.tryCatchRuntimeEx
        (do
          dispatchStep
          return .ok ())
        (fun ex => do
          restoreState savedBeforeDispatch
          Core.setMessageLog savedMsgsBeforeDispatch
          return .error ex)
    catch ex =>
      restoreState savedBeforeDispatch
      Core.setMessageLog savedMsgsBeforeDispatch
      Pure.pure (.error ex)
  match stepRes? with
  | .ok () => return outcome
  | .error ex =>
    let retryOk ←
      if isSingleStep && proofLib.wpAutoSubwordFocus.get (← getOptions) then
        let savedRetry ← saveState
        let savedRetryMsgs ← Core.getMessageLog
        let ok ← tryTacticCatchRuntimeBool do
          if ← pure isW32Access <&&> tryTacticCatchRuntimeBool (wpStep32Core instExpr fetchPrf) then
            return
          if !(← tryAutoFocusSubwordOrRegion? instExpr) then
            throwError "no autofocus"
          dispatchStep
        if !ok then
          restoreState savedRetry
          Core.setMessageLog savedRetryMsgs
        pure ok
      else
        pure false
    if retryOk then
      return outcome
    let g ← getMainGoal
    if MaxRecDepthDiag.isMaxRecDepthEx ex then
      -- Name the instruction, PC and failing sub-step, and point at the deep term instead of
      -- the generic step-rule hints (which do not apply to a recursion-depth failure).
      let pcStr ← g.withContext (MaxRecDepthDiag.withFreshRecDepth (ppExprTruncated pcExpr 80 6))
      let opStr ← g.withContext (MaxRecDepthDiag.withFreshRecDepth (ppExprTruncated opExpr 120 8))
      let detailLine := (((← ex.toMessageData.toString).splitOn "\n").headD "").trimAsciiEnd.toString
      let detailLine := if detailLine.endsWith ":" then (detailLine.dropEnd 1).toString else detailLine
      let report ← MaxRecDepthDiag.maxRecDepthContextReport g
        m!"check hypotheses that the step normalization rewrites with (register/flag/memory equations such as `s.readReg64 r = v`, `s.pc = ...`): restate them with a small right-hand side or `clear` the ones this step does not need"
      -- A plain (non-runtime) error, like every other `wp_step` failure, so callers that
      -- `try`/`first` a step still fall back as before.
      throw <| .error (← getRef) <| .tagged MaxRecDepthDiag.diagTag <|
        m!"wp_step: maximum recursion depth (`maxRecDepth`) reached while stepping instruction `{opStr}` at pc {pcStr}\nfailing sub-step: {detailLine}" ++ report
    let (eaMsg, hintMsg) ←
      if let some amExpr := extractLoadStoreAddrMode? instExpr then
        let ea? ← g.withContext do
          let ty := (← instantiateMVars (← g.getType)).consumeMData
          if ty.isAppOfArity ``SepWP 6 then
            evalLoadStoreEffAddrDiag? (ty.getArg! 2) amExpr
          else
            pure none
        let eaLine := match ea? with
          | some ea => m!"\neffective address: `{ea}`"
          | none => m!"\naddressing mode: `{amExpr}`"
        let hintLine :=
          m!"\nhint: if the target cell is in context at a different width (`↦₆₄` vs `↦₈`/`↦₁₆`/`↦₃₂`) or inside a byte slice/region (`↦ₛ`, `↦ᵣ`, `memRegion`, `stackFrameAt`), prove the slice length bound (`off + w ≤ bs.length` for `wp_sep_access`), split the cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), or use `wp_sym_steps`"
        pure (eaLine, hintLine)
      else
        pure (m!"", m!"")
    g.withContext do
      let lazyDiag := MessageData.ofLazyM (es := #[opExpr, instExpr, pcExpr]) do
        let ty := (← instantiateMVars (← g.getType)).consumeMData
        let P := if ty.isAppOfArity ``SepWP 6 then SepSolver.stripMData (ty.getArg! 3) else mkConst ``SepProp.emp
        let ptAtoms := (SepSolver.atoms P).filter fun a =>
          !a.isAppOfArity ``SepProp.pure 1 && !a.isConstOf ``SepProp.emp
        let atomsMsg := if ptAtoms.isEmpty then m!"(none)"
          else MessageData.joinSep (ptAtoms.toList.map (fun a => m!"{a}")) m!", "
        return m!"wp_step: no step rule succeeded for instruction `{opExpr}` (full: `{instExpr}`) at PC `{pcExpr}`{eaMsg}\nspatial context points-to atoms: {atomsMsg}\n(detail: {ex.toMessageData}){hintMsg}"
      throwError lazyDiag

/-- Internal helper: take a single `SepWP` step, returning `true` if the instruction was `bl`
    (`.b true offset`) so `wp_steps` knows to pause at the callee entry. -/
def wpStepCore : TacticM Bool := do
  return (← wpStepCoreWithOutcome) == .steppedCall

/-- Take a single forward symbolic execution step on a `SepWP` goal. -/
elab "wp_step" : tactic => do
  let _ ← wpStepCoreWithOutcome (isSingleStep := true)


end ProofLib
