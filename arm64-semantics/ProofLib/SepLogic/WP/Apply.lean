/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.WP.ControlTactics
public import ProofLib.SepLogic.WP.FrameAuto
import Arm64.Trusted.Spec.SepLogic

/-!
# Contract Lookup for Subroutine Calls

Implements `@[wp_spec]` (`DiscrTree`-indexed `subroutine_ok prog addr spec` registration with
canonicalized bit-vector address keys), `wp_apply` / `wp_apply?` (automatic contract lookup,
parameter instantiation, and `wp_call` or `FrameHook`-driven application at the current PC),
and `wp_spec_intro` (introducing matching `@[wp_spec]` contracts into the local context before
entry generalization). Set `set_option trace.ProofLib.wpApply true` to trace candidate matching.
-/

namespace ProofLib

open Arm64
open Lean Elab Tactic Meta

public meta section

namespace WpApply

initialize registerTraceClass `ProofLib.wpApply

/-! ## Contract database -/

/-- A registered contract: declaration name and the `DiscrTree` keys of its callee address. -/
structure SpecEntry where
  declName : Name
  keys : Array DiscrTree.Key
  deriving Inhabited

/-- `@[wp_spec]` lemmas indexed by callee address (scoped: `local` / `scoped` attributes work). -/
initialize wpSpecExt : SimpleScopedEnvExtension SpecEntry (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun d e => d.insertKeyValue e.keys e.declName
    initial := {}
  }

/-- `(width, value)` of a bit-vector numeral written `BitVec.ofNat w n`, `n#w` or
    `OfNat.ofNat (BitVec w) n _`. -/
def bvLit? (e : Expr) : Option (Nat × Nat) :=
  let e := e.consumeMData
  if let some r := evalBitVecLitPure? e then some r
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty := (e.getArg! 0).consumeMData
    if ty.isAppOfArity ``BitVec 1 then
      match evalNatLitPure? (ty.getArg! 0), evalNatLitPure? (e.getArg! 1) with
      | some w, some v => some (w, v % (2 ^ w))
      | _, _ => none
    else none
  else none

/-- Rewrite every bit-vector numeral of `e` to the single form `BitVec.ofNat w v` (raw literals),
    so that index keys agree however the numeral was written. Only used to compute keys. -/
def canonLits (e : Expr) : Expr :=
  e.replace fun t =>
    match bvLit? t with
    | some (w, v) => some (mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit w) (mkRawNatLit v))
    | none => none

def subOkView? (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.subroutine_ok 4 then some (e.getArg! 1, e.getArg! 2, e.getArg! 3)
  else none

def binderNames : Expr → Array Name
  | .forallE n _ b _ => #[n] ++ binderNames b
  | .mdata _ b => binderNames b
  | _ => #[]

/-- Open a contract type `∀ xs, ... subroutine_ok prog addr spec` into metavariables `xs` and the
    `(prog, addr, spec)` view, unfolding at most `fuel` definitions (`Program.subroutineOk`,
    `fn_subroutine_ok`, user `def`s that hide a `∀ ..., subroutine_ok ...`). The binders of
    `subroutine_ok` itself are never opened. -/
partial def openContractType (ty : Expr) (fuel : Nat := 6) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr × Expr) := do
  let names := binderNames ty
  let (xs, bis, body) ← forallMetaTelescope ty
  for x in xs, n in names do
    x.mvarId!.setUserName n
  if let some (p, a, s) := subOkView? body then return (xs, bis, p, a, s)
  if fuel == 0 then throwError "not a `subroutine_ok` contract:{indentExpr body}"
  let body ← whnfCore (← instantiateMVars body)
  if let some (p, a, s) := subOkView? body then return (xs, bis, p, a, s)
  let some body' ← unfoldDefinition? body
    | throwError "not a `subroutine_ok` contract:{indentExpr body}"
  let (ys, bis', p, a, s) ← openContractType body' (fuel - 1)
  return (xs ++ ys, bis ++ bis', p, a, s)

/-- The form of an address used for indexing: a ground address (a numeral, or a constant /
    sum that evaluates to one) becomes the numeral `BitVec.ofNat w v`; otherwise numerals inside
    it are canonicalized (`canonLits`). -/
def keyAddr (a : Expr) : MetaM Expr := do
  let a ← instantiateMVars a
  if !a.hasExprMVar && !a.hasFVar then
    if let some (w, v) ← evalBitVecLit? a then
      return mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit w) (mkRawNatLit v)
  return canonLits a

/-- `DiscrTree` keys of a contract declaration (its callee address). -/
def specKeys (declName : Name) : MetaM (Array DiscrTree.Key) := do
  let info ← getConstInfo declName
  let (_, _, _, addr, _) ← openContractType info.type
  DiscrTree.mkPath (← keyAddr addr)

initialize registerBuiltinAttribute {
  name := `wp_spec
  descr := "subroutine contract (`subroutine_ok prog addr spec`) used by `wp_apply` / `wp_spec_intro`, indexed by its callee address"
  applicationTime := .afterTypeChecking
  add := fun declName _stx kind => do
    let keys ← try (specKeys declName).run' catch _ =>
      throwError "@[wp_spec]: the conclusion of `{declName}` is not a `subroutine_ok prog addr spec` contract (after its binders and unfolding `Program.subroutineOk`-style wrappers)"
    wpSpecExt.add { declName, keys } kind
}

/-- Global contracts whose address key unifies with `pc` (most specific first, as `DiscrTree`). -/
def lookupGlobal (pc : Expr) : MetaM (Array Name) := do
  let d := wpSpecExt.getState (← getEnv)
  let hits ← d.getUnify (← keyAddr pc)
  return hits.reverse

def allGlobal : MetaM (Array Name) := do
  return (wpSpecExt.getState (← getEnv)).values

/-! ## Contract Instantiation -/

/-- How a candidate's callee address relates to the current PC. -/
inductive AddrMatch where
  /-- unified / proved equal without tactics -/
  | yes
  /-- not decided cheaply: let `wp_call` try (it can use local address equations) -/
  | maybe
  /-- provably different base or offset -/
  | no
  deriving BEq, Repr

/-- Decide (without tactics) whether contract address `a` (may contain metavariables of the
    contract's parameters, which get assigned) denotes the current PC `pc`. -/
def matchAddr (a pc : Expr) : MetaM AddrMatch := do
  let a ← instantiateMVars a
  if ← withReducibleAndInstances (isDefEq a pc) then return .yes
  let a ← instantiateMVars a
  if !a.hasExprMVar then
    if (← proveSepAddrEqMeta? pc a).isSome then return .yes
  let (aN, _) ← SepSolver.normAddrMeta a
  let (pN, _) ← SepSolver.normAddrMeta pc
  if ← withReducibleAndInstances (isDefEq aN pN) then return .yes
  let (b1, o1) ← sepAddrBaseOff (← instantiateMVars aN)
  let (b2, o2) ← sepAddrBaseOff pN
  if !b1.hasExprMVar && (b1 == b2 || (← withReducible (isDefEq b1 b2))) && o1 != o2 then
    return .no
  return .maybe

/-- `(T, tac)` for a binder type `autoParam T tac`, decoding the tactic the way the elaborator
    does (`Lean.Elab.evalSyntaxConstant`). -/
def autoParamTac? (ty : Expr) : MetaM (Option (Expr × Syntax)) := do
  let ty := ty.consumeMData
  unless ty.isAppOfArity ``autoParam 2 do return none
  let .const tacDecl _ := ty.appArg! | return none
  match Lean.Elab.evalSyntaxConstant (← getEnv) (← getOptions) tacDecl with
  | .ok stx => return some (ty.appFn!.appArg!, stx)
  | .error _ => return none

/-- Run `tac` on a fresh goal of type `ty`; return the proof if it closes the goal. -/
def proveBy (ty : Expr) (tac : Syntax) : TacticM (Option Expr) := do
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  let ok ← tryTacticCatchRuntimeBool do
    let gs ← Tactic.run g.mvarId! (evalTactic tac)
    unless gs.isEmpty do throwError "unsolved"
  if ok then return some (← instantiateMVars g) else return none

/-- Close a `Prop` parameter of a contract from a local hypothesis (assigning metavariables of
    the contract's other parameters by unification). -/
def closeByAssumption (x : Expr) (ty : Expr) : MetaM Bool := do
  for decl in (← getLCtx).decls.toList.reverse do
    let some decl := decl | continue
    if decl.isImplementationDetail then continue
    let saved ← saveState
    if ← withReducible (isDefEq decl.type ty) then
      if ← isDefEq x decl.toExpr then return true
    saved.restore
  return false

/-- Fill the parameters `xs` of a contract (after its address was unified): instances by
    synthesis, `Prop` parameters by local assumption or their `autoParam` tactic. With
    `allowOpen`, parameters that stay undetermined are kept (for `wp_spec_intro`); otherwise they
    are an error. -/
def fillParams (xs : Array Expr) (bis : Array BinderInfo) (allowOpen : Bool) :
    TacticM (Except MessageData Unit) := do
  for x in xs, bi in bis do
    if (← instantiateMVars x).isMVar && bi.isInstImplicit then
      let ty ← instantiateMVars (← inferType x)
      if !ty.hasExprMVar then
        if let some inst ← (synthInstance? ty : MetaM _) then
          discard <| isDefEq x inst
  -- Run two passes on `Prop` parameters since closing one can determine another's type.
  for _ in [0:2] do
    for x in xs do
      let x' ← instantiateMVars x
      unless x'.isMVar do continue
      let ty ← instantiateMVars (← inferType x)
      unless ← isProp ty do continue
      let (tyCore, tac?) := match ← autoParamTac? ty with
        | some (t, tac) => (t, some tac)
        | none => (ty, none)
      if ← closeByAssumption x tyCore then continue
      if let some tac := tac? then
        let tyCore ← instantiateMVars tyCore
        if !tyCore.hasExprMVar then
          if let some prf ← proveBy tyCore tac then
            discard <| isDefEq x prf
  if allowOpen then return .ok ()
  for x in xs do
    let x' ← instantiateMVars x
    if x'.isMVar then
      let ty ← instantiateMVars (← inferType x)
      let n ← x'.mvarId!.getTag
      if ← isProp ty then
        return .error m!"cannot prove the contract hypothesis `{n}`:{indentExpr ty.cleanupAnnotations}\n\
          (tried local assumptions and its default tactic); pass it with `wp_apply using`"
      return .error m!"cannot determine the contract parameter `{n}`:{indentExpr ty}\n\
        from the call site; pass it with `wp_apply using`"
  return .ok ()

/-- A candidate contract: how to print it, the term, and where it comes from. -/
structure Candidate where
  label : MessageData
  /-- the contract term (a local hypothesis or a constant), before instantiation -/
  term : Expr
  /-- `true` for local hypotheses -/
  isLocal : Bool

/-- Open candidate `c`, unify its program with `prog` and its callee address with `pc`. -/
def openAndMatch (c : Expr) (prog pc : Expr) :
    TacticM (Except MessageData (Array Expr × Array BinderInfo × AddrMatch)) := do
  let cTy ← instantiateMVars (← inferType c)
  let opened ← try some <$> openContractType cTy catch _ => pure none
  let some (xs, bis, p, a, _) := opened | return .error m!"not a `subroutine_ok` contract"
  unless ← isDefEq p prog do
    return .error m!"program{indentExpr (← instantiateMVars p)}\ndoes not match{indentExpr prog}"
  let am ← matchAddr a pc
  if am == .no then
    return .error m!"callee address{indentExpr (← instantiateMVars a)}\ndiffers from the current PC{indentExpr pc}"
  return .ok (xs, bis, am)

/-- How candidate `c`'s callee address relates to `pc` (caller restores the state). -/
def probeCandidate (c : Expr) (prog pc : Expr) : TacticM (Except MessageData AddrMatch) := do
  match ← openAndMatch c prog pc with
  | .ok (_, _, am) => return .ok am
  | .error e => return .error e

/-- Instantiate candidate `c` at the current call site (`prog`, `pc`): returns the closed
    contract term and how its address matched. -/
def instantiateCandidate (c : Expr) (prog pc : Expr) :
    TacticM (Except MessageData (Expr × AddrMatch)) := do
  let (xs, bis, am) ← match ← openAndMatch c prog pc with
    | .ok r => pure r
    | .error e => return .error e
  match ← fillParams xs bis (allowOpen := false) with
  | .error e => return .error e
  | .ok () => pure ()
  let t ← instantiateMVars (mkAppN c xs)
  if t.hasExprMVar then
    return .error m!"contract term still has metavariables:{indentExpr t}"
  return .ok (t, am)

/-! ## Call drivers and the frame-procedure hook -/

/-- The frame-procedure hook: how the callee precondition `m ⊨ spec.pre x s ∗ (F ∗ R)` is
    discharged (assigning the ghost `x` and the frame `F`) when `wp_apply` does not use
    `wp_call`'s built-in matcher. -/
inductive FrameHook where
  /-- a frame procedure (same signature as `SepFrameInfer.frameProc`, the `sep_frame` solver) -/
  | proc (fp : SepFrameInfer.FrameProc)
  /-- a tactic that must close the precondition goal (e.g. `sep_frame`) -/
  | tac (stx : Syntax)

/-- Apply the closed contract `t` with `wp_call` (built-in matcher, `sep_frame` fallback). A
    `Unit` ghost argument is passed explicitly (`wp_call` leaves it as a goal otherwise). -/
def driveWpCall (t : Expr) (ghost? : Option Term := none) : TacticM Unit := do
  let stx ← Term.exprToSyntax t
  let ghost? ← match ghost? with
    | some g => pure (some g)
    | none => do
      let ty ← whnfR (← instantiateMVars (← inferType t))
      let α? := if ty.isAppOfArity ``Arm64.subroutine_ok 4 then some (ty.getArg! 0) else none
      match α? with
      | some α =>
        let α ← whnfR α
        if α.isConstOf ``Unit || α.isConstOf ``PUnit then
          pure (some (← `(())))
        else pure none
      | none => pure none
  match ghost? with
  | some gs => evalTactic (← `(tactic| wp_call ($stx) (x := $gs)))
  | none => evalTactic (← `(tactic| wp_call ($stx)))

/-- Conjuncts of the pure atoms `⌜φ⌝` of a separating conjunction. -/
partial def pureConjuncts (P : Expr) : Array Expr :=
  let P := P.consumeMData
  if P.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    pureConjuncts (P.getArg! 0) ++ pureConjuncts (P.getArg! 1)
  else if P.isAppOfArity ``Arm64.SepProp.pure 1 then
    splitAnd (P.getArg! 0)
  else #[]
where
  splitAnd (φ : Expr) : Array Expr :=
    let φ := φ.consumeMData
    if φ.isAppOfArity ``And 2 then splitAnd (φ.getArg! 0) ++ splitAnd (φ.getArg! 1) else #[φ]

/-- Normalize `e` with the `wp_norm` and `arm64_norm` simp sets (register reads through
    `State.write*` / `State.set*` spines, address arithmetic). -/
def normWp (e : Expr) : MetaM Expr := do
  let mut thms : SimpTheoremsArray := #[]
  for n in [`wp_norm, `arm64_norm] do
    if let some ext ← getSimpExtension? n then
      thms := thms.push (← ext.getTheorems)
  -- Local register / stack-pointer equations (`s.readReg64 r = v`, `s.sp = v`) as rewrite rules.
  let mut locals : SimpTheorems := {}
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, l, _) := ty.eq? | continue
    if l.isAppOfArity ``Arm64.State.readReg64 2 || l.isAppOfArity ``Arm64.State.sp 1 then
      locals ← locals.add (.fvar decl.fvarId) #[] decl.toExpr
  thms := thms.push locals
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := thms)
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp e ctx
  return r.expr

/-- In a main goal `m ⊨ G`, assign ghost metavariables from the pure equations of `G` whose one
    side is a metavariable and the other side is metavariable-free (`s.readReg64 .x0 = ?p`); the
    value is normalized with `normWp` first, so the ghost field gets the register's value
    instead of a read through the state spine. -/
def bindGhostsFromPure : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ty := SepSolver.stripMData (← instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 do return
    for φ in pureConjuncts (ty.getArg! 0) do
      let φ ← instantiateMVars φ
      let some (_, l, r) := φ.eq? | continue
      if r.isMVar && !l.hasExprMVar then discard <| isDefEq r (← normWp l)
      else if l.isMVar && !r.hasExprMVar then discard <| isDefEq l (← normWp r)

/-- Apply the closed contract `t` through `SepWP.call_subroutine_frame_auto`, discharging the
    callee precondition `spec.pre x s ∗ (F ∗ R)` with the frame procedure `fp` (which assigns the
    ghost `x` and the frame `F`). -/
def driveFrameProc (t : Expr) (hook : FrameHook) : TacticM Unit := do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let goal ← getMainGoal
  let ms ← goal.withContext do
    let f ← mkConstWithFreshMVarLevels ``SepWP.call_subroutine_frame_auto
    let (ms, _, concl) ← forallMetaTelescope (← inferType f)
    -- Binders: α prog entry target_pc spec hcall x s P F post oom ret_pc hpc hrun hsp_align hlr
    -- h_no_panic h_no_exit hnext hpre h_oom.
    unless ms.size == 22 do
      throwError "wp_apply: unexpected shape of `SepWP.call_subroutine_frame_auto`"
    unless ← isDefEq ms[5]! t do
      throwError "wp_apply: the contract does not fit `SepWP.call_subroutine_frame_auto`"
    unless ← isDefEq concl (← goal.getType) do
      throwError "wp_apply: `SepWP.call_subroutine_frame_auto` does not match the goal"
    goal.assign (mkAppN f ms)
    return ms.extract 6 22
  let gPc := ms[7]!.mvarId!
  let gRun := ms[8]!.mvarId!
  let gSp := ms[9]!.mvarId!
  let gLr := ms[10]!.mvarId!
  let gPanic := ms[11]!.mvarId!
  let gExit := ms[12]!.mvarId!
  let gNext := ms[13]!.mvarId!
  let gPre ← ms[14]!.mvarId!.withContext do
    ms[14]!.mvarId!.replaceTargetDefEq (← ms[14]!.mvarId!.getType).cleanupAnnotations
  let gOom := ms[15]!.mvarId!
  -- Precondition first: it assigns the ghost argument and the frame. Before calling the frame
  -- procedure, expand structure/product ghosts into fields, normalize register reads, and bind
  -- ghost fields from pure register equations (`s.readReg64 .x0 = ?p`), so that the spatial
  -- matcher sees the ghost values (a frame procedure typically matches atoms before it checks
  -- pure side conditions).
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R _hmR))
  evalTactic (← `(tactic| try wp_unfold_specs))
  evalTactic (← `(tactic| try dsimp only))
  discard <| etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| try dsimp only))
  bindGhostsFromPure
  let g ← getMainGoal
  let closed ← match hook with
    | .tac stx => tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close ($(⟨stx⟩)))))
    | .proc fp => g.withContext do
      let ty := SepSolver.stripMData (← instantiateMVars (← g.getType))
      unless ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 do return false
      let m := ty.getArg! 1
      let some (h, P) ← SepFrameInfer.findSatHypForFrame? m | return false
      trace[ProofLib.wpApply] "frame procedure on{indentExpr P}\n⊢{indentExpr (ty.getArg! 0)}"
      let some prf ← fp (← SepFrameInfer.defaultDisch) (← instantiateMVars m) P h (ty.getArg! 0)
        | return false
      g.assign prf
      return true
  unless closed do
    throwError "wp_apply: the frame procedure did not prove the callee precondition"
  for gSetup in [gPc, gRun, gSp, gLr] do
    setGoals [gSetup]
    unless ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
        wp_focus_close (first | wp_norm_lhs | wp_norm_goal)))) do
      let s ← gSetup.withContext do return m!"{← instantiateMVars (← gSetup.getType)}"
      throwError "wp_apply: cannot prove call-site condition{indentD s}"
  setGoals [gPanic, gExit, gOom]
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp)
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ho; first
      | exact _ho
      | exact False.elim (not_satisfies_false_sepConj _ho)
      | exact satisfies_true_sepConj_frame _ho
      | exact Satisfies.drop_mid _ho))))
  setGoals [gNext]
  evalTactic (← `(tactic| intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

/-- Find the ghost argument `x` of the call rule used in the proof `prf` (for `wp_apply?`). -/
def findGhost? (prf : Expr) : MetaM (Option Expr) := do
  let callRules := #[``SepWP.call_subroutine, ``SepWP.call_subroutine_frame,
    ``SepWP.call_subroutine_frame_frozen, ``SepWP.call_sep, ``SepWP.call_subroutine_frame_auto,
    ``SepWPp.call_wpp, ``SepWPp.call_wpp_frozen, ``SepWPp.call_sep]
  let some app := prf.find? fun e => callRules.any (e.isAppOf ·) | return none
  let .const n _ := app.getAppFn | return none
  let info ← getConstInfo n
  let names ← forallTelescopeReducing info.type fun ys _ => ys.mapM fun y => y.fvarId!.getUserName
  let some idx := names.findIdx? (· == `x) | return none
  if idx < app.getAppNumArgs then
    return some (app.getArg! idx)
  return none

structure Config where
  /-- explicit contract (`using h`) -/
  using? : Option Term := none
  /-- explicit ghost argument for `wp_call` (`with t`), for ghosts the call site does not determine -/
  ghost? : Option Term := none
  /-- frame-procedure hook (`(frame := tac)`, or `FrameHook.proc` from Lean code) -/
  frame? : Option FrameHook := none
  /-- print the explicit `wp_call` (`wp_apply?`) -/
  report : Bool := false

def wpApplyCore (cfg : Config) (ref : Syntax) : TacticM Unit := do
  transitionToContinuationGoalIfReady (forWppCall := false)
  let goal ← getMainGoal
  goal.withContext (wpApplyCoreIn cfg ref goal)
where
  wpApplyCoreIn (cfg : Config) (ref : Syntax) (goal : MVarId) : TacticM Unit := do
    let (prog, _target, pc) ← getSepWPOrWPpStateAndPC
    let candidates : Array Candidate ← goal.withContext do
      match cfg.using? with
      | some h =>
        let e ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        return #[{ label := m!"{h}", term := e, isLocal := true }]
      | none =>
        let mut cs : Array Candidate := #[]
        -- Newest first; a hypothesis shadowed by a later one with the same name (e.g. the
        -- original of a hypothesis that `wp_entry` rewrote) is skipped.
        let mut seen : NameSet := {}
        for decl in (← getLCtx).decls.toList.reverse do
          let some decl := decl | continue
          if decl.isImplementationDetail || decl.isAuxDecl then continue
          if seen.contains decl.userName then continue
          seen := seen.insert decl.userName
          let ty ← instantiateMVars decl.type
          if !(← isProp ty) then continue
          let saved ← saveState
          let isContract ← try
              discard <| openContractType ty 2
              pure true
            catch _ => pure false
          saved.restore
          if isContract then
            cs := cs.push { label := m!"{mkFVar decl.fvarId}", term := decl.toExpr, isLocal := true }
        for n in ← lookupGlobal pc do
          let c ← mkConstWithFreshMVarLevels n
          cs := cs.push { label := m!"{mkConst n}", term := c, isLocal := false }
        return cs
    let mut ready : Array Candidate := #[]
    let mut maybe : Array Candidate := #[]
    let mut failures : Array MessageData := #[]
    let probe (c : Candidate) : TacticM (Except MessageData AddrMatch) := do
      let saved ← saveState
      let r ← goal.withContext (probeCandidate c.term prog pc)
      saved.restore
      return r
    for c in candidates do
      match ← probe c with
      | .ok .yes => ready := ready.push c
      | .ok _ => maybe := maybe.push c
      | .error e =>
        trace[ProofLib.wpApply] "{c.label}: rejected: {e}"
        failures := failures.push m!"{c.label}: {e}"
    -- Fallback: the index compares addresses syntactically, so a contract stated at an address that
    -- is equal to the PC only up to definitions or local equations (`prog.fnAddr "f"` vs a numeral)
    -- is not a hit. When nothing matched for sure, also probe the other `@[wp_spec]` lemmas.
    if ready.isEmpty && cfg.using?.isNone then
      let hits ← goal.withContext (lookupGlobal pc)
      for n in ← allGlobal do
        if hits.contains n then continue
        let c ← goal.withContext (mkConstWithFreshMVarLevels n)
        let cand : Candidate := { label := m!"{mkConst n}", term := c, isLocal := false }
        match ← probe cand with
        | .ok .yes => ready := ready.push cand
        | .ok _ => maybe := maybe.push cand
        | .error e => trace[ProofLib.wpApply] "{cand.label}: rejected: {e}"
    if ready.isEmpty && maybe.isEmpty && failures.isEmpty then
      throwError "wp_apply: no contract for the current PC{indentExpr pc}\nno local `subroutine_ok` hypothesis and no `@[wp_spec]` lemma matches; add one, or use `wp_apply using h`"
    for c in ready ++ maybe do
      trace[ProofLib.wpApply] "trying {c.label}"
      let r ← tryTacticCatchRuntimeMsg do
        let t ← goal.withContext do
          match ← instantiateCandidate c.term prog pc with
          | .ok (t, _) => pure t
          | .error e => throwError e
        match cfg.frame? with
        | some hook => driveFrameProc t hook
        | none => driveWpCall t cfg.ghost?
        return t
      match r with
      | .ok t =>
        if cfg.report then
          goal.withContext do
            let prf ← instantiateMVars (mkMVar goal)
            let tStx ← withOptions (fun o => o.setBool `pp.analyze true) (PrettyPrinter.delab t)
            let ghost? ← findGhost? prf
            let sugg ← match ghost? with
              | some x =>
                let xStx ← PrettyPrinter.delab (← instantiateMVars x)
                `(tactic| wp_call ($tStx) ($xStx))
              | none => `(tactic| wp_call ($tStx))
            Lean.Meta.Tactic.TryThis.addSuggestion ref sugg
        return
      | .error e =>
        trace[ProofLib.wpApply] "{c.label}: failed: {e}"
        failures := failures.push m!"{c.label}: {e}"
    throwError "wp_apply: no candidate contract applies at PC{indentExpr pc}\n{MessageData.joinSep failures.toList "\n"}"

/-! ## Introducing Registered Contracts Before Entry Generalization -/

def wpSpecIntroCore (names? : Option (Array Name)) : TacticM Unit := do
  let goal ← getMainGoal
  let newHyps ← goal.withContext do
    let tgt := (← instantiateMVars (← goal.getType)).consumeMData
    let (prog, entry) ← if tgt.isAppOf ``SepWP || tgt.isAppOf ``SepWPp then
        if tgt.getAppNumArgs < 3 then
          throwError "wp_spec_intro: unexpected `SepWP` goal{indentExpr tgt}"
        pure (tgt.getArg! 0, ← extractSepWPPC (tgt.getArg! 2))
      else
        let (_, _, prog, entry, _) ← try openContractType tgt
          catch _ => throwError "wp_spec_intro: goal is not a `subroutine_ok prog entry spec`, \
            `SepWP` or `SepWPp` judgment"
        pure (prog, entry)
    let names ← match names? with
      | some ns => pure ns
      | none => allGlobal
    let mut out : Array (Name × Expr × Expr) := #[]
    for n in names do
      let saved ← saveState
      let c ← mkConstWithFreshMVarLevels n
      let (xs, bis, p, a, _) ← try openContractType (← inferType c)
        catch _ => saved.restore; throwError "wp_spec_intro: `{n}` is not a `subroutine_ok` contract"
      unless ← isDefEq p prog do
        trace[ProofLib.wpApply] "wp_spec_intro: {n}: program does not match"
        saved.restore
        continue
      -- Contracts written relative to a function entry (`base + k`): take `base` from the goal.
      let a ← instantiateMVars a
      if a.isAppOfArity ``HAdd.hAdd 6 && (a.getArg! 4).hasExprMVar then
        let saved2 ← saveState
        unless ← withReducible (isDefEq (a.getArg! 4) entry) do saved2.restore
      match ← fillParams xs bis (allowOpen := true) with
      | .error e => throwError "wp_spec_intro: {n}: {e}"
      | .ok () => pure ()
      let r ← abstractMVars (← instantiateMVars (mkAppN c xs))
      let val := r.expr
      let ty ← inferType val
      let hName := Name.mkSimple ("h_" ++ match n with | .str _ s => s | _ => n.toString)
      out := out.push (hName, ty, val)
    return out
  let mut g := goal
  for (h, ty, val) in newHyps do
    let g' ← g.assert h ty val
    let (_, g'') ← g'.intro1P
    g := g''
  replaceMainGoal [g]

end WpApply

open WpApply in
/-- `wp_apply`: apply the contract of the subroutine whose entry is the current PC. Candidates are
    local `subroutine_ok` hypotheses (also `∀`-quantified, e.g. from `wp_spec_intro`) and
    `@[wp_spec]` lemmas whose callee address matches the PC. Contract parameters are filled by
    address unification, local assumptions, instances and `autoParam` tactics; the ghost argument
    and the frame are inferred by `wp_call`. Variants:
    - `wp_apply using h`: use the contract `h` (a hypothesis or a partially applied lemma);
    - `wp_apply with t`: pass the ghost argument `t` to `wp_call` (e.g. `⟨_, _, 0#64⟩` for a ghost
      field the call site does not determine); the contract is still looked up;
    - `wp_apply?`: also print the equivalent explicit `wp_call` (contract and ghost argument);
    - `wp_apply (frame := tac)`: discharge the precondition with the tactic `tac` (e.g.
      `sep_frame`) through `SepWP.call_subroutine_frame_auto`; Lean callers of `wpApplyCore` can
      pass a `SepFrameInfer.FrameProc` value instead (`FrameHook.proc`). -/
syntax (name := wpApply) "wp_apply" (" (" &"frame" " := " tacticSeq ")")? (" using " term)?
  (" with " term:max)? : tactic

@[inherit_doc wpApply]
syntax (name := wpApplyQ) "wp_apply?" (" (" &"frame" " := " tacticSeq ")")? (" using " term)?
  (" with " term:max)? : tactic

open WpApply in
elab_rules : tactic
  | `(tactic| wp_apply $[ (frame := $fp?)]? $[using $h?]? $[with $g?]?) => do
    let frame? := fp?.map fun fp => FrameHook.tac fp.raw
    wpApplyCore { using? := h?, ghost? := g?, frame?, report := false } (← getRef)
  | `(tactic| wp_apply? $[ (frame := $fp?)]? $[using $h?]? $[with $g?]?) => do
    let frame? := fp?.map fun fp => FrameHook.tac fp.raw
    wpApplyCore { using? := h?, ghost? := g?, frame?, report := true } (← getRef)

/-- `wp_spec_intro` / `wp_spec_intro [c₁, ...]`: on a `subroutine_ok prog entry spec` goal, or a
    `SepWP` / `SepWPp` goal whose current PC is `entry` (before `wp_entry` / `generalize_entry`
    abstract the program and the entry), add each `@[wp_spec]` contract
    (resp. each listed contract) whose program unifies with `prog` as a local hypothesis `h_<name>`.
    Parameters determined by the program, by local assumptions or instances are filled; for a
    contract whose address is `base + k` with `base` unifiable with `entry` (e.g.
    `prog.fnAddr ?name + BitVec.ofNat 64 ?k`) `base` is taken from `entry`; the remaining
    parameters stay `∀`-bound and are instantiated by `wp_apply` at the call site. -/
syntax (name := wpSpecIntro) "wp_spec_intro" (" [" ident,* "]")? : tactic

open WpApply in
elab_rules : tactic
  | `(tactic| wp_spec_intro) => wpSpecIntroCore none
  | `(tactic| wp_spec_intro [$cs,*]) => do
    let names ← cs.getElems.mapM fun c => realizeGlobalConstNoOverloadWithInfo c
    wpSpecIntroCore (some names)

end

end ProofLib
