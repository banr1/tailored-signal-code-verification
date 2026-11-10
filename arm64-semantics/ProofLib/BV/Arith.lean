/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.ArithTranslate
public import ProofLib.BV.ArithClassify
public import ProofLib.BV.Linear
public import ProofLib.BV.Bits
import Arm64.Trusted.Spec.SepLogic

/-!
# `BitVec` Arithmetic Automation

Top-level kernel-checked `BitVec` tactics and `MetaM` decision procedures:
- `bv_arith` closes linear and modular `BitVec` goals via a reflective linear normal-form shortcut
  on equalities/disequalities followed by relevance-filtered, bound-driven `toNat`/`toInt`
  translation and a single `omega` call.
- `bv_solve` classifies the goal (`GoalClass`) and dispatches `decide`, `bv_arith`, or the
  kernel-only `bv_fallback` chain (`bv_ext_bool | bv_bits | bv_omega`).
- `decideProp?` tries to prove or refute a proposition in `MetaM`, combining relevance filtering,
  a scalar negative cache, classification, and concrete test-vector screening before invoking a
  solver.
-/

public meta section

namespace ProofLib.BV.Arith
open Lean Meta Elab Tactic

/-! ## Reflective Linear Shortcut -/

/-- Replace closed non-literal `BitVec` subterms (`~~~65520#64`, `a &&& b ||| c` on literals) by
their value `BitVec.ofNat w k`; the result is definitionally equal (kernel evaluation). -/
def foldClosedBV (e : Expr) : Expr :=
  e.replace fun t =>
    if t.hasFVar || t.hasMVar || (bvLit? t).isSome then none
    else match eval {} t with
      | some (.bv w k) =>
        if t.isAppOf ``BitVec.ofNat || t.isAppOf ``OfNat.ofNat then none
        else some (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit k))
      | _ => none

/-- Close `g : a = b` / `a ≠ b` / `¬ a = b` over `BitVec` with the reflective linear normal form
(`ProofLib.BV.Lin.proveEq?` / `proveNe?`), after folding closed `BitVec` subterms to literals.
Hypotheses are not used. Returns `true` iff it closed the goal; never throws. -/
def tryBvLin (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let ty0 := ty
  let ty := foldClosedBV ty
  let shape? : Option (Bool × Expr × Expr) := match_expr ty with
    | Eq _ a b => some (true, a, b)
    | Ne _ a b => some (false, a, b)
    | Not p => match_expr p with
      | Eq _ a b => some (false, a, b)
      | _ => none
    | _ => none
  let some (isEq, a, b) := shape? | return false
  let s ← saveState
  try
    let some _ ← ProofLib.BV.Lin.bvWidth? a | return false
    let pf? ← if isEq then ProofLib.BV.Lin.proveEq? a b else ProofLib.BV.Lin.proveNe? a b
    let some pf := pf? | s.restore; return false
    g.assign (← mkExpectedTypeHint pf ty0)
    return true
  catch _ => s.restore; return false

/-- Distinct `(w, a, b)` with `BitVec.ofNat w (a - b)` (`Nat` subtraction) a subterm of `e`. -/
partial def ofNatSubs (e : Expr) (acc : Array (Expr × Expr × Expr) := #[]) :
    Array (Expr × Expr × Expr) :=
  let acc := match e.getAppFnArgs with
    | (``BitVec.ofNat, #[w, n]) => match n.getAppFnArgs with
      | (``HSub.hSub, #[α, _, _, _, a, b]) =>
        if α.isConstOf ``Nat && !acc.contains (w, a, b) then acc.push (w, a, b) else acc
      | _ => acc
    | _ => acc
  match e with
  | .app f x => ofNatSubs x (ofNatSubs f acc)
  | .mdata _ b => ofNatSubs b acc
  | _ => acc

/-- `tryBvLin` after rewriting each `BitVec.ofNat w (a - b)` to `ofNat w a - ofNat w b`
(`ofNat_sub_of_le`), repeated while new ones appear (at most 4 rounds). The side conditions `b ≤ a` are proved with `arithCore` (hypotheses
used) only once the linear normal form has closed the rewritten goal. Never throws. -/
def tryBvLinSub (g : MVarId) : MetaM Bool := g.withContext do
  if (ofNatSubs (← instantiateMVars (← g.getType))).isEmpty then return false
  let s ← saveState
  try
    let mut g := g
    let mut sides := #[]
    -- rewriting `ofNat w (a - (b - c))` exposes `ofNat w (b - c)`: iterate (bounded)
    for _ in [0:4] do
      let subs := ofNatSubs (← instantiateMVars (← g.getType))
      if subs.isEmpty then break
      for (w, a, b) in subs do
        let h ← mkFreshExprMVar (mkNatLe b a)
        let r ← g.rewrite (← g.getType) (mkApp4 (mkConst ``ofNat_sub_of_le) w a b h)
        g ← g.replaceTargetEq r.eNew r.eqProof
        sides := sides.push h.mvarId!
    unless ← tryBvLin g do s.restore; return false
    for h in sides do arithCore h (retryAll := false)
    return true
  catch _ => s.restore; return false

/-- `tryBvLin`, then `tryBvLinSub`. -/
def tryBvLin' (g : MVarId) : MetaM Bool := do
  if ← tryBvLin g then return true
  perf "bvLinSub" <| tryBvLinSub g

/-- `bv_arith` as a `TacticM` finishing step on the main goal. -/
def bvArithTac : TacticM Unit := do
  let g ← getMainGoal
  let (_, g') ← g.intros
  if ← perf "bvLin" <| tryBvLin' g' then replaceMainGoal []; return
  arithCore g'
  replaceMainGoal []

/-- Close linear and modular `BitVec` arithmetic goals: try the reflective linear normal form on
`=`/`≠`, then relevance-filter hypotheses, normalize `Bool`/`Prop` comparisons, emit bound-driven
`toNat` node equations, and run a single `omega` call. -/
elab "bv_arith" : tactic => bvArithTac

/-! ## Kernel-Only Fallback (`bv_kernel`, `bv_fallback`) -/

/-- Opt-in escape hatch: when `true`, `bv_fallback` (the bit-level fallback used by `bv_solve`,
`decideProp?`, `wp_auto`, `vcgen`, `sep_solve`, ...) runs `bv_decide` after the kernel-only chain
fails. `bv_decide` proofs depend on `Lean.ofReduceBool` (a `._native.bv_decide.ax_*` axiom), so
they are rejected by the kernel-axiom audit (`#axiom_audit`) and by comparator. Default `false`:
automation is kernel-only and fails loudly instead. -/
register_option proofLib.bvDecideFallback : Bool := {
  defValue := false
  descr := "let ProofLib automation fall back to `bv_decide` (native axioms) after the \
    kernel-only `bv_kernel` chain fails"
}

private partial def isPureBitwiseBV (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``HXor.hXor 6 || e.isAppOfArity ``HAnd.hAnd 6 || e.isAppOfArity ``HOr.hOr 6 ||
     e.isAppOfArity ``BitVec.xor 3 || e.isAppOfArity ``BitVec.and 3 || e.isAppOfArity ``BitVec.or 3 then
    isPureBitwiseBV (e.getArg! (e.getAppNumArgs - 2)) &&
    isPureBitwiseBV (e.getArg! (e.getAppNumArgs - 1))
  else if e.isAppOfArity ``Complement.complement 3 || e.isAppOfArity ``BitVec.not 2 then
    isPureBitwiseBV (e.getArg! (e.getAppNumArgs - 1))
  else if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HMul.hMul 6 ||
          e.isAppOf ``BitVec.extractLsb' || e.isAppOf ``HAppend.hAppend ||
          e.isAppOf ``BitVec.setWidth || e.isAppOf ``BitVec.zeroExtend || e.isAppOf ``BitVec.signExtend ||
          e.isAppOf ``HShiftLeft.hShiftLeft || e.isAppOf ``HShiftRight.hShiftRight then
    false
  else if e.isAppOfArity ``OfNat.ofNat 3 || e.isAppOfArity ``BitVec.ofNat 2 then
    (e.getArg! 1).nat? == some 0
  else
    true

/-- Pointwise bitwise equality solver: apply `ext i _`, push `getElem`/`getLsbD` through
`^^^`/`&&&`/`|||`/`~~~`/`0`/`allOnes`, generalize at most 4 `Bool` bit-access atoms, and close by
`decide`. Fails immediately when non-boolean terms remain. -/
elab "bv_ext_bool" : tactic => do
  let g0 ← getMainGoal
  g0.withContext do
    let tgt0 ← instantiateMVars (← g0.getType)
    let some (ty, lhs, rhs) := tgt0.eq? | throwError "bv_ext_bool: not an equality"
    unless ty.isAppOfArity ``BitVec 1 && isPureBitwiseBV lhs && isPureBitwiseBV rhs do
      throwError "bv_ext_bool: not a pure bitwise BitVec equality"
  evalTactic (← `(tactic| (
    ext i _
    simp -failIfUnchanged only [
      BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_zero,
      BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_zero,
      BitVec.getLsbD_allOnes])))
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let rec collect (e : Expr) (acc : Array Expr) : Array Expr :=
      if e.isAppOf ``GetElem.getElem || e.isAppOf ``BitVec.getLsbD then
        if acc.contains e then acc else acc.push e
      else match e with
        | .app f a => collect a (collect f acc)
        | _ => acc
    let atoms := collect tgt #[]
    if atoms.size > 4 then throwError "bv_ext_bool: too many bit atoms ({atoms.size})"
    let mut g := g
    let mut fvars : Array FVarId := #[]
    for a in atoms do
      let (fvs, g') ← g.generalize #[{ expr := a }]
      g := g'
      fvars := fvars ++ fvs
    let (_, g') ← g.revert fvars
    let closedTgt ← g'.withContext do instantiateMVars (← g'.getType)
    if closedTgt.hasFVar then throwError "bv_ext_bool: non-boolean terms remain"
    replaceMainGoal [g']
  evalTactic (← `(tactic| decide))

/-- Kernel-only finishing chain `bv_ext_bool | bv_bits | bv_omega` for bit-level goals (pure
bitwise identities, literal masks, `zeroExtend`/`extractLsb'`, `++` byte extraction, and
comparisons). Never introduces `ofReduceBool` axioms. -/
macro "bv_kernel" : tactic =>
  `(tactic| first | (bv_ext_bool; done) | (bv_bits; done) | (bv_omega; done))

/-- Run `bv_kernel`, falling back to `bv_decide` only when `proofLib.bvDecideFallback` is `true`. -/
elab "bv_fallback" : tactic => do
  let s ← saveState
  try evalTactic (← `(tactic| bv_kernel))
  catch e =>
    unless proofLib.bvDecideFallback.get (← getOptions) do throw e
    s.restore
    evalTactic (← `(tactic| bv_decide))

/-! ## Router -/

/-- Relevant hypotheses for goal type `p` (instantiated), as `(fvarId, type)`. -/
def relevantFor (p : Expr) : MetaM (Array (FVarId × Expr)) := do
  let cands ← arithHyps
  -- goal `False` / opaque `Prop`: only a contradiction among the hypotheses can close it
  if p.consumeMData.isFalse || !(← isArithProp p) || isFalseGround p then return cands
  return relevantFilter (collectAtoms p {}) cands

/-- Classify the main goal of `g` (after `intros`). -/
def classifyGoal (g : MVarId) : MetaM (GoalClass × Array (FVarId × Expr)) := g.withContext do
  let p ← instantiateMVars (← g.getType)
  let hs ← relevantFor p
  return (← classify p (hs.map (·.2)), hs)

/-- Clear every `Prop` hypothesis not in `keep` (best effort). -/
def clearIrrelevant (g : MVarId) (keep : Array FVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx).getFVarIds.reverse do
    if keep.contains d then continue
    let decl ← d.getDecl
    if decl.isImplementationDetail then continue
    if ← isProp decl.type then g ← g.tryClear d
  return g

def runTac (g : MVarId) (stx : TSyntax `tactic) : TacticM Unit := do
  let gs ← Tactic.run g (evalTactic stx)
  unless gs.isEmpty do throwError "{gs.length} goals remain"

/-- Dispatch exactly one solver for class `c`. -/
def dispatch (g : MVarId) (c : GoalClass) (_hs : Array (FVarId × Expr)) : TacticM Unit := do
  match c with
  | .ground => runTac g (← `(tactic| decide))
  | .linearEq | .linearArith =>
    if ← tryBvLin' g then return
    arithCore g
  | .bitwise =>
    -- keep every arithmetic hypothesis (the solver may need a contradiction among hypotheses
    -- unrelated to the goal), drop the rest (sep-logic facts etc. slow its preprocessing)
    let g ← g.withContext do clearIrrelevant g ((← arithHyps).map (·.1))
    runTac g (← `(tactic| first | bv_fallback | (simp_all; done)))
  | .symbolicShift =>
    let g ← g.withContext do clearIrrelevant g ((← arithHyps).map (·.1))
    if proofLib.bvDecideFallback.get (← getOptions) then
      runTac g (← `(tactic| first | bv_fallback | (simp_all; done)))
    else
      runTac g (← `(tactic| (simp_all; done)))
  | .unsupported =>
    throwError "bv_solve: goal classified as {c}; no solver is run for this class"

/-- Classify the goal and run exactly one solver (`decide` / `bv_lin` / `bv_arith` /
`bv_fallback`), or fail immediately on `unsupported`. Use
`set_option trace.bv_solve true` to see the classification and the chosen solver. -/
elab "bv_solve" : tactic => do
  let g ← getMainGoal
  let (_, g) ← g.intros
  let (c, hs) ← classifyGoal g
  trace[bv_solve] "class {c}, {hs.size} relevant hyps; solver: {match c with
    | .ground => "decide" | .linearEq => "bv_lin/bv_arith" | .linearArith => "bv_arith"
    | .bitwise | .symbolicShift => "bv_fallback" | .unsupported => "none"}"
  try dispatch g c hs
  catch e => throwError "bv_solve [{c}]: {e.toMessageData}"
  replaceMainGoal []

/-! ## `decideProp?` -/

/-- Scalar-only fingerprint for `decideProp?` negative cache entries. Containing zero `Expr`
object pointers (`m_objs = 0`) avoids `lean_mark_mt` traversal or `m_rc < 0` flips on the caller's
live goal expressions when inserting into `negCache : IO.Ref`, so negative results can be shared
across declarations. -/
structure CacheKey where
  propHash  : UInt64
  propDepth : UInt32
  hypsHash  : UInt64
  numHyps   : UInt32
  bvDecide  : Bool
  deriving BEq, Hashable

@[inline] def mkCacheKey (p : Expr) (hs : Array (FVarId × Expr)) (allowBvDecide : Bool) :
    CacheKey :=
  let hypsHash := hs.foldl (init := 1723) fun h (_, ty) =>
    mixHash h (mixHash ty.hash ty.approxDepth.toUInt64)
  { propHash := p.hash
    propDepth := p.approxDepth
    hypsHash
    numHyps := hs.size.toUInt32
    bvDecide := allowBvDecide }

/-- Negative cache: problems for which both attempts failed (or were skipped as hopeless).
Keyed on the scalar fingerprint of the instantiated proposition and the types of its relevant
hypotheses, so an entry remains valid across declarations without retaining or marking `Expr` heap
objects. Positive results are not cached because their proof terms reference auxiliary theorems
that roll back on elaboration backtracking. -/
initialize negCache : IO.Ref (Std.HashSet CacheKey) ← IO.mkRef {}

def cacheLimit : Nat := 10000

/-- Prove `goal` (in the current context) with one solver for class `c`. -/
def attempt (goal : Expr) (c : GoalClass) (_hs : Array (FVarId × Expr)) : MetaM (Option Expr) := do
  let m ← mkFreshExprSyntheticOpaqueMVar goal
  let s ← saveState
  try
    match c with
    | .ground =>
      let pf ← mkDecideProof goal
      -- check the `Decidable` instance evaluates to `isTrue` / `Bool.true` before trusting it
      let inst ← withAtLeastTransparency .default <| whnf (pf.appFn!.appArg!)
      let ok ←
        if inst.isAppOf ``Decidable.isTrue then
          pure true
        else
          let dec ← withAtLeastTransparency .default <| whnf (mkApp2 (mkConst ``Decidable.decide) goal inst)
          pure (dec.isConstOf ``Bool.true)
      unless ok do throwError "decide failed"
      m.mvarId!.assign pf
    | .bitwise =>
      let g ← clearIrrelevant m.mvarId! ((← arithHyps).map (·.1))
      let gs ← Term.TermElabM.run' <| Tactic.run g (evalTactic (← `(tactic| first | bv_fallback | (simp_all; done))))
      unless gs.isEmpty do throwError "bv_fallback left goals"
    | .symbolicShift =>
      let g ← clearIrrelevant m.mvarId! ((← arithHyps).map (·.1))
      let tac ← if proofLib.bvDecideFallback.get (← getOptions) then
          `(tactic| first | bv_fallback | (simp_all; done))
        else
          `(tactic| (simp_all; done))
      let gs ← Term.TermElabM.run' <| Tactic.run g (evalTactic tac)
      unless gs.isEmpty do throwError "symbolicShift left goals"
    | _ => unless ← tryBvLin' m.mvarId! do arithCore m.mvarId! (retryAll := false)
    return some (← instantiateMVars m)
  catch _ =>
    s.restore; return none

/-- Try to decide the proposition `p` in the current local context, returning `some (true, h)`
with `h : p`, `some (false, h)` with `h : ¬p`, or `none`.

1. Filter local hypotheses to arithmetic facts transitively sharing atoms with `p`.
2. Consult `negCache` on `(p, relevant hyp types, allowBvDecide)`.
3. Reject `unsupported` (and `bitwise`/`symbolicShift` unless `allowBvDecide`) immediately.
4. Screen `p` and the hypotheses on concrete test vectors (`evalVerdict`): return `none` when two
   satisfying vectors disagree on `p`, and try only the matching polarity when all agree.
5. Run at most one kernel-checked solver call per remaining polarity. -/
def decideProp? (p : Expr) (allowBvDecide := false) : MetaM (Option (Bool × Expr)) := do
  let p ← instantiateMVars p
  let hs ← relevantFor p
  let key := mkCacheKey p hs allowBvDecide
  let cacheable := !p.hasMVar && !hs.any (·.2.hasMVar)
  if cacheable && (← negCache.get).contains key then
    trace[bv_solve] "decideProp?: cache hit (undetermined) {p}"; return none
  let giveUp : MetaM (Option (Bool × Expr)) := do
    if cacheable then
      negCache.modify fun c => (if c.size ≥ cacheLimit then {} else c).insert key
    return none
  let hyps := hs.map (·.2)
  let c ← classify p hyps
  trace[bv_solve] "decideProp?: class {c}, {hs.size} relevant hyps: {p}"
  if c == .unsupported || ((c == .bitwise || c == .symbolicShift) && !allowBvDecide) then
    return ← giveUp
  let v ← evalVerdict p hyps
  let (tryPos, tryNeg) := match v with
    | .undetermined => (false, false)
    | .likely b => (b, !b)
    | .unknown => (true, true)
  trace[bv_solve] "decideProp?: verdict {match v with
    | .undetermined => "undetermined" | .likely b => s!"likely {b}" | .unknown => "unknown"}"
  if tryPos then
    if let some h ← attempt p c hs then return some (true, h)
  if tryNeg then
    if let some h ← attempt (mkNot p) c hs then return some (false, h)
  giveUp

/-- Test/diagnostic tactic: `decide_prop? p` logs the result of `decideProp? p` (`proved`,
`refuted` or `undetermined`) and leaves the goal unchanged. -/
elab "decide_prop? " t:term : tactic => withMainContext do
  let p ← Term.elabTerm t (some (mkSort .zero))
  match ← decideProp? p with
  | some (true, _) => logInfo m!"proved: {p}"
  | some (false, _) => logInfo m!"refuted: {p}"
  | none => logInfo m!"undetermined: {p}"

end ProofLib.BV.Arith
