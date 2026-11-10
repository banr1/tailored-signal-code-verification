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
# Syntactic Classification of Branch and Side Conditions

Syntactic feature detectors (`relevantCtx`, `hasSymbolicShift`, `hasBitwise`, `hasNatStructure`)
and `classify`, used by weakest-precondition tactics to route branch and side conditions between
`bv_decide`, `ProofLib.BV.Arith`, and `omega`, together with diagnostic and stepping options.
-/

namespace ProofLib.CondClassify

public meta section

open Lean Meta Elab Tactic

register_option proofLib.condStats : Bool := {
  defValue := false
  descr := "log the outcome and wall time of every WP decision-procedure call to stderr"
}

register_option proofLib.verdictAudit : Bool := {
  defValue := false
  descr := "diagnostic: when the evaluator says a WP branch condition is undetermined, still run the old decision chain, log its outcome (`condTime audit.<level>`), and use its result"
}

register_option proofLib.verdictSkip : Bool := {
  defValue := false
  descr := "skip the WP decision chain on branch conditions the evaluator shows undetermined (two models of the relevant hypotheses disagreeing on the condition); off by default: the measured speedup is below 3%"
}

register_option proofLib.arithRoute : Bool := {
  defValue := true
  descr := "route WP branch conditions through ProofLib.BV.Arith (`arithRoute?`) before the omega family"
}

register_option proofLib.wpVerbose : Bool := {
  defValue := false
  descr := "make `wp_steps` / `wp_sym_steps` log an info message at every stop (call, return/target, tail-call entry, unresolved branch); off by default, so proofs build without one message per stepping segment"
}

register_option proofLib.wpStrict : Bool := {
  defValue := false
  descr := "make `wp_steps` / `wp_sym_steps` throw an error naming the instruction (and the step rule failure) when they stop because no step rule applies at a non-branch PC, instead of silently leaving the goal at that PC; under `proofLib.wpVerbose` the same report is logged as an info message"
}

register_option proofLib.wpSymbolicBytes : Bool := {
  defValue := true
  descr := "let `wp_sep_access` (and the step rules that use it) resolve loads and stores against byte-list atoms `base ↦ₛ bs` / `base ↦ᵣ bs` whose contents or offset are symbolic; turn off for proofs that step such accesses by hand"
}

register_option proofLib.wpStopAtBranchTarget : Bool := {
  defValue := true
  descr := "make `wp_steps` / `wp_sym_steps` stop at the `SepWP` target when a conditional branch is decided towards it (loop back-edges), instead of resolving the branch and stepping on; turn off for proofs that expect the unresolved `ite` PC"
}

/-- Report (to stderr, when `proofLib.condStats` is set) the outcome and wall time of one
    decision-procedure call. -/
def reportTiming (tag : Name) (ok : Bool) (ms : Nat) (goal : Expr) : CoreM Unit := do
  if proofLib.condStats.get (← getOptions) then
    IO.eprintln s!"condTime {tag} {if ok then "ok" else "fail"} {ms} {(toString goal).take 200 |>.replace "\n" " "}"

/-- Atoms of `e`: free variables that are not machine states, and maximal applications that take
    a machine-state free variable as a direct argument (`s.readReg64 r`, `s.mem`, ...). -/
partial def atomsOf (stateFVars : Std.HashSet FVarId) (e : Expr) : Std.HashSet Expr :=
  (go e {} {}).1
where
  go (e : Expr) (acc : Std.HashSet Expr) (seen : Std.HashSet Expr) :
      Std.HashSet Expr × Std.HashSet Expr :=
    if !e.hasFVar || seen.contains e then (acc, seen) else
    let seen := seen.insert e
    match e with
    | .fvar id => if stateFVars.contains id then (acc, seen) else (acc.insert e, seen)
    | .app .. =>
      let args := e.getAppArgs
      if args.any (fun a => match a with | .fvar id => stateFVars.contains id | _ => false) then
        (acc.insert e, seen)
      else
        let (acc, seen) := go e.getAppFn acc seen
        args.foldl (fun (acc, seen) a => go a acc seen) (acc, seen)
    | .lam _ d b _ | .forallE _ d b _ =>
      let (acc, seen) := go d acc seen
      go b acc seen
    | .letE _ t v b _ =>
      let (acc, seen) := go t acc seen
      let (acc, seen) := go v acc seen
      go b acc seen
    | .mdata _ b | .proj _ _ b => go b acc seen
    | _ => (acc, seen)

/-- The relevant local context of `goal`: the types of `Prop` hypotheses and the values of
    `let`-bindings that are connected to `goal` through shared atoms (transitively), plus every
    closed hypothesis, in local-context order. Returns `none` if a relevant hypothesis still
    contains metavariables. -/
def relevantCtx (goal : Expr) : MetaM (Option (Array Expr)) := do
  let lctx ← getLCtx
  let mut stateFVars : Std.HashSet FVarId := {}
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet &&
        (← instantiateMVars decl.type).isConstOf `Arm64.State then
      stateFVars := stateFVars.insert decl.fvarId
  let mut facts : Array (Expr × Std.HashSet Expr) := #[]
  for decl in lctx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if let some v := decl.value? then
      let v ← instantiateMVars v
      facts := facts.push (v, (atomsOf stateFVars v).insert (.fvar decl.fvarId))
    else if ← isProp ty then
      facts := facts.push (ty, atomsOf stateFVars ty)
  let mut tracked := atomsOf stateFVars goal
  let mut included : Array Bool := facts.map (·.2.isEmpty)
  let mut changed := true
  while changed do
    changed := false
    for i in [0:facts.size] do
      if !included[i]! then
        let atoms := facts[i]!.2
        if atoms.any (tracked.contains ·) then
          included := included.set! i true
          tracked := atoms.fold (·.insert ·) tracked
          changed := true
  let mut out := #[]
  for i in [0:facts.size] do
    if included[i]! then
      let e := facts[i]!.1
      if e.hasMVar then return none
      out := out.push e
  return some out

/-- Does `e` contain a shift by a non-literal (free-variable-dependent) amount? `bv_omega` turns
    `x <<< k` into `x.toNat * 2 ^ k.toNat`, which `omega` cannot use, and such goals can take
    seconds per failing attempt (e.g. a prefix mask `~~~0 <<< (k &&& 31)`). -/
def hasSymbolicShift (e : Expr) : Bool :=
  (e.find? fun s =>
    ((s.isAppOfArity `HShiftLeft.hShiftLeft 6 || s.isAppOfArity `HShiftRight.hShiftRight 6) &&
      (s.getArg! 5).hasFVar) ||
    ((s.isAppOfArity `BitVec.shiftLeft 3 || s.isAppOfArity `BitVec.ushiftRight 3 ||
      s.isAppOfArity `BitVec.sshiftRight 3) && (s.getArg! 2).hasFVar) ||
    ((s.isAppOfArity `BitVec.shiftLeftRec 4 || s.isAppOfArity `BitVec.ushiftRightRec 4 ||
      s.isAppOfArity `BitVec.sshiftRightRec 4) && (s.getArg! 2).hasFVar)).isSome

/-- Does `e` contain a bitwise `BitVec` operation (`&&&`, `|||`, `^^^`, `~~~`)? Truncations and
    extensions of such terms are covered because the search visits all subterms. -/
def hasBitwise (e : Expr) : Bool :=
  (e.find? fun s =>
    (s.isAppOfArity ``HAnd.hAnd 6 || s.isAppOfArity ``HOr.hOr 6 || s.isAppOfArity ``HXor.hXor 6) &&
      (s.getArg! 0).isAppOf ``BitVec ||
    (s.isAppOfArity ``Complement.complement 3 && (s.getArg! 0).isAppOf ``BitVec) ||
    s.isAppOf ``BitVec.and || s.isAppOf ``BitVec.or || s.isAppOf ``BitVec.xor ||
    s.isAppOf ``BitVec.not).isSome

/-- Does `e` have `Nat`/`Int` arithmetic structure that `omega` reasons about natively
    (`toNat`, `Nat`/`Int` comparisons or arithmetic, or `BitVec.ult`/`ule`, which `wp_bv_omega`
    rewrites to `toNat` comparisons)? -/
def hasNatStructure (e : Expr) : Bool :=
  (e.find? fun s =>
    s.isAppOf ``BitVec.toNat || s.isAppOf ``BitVec.toInt || s.isAppOf ``BitVec.ult ||
    s.isAppOf ``BitVec.ule ||
    ((s.isAppOfArity ``LT.lt 4 || s.isAppOfArity ``LE.le 4) &&
      ((s.getArg! 0).isConstOf ``Nat || (s.getArg! 0).isConstOf ``Int)) ||
    ((s.isAppOfArity ``HAdd.hAdd 6 || s.isAppOfArity ``HSub.hSub 6 ||
      s.isAppOfArity ``HMul.hMul 6 || s.isAppOfArity ``HMod.hMod 6 ||
      s.isAppOfArity ``HDiv.hDiv 6) &&
      ((s.getArg! 0).isConstOf ``Nat || (s.getArg! 0).isConstOf ``Int))).isSome

/-- Decide whether `goal` should try `bv_decide` before the `omega` family, returning
    `(bitwiseFirst, natStructure)`:

    * `bitwiseFirst`: a hypothesis or `let`-value in `relevantCtx goal` contains a bitwise
      operation, and `goal` itself has neither a bitwise operation nor `Nat`/`toNat` structure
      (`hasNatStructure`). Masked hypothesis terms are opaque atoms to `omega` unless they also
      appear in `goal`, whereas goals with bitwise or `Nat` structure are tried with `omega` first.
    * `natStructure`: the goal or relevant context has `Nat`/`toNat` structure, so the `omega`
      family is worth trying after `bv_decide` fails.

    Falls back to `(false, true)` if the relevant context cannot be computed. -/
def classify (goal : Expr) : MetaM (Bool × Bool) := do
  let goal ← instantiateMVars goal
  let some ctx ← relevantCtx goal | return (false, true)
  let bitwiseFirst := !hasBitwise goal && !hasNatStructure goal && ctx.any hasBitwise
  return (bitwiseFirst, (ctx.push goal).any hasNatStructure)

end

end ProofLib.CondClassify
