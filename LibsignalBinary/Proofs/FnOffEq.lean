/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.SepLogic.CodeLookup
public meta import Lean -- shake: keep

/-!
# `fnoff_eq`: elaboration-time `fnOff` / `fnAddr` / `stubOff` / `hookAtOff?` solver

Closes concrete symbol-offset, entry-address, and extern-hook lookup goals via
`ProofLib.CodeLookup` without unfolding generated `*Code` constants or `Program.fnOff` in either
the elaborator or the kernel.
-/

@[expose] public section

namespace CryptoVerification.FnOffEq

theorem rebase_base_eq (p : Arm64.Program) (b : BitVec 64)
    (X O : String → Option (Arm64.State → Arm64.State)) :
    (p.rebase b X O).base = b := rfl

theorem rebase_fnOff_eq (p : Arm64.Program) (b : BitVec 64)
    (X O : String → Option (Arm64.State → Arm64.State)) (s : String) :
    (p.rebase b X O).fnOff s = p.fnOff s := rfl

theorem fnOff_of_rebase (prog c : Arm64.Program) (s : String) (off : Nat)
    (hprog : prog.fnOff s = c.fnOff s) (hoff : c.fnOff s = off) :
    prog.fnOff s = off :=
  hprog.trans hoff

theorem fnAddr_of_rebase (prog c : Arm64.Program) (b : BitVec 64) (s : String) (off : Nat)
    (hbase : prog.base = b) (hprog : prog.fnOff s = c.fnOff s) (hoff : c.fnOff s = off) :
    prog.fnAddr s = b + BitVec.ofNat 64 off := by
  unfold Arm64.Program.fnAddr
  rw [hbase, hprog, hoff]

theorem fnAddr_of_base (prog c : Arm64.Program) (s : String) (off : Nat)
    (hprog : prog = c) (hoff : c.fnOff s = off) :
    prog.fnAddr s = prog.base + BitVec.ofNat 64 off := by
  subst hprog
  unfold Arm64.Program.fnAddr
  rw [hoff]

theorem stubOff_of_fnOff (lhs : BitVec 64) (c : Arm64.Program) (s : String) (off : Nat)
    (hlhs : lhs = BitVec.ofNat 64 (c.fnOff s)) (hoff : c.fnOff s = off) :
    lhs = BitVec.ofNat 64 off :=
  hlhs.trans (congrArg (BitVec.ofNat 64) hoff)

public meta section MetaImpl

open Lean Meta Elab Tactic

/-- Return `true` when `e` is any `*.stubOff` constant. -/
def isStubOffConst (e : Expr) : Bool :=
  match e.consumeMData with
  | .const (.str _ "stubOff") _ => true
  | _ => false

/-- Match a 1-argument `stubOff sym` application for any `*.stubOff` constant, stripping `Expr.mdata`. -/
def matchStubOff? (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .app hd a =>
    if isStubOffConst hd then some a else none
  | _ => none

/-- Match a 2-argument constant application `fn a1 a2`, stripping any `Expr.mdata` wrappers. -/
def matchApp2? (e : Expr) (fnName : Name) : Option (Expr × Expr) :=
  match e.consumeMData with
  | .app f a2 =>
    match f.consumeMData with
    | .app hd a1 =>
      if hd.consumeMData.isConstOf fnName then some (a1, a2) else none
    | _ => none
  | _ => none

/-- Return `true` when `cname` has generated `fnOff` or `stubOff` layout lemmas in the environment. -/
def isBaseCodeConst (cname : Name) : MetaM Bool := do
  if !(← ProofLib.CodeLookup.entries cname .fnOff).isEmpty then
    return true
  if !(← ProofLib.CodeLookup.entries cname .stubOff).isEmpty then
    return true
  return false

/-- Resolved form of a `Program` expression, obtained by unfolding lightweight wrapper definitions
without unfolding generated `*Code` constants. -/
inductive ResolvedProg where
  | base (codeName : Name) (codeExpr : Expr)
  | rebased (codeName : Name) (codeExpr : Expr) (b X O : Expr)

/-- Resolve `progExpr : Arm64.Program` to either a base `*Code` constant or `c.rebase b X O`
    using bounded `unfoldDefinition?` without ever unfolding a base `*Code` constant. -/
partial def resolveProg (progExpr : Expr) (fuel : Nat := 16) : MetaM ResolvedProg := do
  let cur := progExpr.consumeMData
  if let .const cname _ := cur then
    if ← isBaseCodeConst cname then
      return .base cname cur
  if cur.isAppOfArity ``Arm64.Program.rebase 4 then
    let args := cur.getAppArgs
    let inner ← resolveProg args[0]! fuel
    match inner with
    | .base codeName codeExpr =>
      return .rebased codeName codeExpr args[1]! args[2]! args[3]!
    | .rebased codeName codeExpr _ _ _ =>
      return .rebased codeName codeExpr args[1]! args[2]! args[3]!
  if fuel == 0 then
    throwError "fnoff_eq: exhausted fuel resolving `Program` expression `{progExpr}`"
  if let .const cname _ := cur.getAppFn.consumeMData then
    if ← isBaseCodeConst cname then
      throwError "fnoff_eq: unexpected application of base code constant `{cur}`"
  match ← unfoldDefinition? cur with
  | some next => resolveProg next (fuel - 1)
  | none =>
    throwError "fnoff_eq: cannot resolve `Program` expression `{progExpr}` to a generated `*Code` constant"

/-- Builds `(offExpr, hoff)` with `hoff : Arm64.Program.fnOff codeExpr symExpr = offExpr` via `@id`
so the kernel unfolds at most `symExpr` and never `codeExpr` or `Program.fnOff`. -/
def mkBaseFnOffEq (codeName : Name) (codeExpr symExpr : Expr) : MetaM (Expr × Expr) := do
  let some sym ← ProofLib.CodeLookup.evalStringExpr? symExpr
    | throwError "fnoff_eq: cannot resolve symbol name `{symExpr}` to a concrete String literal"
  let entry ← ProofLib.CodeLookup.lookupOff codeName sym
  let ci ← getConstInfo entry.decl
  let offExpr :=
    if ci.type.isAppOfArity ``Eq 3 then ci.type.appArg!
    else mkNatLit entry.val
  let rawProof := mkConst entry.decl
  let isExactLit :=
    match symExpr with
    | .lit (.strVal s) => s == sym
    | _ => false
  if isExactLit && codeExpr.isConstOf codeName then
    return (offExpr, rawProof)
  let expectedEq := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat)
    (mkApp2 (mkConst ``Arm64.Program.fnOff) codeExpr symExpr)
    offExpr
  let wrapped := mkApp2 (mkConst ``id [Level.zero]) expectedEq rawProof
  return (offExpr, wrapped)

/-- Build `(α, rhs, heq)` with `heq : occ = rhs` for a single `fnOff`, `fnAddr`, or `stubOff`
    occurrence `occ`. -/
def buildRewriteForOcc (occ : Expr) : MetaM (Expr × Expr × Expr) := do
  let natTy := mkConst ``Nat
  let bv64Ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
  if let some (progExpr, symExpr) := matchApp2? occ ``Arm64.Program.fnOff then
    match ← resolveProg progExpr with
    | .base codeName codeExpr =>
      let (offExpr, hoff) ← mkBaseFnOffEq codeName codeExpr symExpr
      if progExpr == codeExpr then
        let expectedEq := mkApp3 (mkConst ``Eq [Level.one]) natTy occ offExpr
        return (natTy, offExpr, mkApp2 (mkConst ``id [Level.zero]) expectedEq hoff)
      else
        let hprogEqTy := mkApp3 (mkConst ``Eq [Level.one]) natTy
          occ
          (mkApp2 (mkConst ``Arm64.Program.fnOff) codeExpr symExpr)
        let hprog := mkApp2 (mkConst ``id [Level.zero]) hprogEqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (mkApp2 (mkConst ``Arm64.Program.fnOff) codeExpr symExpr))
        let pf := mkAppN (mkConst ``fnOff_of_rebase) #[progExpr, codeExpr, symExpr, offExpr, hprog, hoff]
        let expectedEq := mkApp3 (mkConst ``Eq [Level.one]) natTy occ offExpr
        return (natTy, offExpr, mkApp2 (mkConst ``id [Level.zero]) expectedEq pf)
    | .rebased codeName codeExpr b X O =>
      let (offExpr, hoff) ← mkBaseFnOffEq codeName codeExpr symExpr
      let hprogTy := mkApp3 (mkConst ``Eq [Level.one]) natTy
        (mkApp2 (mkConst ``Arm64.Program.fnOff) progExpr symExpr)
        (mkApp2 (mkConst ``Arm64.Program.fnOff) codeExpr symExpr)
      let hprogRaw := mkAppN (mkConst ``rebase_fnOff_eq) #[codeExpr, b, X, O, symExpr]
      let hprog := mkApp2 (mkConst ``id [Level.zero]) hprogTy hprogRaw
      let pf := mkAppN (mkConst ``fnOff_of_rebase) #[progExpr, codeExpr, symExpr, offExpr, hprog, hoff]
      let expectedEq := mkApp3 (mkConst ``Eq [Level.one]) natTy occ offExpr
      return (natTy, offExpr, mkApp2 (mkConst ``id [Level.zero]) expectedEq pf)
  else if let some (progExpr, symExpr) := matchApp2? occ ``Arm64.Program.fnAddr then
    match ← resolveProg progExpr with
    | .base codeName codeExpr =>
      let (offExpr, hoff) ← mkBaseFnOffEq codeName codeExpr symExpr
      let progEqTy := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Arm64.Program) progExpr codeExpr
      let hprog := mkApp2 (mkConst ``id [Level.zero]) progEqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Arm64.Program) codeExpr)
      let rhs := mkApp6 (mkConst ``HAdd.hAdd [Level.zero, Level.zero, Level.zero])
        bv64Ty bv64Ty bv64Ty
        (← synthInstance (mkApp3 (mkConst ``HAdd [Level.zero, Level.zero, Level.zero]) bv64Ty bv64Ty bv64Ty))
        (mkApp (mkConst ``Arm64.Program.base) progExpr)
        (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) offExpr)
      let pf := mkAppN (mkConst ``fnAddr_of_base) #[progExpr, codeExpr, symExpr, offExpr, hprog, hoff]
      let expectedEq := mkApp3 (mkConst ``Eq [Level.one]) bv64Ty occ rhs
      return (bv64Ty, rhs, mkApp2 (mkConst ``id [Level.zero]) expectedEq pf)
    | .rebased codeName codeExpr b X O =>
      let (offExpr, hoff) ← mkBaseFnOffEq codeName codeExpr symExpr
      let hbaseTy := mkApp3 (mkConst ``Eq [Level.one]) bv64Ty
        (mkApp (mkConst ``Arm64.Program.base) progExpr) b
      let hbase := mkApp2 (mkConst ``id [Level.zero]) hbaseTy
        (mkAppN (mkConst ``rebase_base_eq) #[codeExpr, b, X, O])
      let hprogTy := mkApp3 (mkConst ``Eq [Level.one]) natTy
        (mkApp2 (mkConst ``Arm64.Program.fnOff) progExpr symExpr)
        (mkApp2 (mkConst ``Arm64.Program.fnOff) codeExpr symExpr)
      let hprog := mkApp2 (mkConst ``id [Level.zero]) hprogTy
        (mkAppN (mkConst ``rebase_fnOff_eq) #[codeExpr, b, X, O, symExpr])
      let addInst ← synthInstance (mkApp3 (mkConst ``HAdd [Level.zero, Level.zero, Level.zero]) bv64Ty bv64Ty bv64Ty)
      let rhs := mkApp6 (mkConst ``HAdd.hAdd [Level.zero, Level.zero, Level.zero])
        bv64Ty bv64Ty bv64Ty addInst b (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) offExpr)
      let pf := mkAppN (mkConst ``fnAddr_of_rebase) #[progExpr, codeExpr, b, symExpr, offExpr, hbase, hprog, hoff]
      let expectedEq := mkApp3 (mkConst ``Eq [Level.one]) bv64Ty occ rhs
      return (bv64Ty, rhs, mkApp2 (mkConst ``id [Level.zero]) expectedEq pf)
  else if let some symExpr := matchStubOff? occ then
    let some unfolded ← unfoldDefinition? occ.consumeMData
      | throwError "fnoff_eq: cannot unfold `{occ}`"
    let some (progExpr, _) := matchApp2? unfolded.appArg! ``Arm64.Program.fnOff
      | throwError "fnoff_eq: unexpected `stubOff` body `{unfolded}`"
    let .base codeName codeExpr ← resolveProg progExpr
      | throwError "fnoff_eq: expected base code constant in `stubOff`, got `{progExpr}`"
    let (offExpr, hoff) ← mkBaseFnOffEq codeName codeExpr symExpr
    let rhs := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) offExpr
    let hlhsTy := mkApp3 (mkConst ``Eq [Level.one]) bv64Ty occ
      (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkApp2 (mkConst ``Arm64.Program.fnOff) codeExpr symExpr))
    let hlhs := mkApp2 (mkConst ``id [Level.zero]) hlhsTy
      (mkApp2 (mkConst ``Eq.refl [Level.one]) bv64Ty unfolded)
    let pf := mkAppN (mkConst ``stubOff_of_fnOff) #[occ, codeExpr, symExpr, offExpr, hlhs, hoff]
    return (bv64Ty, rhs, pf)
  else
    throwError "fnoff_eq: internal error: unrecognized occurrence `{occ}`"

/-- Replace every subterm syntactically equal (`==`) to closed/fvar term `occ` with `.bvar depth`
    without calling `Meta.isDefEq` or `whnf`. -/
partial def abstractExact (e : Expr) (occ : Expr) (depth : Nat := 0) : Expr :=
  if e == occ then
    .bvar depth
  else
    match e with
    | .app f a => .app (abstractExact f occ depth) (abstractExact a occ depth)
    | .lam n t b bi => .lam n (abstractExact t occ depth) (abstractExact b occ (depth + 1)) bi
    | .forallE n t b bi => .forallE n (abstractExact t occ depth) (abstractExact b occ (depth + 1)) bi
    | .letE n t v b nd =>
      .letE n (abstractExact t occ depth) (abstractExact v occ depth) (abstractExact b occ (depth + 1)) nd
    | .mdata m b => .mdata m (abstractExact b occ depth)
    | .proj tn idx s => .proj tn idx (abstractExact s occ depth)
    | _ => e

/-- Collect outermost `fnOff`, `fnAddr`, and `stubOff` subterms in `e` that have no loose bvars. -/
partial def collectOutermostOccs (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let checkNode : Bool :=
    !e.isMData && !e.hasLooseBVars &&
      ((matchApp2? e ``Arm64.Program.fnOff).isSome ||
       (matchApp2? e ``Arm64.Program.fnAddr).isSome ||
       (matchStubOff? e).isSome)
  if checkNode then
    if acc.contains e then acc else acc.push e
  else
    match e with
    | .app f a => collectOutermostOccs a (collectOutermostOccs f acc)
    | .lam _ t b _ => collectOutermostOccs b (collectOutermostOccs t acc)
    | .forallE _ t b _ => collectOutermostOccs b (collectOutermostOccs t acc)
    | .letE _ t v b _ => collectOutermostOccs b (collectOutermostOccs v (collectOutermostOccs t acc))
    | .mdata _ b => collectOutermostOccs b acc
    | .proj _ _ s => collectOutermostOccs s acc
    | _ => acc

/-- Rewrite `occ` to `rhs` in `mvarId`'s target using `heq : occ = rhs` and syntactic abstraction. -/
def rewriteOccInGoal (mvarId : MVarId) (α occ rhs heq : Expr) : MetaM MVarId :=
  mvarId.withContext do
    let T ← instantiateMVars (← mvarId.getType)
    let body := abstractExact T occ 0
    let T' := body.instantiate1 rhs
    let motive := Expr.lam `_x α body .default
    let hPropEq := mkApp6 (mkConst ``congrArg [Level.one, Level.one])
      α (mkSort Level.zero) occ rhs motive heq
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar T' (← mvarId.getTag)
    let proof := mkApp4 (mkConst ``Eq.mpr [Level.zero]) T T' hPropEq mvarNew
    mvarId.assign proof
    return mvarNew.mvarId!

/-- Check whether `O` is syntactically `fun _ => none` (`Option.none`). -/
def isDefaultNoneOverrides (O : Expr) : Bool :=
  match O.consumeMData with
  | .lam _ _ body _ => body.consumeMData.isAppOf ``Option.none
  | _ => false

/-- Close `(c.rebase b H).hookAtOff? offLit = H sym` directly via `<code>_hookAtOff?_...`
    when the goal has that shape. Returns `true` if closed. -/
def tryCloseHookAtOff (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let T ← instantiateMVars (← mvarId.getType)
    let Tc := T.consumeMData
    if !Tc.isAppOfArity ``Eq 3 then return false
    let lhs := Tc.getArg! 1
    let rhs := Tc.getArg! 2
    let some (progExpr, offExpr) := matchApp2? lhs ``Arm64.Program.hookAtOff?
      | return false
    let .app hFn symExpr := rhs.consumeMData
      | throwError "fnoff_eq: expected `H sym` on RHS of `hookAtOff?` goal `{T}`"
    let .rebased codeName _ b X O ← resolveProg progExpr
      | throwError "fnoff_eq: expected rebased program in `hookAtOff?` goal `{T}`"
    unless isDefaultNoneOverrides O do
      throwError "fnoff_eq: non-empty override table in `hookAtOff?` goal `{T}`"
    unless hFn.consumeMData == X.consumeMData do
      throwError "fnoff_eq: hook function mismatch between `{X}` and `{hFn}` in `{T}`"
    let some sym ← ProofLib.CodeLookup.evalStringExpr? symExpr
      | throwError "fnoff_eq: cannot resolve hook symbol `{symExpr}` to a String literal"
    let some offVal ← ProofLib.CodeLookup.evalNatExpr? offExpr
      | throwError "fnoff_eq: hook offset `{offExpr}` did not reduce to a numeral"
    let entry ← ProofLib.CodeLookup.lookup codeName .hookAtOff sym
    unless entry.val == offVal do
      throwError "fnoff_eq: hook offset mismatch for {repr sym}: goal has {offVal}, table has {entry.val}"
    let rawProof := mkApp2 (mkConst entry.decl) b X
    let wrapped := mkApp2 (mkConst ``id [Level.zero]) T rawProof
    mvarId.assign wrapped
    return true

/-- Fail closed if any `Program.fnOff`, `Program.fnAddr`, `stubOff`, or `Program.hookAtOff?`
    remains anywhere in `e`. -/
def ensureNoResidualFnOff (e : Expr) : MetaM Unit := do
  let bad? := e.find? fun sub =>
    sub.isConstOf ``Arm64.Program.fnOff ||
    sub.isConstOf ``Arm64.Program.fnAddr ||
    isStubOffConst sub ||
    sub.isConstOf ``Arm64.Program.hookAtOff?
  if let some bad := bad? then
    throwError "fnoff_eq: residual `{bad}` remains in goal `{e}`; refusing to fall back to kernel/simp unfolding"

/-- Core `TacticM` implementation of `fnoff_eq`. -/
def fnoffEqTac : TacticM Unit := do
  let (_, mvar0) ← (← getMainGoal).intros
  let mut mvarId := mvar0
  for _ in [:8] do
    let T ← mvarId.withContext do instantiateMVars (← mvarId.getType)
    let occs := collectOutermostOccs T
    if occs.isEmpty then break
    for occ in occs do
      let (α, rhs, heq) ← mvarId.withContext do buildRewriteForOcc occ
      mvarId ← rewriteOccInGoal mvarId α occ rhs heq
  if ← tryCloseHookAtOff mvarId then
    replaceMainGoal []
    return
  let Tfinal ← mvarId.withContext do instantiateMVars (← mvarId.getType)
  ensureNoResidualFnOff Tfinal
  if let some (_, lhs, rhs) := Tfinal.consumeMData.eq? then
    if lhs == rhs then
      mvarId.assign (← mvarId.withContext do Meta.mkEqRefl lhs)
      replaceMainGoal []
      return
  replaceMainGoal [mvarId]
  if !Tfinal.hasFVar then
    evalTactic (← `(tactic| first | (rfl; done) | (omega; done) | (bv_arith; done) | (bv_omega; done)))
  else
    evalTactic (← `(tactic| first | (omega; done) | (bv_arith; done) | (bv_omega; done) | (rfl; done)))

end MetaImpl

end CryptoVerification.FnOffEq

/-- Close concrete `Program.fnOff` / `Program.fnAddr` / `stubOff` / `Program.hookAtOff?` offset
    and address goals via `ProofLib.CodeLookup` without unfolding `Program.fnOff` or `*Code`
    constants in either the elaborator or the kernel. -/
elab "fnoff_eq" : tactic => CryptoVerification.FnOffEq.fnoffEqTac
