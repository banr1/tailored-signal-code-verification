/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SimpAttrs

/-!
# `[wp_proj_guard]` Simp Attribute and Table-Projection Guards

Pre-order `dsimproc ↓` guards and term predicates preventing `dsimp` and `simp` from unfolding
concrete image, library, relocation, and symbol-table projections into deep `List.cons` spines.
-/

/-- Simp set of pre-order `dsimproc ↓` guards preventing `dsimp`/`simp` from reducing table-valued
    structure projections on concrete image, library, or layout constants. -/
register_simp_attr wp_proj_guard

namespace ProofLib

open Lean Meta

public meta section

/-- True when `e` is a local variable (`cdecl`, not a `let`-binding with a value) or a chain of
    1-argument structure projections rooted at one. Projection reduction on such a receiver never
    materializes a concrete table literal. -/
partial def isProjChainFromVar (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if let .fvar fvarId := e then
    match ← fvarId.findDecl? with
    | some decl => return !decl.hasValue
    | none => return true
  if let .proj _ _ s := e then
    return ← isProjChainFromVar s
  if e.getAppNumArgs == 1 then
    if let .const nm _ := e.getAppFn.consumeMData then
      if (← getProjectionFnInfo? nm).isSome then
        return ← isProjChainFromVar (e.getArg! 0)
  return false

/-- True when `e` is a `List.cons` spine of length at least `limit` (indicating an inline concrete
    table literal whose traversal in `dsimp`/`simp` risks exceeding `maxRecDepth`). -/
partial def hasDeepListSpine (e : Expr) (limit : Nat := 32) : Bool :=
  match limit with
  | 0 => true
  | limit' + 1 =>
    let e := e.consumeMData
    if e.isAppOfArity ``List.cons 3 then
      hasDeepListSpine (e.getArg! 2) limit'
    else
      false

/-- Build a `dsimproc ↓` for a 1-argument table-valued structure projection `projName` (of
    constructor `ctorName`) that stops `dsimp`/`simp` before `reduceProj?` / `reduceProjFn?`
    unfolds concrete image, library, or symbol-table constants into deep `List.cons` spines.
    Reduction still proceeds on explicit unfold requests (`simp [ProjName]`), local-variable
    receivers, small inline structure literals (list spines `< 32`), and wrapper heads in
    `allowHeads` (e.g. `(P.rebase b H).symbols` to `P.symbols`). -/
def guardConcreteTableProj (projName ctorName : Name)
    (allowHeads : Array Name := #[]) : Simp.DSimproc := fun e => do
  let ctx ← Simp.getContext
  if ctx.isDeclToUnfold projName then
    return .continue
  let eClean := e.consumeMData
  let recv? : Option Expr :=
    match eClean with
    | .proj structName _ s =>
      if ctx.isDeclToUnfold structName then none else some s.consumeMData
    | _ =>
      if eClean.getAppNumArgs == 1 then some (eClean.getArg! 0).consumeMData else none
  let some recv := recv? | return .continue
  if ← isProjChainFromVar recv then
    return .continue
  if let .const nm _ := recv.getAppFn.consumeMData then
    if nm == ctorName then
      if recv.getAppArgs.any (hasDeepListSpine · 32) then
        return .done e
      else
        return .continue
    if allowHeads.contains nm || ctx.isDeclToUnfold nm then
      return .continue
  return .done e

/-- True when `nm` is an object, image, interned-library, placed-library, or ELF record type whose
    fields carry concrete code, symbol, relocation, or layout tables. -/
def isGuardedTableTypeName (nm : Name) : Bool :=
  nm == `Arm64.Obj.Image || nm == `Arm64.Obj.LinkedImage ||
  nm == `Arm64.Obj.ObjectInfo || nm == `Arm64.Obj.SymCodeInfo ||
  nm == `Arm64.Obj.SymDataInfo || nm == `Arm64.Obj.CodeBlock ||
  nm == `Arm64.Obj.PlacedLib || nm == `Arm64.Obj.MultiPlacedLib ||
  nm == `Arm64.Obj.MultiPlacedLib.SymIndex || nm == `Arm64.Obj.RelocFnIndex ||
  nm == `Arm64.Process.ElfImage ||
  nm == `Arm64.Obj.Interned.Lib || nm == `Arm64.Obj.Interned.Layout ||
  nm == `Arm64.Obj.Interned.Block || nm == `Arm64.Obj.Interned.MultiLib ||
  nm == `Arm64.Obj.Interned.MultiLayout

/-- True when `e` mentions a projection or constant from an object, image, interned-library,
    placed-library, or symbol-lookup table whose ground evaluation via `simp (config := { decide := true })`
    (`Simp.simpUsingDecide`) would unfold concrete multi-hundred-entry tables in `whnf`. -/
def hasGuardedTableTerm (e : Expr) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .proj structName _ _ => isGuardedTableTypeName structName
    | .const nm _ =>
      isGuardedTableTypeName nm.getPrefix ||
      nm == `Arm64.Obj.lookup || nm == `Arm64.Obj.lookupUnique ||
      nm == `Arm64.Obj.lookupBlockSym || nm == `Arm64.Obj.lookupBlockSymAux ||
      nm == `Arm64.Obj.lookupSymInLists
    | _ => false).isSome

/-- True when `e` contains a closed ground `Prop` subexpression (`!hasLooseBVars && !hasFVar && !hasMVar`)
    mentioning a guarded table term, where `simp (config := { decide := true })` (`Simp.simpUsingDecide`)
    could synthesize `Decidable` and unfold concrete multi-hundred-entry tables in `whnf`. Non-`Prop`
    terms (such as `lib.dataInit pl : SepProp`) and propositions containing local variables (`pl`, `s0`)
    return `false` so ground arithmetic `decide` reduction stays active. -/
partial def hasGroundGuardedTableProp (e : Expr) : MetaM Bool := do
  if !hasGuardedTableTerm e then
    return false
  let rec visit (t : Expr) : MetaM Bool := do
    let t := t.consumeMData
    if !hasGuardedTableTerm t then
      return false
    if !t.hasLooseBVars && !t.hasFVar && !t.hasMVar then
      if ← Meta.isProp t then
        return true
    match t with
    | .app f a => visit f <||> visit a
    | .lam _ d b _ | .forallE _ d b _ => visit d <||> visit b
    | .letE _ ty val body _ =>
      visit ty <||> visit val <||>
        (if body.hasLooseBVars then visit (body.instantiate1 val) else visit body)
    | .proj _ _ s => visit s
    | _ => return false
  visit e

/-- True when `e` applies a table projection, library address helper, or symbol-table lookup to a
    non-variable receiver. Local-variable receivers (`img.base`, `lib.fnAddr pl s`, `s0.symtab`,
    `lookupBlockSym "fn" blocks`) return `false`. -/
def hasConcreteGuardedTableTerm (e : Expr) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .proj structName _ s =>
      isGuardedTableTypeName structName && !s.consumeMData.isFVar
    | .app .. =>
      if let .const nm _ := sub.getAppFn.consumeMData then
        let n := sub.getAppNumArgs
        if isGuardedTableTypeName nm.getPrefix && nm.getString! != "mk" then
          let recvIdx :=
            if nm.getPrefix == `Arm64.Obj.MultiPlacedLib.SymIndex ||
               nm.getPrefix == `Arm64.Obj.RelocFnIndex ||
               nm == `Arm64.Obj.LinkedImage.toProgramWithSvc ||
               nm == `Arm64.Obj.MultiPlacedLib.withCodeLoaded ||
               nm == `Arm64.Obj.Interned.Block.idsOk ||
               nm == `Arm64.Obj.Interned.Block.toCodeBlock then 1
            else if nm == `Arm64.Obj.PlacedLib.subroutineOk ||
                    nm == `Arm64.Obj.MultiPlacedLib.subroutineOk then 3
            else 0
          n > recvIdx && !(sub.getArg! recvIdx).consumeMData.isFVar
        else if (nm == `Arm64.Obj.lookup || nm == `Arm64.Obj.lookupUnique ||
                 nm == `Arm64.Obj.Interned.lookupId ||
                 nm == `Arm64.Obj.lookupBlockSymAux ||
                 nm == `Arm64.Obj.lookupSymInLists ||
                 nm == `Arm64.Obj.Interned.lookupBlockSymIdAux) && n >= 3 then
          !(sub.getArg! 2).consumeMData.isFVar
        else if (nm == `Arm64.Obj.lookupBlockSym ||
                 nm == `Arm64.Obj.Interned.lookupBlockSymId) && n >= 2 then
          !(sub.getArg! 1).consumeMData.isFVar
        else
          false
      else
        false
    | _ => false).isSome

/-- True when `e` contains an inline `List.cons` spine of length `>= 64`, or a concrete guarded
    structure projection that reduces at `@[reducible]` transparency (as in `DiscrTree.mkPath`) to
    a `List.cons` spine of length `>= 64`. `def`-backed libraries and small inline fixtures return
    `false` so rewrite hypotheses such as `lib.text.target pl r = addr` remain eligible in `simp`
    and `wp_sym_steps`. -/
partial def hasReducibleDeepListSpine (e : Expr) : MetaM Bool := do
  if (e.find? (hasDeepListSpine · 64)).isSome then
    return true
  if !hasConcreteGuardedTableTerm e then
    return false
  let rec visit (t : Expr) : MetaM Bool := do
    let t := t.consumeMData
    match t with
    | .proj structName _ s =>
      if isGuardedTableTypeName structName && !s.consumeMData.isFVar then
        let red ← withReducible (whnf t)
        if hasDeepListSpine red 64 then
          return true
      visit s
    | .app f a =>
      if t.getAppNumArgs == 1 then
        if let .const nm _ := t.getAppFn.consumeMData then
          if isGuardedTableTypeName nm.getPrefix && !(t.getArg! 0).consumeMData.isFVar then
            if (← getProjectionFnInfo? nm).isSome then
              let red ← withReducible (whnf t)
              if hasDeepListSpine red 64 then
                return true
      visit f <||> visit a
    | .lam _ d b _ | .forallE _ d b _ => visit d <||> visit b
    | .letE _ ty val body _ => visit ty <||> visit val <||> visit body
    | _ => return false
  visit e

/-- Register paired pre-order `dsimproc ↓ [arm64_norm, wp_norm, wp_proj_guard]` guards for both
    primitive dot-projections `((_ : Struct).field)` (`Key.proj`) and prefix projection calls
    `(Struct.field _)` (`Key.const`). -/
elab "declare_wp_proj_guard " baseName:ident structId:ident field:ident
    projNameTerm:term:max ctorNameTerm:term:max allow?:(colGt term:max)? : command => do
  let dotName := Lean.mkIdent (baseName.getId.eraseMacroScopes.appendAfter "Dot")
  let appName := Lean.mkIdent (baseName.getId.eraseMacroScopes.appendAfter "App")
  let projId := Lean.mkIdent (structId.getId.eraseMacroScopes ++ field.getId.eraseMacroScopes)
  let attrArm64 := Lean.mkIdent `arm64_norm
  let attrWp := Lean.mkIdent `wp_norm
  let attrGuard := Lean.mkIdent `wp_proj_guard
  let body ← match allow? with
    | some allow => `(ProofLib.guardConcreteTableProj $projNameTerm $ctorNameTerm $allow)
    | none => `(ProofLib.guardConcreteTableProj $projNameTerm $ctorNameTerm)
  Lean.Elab.Command.elabCommand (← `(command|
    dsimproc ↓ [$attrArm64:ident, $attrWp:ident, $attrGuard:ident] $dotName ((_ : $structId).$field) := $body))
  Lean.Elab.Command.elabCommand (← `(command|
    dsimproc ↓ [$attrArm64:ident, $attrWp:ident, $attrGuard:ident] $appName ($projId _) := $body))

end

end ProofLib
