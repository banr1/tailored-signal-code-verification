/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public import Computational.Proofs.SpecLemmas.Reductions.ReductionDsl.Core

/-!
# Syntactic Sugar for `ReductionDsl`

Compile-time macros (`rdsl`, `rdslRaw`, `rdslExpr`, `rdslExprRaw`) for writing `ReductionDsl.Comp`
and `ReductionDsl.Expr` ASTs with `do` notation, named lexical binders and tuple/`as`-patterns, and
`Option`/`Bool`/nested-`Sum` pattern matching (`rdsl_pat`). Every construct expands at
macro-expansion time directly into raw `ReductionDsl` constructors.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.ReductionDsl.Notation

open Lean Parser.Term

/-- Extensible pattern category for constructor-named sum arms inside `rdsl` and `rdslExpr`. -/
declare_syntax_cat rdsl_pat

scoped syntax term : rdsl_pat

/-- Monadic `ReductionDsl.Comp` block with optional innermost-first context binder list. -/
scoped syntax "rdsl" ("[" term,* "]")? "do" doSeq : term

/-- Monadic `ReductionDsl.Comp` block emitting `Expr.var (.succ^k .zero)` instead of `Expr.v0..v7`. -/
scoped syntax "rdslRaw" ("[" term,* "]")? "do" doSeq : term

/-- Pure `ReductionDsl.Expr` block with optional innermost-first context binder list. -/
scoped syntax "rdslExpr" ("[" term,* "]")? "=>" term : term

/-- Pure `ReductionDsl.Expr` block emitting `Expr.var (.succ^k .zero)` instead of `Expr.v0..v7`. -/
scoped syntax "rdslExprRaw" ("[" term,* "]")? "=>" term : term

meta inductive ProjStep where
  | fst
  | snd
  deriving Repr, BEq

meta inductive Binding where
  | var (slotId : Nat) (path : List ProjStep)
  | letAlias (rhs : TSyntax `term) (savedBindings : List (Name × Binding))

/-- Macro-time lexical context mapping active de Bruijn slot IDs (`v0` innermost) and `let` aliases. -/
meta structure Ctx where
  nextId : Nat := 0
  slots : List Nat := []
  bindings : List (Name × Binding) := []
  rawVars : Bool := false

meta def Ctx.pushAnon (ctx : Ctx) : Ctx :=
  { ctx with nextId := ctx.nextId + 1, slots := ctx.nextId :: ctx.slots }

meta def Ctx.addAlias (ctx : Ctx) (nm : Name) (rhs : TSyntax `term) : Ctx :=
  { ctx with bindings := (nm, .letAlias rhs ctx.bindings) :: ctx.bindings }

meta def Ctx.lookup? (ctx : Ctx) (nm : Name) : Option Binding :=
  ctx.bindings.findSome? fun (k, v) => if k == nm then some v else none

meta def findSlotIdx? (slots : List Nat) (slotId : Nat) : Option Nat :=
  let rec go : List Nat → Nat → Option Nat
    | [], _ => none
    | s :: ss, i => if s == slotId then some i else go ss (i + 1)
  go slots 0

meta def mkVarSuccs (idx : Nat) (base : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut v := base
  for _ in [:idx] do
    v ← `(ReductionDsl.Var.succ $v)
  return v

meta def mkVarSyntax (idx : Nat) : MacroM (TSyntax `term) := do
  let z ← `(ReductionDsl.Var.zero)
  mkVarSuccs idx z

/-- Emits `Expr.v0..v7` by default, or `Expr.var (.succ^idx .zero)` when `rawVars` is set. -/
meta def mkExprVarSyntax (rawVars : Bool) (idx : Nat) : MacroM (TSyntax `term) := do
  if !rawVars then
    match idx with
    | 0 => return (← `(ReductionDsl.Expr.v0))
    | 1 => return (← `(ReductionDsl.Expr.v1))
    | 2 => return (← `(ReductionDsl.Expr.v2))
    | 3 => return (← `(ReductionDsl.Expr.v3))
    | 4 => return (← `(ReductionDsl.Expr.v4))
    | 5 => return (← `(ReductionDsl.Expr.v5))
    | 6 => return (← `(ReductionDsl.Expr.v6))
    | 7 => return (← `(ReductionDsl.Expr.v7))
    | _ => pure ()
  let v ← mkVarSyntax idx
  `(ReductionDsl.Expr.var $v)

meta def applyProjPath (base : TSyntax `term) (path : List ProjStep) : MacroM (TSyntax `term) := do
  let mut e := base
  for step in path do
    e ← match step with
      | .fst => `(ReductionDsl.Expr.fst $e)
      | .snd => `(ReductionDsl.Expr.snd $e)
  return e

meta partial def stripParens (stx : TSyntax `term) : TSyntax `term :=
  if stx.raw.getKind == ``Lean.Parser.Term.paren && stx.raw.getNumArgs == 3 then
    let inner := stx.raw[1]
    if inner.isMissing || inner.getKind == nullKind then stx
    else stripParens ⟨inner⟩
  else
    stx

meta partial def bindPatAt (bindings : List (Name × Binding)) (slotId : Nat)
    (path : List ProjStep) (pat : TSyntax `term) : MacroM (List (Name × Binding)) := do
  let p := stripParens pat
  if p.raw.isIdent then
    let nm := p.raw.getId
    if nm == `_ || nm == ``Unit.unit then
      return bindings
    else
      return (nm, .var slotId path) :: bindings
  else if p.raw.getKind == ``Lean.Parser.Term.namedPattern && p.raw.getNumArgs >= 3 then
    let x := p.raw[0]
    let sub : TSyntax `term := ⟨p.raw[p.raw.getNumArgs - 1]!⟩
    let b1 :=
      if x.isIdent && x.getId != `_ then (x.getId, .var slotId path) :: bindings else bindings
    bindPatAt b1 slotId path sub
  else
    match p with
    | `(_) => return bindings
    | `(()) | `(.unit) | `(Unit.unit) => return bindings
    | `(($pSub:term : $_ty:term)) => bindPatAt bindings slotId path pSub
    | `(($a:term, $bs:term,*)) =>
      let elems := #[a] ++ bs.getElems
      let rec goTuple (idx : Nat) (curPath : List ProjStep)
          (acc : List (Name × Binding)) : MacroM (List (Name × Binding)) := do
        if h : idx + 1 < elems.size then
          let acc' ← bindPatAt acc slotId (curPath ++ [.fst]) elems[idx]
          goTuple (idx + 1) (curPath ++ [.snd]) acc'
        else if h2 : idx < elems.size then
          bindPatAt acc slotId curPath elems[idx]
        else
          return acc
      goTuple 0 path bindings
    | _ =>
      Macro.throwErrorAt pat s!"rdsl: unsupported binder pattern `{pat}`"

meta def pushBinderPat (ctx : Ctx) (pat : TSyntax `term) : MacroM Ctx := do
  let slotId := ctx.nextId
  let bindings' ← bindPatAt ctx.bindings slotId [] pat
  return { ctx with
    nextId := slotId + 1
    slots := slotId :: ctx.slots
    bindings := bindings'
  }

meta def initCtx (pats : Array (TSyntax `term)) (rawVars : Bool := false) : MacroM Ctx := do
  let mut ctx : Ctx := { rawVars := rawVars }
  for pat in pats.reverse do
    ctx ← pushBinderPat ctx pat
  return ctx

meta def unpackFun? (stx : TSyntax `term) : Option (Array (TSyntax `term) × TSyntax `term) :=
  let s := stripParens stx
  if s.raw.getKind == ``Lean.Parser.Term.fun && s.raw.getNumArgs >= 2 then
    let bf := s.raw[1]
    if bf.getKind == ``Lean.Parser.Term.basicFun && bf.getNumArgs >= 4 then
      let binders := bf[0].getArgs.map (⟨·⟩)
      let body : TSyntax `term := ⟨bf[3]⟩
      some (binders, body)
    else
      none
  else
    none

meta def getDoElems (seq : TSyntax ``doSeq) : MacroM (Array (TSyntax `doElem)) := do
  if seq.raw.getKind == ``Lean.Parser.Term.doSeqIndent && seq.raw.getNumArgs >= 1 then
    return seq.raw[0].getArgs.map fun item => ⟨item[0]⟩
  else if seq.raw.getKind == ``Lean.Parser.Term.doSeqBracketed && seq.raw.getNumArgs >= 2 then
    return seq.raw[1].getArgs.map fun item => ⟨item[0]⟩
  else
    Macro.throwErrorAt seq "rdsl: unsupported `do` sequence syntax"

meta def unpackDoIf? (el : TSyntax `doElem) :
    Option (TSyntax `term × TSyntax ``doSeq × Array (TSyntax `term × TSyntax ``doSeq) × TSyntax ``doSeq) :=
  if el.raw.getKind == ``Lean.Parser.Term.doIf && el.raw.getNumArgs >= 6 then
    let prop0 := el.raw[1]
    let elseNode := el.raw[5]
    if prop0.getKind == ``Lean.Parser.Term.doIfProp && prop0.getNumArgs >= 2 &&
        elseNode.getNumArgs >= 2 then
      let c0 : TSyntax `term := ⟨prop0[1]⟩
      let t0 : TSyntax ``doSeq := ⟨el.raw[3]⟩
      let elseIfs := el.raw[4].getArgs.filterMap fun g =>
        if g.getNumArgs >= 4 && g[1].getKind == ``Lean.Parser.Term.doIfProp && g[1].getNumArgs >= 2 then
          some ((⟨g[1][1]⟩ : TSyntax `term), (⟨g[3]⟩ : TSyntax ``doSeq))
        else
          none
      let f0 : TSyntax ``doSeq := ⟨elseNode[1]⟩
      some (c0, t0, elseIfs, f0)
    else
      none
  else
    none

meta def unpackMatchCore? (node : Syntax) (discrIdx altsIdx : Nat) :
    Option (TSyntax `term × Array (TSyntax `term) × Array Syntax) := Id.run do
  if node.getNumArgs <= altsIdx then return none
  let discrs := node[discrIdx]
  let altsNode := node[altsIdx]
  if discrs.getNumArgs != 1 then return none
  let d0 := discrs[0]
  if d0.getKind != ``Lean.Parser.Term.matchDiscr || d0.getNumArgs < 2 then return none
  if altsNode.getKind != ``Lean.Parser.Term.matchAlts || altsNode.getNumArgs < 1 then return none
  let scrut : TSyntax `term := ⟨d0[1]⟩
  let mut pats : Array (TSyntax `term) := #[]
  let mut rhss : Array Syntax := #[]
  for alt in altsNode[0].getArgs do
    if alt.getKind != ``Lean.Parser.Term.matchAlt || alt.getNumArgs < 4 then return none
    let patGroups := alt[1].getArgs
    if patGroups.isEmpty then return none
    for g in patGroups do
      if g.getNumArgs != 1 then return none
      pats := pats.push ⟨g[0]⟩
      rhss := rhss.push alt[3]
  return some (scrut, pats, rhss)

meta def unpackTermMatch? (stx : TSyntax `term) :
    Option (TSyntax `term × Array (TSyntax `term) × Array (TSyntax `term)) :=
  if stx.raw.getKind == ``Lean.Parser.Term.match then
    match unpackMatchCore? stx.raw 3 5 with
    | some (scrut, pats, rhss) => some (scrut, pats, rhss.map (⟨·⟩))
    | none => none
  else
    none

meta def unpackDoMatch? (el : TSyntax `doElem) :
    Option (TSyntax `term × Array (TSyntax `term) × Array (TSyntax ``doSeq)) :=
  if el.raw.getKind == ``Lean.Parser.Term.doMatch then
    match unpackMatchCore? el.raw 4 6 with
    | some (scrut, pats, rhss) => some (scrut, pats, rhss.map (⟨·⟩))
    | none => none
  else
    none

meta inductive SumPat where
  | leaf (pat : TSyntax `term)
  | inl (inner : SumPat)
  | inr (inner : SumPat)
  deriving Inhabited

meta partial def parseSumPat (fuel : Nat) (pat : TSyntax `term) : MacroM SumPat := do
  let p := stripParens pat
  match p with
  | `(.inl $sub:term) | `(Sum.inl $sub:term) =>
    return .inl (← parseSumPat fuel sub)
  | `(.inr $sub:term) | `(Sum.inr $sub:term) =>
    return .inr (← parseSumPat fuel sub)
  | _ =>
    if fuel > 0 then
      let patCat ← `(rdsl_pat| $p:term)
      match ← Macro.expandMacro? patCat with
      | some expanded =>
        match (⟨expanded⟩ : TSyntax `rdsl_pat) with
        | `(rdsl_pat| $p':term) => return (← parseSumPat (fuel - 1) p')
        | _ => return .leaf p
      | none => return .leaf p
    else
      return .leaf p

meta partial def expandPatTerm (fuel : Nat) (pat : TSyntax `term) : MacroM (TSyntax `term) := do
  let p := stripParens pat
  if fuel == 0 then return p
  let patCat ← `(rdsl_pat| $p:term)
  match ← Macro.expandMacro? patCat with
  | some expanded =>
    match (⟨expanded⟩ : TSyntax `rdsl_pat) with
    | `(rdsl_pat| $p':term) => expandPatTerm (fuel - 1) p'
    | _ => return p
  | none => return p

meta def isNonePat (pat : TSyntax `term) : Bool :=
  let p := stripParens pat
  match p with
  | `(none) | `(.none) | `(Option.none) => true
  | _ => false

meta def isSomePat? (pat : TSyntax `term) : Option (TSyntax `term) :=
  let p := stripParens pat
  match p with
  | `(some $sub:term) | `(.some $sub:term) | `(Option.some $sub:term) => some sub
  | _ => none

meta def isBoolPat? (pat : TSyntax `term) : Option Bool :=
  let p := stripParens pat
  match p with
  | `(true) | `(.true) | `(Bool.true) => some true
  | `(false) | `(.false) | `(Bool.false) => some false
  | _ => none

/-- Compiles sum pattern arms into nested `.caseSum` nodes, pushing an anonymous remainder slot at
each non-leaf split. -/
meta partial def compileSumArms {α : Type} (ref : Syntax)
    (scrutExpr : TSyntax `term) (ctx : Ctx) (arms : List (SumPat × α))
    (mkCaseSum : TSyntax `term → TSyntax `term → TSyntax `term → MacroM (TSyntax `term))
    (expandLeaf : Ctx → TSyntax `term → α → MacroM (TSyntax `term)) :
    MacroM (TSyntax `term) := do
  let mut inlArms : List (SumPat × α) := []
  let mut inrArms : List (SumPat × α) := []
  for (sp, rhs) in arms do
    match sp with
    | .inl sub => inlArms := inlArms ++ [(sub, rhs)]
    | .inr sub => inrArms := inrArms ++ [(sub, rhs)]
    | .leaf p =>
      Macro.throwErrorAt p
        "rdsl: mixed leaf/constructor sum pattern in `match`; expected `.inl ...` or `.inr ...`"
  if inlArms.isEmpty then
    Macro.throwErrorAt ref "rdsl: non-exhaustive sum `match` (missing `.inl` branch)"
  if inrArms.isEmpty then
    Macro.throwErrorAt ref "rdsl: non-exhaustive sum `match` (missing `.inr` branch)"
  let v0 ← mkExprVarSyntax ctx.rawVars 0
  let lOut ← match inlArms with
    | [(.leaf pat, rhs)] => expandLeaf ctx pat rhs
    | _ => compileSumArms ref v0 ctx.pushAnon inlArms mkCaseSum expandLeaf
  let rOut ← match inrArms with
    | [(.leaf pat, rhs)] => expandLeaf ctx pat rhs
    | _ => compileSumArms ref v0 ctx.pushAnon inrArms mkCaseSum expandLeaf
  mkCaseSum scrutExpr lOut rOut

meta def resolveDirectSlotIdx (ctx : Ctx) (x : Ident) : MacroM Nat := do
  match ctx.lookup? x.getId with
  | some (.var slotId []) =>
    match findSlotIdx? ctx.slots slotId with
    | some idx => return idx
    | none => Macro.throwErrorAt x s!"rdsl: internal error: slot for `{x.getId}` not in scope"
  | some (.var _ (_ :: _)) =>
    Macro.throwErrorAt x
      s!"rdsl: `{x.getId}` is a projected tuple field, not a standalone `Var` slot"
  | some (.letAlias _ _) =>
    Macro.throwErrorAt x s!"rdsl: `{x.getId}` is a `let` alias, not a `Var` slot"
  | none =>
    Macro.throwErrorAt x s!"rdsl: unknown variable `{x.getId}`"

meta def isHeadOneOf (fn : Syntax) (names : List Name) : Bool :=
  if fn.isIdent then
    let id := fn.getId
    names.any fun nm =>
      id == nm ||
      id == (`Expr ++ nm) ||
      id == (`Comp ++ nm) ||
      id == (`ReductionDsl.Expr ++ nm) ||
      id == (`ReductionDsl.Comp ++ nm)
  else if fn.getKind == ``Lean.Parser.Term.dotIdent && fn.getNumArgs >= 2 && fn[1].isIdent then
    names.contains fn[1].getId
  else
    false

meta partial def compileMatch {α : Type} [Inhabited α] (ref : Syntax) (ctx : Ctx)
    (scrut : TSyntax `term) (pats : Array (TSyntax `term)) (rhss : Array α)
    (mkIte : TSyntax `term → TSyntax `term → TSyntax `term → MacroM (TSyntax `term))
    (mkCaseOpt : TSyntax `term → TSyntax `term → TSyntax `term → MacroM (TSyntax `term))
    (mkCaseSum : TSyntax `term → TSyntax `term → TSyntax `term → MacroM (TSyntax `term))
    (expandPlain : Ctx → α → MacroM (TSyntax `term)) :
    MacroM (TSyntax `term) := do
  let expPats ← pats.mapM (expandPatTerm 16)
  if expPats.size == 2 then
    if isNonePat expPats[0]! then
      if let some someSub := isSomePat? expPats[1]! then
        let nBranch ← expandPlain ctx rhss[0]!
        let ctxSome ← pushBinderPat ctx someSub
        let sBranch ← expandPlain ctxSome rhss[1]!
        return (← mkCaseOpt scrut nBranch sBranch)
    if isNonePat expPats[1]! then
      if let some someSub := isSomePat? expPats[0]! then
        let nBranch ← expandPlain ctx rhss[1]!
        let ctxSome ← pushBinderPat ctx someSub
        let sBranch ← expandPlain ctxSome rhss[0]!
        return (← mkCaseOpt scrut nBranch sBranch)
    if let (some b0, some b1) := (isBoolPat? expPats[0]!, isBoolPat? expPats[1]!) then
      if b0 == true && b1 == false then
        return (← mkIte scrut (← expandPlain ctx rhss[0]!) (← expandPlain ctx rhss[1]!))
      if b0 == false && b1 == true then
        return (← mkIte scrut (← expandPlain ctx rhss[1]!) (← expandPlain ctx rhss[0]!))
  let mut sumArms : List (SumPat × α) := []
  for i in [:pats.size] do
    let sp ← parseSumPat 16 pats[i]!
    sumArms := sumArms ++ [(sp, rhss[i]!)]
  compileSumArms ref scrut ctx sumArms mkCaseSum fun ctxLeaf leafPat rhs => do
    let ctx' ← pushBinderPat ctxLeaf leafPat
    expandPlain ctx' rhs

meta partial def expandExprSyntax?
    (rec : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (ctx : Ctx) (s : TSyntax `term) : MacroM (Option (TSyntax `term)) := do
  match s with
  | `(()) | `(.unit) =>
    return some (← `(ReductionDsl.Expr.unit))
  | `(.true) =>
    return some (← `(ReductionDsl.Expr.bool true))
  | `(.false) =>
    return some (← `(ReductionDsl.Expr.bool false))
  | `(.none) =>
    return some (← `(ReductionDsl.Expr.none))
  | `([]) | `(.nil) =>
    return some (← `(ReductionDsl.Expr.nil))
  | `([$xs:term,*]) =>
    let mut acc ← `(ReductionDsl.Expr.nil)
    for x in xs.getElems.reverse do
      acc ← `(ReductionDsl.Expr.cons $(← rec ctx x) $acc)
    return some acc
  | `($n:num) =>
    return some (← `(ReductionDsl.Expr.nat $n))
  | _ => pure ()

  match s with
  | `(($a:term, $bs:term,*)) =>
    let elems := #[a] ++ bs.getElems
    let mut acc ← rec ctx elems.back!
    for i in [:elems.size - 1] do
      let idx := elems.size - 2 - i
      acc ← `(ReductionDsl.Expr.pair $(← rec ctx elems[idx]!) $acc)
    return some acc
  | `(($e:term : $ty:term)) =>
    return some (← `(($(← rec ctx e) : $ty)))
  | `($x:term :: $xs:term) =>
    return some (← `(ReductionDsl.Expr.cons $(← rec ctx x) $(← rec ctx xs)))
  | `(if $c:term then $t:term else $f:term) =>
    return some (← `(ReductionDsl.Expr.ite $(← rec ctx c) $(← rec ctx t) $(← rec ctx f)))
  | `(let $x:ident := $v:term; $b:term) =>
    return some (← rec (ctx.addAlias x.getId v) b)
  | `(let $x:ident : $_ty:term := $v:term; $b:term) =>
    return some (← rec (ctx.addAlias x.getId v) b)
  | _ => pure ()

  match s with
  | `($a:term + $b:term) =>
    return some (← `(ReductionDsl.Expr.add $(← rec ctx a) $(← rec ctx b)))
  | `($a:term - $b:term) =>
    return some (← `(ReductionDsl.Expr.sub $(← rec ctx a) $(← rec ctx b)))
  | `($k:term * $a:term) =>
    return some (← `(ReductionDsl.Expr.mulK $k $(← rec ctx a)))
  | `($a:term / $k:term) =>
    return some (← `(ReductionDsl.Expr.divK $k $(← rec ctx a)))
  | `($a:term % $k:term) =>
    return some (← `(ReductionDsl.Expr.modK $k $(← rec ctx a)))
  | _ => pure ()

  match s with
  | `($a:term < $b:term) =>
    return some (← `(ReductionDsl.Expr.lt $(← rec ctx a) $(← rec ctx b)))
  | `($a:term == $b:term) =>
    return some (← `(ReductionDsl.Expr.eqN $(← rec ctx a) $(← rec ctx b)))
  | `(!$a:term) =>
    return some (← `(ReductionDsl.Expr.not $(← rec ctx a)))
  | `($a:term && $b:term) =>
    return some (← `(ReductionDsl.Expr.and $(← rec ctx a) $(← rec ctx b)))
  | _ => return none

meta partial def expandExprPureApp?
    (rec : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (ctx : Ctx) (fn : Syntax) (args : Array Syntax) : MacroM (Option (TSyntax `term)) := do
  if isHeadOneOf fn [`nat] && args.size == 1 then
    return some (← `(ReductionDsl.Expr.nat $(⟨args[0]!⟩)))
  if isHeadOneOf fn [`bool] && args.size == 1 then
    return some (← `(ReductionDsl.Expr.bool $(⟨args[0]!⟩)))
  if isHeadOneOf fn [`fst] && args.size == 1 then
    return some (← `(ReductionDsl.Expr.fst $(← rec ctx ⟨args[0]!⟩)))
  if isHeadOneOf fn [`snd] && args.size == 1 then
    return some (← `(ReductionDsl.Expr.snd $(← rec ctx ⟨args[0]!⟩)))
  if isHeadOneOf fn [`pair] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.pair $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if (isHeadOneOf fn [`inl] || fn.getId == ``Sum.inl) && args.size == 1 then
    return some (← `(ReductionDsl.Expr.inl $(← rec ctx ⟨args[0]!⟩)))
  if (isHeadOneOf fn [`inr] || fn.getId == ``Sum.inr) && args.size == 1 then
    return some (← `(ReductionDsl.Expr.inr $(← rec ctx ⟨args[0]!⟩)))
  if (isHeadOneOf fn [`some] || fn.getId == ``Option.some) && args.size == 1 then
    return some (← `(ReductionDsl.Expr.some $(← rec ctx ⟨args[0]!⟩)))
  if isHeadOneOf fn [`add] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.add $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`sub] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.sub $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`mulK] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.mulK $(⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`divK] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.divK $(⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`modK] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.modK $(⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`lt] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.lt $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`eqN] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.eqN $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`not] && args.size == 1 then
    return some (← `(ReductionDsl.Expr.not $(← rec ctx ⟨args[0]!⟩)))
  if isHeadOneOf fn [`and] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.and $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`ite] && args.size == 3 then
    return some (← `(ReductionDsl.Expr.ite $(← rec ctx ⟨args[0]!⟩)
      $(← rec ctx ⟨args[1]!⟩) $(← rec ctx ⟨args[2]!⟩)))
  if isHeadOneOf fn [`op] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.op $(⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`cons] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.cons $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`len] && args.size == 1 then
    return some (← `(ReductionDsl.Expr.len $(← rec ctx ⟨args[0]!⟩)))
  if isHeadOneOf fn [`take] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.take $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`appendL] && args.size == 3 then
    return some (← `(ReductionDsl.Expr.appendL $(⟨args[0]!⟩)
      $(← rec ctx ⟨args[1]!⟩) $(← rec ctx ⟨args[2]!⟩)))
  if isHeadOneOf fn [`tconst] && args.size == 1 then
    return some (← `(ReductionDsl.Expr.tconst $(← rec ctx ⟨args[0]!⟩)))
  if isHeadOneOf fn [`tget] && args.size == 2 then
    return some (← `(ReductionDsl.Expr.tget $(← rec ctx ⟨args[0]!⟩) $(← rec ctx ⟨args[1]!⟩)))
  if isHeadOneOf fn [`tset] && args.size == 3 then
    return some (← `(ReductionDsl.Expr.tset $(← rec ctx ⟨args[0]!⟩)
      $(← rec ctx ⟨args[1]!⟩) $(← rec ctx ⟨args[2]!⟩)))
  return none

meta partial def expandExprBinderApp?
    (rec : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (ctx : Ctx) (fn : Syntax) (args : Array Syntax) : MacroM (Option (TSyntax `term)) := do
  if isHeadOneOf fn [`letE] && args.size == 2 then
    let val ← rec ctx ⟨args[0]!⟩
    let fnArg : TSyntax `term := ⟨args[1]!⟩
    let bodyOut ← match unpackFun? fnArg with
      | some (#[pat], body) => do
        let ctx' ← pushBinderPat ctx pat
        rec ctx' body
      | _ => rec ctx.pushAnon fnArg
    return some (← `(ReductionDsl.Expr.letE $val $bodyOut))
  if isHeadOneOf fn [`findB] && args.size == 3 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← rec ctx ⟨args[1]!⟩
    let fnArg : TSyntax `term := ⟨args[2]!⟩
    let bodyOut ← match unpackFun? fnArg with
      | some (#[pat], body) => do
        let ctx' ← pushBinderPat ctx pat
        rec ctx' body
      | _ => rec ctx.pushAnon fnArg
    return some (← `(ReductionDsl.Expr.findB $K $l $bodyOut))
  if isHeadOneOf fn [`anyB] && args.size == 3 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← rec ctx ⟨args[1]!⟩
    let fnArg : TSyntax `term := ⟨args[2]!⟩
    let bodyOut ← match unpackFun? fnArg with
      | some (#[pat], body) => do
        let ctx' ← pushBinderPat ctx pat
        rec ctx' body
      | _ => rec ctx.pushAnon fnArg
    return some (← `(ReductionDsl.Expr.anyB $K $l $bodyOut))
  if isHeadOneOf fn [`mapB] && args.size == 3 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← rec ctx ⟨args[1]!⟩
    let fnArg : TSyntax `term := ⟨args[2]!⟩
    let bodyOut ← match unpackFun? fnArg with
      | some (#[pat], body) => do
        let ctx' ← pushBinderPat ctx pat
        rec ctx' body
      | _ => rec ctx.pushAnon fnArg
    return some (← `(ReductionDsl.Expr.mapB $K $l $bodyOut))
  if isHeadOneOf fn [`foldrB] && args.size == 4 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← rec ctx ⟨args[1]!⟩
    let z ← rec ctx ⟨args[2]!⟩
    let fnArg : TSyntax `term := ⟨args[3]!⟩
    let bodyOut ← match unpackFun? fnArg with
      | some (#[xPat, accPat], body) => do
        let ctxAcc ← pushBinderPat ctx accPat
        let ctxStep ← pushBinderPat ctxAcc xPat
        rec ctxStep body
      | _ => rec ctx.pushAnon.pushAnon fnArg
    return some (← `(ReductionDsl.Expr.foldrB $K $l $z $bodyOut))
  return none

mutual

/-- Substitutes bound DSL variables inside a host Lean syntax tree (`raw` or named arguments),
leaving host literals, operators, and constructors untouched. -/
meta partial def substVarsOnly (ctx : Ctx) (stx : Syntax) : MacroM Syntax := do
  if stx.isIdent then
    match ctx.lookup? stx.getId with
    | some _ =>
      let e ← expandExpr ctx ⟨stx⟩
      return e.raw
    | none => return stx
  else
    match stx with
    | .node info kind args =>
      if kind == ``Lean.Parser.Term.dotIdent then
        return stx
      else if kind == ``Lean.Parser.Term.namedArgument && args.size >= 4 then
        let mut args' := args
        for i in [2 : args.size] do
          args' := args'.set! i (← substVarsOnly ctx args[i]!)
        return .node info kind args'
      else if kind == ``Lean.Parser.Term.proj && args.size >= 3 then
        let mut args' := args
        args' := args'.set! 0 (← substVarsOnly ctx args[0]!)
        return .node info kind args'
      else
        let args' ← args.mapM (substVarsOnly ctx)
        return .node info kind args'
    | _ => return stx

meta partial def expandExpr (ctx : Ctx) (stx : TSyntax `term) : MacroM (TSyntax `term) := do
  let s := stripParens stx
  if s.raw.getKind == ``Lean.Parser.Term.app && s.raw.getNumArgs >= 2 then
    let fn := s.raw[0]
    let args := s.raw[1].getArgs
    if fn.isIdent && args.size == 1 then
      let arg0 := stripParens ⟨args[0]!⟩
      if fn.getId == `raw then
        return ⟨← substVarsOnly ctx arg0.raw⟩
      if fn.getId == `extVar then
        let shifted ← mkVarSuccs ctx.slots.length arg0
        return (← `(ReductionDsl.Expr.var $shifted))
      if fn.getId == `parentVar then
        if !arg0.raw.isIdent then
          Macro.throwErrorAt arg0 "rdsl: `parentVar` expects an identifier"
        let x : Ident := ⟨arg0.raw⟩
        let idx ← resolveDirectSlotIdx ctx x
        if idx == 0 then
          Macro.throwErrorAt x
            s!"rdsl: `parentVar {x.getId}` requires `{x.getId}` to be outside the innermost binder"
        return (← mkVarSyntax (idx - 1))
      if fn.getId == `varOf then
        if !arg0.raw.isIdent then
          Macro.throwErrorAt arg0 "rdsl: `varOf` expects an identifier"
        let idx ← resolveDirectSlotIdx ctx ⟨arg0.raw⟩
        return (← mkVarSyntax idx)

  if s.raw.isIdent then
    let nm := s.raw.getId
    match ctx.lookup? nm with
    | some (.var slotId path) =>
      match findSlotIdx? ctx.slots slotId with
      | some idx =>
        let base ← mkExprVarSyntax ctx.rawVars idx
        return (← applyProjPath base path)
      | none =>
        Macro.throwErrorAt s s!"rdsl: internal error: slot for `{nm}` not found"
    | some (.letAlias rhs saved) =>
      return (← expandExpr { ctx with bindings := saved } rhs)
    | none =>
      if nm == ``true || nm == `true then
        return (← `(ReductionDsl.Expr.bool true))
      else if nm == ``false || nm == `false then
        return (← `(ReductionDsl.Expr.bool false))
      else if nm == ``Option.none || nm == `none then
        return (← `(ReductionDsl.Expr.none))
      else
        return s

  if s.raw.getKind == ``Lean.Parser.Term.proj && s.raw.getNumArgs >= 3 then
    let base : TSyntax `term := ⟨s.raw[0]⟩
    let fld := s.raw[2]
    if fld.getKind == `fieldIdx && fld.getNumArgs >= 1 then
      let idxStr := fld[0].getAtomVal
      if idxStr == "1" then
        return (← `(ReductionDsl.Expr.fst $(← expandExpr ctx base)))
      else if idxStr == "2" then
        return (← `(ReductionDsl.Expr.snd $(← expandExpr ctx base)))
    else if fld.isIdent then
      if fld.getId == `fst then
        return (← `(ReductionDsl.Expr.fst $(← expandExpr ctx base)))
      else if fld.getId == `snd then
        return (← `(ReductionDsl.Expr.snd $(← expandExpr ctx base)))
    return ⟨← substVarsOnly ctx s.raw⟩

  if let some (d, pats, rhss) := unpackTermMatch? s then
    let scrut ← expandExpr ctx d
    return (← compileMatch s.raw ctx scrut pats rhss
      (fun c t f => `(ReductionDsl.Expr.ite $c $t $f))
      (fun e n sm => `(ReductionDsl.Expr.caseOpt $e $n $sm))
      (fun e l r => `(ReductionDsl.Expr.caseSum $e $l $r))
      expandExpr)

  if let some out ← expandExprSyntax? expandExpr ctx s then
    return out

  if s.raw.getKind == ``Lean.Parser.Term.app && s.raw.getNumArgs >= 2 then
    let fn := s.raw[0]
    let args := s.raw[1].getArgs
    if let some out ← expandExprPureApp? expandExpr ctx fn args then
      return out
    if let some out ← expandExprBinderApp? expandExpr ctx fn args then
      return out
    let fn' ← substVarsOnly ctx fn
    let args' ← args.mapM fun a => do
      if a.getKind == ``Lean.Parser.Term.namedArgument then
        substVarsOnly ctx a
      else
        return (← expandExpr ctx ⟨a⟩).raw
    return ⟨Syntax.node .none ``Lean.Parser.Term.app #[fn', Syntax.node .none nullKind args']⟩
  return ⟨← substVarsOnly ctx s.raw⟩

end

private meta def expandCompSyntax?
    (recComp : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (recDoSeq : Ctx → TSyntax ``doSeq → MacroM (TSyntax `term))
    (ctx : Ctx) (s : TSyntax `term) : MacroM (Option (TSyntax `term)) := do
  match s with
  | `(do $seq:doSeq) =>
    return some (← recDoSeq ctx seq)
  | `(rdsl do $seq:doSeq) =>
    return some (← recDoSeq ctx seq)
  | `(pure $e:term) =>
    return some (← `(ReductionDsl.Comp.ret $(← expandExpr ctx e)))
  | `(if $c:term then $t:term else $f:term) =>
    return some (← `(ReductionDsl.Comp.ite $(← expandExpr ctx c)
      $(← recComp ctx t) $(← recComp ctx f)))
  | `(let $x:ident := $v:term; $b:term) =>
    return some (← recComp (ctx.addAlias x.getId v) b)
  | `(let $x:ident : $_ty:term := $v:term; $b:term) =>
    return some (← recComp (ctx.addAlias x.getId v) b)
  | `(($c:term : $ty:term)) =>
    return some (← `(($(← recComp ctx c) : $ty)))
  | _ =>
    return none

private meta def expandCompPrimApp?
    (recComp : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (ctx : Ctx) (fn : Syntax) (args : Array Syntax) : MacroM (Option (TSyntax `term)) := do
  if isHeadOneOf fn [`ret] && args.size >= 1 then
    let prefixArgs := args.extract 0 (args.size - 1)
    let lastExpr ← expandExpr ctx ⟨args.back!⟩
    let head ← `(ReductionDsl.Comp.ret)
    return some ⟨Syntax.node .none ``Lean.Parser.Term.app
      #[head.raw, Syntax.node .none nullKind (prefixArgs.push lastExpr.raw)]⟩
  if isHeadOneOf fn [`query] && args.size >= 2 then
    let prefixArgs ← (args.extract 0 (args.size - 1)).mapM (substVarsOnly ctx)
    let lastExpr ← expandExpr ctx ⟨args.back!⟩
    let head ← `(ReductionDsl.Comp.query)
    return some ⟨Syntax.node .none ``Lean.Parser.Term.app
      #[head.raw, Syntax.node .none nullKind (prefixArgs.push lastExpr.raw)]⟩
  if isHeadOneOf fn [`sample] && args.size >= 2 then
    let prefixArgs ← (args.extract 0 (args.size - 1)).mapM (substVarsOnly ctx)
    let lastExpr ← expandExpr ctx ⟨args.back!⟩
    let head ← `(ReductionDsl.Comp.sample)
    return some ⟨Syntax.node .none ``Lean.Parser.Term.app
      #[head.raw, Syntax.node .none nullKind (prefixArgs.push lastExpr.raw)]⟩
  if isHeadOneOf fn [`ite] && args.size == 3 then
    return some (← `(ReductionDsl.Comp.ite $(← expandExpr ctx ⟨args[0]!⟩)
      $(← recComp ctx ⟨args[1]!⟩) $(← recComp ctx ⟨args[2]!⟩)))
  return none

private meta def expandCompBinderApp?
    (recComp : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (ctx : Ctx) (fn : Syntax) (args : Array Syntax) : MacroM (Option (TSyntax `term)) := do
  if isHeadOneOf fn [`iter] && args.size == 3 then
    let n : TSyntax `term := ⟨args[0]!⟩
    let init ← expandExpr ctx ⟨args[1]!⟩
    let fnArg : TSyntax `term := ⟨args[2]!⟩
    match unpackFun? fnArg with
    | some (#[accPat], body) =>
      let ctx' ← pushBinderPat ctx accPat
      return some (← `(ReductionDsl.Comp.iter $n $init $(← recComp ctx' body)))
    | _ =>
      return some (← `(ReductionDsl.Comp.iter $n $init $(← recComp ctx.pushAnon fnArg)))
  if isHeadOneOf fn [`findM] && args.size == 3 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← expandExpr ctx ⟨args[1]!⟩
    let fnArg : TSyntax `term := ⟨args[2]!⟩
    match unpackFun? fnArg with
    | some (#[pat], body) =>
      let ctx' ← pushBinderPat ctx pat
      return some (← `(ReductionDsl.Comp.findM $K $l $(← recComp ctx' body)))
    | _ =>
      return some (← `(ReductionDsl.Comp.findM $K $l $(← recComp ctx.pushAnon fnArg)))
  if isHeadOneOf fn [`anyM] && args.size == 3 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← expandExpr ctx ⟨args[1]!⟩
    let fnArg : TSyntax `term := ⟨args[2]!⟩
    match unpackFun? fnArg with
    | some (#[pat], body) =>
      let ctx' ← pushBinderPat ctx pat
      return some (← `(ReductionDsl.Comp.anyM $K $l $(← recComp ctx' body)))
    | _ =>
      return some (← `(ReductionDsl.Comp.anyM $K $l $(← recComp ctx.pushAnon fnArg)))
  if isHeadOneOf fn [`mapM] && args.size == 3 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← expandExpr ctx ⟨args[1]!⟩
    let fnArg : TSyntax `term := ⟨args[2]!⟩
    match unpackFun? fnArg with
    | some (#[pat], body) =>
      let ctx' ← pushBinderPat ctx pat
      return some (← `(ReductionDsl.Comp.mapM $K $l $(← recComp ctx' body)))
    | _ =>
      return some (← `(ReductionDsl.Comp.mapM $K $l $(← recComp ctx.pushAnon fnArg)))
  if isHeadOneOf fn [`consumeFirstM] && args.size == 4 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← expandExpr ctx ⟨args[1]!⟩
    let testFn : TSyntax `term := ⟨args[2]!⟩
    let markFn : TSyntax `term := ⟨args[3]!⟩
    let testOut ← match unpackFun? testFn with
      | some (#[pat], body) => do
        let ctx' ← pushBinderPat ctx pat
        recComp ctx' body
      | _ => recComp ctx.pushAnon testFn
    let markOut ← match unpackFun? markFn with
      | some (#[pat], body) => do
        let ctx' ← pushBinderPat ctx pat
        expandExpr ctx' body
      | _ => expandExpr ctx.pushAnon markFn
    return some (← `(ReductionDsl.Comp.consumeFirstM $K $l $testOut $markOut))
  if isHeadOneOf fn [`foldM] && args.size == 4 then
    let K : TSyntax `term := ⟨args[0]!⟩
    let l ← expandExpr ctx ⟨args[1]!⟩
    let z ← expandExpr ctx ⟨args[2]!⟩
    let fnArg : TSyntax `term := ⟨args[3]!⟩
    match unpackFun? fnArg with
    | some (#[xPat, accPat], body) =>
      let ctxAcc ← pushBinderPat ctx accPat
      let ctxStep ← pushBinderPat ctxAcc xPat
      return some (← `(ReductionDsl.Comp.foldM $K $l $z $(← recComp ctxStep body)))
    | _ =>
      return some (← `(ReductionDsl.Comp.foldM $K $l $z $(← recComp ctx.pushAnon.pushAnon fnArg)))
  return none

private meta def expandDoTerminal
    (recComp : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (recDoSeq : Ctx → TSyntax ``doSeq → MacroM (TSyntax `term))
    (ctx : Ctx) (last : TSyntax `doElem) : MacroM (TSyntax `term) := do
  if let some (c, t, elseIfs, f) := unpackDoIf? last then
    let mut elseComp ← recDoSeq ctx f
    for i in [:elseIfs.size] do
      let (ci, ti) := elseIfs[elseIfs.size - 1 - i]!
      elseComp ← `(ReductionDsl.Comp.ite $(← expandExpr ctx ci)
        $(← recDoSeq ctx ti) $elseComp)
    return (← `(ReductionDsl.Comp.ite $(← expandExpr ctx c) $(← recDoSeq ctx t) $elseComp))
  if let some (d, pats, rhss) := unpackDoMatch? last then
    let scrut ← expandExpr ctx d
    return (← compileMatch last.raw ctx scrut pats rhss
      (fun c t f => `(ReductionDsl.Comp.ite $c $t $f))
      (fun e n sm => `(ReductionDsl.Comp.caseOpt $e $n $sm))
      (fun e l r => `(ReductionDsl.Comp.caseSum $e $l $r))
      recDoSeq)
  match last with
  | `(doElem| return $e:term) =>
    `(ReductionDsl.Comp.ret $(← expandExpr ctx e))
  | `(doElem| for $pat:term in ($K:term, $l:term) do $body:doSeq) =>
    let lExpr ← expandExpr ctx l
    let ctx' ← pushBinderPat ctx pat
    `(ReductionDsl.Comp.mapM $K $lExpr $(← recDoSeq ctx' body))
  | `(doElem| $t:term) =>
    recComp ctx t
  | _ =>
    Macro.throwErrorAt last "rdsl: unsupported terminal statement in `do` block"

private meta def expandDoStep
    (recComp : Ctx → TSyntax `term → MacroM (TSyntax `term))
    (recItems : Ctx → List (TSyntax `doElem) → MacroM (TSyntax `term))
    (ctx : Ctx) (first : TSyntax `doElem) (rest : List (TSyntax `doElem)) :
    MacroM (TSyntax `term) := do
  match first with
  | `(doElem| let $x:ident := $v:term) =>
    recItems (ctx.addAlias x.getId v) rest
  | `(doElem| let $x:ident : $_ty:term := $v:term) =>
    recItems (ctx.addAlias x.getId v) rest
  | `(doElem| $x:ident ← $rhs:doElem) | `(doElem| let $x:ident ← $rhs:doElem) =>
    let rhsComp ← recItems ctx [rhs]
    let patTerm : TSyntax `term := ⟨x.raw⟩
    let ctx' ← pushBinderPat ctx patTerm
    let bodyComp ← recItems ctx' rest
    `(ReductionDsl.Comp.bind $rhsComp $bodyComp)
  | `(doElem| $pat:term ← $rhs:doElem) | `(doElem| let $pat:term ← $rhs:doElem) =>
    let rhsComp ← recItems ctx [rhs]
    let ctx' ← pushBinderPat ctx pat
    let bodyComp ← recItems ctx' rest
    `(ReductionDsl.Comp.bind $rhsComp $bodyComp)
  | `(doElem| $c:term) =>
    let rhsComp ← recComp ctx c
    let bodyComp ← recItems ctx.pushAnon rest
    `(ReductionDsl.Comp.bind $rhsComp $bodyComp)
  | _ =>
    Macro.throwErrorAt first "rdsl: unsupported non-terminal statement in `do` block"

mutual

meta partial def expandCompTerm (ctx : Ctx) (stx : TSyntax `term) : MacroM (TSyntax `term) := do
  let s := stripParens stx
  if s.raw.getKind == ``Lean.Parser.Term.app && s.raw.getNumArgs >= 2 then
    let fn := s.raw[0]
    let args := s.raw[1].getArgs
    if fn.isIdent && fn.getId == `raw && args.size == 1 then
      let arg0 := stripParens ⟨args[0]!⟩
      return ⟨← substVarsOnly ctx arg0.raw⟩
  if let some (d, pats, rhss) := unpackTermMatch? s then
    let scrut ← expandExpr ctx d
    return (← compileMatch s.raw ctx scrut pats rhss
      (fun c t f => `(ReductionDsl.Comp.ite $c $t $f))
      (fun e n sm => `(ReductionDsl.Comp.caseOpt $e $n $sm))
      (fun e l r => `(ReductionDsl.Comp.caseSum $e $l $r))
      expandCompTerm)
  if let some out ← expandCompSyntax? expandCompTerm expandDoSeq ctx s then
    return out
  if s.raw.getKind == ``Lean.Parser.Term.app && s.raw.getNumArgs >= 2 then
    let fn := s.raw[0]
    let args := s.raw[1].getArgs
    if let some out ← expandCompPrimApp? expandCompTerm ctx fn args then
      return out
    if let some out ← expandCompBinderApp? expandCompTerm ctx fn args then
      return out
    let fn' ← substVarsOnly ctx fn
    let args' ← args.mapM fun a => do
      if a.getKind == ``Lean.Parser.Term.namedArgument then
        substVarsOnly ctx a
      else
        return (← expandExpr ctx ⟨a⟩).raw
    return ⟨Syntax.node .none ``Lean.Parser.Term.app #[fn', Syntax.node .none nullKind args']⟩
  return ⟨← substVarsOnly ctx s.raw⟩

meta partial def expandDoSeq (ctx : Ctx) (seq : TSyntax ``doSeq) : MacroM (TSyntax `term) := do
  let elems ← getDoElems seq
  expandDoItems ctx elems.toList

meta partial def expandDoItems (ctx : Ctx) (items : List (TSyntax `doElem)) :
    MacroM (TSyntax `term) := do
  match items with
  | [] => Macro.throwError "rdsl: empty `do` block"
  | [last] => expandDoTerminal expandCompTerm expandDoSeq ctx last
  | first :: rest => expandDoStep expandCompTerm expandDoItems ctx first rest

end

scoped macro_rules
  | `(rdsl [$pats:term,*] do $seq:doSeq) => do
    let ctx ← initCtx pats.getElems false
    expandDoSeq ctx seq
  | `(rdsl do $seq:doSeq) => do
    expandDoSeq { rawVars := false } seq
  | `(rdslRaw [$pats:term,*] do $seq:doSeq) => do
    let ctx ← initCtx pats.getElems true
    expandDoSeq ctx seq
  | `(rdslRaw do $seq:doSeq) => do
    expandDoSeq { rawVars := true } seq
  | `(rdslExpr [$pats:term,*] => $e:term) => do
    let ctx ← initCtx pats.getElems false
    expandExpr ctx e
  | `(rdslExpr => $e:term) => do
    expandExpr { rawVars := false } e
  | `(rdslExprRaw [$pats:term,*] => $e:term) => do
    let ctx ← initCtx pats.getElems true
    expandExpr ctx e
  | `(rdslExprRaw => $e:term) => do
    expandExpr { rawVars := true } e

end Computational.Proofs.ReductionDsl.Notation
