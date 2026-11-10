/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# Mechanical Theorem Variants (`#derive_variant`)

Commands for generating a theorem variant whose statement differs from an existing theorem by a
declared term substitution (for example, substituting an external hook table `H.ext` with a
fault-injecting variant `faultOnX H.ext`):

- `declare_variant_kind k (x : a) ... : src ==> tgt rename "a" ==> "b", ...` registers a
  pattern-substitution and constant-renaming kind `k`.
- `#derive_variant (k) tgt from src` translates the statement and proof term of `src` (or applies a
  conclusion transfer lemma `t` when invoked with `using t`).
- `variant_map (k) a => b` registers a checked constant translation for `k`.
- `#guard_same_type a b` checks that two constants have definitionally equal statements.

Every generated theorem is kernel-checked via `addDecl` synchronously (`Elab.async` disabled), and
any failed derivation rolls back the `Environment` to its pre-call state.
-/

@[expose] public section

namespace ProofLib.Variant

/-- `declare_variant_kind k (x : a) ... : src ==> tgt rename "a" ==> "b", ...` declares variant
    kind `k`. Every subterm matching `src` (where binders are pattern variables occurring in `src`)
    is replaced by `tgt`; any constant whose last name component contains `a` is mapped to the
    constant with `a` replaced by `b` when present in the environment. -/
syntax (name := declareVariantKind) "declare_variant_kind " ident ppSpace bracketedBinder* " : "
  term " ==> " term (" rename " sepBy1(str " ==> " str, ", "))? : command

/-- `variant_map (k) a => b` registers `b` as the `k`-variant of `a`, verifying that the statement
    of `b` matches the `k`-translation of the statement of `a`. -/
syntax (name := variantMap) "variant_map " "(" ident ") " ident " => " ident : command

/-- `#derive_variant (k) tgt from src` (or `#derive_variant (k) from src`, naming the result via
    the rename rules of `k`) derives theorem `tgt` as the `k`-variant of `src` by proof-term
    translation, or via `t (src ...)` when `using t` is supplied. A preceding doc comment is
    attached to `tgt`. -/
syntax (name := deriveVariant) (docComment)? "#derive_variant " "(" ident ") " (ident)? " from "
  ident (" using " term)? : command

/-- `#guard_same_type a b` verifies that constants `a` and `b` have definitionally equal statements
    at default transparency. -/
syntax (name := guardSameType) "#guard_same_type " ident ppSpace ident : command

end ProofLib.Variant

end

public meta section

namespace ProofLib.Variant

open Lean Meta Elab Command Term

/-- A variant kind: closed lambdas `source` and `target` over `numParams` pattern variables,
    together with substring replacement rules on constant names. -/
structure VariantKind where
  name : Name
  source : Expr
  target : Expr
  numParams : Nat
  renames : Array (String × String)
  deriving Inhabited

/-- Entry in the `variantExt` persistent environment extension. -/
inductive VariantEntry where
  | kind (k : VariantKind)
  | map (kind src tgt : Name)
  deriving Inhabited

/-- Persistent state of declared variant kinds and explicit per-kind constant translations. -/
structure VariantState where
  kinds : NameMap VariantKind := {}
  maps : NameMap (NameMap Name) := {}
  deriving Inhabited

def VariantState.add (s : VariantState) : VariantEntry → VariantState
  | .kind k => { s with kinds := s.kinds.insert k.name k }
  | .map k a b => { s with maps := s.maps.insert k (((s.maps.find? k).getD {}).insert a b) }

initialize variantExt : SimplePersistentEnvExtension VariantEntry VariantState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := VariantState.add
    addImportedFn := fun ess => ess.foldl (fun s es => es.foldl VariantState.add s) {}
  }

def getKind (k : Name) : CoreM VariantKind := do
  let some kind := (variantExt.getState (← getEnv)).kinds.find? k
    | throwError "unknown variant kind `{k}`; declare it with `declare_variant_kind`"
  return kind

def getMap (k : Name) : CoreM (NameMap Name) :=
  return ((variantExt.getState (← getEnv)).maps.find? k).getD {}

/-! ## Pattern Matching -/

/-- Strip the first `n` lambda binders from `e`, exposing loose de Bruijn indices `0 .. n - 1`. -/
def lambdaBody (e : Expr) : Nat → Expr
  | 0 => e
  | n + 1 => match e with
    | .lam _ _ b _ => lambdaBody b n
    | _ => e

/-- Structural match of pattern `p` against `e`. Loose bvars `< n` of `p` are pattern variables
    (assigned in `asg`); everything else must be equal. A pattern `S.f x` with `S.f` a structure
    projection function also matches the primitive projection `Expr.proj S i x`. -/
partial def matchPat (env : Environment) (n : Nat) (p e : Expr) (asg : Array (Option Expr)) :
    Option (Array (Option Expr)) :=
  match p, e with
  | .bvar i, _ =>
    if i < n then
      match asg[i]! with
      | none => some (asg.set! i (some e))
      | some e' => if e' == e then some asg else none
    else if p == e then some asg else none
  | .mdata _ p', _ => matchPat env n p' e asg
  | _, .mdata _ e' => matchPat env n p e' asg
  | .app f a, .app g b => do
    let asg ← matchPat env n f g asg
    matchPat env n a b asg
  | .app _ a, .proj s i x =>
    match p.getAppFn with
    | .const c _ =>
      match env.getProjectionFnInfo? c with
      | some info =>
        if info.i == i && p.getAppNumArgs == info.numParams + 1 &&
            (env.find? info.ctorName).any (fun ci => match ci with
              | .ctorInfo v => v.induct == s
              | _ => false) then
          matchPat env n a x asg
        else none
      | none => none
    | _ => none
  | _, _ => if p == e then some asg else none

/-! ## Translation -/

/-- Context of one `#derive_variant` run. -/
structure TCtx where
  kind : VariantKind
  srcBody : Expr
  tgtBody : Expr
  map : NameMap Name
  rootSrc : Name
  rootTgt : Name

/-- State: translation cache and translated auxiliary constants. -/
structure TState where
  cache : Std.HashMap Expr Expr := {}
  consts : NameMap (Option Name) := {}
  auxCount : Nat := 0

abbrev TM := ReaderT TCtx (StateRefT TState MetaM)

/-- Apply the rename rules of the kind to the last component of `n`. -/
def renameName (kind : VariantKind) (n : Name) : Name :=
  match n with
  | .str p s =>
    let s' := kind.renames.foldl (fun s (a, b) => s.replace a b) s
    .str p s'
  | _ => n

/-- Whether `c` is an auxiliary constant generated while elaborating `root`. -/
def isAuxOf (root c : Name) : Bool :=
  c.isInternalDetail || (privateToUserName root).isPrefixOf (privateToUserName c)

mutual

/-- Translate an expression (works under binders: it never needs types). -/
partial def visit (e : Expr) : TM Expr := do
  if let some r := (← get).cache[e]? then return r
  let ctx ← read
  let r ← do
    let env ← getEnv
    match matchPat env ctx.kind.numParams ctx.srcBody e (.replicate ctx.kind.numParams none) with
    | some asg =>
      let args ← asg.mapM fun a? => visit (a?.getD (mkSort 0))
      pure (ctx.tgtBody.instantiate args)
    | none =>
      match e with
      | .const c ls => do
        match ← translateConst c with
        | some c' => pure (.const c' ls)
        | none => pure e
      | .app f a => return e.updateApp! (← visit f) (← visit a)
      | .lam _ t b _ => return e.updateLambdaE! (← visit t) (← visit b)
      | .forallE _ t b _ => return e.updateForallE! (← visit t) (← visit b)
      | .letE _ t v b _ => return e.updateLetE! (← visit t) (← visit v) (← visit b)
      | .mdata _ b => return e.updateMData! (← visit b)
      | .proj _ _ b => return e.updateProj! (← visit b)
      | _ => pure e
  modify fun s => { s with cache := s.cache.insert e r }
  return r

/-- The translation of constant `c`, if it has one: an explicit `variant_map` entry, a translated
    auxiliary constant, or the renamed constant when it exists. -/
partial def translateConst (c : Name) : TM (Option Name) := do
  if let some r := (← get).consts.find? c then return r
  let ctx ← read
  let r ← do
    if let some t := ctx.map.find? c then pure (some t)
    else if c != ctx.rootSrc && isAuxOf ctx.rootSrc c then translateAux c
    else
      let c' := renameName ctx.kind c
      if c' != c && (← getEnv).contains c' then pure (some c') else pure none
  modify fun s => { s with consts := s.consts.insert c r }
  return r

/-- Translate auxiliary constant `c` if its type or value changes under the translation. -/
partial def translateAux (c : Name) : TM (Option Name) := do
  let ctx ← read
  let some ci := (← getEnv).find? c | return none
  let type' ← visit ci.type
  let value? := ci.value? (allowOpaque := true)
  let value'? ← value?.mapM visit
  if type' == ci.type && value'? == value? then return none
  let n := (← get).auxCount + 1
  modify fun s => { s with auxCount := n }
  let rootU := privateToUserName ctx.rootSrc
  let cU := privateToUserName c
  let tgt :=
    if rootU.isPrefixOf cU then cU.replacePrefix rootU ctx.rootTgt
    else ctx.rootTgt.str s!"_variant_{n}"
  match ci with
  | .thmInfo _ =>
    addDecl <| .thmDecl
      { name := tgt, levelParams := ci.levelParams, type := type', value := value'?.get! }
  | .defnInfo v =>
    addDecl <| .defnDecl
      { name := tgt, levelParams := ci.levelParams, type := type', value := value'?.get!
        hints := v.hints, safety := v.safety }
    if let some info ← getMatcherInfo? c then Match.addMatcherInfo tgt info
  | _ => return none
  return some tgt

end

/-- Run a translation for kind `kind` from `rootSrc` to `rootTgt`. -/
def TM.run' {α} (kind : VariantKind) (rootSrc rootTgt : Name) (x : TM α) : MetaM α := do
  let ctx : TCtx := {
    kind, rootSrc, rootTgt, map := ← getMap kind.name
    srcBody := lambdaBody kind.source kind.numParams
    tgtBody := lambdaBody kind.target kind.numParams }
  (x.run ctx).run' {}

/-- Constants in `e` whose names match a rename source pattern; used for diagnostic hints when
    translated proof terms fail to type-check. -/
def suspiciousConsts (kind : VariantKind) (e : Expr) : Array Name :=
  e.foldConsts #[] fun c acc =>
    let s := c.toString
    if kind.renames.any (fun (a, _) => (s.splitOn a).length > 1) && !acc.contains c then
      acc.push c
    else acc

/-- Check that two expressions are the same statement; `none` if equal, else a description. -/
def sameStatement (a b : Expr) : MetaM (Option MessageData) := do
  if a == b then return none
  if ← withDefault (isDefEq a b) then return none
  return m!"{indentExpr a}\nis not{indentExpr b}"

/-! ## Commands -/

@[command_elab declareVariantKind]
def elabDeclareVariantKind : CommandElab := fun stx => do
  match stx with
  | `(declare_variant_kind $k $bs* : $src ==> $tgt $[rename $[$as ==> $bs'],*]?) =>
    let kind ← liftTermElabM do
      Term.elabBinders bs fun xs => do
        let s ← elabTerm src none
        let t ← elabTerm tgt none
        synthesizeSyntheticMVarsNoPostponing
        let s ← instantiateMVars s
        let t ← instantiateMVars t
        if s.hasMVar || t.hasMVar then
          throwError "variant kind terms must be fully elaborated"
        unless ← isDefEq (← inferType s) (← inferType t) do
          throwError "source and target of a variant kind must have the same type"
        let sl ← mkLambdaFVars xs s
        let tl ← mkLambdaFVars xs t
        let body := lambdaBody sl xs.size
        for i in [0:xs.size] do
          unless body.hasLooseBVar i do
            throwError "pattern variable `{xs[xs.size - 1 - i]!}` does not occur in the source"
        if body.isBVar then throwError "the source of a variant kind cannot be a variable"
        let renames := match as, bs' with
          | some as, some bs' => (as.zip bs').map fun (a, b) => (a.getString, b.getString)
          | _, _ => #[]
        return { name := k.getId, source := sl, target := tl, numParams := xs.size, renames }
    if (variantExt.getState (← getEnv)).kinds.contains kind.name then
      throwError "variant kind `{kind.name}` is already declared"
    modifyEnv (variantExt.addEntry · (.kind kind))
  | _ => throwUnsupportedSyntax

@[command_elab variantMap]
def elabVariantMap : CommandElab := fun stx => do
  match stx with
  | `(variant_map ($k) $a => $b) =>
    liftTermElabM do
      let kind ← getKind k.getId
      let a ← realizeGlobalConstNoOverloadWithInfo a
      let b ← realizeGlobalConstNoOverloadWithInfo b
      let ai ← getConstInfo a
      let bi ← getConstInfo b
      let ty ← TM.run' kind a b (visit ai.type)
      if let some msg ← sameStatement ty bi.type then
        throwError "variant_map: `{b}` is not the `{kind.name}`-variant of `{a}`:{msg}"
      modifyEnv (variantExt.addEntry · (.map kind.name a b))
  | _ => throwUnsupportedSyntax

/-- Prove the translated statement `type'` as `t (src xs)` (transfer mode). -/
def transferValue (src : Name) (srcType type' : Expr) (levels : List Level) (t : Term) :
    TermElabM Expr := do
  let arity := srcType.getForallBinderNames.length
  forallBoundedTelescope type' (some arity) fun xs concl' => do
    let srcInst := mkAppN (.const src levels) xs
    let mut srcConcl := srcType
    for x in xs do
      let .forallE _ d b _ := srcConcl | unreachable!
      unless ← isDefEq d (← inferType x) do
        throwError "using: the hypotheses of `{src}` change under the variant kind; transfer \
          mode needs a variant that changes only the conclusion (drop `using` to translate the \
          proof)"
      srcConcl := b.instantiate1 x
    withLocalDeclD `hsrc srcConcl fun h => do
      let v ← withoutErrToSorry do
        let v ← elabTermEnsuringType (← `($t $(mkIdent `hsrc))) concl'
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars v
      if v.hasMVar then throwError "using: could not fully elaborate the transfer proof"
      if v.hasSorry then throwError "using: the transfer proof contains `sorry`"
      let v := (← mkLambdaFVars #[h] v).beta #[srcInst]
      mkLambdaFVars xs v

private def deriveVariantAux (kind : VariantKind) (src tgt : Name) (t? : Option Term) :
    TermElabM Unit := do
  let .thmInfo srcInfo ← getConstInfo src
    | throwError "#derive_variant: `{src}` is not a theorem"
  if (← getEnv).contains tgt then throwError "#derive_variant: `{tgt}` already exists"
  let levels := srcInfo.levelParams.map Level.param
  let (type', value') ← TM.run' kind src tgt do
    let type' ← visit srcInfo.type
    match t? with
    | some _ => return (type', none)
    | none => return (type', some (← visit srcInfo.value))
  if type' == srcInfo.type then
    throwError "#derive_variant: the variant kind `{kind.name}` does not change the statement \
      of `{src}`"
  let value' ← match value', t? with
    | some v, _ => pure v
    | none, some t => transferValue src srcInfo.type type' levels t
    | none, none => unreachable!
  let decl := Declaration.thmDecl
    { name := tgt, levelParams := srcInfo.levelParams, type := type', value := value' }
  try addDecl decl
  catch ex =>
    let sus := suspiciousConsts kind value'
    let hint := if sus.isEmpty then m!"" else
      m!"\nconstants without a `{kind.name}` variant (derive them first or add \
        `variant_map`): {sus.toList}"
    throwError "#derive_variant: the translated proof of `{src}` does not type-check:\
      {indentD ex.toMessageData}{hint}"
  modifyEnv (variantExt.addEntry · (.map kind.name src tgt))

/-- Derive the `kind`-variant `tgt` of theorem `src` (in translate mode, or transfer mode when `t?`
    is given) and record `src => tgt`. Runs kernel checking synchronously (`Elab.async` disabled)
    and restores the environment on any error so failed derivations leave no fallback declarations. -/
def deriveVariantCore (kind : VariantKind) (src tgt : Name) (t? : Option Term := none) :
    TermElabM Unit := do
  let env ← getEnv
  tryCatchRuntimeEx
    (withOptions (Elab.async.set · false) (deriveVariantAux kind src tgt t?))
    fun ex => do
      setEnv env
      throw ex

@[command_elab deriveVariant]
def elabDeriveVariant : CommandElab := fun stx => do
  match stx with
  | `($[$doc?]? #derive_variant ($k) $[$tgt?]? from $src $[using $t?]?) =>
    liftTermElabM do
      let kind ← getKind k.getId
      let src ← realizeGlobalConstNoOverloadWithInfo src
      let tgt ← match tgt? with
        | some t => pure ((← getCurrNamespace) ++ t.getId)
        | none =>
          let t := renameName kind src
          if t == src then
            throwError "#derive_variant: the rename rules of `{kind.name}` do not change `{src}`; \
              give the target name explicitly"
          pure t
      deriveVariantCore kind src tgt t?
      addDeclarationRangesFromSyntax tgt stx
      match doc? with
      | some doc => addDocString tgt .missing doc
      | none => addDocStringCore tgt s!"`{kind.name}`-variant of `{src}` (`#derive_variant`)."
  | _ => throwUnsupportedSyntax

@[command_elab guardSameType]
def elabGuardSameType : CommandElab := fun stx => do
  match stx with
  | `(#guard_same_type $a $b) =>
    liftTermElabM do
      let a ← realizeGlobalConstNoOverloadWithInfo a
      let b ← realizeGlobalConstNoOverloadWithInfo b
      let ai ← getConstInfo a
      let bi ← getConstInfo b
      if ai.levelParams.length != bi.levelParams.length then
        throwError "#guard_same_type: `{a}` and `{b}` have different universe parameters"
      let bt := bi.type.instantiateLevelParams bi.levelParams (ai.levelParams.map Level.param)
      if let some msg ← sameStatement ai.type bt then
        throwError "#guard_same_type: `{a}` and `{b}` have different statements:{msg}"
  | _ => throwUnsupportedSyntax

end ProofLib.Variant

end
