/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Hoare.SubroutineOk
public meta import Lean

/-!
# Non-Vacuity Witnesses and Coverage Lint

Derives the joint-satisfiability proposition of a theorem's premises (`hyps_of%`), emits
kernel-checked adequacy theorems (`#nonvacuous`, `#nonvacuous?`, `#nonvacuous_adequate`) that feed
destructured witnesses directly into the target theorem, provides the binder-named `witness` tactic,
and checks non-vacuity coverage over `@[contract]` declarations (`#check_nonvacuity_coverage`).
-/

namespace ProofLib.NonVacuity

open Lean Meta Elab Term Tactic Command

public meta section

/-- Metadata key recording the original binder name of a non-dependent `Prop` hypothesis on `And`
    conjuncts so `witness h := proof` can match named hypothesis binders as well as `∃` binders. -/
def nonvacBinderKey : Name := `nonvacBinder

private def attachBinderName (nm : Name) (ty : Expr) : Expr :=
  let clean := nm.eraseMacroScopes
  if clean.isAnonymous then ty
  else Expr.mdata (KVMap.empty.insert nonvacBinderKey (.ofName clean)) ty

private def extractBinderName? (ty : Expr) : Option Name :=
  match ty with
  | .mdata md _ =>
    let nm := md.getName nonvacBinderKey .anonymous
    if nm.isAnonymous then none else some nm
  | _ => none

/-! ## Syntax -/

/-- Explicit list of definitions/projections to unfold while deriving premises. -/
syntax nonvacUnfold := atomic("(" &"unfold" " := " "[") ident,* "]" ")"

/-- Named binder instantiation `(x := term)` for `hyps_of%` and `#nonvacuous`. -/
syntax nonvacBind := atomic("(" ident " := ") term ")"

/-- Modifier argument accepted by `hyps_of%`, `#nonvacuous`, `#nonvacuous?`, and `#nonvacuous_adequate`. -/
syntax nonvacArg := nonvacUnfold <|> nonvacBind

/-- Derive the joint-satisfiability proposition of a constant's premises. -/
syntax (name := hypsOfStx) "hyps_of% " ident nonvacArg* : term

/-- Internal term elaborator computing the expected type of `<foo>.nonvacuous_adequate`. -/
syntax (name := nonvacConclOfStx) "nonvac_concl_of% " ident nonvacArg* : term

/-- Prove that a theorem's premises are jointly satisfiable and kernel-check adequacy. -/
syntax (name := nonvacuousCmd)
  (docComment)? "#nonvacuous " ident nonvacArg* " := " term : command

/-- Display the derived non-vacuity goal for a theorem without adding declarations. -/
syntax (name := nonvacuousQueryCmd) "#nonvacuous? " ident nonvacArg* : command

/-- Check adequacy of an explicit witness theorem against a target theorem's real premises. -/
syntax (name := nonvacuousAdequateCmd)
  "#nonvacuous_adequate " ident ident nonvacArg* : command

/-- Single item in `witness`: either `ident := term` (binder-named) or `term` (closed hook proof). -/
syntax witnessNamedItem := atomic(ident " := ") term
syntax witnessItem := witnessNamedItem <|> term

/-- Fill existentials by binder name and discharge hook premises with closed callee theorems. -/
syntax (name := witnessTac) "witness " witnessItem,+ : tactic

/-- Exempt a `@[contract]` declaration from `#check_nonvacuity_coverage` with an explicit reason. -/
syntax (name := vacuityExemptAttr) "vacuity_exempt" str : attr

/-- Verify that every `@[contract]` declaration (optionally under module/name prefix `ident`) has
    either a `<decl>.nonvacuous` sibling theorem or `@[vacuity_exempt "reason"]`. -/
syntax (name := checkNonVacuityCoverageCmd) "#check_nonvacuity_coverage" (ppSpace ident)? : command

/-! ## Persistent Environment Extensions -/

/-- Opt-in tag marking a contract theorem or specification whose premises must have a machine-checked
    `.nonvacuous` sibling theorem or an explicit `@[vacuity_exempt "reason"]` annotation. -/
initialize contractAttr : TagAttribute ←
  registerTagAttribute `contract
    "mark a theorem/contract as requiring a `.nonvacuous` witness or `@[vacuity_exempt \"reason\"]`"

/-- Persistent map from exempted declaration name to its human-readable justification string. -/
initialize vacuityExemptExt : SimplePersistentEnvExtension (Name × String) (NameMap String) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun acc arr =>
        arr.foldl (fun m (nm, rsn) => m.insert nm rsn) acc
    addEntryFn := fun m (nm, rsn) => m.insert nm rsn
    toArrayFn := Array.mk
  }

initialize registerBuiltinAttribute {
  name := `vacuityExemptAttr
  descr := "exempt a `@[contract]` declaration from `#check_nonvacuity_coverage` with a reason"
  applicationTime := .afterCompilation
  add := fun declName stx attrKind => do
    unless attrKind == .global do
      throwError "`@[vacuity_exempt]` must have global scope"
    match stx with
    | `(attr| vacuity_exempt $s:str) =>
      let reason := s.getString
      if reason.trimAscii.toString.isEmpty then
        throwError "`@[vacuity_exempt]` requires a non-empty reason string"
      modifyEnv fun env => vacuityExemptExt.addEntry env (declName, reason)
    | _ => throwUnsupportedSyntax
}

/-- Private persistent map from a target declaration `foo` to the kernel-checked adequacy
    theorems (`foo.nonvacuous_adequate`, `foo.nonvacuous_2_adequate`, ...) emitted by `#nonvacuous`
    or `#nonvacuous_adequate`. Kept `private` so hand-written `theorem foo.nonvacuous : True`
    declarations cannot forge coverage in `#check_nonvacuity_coverage`. -/
private initialize nonvacuousAdequateExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun acc arr =>
        arr.foldl (fun m (decl, adeq) =>
          let cur := (m.find? decl).getD #[]
          m.insert decl (cur.push adeq)) acc
    addEntryFn := fun m (decl, adeq) =>
      let cur := (m.find? decl).getD #[]
      m.insert decl (cur.push adeq)
    toArrayFn := Array.mk
  }

private def hasVerifiedNonvacuousWitness (env : Environment) (declName : Name) : Bool :=
  match (nonvacuousAdequateExt.getState env).find? declName with
  | none => false
  | some adeqNames =>
    adeqNames.any fun adeqName =>
      match env.find? adeqName with
      | some (.thmInfo tval)  => tval.value.getUsedConstants.contains declName
      | some (.defnInfo dval) => dval.value.getUsedConstants.contains declName
      | _ => false

/-! ## Controlled Unfolding and Telescope Analysis -/

private structure ParsedNonvacArgs where
  unfoldIdents : Array (TSyntax `ident) := #[]
  fixedArgs    : Array (Name × Syntax × Term) := #[]

private def parseNonvacArgs (args : Array (TSyntax `ProofLib.NonVacuity.nonvacArg)) :
    CoreM ParsedNonvacArgs := do
  let mut out : ParsedNonvacArgs := {}
  let mut seen : NameSet := {}
  for arg in args do
    match arg with
    | `(nonvacArg| (unfold := [$ids,*])) =>
      out := { out with unfoldIdents := out.unfoldIdents ++ ids.getElems }
    | `(nonvacArg| ($nm:ident := $val:term)) =>
      let key := nm.getId.eraseMacroScopes
      if seen.contains key then
        throwErrorAt nm "duplicate binder instantiation `({key} := ...)`"
      seen := seen.insert key
      out := { out with fixedArgs := out.fixedArgs.push (key, nm, val) }
    | _ => throwErrorAt arg "unexpected argument syntax in non-vacuity specification"
  return out

private def hoareWrapperCompanionNames : Array Name := #[
  ``Arm64.Program.subroutineOk,
  ``Arm64.Program.rawSubroutineOk,
  ``Arm64.Program.safeSubroutineOk,
  ``Arm64.fn_subroutine_ok,
  ``Arm64.Program.relocSubroutineOk,
  ``Arm64.Program.alignedSubroutineOk,
  `Arm64.Obj.LinkedImage.subroutineOk,
  ``Arm64.FnPtrSpec,
  ``Arm64.SafeFnPtrSpec,
  ``Arm64.ToBaseSpec.toSpec,
  ``Arm64.instToBaseSpecId,
  ``Arm64.instToBaseSpecFn
]

private def hoareJudgmentRootNames : Array Name := #[
  ``Arm64.subroutine_ok,
  ``Arm64.raw_subroutine_ok,
  ``Arm64.safe_subroutine_ok,
  ``Arm64.Program.subroutineOk,
  ``Arm64.Program.rawSubroutineOk,
  ``Arm64.Program.safeSubroutineOk,
  ``Arm64.fn_subroutine_ok,
  ``Arm64.Program.relocSubroutineOk,
  ``Arm64.Program.alignedSubroutineOk,
  `Arm64.Obj.LinkedImage.subroutineOk
]

private def resolveUnfoldSet (ids : Array (TSyntax `ident)) : CoreM NameSet := do
  let mut s : NameSet := {}
  for id in ids do
    let cs ← realizeGlobalConstWithInfos id
    for c in cs do
      s := s.insert c
  if hoareJudgmentRootNames.any s.contains then
    for w in hoareWrapperCompanionNames do
      s := s.insert w
  return s

private def projFnName? (env : Environment) (structName : Name) (idx : Nat) : Option Name := do
  let fields := getStructureFieldsFlattened env structName (includeSubobjectFields := true)
  let fieldName ← fields[idx]?
  return structName ++ fieldName

private def unfoldOneStep? (unfoldSet : NameSet) (e : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  match e with
  | .proj structName idx target =>
    let matchesProj := (projFnName? env structName idx).any unfoldSet.contains
    let matchesTarget := target.getAppFn.constName?.any unfoldSet.contains
    if matchesProj || matchesTarget then
      let target' ← whnf target
      if let some reduced ← reduceProj? (.proj structName idx target') then
        return some reduced.headBeta
    return none
  | _ =>
    let fn := e.getAppFn
    let .const c _ := fn | return none
    -- Opaque Hoare judgments are eliminated via `.to_outcome` in `peelTelescope`.
    if c == ``Arm64.subroutine_ok || c == ``Arm64.raw_subroutine_ok then
      return none
    if let some projInfo ← getProjectionFnInfo? c then
      let args := e.getAppArgs
      if projInfo.numParams < args.size then
        let structArg := args[projInfo.numParams]!
        let matchesProj := unfoldSet.contains c
        let matchesTarget := structArg.getAppFn.constName?.any unfoldSet.contains
        if matchesProj || matchesTarget then
          let structArg' ← whnf structArg
          let rebuilt := mkAppN fn (args.set! projInfo.numParams structArg')
          if let some unfolded ← unfoldDefinition? rebuilt then
            let reduced ← Core.betaReduce unfolded
            if let .proj sName idx inner := reduced.getAppFn then
              if let some pVal ← reduceProj? (.proj sName idx inner) then
                return some (mkAppN pVal reduced.getAppArgs).headBeta
            if reduced != e then
              return some reduced
    if unfoldSet.contains c then
      if let some unfolded ← unfoldDefinition? e then
        return some unfolded.headBeta
    return none

private partial def unfoldExpr (unfoldSet : NameSet) (e : Expr) (fuel : Nat := 16) : MetaM Expr := do
  if unfoldSet.isEmpty || fuel == 0 then
    return e
  let changedRef ← IO.mkRef false
  let e' ← Meta.transform e (pre := fun sub => do
    match ← unfoldOneStep? unfoldSet sub with
    | some next =>
      changedRef.set true
      return .done next
    | none => return .continue)
  if (← changedRef.get) then
    unfoldExpr unfoldSet e' (fuel - 1)
  else
    return e'

private inductive TelescopeStep where
  | fixedBinder (name : Name) (bi : BinderInfo) (valStx : Term) (valExpr : Expr)
  | freeBinder  (name : Name) (bi : BinderInfo) (fvar : Expr) (ty : Expr) (isPropTy : Bool)
  | toOutcome   (elimConst : Name)

private structure FreeBinderInfo where
  name     : Name
  bi       : BinderInfo
  fvar     : Expr
  ty       : Expr
  isPropTy : Bool
  deriving Inhabited

private structure TelescopeResult where
  steps          : Array TelescopeStep
  freeBinders    : Array FreeBinderInfo
  hypsType       : Expr
  adequateType   : Expr
  keptFreeIndices : Array Nat

private def buildHypsExpr (freeBinders : Array FreeBinderInfo) : MetaM Expr := do
  if h0 : freeBinders.size = 0 then
    return mkConst ``True
  else
    let lastIdx := freeBinders.size - 1
    let last := freeBinders[lastIdx]
    let mut acc : Expr ←
      if last.isPropTy then
        pure (attachBinderName last.name last.ty)
      else
        mkAppM ``Exists #[← mkLambdaFVars #[last.fvar] (mkConst ``True)]
    let mut i := lastIdx
    while i > 0 do
      i := i - 1
      let b := freeBinders[i]!
      if b.isPropTy then
        if acc.containsFVar b.fvar.fvarId! then
          acc ← mkAppM ``Exists #[← mkLambdaFVars #[b.fvar] acc]
        else
          acc ← mkAppM ``And #[attachBinderName b.name b.ty, acc]
      else
        acc ← mkAppM ``Exists #[← mkLambdaFVars #[b.fvar] acc]
    return acc

private def buildAdequateExpr (freeBinders : Array FreeBinderInfo) (concl : Expr) :
    MetaM (Expr × Array Nat) := do
  let mut acc := concl
  let mut keptRev : Array Nat := #[]
  let mut i := freeBinders.size
  while i > 0 do
    i := i - 1
    let b := freeBinders[i]!
    if !b.isPropTy || acc.containsFVar b.fvar.fvarId! then
      acc ← mkAppM ``Exists #[← mkLambdaFVars #[b.fvar] acc]
      keptRev := keptRev.push i
  return (acc, keptRev.reverse)

private partial def peelTelescope
    (declName : Name)
    (unfoldSet : NameSet)
    (fixedArgs : Array (Name × Syntax × Term))
    (usedFixed : NameSet)
    (steps : Array TelescopeStep)
    (freeBinders : Array FreeBinderInfo)
    (ty : Expr)
    (fuel : Nat := 256) : TermElabM (TelescopeResult × NameSet) := do
  let ty := ty.consumeMData.headBeta
  if fuel == 0 then
    let hyps ← buildHypsExpr freeBinders
    let (adeq, kept) ← buildAdequateExpr freeBinders ty
    return ({ steps, freeBinders, hypsType := hyps, adequateType := adeq, keptFreeIndices := kept }, usedFixed)
  match ty with
  | .letE _ _ val body _ =>
    peelTelescope declName unfoldSet fixedArgs usedFixed steps freeBinders
      (body.instantiate1 val) (fuel - 1)
  | .forallE bname dom body bi =>
    let dom' ← unfoldExpr unfoldSet dom
    let cleanName := bname.eraseMacroScopes
    if let some (_, _, valStx) := fixedArgs.find? (fun (k, _, _) => k == cleanName && !usedFixed.contains k) then
      let valExpr ← Term.elabTermEnsuringType valStx (some dom')
      let step := TelescopeStep.fixedBinder cleanName bi valStx valExpr
      peelTelescope declName unfoldSet fixedArgs (usedFixed.insert cleanName)
        (steps.push step) freeBinders (body.instantiate1 valExpr) (fuel - 1)
    else
      withLocalDecl bname bi dom' fun fvar => do
        let isPropDom ← isProp dom'
        let info : FreeBinderInfo := {
          name := cleanName, bi, fvar, ty := dom', isPropTy := isPropDom
        }
        let step := TelescopeStep.freeBinder cleanName bi fvar dom' isPropDom
        peelTelescope declName unfoldSet fixedArgs usedFixed
          (steps.push step) (freeBinders.push info) (body.instantiate1 fvar) (fuel - 1)
  | _ =>
    if !unfoldSet.isEmpty then
      if let some ty' ← unfoldOneStep? unfoldSet ty then
        return ← peelTelescope declName unfoldSet fixedArgs usedFixed
          steps freeBinders ty' (fuel - 1)
      if ty.isAppOfArity ``Arm64.subroutine_ok 4 && unfoldSet.contains ``Arm64.subroutine_ok then
        let nextTy ← withLocalDeclD `_h ty fun hFVar => do
          inferType (← mkAppM ``Arm64.subroutine_ok.to_outcome #[hFVar])
        return ← peelTelescope declName unfoldSet fixedArgs usedFixed
          (steps.push (.toOutcome ``Arm64.subroutine_ok.to_outcome))
          freeBinders nextTy (fuel - 1)
      if ty.isAppOfArity ``Arm64.raw_subroutine_ok 4 && unfoldSet.contains ``Arm64.raw_subroutine_ok then
        let nextTy ← withLocalDeclD `_h ty fun hFVar => do
          inferType (← mkAppM ``Arm64.raw_subroutine_ok.to_outcome #[hFVar])
        return ← peelTelescope declName unfoldSet fixedArgs usedFixed
          (steps.push (.toOutcome ``Arm64.raw_subroutine_ok.to_outcome))
          freeBinders nextTy (fuel - 1)
    let hyps ← buildHypsExpr freeBinders
    let (adeq, kept) ← buildAdequateExpr freeBinders ty
    return ({ steps, freeBinders, hypsType := hyps, adequateType := adeq, keptFreeIndices := kept }, usedFixed)

private def analyzeTarget
    (id : TSyntax `ident)
    (args : Array (TSyntax `ProofLib.NonVacuity.nonvacArg)) :
    TermElabM (Name × TelescopeResult) := do
  let declName ← realizeGlobalConstNoOverloadWithInfo id
  let parsed ← parseNonvacArgs args
  let unfoldSet ← resolveUnfoldSet parsed.unfoldIdents
  let cInfo ← getConstInfo declName
  let us ← mkFreshLevelMVarsFor cInfo
  let initTy := cInfo.instantiateTypeLevelParams us
  let (res, usedFixed) ← peelTelescope declName unfoldSet parsed.fixedArgs {} #[] #[] initTy
  for (key, stxNode, _) in parsed.fixedArgs do
    unless usedFixed.contains key do
      let avail := res.freeBinders.toList.filterMap fun b =>
        if b.name.isAnonymous then none else some b.name
      throwErrorAt stxNode
        "unknown binder `{key}` in `{declName}` (available uninstantiated binders: {avail})"
  return (declName, res)

@[term_elab hypsOfStx]
def elabHypsOf : TermElab := fun stx _expectedType? => do
  match stx with
  | `(hyps_of% $id:ident $args:nonvacArg*) =>
    let (_, res) ← analyzeTarget id args
    return res.hypsType
  | _ => throwUnsupportedSyntax

@[term_elab nonvacConclOfStx]
def elabNonvacConclOf : TermElab := fun stx _expectedType? => do
  match stx with
  | `(nonvac_concl_of% $id:ident $args:nonvacArg*) =>
    let (_, res) ← analyzeTarget id args
    return res.adequateType
  | _ => throwUnsupportedSyntax

/-! ## Adequacy Proof Generation -/

private def mkFreshSiblingNames (env : Environment) (declName : Name) : Name × Name := Id.run do
  let base := declName ++ `nonvacuous
  if !env.contains base then
    return (base, declName ++ `nonvacuous_adequate)
  let mut idx := 2
  while env.contains (declName ++ Name.mkSimple s!"nonvacuous_{idx}") do
    idx := idx + 1
  return (declName ++ Name.mkSimple s!"nonvacuous_{idx}",
          declName ++ Name.mkSimple s!"nonvacuous_{idx}_adequate")

private def mkDeclTargetIdent (declName : Name) : Bool × Ident :=
  if isPrivateName declName then
    (true, mkIdent (`_root_ ++ privateToUserName declName))
  else
    (false, mkIdent (`_root_ ++ declName))

private def buildWitnessRefTerm
    (ref : Syntax)
    (witnessDeclName : Name)
    (secNamedVars : Array (Name × Expr))
    (hypsType : Expr) : CommandElabM Term := do
  let wInfo ← getConstInfo witnessDeclName
  let mut curr := wInfo.type
  let mut secIdx := 0
  let mut secArgs : Array Ident := #[]
  while curr != hypsType && curr.isForall && secIdx < secNamedVars.size do
    let .forallE bname _ body _ := curr | break
    let targetName := bname.eraseMacroScopes
    let mut found? : Option (Nat × Expr) := none
    for j in [secIdx:secNamedVars.size] do
      let (vName, v) := secNamedVars[j]!
      if vName == targetName then
        found? := some (j, v)
        break
    match found? with
    | some (j, v) =>
      secArgs := secArgs.push (mkIdentFrom ref targetName)
      curr := body.instantiate1 v
      secIdx := j + 1
    | none => break
  let baseRef : Term := mkCIdentFrom ref witnessDeclName
  if secArgs.isEmpty then
    return baseRef
  else
    let mut app : Term ← `(@$baseRef)
    for sarg in secArgs do
      app ← `($app $sarg)
    return app

private def mkAdequacyCommandStx
    (ref : Syntax)
    (targetId : TSyntax `ident)
    (targetDeclName : Name)
    (witnessDeclName : Name)
    (adequateDeclName : Name)
    (args : Array (TSyntax `ProofLib.NonVacuity.nonvacArg))
    (secNamedVars : Array (Name × Expr))
    (res : TelescopeResult) : CommandElabM Syntax := do
  let mut wIdents : Array Ident := #[]
  for i in [:res.freeBinders.size] do
    wIdents := wIdents.push (mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple s!"w_{i}")))

  let witnessRef ← buildWitnessRefTerm ref witnessDeclName secNamedVars res.hypsType
  let unpackTac? : Option (TSyntax `tactic) ← do
    if h0 : res.freeBinders.size = 0 then
      pure none
    else if h1 : res.freeBinders.size = 1 then
      let b0 := res.freeBinders[0]
      let w0 := wIdents[0]!
      if b0.isPropTy then
        pure (some (← `(tactic| have $w0:ident := $witnessRef)))
      else
        let pat ← `(rcasesPat| ⟨$w0, _⟩)
        pure (some (← `(tactic| obtain $pat := $witnessRef)))
    else
      let last := res.freeBinders[res.freeBinders.size - 1]!
      let mut pats : Array (TSyntax `rcasesPat) := #[]
      for w in wIdents do
        pats := pats.push (← `(rcasesPat| $w:ident))
      if !last.isPropTy then
        pats := pats.push (← `(rcasesPat| _))
      let tuplePat ← `(rcasesPat| ⟨$pats,*⟩)
      pure (some (← `(tactic| obtain $tuplePat := $witnessRef)))

  let targetRef : Term := mkCIdentFrom ref targetDeclName
  let mut appTerm : Term ← `(@$targetRef)
  let mut freeIdx := 0
  for step in res.steps do
    match step with
    | .fixedBinder _ _ valStx _ =>
      appTerm ← `($appTerm ($valStx))
    | .freeBinder _ _ _ _ _ =>
      let w := wIdents[freeIdx]!
      freeIdx := freeIdx + 1
      appTerm ← `($appTerm $w)
    | .toOutcome elimConst =>
      let elimRef : Term := mkCIdentFrom ref elimConst
      appTerm ← `($elimRef ($appTerm))

  let existsIntroRef : Term := mkCIdentFrom ref ``Exists.intro
  let mut proofTerm : Term := appTerm
  let mut k := res.keptFreeIndices.size
  while k > 0 do
    k := k - 1
    let w := wIdents[res.keptFreeIndices[k]!]!
    proofTerm ← `(@$existsIntroRef _ _ $w ($proofTerm))

  let exactTac ← `(tactic| exact $proofTerm)
  let tacSeq : Array (TSyntax `tactic) :=
    match unpackTac? with
    | some u => #[u, exactTac]
    | none   => #[exactTac]

  let (isPriv, adeqIdent) := mkDeclTargetIdent adequateDeclName
  if isPriv then
    `(command|
      private theorem $adeqIdent : nonvac_concl_of% $targetId $args* := by
        $[$tacSeq]*)
  else
    `(command|
      theorem $adeqIdent : nonvac_concl_of% $targetId $args* := by
        $[$tacSeq]*)

@[command_elab nonvacuousCmd]
def elabNonvacuousCmd : CommandElab := fun stx => do
  match stx with
  | `($[$doc?:docComment]? #nonvacuous $id:ident $args:nonvacArg* := $proof:term) =>
    let (secNamedVars, declName, res) ← runTermElabM fun secVars => do
      let named ← secVars.mapM fun v => do
        return ((← v.fvarId!.getUserName).eraseMacroScopes, v)
      let (d, r) ← analyzeTarget id args
      return (named, d, r)
    let env ← getEnv
    let (witnessDeclName, adequateDeclName) := mkFreshSiblingNames env declName
    let (isPriv, witnessIdent) := mkDeclTargetIdent witnessDeclName
    let witnessCmd ←
      if isPriv then
        `(command| $[$doc?:docComment]? private theorem $witnessIdent : hyps_of% $id $args* := $proof)
      else
        `(command| $[$doc?:docComment]? theorem $witnessIdent : hyps_of% $id $args* := $proof)
    withMacroExpansion stx witnessCmd <| elabCommand witnessCmd
    let adeqCmd ← mkAdequacyCommandStx stx id declName witnessDeclName adequateDeclName args secNamedVars res
    withMacroExpansion stx adeqCmd <| elabCommand adeqCmd
    if (← getEnv).contains adequateDeclName then
      modifyEnv fun env => nonvacuousAdequateExt.addEntry env (declName, adequateDeclName)
  | _ => throwUnsupportedSyntax

@[command_elab nonvacuousQueryCmd]
def elabNonvacuousQueryCmd : CommandElab := fun stx => do
  match stx with
  | `(#nonvacuous? $id:ident $args:nonvacArg*) =>
    let (declName, res) ← runTermElabM fun _ => analyzeTarget id args
    let msg ← liftTermElabM <|
      addMessageContextFull m!"-- {privateToUserName declName}.nonvacuous :\n{res.hypsType}"
    logInfoAt stx msg
  | _ => throwUnsupportedSyntax

@[command_elab nonvacuousAdequateCmd]
def elabNonvacuousAdequateCmd : CommandElab := fun stx => do
  match stx with
  | `(#nonvacuous_adequate $targetId:ident $witnessId:ident $args:nonvacArg*) =>
    let (secNamedVars, declName, res) ← runTermElabM fun secVars => do
      let named ← secVars.mapM fun v => do
        return ((← v.fvarId!.getUserName).eraseMacroScopes, v)
      let (d, r) ← analyzeTarget targetId args
      return (named, d, r)
    let witnessDeclName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo witnessId
    let adeqDeclName := witnessDeclName ++ `adequate
    let adeqCmd ← mkAdequacyCommandStx stx targetId declName witnessDeclName adeqDeclName args secNamedVars res
    withMacroExpansion stx adeqCmd <| elabCommand adeqCmd
    if (← getEnv).contains adeqDeclName then
      modifyEnv fun env => nonvacuousAdequateExt.addEntry env (declName, adeqDeclName)
  | _ => throwUnsupportedSyntax

/-! ## The `witness` Tactic -/

private structure UnassignedExistential where
  name   : Name
  mvarId : MVarId
  isInst : Bool
  isProp : Bool

private partial def walkWitnessSpine
    (goalId : MVarId)
    (namedArgs : Array (Name × Syntax × Term))
    (usedNamed : NameSet)
    (availNames : Array Name)
    (unassignedEx : Array UnassignedExistential)
    (openPropGoals : Array MVarId)
    (extraHoleGoals : Array MVarId)
    (fuel : Nat := 256) :
    TacticM (NameSet × Array Name × Array UnassignedExistential × Array MVarId × Array MVarId) := do
  if fuel == 0 then
    return (usedNamed, availNames, unassignedEx, openPropGoals.push goalId, extraHoleGoals)
  goalId.withContext do
    let rawTarget ← instantiateMVars (← goalId.getType)
    let binderHint? := extractBinderName? rawTarget
    let target := rawTarget.consumeMData.headBeta
    if target.isAppOfArity ``Exists 2 then
      let α := target.getArg! 0
      let p := target.getArg! 1
      let (bname, bi) := match p with
        | .lam nm _ _ binfo => (nm.eraseMacroScopes, binfo)
        | _ => (.anonymous, BinderInfo.default)
      let availNames := if bname.isAnonymous then availNames else availNames.push bname
      if let some (_, _, valStx) := namedArgs.find? (fun (k, _, _) => k == bname && !usedNamed.contains k) then
        setGoals [goalId]
        let (valExpr, holes) ← elabTermWithHoles valStx (some α) bname (allowNaturalHoles := true)
        let restTy := (mkApp p valExpr).headBeta
        let restMVar ← mkFreshExprSyntheticOpaqueMVar restTy
        let proof ← mkAppOptM ``Exists.intro #[some α, some p, some valExpr, some restMVar]
        goalId.assign proof
        walkWitnessSpine restMVar.mvarId! namedArgs (usedNamed.insert bname) availNames
          unassignedEx openPropGoals (extraHoleGoals ++ holes.toArray) (fuel - 1)
      else
        let xMVar ← mkFreshExprSyntheticOpaqueMVar α bname
        let isPropDom ← isProp α
        let exInfo : UnassignedExistential := {
          name := bname, mvarId := xMVar.mvarId!, isInst := (bi == .instImplicit), isProp := isPropDom
        }
        let restTy := (mkApp p xMVar).headBeta
        let restMVar ← mkFreshExprSyntheticOpaqueMVar restTy
        let proof ← mkAppOptM ``Exists.intro #[some α, some p, some xMVar, some restMVar]
        goalId.assign proof
        walkWitnessSpine restMVar.mvarId! namedArgs usedNamed availNames
          (unassignedEx.push exInfo) openPropGoals extraHoleGoals (fuel - 1)
    else if target.isLet then
      let (_, restGoalId) ← goalId.intro1P
      walkWitnessSpine restGoalId namedArgs usedNamed availNames
        unassignedEx openPropGoals extraHoleGoals (fuel - 1)
    else if target.isAppOfArity ``And 2 then
      let rawLeft := target.getArg! 0
      let rawRight := target.getArg! 1
      let leftHint? := extractBinderName? rawLeft
      let leftTy := rawLeft.consumeMData
      let availNames := match leftHint? with
        | some nm => availNames.push nm
        | none => availNames
      let leftMVar ← mkFreshExprSyntheticOpaqueMVar leftTy (leftHint?.getD .anonymous)
      let rightMVar ← mkFreshExprSyntheticOpaqueMVar rawRight
      goalId.assign (mkApp4 (mkConst ``And.intro) leftTy rawRight leftMVar rightMVar)
      match leftHint? with
      | some nm =>
        if let some (_, _, valStx) := namedArgs.find? (fun (k, _, _) => k == nm && !usedNamed.contains k) then
          setGoals [leftMVar.mvarId!]
          let (valExpr, holes) ← elabTermWithHoles valStx (some leftTy) nm (allowNaturalHoles := true)
          leftMVar.mvarId!.assign valExpr
          return ← walkWitnessSpine rightMVar.mvarId! namedArgs (usedNamed.insert nm) availNames
            unassignedEx openPropGoals (extraHoleGoals ++ holes.toArray) (fuel - 1)
      | none => pure ()
      walkWitnessSpine rightMVar.mvarId! namedArgs usedNamed availNames
        unassignedEx (openPropGoals.push leftMVar.mvarId!) extraHoleGoals (fuel - 1)
    else if target.isConstOf ``True then
      goalId.assign (mkConst ``True.intro)
      return (usedNamed, availNames, unassignedEx, openPropGoals, extraHoleGoals)
    else
      let availNames := match binderHint? with
        | some nm => availNames.push nm
        | none => availNames
      match binderHint? with
      | some nm =>
        if let some (_, _, valStx) := namedArgs.find? (fun (k, _, _) => k == nm && !usedNamed.contains k) then
          setGoals [goalId]
          let (valExpr, holes) ← elabTermWithHoles valStx (some target) nm (allowNaturalHoles := true)
          goalId.assign valExpr
          return (usedNamed.insert nm, availNames, unassignedEx, openPropGoals, extraHoleGoals ++ holes.toArray)
      | none => pure ()
      return (usedNamed, availNames, unassignedEx, openPropGoals.push goalId, extraHoleGoals)

@[tactic witnessTac]
def evalWitnessTac : Tactic := fun stx => do
  match stx with
  | `(tactic| witness $items:witnessItem,*) =>
    let mut namedArgs : Array (Name × Syntax × Term) := #[]
    let mut unnamedTerms : Array Term := #[]
    let mut seenNames : NameSet := {}
    for item in items.getElems do
      match item with
      | `(witnessItem| $nm:ident := $val:term) =>
        let key := nm.getId.eraseMacroScopes
        if seenNames.contains key then
          throwErrorAt nm "witness: duplicate binder `{key}`"
        seenNames := seenNames.insert key
        namedArgs := namedArgs.push (key, nm, val)
      | `(witnessItem| $val:term) =>
        unnamedTerms := unnamedTerms.push val
      | _ => throwUnsupportedSyntax

    let mainGoal :: otherGoals ← getUnsolvedGoals
      | throwNoGoalsToBeSolved
    let (usedNamed, availNames, unassignedEx, openPropGoals, mutHoles) ←
      walkWitnessSpine mainGoal namedArgs {} #[] #[] #[] #[]

    for (key, nmStx, _) in namedArgs do
      unless usedNamed.contains key do
        throwErrorAt nmStx
          "witness: unknown or already-instantiated binder `{key}` (available binders: {availNames.toList})"

    for ex in unassignedEx do
      if !(← ex.mvarId.isAssigned) && ex.isInst then
        ex.mvarId.withContext do
          let instTy ← instantiateMVars (← ex.mvarId.getType)
          if let some instVal ← synthInstance? instTy then
            ex.mvarId.assign instVal

    let mut extraHoles := mutHoles
    let candidatePropMVars : Array MVarId :=
      (unassignedEx.filter (·.isProp) |>.map (·.mvarId)) ++ openPropGoals
    for proofStx in unnamedTerms do
      let mut matched := false
      for candId in candidatePropMVars do
        if !matched && !(← candId.isAssigned) then
          let saved ← saveState
          try
            setGoals [candId]
            let holes ← candId.withContext do
              let expected ← instantiateMVars (← candId.getType)
              let (val, hs) ← withoutErrToSorry <|
                elabTermWithHoles proofStx (some expected) `witness (allowNaturalHoles := true)
              candId.assign val
              pure hs
            extraHoles := extraHoles ++ holes.toArray
            matched := true
          catch _ =>
            restoreState saved
      unless matched do
        throwErrorAt proofStx
          "witness: term `{proofStx}` did not match any remaining hypothesis goal"

    let mut newGoals : List MVarId := []
    let mut seenMVar : Std.HashSet MVarId := {}
    let pushIfOpen (acc : List MVarId) (seen : Std.HashSet MVarId) (m : MVarId) :
        TacticM (List MVarId × Std.HashSet MVarId) := do
      if seen.contains m || (← m.isAssigned) then
        return (acc, seen)
      else
        return (acc ++ [m], seen.insert m)

    for m in extraHoles do
      (newGoals, seenMVar) ← pushIfOpen newGoals seenMVar m
    for ex in unassignedEx do
      (newGoals, seenMVar) ← pushIfOpen newGoals seenMVar ex.mvarId
    for g in openPropGoals do
      (newGoals, seenMVar) ← pushIfOpen newGoals seenMVar g

    setGoals (newGoals ++ otherGoals)
  | _ => throwUnsupportedSyntax

/-! ## Environment Coverage Check -/

private def matchesOptionalPrefix (env : Environment) (declName : Name) (pfx? : Option Name) : Bool :=
  let userDecl := privateToUserName declName
  match pfx? with
  | none => true
  | some pfx =>
    pfx.isPrefixOf userDecl ||
      match env.getModuleIdxFor? declName with
      | some modIdx =>
        match env.header.moduleNames[modIdx.toNat]? with
        | some modName => pfx.isPrefixOf modName
        | none => false
      | none => pfx.isPrefixOf env.mainModule

@[command_elab checkNonVacuityCoverageCmd]
def elabCheckNonVacuityCoverage : CommandElab := fun stx => do
  match stx with
  | `(#check_nonvacuity_coverage $[$pfxIdent?:ident]?) =>
    let env ← getEnv
    let pfx? := pfxIdent?.map (·.getId.eraseMacroScopes)
    let exemptMap := vacuityExemptExt.getState env
    let mut tagged : Array Name := #[]
    for modIdx in [:env.header.moduleNames.size] do
      for declName in contractAttr.ext.getModuleEntries env modIdx do
        tagged := tagged.push declName
    for declName in contractAttr.ext.getState env do
      tagged := tagged.push declName

    let mut missing : Array (Name × String) := #[]
    for declName in tagged do
      if matchesOptionalPrefix env declName pfx? then
        let hasVerified := hasVerifiedNonvacuousWitness env declName
        let isExempt := exemptMap.contains declName
        if !hasVerified && !isExempt then
          let baseLoc := match env.getModuleIdxFor? declName with
            | some idx =>
              match env.header.moduleNames[idx.toNat]? with
              | some m => s!"in `{m}`"
              | none   => "in imported module"
            | none => "in current module"
          let locStr :=
            if env.contains (declName ++ `nonvacuous) then
              s!"{baseLoc}; found unverified `.nonvacuous` sibling not generated by `#nonvacuous`"
            else
              baseLoc
          missing := missing.push (privateToUserName declName, locStr)

    if !missing.isEmpty then
      let lines := missing.toList.map fun (nm, loc) => s!"  • `{nm}` ({loc})"
      throwErrorAt stx
        "non-vacuity coverage check failed: {missing.size} `@[contract]` declaration(s) missing a `.nonvacuous` witness or `@[vacuity_exempt \"reason\"]`:\n{String.intercalate "\n" lines}"
  | _ => throwUnsupportedSyntax

end

end ProofLib.NonVacuity
