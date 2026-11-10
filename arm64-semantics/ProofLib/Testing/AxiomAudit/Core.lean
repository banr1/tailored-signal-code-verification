/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.TrustedClosure
public meta import ProofLib.TrustedClosure
public meta import Lean

/-!
# Kernel Axiom Audit

Environment-level audit checking that theorem closures depend only on the standard Lean axioms
`[propext, Quot.sound, Classical.choice]`, rejecting `sorryAx`, `Lean.ofReduceBool`,
`Lean.trustCompiler`, compiled `bv_decide` LRAT axioms (`<lemma>._native.bv_decide.ax_*`), and
custom axioms.

Memoizes constant dependencies across the `Environment` DAG and attributes each non-standard axiom
to the declaration that introduced it (for `bv_decide` axioms, the prefix before `._native`).
Provides `#axiom_audit`, `#axiom_audit_modules`, `#axiom_audit_module`, and
`#trusted_closure_modules_batch` (with `!` strict variants that fail on violations).
-/

public meta section

namespace Testing.AxiomAudit

open Lean Elab Command

/-- Axioms accepted by `leanprover/comparator` (`permitted_axioms`). -/
def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Declaration responsible for an axiom: maps `Foo.bar._native.bv_decide.ax_1_5` to `Foo.bar`, and
    leaves other axioms unchanged. -/
def blameOf (ax : Name) : Name :=
  let comps := (privateToUserName ax).components
  match comps.findIdx? (· == `_native) with
  | some i => (comps.take i).foldl Name.append .anonymous
  | none => ax

/-- Human-readable class of a non-standard axiom. -/
def axiomKind (ax : Name) : String :=
  if ax == ``sorryAx then "sorry"
  else if ax == `Lean.ofReduceBool then "ofReduceBool"
  else if ax == `Lean.trustCompiler then "trustCompiler"
  else if ax.components.contains `bv_decide then "bv_decide"
  else if ax.components.contains `_native then "native"
  else "axiom"

/-- Memoized map from constant to the (deduplicated) non-standard axioms it transitively uses. -/
abbrev AuditM := StateT (Std.HashMap Name (Array Name)) CoreM

private def dedup (xs : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

/-- Non-standard axioms used by `c` (type, value, and inductive constructors). -/
partial def nonStdAxioms (c : Name) : AuditM (Array Name) := do
  if let some r := (← get)[c]? then return r
  -- Cycle guard (kernel constants are acyclic, but recursors/inductives refer to each other).
  modify (·.insert c #[])
  let env := (← getEnv).setExporting false
  let some ci := env.find? c | return #[]
  let res ← match ci with
    | .axiomInfo _ => do
      let axs ← Lean.collectAxioms c
      pure (dedup (axs.filter (!standardAxioms.contains ·)))
    | _ => do
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        deps := deps ++ v.getUsedConstants
      if let .inductInfo iv := ci then
        deps := deps ++ iv.ctors.toArray
      let mut acc := #[]
      for d in deps do
        acc := acc ++ (← nonStdAxioms d)
      pure (dedup acc)
  modify (·.insert c res)
  return res

/-- Summary of one audit run. -/
structure Report where
  total : Nat := 0
  dirty : Array (Name × Array Name) := #[]

/-- Audit `thms`, returning dirty theorems with their offending axioms. -/
def auditTheorems (thms : Array Name) : CoreM Report := do
  let go : AuditM Report := do
    let mut rep : Report := {}
    for t in thms do
      let axs ← nonStdAxioms t
      rep := { rep with total := rep.total + 1 }
      unless axs.isEmpty do
        rep := { rep with dirty := rep.dirty.push (t, axs) }
    return rep
  let (rep, _) ← go.run {}
  return rep

/-- Render a report: one summary line, a blame table sorted by number of dependent theorems, and
    one line per dirty theorem. -/
def renderReport (scope : String) (rep : Report) : String := Id.run do
  let mut blame : Std.HashMap Name (String × Nat) := {}
  for (_, axs) in rep.dirty do
    let culprits := dedup (axs.map blameOf)
    for ax in axs do
      let b := blameOf ax
      if culprits.contains b then
        let (k, n) := blame.getD b (axiomKind ax, 0)
        blame := blame.insert b (k, n)
    for b in culprits do
      let (k, n) := blame.getD b ("axiom", 0)
      blame := blame.insert b (k, n + 1)
  let sorted := blame.toArray.qsort fun (a, _, n) (b, _, m) =>
    n > m || (n == m && a.toString < b.toString)
  let mut lines := #[s!"[axiom_audit] scope={scope} theorems={rep.total} " ++
    s!"clean={rep.total - rep.dirty.size} dirty={rep.dirty.size} culprits={sorted.size}"]
  for (b, k, n) in sorted do
    lines := lines.push s!"[axiom_audit] blame {b} kind={k} dependents={n}"
  for (t, axs) in rep.dirty.qsort (fun a b => a.1.toString < b.1.toString) do
    let culprits := dedup (axs.map blameOf)
    lines := lines.push s!"[axiom_audit] dirty {t} <- {culprits.toList}"
  return "\n".intercalate lines.toList

/-- Shared elaboration: log the report, and throw if `strict` and anything is dirty. -/
def runAudit (scope : String) (thms : Array Name) (strict : Bool) : CommandElabM Unit := do
  let rep ← liftCoreM (auditTheorems thms)
  let msg := renderReport scope rep
  if strict && !rep.dirty.isEmpty then
    throwError msg
  else
    logInfo msg

/-- `#axiom_audit thm...` audits explicit theorems; `#axiom_audit! thm...` errors if any is dirty. -/
syntax (name := axiomAuditCmd) "#axiom_audit" ("!")? (ppSpace ident)+ : command

@[command_elab axiomAuditCmd] def elabAxiomAudit : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let ids := stx[2].getArgs
  let mut thms := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    thms := thms.push n
  runAudit "explicit" thms strict

/-- True when `c` is a non-auxiliary declaration name after stripping `_private.<mod>.0.`. -/
def isUserFacing (c : Name) : Bool :=
  let u := privateToUserName c
  !u.isInternalDetail && !u.isInternal

/-- Theorems declared in imported modules selected by `sel`. Includes every `.thmInfo` constant in
    `Theorems` modules (including `_`-prefixed names) and user-facing theorems in other modules. -/
def importedTheoremsWhere (env : Environment) (sel : Name → Bool)
    (modNameFn : Name → Name := id) : Array Name := Id.run do
  let mods := env.header.moduleNames
  let mut thms := #[]
  for h : idx in [:mods.size] do
    let m := modNameFn mods[idx]
    let inTheorems := ProofLib.TrustedClosure.isTheoremsModule m
    if sel m then
      if h2 : idx < env.header.moduleData.size then
        for ci in env.header.moduleData[idx].constants do
          if ci matches .thmInfo _ then
            if inTheorems || isUserFacing ci.name then
              thms := thms.push ci.name
  return thms

/-- `#axiom_audit_modules P...` audits every user-facing theorem declared in an imported module
    whose name has prefix `P` in one shared memoized pass; `!` errors if any is dirty. -/
syntax (name := axiomAuditModulesCmd) "#axiom_audit_modules" ("!")? (ppSpace ident)+ : command

@[command_elab axiomAuditModulesCmd] def elabAxiomAuditModules : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let pfxs := stx[2].getArgs.map (·.getId)
  let scope := if h : pfxs.size = 1 then pfxs[0].toString else s!"prefixes({pfxs.size})"
  runAudit scope (importedTheoremsWhere (← getEnv) (fun m => pfxs.any (·.isPrefixOf m))) strict

/-- `#trusted_closure_modules_batch P...` audits every user-facing theorem declared in an imported
    non-fixture module under `P...` (and every theorem in any `Theorems` module under `P...`) in
    one shared `FastClosureM` pass; `!` fails on any `Alloc` leak or `Theorems` purity violation. -/
syntax (name := trustedClosureModulesBatchCmd)
  "#trusted_closure_modules_batch" ("!")? (ppSpace ident)+ : command

@[command_elab trustedClosureModulesBatchCmd]
def elabTrustedClosureModulesBatch : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let pfxs := stx[2].getArgs.map (·.getId)
  let scope := if h : pfxs.size = 1 then pfxs[0].toString else s!"prefixes({pfxs.size})"
  let env ← getEnv
  let explicitFixturePfxs := pfxs.filter (·.toString.endsWith ".Fixtures")
  let thms := importedTheoremsWhere env fun m =>
    pfxs.any (·.isPrefixOf m) &&
    (ProofLib.TrustedClosure.isTheoremsModule m ||
      !m.toString.endsWith ".Fixtures" ||
      explicitFixturePfxs.any (·.isPrefixOf m))
  ProofLib.TrustedClosure.runClosureCheck scope thms strict (printAll := false)
    (cliMods := env.header.moduleNames.filter fun m => pfxs.any (·.isPrefixOf m))

/-- `#axiom_audit_module M...` audits every user-facing theorem declared in the exact imported
    modules `M...` (excluding submodules) in one pass; `!` errors if any is dirty. Errors if any
    `M` is not imported. -/
syntax (name := axiomAuditModuleCmd) "#axiom_audit_module" ("!")? (ppSpace ident)+ : command

@[command_elab axiomAuditModuleCmd] def elabAxiomAuditModule : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let ms := stx[2].getArgs.map (·.getId)
  let env ← getEnv
  for m in ms do
    unless env.header.moduleNames.contains m do
      throwError "#axiom_audit_module: module {m} is not imported"
  let scope := if h : ms.size = 1 then s!"module {ms[0]}" else s!"modules({ms.size})"
  runAudit scope (importedTheoremsWhere env ms.contains) strict

/-- Remap imported fixture module `fromMod` to `targetMod` and run both
    `Testing.AxiomAudit.importedTheoremsWhere` and `ProofLib.TrustedClosure.importedTheoremsWhere`
    with `runClosureCheck` (`enforceAllStmtPurity := false`) on `Theorems` path/name edge cases. -/
syntax (name := testTheoremsModuleRemapCmd)
  "#test_theorems_module_remap!" ppSpace ident ppSpace ident ppSpace ident : command

@[command_elab testTheoremsModuleRemapCmd]
def elabTestTheoremsModuleRemap : CommandElab := fun stx => do
  let fromMod := stx[1].getId
  let targetMod := stx[2].getId
  let expectedThm := stx[3].getId
  let remap : Name → Name := fun m => if m == fromMod then targetMod else m
  let env ← getEnv
  let axiomThms := importedTheoremsWhere env (· == targetMod) remap
  unless axiomThms.contains expectedThm do
    throwError m!"Testing.AxiomAudit.importedTheoremsWhere skipped {expectedThm} in {targetMod}; got={axiomThms.toList}"
  let thms := ProofLib.TrustedClosure.importedTheoremsWhere env (· == targetMod) remap
  ProofLib.TrustedClosure.runClosureCheck targetMod.toString thms (strict := true)
    (printAll := false) (enforceAllStmtPurity := false) (modNameFn := remap)

end Testing.AxiomAudit
