/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# Kernel Cost Profiling

Diagnostic commands `#kernel_profile`, `#kernel_profile!`, `#kernel_profile_module`,
`#kernel_profile_module!`, and `#kernel_hotspots` that time `Kernel.check` and `Kernel.isDefEq`
on stored proof terms without modifying the environment.

Timings are wall-clock nanoseconds around a single synchronous kernel call. A site re-checked in
isolation does not share the kernel caches of the full check, so site times rank sites without
partitioning the declaration total.
-/

namespace ProofLib.ProofTerm

public meta section

open Lean Meta Elab Command

register_option proofLib.kernelProfile.thresholdMs : Nat := {
  defValue := 5000
  descr := "`#kernel_profile_module` lists (and the `!` variants reject) declarations whose kernel check takes at least this many milliseconds"
}

register_option proofLib.kernelProfile.deterministic : Bool := {
  defValue := false
  descr := "print `<t>` instead of timings and sort by name (for `#guard_msgs` regression tests)"
}

register_option proofLib.kernelHotspots.top : Nat := {
  defValue := 8
  descr := "number of definitional-equality sites `#kernel_hotspots` prints"
}

register_option proofLib.kernelHotspots.minMs : Nat := {
  defValue := 10
  descr := "`#kernel_hotspots` only prints sites whose isolated kernel check takes at least this many milliseconds"
}

/-! ## Timed kernel calls

The kernel entry points are pure functions, so the compiler is free to evaluate a call wherever
it likes (for example when the closure passed to `timed` is built). Each wrapper therefore takes
the first clock reading `t` and makes its input depend on it (`pick t e`, which returns `e` for
every `t ≠ 0`), so the call cannot run before that reading; `timed` stores the result in a
reference before the second reading, so it cannot run after it either. -/

/-- `e`, behind an opaque dependency on the clock reading `t` (never `0` in practice). -/
@[noinline] def pick (t : Nat) (e : Expr) : Expr := if t == 0 then .bvar 0 else e

/-- `Kernel.check` with a dependency on the clock reading `t`. -/
@[noinline] def kernelCheckAt (env : Environment) (lctx : LocalContext) (e : Expr) (t : Nat) :
    Except Kernel.Exception Expr :=
  Kernel.check env lctx (pick t e)

/-- `Kernel.isDefEq` with a dependency on the clock reading `t`. -/
@[noinline] def kernelDefEqAt (env : Environment) (lctx : LocalContext) (a b : Expr) (t : Nat) :
    Except Kernel.Exception Bool :=
  Kernel.isDefEq env lctx (pick t a) b

/-- `Kernel.whnf` with a dependency on the clock reading `t`. -/
@[noinline] def kernelWhnfAt (env : Environment) (lctx : LocalContext) (e : Expr) (t : Nat) :
    Except Kernel.Exception Expr :=
  Kernel.whnf env lctx (pick t e)

/-- Run `f` (given the first clock reading) and return its result with the elapsed nanoseconds. -/
def timed {α : Type} (f : Nat → Except Kernel.Exception α) :
    BaseIO (Except Kernel.Exception α × Nat) := do
  let t0 ← IO.monoNanosNow
  -- Storing the result in a reference is an effect that needs the value, so the kernel call
  -- runs before the second clock reading (a plain `match` lets the compiler move that reading
  -- in front of the call).
  let ref ← IO.mkRef (none : Option (Except Kernel.Exception α))
  ref.set (some (f t0))
  let t1 ← IO.monoNanosNow
  match ← ref.get with
  | some r => return (r, t1 - t0)
  | none => return (f t0, t1 - t0)

/-- Milliseconds with one decimal, e.g. `1234.5 ms`; `<t>` in deterministic mode. -/
def fmtMs (opts : Options) (ns : Nat) : String :=
  if proofLib.kernelProfile.deterministic.get opts then "<t>"
  else
    let tenths := (ns + 50000) / 100000
    s!"{tenths / 10}.{tenths % 10} ms"

/-- Percentage with one decimal; `<p>` in deterministic mode. -/
def fmtPct (opts : Options) (part total : Nat) : String :=
  if proofLib.kernelProfile.deterministic.get opts then "<p>"
  else if total == 0 then "0.0%"
  else
    let tenths := (part * 1000 + total / 2) / total
    s!"{tenths / 10}.{tenths % 10}%"

/-! ## Per-declaration kernel time -/

/-- Kernel cost of one declaration. -/
structure DeclCost where
  name : Name
  /-- `Kernel.check` of the stored value. -/
  checkNs : Nat := 0
  /-- `Kernel.isDefEq` of the inferred type against the declared type. -/
  typeNs : Nat := 0
  /-- Number of auxiliary declarations (`foo._proof_1`, `decide +kernel` lemmas, ...) whose cost is
      included. -/
  aux : Nat := 0
  /-- Kernel error, if the re-check failed (e.g. a body that depends on a private constant). -/
  error? : Option MessageData := none
  deriving Inhabited

def DeclCost.total (c : DeclCost) : Nat := c.checkNs + c.typeNs

/-- Re-check `ci`'s value with the kernel and time it. `none` if `ci` has no value. -/
def profileConst (ci : ConstantInfo) : CoreM (Option DeclCost) := do
  let some v := ci.value? (allowOpaque := true) | return none
  let env ← getEnv
  let opts ← getOptions
  let (r, checkNs) ← timed fun t => kernelCheckAt env {} v t
  match r with
  | .error e => return some { name := ci.name, checkNs, error? := e.toMessageData opts }
  | .ok ty =>
    let (r2, typeNs) ← timed fun t => kernelDefEqAt env {} ty ci.type t
    match r2 with
    | .ok true => return some { name := ci.name, checkNs, typeNs }
    | .ok false =>
      return some { name := ci.name, checkNs, typeNs,
                    error? := m!"inferred type is not definitionally equal to the declared type" }
    | .error e => return some { name := ci.name, checkNs, typeNs, error? := e.toMessageData opts }

/-- The declaration an auxiliary constant belongs to: the prefix before the first component that
    starts with `_` or is numeric (`foo._proof_1 ↦ foo`, `foo._auxLemma.3 ↦ foo`). -/
def ownerOf (n : Name) : Name :=
  -- `_private.<Module>.0.foo._proof_1`: keep the private prefix, strip after the user name.
  let user := privateToUserName n
  let prefixLen := n.components.length - user.components.length
  let comps := n.components
  let internal (c : Name) : Bool :=
    match c with
    | .str _ s => s.startsWith "_"
    | .num .. => true
    | .anonymous => false
  match (comps.drop prefixLen).findIdx? internal with
  | some 0 | none => n
  | some i => (comps.take (prefixLen + i)).foldl Name.append .anonymous

/-- Grouping key of a constant: its owner with any private prefix removed, so a private
    auxiliary lemma (`_private.M.0.foo._proof_1`, as the module system names them) groups with the
    public `foo`. -/
def ownerKey (n : Name) : Name := privateToUserName (ownerOf n)

/-- Declarations worth profiling: theorems, definitions and opaque constants with a value,
    excluding auxiliary recursors and `noConfusion` constructions. -/
def isProfiled (env : Environment) (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
    !isAuxRecursor env ci.name && !isNoConfusion env ci.name
  | _ => false

/-- Sum the costs of a declaration and its auxiliary declarations under the owner's name. -/
def aggregate (owner : Name) (cs : Array DeclCost) : DeclCost :=
  cs.foldl (init := { name := owner })
    fun acc c => { acc with checkNs := acc.checkNs + c.checkNs, typeNs := acc.typeNs + c.typeNs,
                            aux := acc.aux + (if c.name == owner then 0 else 1),
                            error? := acc.error?.orElse fun _ => c.error? }

/-- Format and log a profile. `strict` turns entries above the threshold into an error. -/
def reportProfile (scope : String) (costs : Array DeclCost) (thresholdNs : Nat) (strict : Bool)
    (listAll : Bool) : CommandElabM Unit := do
  let opts ← getOptions
  let det := proofLib.kernelProfile.deterministic.get opts
  let total := costs.foldl (· + ·.total) 0
  let sorted :=
    if det then costs.qsort (fun a b => a.name.toString < b.name.toString)
    else costs.qsort (fun a b => a.total > b.total)
  let over := sorted.filter (·.total ≥ thresholdNs)
  let failed := sorted.filter (·.error?.isSome)
  let shown := if listAll then sorted else over
  let mut msg : MessageData :=
    m!"[kernel_profile] scope={scope} decls={costs.size} over_threshold={over.size} \
      threshold={fmtMs opts thresholdNs} total={fmtMs opts total}"
  for c in shown do
    let auxNote := if c.aux == 0 then "" else s!" aux_decls={c.aux}"
    msg := msg ++ m!"\n[kernel_profile] {c.name} kernel={fmtMs opts c.total} \
      (value {fmtMs opts c.checkNs} + type {fmtMs opts c.typeNs}) \
      share={fmtPct opts c.total total}{auxNote}"
  for c in failed do
    msg := msg ++ m!"\n[kernel_profile] {c.name} kernel re-check failed: {c.error?.getD m!""}"
  if strict && (over.size > 0 || failed.size > 0) then
    throwError msg
  else
    logInfo msg

def resolveDecl (id : Ident) : CommandElabM ConstantInfo := do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some ci := (← getEnv).find? n | throwError "unknown declaration '{n}'"
  return ci

/-- All profiled constants (imported and local) whose owner is in `owners`. -/
def auxConstsOf (owners : NameSet) (named : Array Name := #[]) : CoreM (Array ConstantInfo) := do
  let env ← getEnv
  let pick (acc : Array ConstantInfo) (n : Name) (ci : ConstantInfo) : Array ConstantInfo :=
    if owners.contains (ownerKey n) && isProfiled env ci then acc.push ci else acc
  -- Auxiliary declarations live in their owner's module: scan only those modules (and the
  -- current file), not the whole environment.
  let mods : Std.HashSet Nat := named.foldl (init := {}) fun s n =>
    match env.getModuleIdxFor? n with
    | some idx => s.insert idx.toNat
    | none => s
  let mut acc := #[]
  for idx in mods do
    if h : idx < env.header.moduleData.size then
      for n in env.header.moduleData[idx].constNames do
        if let some ci := env.find? n then acc := pick acc n ci
  return env.constants.map₂.foldl pick acc

/-- Profile explicitly named declarations together with their auxiliary declarations. Every named
    declaration is listed. -/
def profileNamed (ids : Array Ident) (strict : Bool) : CommandElabM Unit := do
  let cis ← ids.mapM resolveDecl
  for ci in cis do
    if ci.value? (allowOpaque := true) |>.isNone then
      throwError "'{ci.name}' has no value to re-check (axiom, constructor, or body not \
        visible from this module; use `import all` for module-system files)"
  let owners : NameSet := cis.foldl (fun s ci => s.insert (ownerKey ci.name)) {}
  let all ← liftCoreM <| auxConstsOf owners (cis.map (·.name))
  let mut costs := #[]
  for ci in cis do
    let mut parts := #[]
    for a in all do
      if ownerKey a.name == ownerKey ci.name then
        if let some c ← liftCoreM (profileConst a) then parts := parts.push c
    costs := costs.push (aggregate ci.name parts)
  let thresholdNs := proofLib.kernelProfile.thresholdMs.get (← getOptions) * 1000000
  reportProfile "explicit" costs thresholdNs strict (listAll := true)

/-- Declarations of the current file, or of imported modules whose name starts with `pfx`. -/
def declsInScope (pfx? : Option Name) : CommandElabM (Array ConstantInfo) := do
  let env ← getEnv
  match pfx? with
  | none =>
    return env.constants.map₂.foldl (init := #[]) fun acc _ ci =>
      if isProfiled env ci then acc.push ci else acc
  | some pfx =>
    let mods := env.header.moduleNames
    return env.constants.map₁.fold (init := #[]) fun acc n ci =>
      match env.getModuleIdxFor? n with
      | some idx =>
        if pfx.isPrefixOf mods[idx.toNat]! && isProfiled env ci then acc.push ci else acc
      | none => acc

/-- Profile every declaration in scope (auxiliary declarations counted under their owner) and
    list those above the threshold. -/
def profileModule (pfx? : Option Name) (strict : Bool) : CommandElabM Unit := do
  let cis ← declsInScope pfx?
  let mut groups : Std.HashMap Name (Array DeclCost) := {}
  for ci in cis do
    if let some c ← liftCoreM (profileConst ci) then
      let o := ownerKey ci.name
      groups := groups.insert o ((groups.getD o #[]).push c)
  let costs := groups.fold (init := #[]) fun acc o cs => acc.push (aggregate o cs)
  let thresholdNs := proofLib.kernelProfile.thresholdMs.get (← getOptions) * 1000000
  let scope := match pfx? with | some p => s!"module {p}" | none => "current file"
  reportProfile scope costs thresholdNs strict (listAll := false)

/-- `#kernel_profile d₁ d₂ ...`: kernel re-check time of each declaration, largest first. -/
syntax (name := kernelProfileCmd) "#kernel_profile " (ppSpace ident)+ : command
/-- `#kernel_profile! d₁ ...`: like `#kernel_profile`, but an error when a declaration's kernel
    time reaches `proofLib.kernelProfile.thresholdMs`. -/
syntax (name := kernelProfileStrictCmd) "#kernel_profile! " (ppSpace ident)+ : command
/-- `#kernel_profile_module [Mod.Prefix]`: kernel re-check time of every declaration of the
    matching imported modules (or of the current file), listing those above
    `proofLib.kernelProfile.thresholdMs`. -/
syntax (name := kernelProfileModuleCmd) "#kernel_profile_module" (ppSpace ident)? : command
/-- Strict variant of `#kernel_profile_module`: an error when a declaration is above the
    threshold (a per-declaration kernel budget gate). -/
syntax (name := kernelProfileModuleStrictCmd) "#kernel_profile_module!" (ppSpace ident)? : command

@[command_elab kernelProfileCmd] def elabKernelProfile : CommandElab
  | `(#kernel_profile $ids*) => profileNamed ids (strict := false)
  | _ => throwUnsupportedSyntax

@[command_elab kernelProfileStrictCmd] def elabKernelProfileStrict : CommandElab
  | `(#kernel_profile! $ids*) => profileNamed ids (strict := true)
  | _ => throwUnsupportedSyntax

@[command_elab kernelProfileModuleCmd] def elabKernelProfileModule : CommandElab
  | `(#kernel_profile_module $[$pfx?]?) => profileModule (pfx?.map (·.getId)) (strict := false)
  | _ => throwUnsupportedSyntax

@[command_elab kernelProfileModuleStrictCmd] def elabKernelProfileModuleStrict : CommandElab
  | `(#kernel_profile_module! $[$pfx?]?) => profileModule (pfx?.map (·.getId)) (strict := true)
  | _ => throwUnsupportedSyntax

/-! ## Hot-spot localisation -/

/-- The tactic that usually produces an application with head `n`. -/
def provenance (n : Name) : String :=
  if n == ``Eq.mpr || n == ``Eq.mp || n == ``cast || n == ``Eq.ndrec || n == ``Eq.rec ||
      n == ``congrArg || n == ``Eq.substr || n == ``Eq.subst then
    "rewrite cast (rw / simp / subst)"
  else if n == ``id then "definitional cast (change / show / dsimp / unfold)"
  else if n == ``of_eq_true || n == ``eq_self then "rfl-closed simp goal"
  else if n == ``of_decide_eq_true then "decide (kernel evaluates the Decidable instance)"
  else "application argument (exact / apply / refine / autoParam)"

/-- `provenance`, refined by the expected type of the site: a `decide p = true` check, or the
    `(lhs = rhs) = (lhs' = rhs)` motive cast that `rw` wraps in `id`. -/
def siteProvenance (head : Name) (expected : Expr) : String :=
  match expected.eq? with
  | some (ty, l, _) =>
    if l.isAppOf ``Decidable.decide then "decide (kernel evaluates the Decidable instance)"
    else if head == ``id && ty.isProp then "rewrite motive cast (rw)"
    else provenance head
  | none => provenance head

/-- Callbacks of the generic proof-term walk `walkSites`. They run in the local context of the
    site (binders of the proof term are local declarations). -/
structure SiteHandlers where
  /-- A definitional-equality site whose two types differ syntactically:
      `kind` (`arg` / `let` / `type`), head constant, argument index, expected and actual type. -/
  defEq : String → Name → Nat → Expr → Expr → MetaM Unit
  /-- A type the kernel must reduce to a Π-type (`pi`) or a structure type (`proj`). -/
  whnf : String → Name → Nat → Expr → MetaM Unit := fun _ _ _ _ => pure ()
  /-- Every application node, before its arguments are visited. -/
  app : Expr → MetaM Unit := fun _ => pure ()

/-- Walk a term without loose bound variables, mirroring the kernel's type inference, and call
    the handlers at every site where the kernel must decide a definitional equality or reduce a
    type. Shared sub-terms are visited once (`visited`, keyed structurally). -/
partial def walkSites (h : SiteHandlers) (visited : IO.Ref (Std.HashSet Expr)) (e : Expr) :
    MetaM Unit := do
  if (← visited.get).contains e then return
  visited.modify (·.insert e)
  match e with
  | .app .. =>
    h.app e
    let f := e.getAppFn
    let args := e.getAppArgs
    let head := f.constName?.getD .anonymous
    unless f.isConst || f.isFVar do walkSites h visited f
    let mut fTy ← inferType f
    for hi : i in [0:args.size] do
      let a := args[i]
      walkSites h visited a
      unless fTy.isForall do
        h.whnf "pi" head i fTy
        -- the kernel exposes the Π-type with its own `whnf`; do the same (Meta's `whnf` can
        -- unfold much further than needed and is subject to `maxHeartbeats`)
        fTy ← match Kernel.whnf (← getEnv) (← getLCtx) fTy with
          | .ok t => pure t
          | .error _ => whnf fTy
      match fTy with
      | .forallE _ d b _ =>
        let aTy ← inferType a
        let d' := d.cleanupAnnotations.headBeta
        let aTy' := aTy.cleanupAnnotations.headBeta
        unless d' == aTy' do h.defEq "arg" head i d' aTy'
        fTy := b.instantiate1 a
      | _ => return  -- not a function type even after `whnf`: give up on this node
  | .lam n d b bi =>
    walkSites h visited d
    withLocalDecl n bi d fun x => walkSites h visited (b.instantiate1 x)
  | .forallE n d b bi =>
    walkSites h visited d
    withLocalDecl n bi d fun x => walkSites h visited (b.instantiate1 x)
  | .letE n t v b _ =>
    walkSites h visited t
    walkSites h visited v
    let vTy ← inferType v
    unless t == vTy do h.defEq "let" .anonymous 0 t vTy
    withLetDecl n t v fun x => walkSites h visited (b.instantiate1 x)
  | .proj s _ b =>
    walkSites h visited b
    let bTy ← inferType b
    unless bTy.getAppFn.constName? == some s do h.whnf "proj" s 0 bTy
  | .mdata _ b => walkSites h visited b
  | _ => pure ()

/-- Run `walkSites` on a declaration's value and on its "inferred ≡ declared type" site. -/
def walkDecl (h : SiteHandlers) (ci : ConstantInfo) : MetaM Unit :=
  -- re-traversing an elaborated term: `inferType` on big proofs must not hit `maxHeartbeats`
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let some v := ci.value? (allowOpaque := true) | return
  let visited ← IO.mkRef {}
  walkSites h visited v
  let vTy ← inferType v
  unless vTy == ci.type do h.defEq "type" .anonymous 0 ci.type vTy

/-- One definitional-equality (or Π-exposure) site of a proof term and its isolated kernel cost. -/
structure Site where
  ns : Nat
  /-- `arg`, `let`, `pi`, `proj` or `type`. -/
  kind : String
  /-- Head constant of the enclosing application (`anonymous` if none). -/
  head : Name
  /-- Argument index (0-based) for `arg` sites. -/
  argIdx : Nat
  expected : Expr
  actual : Expr
  lctx : LocalContext
  localInsts : LocalInstances

/-- Time every site of `ci` with the kernel; returns the sites at or above `minNs` and the number
    of sites timed. -/
def timeSites (ci : ConstantInfo) (minNs : Nat) : MetaM (Array Site × Nat) := do
  let sites ← IO.mkRef (#[] : Array Site)
  let count ← IO.mkRef 0
  let record (ns : Nat) (kind : String) (head : Name) (argIdx : Nat) (expected actual : Expr) :
      MetaM Unit := do
    count.modify (· + 1)
    if ns ≥ minNs then
      let site : Site := { ns, kind, head, argIdx, expected, actual, lctx := ← getLCtx,
                           localInsts := ← getLocalInstances }
      sites.modify (·.push site)
  let handlers : SiteHandlers := {
    defEq := fun kind head i expected actual => do
      let env ← getEnv
      let lctx ← getLCtx
      let (_, ns) ← timed fun t => kernelDefEqAt env lctx actual expected t
      record ns kind head i expected actual
    whnf := fun kind head i ty => do
      let env ← getEnv
      let lctx ← getLCtx
      let (r, ns) ← timed fun t => kernelWhnfAt env lctx ty t
      let reduced := match r with | .ok e => e | .error _ => ty
      record ns kind head i reduced ty }
  walkDecl handlers ci
  return (← sites.get, ← count.get)

def constsOf (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

/-- Constants occurring on exactly one side of a site, sorted by name, at most `k` per side. -/
def diffConsts (a b : Expr) (k : Nat := 8) : List Name × List Name :=
  let ca := constsOf a
  let cb := constsOf b
  let onlyA := ca.toList.filter (!cb.contains ·)
  let onlyB := cb.toList.filter (!ca.contains ·)
  let srt (l : List Name) := (l.toArray.qsort (·.toString < ·.toString)).toList.take k
  (srt onlyA, srt onlyB)

/-- Pretty-print a site's type compactly (deep subterms elided). -/
def ppCompact (s : Site) (e : Expr) : MetaM MessageData :=
  withLCtx s.lctx s.localInsts do
    withOptions (fun o => o.setBool `pp.deepTerms false |>.set `pp.deepTerms.threshold (6 : Nat)
        |>.setBool `pp.proofs false |>.set `pp.maxSteps (400 : Nat)) do
      return m!"{(← ppExpr e).pretty 100000}"

/-- Localise the kernel cost of declaration `ci` and of those of its auxiliary declarations
    (`aux`) whose own kernel time reaches the reporting minimum. -/
def hotspots (ci : ConstantInfo) (aux : Array ConstantInfo) : MetaM MessageData := do
  let opts ← getOptions
  let minNs := proofLib.kernelHotspots.minMs.get opts * 1000000
  let det := proofLib.kernelProfile.deterministic.get opts
  let mut total := 0
  let mut sites : Array (Name × Site) := #[]
  let mut nTimed := 0
  let mut walked : Array Name := #[]
  for c in #[ci] ++ aux do
    let some cost ← profileConst c | continue
    total := total + cost.total
    unless c.name == ci.name || cost.total ≥ minNs do continue
    walked := walked.push c.name
    let (cs, n) ← timeSites c minNs
    nTimed := nTimed + n
    sites := sites ++ cs.map (c.name, ·)
  let top := proofLib.kernelHotspots.top.get opts
  let key (x : Name × Site) : String := s!"{x.1}|{x.2.kind}|{x.2.head}|{x.2.argIdx}"
  let sorted :=
    if det then sites.qsort (fun a b => key a < key b)
    else sites.qsort (fun a b => a.2.ns > b.2.ns)
  let shown := sorted.toList.take top
  let auxNote := if aux.isEmpty then m!"" else m!" aux_decls={aux.size} walked={walked.toList}"
  let mut msg := m!"[kernel_hotspots] {ci.name} kernel={fmtMs opts total}{auxNote} \
    sites_timed={if det then "<n>" else toString nTimed} \
    over_min={if det then "<n>" else toString sorted.size} \
    (min {proofLib.kernelHotspots.minMs.get opts} ms)"
  let mut i : Nat := 0
  for (d, s) in shown do
    i := i + 1
    let (onlyExp, onlyAct) := diffConsts s.expected s.actual
    let what := match s.kind with
      | "arg" => s!"argument {s.argIdx} of `{s.head}` — {siteProvenance s.head s.expected}"
      | "let" => "`let` value against its declared type"
      | "pi" => s!"type of `{s.head}` reduced to a Π-type before argument {s.argIdx}"
      | "proj" => s!"structure type reduced for projection `{s.head}`"
      | _ => "inferred type of the value against the declared type"
    let inDecl := if d == ci.name then m!"" else m!" (in {d})"
    let reduces := s.kind == "pi" || s.kind == "proj"
    let (lblE, lblA) := if reduces then ("reduct", "type") else ("expected", "actual")
    msg := msg ++ m!"\n#{i} {fmtMs opts s.ns}  {what}{inDecl}\
      \n   {lblE}: {← ppCompact s s.expected}\
      \n   {lblA}: {← ppCompact s s.actual}\
      \n   only in {lblE}: {onlyExp}\
      \n   only in {lblA}: {onlyAct}"
  return msg

/-- `#kernel_hotspots d`: rank the definitional-equality sites of `d`'s proof term (and of its
    expensive auxiliary declarations) by isolated kernel cost (see the module docstring). -/
syntax (name := kernelHotspotsCmd) "#kernel_hotspots " ident : command

@[command_elab kernelHotspotsCmd] def elabKernelHotspots : CommandElab
  | `(#kernel_hotspots $id) => do
    let ci ← resolveDecl id
    if ci.value? (allowOpaque := true) |>.isNone then
      throwError "'{ci.name}' has no value to analyse"
    let aux := (← liftCoreM <| auxConstsOf (({} : NameSet).insert (ownerKey ci.name)) #[ci.name]).filter
      (·.name != ci.name)
    let msg ← liftTermElabM <| hotspots ci aux
    logInfo msg
  | _ => throwUnsupportedSyntax

end

end ProofLib.ProofTerm
