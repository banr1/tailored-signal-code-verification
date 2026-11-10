/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Process
public meta import Lean

/-!
# Trusted Closure Linter (`#trusted_closure`)

Computes the transitive `Arm64.Trusted.*` constant closure of theorem statements (with `optParam`
defaults erased) and checks statement-purity and syscall-bundle isolation invariants, failing
closed under `!` if a non-allocator bundle reaches `Arm64.Trusted.Syscalls.Alloc` or a `Theorems`
statement references non-`Spec` definitions.
-/

public meta section

namespace ProofLib.TrustedClosure

open Lean Elab Command

/-- Prefix of all trusted TCB modules. -/
def trustedModPrefix : Name := `Arm64.Trusted

/-- Module defining the virtual-memory allocator syscall family (`mmap`, `munmap`, `mprotect`,
    `madvise`, `brk`, `PAGE_SIZE`, `pageAlignUp`, non-frozen unmap/mprotect helpers). -/
def allocModName : Name := `Arm64.Trusted.Syscalls.Alloc

/-- Trusted supervisor-call bundle entry points that intentionally exclude `Alloc`. -/
def nonAllocBundleConsts : Array Name :=
  #[``Arm64.noSyscalls,
    ``Arm64.Syscall.none,
    ``Arm64.Syscall.stdioWrite,
    ``Arm64.Syscall.stdioCli,
    ``Arm64.Syscall.fileIo,
    ``Arm64.Syscall.signals,
    ``Arm64.Syscall.time,
    ``Arm64.Syscall.random,
    ``Arm64.Syscall.misc,
    ``Arm64.Program.noSyscalls,
    ``Arm64.Program.stdioWrite,
    ``Arm64.Program.stdioCli,
    ``Arm64.Program.fileIo]

/-- Trusted entry points that explicitly request the full standard table or the allocator bundle. -/
def allocCapableEntryConsts : Array Name :=
  #[``Arm64.Syscall.standard,
    ``Arm64.Syscall.alloc,
    ``Arm64.execSyscall,
    ``Arm64.execInst,
    ``Arm64.Program.pureMem,
    ``Arm64.Program.alloc]

/-- Resolve the declaring module of constant `c` in `env`. -/
def definingModuleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx =>
    let i := idx.toNat
    if h : i < env.header.moduleNames.size then env.header.moduleNames[i] else env.mainModule
  | none => env.mainModule

/-- Whether `c` is declared in an `Arm64.Trusted.*` module. -/
def isTrustedConst (env : Environment) (c : Name) : Bool :=
  trustedModPrefix.isPrefixOf (definingModuleOf env c)

/-- Prefix of the virtual-memory (`mm/`) syscall family modules (`Arm64.Trusted.Syscalls.Mm.*`). -/
def allocModPrefix : Name := `Arm64.Trusted.Syscalls.Mm

/-- Whether `c` is declared in `Arm64.Trusted.Syscalls.Alloc` or `Arm64.Trusted.Syscalls.Mm.*`. -/
def isAllocConst (env : Environment) (c : Name) : Bool :=
  let m := definingModuleOf env c
  m == allocModName || allocModPrefix.isPrefixOf m

private def dedupNames (xs : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

/-- Erase optional-argument defaults: `optParam α d` becomes `α`. `optParam α d` is reducibly `α`,
    so `d` is an elaboration hint only and never part of what a statement means; a judgment whose
    default argument is the full syscall table must not pull that table into the closure of a
    statement that passes a smaller bundle explicitly. -/
partial def stripOptParams (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity ``optParam 2 then some (stripOptParams e.appFn!.appArg!) else none

/-- Direct constant dependencies of `ci` (type with `optParam` defaults erased, body including
    private/opaque bodies, and inductive constructors). -/
def directDepsOf (ci : ConstantInfo) : Array Name := Id.run do
  let mut deps := (stripOptParams ci.type).getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then
    deps := deps ++ v.getUsedConstants
  if let .inductInfo iv := ci then
    deps := deps ++ iv.ctors.toArray
  return deps

/-- Precomputed bitset index over all `Arm64.Trusted.*` constants in `env`, sorted lexicographically
    by `Name.toString` so bit-order decoding yields already-sorted `Array Name` outputs. -/
private structure TrustedIndex where
  names : Array Name
  idxOf : Std.HashMap Name Nat
  modNames : Array Name
  constModIdx : Array Nat
  numWords : Nat
  allocMask : Array UInt64
  nonAllocMask : Array UInt64
  allocEntryMask : Array UInt64

private def emptyBits (w : Nat) : Array UInt64 := Id.run do
  let mut out := Array.mkEmpty w
  for _ in [:w] do
    out := out.push 0
  return out

private def setBit (bs : Array UInt64) (k : Nat) : Array UInt64 :=
  let wi := k / 64
  let bi := (k % 64).toUInt64
  if h : wi < bs.size then
    bs.set wi (bs[wi] ||| ((1 : UInt64) <<< bi))
  else
    bs

private def orBits (a b : Array UInt64) : Array UInt64 := Id.run do
  let mut out := a
  for i in [:b.size] do
    if h : i < out.size then
      out := out.set i (out[i] ||| b[i]!)
  return out

private def andBits (a b : Array UInt64) : Array UInt64 := Id.run do
  let mut out := Array.mkEmpty a.size
  for i in [:a.size] do
    out := out.push (a[i]! &&& b.getD i 0)
  return out

private def decodeBits (names : Array Name) (bs : Array UInt64) : Array Name := Id.run do
  let mut out := #[]
  for wi in [:bs.size] do
    let word := bs[wi]!
    if word != 0 then
      for bi in [:64] do
        if (word &&& ((1 : UInt64) <<< bi.toUInt64)) != 0 then
          let k := wi * 64 + bi
          if h : k < names.size then
            out := out.push names[k]
  return out

private def maskOfNames (w : Nat) (idxOf : Std.HashMap Name Nat) (ns : Array Name) :
    Array UInt64 := Id.run do
  let mut m := emptyBits w
  for n in ns do
    if let some k := idxOf[n]? then
      m := setBit m k
  return m

private def buildTrustedIndex (env : Environment) : TrustedIndex := Id.run do
  let mut raw : Array Name := #[]
  let mods := env.header.moduleNames
  for h : idx in [:mods.size] do
    if trustedModPrefix.isPrefixOf mods[idx] then
      if h2 : idx < env.header.moduleData.size then
        for ci in env.header.moduleData[idx].constants do
          raw := raw.push ci.name
  if trustedModPrefix.isPrefixOf env.mainModule then
    for (c, _) in env.constants.map₂ do
      raw := raw.push c
  let unique := dedupNames raw
  let sorted := (unique.map fun n => (n, n.toString)).qsort (fun a b => a.2 < b.2)
  let names := sorted.map (·.1)
  let mut idxOf : Std.HashMap Name Nat := {}
  for h : k in [:names.size] do
    idxOf := idxOf.insert names[k] k
  let w := (names.size + 63) / 64
  let rawMods := dedupNames (names.map (definingModuleOf env))
  let sortedMods := (rawMods.map fun m => (m, m.toString)).qsort (fun a b => a.2 < b.2)
  let modNames := sortedMods.map (·.1)
  let mut modIdxOf : Std.HashMap Name Nat := {}
  for h : mi in [:modNames.size] do
    modIdxOf := modIdxOf.insert modNames[mi] mi
  let mut constModIdx := Array.mkEmpty names.size
  let mut allocMask := emptyBits w
  for h : k in [:names.size] do
    constModIdx := constModIdx.push (modIdxOf.getD (definingModuleOf env names[k]) 0)
    if isAllocConst env names[k] then
      allocMask := setBit allocMask k
  let nonAllocMask := maskOfNames w idxOf nonAllocBundleConsts
  let allocEntryMask := maskOfNames w idxOf allocCapableEntryConsts
  return {
    names, idxOf, modNames, constModIdx,
    numWords := w, allocMask, nonAllocMask, allocEntryMask
  }

/-- Cached `(fullClosureBits, boundaryEntryBits)` per constant in `env`. -/
private structure ConstSummary where
  full : Array UInt64
  entry : Array UInt64

/-- Memoized state for full transitive and boundary-entry `Arm64.Trusted.*` closure walks. -/
private abbrev FastClosureM := StateT (Std.HashMap Name ConstSummary) CoreM

private partial def summaryOfConst (env : Environment) (tidx : TrustedIndex) (c : Name) :
    FastClosureM ConstSummary := do
  if let some cached := (← get)[c]? then
    return cached
  let z := emptyBits tidx.numWords
  modify (·.insert c { full := z, entry := z })
  let some ci := env.find? c | return { full := z, entry := z }
  match tidx.idxOf[c]? with
  | some k =>
    let selfBits := setBit z k
    let mut full := selfBits
    for d in directDepsOf ci do
      let child ← summaryOfConst env tidx d
      full := orBits full child.full
    let res : ConstSummary := { full, entry := selfBits }
    modify (·.insert c res)
    return res
  | none =>
    let mut full := z
    let mut entry := z
    for d in directDepsOf ci do
      let child ← summaryOfConst env tidx d
      full := orBits full child.full
      entry := orBits entry child.entry
    let res : ConstSummary := { full, entry }
    modify (·.insert c res)
    return res

private def summaryOfExpr (env : Environment) (tidx : TrustedIndex) (e : Expr) :
    FastClosureM ConstSummary := do
  let z := emptyBits tidx.numWords
  let mut full := z
  let mut entry := z
  for d in e.getUsedConstants do
    let child ← summaryOfConst env tidx d
    full := orBits full child.full
    entry := orBits entry child.entry
  return { full, entry }

/-- Memoized state for standalone `trustedClosureOfConst` / `trustedClosureOfExpr` callers. -/
abbrev ClosureM := StateT (Std.HashMap Name (Array Name)) CoreM

/-- Compute all constants declared in `Arm64.Trusted.*` reachable from constant `c`. -/
partial def trustedClosureOfConst (env : Environment) (c : Name) : ClosureM (Array Name) := do
  let tidx := buildTrustedIndex env
  let (s, _) ← (summaryOfConst env tidx c).run {}
  return decodeBits tidx.names s.full

/-- Compute all `Arm64.Trusted.*` constants reachable from expression `e`. -/
def trustedClosureOfExpr (env : Environment) (e : Expr) : ClosureM (Array Name) := do
  let tidx := buildTrustedIndex env
  let (s, _) ← (summaryOfExpr env tidx e).run {}
  return decodeBits tidx.names s.full

/-- Find a shortest blame path from `roots` to any constant satisfying `pred` in `env`. -/
def findBlamePath (env : Environment) (roots : Array Name) (pred : Name → Bool) :
    Option (Array Name) := Id.run do
  let mut parent : Std.HashMap Name (Option Name) := {}
  let mut queue : Array Name := #[]
  for r in roots do
    unless parent.contains r do
      parent := parent.insert r none
      queue := queue.push r
  let mut i : Nat := 0
  let mut hit : Option Name := none
  while h : i < queue.size do
    let cur := queue[i]
    i := i + 1
    if pred cur then
      hit := some cur
      break
    if let some ci := env.find? cur then
      for d in directDepsOf ci do
        unless parent.contains d do
          parent := parent.insert d (some cur)
          queue := queue.push d
  let some target := hit | return none
  let mut path : Array Name := #[target]
  let mut cur := target
  for _ in [:queue.size + 1] do
    match parent.getD cur none with
    | some p =>
      path := path.push p
      cur := p
    | none => break
  return some path.reverse

/-- Per-theorem trusted closure audit record. -/
structure TheoremClosure where
  thm : Name
  defMod : Name
  entryBundles : Array Name
  trustedModules : Array Name
  trustedConsts : Array Name
  allocConsts : Array Name
  violation? : Option String

private def formatPath (p : Array Name) : String :=
  " -> ".intercalate (p.toList.map Name.toString)

/-- Fixed role directory names inside a `FormalRfcs` package. -/
def formalRfcRoleDirs : List String :=
  ["Spec", "Proofs", "Testing", "Theorems", "Generated", "Witness", "Implementation", "Drivers"]

/-- Whether `rfc` / `imp` name a per-implementation formal RFC package `FormalRfcs.<Rfc>.<Impl>`
    (`<Rfc>` not `Common`, neither a fixed package role directory), matching
    `tcb_map::discovery::package_depth`. -/
def isFormalRfcImplPackage (rfc imp : String) : Bool :=
  rfc != "Common" && !formalRfcRoleDirs.contains rfc && !formalRfcRoleDirs.contains imp

/-- Whether `m` is a `Theorems` module (`VerifiedLibraries.Theorems[.*]`,
    `VerifiedLibraries.<Lib>.Theorems[.*]`, `CaseStudies.<Lib>.Theorems[.*]` for
    `Lib ≠ "Testing"`, or `FormalRfcs.<Rfc>.<Impl>.Theorems[.*]`), matching
    `tcb_map::discovery::classify` with no `Testing` exemption under `Theorems`. -/
def isTheoremsModule (m : Name) : Bool :=
  match m.components.map Name.toString with
  | "VerifiedLibraries" :: "Theorems" :: _ => true
  | "VerifiedLibraries" :: lib :: "Theorems" :: _ => lib != "Testing"
  | "CaseStudies" :: lib :: "Theorems" :: _ => lib != "Testing"
  | "FormalRfcs" :: rfc :: imp :: "Theorems" :: _ => isFormalRfcImplPackage rfc imp
  | _ => false

/-- Whether `m` is a trusted specification or toolchain module allowed in the type closure of a
    `Theorems` theorem statement (`Init`/`Std`/`Lean`/`Lake`, `Arm64[.*]` outside `Testing`,
    non-`Testing` `(VerifiedLibraries|CaseStudies).<Pkg>.Spec[.*]`, the formal RFC models
    `FormalRfcs.<Rfc>.Spec[.*]` and `FormalRfcs.<Rfc>.<Impl>.Spec[.*]`, the shared equivalence
    vocabulary `Equivalence.Spec[.*]`, or `(VerifiedLibraries|CaseStudies).<Pkg>.Generated.*Obj`;
    `*.Theorems.*` is never allowed).
    `Spec` / `Generated` are matched positionally (third component; second for
    `Equivalence`), exactly like
    `tcb_map::discovery::classify`, so a `Proofs` module such as
    `CaseStudies.<Pkg>.Proofs.Spec.X` can never supply statement vocabulary. -/
def isAllowedTheoremsStmtModule (m : Name) : Bool :=
  let comps := m.components.map Name.toString
  if comps.any (· == "Testing") || isTheoremsModule m then
    false
  else
    match comps with
    | "Init" :: _ | "Std" :: _ | "Lean" :: _ | "Lake" :: _ | "Arm64" :: _ => true
    | "CaseStudies" :: _ :: "Spec" :: _ | "VerifiedLibraries" :: _ :: "Spec" :: _ => true
    | "Equivalence" :: "Spec" :: _ => true
    | "FormalRfcs" :: rfc :: "Spec" :: _ => !formalRfcRoleDirs.contains rfc
    | "FormalRfcs" :: rfc :: imp :: "Spec" :: _ => isFormalRfcImplPackage rfc imp
    | "CaseStudies" :: _ :: "Generated" :: _ :: _
    | "VerifiedLibraries" :: _ :: "Generated" :: _ :: _ =>
      (comps.getLast?.getD "").endsWith "Obj"
    | _ => false

/-! ## Formal RFC CLI statement shape

A per-implementation formal RFC package `FormalRfcs.<Rfc>.<Impl>` states only instantiations of
the shared CLI templates. This check runs on the elaborated statements, so no name resolution
trick (an enclosing `namespace`, a decoy declaration, a coercion) can change what is checked. -/

/-- The shared CLI statement templates, all declared under `formalRfcTemplateModPrefix`. -/
def formalRfcCliTemplates : Array Name :=
  #[`FormalRfcs.CliProfile.DecodeCliStmt, `FormalRfcs.CliProfile.EncodeCliStmt]

/-- Modules allowed to declare a shared CLI statement template. -/
def formalRfcTemplateModPrefix : Name := `FormalRfcs.Common.Spec

/-- Most implementation `Spec` definitions unfolded before the head must be a template. -/
def formalRfcCliUnfoldFuel : Nat := 8

/-- `(rfc, impl, role)` of a per-implementation module `FormalRfcs.<Rfc>.<Impl>.<Role>[.*]`. -/
def formalRfcImplModule? (m : Name) : Option (String × String × String) :=
  match m.components.map Name.toString with
  | "FormalRfcs" :: rfc :: imp :: role :: _ =>
    if isFormalRfcImplPackage rfc imp then some (rfc, imp, role) else none
  | _ => none

/-- Whether `ty` is `List (BitVec 8)` (or an abbreviation that is syntactically that). -/
def isFormalRfcByteListType (ty : Expr) : Bool :=
  match ty.consumeMData with
  | .app (.const ``List _) arg =>
    match arg.consumeMData with
    | .app (.const ``BitVec []) w =>
      let w := w.consumeMData
      w.nat? == some 8 || w.rawNatLit? == some 8
    | _ => false
  | _ => false

/-- Check that `e` is `<Template> <P> <D> <E>` for the implementation `FormalRfcs.<rfc>.<imp>`,
    after unfolding at most `formalRfcCliUnfoldFuel` argument-free definitions declared in the
    implementation's own `Spec`: the head is exactly a template of `formalRfcCliTemplates`, declared
    under `formalRfcTemplateModPrefix`; `<P>` and `<D>` are bare constants named and declared in
    `FormalRfcs.<rfc>.Spec`; `<E>` is the bare constant `FormalRfcs.<rfc>.<imp>.elfBytes`, a
    definition of type `List (BitVec 8)` declared in `FormalRfcs.<rfc>.<imp>.Spec` (its body is a
    `file_bytes%` literal; the `formal-rfcs-statement-shape` repo-lint checks the path).
    `modOf` resolves a constant's declaring module. Returns the template, or an error. -/
def formalRfcCliStmtCheck (env : Environment) (modOf : Name → Name) (rfc imp : String)
    (e : Expr) : Except String Name := do
  let rfcNs : Name := (`FormalRfcs).str rfc
  let implNs : Name := rfcNs.str imp
  let rfcSpecMod : Name := rfcNs.str "Spec"
  let implSpecMod : Name := implNs.str "Spec"
  -- Unfold only argument-free definitions of this implementation's `Spec`.
  let mut cur := e.consumeMData
  let mut fuel := formalRfcCliUnfoldFuel
  repeat
    let .const c us := cur | break
    unless implSpecMod.isPrefixOf (modOf c) do break
    if fuel == 0 then
      throw s!"unfolds more than {formalRfcCliUnfoldFuel} definitions of {implSpecMod} without reaching a CLI template"
    let some ci@(.defnInfo _) := env.find? c
      | throw s!"{c} (in {implSpecMod}) is not a definition whose body is visible"
    cur := (ci.instantiateValueLevelParams! us).consumeMData
    fuel := fuel - 1
  let fn := cur.getAppFn.consumeMData
  let args := cur.getAppArgs.map Expr.consumeMData
  let .const t _ := fn
    | throw s!"head is not a constant: {cur}"
  unless formalRfcCliTemplates.contains t do
    throw s!"head {t} is not one of the shared CLI templates {formalRfcCliTemplates.toList}"
  unless formalRfcTemplateModPrefix.isPrefixOf (modOf t) do
    throw s!"template {t} is declared in {modOf t}, not under {formalRfcTemplateModPrefix}"
  unless args.size == 3 do
    throw s!"template {t} is applied to {args.size} arguments, not 3"
  let rfcConst (what : String) (a : Expr) : Except String Unit := do
    let .const c _ := a
      | throw s!"{what} is not a constant of {rfcSpecMod}: {a}"
    unless rfcNs.isPrefixOf c && rfcSpecMod.isPrefixOf (modOf c) do
      throw s!"{what} {c} (in {modOf c}) is not a {rfcNs} constant declared in {rfcSpecMod}"
  rfcConst "profile" args[0]!
  rfcConst "decoder" args[1]!
  let elfName := implNs.str "elfBytes"
  let .const c _ := args[2]!
    | throw s!"ELF is not the constant {elfName}: {args[2]!}"
  unless c == elfName && implSpecMod.isPrefixOf (modOf c) do
    throw s!"ELF {c} (in {modOf c}) is not {elfName} declared in {implSpecMod}"
  let some ci@(.defnInfo _) := env.find? c
    | throw s!"ELF {c} is not a definition"
  unless ci.levelParams.isEmpty && isFormalRfcByteListType ci.type do
    throw s!"ELF {c} does not have type List (BitVec 8)"
  return t

/-- Statement violations of the per-implementation package `FormalRfcs.<rfc>.<imp>`: its `Spec`
    declares `DecodeStmt` (and optionally `EncodeStmt`), argument-free `Prop` definitions that
    pass `formalRfcCliStmtCheck` with the decode / encode template respectively. -/
def formalRfcPackageViolations (env : Environment) (modOf : Name → Name) (rfc imp : String) :
    Array String := Id.run do
  let implNs : Name := ((`FormalRfcs).str rfc).str imp
  let implSpecMod : Name := implNs.str "Spec"
  let mut out := #[]
  for (stmt, tmpl, required) in
      [("DecodeStmt", `FormalRfcs.CliProfile.DecodeCliStmt, true),
       ("EncodeStmt", `FormalRfcs.CliProfile.EncodeCliStmt, false)] do
    let c := implNs.str stmt
    match env.find? c with
    | none =>
      if required then
        out := out.push s!"formal RFC package {implNs} declares no {c} (in {implSpecMod})"
    | some ci =>
      if !(ci matches .defnInfo _) || !implSpecMod.isPrefixOf (modOf c) then
        out := out.push s!"{c} (in {modOf c}) is not a definition declared in {implSpecMod}"
      else if !ci.levelParams.isEmpty || ci.type.consumeMData != .sort .zero then
        out := out.push s!"{c} is not an argument-free Prop"
      else
        match formalRfcCliStmtCheck env modOf rfc imp (.const c []) with
        | .error err => out := out.push s!"{c} is not a CLI template instantiation: {err}"
        | .ok t =>
          if t != tmpl then
            out := out.push s!"{c} instantiates {t}, not {tmpl}"
  return out

/-- Package violations (`formalRfcPackageViolations`) of every per-implementation package with a
    `Spec` or `Theorems` module in `mods` (module names after `modNameFn`). -/
def formalRfcPackagesViolations (env : Environment) (mods : Array Name)
    (modNameFn : Name → Name := id) : Array String := Id.run do
  let mut seen : Std.HashSet (String × String) := {}
  let mut out := #[]
  for m in mods do
    let some (rfc, imp, role) := formalRfcImplModule? m | continue
    unless role == "Spec" || role == "Theorems" do continue
    if seen.contains (rfc, imp) then continue
    seen := seen.insert (rfc, imp)
    out := out ++ formalRfcPackageViolations env (fun c => modNameFn (definingModuleOf env c)) rfc imp
  return out

/-- Compiler-generated auxiliary theorems, which a `Theorems` module may contain next to its
    statements: reserved names (`eq_N`, `eq_def`, `_unfold`, ...), and internal-detail names
    (`_proof_N`, `match_N`, ...) whose parent is a constant declared in the same module, or
    `<module>._auxLemma.N` of the declaring module. A user theorem merely *named* like an
    auxiliary (`_foo`, `match_1`, or `<P>.match_1` for a parent `P` of another module) is not
    one. -/
def isCompilerAuxTheorem (env : Environment) (c : Name) : Bool :=
  isReservedName env c ||
    ((privateToUserName c).isInternalDetail &&
      match c with
      | .str p _ | .num p _ =>
        let m := definingModuleOf env c
        (env.contains p && definingModuleOf env p == m) || p == m.str "_auxLemma"
      | .anonymous => false)

/-- The violation, if any, of theorem `t` (of type `ty`) of the formal RFC implementation
    `FormalRfcs.<rfc>.<imp>`'s `Theorems`: it must state a CLI template instantiation
    (`formalRfcCliStmtCheck`) unless it is a compiler auxiliary (`isCompilerAuxTheorem`). -/
def formalRfcTheoremViolation? (env : Environment) (modOf : Name → Name) (rfc imp : String)
    (t : Name) (ty : Expr) : Option String :=
  if isCompilerAuxTheorem env t then none
  else
    match formalRfcCliStmtCheck env modOf rfc imp ty with
    | .ok _ => none
    | .error err => some s!"theorem {t} does not state a formal RFC CLI template instantiation: {err}"

/-- Statement-level dependencies of `ci`: type (with `optParam` defaults erased), plus definition
    body and inductive constructors for non-theorem constants (never descending into `.thmInfo`
    proof terms). -/
private def stmtDepsOf (ci : ConstantInfo) : Array Name := Id.run do
  let mut deps := (stripOptParams ci.type).getUsedConstants
  if !(ci matches .thmInfo _) then
    if let some v := ci.value? (allowOpaque := true) then
      deps := deps ++ v.getUsedConstants
    if let .inductInfo iv := ci then
      deps := deps ++ iv.ctors.toArray
  return deps

/-- Find the shortest blame path from `roots` to any constant declared outside
    `isAllowedTheoremsStmtModule`, updating `cleanCache` with verified-clean subgraphs so module
    batches walk each `Spec` definition at most once. -/
private def findUntrustedStmtPath (env : Environment) (roots : Array Name)
    (cleanCache : Std.HashSet Name) : Option (Array Name) × Std.HashSet Name := Id.run do
  let mut parent : Std.HashMap Name (Option Name) := {}
  let mut queue : Array Name := #[]
  for r in roots do
    if !cleanCache.contains r && !parent.contains r then
      parent := parent.insert r none
      queue := queue.push r
  let mut i : Nat := 0
  let mut hit : Option Name := none
  while h : i < queue.size do
    let cur := queue[i]
    i := i + 1
    let defMod := definingModuleOf env cur
    if !isAllowedTheoremsStmtModule defMod then
      hit := some cur
      break
    if let some ci := env.find? cur then
      for d in stmtDepsOf ci do
        if !cleanCache.contains d && !parent.contains d then
          parent := parent.insert d (some cur)
          queue := queue.push d
  match hit with
  | none =>
    let mut cache := cleanCache
    for c in queue do
      cache := cache.insert c
    return (none, cache)
  | some target =>
    let mut path : Array Name := #[target]
    let mut cur := target
    for _ in [:queue.size + 1] do
      match parent.getD cur none with
      | some p =>
        path := path.push p
        cur := p
      | none => break
    return (some path.reverse, cleanCache)

/-- Audit `thms` and all built-in non-alloc bundles in a single memoized pass. When
    `enforceAllStmtPurity` is `true` (or automatically for every theorem declared in a
    `Theorems` module), also verifies that every constant in `(stripOptParams ci.type)` and
    its transitive definition closure belongs to `isAllowedTheoremsStmtModule`. -/
def auditTrustedClosures (thms : Array Name) (enforceAllStmtPurity : Bool := false)
    (modNameFn : Name → Name := id) (cliMods : Array Name := #[]) :
    CoreM (Array String × Array TheoremClosure) := do
  let env := (← getEnv).setExporting false
  let tidx := buildTrustedIndex env
  let modWords := (tidx.modNames.size + 63) / 64
  let go : FastClosureM (Array String × Array TheoremClosure) := do
    let mut bundleErrors : Array String := formalRfcPackagesViolations env cliMods modNameFn
    for b in nonAllocBundleConsts do
      let sum ← summaryOfConst env tidx b
      let leaked := decodeBits tidx.names (andBits sum.full tidx.allocMask)
      unless leaked.isEmpty do
        let pathStr := match findBlamePath env #[b] (isAllocConst env) with
          | some p => formatPath p
          | none => s!"{b} -> {leaked.toList}"
        bundleErrors := bundleErrors.push
          s!"non-alloc bundle {b} reaches {allocModName}: {pathStr}"
    let mut records : Array TheoremClosure := #[]
    let mut stmtCleanCache : Std.HashSet Name := {}
    for t in thms do
      let some ci := env.find? t
        | throwError "#trusted_closure: unknown constant {t}"
      let strippedType := stripOptParams ci.type
      let sum ← summaryOfExpr env tidx strippedType
      let nonAllocUsed := nonAllocBundleConsts.filter fun b =>
        match tidx.idxOf[b]? with
        | some k => (sum.entry.getD (k / 64) 0 &&& ((1 : UInt64) <<< (k % 64).toUInt64)) != 0
        | none => false
      let allocEntryUsed := allocCapableEntryConsts.filter fun b =>
        match tidx.idxOf[b]? with
        | some k => (sum.entry.getD (k / 64) 0 &&& ((1 : UInt64) <<< (k % 64).toUInt64)) != 0
        | none => false
      let trustedConsts := decodeBits tidx.names sum.full
      let mut modBits := emptyBits modWords
      for wi in [:sum.full.size] do
        let word := sum.full[wi]!
        if word != 0 then
          for bi in [:64] do
            if (word &&& ((1 : UInt64) <<< bi.toUInt64)) != 0 then
              let k := wi * 64 + bi
              if h : k < tidx.constModIdx.size then
                modBits := setBit modBits tidx.constModIdx[k]
      let trustedMods := decodeBits tidx.modNames modBits
      let allocConsts := decodeBits tidx.names (andBits sum.full tidx.allocMask)
      let allocViolation? :=
        if !nonAllocUsed.isEmpty && allocEntryUsed.isEmpty && !allocConsts.isEmpty then
          let pathStr := match findBlamePath env strippedType.getUsedConstants (isAllocConst env) with
            | some p => s!"{t} -> {formatPath p}"
            | none => s!"{t} -> {allocConsts.toList}"
          some s!"theorem {t} uses non-alloc bundle {nonAllocUsed.toList} but its statement closure reaches {allocModName} ({allocConsts.toList}) via {pathStr}"
        else
          none
      let defMod := modNameFn (definingModuleOf env t)
      let stmtViolation? ←
        if enforceAllStmtPurity || isTheoremsModule defMod then
          let (badPath?, cache') :=
            findUntrustedStmtPath env strippedType.getUsedConstants stmtCleanCache
          stmtCleanCache := cache'
          match badPath? with
          | some p =>
            let badConst := p.back? |>.getD t
            let badMod := definingModuleOf env badConst
            pure <| some
              s!"theorem {t} (in {defMod}) references non-Spec constant {badConst} (from {badMod}) in its statement type via {t} -> {formatPath p}"
          | none => pure none
        else
          pure none
      -- A formal RFC implementation's `Theorems` theorem states a CLI template instantiation.
      let cliViolation? :=
        match formalRfcImplModule? defMod with
        | some (rfc, imp, "Theorems") =>
          (formalRfcTheoremViolation? env (fun c => modNameFn (definingModuleOf env c)) rfc imp t
            ci.type).map (s!"{·} (in {defMod})")
        | _ => none
      let violations := #[allocViolation?, stmtViolation?, cliViolation?].filterMap id
      let violation? := if violations.isEmpty then none else some ("; ".intercalate violations.toList)
      records := records.push {
        thm := t
        defMod := defMod
        entryBundles := nonAllocUsed ++ allocEntryUsed
        trustedModules := trustedMods
        trustedConsts := trustedConsts
        allocConsts := allocConsts
        violation? := violation?
      }
    return (bundleErrors, records)
  let (res, _) ← go.run {}
  return res

/-- Whether `m` is a specification or `Theorems` module whose top-level theorems should
    always have their full `Arm64.Trusted.*` closure printed in module-level audit reports. -/
private def isSpecOrTheoremsModule (m : Name) : Bool :=
  isTheoremsModule m ||
    (m.components.map Name.toString).any (fun seg => seg == "Spec" || seg.startsWith "Spec")

/-- Render the trusted-closure report for `scope`. When `printAll` is `false` (module-wide CI runs),
    full per-theorem closures are printed for all top/spec theorems (`*.Spec*`, `*Theorems*`) and
    any violating theorems, while all theorems in `records` are still strictly audited. -/
def renderClosureReport (scope : String) (bundleErrors : Array String)
    (records : Array TheoremClosure) (printAll : Bool := true) : String := Id.run do
  let violations := bundleErrors ++ records.filterMap (·.violation?)
  let allocCount := records.filter (!·.allocConsts.isEmpty) |>.size
  let mut lines := #[
    s!"[trusted_closure] scope={scope} theorems={records.size} " ++
    s!"without_alloc={records.size - allocCount} with_alloc={allocCount} " ++
    s!"violations={violations.size}"
  ]
  for r in records do
    let isTop := printAll || r.violation?.isSome ||
      isSpecOrTheoremsModule r.defMod || isSpecOrTheoremsModule r.thm.getPrefix
    if isTop then
      let modsStr := ", ".intercalate (r.trustedModules.toList.map Name.toString)
      let constsStr := ", ".intercalate (r.trustedConsts.toList.map Name.toString)
      lines := lines.push
        (s!"[trusted_closure] {r.thm} modules=[{modsStr}] " ++
         s!"trusted_consts({r.trustedConsts.size})=[{constsStr}]")
  for v in violations do
    lines := lines.push s!"[trusted_closure] ERROR: {v}"
  return "\n".intercalate lines.toList

/-- Run `#trusted_closure` over `thms` and log or fail when `strict` and any violation occurs. -/
def runClosureCheck (scope : String) (thms : Array Name) (strict : Bool)
    (printAll : Bool := true) (enforceAllStmtPurity : Bool := false)
    (modNameFn : Name → Name := id) (cliMods : Array Name := #[]) : CommandElabM Unit := do
  let (bundleErrors, records) ←
    liftCoreM (auditTrustedClosures thms enforceAllStmtPurity modNameFn cliMods)
  let msg := renderClosureReport scope bundleErrors records printAll
  let hasViolation := !bundleErrors.isEmpty || records.any (·.violation?.isSome)
  if strict && hasViolation then
    throwError msg
  else
    logInfo msg

private def isUserFacing (c : Name) : Bool :=
  let u := privateToUserName c
  !u.isInternalDetail && !u.isInternal

private def isFixtureModule (m : Name) : Bool :=
  m.toString.endsWith ".Fixtures"

/-- Theorems declared in imported modules satisfying `sel`. In `Theorems` modules, neither
    `.Fixtures` module suffixes nor `_`-prefixed internal theorem names are skipped. -/
def importedTheoremsWhere (env : Environment) (sel : Name → Bool)
    (modNameFn : Name → Name := id) : Array Name := Id.run do
  let mods := env.header.moduleNames
  let mut thms := #[]
  for h : idx in [:mods.size] do
    let m := modNameFn mods[idx]
    let inTheorems := isTheoremsModule m
    if sel m && (inTheorems || !isFixtureModule m) then
      if h2 : idx < env.header.moduleData.size then
        for ci in env.header.moduleData[idx].constants do
          if ci matches .thmInfo _ then
            if inTheorems || isUserFacing ci.name then
              thms := thms.push ci.name
  return thms

/-- `#trusted_closure thm...` prints each theorem statement's `Arm64.Trusted.*` closure;
    `#trusted_closure! thm...` fails if any non-alloc theorem reaches `Arm64.Trusted.Syscalls.Alloc`. -/
syntax (name := trustedClosureCmd) "#trusted_closure" ("!")? (ppSpace ident)+ : command

@[command_elab trustedClosureCmd] def elabTrustedClosure : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let ids := stx[2].getArgs
  let mut thms := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    thms := thms.push n
  runClosureCheck "explicit" thms strict (printAll := true)

/-- `#trusted_closure_modules P` audits every user-facing theorem declared in an imported module
    whose name starts with `P`; `!` fails on any `Alloc` leak. -/
syntax (name := trustedClosureModulesCmd)
  "#trusted_closure_modules" ("!")? ppSpace ident : command

@[command_elab trustedClosureModulesCmd] def elabTrustedClosureModules : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let pfx := stx[2].getId
  let env ← getEnv
  runClosureCheck pfx.toString (importedTheoremsWhere env pfx.isPrefixOf) strict
    (printAll := false) (cliMods := env.header.moduleNames.filter pfx.isPrefixOf)

/-- `#trusted_closure_module M...` audits every user-facing theorem declared in the imported modules
    `M...` (excluding submodules); `!` fails on any `Alloc` leak. -/
syntax (name := trustedClosureModuleCmd)
  "#trusted_closure_module" ("!")? (ppSpace ident)+ : command

@[command_elab trustedClosureModuleCmd] def elabTrustedClosureModule : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let ms := stx[2].getArgs.map (·.getId)
  let env ← getEnv
  for m in ms do
    unless env.header.moduleNames.contains m do
      throwError "#trusted_closure_module: module {m} is not imported"
  let scope := if h : ms.size = 1 then s!"module {ms[0]}" else s!"modules({ms.size})"
  runClosureCheck scope (importedTheoremsWhere env ms.contains) strict (printAll := false)
    (cliMods := ms)

/-- `#trusted_closure_theorems thm...` runs `#trusted_closure` with `Theorems` statement-purity
    enforcement enabled regardless of the declaring module (`!` fails closed). -/
syntax (name := trustedClosureTheoremsCmd)
  "#trusted_closure_theorems" ("!")? (ppSpace ident)+ : command

@[command_elab trustedClosureTheoremsCmd] def elabTrustedClosureTheorems : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let ids := stx[2].getArgs
  let mut thms := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    thms := thms.push n
  runClosureCheck "theorems" thms strict (printAll := true) (enforceAllStmtPurity := true)

/-! ## Formal RFC CLI statement test commands -/

/-- Declaring module of `c` for the formal RFC test commands. An imported constant keeps its real
    module. A constant of the current file is placed in `FormalRfcs.<rfc>.<imp>.Spec.Top` if it is
    listed in `implDecls` or named `FormalRfcs.<rfc>.<imp>.*`, in `FormalRfcs.<R>.Spec.Top` if it is
    named `FormalRfcs.<R>.*`, and in the current module otherwise. -/
def formalRfcTestModOf (env : Environment) (rfc imp : String) (implDecls : Array Name)
    (c : Name) : Name :=
  if (env.getModuleIdxFor? c).isSome then definingModuleOf env c
  else
    let implNs : Name := ((`FormalRfcs).str rfc).str imp
    if implDecls.contains c || implNs.isPrefixOf c then (implNs.str "Spec").str "Top"
    else
      match c.components.map Name.toString with
      | "FormalRfcs" :: r :: _ :: _ => (((`FormalRfcs).str r).str "Spec").str "Top"
      | _ => env.mainModule

/-- `#test_formal_rfc_cli_stmt Rfc Impl [impl_spec c...] t` elaborates the `Prop` `t` and runs
    `formalRfcCliStmtCheck` for `FormalRfcs.Rfc.Impl` on it, with the current file's constants
    placed by `formalRfcTestModOf`. Logs `ok <template>` or fails with the violation. -/
syntax (name := testFormalRfcCliStmtCmd)
  "#test_formal_rfc_cli_stmt " ident ident ("impl_spec" "[" ident,* "]")? term : command

@[command_elab testFormalRfcCliStmtCmd] def elabTestFormalRfcCliStmt : CommandElab := fun stx => do
  let rfc := stx[1].getId.toString
  let imp := stx[2].getId.toString
  let implDecls ← stx[3].getOptional?.elim (pure #[]) fun s =>
    s[2].getSepArgs.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let e ← liftTermElabM do
    let e ← Term.elabType stx[4]
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let env ← getEnv
  match formalRfcCliStmtCheck env (formalRfcTestModOf env rfc imp implDecls) rfc imp e with
  | .ok t => logInfo m!"ok {t}"
  | .error err => throwError "formal RFC CLI statement check failed: {err}"

/-- `#test_formal_rfc_theorem Rfc Impl t...` runs the per-theorem check of a formal RFC
    implementation's `Theorems` (`formalRfcTheoremViolation?`) on each theorem `t`, with the current
    file's constants placed by `formalRfcTestModOf`. Logs `ok` (or `skipped` for a compiler
    auxiliary) per theorem, or fails with the violations. -/
syntax (name := testFormalRfcTheoremCmd)
  "#test_formal_rfc_theorem " ident ident (ppSpace ident)+ : command

@[command_elab testFormalRfcTheoremCmd] def elabTestFormalRfcTheorem : CommandElab := fun stx => do
  let rfc := stx[1].getId.toString
  let imp := stx[2].getId.toString
  let mut errs := #[]
  for id in stx[3].getArgs do
    let t ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let env ← getEnv
    let some ci := env.find? t | throwError "unknown constant {t}"
    if isCompilerAuxTheorem env t then
      logInfo m!"skipped {t} (compiler auxiliary)"
    else
      match formalRfcTheoremViolation? env (formalRfcTestModOf env rfc imp #[]) rfc imp t ci.type with
      | none => logInfo m!"ok {t}"
      | some v => errs := errs.push v
  unless errs.isEmpty do
    throwError "formal RFC theorem check failed: {"; ".intercalate errs.toList}"

/-- `#test_formal_rfc_package Rfc Impl` runs `formalRfcPackageViolations` for `FormalRfcs.Rfc.Impl`,
    with the current file's constants placed by `formalRfcTestModOf`. Logs `ok` or fails with the
    violations. -/
syntax (name := testFormalRfcPackageCmd) "#test_formal_rfc_package " ident ident : command

@[command_elab testFormalRfcPackageCmd] def elabTestFormalRfcPackage : CommandElab := fun stx => do
  let rfc := stx[1].getId.toString
  let imp := stx[2].getId.toString
  let env ← getEnv
  let vs := formalRfcPackageViolations env (formalRfcTestModOf env rfc imp #[]) rfc imp
  if vs.isEmpty then logInfo "ok"
  else throwError "formal RFC package check failed: {"; ".intercalate vs.toList}"

end ProofLib.TrustedClosure

end
