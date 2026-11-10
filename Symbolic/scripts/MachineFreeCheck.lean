/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean

/-!
# Transitive Constant-Cone Machine-Free Checker

Checks whether target declarations are machine-free with respect to defining-module deny lists
(`Symbolic/scripts/machine_free_deny*.txt`) and exact per-constant allow-lists
(`Symbolic/scripts/machine_free_allow*.txt`). Traverses outgoing dependencies across declaration
types, values, proof terms, inductive/recursor rules, and primitive `Expr.proj` projections,
attributing compiler-generated and `_simp_` auxiliary lemmas to their parent declarations and
failing closed on unattributed local constants. Supports per-root cone audits, `--root-report`
type/bridge/axiom/residual checks, and `--criterion` / `--emit-proofdeps` / `--check-proofdeps`
least-fixed-point proof-dependency taint analysis over the default Lake target closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MachineFreeCheck

open Lean System

inductive DenyPattern where
  | exact (modName : String)
  | prefixWildcard (modPrefix : String)
  deriving Repr, Inhabited, BEq

def DenyPattern.matchesMod (pat : DenyPattern) (modStr : String) : Bool :=
  match pat with
  | .exact m => modStr == m
  | .prefixWildcard p => modStr == p || modStr.startsWith (p ++ ".")

def DenyPattern.render (pat : DenyPattern) : String :=
  match pat with
  | .exact m => m
  | .prefixWildcard p => p ++ ".*"

def validModSegments (s : String) : Bool :=
  let segs := s.splitOn "."
  !s.isEmpty && !segs.isEmpty && segs.all (fun seg =>
    !seg.isEmpty && !seg.any Char.isWhitespace)

def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc seg =>
    if !seg.isEmpty && seg.all Char.isDigit then
      match seg.toNat? with
      | some n => Name.mkNum acc n
      | none   => Name.mkStr acc seg
    else
      Name.mkStr acc seg) Name.anonymous

def dispConst (c : Name) : String :=
  match Lean.privateToUserName? c with
  | some u => s!"{u} [priv]"
  | none   => c.toString

def sortNames (s : NameSet) : Array Name :=
  let keyed := s.toArray.map (fun n => (n.toString, n))
  (keyed.qsort (fun a b => a.1 < b.1)).map (·.2)

/-- Append `v` to `m[k]` in amortized `O(1)` time by erasing `k` before `Array.push` so `arr` keeps
exclusive ownership (`rc == 1`). -/
@[inline] def pushMapArr {α β : Type} [BEq α] [Hashable α]
    (m : Std.HashMap α (Array β)) (k : α) (v : β) : Std.HashMap α (Array β) :=
  match m[k]? with
  | none => m.insert k #[v]
  | some arr =>
      let m' := m.erase k
      m'.insert k (arr.push v)

def parseGroupHeader? (code : String) : Option String := do
  guard (code.startsWith "[group " && code.endsWith "]")
  let inner := ((code.drop 7).dropEnd 1).trimAscii.toString
  guard (!inner.isEmpty && !inner.any Char.isWhitespace && !inner.contains '[' && !inner.contains ']')
  return inner

/-- Load defining-module deny patterns from `--deny-file` paths, supporting `[group <id>]` sections
and `--exclude-deny-group <id>`. Fails closed on malformed headers, ungrouped entries before the
first group, unknown excluded groups, or an empty resulting deny set. -/
def loadDenyPatternsFromFiles (paths : Array FilePath) (excludedGroups : Array String) :
    IO (Array DenyPattern) := do
  if paths.isEmpty then
    throw <| IO.userError "no --deny-file specified (fail-closed)"
  let excludedSet : Std.HashSet String := excludedGroups.foldl (·.insert ·) {}
  let mut seenGroups : Std.HashSet String := {}
  let mut out : Array DenyPattern := #[]
  for path in paths do
    unless (← path.pathExists) do
      throw <| IO.userError s!"deny file does not exist: {path}"
    let raw ← IO.FS.readFile path
    let mut lineNo : Nat := 0
    let mut currentGroup : Option String := none
    let mut sawUngrouped : Bool := false
    let mut ungroupedLine : Nat := 0
    let mut ungroupedCode : String := ""
    for rawLine in raw.splitOn "\n" do
      lineNo := lineNo + 1
      let code := ((rawLine.splitOn "#").head!).trimAscii.toString
      if code.isEmpty then continue
      if code.startsWith "[" then
        match parseGroupHeader? code with
        | some gid =>
            if sawUngrouped then
              throw <| IO.userError s!"{path}:{ungroupedLine}: ungrouped pattern '{ungroupedCode}' precedes first [group {gid}]"
            currentGroup := some gid
            seenGroups := seenGroups.insert gid
        | none =>
            throw <| IO.userError s!"{path}:{lineNo}: malformed [group <id>] header '{code}'"
        continue
      if currentGroup.isNone && !sawUngrouped then
        sawUngrouped := true
        ungroupedLine := lineNo
        ungroupedCode := code
      let skip := match currentGroup with
        | some gid => excludedSet.contains gid
        | none     => false
      let pat ←
        if code.endsWith ".*" then
          let pre := (code.dropEnd 2).toString
          if !validModSegments pre then
            throw <| IO.userError s!"{path}:{lineNo}: invalid wildcard pattern '{code}'"
          else
            pure (DenyPattern.prefixWildcard pre)
        else
          if !(validModSegments code && !code.contains '*') then
            throw <| IO.userError s!"{path}:{lineNo}: invalid module pattern '{code}'"
          else
            pure (DenyPattern.exact code)
      unless skip do
        unless out.contains pat do
          out := out.push pat
  for gid in excludedGroups do
    unless seenGroups.contains gid do
      throw <| IO.userError s!"excluded deny group '{gid}' not found in any --deny-file (seen groups: {seenGroups.toArray})"
  if out.isEmpty then
    throw <| IO.userError s!"deny list is empty (fail-closed)"
  return out

def validExactConstSyntax (s : String) : Bool :=
  !s.isEmpty &&
  !s.startsWith "." &&
  !s.endsWith "." &&
  !s.contains '*' &&
  !s.contains '?' &&
  !s.contains '/' &&
  validModSegments s

def loadAllowMapFromFiles (paths : Array FilePath) (denyPats : Array DenyPattern) :
    IO (Std.HashMap Name String) := do
  let mut out : Std.HashMap Name String := {}
  for path in paths do
    unless (← path.pathExists) do
      throw <| IO.userError s!"allow file does not exist: {path}"
    let raw ← IO.FS.readFile path
    let mut lineNo : Nat := 0
    let mut inHeader : Bool := true
    let mut reqTag? : Option String := none
    for rawLine in raw.splitOn "\n" do
      lineNo := lineNo + 1
      let trimmed := rawLine.trimAscii.toString
      if trimmed.isEmpty then continue
      if trimmed.startsWith "#" then
        let rest := (trimmed.drop 1).trimAscii.toString
        if rest.startsWith "require-tag:" then
          unless inHeader do
            throw <| IO.userError s!"{path}:{lineNo}: `# require-tag:` must appear in leading header"
          let tag := (rest.drop 12).trimAscii.toString
          if tag.isEmpty || tag.any Char.isWhitespace then
            throw <| IO.userError s!"{path}:{lineNo}: malformed `# require-tag:` directive '{trimmed}'"
          if let some prev := reqTag? then
            if prev != tag then
              throw <| IO.userError s!"{path}:{lineNo}: conflicting `# require-tag:` ('{prev}' vs '{tag}')"
          reqTag? := some tag
        continue
      inHeader := false
      let parts := trimmed.splitOn ":"
      if parts.length < 2 then
        throw <| IO.userError s!"{path}:{lineNo}: allow entry must be '<FullConstName> : <reason>', got '{trimmed}'"
      let cStr := parts[0]!.trimAscii.toString
      let reason := (String.intercalate ":" (parts.drop 1)).trimAscii.toString
      unless validExactConstSyntax cStr && !reason.isEmpty do
        throw <| IO.userError s!"{path}:{lineNo}: invalid allow entry '{cStr}' (exact constant name and non-empty reason required; wildcards/prefixes forbidden)"
      if let some tag := reqTag? then
        unless reason.startsWith tag && !((reason.drop tag.length).trimAscii.toString.isEmpty) do
          throw <| IO.userError s!"{path}:{lineNo}: allow entry '{cStr}' must start reason with required tag '{tag}' followed by non-empty explanation"
      if !(cStr.contains '.') then
        throw <| IO.userError s!"{path}:{lineNo}: allow entry '{cStr}' looks like a top-level package/prefix, not a qualified constant"
      for dp in denyPats do
        match dp with
        | .exact modStr =>
            if cStr == modStr then
              throw <| IO.userError s!"{path}:{lineNo}: allow entry '{cStr}' matches denied module '{modStr}'; module-level allow entries are forbidden"
        | .prefixWildcard pre =>
            if cStr == pre then
              throw <| IO.userError s!"{path}:{lineNo}: allow entry '{cStr}' matches denied module prefix '{pre}.*'; prefix allow entries are forbidden"
      let parsed := parseName cStr
      if out.contains parsed then
        throw <| IO.userError s!"{path}:{lineNo}: duplicate allow entry '{cStr}'"
      out := out.insert parsed reason
  return out

def loadSeedBatchesFile (path : FilePath) : IO (Array (Array Name)) := do
  unless (← path.pathExists) do
    throw <| IO.userError s!"module list file does not exist: {path}"
  let raw ← IO.FS.readFile path
  let mut batches : Array (Array Name) := #[]
  let mut lineNo : Nat := 0
  for rawLine in raw.splitOn "\n" do
    lineNo := lineNo + 1
    let code := ((rawLine.splitOn "#").head!).trimAscii.toString
    if code.isEmpty then continue
    let mut batchSeen : Std.HashSet Name := {}
    let mut batch : Array Name := #[]
    for rawPart in code.splitOn "," do
      let modStr := rawPart.trimAscii.toString
      if modStr.isEmpty then continue
      unless validModSegments modStr && !modStr.contains '*' do
        throw <| IO.userError s!"{path}:{lineNo}: invalid exact module name '{modStr}'"
      let m := parseName modStr
      unless batchSeen.contains m do
        batchSeen := batchSeen.insert m
        batch := batch.push m
    if !batch.isEmpty then
      batches := batches.push batch
  if batches.isEmpty then
    throw <| IO.userError s!"{path}: module list is empty (fail-closed)"
  return batches

def loadExactModSetFile (path : FilePath) (requireNonEmpty : Bool) : IO (Std.HashSet Name) := do
  unless (← path.pathExists) do
    throw <| IO.userError s!"module list file does not exist: {path}"
  let raw ← IO.FS.readFile path
  let mut out : Std.HashSet Name := {}
  let mut lineNo : Nat := 0
  for rawLine in raw.splitOn "\n" do
    lineNo := lineNo + 1
    let code := ((rawLine.splitOn "#").head!).trimAscii.toString
    if code.isEmpty then continue
    for rawPart in code.splitOn "," do
      let modStr := rawPart.trimAscii.toString
      if modStr.isEmpty then continue
      unless validModSegments modStr && !modStr.contains '*' do
        throw <| IO.userError s!"{path}:{lineNo}: invalid exact module name '{modStr}'"
      out := out.insert (parseName modStr)
  if requireNonEmpty && out.isEmpty then
    throw <| IO.userError s!"{path}: module list is empty (fail-closed)"
  return out

def loadExactModArrayFile (path : FilePath) : IO (Array Name) := do
  let s ← loadExactModSetFile path true
  return s.toArray.qsort (fun a b => a.toString < b.toString)

/-- Reject allow entries that name a module, module prefix, or namespace prefix in `env` rather than
an exact constant declaration. -/
def validateAllowMapInEnv (env : Environment) (allowMap : Std.HashMap Name String) : IO Unit := do
  if allowMap.isEmpty then return
  for (allowName, _) in allowMap.toArray do
    if env.contains allowName then continue
    let allowStr := allowName.toString
    let allowDot := allowStr ++ "."
    for modName in env.header.moduleNames do
      let modStr := modName.toString
      if modName == allowName || modStr.startsWith allowDot then
        throw <| IO.userError s!"allow entry '{allowStr}' names a module or module prefix ('{modStr}'), not a constant"
    for md in env.header.moduleData do
      for k in md.constNames do
        let u := (Lean.privateToUserName? k).getD k
        if allowName != u && allowName.isPrefixOf u then
          throw <| IO.userError s!"allow entry '{allowStr}' is a namespace/prefix of '{u}', not an exact constant name"

structure AllowBatchValidation where
  foundConsts : Std.HashSet Name := {}
  badErrors   : Std.HashMap Name String := {}
  deriving Inhabited

def recordAllowMapInBatchEnv (st : AllowBatchValidation) (env : Environment)
    (allowMap : Std.HashMap Name String) : AllowBatchValidation := Id.run do
  if allowMap.isEmpty then return st
  let mut found := st.foundConsts
  let mut errs := st.badErrors
  for (allowName, _) in allowMap.toArray do
    if found.contains allowName then continue
    if env.contains allowName then
      found := found.insert allowName
      errs := errs.erase allowName
    else if !errs.contains allowName then
      let allowStr := allowName.toString
      let allowDot := allowStr ++ "."
      let mut hit? : Option String := none
      for modName in env.header.moduleNames do
        if hit?.isNone then
          let modStr := modName.toString
          if modName == allowName || modStr.startsWith allowDot then
            hit? := some s!"allow entry '{allowStr}' names a module or module prefix ('{modStr}'), not a constant"
      if hit?.isNone then
        for md in env.header.moduleData do
          if hit?.isNone then
            for k in md.constNames do
              if hit?.isNone then
                let u := (Lean.privateToUserName? k).getD k
                if allowName != u && allowName.isPrefixOf u then
                  hit? := some s!"allow entry '{allowStr}' is a namespace/prefix of '{u}', not an exact constant name"
      if let some msg := hit? then
        errs := errs.insert allowName msg
  return { foundConsts := found, badErrors := errs }

def finalizeAllowBatchValidation (st : AllowBatchValidation)
    (allowMap : Std.HashMap Name String) : IO Unit := do
  let sortedKeys := (allowMap.toArray.map (·.1)).qsort (fun a b => a.toString < b.toString)
  for allowName in sortedKeys do
    unless st.foundConsts.contains allowName do
      if let some msg := st.badErrors[allowName]? then
        throw <| IO.userError msg

def isCoreModName (m : Name) : Bool :=
  let s := m.toString
  s == "Init" || s.startsWith "Init." ||
  s == "Std" || s.startsWith "Std." ||
  s == "Lean" || s.startsWith "Lean." ||
  s == "Mathlib" || s.startsWith "Mathlib." ||
  s == "Batteries" || s.startsWith "Batteries." ||
  s == "Qq" || s.startsWith "Qq." ||
  s == "Aesop" || s.startsWith "Aesop." ||
  s == "ProofWidgets" || s.startsWith "ProofWidgets." ||
  s == "Plausible" || s.startsWith "Plausible." ||
  s == "ImportGraph" || s.startsWith "ImportGraph." ||
  s == "Cli" || s.startsWith "Cli."

def isDigitsNonEmpty (s : String) : Bool :=
  !s.isEmpty && s.all Char.isDigit

def isGeneratedChildSeg (seg : String) : Bool :=
  seg == "eq_def" || seg == "eq_unfold" || seg == "induct" || seg == "fun_cases" ||
  seg == "mutual_induct" || seg == "congr_simp" || seg == "splitter" ||
  (seg.startsWith "eq_" && isDigitsNonEmpty (seg.drop 3).toString) ||
  (seg.startsWith "match_" && isDigitsNonEmpty (seg.drop 6).toString) ||
  (seg.startsWith "proof_" && isDigitsNonEmpty (seg.drop 6).toString) ||
  (seg.startsWith "_proof_" && isDigitsNonEmpty (seg.drop 7).toString)

/-- For compiler-synthesized declarations (`(declRangeExt.find? env c).isNone`), strip trailing
generated suffixes (`eq_<n>`, `eq_def`, `induct`, `match_<n>`, `proof_<n>`, etc.) while the parent
exists in `env`. Checks suffix syntax before consulting `declRangeExt`. -/
def generatedAncestor? (env : Environment) (c : Name) : Option Name := Id.run do
  let okFirst := match c with
    | .str _ seg => isGeneratedChildSeg seg
    | _ => false
  if !okFirst then return none
  let mut cur := c
  while true do
    match cur with
    | .str p seg =>
        if isGeneratedChildSeg seg && env.contains p then
          cur := p
        else
          break
    | _ => break
  if cur == c then return none
  if (Lean.declRangeExt.find? env c).isSome then return none
  return some cur

def rawModuleOf? (env : Environment) (c : Name) : IO (Option Name) := do
  match env.getModuleIdxFor? c with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => return some m
      | none   => throw <| IO.userError s!"moduleIdx {idx.toNat} out of bounds for {c}"
  | none => return none

def isSimpAuxSeg (seg : String) : Bool :=
  seg.startsWith "_simp_" && isDigitsNonEmpty (seg.drop 6).toString

/-- Return the parent declaration of a compiler-synthesized `<parent>._simp_<digits>` theorem
emitted by `mkSimpTheoremFromConst` (when `c` has no source range and `parent` exists in `env`). -/
def simpAuxParent? (env : Environment) (c : Name) : Option Name :=
  let u := (Lean.privateToUserName? c).getD c
  match u with
  | .str userParent seg =>
      if !isSimpAuxSeg seg then
        none
      else if (Lean.declRangeExt.find? env c).isSome then
        none
      else
        match env.find? c with
        | some (.thmInfo _) =>
            if env.contains userParent then
              some userParent
            else
              match c with
              | .str rawParent rawSeg =>
                  if isSimpAuxSeg rawSeg && env.contains rawParent then some rawParent else none
              | _ => none
        | _ => none
  | _ => none

/-- Resolve the defining module of `c`, attributing `_simp_<digits>` and non-core generated
auxiliaries to their parent declarations and failing closed with `E3_LOCAL_CONST` when `none`
outside `--gk-control`. -/
partial def definingModWithPolicy? (env : Environment) (allowLocalControl : Bool) (c : Name) :
    IO (Option Name) := do
  let rawSelf ← rawModuleOf? env c
  if rawSelf.isSome then
    if let some simpParent := simpAuxParent? env c then
      return (← definingModWithPolicy? env allowLocalControl simpParent)
  if let some anc := generatedAncestor? env c then
    if let some ancMod ← rawModuleOf? env anc then
      if !isCoreModName ancMod && rawSelf != some ancMod then
        return some ancMod
  match rawSelf with
  | some m => return some m
  | none =>
      match c with
      | .str parent seg =>
          if seg.startsWith "_raw_proj_" then
            return (← definingModWithPolicy? env allowLocalControl parent)
          else
            pure ()
      | _ => pure ()
      if allowLocalControl then
        if (`Arm64.TestStandIn).isPrefixOf c then
          return some `Arm64.Trusted.ISA.State
        return none
      else
        throw <| IO.userError s!"E3_LOCAL_CONST:{dispConst c}"

def modLabel (m? : Option Name) : String :=
  match m? with
  | some m => m.toString
  | none   => "<local>"

def isModDenied (pats : Array DenyPattern) (m? : Option Name) : Bool :=
  match m? with
  | none   => false
  | some m =>
      let ms := m.toString
      pats.any (fun p => p.matchesMod ms)

/-- True on forbidden projections, recursors, and auxiliaries of inert environment types (`Oracle`,
`Timespec`, `AuxvConfig`, `ProcessInit`, and unsigned `ProcessInputs` fields). Only the type
constructors, `.mk`, and `ProcessInputs.{files,dirs,stdin}` are permitted. -/
def isForbiddenInertConst (c : Name) : Bool :=
  let u := (Lean.privateToUserName? c).getD c
  if (`Arm64.Oracle).isPrefixOf u then
    u != `Arm64.Oracle && u != `Arm64.Oracle.mk
  else if (`Arm64.Timespec).isPrefixOf u then
    u != `Arm64.Timespec && u != `Arm64.Timespec.mk
  else if (`Arm64.Process.AuxvConfig).isPrefixOf u then
    u != `Arm64.Process.AuxvConfig && u != `Arm64.Process.AuxvConfig.mk
  else if (`Arm64.Process.ProcessInit).isPrefixOf u then
    u != `Arm64.Process.ProcessInit && u != `Arm64.Process.ProcessInit.mk
  else if (`Arm64.Process.ProcessInputs).isPrefixOf u then
    u != `Arm64.Process.ProcessInputs &&
    u != `Arm64.Process.ProcessInputs.mk &&
    u != `Arm64.Process.ProcessInputs.files &&
    u != `Arm64.Process.ProcessInputs.dirs &&
    u != `Arm64.Process.ProcessInputs.stdin
  else
    false

/-- Rust heap-layout ghost type prefixes forbidden in audited root types. -/
def a2GhostRoots : Array Name := #[
  `CryptoVerification.LibsignalSessionRepr.VecPin,
  `CryptoVerification.LibsignalSessionRepr.VecGhost,
  `CryptoVerification.LibsignalSessionRepr.MessageKeyGhost,
  `CryptoVerification.LibsignalSessionRepr.ChainGhost,
  `CryptoVerification.LibsignalSessionRepr.SenderChainGhost,
  `CryptoVerification.LibsignalSessionRepr.TailVecGhost,
  `CryptoVerification.LibsignalSessionRepr.SessionGhost,
  `CryptoVerification.LibsignalTripleRatchetRepr.VecPin,
  `CryptoVerification.LibsignalTripleRatchetRepr.VecGhost,
  `CryptoVerification.LibsignalTripleRatchetRepr.MessageKeyGhost,
  `CryptoVerification.LibsignalTripleRatchetRepr.ChainGhost,
  `CryptoVerification.LibsignalTripleRatchetRepr.SenderChainGhost,
  `CryptoVerification.LibsignalTripleRatchetRepr.TailVecGhost,
  `CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost,
  `CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost
]

def isA2HeapGhostConst (c : Name) : Bool :=
  let u := (Lean.privateToUserName? c).getD c
  a2GhostRoots.any (fun g => g == u || g.isPrefixOf u)

def std3Axioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- True if the name has `bv_decide` certificate-axiom shape `<owner>._native.bv_decide.ax_<n>_<m>`. -/
def isBvdCertAxiomName : Name → Bool
  | .str (.str (.str p "_native") "bv_decide") s =>
      !p.isAnonymous &&
      match s.splitOn "_" with
      | ["ax", n, m] => isDigitsNonEmpty n && isDigitsNonEmpty m
      | _ => false
  | _ => false

def isNativeDecideAxiomName : Name → Bool
  | .str (.str (.str p "_native") "native_decide") s =>
      !p.isAnonymous && s.startsWith "ax"
  | _ => false

def isBvAuxDef (env : Environment) (owner k : Name) (pre : String) (ty : Name) : Bool :=
  let nameOk := k.getPrefix == owner && match k with
    | .str _ s => s.startsWith pre
    | _ => false
  nameOk && match env.find? k with
    | some (.defnInfo d) => d.type == .const ty []
    | _ => false

def isBvdCertShape (env : Environment) (owner : Name) (ty : Expr) : Bool := Id.run do
  unless ty.isAppOfArity ``Eq 3 && ty.appFn!.appFn!.appArg! == .const ``Bool []
      && ty.appArg! == .const ``Bool.true [] do
    return false
  let lhs := ty.appFn!.appArg!
  unless lhs.isAppOfArity `Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 do return false
  let .const e [] := lhs.appFn!.appArg! | return false
  let .const c [] := lhs.appArg! | return false
  return isBvAuxDef env owner e "_expr_def" `Std.Tactic.BVDecide.BVLogicalExpr
    && isBvAuxDef env owner c "_cert_def" ``String

def isBvdOwnerThm (env : Environment) (owner a : Name) : Bool :=
  match env.find? owner with
  | some (.thmInfo _) => env.getModuleIdxFor? owner == env.getModuleIdxFor? a
  | _ => false

def isAllowedBvdAxiom (env : Environment) (a : Name) : Bool :=
  isBvdCertAxiomName a &&
  match env.find? a with
  | some (.axiomInfo v) =>
      let owner := a.getPrefix.getPrefix.getPrefix
      v.levelParams.isEmpty && !v.isUnsafe && isBvdCertShape env owner v.type &&
      isBvdOwnerThm env owner a
  | _ => false

def isBvdAuxConst (env : Environment) (c : Name) : Bool :=
  if isBvdCertAxiomName c then true
  else
    match c with
    | .str owner seg =>
        if seg.startsWith "_expr_def" then
          isBvAuxDef env owner c "_expr_def" `Std.Tactic.BVDecide.BVLogicalExpr
        else if seg.startsWith "_cert_def" then
          isBvAuxDef env owner c "_cert_def" ``String
        else
          false
    | _ => false

structure ModBuckets where
  mathlib : Nat := 0
  std     : Nat := 0
  initMod : Nat := 0
  leanMod : Nat := 0
  other   : Nat := 0
  deriving Inhabited

def ModBuckets.add (b : ModBuckets) (m? : Option Name) : ModBuckets :=
  match m? with
  | none => { b with other := b.other + 1 }
  | some m =>
      let s := m.toString
      if s == "Mathlib" || s.startsWith "Mathlib." then { b with mathlib := b.mathlib + 1 }
      else if s == "Std" || s.startsWith "Std." then { b with std := b.std + 1 }
      else if s == "Init" || s.startsWith "Init." then { b with initMod := b.initMod + 1 }
      else if s == "Lean" || s.startsWith "Lean." then { b with leanMod := b.leanMod + 1 }
      else { b with other := b.other + 1 }

def ModBuckets.fmt (b : ModBuckets) : String :=
  s!"Mathlib={b.mathlib}, Std={b.std}, Init={b.initMod}, Lean={b.leanMod}, Other={b.other}"

def addSet (acc add : NameSet) : NameSet := Id.run do
  let mut out := acc
  for n in add do
    out := out.insert n
  return out

/-- Collect structure type names and `idx`-th field projection functions from primitive `Expr.proj`
nodes, pointer-memoized over the `Expr` DAG so shared subterms are visited once. -/
unsafe def collectProjRefsWithMode (env : Environment) (useBuggyFieldInfoIdx : Bool) (e : Expr) : NameSet := Id.run do
  let mut seen : Std.HashSet USize := {}
  let mut out : NameSet := {}
  let mut work : Array Expr := #[e]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    match cur with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => continue
    | _ => pure ()
    let addr := ptrAddrUnsafe cur
    if seen.contains addr then continue
    seen := seen.insert addr
    match cur with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => pure ()
    | .app fn arg =>
        work := work.push fn
        work := work.push arg
    | .lam _ d b _ | .forallE _ d b _ =>
        work := work.push d
        work := work.push b
    | .letE _ t v b _ =>
        work := work.push t
        work := work.push v
        work := work.push b
    | .mdata _ b =>
        work := work.push b
    | .proj typeName idx structExpr =>
        out := out.insert typeName
        let projFn? : Option Name := do
          let si ← getStructureInfo? env typeName
          if useBuggyFieldInfoIdx then
            let fi ← si.fieldInfo[idx]?
            guard (env.contains fi.projFn)
            return fi.projFn
          else
            let fn ← si.fieldNames[idx]?
            let pf ← getProjFnForField? env typeName fn
            guard (env.contains pf)
            return pf
        match projFn? with
        | some pf => out := out.insert pf
        | none    => out := out.insert (Name.mkStr typeName s!"_raw_proj_{idx}")
        work := work.push structExpr
  return out

unsafe def collectProjRefs (env : Environment) (e : Expr) : NameSet :=
  collectProjRefsWithMode env false e

unsafe def collectExprConsts (env : Environment) (e : Expr) : NameSet :=
  addSet e.getUsedConstantsAsSet (collectProjRefs env e)

@[inline] def resolveProjTarget (env : Environment) (typeName : Name) (idx : Nat) : Name :=
  let projFn? : Option Name := do
    let si ← getStructureInfo? env typeName
    let fn ← si.fieldNames[idx]?
    let pf ← getProjFnForField? env typeName fn
    guard (env.contains pf)
    return pf
  match projFn? with
  | some pf => pf
  | none    => Name.mkStr typeName s!"_raw_proj_{idx}"

/-- Single-pass `Expr` DAG collector equivalent to `addSet e.getUsedConstantsAsSet (collectProjRefs env e)`,
pointer-memoized over non-leaf nodes with cached `(typeName, idx)` projection resolution. -/
unsafe def collectExprConstsSinglePass (env : Environment)
    (projMemo0 : Std.HashMap (Name × Nat) Name) (e : Expr) (init : NameSet := {}) :
    (NameSet × Std.HashMap (Name × Nat) Name) := Id.run do
  let mut seen : Std.HashSet USize := {}
  let mut out : NameSet := init
  let mut projMemo := projMemo0
  let mut work : Array Expr := #[e]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    match cur with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => continue
    | .const c _ =>
        out := out.insert c
        continue
    | _ => pure ()
    let addr := ptrAddrUnsafe cur
    if seen.contains addr then continue
    seen := seen.insert addr
    match cur with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => pure ()
    | .app fn arg =>
        work := work.push fn
        work := work.push arg
    | .lam _ d b _ | .forallE _ d b _ =>
        work := work.push d
        work := work.push b
    | .letE _ t v b _ =>
        work := work.push t
        work := work.push v
        work := work.push b
    | .mdata _ b =>
        work := work.push b
    | .proj typeName idx structExpr =>
        out := out.insert typeName
        let key := (typeName, idx)
        let pfName ← match projMemo[key]? with
          | some cached => pure cached
          | none =>
              let r := resolveProjTarget env typeName idx
              projMemo := projMemo.insert key r
              pure r
        out := out.insert pfName
        work := work.push structExpr
  return (out, projMemo)

structure ExprLiteralScan where
  hasNatLit     : Bool := false
  hasBitVecLit  : Bool := false
  hasByteList   : Bool := false
  stringLits    : Array String := #[]
  deriving Inhabited

/-- Pointer-memoized scan of `e` for numeric literals, `BitVec` constructors, `List.cons`, and
string literals. -/
unsafe def scanExprLiterals (e : Expr) : ExprLiteralScan := Id.run do
  let mut seen : Std.HashSet USize := {}
  let mut hasNat := false
  let mut hasBv := false
  let mut hasList := false
  let mut strSet : Std.HashSet String := {}
  let mut work : Array Expr := #[e]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    let addr := ptrAddrUnsafe cur
    if seen.contains addr then continue
    seen := seen.insert addr
    match cur with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ => pure ()
    | .lit (.natVal _) => hasNat := true
    | .lit (.strVal s) => strSet := strSet.insert s
    | .const n _ =>
        if n == ``OfNat.ofNat then hasNat := true
        else if n == `BitVec.ofNat || n == `BitVec.ofFin || n == `BitVec.ofInt then hasBv := true
        else if n == ``List.cons then hasList := true
    | .app fn arg =>
        work := work.push fn
        work := work.push arg
    | .lam _ d b _ | .forallE _ d b _ =>
        work := work.push d
        work := work.push b
    | .letE _ t v b _ =>
        work := work.push t
        work := work.push v
        work := work.push b
    | .mdata _ b =>
        work := work.push b
    | .proj _ _ s =>
        work := work.push s
  let sortedStrs := strSet.toArray.qsort (· < ·)
  return { hasNatLit := hasNat, hasBitVecLit := hasBv, hasByteList := hasList, stringLits := sortedStrs }

unsafe def scanConstLiterals (env : Environment) (c : Name) : ExprLiteralScan := Id.run do
  let some info := env.find? c | return {}
  let sType := scanExprLiterals info.type
  let sVal := match info with
    | .defnInfo v | .thmInfo v | .opaqueInfo v => scanExprLiterals v.value
    | _ => {}
  let mut merged : Std.HashSet String := {}
  for s in sType.stringLits do merged := merged.insert s
  for s in sVal.stringLits do merged := merged.insert s
  return {
    hasNatLit := sType.hasNatLit || sVal.hasNatLit,
    hasBitVecLit := sType.hasBitVecLit || sVal.hasBitVecLit,
    hasByteList := sType.hasByteList || sVal.hasByteList,
    stringLits := merged.toArray.qsort (· < ·)
  }

structure ConstEdges where
  kind      : String := "missing"
  typeDeps  : Array Name := #[]
  valueDeps : Array Name := #[]
  hasValue  : Bool := false
  deriving Inhabited

unsafe def computeConstEdges (env : Environment) (synthInductAux : Bool) (c : Name) :
    ConstEdges := Id.run do
  let some info := env.find? c | return { kind := "missing" }
  let tSet := collectExprConsts env info.type
  match info with
  | .axiomInfo _ =>
      return { kind := "axiom", typeDeps := sortNames tSet, valueDeps := #[], hasValue := false }
  | .quotInfo _ =>
      return { kind := "quot", typeDeps := sortNames tSet, valueDeps := #[], hasValue := false }
  | .thmInfo v =>
      let vSet := collectExprConsts env v.value
      return { kind := "theorem", typeDeps := sortNames tSet, valueDeps := sortNames vSet, hasValue := true }
  | .opaqueInfo v =>
      let vSet := collectExprConsts env v.value
      return { kind := "opaque", typeDeps := sortNames tSet, valueDeps := sortNames vSet, hasValue := true }
  | .defnInfo v =>
      let vSet := collectExprConsts env v.value
      let kind := if (env.getProjectionFnInfo? c).isSome then "projection" else "def"
      return { kind, typeDeps := sortNames tSet, valueDeps := sortNames vSet, hasValue := true }
  | .inductInfo v =>
      let kind := if isStructure env c then "structure" else "inductive"
      let mut vSet : NameSet := {}
      for ctor in v.ctors do
        if env.contains ctor then vSet := vSet.insert ctor
      for indName in v.all do
        if env.contains indName then vSet := vSet.insert indName
      if synthInductAux then
        for indName in v.all do
          let recN := mkRecName indName
          if env.contains recN then vSet := vSet.insert recN
        if let some si := getStructureInfo? env c then
          for fi in si.fieldInfo do
            if env.contains fi.projFn then vSet := vSet.insert fi.projFn
      return { kind, typeDeps := sortNames tSet, valueDeps := sortNames vSet, hasValue := true }
  | .ctorInfo v =>
      let mut vSet : NameSet := {}
      if env.contains v.induct then vSet := vSet.insert v.induct
      return { kind := "ctor", typeDeps := sortNames tSet, valueDeps := sortNames vSet, hasValue := true }
  | .recInfo v =>
      let mut vSet : NameSet := {}
      for indName in v.all do
        if env.contains indName then vSet := vSet.insert indName
      for rule in v.rules do
        vSet := addSet vSet (collectExprConsts env rule.rhs)
      return { kind := "recursor", typeDeps := sortNames tSet, valueDeps := sortNames vSet, hasValue := true }

unsafe def getEdgesCached (env : Environment) (synthInductAux : Bool)
    (cache : IO.Ref (Std.HashMap Name ConstEdges)) (c : Name) : IO ConstEdges := do
  if let some e := (← cache.get)[c]? then
    return e
  let e := computeConstEdges env synthInductAux c
  cache.modify (·.insert c e)
  return e

/-- Collect outgoing dependency constants (`typeDeps ∪ valueDeps`) for `stepCriterionBatch` in a
single `Expr` pass without sorting or allocating `ConstEdges`. -/
unsafe def computeCriterionConstDeps (env : Environment) (synthInductAux : Bool)
    (projMemo0 : Std.HashMap (Name × Nat) Name) (c : Name) :
    (NameSet × Std.HashMap (Name × Nat) Name) := Id.run do
  let some info := env.find? c | return ({}, projMemo0)
  let (tSet, pm1) := collectExprConstsSinglePass env projMemo0 info.type {}
  match info with
  | .axiomInfo _ | .quotInfo _ =>
      return (tSet, pm1)
  | .thmInfo v | .opaqueInfo v | .defnInfo v =>
      return collectExprConstsSinglePass env pm1 v.value tSet
  | .inductInfo v =>
      let mut out := tSet
      for ctor in v.ctors do
        if env.contains ctor then out := out.insert ctor
      for indName in v.all do
        if env.contains indName then out := out.insert indName
      if synthInductAux then
        for indName in v.all do
          let recN := mkRecName indName
          if env.contains recN then out := out.insert recN
        if let some si := getStructureInfo? env c then
          for fi in si.fieldInfo do
            if env.contains fi.projFn then out := out.insert fi.projFn
      return (out, pm1)
  | .ctorInfo v =>
      return (if env.contains v.induct then tSet.insert v.induct else tSet, pm1)
  | .recInfo v =>
      let mut out := tSet
      let mut pm := pm1
      for indName in v.all do
        if env.contains indName then out := out.insert indName
      for rule in v.rules do
        let (out', pm') := collectExprConstsSinglePass env pm rule.rhs out
        out := out'
        pm := pm'
      return (out, pm)

unsafe def computeCriterionSliceDeps (env : Environment) (synthInductAux : Bool)
    (uWork : Array Name) (lo hi : Nat) : Array NameSet := Id.run do
  let mut out : Array NameSet := Array.mkEmpty (hi - lo)
  let mut pm : Std.HashMap (Name × Nat) Name := {}
  for idx in [lo:hi] do
    let (deps, pm') := computeCriterionConstDeps env synthInductAux pm uWork[idx]!
    out := out.push deps
    pm := pm'
  return out

structure DenyHit where
  constName : Name
  defMod    : String
  hops      : Nat
  deriving Inhabited

structure AllowHit where
  constName : Name
  defMod    : String
  reason    : String
  hops      : Nat
  deriving Inhabited

structure ConeResult where
  visited         : Nat := 0
  enqueued        : Nat := 0
  processed       : Nat := 0
  maxHops         : Nat := 0
  layerCounts     : Array Nat := #[]
  unexpandedEdges : Nat := 0
  seenSet         : NameSet := {}
  buckets         : ModBuckets := {}
  parent          : Std.HashMap Name Name := {}
  denyHits        : Array DenyHit := #[]
  allowHits       : Array AllowHit := #[]
  deriving Inhabited

/-- Transitive BFS cone walk from `seeds`. An `allowMap` entry suppresses only `c`'s own deny hit
while still traversing `c`'s `typeDeps` and `valueDeps`. -/
unsafe def runConeBFS (env : Environment) (allowLocalControl synthInductAux : Bool)
    (cache : IO.Ref (Std.HashMap Name ConstEdges))
    (denyPats : Array DenyPattern) (allowMap : Std.HashMap Name String)
    (seeds : Array Name) (seedParent? : Option Name) : IO ConeResult := do
  let mut seen : NameSet := {}
  if let some r := seedParent? then
    seen := seen.insert r
  let mut parent : Std.HashMap Name Name := {}
  let mut dist : Std.HashMap Name Nat := {}
  let mut queue : Array Name := #[]
  let initHops := if seedParent?.isSome then 1 else 0
  for s in seeds do
    unless seen.contains s do
      seen := seen.insert s
      dist := dist.insert s initHops
      if let some p := seedParent? then
        parent := parent.insert s p
      queue := queue.push s
  let mut visited : Nat := 0
  let mut maxHops : Nat := 0
  let mut layerMap : Std.HashMap Nat Nat := {}
  let mut buckets : ModBuckets := {}
  let mut denyHits : Array DenyHit := #[]
  let mut allowHits : Array AllowHit := #[]
  let mut idx : Nat := 0
  while idx < queue.size do
    let c := queue[idx]!
    idx := idx + 1
    let d := dist.getD c 0
    if d > maxHops then maxHops := d
    layerMap := layerMap.insert d ((layerMap.getD d 0) + 1)
    let m? ← definingModWithPolicy? env allowLocalControl c
    visited := visited + 1
    buckets := buckets.add m?
    if isModDenied denyPats m? then
      if let some reason := allowMap[c]? then
        allowHits := allowHits.push { constName := c, defMod := modLabel m?, reason, hops := d }
      else
        denyHits := denyHits.push { constName := c, defMod := modLabel m?, hops := d }
    let edges ← getEdgesCached env synthInductAux cache c
    for next in edges.typeDeps do
      unless seen.contains next do
        seen := seen.insert next
        dist := dist.insert next (d + 1)
        if let some r := seedParent? then
          if next != r then parent := parent.insert next c
        else
          parent := parent.insert next c
        queue := queue.push next
    for next in edges.valueDeps do
      unless seen.contains next do
        seen := seen.insert next
        dist := dist.insert next (d + 1)
        if let some r := seedParent? then
          if next != r then parent := parent.insert next c
        else
          parent := parent.insert next c
        queue := queue.push next

  -- Verify fixed-point closure: no outgoing edge escapes `seen`.
  let mut unexpanded : Nat := 0
  for c in queue do
    let edges ← getEdgesCached env synthInductAux cache c
    for next in edges.typeDeps do
      unless seen.contains next do unexpanded := unexpanded + 1
    for next in edges.valueDeps do
      unless seen.contains next do unexpanded := unexpanded + 1

  let mut layerCounts : Array Nat := #[]
  if queue.size > 0 then
    for h in [:maxHops + 1] do
      layerCounts := layerCounts.push (layerMap.getD h 0)

  let sortedDeny := denyHits.qsort (fun a b =>
    a.hops < b.hops || (a.hops == b.hops && a.constName.toString < b.constName.toString))
  let sortedAllow := allowHits.qsort (fun a b =>
    a.hops < b.hops || (a.hops == b.hops && a.constName.toString < b.constName.toString))
  return {
    visited,
    enqueued := queue.size,
    processed := idx,
    maxHops,
    layerCounts,
    unexpandedEdges := unexpanded,
    seenSet := seen,
    buckets,
    parent,
    denyHits := sortedDeny,
    allowHits := sortedAllow
  }

def reconstructChain (parent : Std.HashMap Name Name) (target : Name) : Array Name := Id.run do
  let mut rev : Array Name := #[target]
  let mut cur := target
  let mut fuel : Nat := parent.size + 2
  while fuel > 0 do
    fuel := fuel - 1
    match parent[cur]? with
    | some p =>
        if p == cur then break
        rev := rev.push p
        cur := p
    | none => break
  return rev.reverse

def renderTruncatedNodes (nodes : Array Name) (maxChainHops : Nat) : (Nat × String) :=
  let hops := if nodes.size > 0 then nodes.size - 1 else 0
  let s :=
    if maxChainHops == 0 || hops <= maxChainHops then
      String.intercalate " -> " (nodes.toList.map dispConst)
    else
      let headKeep := (maxChainHops + 1) / 2
      let tailKeep := (maxChainHops + 1) - headKeep
      let headPart := (nodes.extract 0 headKeep).toList.map dispConst
      let tailPart := (nodes.extract (nodes.size - tailKeep) nodes.size).toList.map dispConst
      let omitted := nodes.size - headKeep - tailKeep
      String.intercalate " -> " headPart ++
        s!" -> ... ({omitted} intermediate constants omitted; {hops} hops) -> " ++
        String.intercalate " -> " tailPart
  (hops, s)

def formatChainRaw (parent : Std.HashMap Name Name) (target : Name) (defMod : String)
    (maxChainHops : Nat) : String :=
  let chain := reconstructChain parent target
  let (hops, renderedNodes) := renderTruncatedNodes chain maxChainHops
  s!"[hops={hops}] {renderedNodes} [{defMod}]"

def formatChain (parent : Std.HashMap Name Name) (hit : DenyHit) (maxChainHops : Nat) : String :=
  formatChainRaw parent hit.constName hit.defMod maxChainHops

def printHitList (indent : String) (parent : Std.HashMap Name Name) (hits : Array DenyHit)
    (maxChainHops maxHits : Nat) : IO Unit := do
  let limit := if maxHits == 0 || hits.size <= maxHits then hits.size else maxHits
  for i in [:limit] do
    let h := hits[i]!
    IO.println s!"{indent}- {formatChain parent h maxChainHops}"
  if hits.size > limit then
    IO.println s!"{indent}... ({hits.size - limit} more deny hits omitted; pass --max-hits 0 for all {hits.size})"

structure CliConfig where
  denyFiles                : Array FilePath := #[]
  excludedGroups           : Array String := #[]
  allowFiles               : Array FilePath := #[]
  exemptSpecsFile          : Option FilePath := none
  defaultSeedsFile         : Option FilePath := none
  defaultClosureFile       : Option FilePath := none
  emitHeaderMetaFile       : Option FilePath := none
  noAllow                  : Bool := false
  subsetAllow              : Bool := false
  criterion                : Bool := false
  criterionTsv             : Option FilePath := none
  oneStep                  : Bool := false
  emitProofdeps            : Option FilePath := none
  checkProofdeps           : Option FilePath := none
  rootReport               : Bool := false
  bridgesFile              : Option FilePath := none
  expectedRootTypeFile     : Option FilePath := none
  allowScratchFixtureRoots : Bool := false
  extraImports             : Array Name := #[]
  maxChainHops             : Nat := 10
  maxHits                  : Nat := 0
  allModuleConsts          : Bool := false
  nonInternalModuleConsts  : Bool := false
  summaryOnly              : Bool := false
  synthInductAux           : Bool := false
  inProcessBatches         : Bool := false
  legacySlowEdges          : Bool := false
  batchWorkerState         : Option FilePath := none
  batchWorkerSeeds         : Option FilePath := none
  gkControl                : Option String := none
  primaryMod               : Option Name := none
  targets                  : Array String := #[]
  showHelp                 : Bool := false
  deriving Inhabited

def validGkControls : Array String :=
  #["neg1", "neg1-standin", "neg2", "neg3", "neg3-bug-demo", "neg4", "neg5", "neg5b", "arch1", "arch2", "arch3"]

def usageText : String :=
  "Usage: lean --run Symbolic/scripts/MachineFreeCheck.lean [OPTIONS] [<Module.Name> [<Const1> <Const2> ...]]\n" ++
  "\n" ++
  "Options:\n" ++
  "  --deny-file PATH                 Defining-module deny list (repeatable; default: Symbolic/scripts/machine_free_deny.txt)\n" ++
  "  --exclude-deny-group ID          Exclude `[group <ID>]` patterns from `--deny-file` (repeatable; fail-closed if absent)\n" ++
  "  --allow-file PATH                Exact per-constant allow-list (repeatable; default: Symbolic/scripts/machine_free_allow.txt)\n" ++
  "  --exempt-specs-file PATH         Closed exemption list E of mixed Specifications modules\n" ++
  "  --default-target-seeds-file PATH Seed modules from `lakefile.lean` `@[default_target] lean_lib`s\n" ++
  "  --default-target-closure-file P  Precomputed default-target module closure for `--root-report` (E2)\n" ++
  "  --emit-header-meta-file PATH     Informational `#` header lines for `--emit-proofdeps` (not compared by `--check-proofdeps`)\n" ++
  "  --no-allow                       Ignore allow-list (check with 0 allowed constants)\n" ++
  "  --subset-allow                   Permit unreached allow-list entries\n" ++
  "  --criterion                      Compute per-module machine-level fixed point over default Lake target closure\n" ++
  "  --criterion-tsv PATH             Write `--criterion` TSV rows to PATH\n" ++
  "  --one-step                       Debug mode for control P5 (`--criterion` only; forbidden with `--emit-proofdeps`/`--check-proofdeps`)\n" ++
  "  --emit-proofdeps OUT_PATH        Write Part-C `machine_free_deny_proofdeps.txt` (fails if D2 > 0)\n" ++
  "  --check-proofdeps PATH           Exact CI drift check on Part-C `machine_free_deny_proofdeps.txt` (exact body vs canonical `--emit-proofdeps`; leading `#` header ignored)\n" ++
  "  --root-report                    Emit R-a root types, R-b bridge table, E1 residual report, and std3/ofReduce checks\n" ++
  "  --bridges-file PATH              Bridge names file for R-b under `--root-report`\n" ++
  "  --expected-root-type-file PATH   Expected `<FullRootConst> : <ppExpr>` file for R-a comparison\n" ++
  "  --allow-scratch-fixture-roots    Control-runner mode only: permit scratch fixture roots outside lakefile default targets\n" ++
  "  --import MOD                     Additional module to import (repeatable)\n" ++
  "  --all-module-consts              Audit ALL constants in <Module.Name> (and --import modules), incl. internals\n" ++
  "  --non-internal-module-consts     Audit !Name.isInternal constants in <Module.Name> (and --import modules)\n" ++
  "  --summary-only                   Print concise per-root one-liners + aggregate summary\n" ++
  "  --synth-induct-aux               Also traverse unused projections/recursors on .inductInfo (comparison mode)\n" ++
  "  --gk-control ID                  Inject negative control in-memory via addDeclCore\n" ++
  "  --max-chain-hops N               Truncate shortest BFS chains longer than N hops (default: 10; 0 = unlimited)\n" ++
  "  --max-hits N                     Cap printed chains per section to N (default: 0 = print all)\n" ++
  "  -h, --help                       Show this help and exit 0"

partial def parseCliArgs (cfg : CliConfig) : List String → Except String CliConfig
  | [] => .ok cfg
  | "-h" :: _ | "--help" :: _ => .ok { cfg with showHelp := true }
  | "--deny-file" :: p :: rest => parseCliArgs { cfg with denyFiles := cfg.denyFiles.push p } rest
  | "--deny-file" :: [] => .error "--deny-file requires a PATH argument"
  | "--exclude-deny-group" :: gid :: rest =>
      if !gid.isEmpty && !gid.any Char.isWhitespace then
        parseCliArgs { cfg with excludedGroups := cfg.excludedGroups.push gid } rest
      else
        .error s!"invalid --exclude-deny-group '{gid}'"
  | "--exclude-deny-group" :: [] => .error "--exclude-deny-group requires a GROUP_ID argument"
  | "--allow-file" :: p :: rest => parseCliArgs { cfg with allowFiles := cfg.allowFiles.push p } rest
  | "--allow-file" :: [] => .error "--allow-file requires a PATH argument"
  | "--exempt-specs-file" :: p :: rest => parseCliArgs { cfg with exemptSpecsFile := some p } rest
  | "--exempt-specs-file" :: [] => .error "--exempt-specs-file requires a PATH argument"
  | "--default-target-seeds-file" :: p :: rest => parseCliArgs { cfg with defaultSeedsFile := some p } rest
  | "--default-target-seeds-file" :: [] => .error "--default-target-seeds-file requires a PATH argument"
  | "--default-target-closure-file" :: p :: rest => parseCliArgs { cfg with defaultClosureFile := some p } rest
  | "--default-target-closure-file" :: [] => .error "--default-target-closure-file requires a PATH argument"
  | "--emit-header-meta-file" :: p :: rest => parseCliArgs { cfg with emitHeaderMetaFile := some p } rest
  | "--emit-header-meta-file" :: [] => .error "--emit-header-meta-file requires a PATH argument"
  | "--no-allow" :: rest => parseCliArgs { cfg with noAllow := true } rest
  | "--subset-allow" :: rest => parseCliArgs { cfg with subsetAllow := true } rest
  | "--criterion" :: rest => parseCliArgs { cfg with criterion := true } rest
  | "--criterion-tsv" :: p :: rest => parseCliArgs { cfg with criterionTsv := some p } rest
  | "--criterion-tsv" :: [] => .error "--criterion-tsv requires a PATH argument"
  | "--one-step" :: rest => parseCliArgs { cfg with oneStep := true } rest
  | "--emit-proofdeps" :: p :: rest => parseCliArgs { cfg with emitProofdeps := some p } rest
  | "--emit-proofdeps" :: [] => .error "--emit-proofdeps requires an OUT_PATH argument"
  | "--check-proofdeps" :: p :: rest => parseCliArgs { cfg with checkProofdeps := some p } rest
  | "--check-proofdeps" :: [] => .error "--check-proofdeps requires a PATH argument"
  | "--root-report" :: rest => parseCliArgs { cfg with rootReport := true } rest
  | "--bridges-file" :: p :: rest => parseCliArgs { cfg with bridgesFile := some p } rest
  | "--bridges-file" :: [] => .error "--bridges-file requires a PATH argument"
  | "--expected-root-type-file" :: p :: rest => parseCliArgs { cfg with expectedRootTypeFile := some p } rest
  | "--expected-root-type-file" :: [] => .error "--expected-root-type-file requires a PATH argument"
  | "--allow-scratch-fixture-roots" :: rest => parseCliArgs { cfg with allowScratchFixtureRoots := true } rest
  | "--import" :: m :: rest =>
      if validModSegments m then
        parseCliArgs { cfg with extraImports := cfg.extraImports.push (parseName m) } rest
      else
        .error s!"invalid module name for --import: '{m}'"
  | "--import" :: [] => .error "--import requires a MODULE argument"
  | "--all-module-consts" :: rest => parseCliArgs { cfg with allModuleConsts := true } rest
  | "--non-internal-module-consts" :: rest => parseCliArgs { cfg with nonInternalModuleConsts := true } rest
  | "--summary-only" :: rest => parseCliArgs { cfg with summaryOnly := true } rest
  | "--synth-induct-aux" :: rest => parseCliArgs { cfg with synthInductAux := true } rest
  | "--in-process-batches" :: rest => parseCliArgs { cfg with inProcessBatches := true } rest
  | "--legacy-slow-edges" :: rest => parseCliArgs { cfg with legacySlowEdges := true } rest
  | "--batch-worker-state" :: p :: rest => parseCliArgs { cfg with batchWorkerState := some p } rest
  | "--batch-worker-state" :: [] => .error "--batch-worker-state requires a PATH argument"
  | "--batch-worker-seeds" :: p :: rest => parseCliArgs { cfg with batchWorkerSeeds := some p } rest
  | "--batch-worker-seeds" :: [] => .error "--batch-worker-seeds requires a PATH argument"
  | "--gk-control" :: cid :: rest =>
      if validGkControls.contains cid then
        parseCliArgs { cfg with gkControl := some cid } rest
      else
        .error s!"unknown --gk-control '{cid}' (expected one of {validGkControls})"
  | "--gk-control" :: [] => .error "--gk-control requires an ID argument"
  | "--max-chain-hops" :: n :: rest =>
      match n.toNat? with
      | some k => parseCliArgs { cfg with maxChainHops := k } rest
      | none   => .error s!"--max-chain-hops expects a non-negative integer, got '{n}'"
  | "--max-chain-hops" :: [] => .error "--max-chain-hops requires an integer argument"
  | "--max-hits" :: n :: rest =>
      match n.toNat? with
      | some k => parseCliArgs { cfg with maxHits := k } rest
      | none   => .error s!"--max-hits expects a non-negative integer, got '{n}'"
  | "--max-hits" :: [] => .error "--max-hits requires an integer argument"
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown option '{arg}'"
      else
        match cfg.primaryMod with
        | none =>
            if validModSegments arg then
              parseCliArgs { cfg with primaryMod := some (parseName arg) } rest
            else
              .error s!"invalid module name '{arg}'"
        | some _ =>
            if validModSegments arg then
              parseCliArgs { cfg with targets := cfg.targets.push arg } rest
            else
              .error s!"invalid constant name '{arg}'"

def resolveTargetConst (env : Environment) (importedMods : Array Name) (raw : String) :
    Except String Name := Id.run do
  let cand := parseName raw
  if env.contains cand then
    return .ok cand
  let mut privMatches : Array Name := #[]
  for m in importedMods do
    if let some idx := env.header.moduleNames.idxOf? m then
      for c in env.header.moduleData[idx]!.constNames do
        if Lean.privateToUserName? c == some cand then
          privMatches := privMatches.push c
  if privMatches.size == 1 then
    return .ok privMatches[0]!
  else if privMatches.size > 1 then
    return .error s!"ambiguous private constant '{raw}' ({privMatches.size} matches in imported modules)"
  else
    return .error s!"constant '{raw}' not found in imported environment"

/-- Inject `--gk-control` negative-control declarations in memory via `Environment.addDeclCore`. -/
unsafe def applyGkControl (cid : String) (env : Environment) (allowMap : Std.HashMap Name String)
    (roots : Array Name) : IO (Environment × Std.HashMap Name String × Array Name) := do
  match cid with
  | "neg1" =>
      let rootName := `Arm64.State.setFs
      unless env.contains rootName do
        throw <| IO.userError s!"gk-control neg1 requires {rootName} in imported environment (pass --import Arm64.Trusted.ISA.State)"
      let allowMap' := allowMap.insert rootName "[TEST-NEG1] allowed root in Arm64.Trusted.ISA.State mentioning Arm64.State"
      IO.println s!"# GK_CONTROL=neg1: added {rootName} [Arm64.Trusted.ISA.State] to allowMap and roots"
      return (env, allowMap', roots.push rootName)
  | "neg1-standin" =>
      unless env.contains `Arm64.State && env.contains `Arm64.State.regs && env.contains `Arm64.RegFile do
        throw <| IO.userError "gk-control neg1-standin requires Arm64.Trusted.ISA.State (--import Arm64.Trusted.ISA.State)"
      let declName := `Arm64.TestStandIn.allowedStandInReadsRegs
      let sTy := Expr.const `Arm64.State []
      let rTy := Expr.const `Arm64.RegFile []
      let declTy := Expr.forallE `s sTy rTy .default
      let declVal := Expr.lam `s sTy (Expr.app (Expr.const `Arm64.State.regs []) (Expr.bvar 0)) .default
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] declTy declVal (.regular 1) .safe [declName])
      match env.addDeclCore 0 4096 decl none (doCheck := true) with
      | .ok env' =>
          let allowMap' := allowMap.insert declName "[TEST-NEG1-STANDIN] allow-listed stand-in whose body reads Arm64.State.regs"
          IO.println s!"# GK_CONTROL=neg1-standin: kernel-checked `def {declName} (s : Arm64.State) : Arm64.RegFile := s.regs`, added `{declName}` to allowMap and roots"
          return (env', allowMap', roots.push declName)
      | .error _ =>
          throw <| IO.userError "gk-control neg1-standin: kernel rejected stand-in declaration"
  | "neg2" =>
      let declName := `GkControl.readExclFails
      let pTy := Expr.const `Arm64.Process.ProcessInputs []
      let retTy := Expr.app (Expr.const `List [Level.zero]) (Expr.const `Bool [])
      let declTy := Expr.forallE `p pTy retTy .default
      let projOracle := Expr.app (Expr.const `Arm64.Process.ProcessInputs.oracle []) (Expr.bvar 0)
      let body := Expr.app (Expr.const `Arm64.Oracle.exclFails []) projOracle
      let declVal := Expr.lam `p pTy body .default
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] declTy declVal (.regular 1) .safe [declName])
      match env.addDeclCore 0 4096 decl none (doCheck := true) with
      | .ok env' =>
          IO.println s!"# GK_CONTROL=neg2: kernel-checked `def {declName} (p : ProcessInputs) : List Bool := p.oracle.exclFails` via addDeclCore"
          return (env', allowMap, roots.push declName)
      | .error _ =>
          throw <| IO.userError "gk-control neg2: kernel rejected GkControl.readExclFails"
  | "neg3" =>
      let pTy := Expr.const `Arm64.Process.ProcessInputs []
      let iTy := Expr.const `Arm64.Process.ProcessInit []
      let oTy := Expr.const `Arm64.Oracle []
      let declTyPI := Expr.forallE `p pTy iTy .default
      let val7 := Expr.lam `p pTy (Expr.proj `Arm64.Process.ProcessInputs 7 (Expr.bvar 0)) .default
      let decl7 := Declaration.defnDecl
        (mkDefinitionValEx `GkControl.rawProjIdx7 [] declTyPI val7 (.regular 1) .safe [`GkControl.rawProjIdx7])
      match env.addDeclCore 0 4096 decl7 none (doCheck := true) with
      | .ok _ =>
          throw <| IO.userError "gk-control neg3: unexpected kernel acceptance of out-of-bounds Expr.proj ProcessInputs idx=7"
      | .error _ =>
          IO.println "# GK_CONTROL=neg3: kernel addDeclCore (doCheck := true) REJECTED out-of-bounds `Expr.proj Arm64.Process.ProcessInputs 7 p` (ProcessInputs has 7 fields, 0-based indices 0..6; 7th field `init` = idx 6)"
      let declTyIO := Expr.forallE `q iTy oTy .default
      let val4 := Expr.lam `q iTy (Expr.proj `Arm64.Process.ProcessInit 5 (Expr.bvar 0)) .default
      let decl4 := Declaration.defnDecl
        (mkDefinitionValEx `GkControl.rawProjInitIdx4 [] declTyIO val4 (.regular 1) .safe [`GkControl.rawProjInitIdx4])
      match env.addDeclCore 0 4096 decl4 none (doCheck := true) with
      | .ok _ =>
          throw <| IO.userError "gk-control neg3: unexpected kernel acceptance of out-of-bounds Expr.proj ProcessInit idx=5"
      | .error _ =>
          IO.println "# GK_CONTROL=neg3: kernel addDeclCore (doCheck := true) REJECTED out-of-bounds `Expr.proj Arm64.Process.ProcessInit 5 q` (5 fields, 0..4; oracle = idx 4)"
      let declName := `GkControl.rawProjInit
      let val6 := Expr.lam `p pTy (Expr.proj `Arm64.Process.ProcessInputs 6 (Expr.bvar 0)) .default
      let decl6 := Declaration.defnDecl
        (mkDefinitionValEx declName [] declTyPI val6 (.regular 1) .safe [declName])
      let env1 ← match env.addDeclCore 0 4096 decl6 none (doCheck := true) with
        | .ok env' =>
            IO.println s!"# GK_CONTROL=neg3: kernel addDeclCore ACCEPTED `def {declName} : ProcessInputs -> ProcessInit := fun p => Expr.proj Arm64.Process.ProcessInputs 6 p` (getUsedConstants type={declTyPI.getUsedConstants}, value={val6.getUsedConstants})"
            pure env'
        | .error _ =>
            throw <| IO.userError "gk-control neg3: kernel rejected valid Expr.proj ProcessInputs idx=6 (init)"
      let declName2 := `GkControl.rawProjInitOracle
      let val3 := Expr.lam `q iTy (Expr.proj `Arm64.Process.ProcessInit 4 (Expr.bvar 0)) .default
      let decl3 := Declaration.defnDecl
        (mkDefinitionValEx declName2 [] declTyIO val3 (.regular 1) .safe [declName2])
      match env1.addDeclCore 0 4096 decl3 none (doCheck := true) with
      | .ok env' =>
          IO.println s!"# GK_CONTROL=neg3: kernel addDeclCore ACCEPTED `def {declName2} : ProcessInit -> Oracle := fun q => Expr.proj Arm64.Process.ProcessInit 4 q` (getUsedConstants type={declTyIO.getUsedConstants}, value={val3.getUsedConstants})"
          return (env', allowMap, (roots.push declName).push declName2)
      | .error _ =>
          throw <| IO.userError "gk-control neg3: kernel rejected valid Expr.proj ProcessInit idx=4 (oracle)"
  | "neg3-bug-demo" =>
      let pTy := Expr.const `Arm64.Process.ProcessInputs []
      let iTy := Expr.const `Arm64.Process.ProcessInit []
      let aTy := Expr.const `Arm64.Process.AuxvConfig []
      let valInit := Expr.lam `p pTy (Expr.proj `Arm64.Process.ProcessInputs 6 (Expr.bvar 0)) .default
      let valAuxv := Expr.lam `q iTy (Expr.proj `Arm64.Process.ProcessInit 0 (Expr.bvar 0)) .default
      let buggy6 := sortNames (collectProjRefsWithMode env true valInit)
      let fixed6 := sortNames (collectProjRefsWithMode env false valInit)
      let buggy0 := sortNames (collectProjRefsWithMode env true valAuxv)
      let fixed0 := sortNames (collectProjRefsWithMode env false valAuxv)
      let buggy0Denied := buggy0.filter (fun c => allowMap[c]?.isNone)
      let fixed0Denied := fixed0.filter (fun c => allowMap[c]?.isNone)
      let buggy6Denied := buggy6.filter (fun c => allowMap[c]?.isNone)
      let fixed6Denied := fixed6.filter (fun c => allowMap[c]?.isNone)
      IO.println s!"# GK_CONTROL=neg3-bug-demo (ProcessInputs idx=6 `init`): legacy_fieldInfo_refs={buggy6} vs fixed_fieldNames_refs={fixed6} => {if buggy6 == fixed6 then "SAME" else "DIFFERENT (legacy resolves the wrong field)"}"
      IO.println s!"# GK_CONTROL=neg3-bug-demo (ProcessInputs idx=6 `init`): legacy_unallowed={buggy6Denied} => LEGACY_BUGGY_STATUS={if buggy6Denied.isEmpty then "PASS (MISSED!)" else "FAIL"}; fixed_unallowed={fixed6Denied} => FIXED_STATUS={if fixed6Denied.isEmpty then "PASS" else "FAIL (CAUGHT!)"}"
      IO.println s!"# GK_CONTROL=neg3-bug-demo (ProcessInit idx=0 `auxv`): legacy_fieldInfo_refs={buggy0}, legacy_unallowed={buggy0Denied} => LEGACY_BUGGY_STATUS={if buggy0Denied.isEmpty then "PASS (MISSED!)" else "FAIL"}"
      IO.println s!"# GK_CONTROL=neg3-bug-demo (ProcessInit idx=0 `auxv`): fixed_fieldNames_refs={fixed0}, fixed_unallowed={fixed0Denied} => FIXED_STATUS={if fixed0Denied.isEmpty then "PASS" else "FAIL (CAUGHT!)"}"
      let declName := `GkControl.rawProjInitAuxv
      let declTy := Expr.forallE `q iTy aTy .default
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] declTy valAuxv (.regular 1) .safe [declName])
      match env.addDeclCore 0 4096 decl none (doCheck := true) with
      | .ok env' =>
          return (env', allowMap, roots.push declName)
      | .error _ =>
          throw <| IO.userError "gk-control neg3-bug-demo: kernel rejected valid Expr.proj ProcessInit idx=0 (auxv)"
  | "neg5" =>
      let some stInfo := env.find? `Arm64.Process.ProcessInit.stackTop
        | throw <| IO.userError "gk-control neg5: Arm64.Process.ProcessInit.stackTop not in env"
      let retTy := stInfo.type.bindingBody!
      let pTy := Expr.const `Arm64.Process.ProcessInputs []
      let iTy := Expr.const `Arm64.Process.ProcessInit []
      let declName := `GkControl.readInitStackTop
      let projInit := Expr.app (Expr.const `Arm64.Process.ProcessInputs.init []) (Expr.bvar 0)
      let val := Expr.lam `p pTy (Expr.app (Expr.const `Arm64.Process.ProcessInit.stackTop []) projInit) .default
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] (Expr.forallE `p pTy retTy .default) val (.regular 1) .safe [declName])
      let env1 ← match env.addDeclCore 0 4096 decl none (doCheck := true) with
        | .ok env' =>
            IO.println s!"# GK_CONTROL=neg5: kernel-checked `def {declName} (p : ProcessInputs) := p.init.stackTop` via addDeclCore"
            pure env'
        | .error _ =>
            throw <| IO.userError "gk-control neg5: kernel rejected GkControl.readInitStackTop"
      let declName2 := `GkControl.readBareInitStackTop
      let val2 := Expr.lam `q iTy (Expr.app (Expr.const `Arm64.Process.ProcessInit.stackTop []) (Expr.bvar 0)) .default
      let decl2 := Declaration.defnDecl
        (mkDefinitionValEx declName2 [] (Expr.forallE `q iTy retTy .default) val2 (.regular 1) .safe [declName2])
      match env1.addDeclCore 0 4096 decl2 none (doCheck := true) with
      | .ok env' =>
          IO.println s!"# GK_CONTROL=neg5: kernel-checked `def {declName2} (q : ProcessInit) := q.stackTop` via addDeclCore"
          return (env', allowMap, (roots.push declName).push declName2)
      | .error _ =>
          throw <| IO.userError "gk-control neg5: kernel rejected GkControl.readBareInitStackTop"
  | "neg5b" =>
      -- Simulate allow-listing `ProcessInit.stackTop` on a bare `ProcessInit` so only
      -- `isForbiddenInertConst` rejects the declaration.
      let wrongAllow := `Arm64.Process.ProcessInit.stackTop
      let some stInfo := env.find? wrongAllow
        | throw <| IO.userError "gk-control neg5b: Arm64.Process.ProcessInit.stackTop not in env"
      let retTy := stInfo.type.bindingBody!
      let iTy := Expr.const `Arm64.Process.ProcessInit []
      let allowMap' := allowMap.insert wrongAllow "[TEST-NEG5B] simulated wrong allow entry; the inert guard must still FAIL"
      IO.println s!"# GK_CONTROL=neg5b: inserted allow entry `{wrongAllow}` into allowMap (simulated wrong sign-off)"
      let declName := `GkControl.readBareInitStackTopAllowed
      let val := Expr.lam `q iTy (Expr.app (Expr.const wrongAllow []) (Expr.bvar 0)) .default
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] (Expr.forallE `q iTy retTy .default) val (.regular 1) .safe [declName])
      match env.addDeclCore 0 4096 decl none (doCheck := true) with
      | .ok env' =>
          IO.println s!"# GK_CONTROL=neg5b: kernel-checked `def {declName} (q : ProcessInit) := q.stackTop` via addDeclCore; expect SUMMARY_INERT_GUARD=FAIL listing {wrongAllow} although it is allow-listed"
          return (env', allowMap', roots.push declName)
      | .error _ =>
          throw <| IO.userError "gk-control neg5b: kernel rejected GkControl.readBareInitStackTopAllowed"
  | "neg4" =>
      let staleConst := `Arm64.FdAccessMode.canRead
      let allowMap' := allowMap.insert staleConst "[TEST-NEG4] stale allow entry never reached by statement"
      IO.println s!"# GK_CONTROL=neg4: inserted unreached allow entry `{staleConst}` into allowMap"
      return (env, allowMap', roots)
  | "arch1" =>
      let some argvInfo := env.find? `Arm64.Process.ProcessInputs.argv
        | throw <| IO.userError "gk-control arch1: Arm64.Process.ProcessInputs.argv not in env"
      let declName := `GkControl.readArgv
      let pTy := Expr.const `Arm64.Process.ProcessInputs []
      let declTy := argvInfo.type
      let declVal := Expr.lam `p pTy (Expr.app (Expr.const `Arm64.Process.ProcessInputs.argv []) (Expr.bvar 0)) .default
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] declTy declVal (.regular 1) .safe [declName])
      match env.addDeclCore 0 4096 decl none (doCheck := true) with
      | .ok env' =>
          IO.println s!"# GK_CONTROL=arch1: kernel-checked `def {declName} (p : ProcessInputs) := p.argv` via addDeclCore"
          return (env', allowMap, roots.push declName)
      | .error _ =>
          throw <| IO.userError "gk-control arch1: kernel rejected GkControl.readArgv"
  | "arch2" =>
      unless env.contains `Arm64.State do
        throw <| IO.userError "gk-control arch2 requires Arm64.State in env (pass --import Arm64.Trusted.ISA.State)"
      let declName := `GkControl.mentionsArm64State
      let declTy := Expr.sort (Level.succ Level.zero)
      let declVal := Expr.const `Arm64.State []
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] declTy declVal (.regular 1) .safe [declName])
      match env.addDeclCore 0 4096 decl none (doCheck := true) with
      | .ok env' =>
          IO.println s!"# GK_CONTROL=arch2: kernel-checked `def {declName} : Type := Arm64.State` via addDeclCore"
          return (env', allowMap, roots.push declName)
      | .error _ =>
          throw <| IO.userError "gk-control arch2: kernel rejected GkControl.mentionsArm64State"
  | "arch3" =>
      let some mmapInfo := env.find? `Arm64.Oracle.mmap
        | throw <| IO.userError "gk-control arch3: Arm64.Oracle.mmap not in env"
      let retTy := mmapInfo.type.bindingBody!
      let declName := `GkControl.readDefaultOracleMmap
      let declVal := Expr.app (Expr.const `Arm64.Oracle.mmap []) (Expr.const `Arm64.Process.defaultOracle [])
      let decl := Declaration.defnDecl
        (mkDefinitionValEx declName [] retTy declVal (.regular 1) .safe [declName])
      match env.addDeclCore 0 4096 decl none (doCheck := true) with
      | .ok env' =>
          IO.println s!"# GK_CONTROL=arch3: kernel-checked `def {declName} := Arm64.Oracle.mmap Arm64.Process.defaultOracle` via addDeclCore"
          return (env', allowMap, roots.push declName)
      | .error _ =>
          throw <| IO.userError "gk-control arch3: kernel rejected GkControl.readDefaultOracleMmap"
  | _ => throw <| IO.userError s!"unsupported gk-control '{cid}'"

/-- Audit the direct, type, value, and combined dependency cones of `root`. -/
unsafe def auditRoot (env : Environment) (cache : IO.Ref (Std.HashMap Name ConstEdges))
    (denyPats : Array DenyPattern) (allowMap : Std.HashMap Name String)
    (cfg : CliConfig) (root : Name) : IO (Bool × Array DenyHit × Array AllowHit) := do
  let allowLocal := cfg.gkControl.isSome
  let rootEdges ← getEdgesCached env cfg.synthInductAux cache root
  let rootMod? ← definingModWithPolicy? env allowLocal root

  let mut directOrigin : Std.HashMap Name String := {}
  directOrigin := directOrigin.insert root "self"
  let mut directOrder : Array Name := #[root]
  for c in rootEdges.typeDeps do
    if !directOrigin.contains c then
      directOrigin := directOrigin.insert c "type"
      directOrder := directOrder.push c
  for c in rootEdges.valueDeps do
    match directOrigin[c]? with
    | none =>
        directOrigin := directOrigin.insert c "value"
        directOrder := directOrder.push c
    | some "type" =>
        directOrigin := directOrigin.insert c "type+value"
    | some _ => pure ()

  let mut directDeny : Array (Name × String × String) := #[]
  for c in directOrder do
    let m? ← definingModWithPolicy? env allowLocal c
    if isModDenied denyPats m? && allowMap[c]?.isNone then
      let tag := directOrigin.getD c "direct"
      directDeny := directDeny.push (c, modLabel m?, tag)

  let combinedCone ← runConeBFS env allowLocal cfg.synthInductAux cache denyPats allowMap #[root] none
  let fixedPointOk := combinedCone.processed == combinedCone.enqueued && combinedCone.unexpandedEdges == 0
  let isClean := combinedCone.denyHits.isEmpty && fixedPointOk
  let mfStr := if isClean then "yes" else "no"
  let stStr := if isClean then "PASS" else "FAIL"

  if cfg.summaryOnly then
    IO.println s!"ROOT_RESULT: {dispConst root} [{modLabel rootMod?}] STATUS={stStr} MACHINE_FREE={mfStr} visited={combinedCone.visited} direct_deny={directDeny.size} transitive_deny={combinedCone.denyHits.size} allow_hits={combinedCone.allowHits.size}"
    return (isClean, combinedCone.denyHits, combinedCone.allowHits)

  let typeCone ← runConeBFS env allowLocal cfg.synthInductAux cache denyPats allowMap rootEdges.typeDeps (some root)
  let valueCone ← runConeBFS env allowLocal cfg.synthInductAux cache denyPats allowMap rootEdges.valueDeps (some root)

  IO.println s!"=== ROOT: {dispConst root} ==="
  IO.println s!"DEFINING_MODULE={modLabel rootMod?} KIND={rootEdges.kind}"
  IO.println s!"MACHINE_FREE={mfStr}"
  IO.println s!"STATUS={stStr}"
  IO.println s!"TOTAL_VISITED={combinedCone.visited} ({combinedCone.buckets.fmt})"
  IO.println s!"BFS_FIXED_POINT={fixedPointOk} (processed={combinedCone.processed}, enqueued={combinedCone.enqueued}, max_hops={combinedCone.maxHops}, unexpanded_edges={combinedCone.unexpandedEdges})"
  IO.println s!"DIRECT: checked={directOrder.size}, deny_hits={directDeny.size}"
  for (c, modStr, via) in directDeny do
    let hopStr := if c == root then "hops=0, self" else s!"hops=1, via {via}"
    if c == root then
      IO.println s!"  - [{hopStr}] {dispConst root} [{modStr}]"
    else
      IO.println s!"  - [{hopStr}] {dispConst root} -> {dispConst c} [{modStr}]"

  IO.println s!"TYPE_CONE: visited={typeCone.visited} ({typeCone.buckets.fmt}), deny_hits={typeCone.denyHits.size}"
  printHitList "  " typeCone.parent typeCone.denyHits cfg.maxChainHops cfg.maxHits

  IO.println s!"VALUE_CONE: visited={valueCone.visited} ({valueCone.buckets.fmt}), deny_hits={valueCone.denyHits.size}"
  printHitList "  " valueCone.parent valueCone.denyHits cfg.maxChainHops cfg.maxHits

  IO.println s!"TRANSITIVE_DENY_HITS={combinedCone.denyHits.size}"
  printHitList "  " combinedCone.parent combinedCone.denyHits cfg.maxChainHops cfg.maxHits

  if !combinedCone.allowHits.isEmpty then
    let allowLimit := if cfg.maxHits == 0 || combinedCone.allowHits.size ≤ cfg.maxHits then
        combinedCone.allowHits.size
      else
        cfg.maxHits
    IO.println s!"ALLOW_HITS={combinedCone.allowHits.size}"
    for i in [:allowLimit] do
      let ah := combinedCone.allowHits[i]!
      IO.println s!"  - {formatChainRaw combinedCone.parent ah.constName ah.defMod cfg.maxChainHops} ({ah.reason})"
    if combinedCone.allowHits.size > allowLimit then
      IO.println s!"  ... ({combinedCone.allowHits.size - allowLimit} more allow hits omitted; pass --max-hits 0 for all {combinedCone.allowHits.size})"

  return (isClean, combinedCone.denyHits, combinedCone.allowHits)

def normalizeWs (s : String) : String := Id.run do
  let mut out : String := ""
  let mut inWs : Bool := true
  for ch in s.toList do
    if ch.isWhitespace then
      if !inWs then
        inWs := true
    else
      if inWs && !out.isEmpty then
        out := out.push ' '
      inWs := false
      out := out.push ch
  return out

def escapeOneLine (s : String) : String :=
  let s1 := s.replace "\\" "\\\\"
  let s2 := s1.replace "\n" "\\n"
  let s3 := s2.replace "\r" "\\r"
  s3.replace "\t" "\\t"

def ppExprFullNames (env : Environment) (e : Expr) : IO String := do
  let mut opts : Options := {}
  opts := opts.setBool `pp.fullNames true
  let ctx : Core.Context := {
    fileName := "<machine-free-check>",
    fileMap := default,
    options := opts,
    maxHeartbeats := 0
  }
  let st : Core.State := { env := env }
  let ((fmt, _), _) ← (Meta.ppExpr e).run {} {} |>.toIO ctx st
  return fmt.pretty 1000000

def loadExpectedRootTypes (path : FilePath) : IO (Std.HashMap Name String) := do
  unless (← path.pathExists) do
    throw <| IO.userError s!"expected-root-type file does not exist: {path}"
  let raw ← IO.FS.readFile path
  let mut out : Std.HashMap Name String := {}
  let mut lineNo : Nat := 0
  for rawLine in raw.splitOn "\n" do
    lineNo := lineNo + 1
    let trimmed := rawLine.trimAscii.toString
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    let parts := trimmed.splitOn ":"
    if parts.length < 2 then
      throw <| IO.userError s!"{path}:{lineNo}: expected '<FullRootConst> : <expected type>'"
    let rName := parseName parts[0]!.trimAscii.toString
    let expTy := normalizeWs (String.intercalate ":" (parts.drop 1))
    out := out.insert rName expTy
  return out

def loadBridgeNames (path : FilePath) : IO (Array (Name × String)) := do
  unless (← path.pathExists) do
    throw <| IO.userError s!"bridges file does not exist: {path}"
  let raw ← IO.FS.readFile path
  let mut out : Array (Name × String) := #[]
  let mut lineNo : Nat := 0
  for rawLine in raw.splitOn "\n" do
    lineNo := lineNo + 1
    let code := ((rawLine.splitOn "#").head!).trimAscii.toString
    if code.isEmpty then continue
    let parts := code.splitOn ":"
    let bStr := parts[0]!.trimAscii.toString
    let note := if parts.length >= 2 then (String.intercalate ":" (parts.drop 1)).trimAscii.toString else ""
    unless validExactConstSyntax bStr do
      throw <| IO.userError s!"{path}:{lineNo}: invalid bridge constant name '{bStr}'"
    out := out.push (parseName bStr, note)
  return out

/-- Try to decompose `CompRefinesCliR {ω} Agree R dirs` or `CompRefinesCli {ω} Agree R` (including
1-step unfolding of an abbreviation/definition like `CompRefinesCliModel`). -/
def decomposeCompRefinesCli? (env : Environment) (ty : Expr) :
    IO (Option (String × String × String × String × String)) := do
  let candExpr := match ty.consumeMData with
    | .const dName _ =>
        match env.find? dName with
        | some (.defnInfo dv) => dv.value.consumeMData
        | _ => ty.consumeMData
    | other => other
  let fn := candExpr.getAppFn
  let args := candExpr.getAppArgs
  match fn with
  | .const fnName _ =>
      if fnName == `DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliR && args.size == 4 then
        let wStr ← ppExprFullNames env args[0]!
        let aStr ← ppExprFullNames env args[1]!
        let rStr ← ppExprFullNames env args[2]!
        let dStr ← ppExprFullNames env args[3]!
        return some ("CompRefinesCliR", normalizeWs wStr, normalizeWs aStr, normalizeWs rStr, normalizeWs dStr)
      else if fnName == `DY.Libsignal.Composed.Refinement.Cli.CompRefinesCli && args.size == 3 then
        let wStr ← ppExprFullNames env args[0]!
        let aStr ← ppExprFullNames env args[1]!
        let rStr ← ppExprFullNames env args[2]!
        return some ("CompRefinesCli (dirs := DY.Libsignal.Composed.Refinement.Cli.initDirs)",
          normalizeWs wStr, normalizeWs aStr, normalizeWs rStr, "DY.Libsignal.Composed.Refinement.Cli.initDirs")
      else
        return none
  | _ => return none

/-- Emit `--root-report` scope, type, bridge-coverage, axiom/reduction, and residual sections. -/
unsafe def emitRootReport (env : Environment) (allowLocal : Bool)
    (cache : IO.Ref (Std.HashMap Name ConstEdges))
    (exemptSpecs defaultClosure : Std.HashSet Name)
    (cfg : CliConfig) (resolvedRoots : Array Name) (unionCone : ConeResult) :
    IO (Bool × Array String) := do
  let mut ok := true
  let mut reasons : Array String := #[]

  IO.println "=== ROOT_SCOPE_CHECK (E2) ==="
  let mut outsideRoots : Array (Name × String) := #[]
  for r in resolvedRoots do
    let m? ← definingModWithPolicy? env allowLocal r
    match m? with
    | some m =>
        unless defaultClosure.contains m do
          if cfg.allowScratchFixtureRoots then
            IO.println s!"# ROOT_SCOPE_NOTE: --allow-scratch-fixture-roots active; permitting scratch fixture root {dispConst r} [{m}] outside lakefile default targets"
          else
            outsideRoots := outsideRoots.push (r, m.toString)
    | none =>
        unless cfg.allowScratchFixtureRoots || allowLocal do
          outsideRoots := outsideRoots.push (r, "<local>")
  if !outsideRoots.isEmpty then
    ok := false
    reasons := reasons.push s!"ROOT_OUTSIDE_DEFAULT_TARGETS={outsideRoots.size}"
    IO.println s!"ROOT_DEFAULT_TARGET_SCOPE=FAIL ({outsideRoots.size} root(s) outside lakefile default-target closure)"
    for (r, mStr) in outsideRoots do
      IO.println s!"  - ROOT_OUTSIDE_DEFAULT_TARGETS: {dispConst r} [{mStr}]"
  else
    IO.println s!"ROOT_DEFAULT_TARGET_SCOPE=PASS (roots={resolvedRoots.size}, scratch_fixture_override={cfg.allowScratchFixtureRoots})"

  let expectedMap ← match cfg.expectedRootTypeFile with
    | some p => loadExpectedRootTypes p
    | none   => pure ({} : Std.HashMap Name String)
  IO.println "=== ROOT_TYPE_REPORT (R-a) ==="
  let mut ghostHitsAll : Array (Name × Name × String) := #[]
  let mut typeMismatchCount : Nat := 0
  for r in resolvedRoots do
    let some info := env.find? r | continue
    let rMod? ← definingModWithPolicy? env allowLocal r
    let ppRaw ← ppExprFullNames env info.type
    let ppNorm := normalizeWs ppRaw
    IO.println s!"ROOT_TYPE: {dispConst r} [{modLabel rMod?}] : {ppNorm}"
    if let some (headKind, wStr, aStr, rStr, dStr) ← decomposeCompRefinesCli? env info.type then
      IO.println s!"  COMPREFINES_CLI_DECOMP: head={headKind} | omega={wStr} | Agree={aStr} | R={rStr} | dirs={dStr}"
    else if let .defnInfo dv := info then
      if let some (headKind, wStr, aStr, rStr, dStr) ← decomposeCompRefinesCli? env dv.value then
        let ppVal ← ppExprFullNames env dv.value
        IO.println s!"  ROOT_DEF_VALUE: {normalizeWs ppVal}"
        IO.println s!"  COMPREFINES_CLI_DECOMP: head={headKind} | omega={wStr} | Agree={aStr} | R={rStr} | dirs={dStr}"
    let typeConsts := sortNames (collectExprConsts env info.type)
    IO.println s!"  ROOT_TYPE_CONSTS={typeConsts.size}"
    for tc in typeConsts do
      let tm? ← definingModWithPolicy? env allowLocal tc
      let ghostFlag := if isA2HeapGhostConst tc then " [A2_GHOST!]" else ""
      IO.println s!"    - {dispConst tc}\t{modLabel tm?}{ghostFlag}"
      if isA2HeapGhostConst tc then
        ghostHitsAll := ghostHitsAll.push (r, tc, modLabel tm?)
    if cfg.expectedRootTypeFile.isSome then
      match expectedMap[r]? with
      | some expNorm =>
          if ppNorm == expNorm then
            IO.println s!"  ROOT_EXPECTED_TYPE_MATCH=PASS"
          else
            typeMismatchCount := typeMismatchCount + 1
            IO.println s!"  ROOT_EXPECTED_TYPE_MATCH=FAIL\n    expected: {expNorm}\n    actual:   {ppNorm}"
      | none =>
          typeMismatchCount := typeMismatchCount + 1
          IO.println s!"  ROOT_EXPECTED_TYPE_MATCH=FAIL (missing entry for '{r}' in --expected-root-type-file)"

  if !ghostHitsAll.isEmpty then
    ok := false
    reasons := reasons.push s!"ROOT_TYPE_A2_GHOSTS={ghostHitsAll.size}"
    IO.println s!"ROOT_TYPE_GHOST_FREE=FAIL ({ghostHitsAll.size} A2 heap-layout ghost occurrence(s) in root types)"
  else
    IO.println "ROOT_TYPE_GHOST_FREE=PASS (0 A2 heap-layout ghost constants in root types)"

  if cfg.expectedRootTypeFile.isSome then
    if typeMismatchCount > 0 then
      ok := false
      reasons := reasons.push s!"ROOT_EXPECTED_TYPE_MISMATCH={typeMismatchCount}"
      IO.println s!"SUMMARY_ROOT_EXPECTED_TYPE=FAIL (mismatches={typeMismatchCount})"
    else
      IO.println "SUMMARY_ROOT_EXPECTED_TYPE=PASS"

  IO.println "=== BRIDGE_COVERAGE (R-b) ==="
  let rootSet : NameSet := resolvedRoots.foldl (·.insert ·) {}
  match cfg.bridgesFile with
  | none =>
      IO.println "# (no --bridges-file supplied)"
  | some bp =>
      let bridges ← loadBridgeNames bp
      IO.println "bridge_const\tdefining_module\tstatus\tnote"
      for (bName, note) in bridges do
        let status :=
          if rootSet.contains bName then "root"
          else if unionCone.seenSet.contains bName then "in_root_cone"
          else if env.contains bName then "not_in_root_cone"
          else "not_in_env"
        let bModStr ← if env.contains bName then
            pure (modLabel (← definingModWithPolicy? env allowLocal bName))
          else
            pure "-"
        IO.println s!"{bName}\t{bModStr}\t{status}\t{note}"

  IO.println "=== AXIOM_AND_REDUCE_REPORT (S7) ==="
  let allSeenSorted := sortNames unionCone.seenSet
  let mut nonStd3PerRoot : Array (Name × Array Name) := #[]
  for r in resolvedRoots do
    let rCone ← runConeBFS env allowLocal cfg.synthInductAux cache #[] {} #[r] none
    let mut rAxioms : Array Name := #[]
    for c in sortNames rCone.seenSet do
      if let some (.axiomInfo _) := env.find? c then
        rAxioms := rAxioms.push c
    let badAx := rAxioms.filter (fun a => !std3Axioms.contains a)
    IO.println s!"ROOT_AXIOMS: {dispConst r} axioms={rAxioms.map dispConst} std3_only={badAx.isEmpty}"
    if !badAx.isEmpty then
      nonStd3PerRoot := nonStd3PerRoot.push (r, badAx)

  let mut badReduce : Array String := #[]
  for c in allSeenSorted do
    let mStr := modLabel (← definingModWithPolicy? env allowLocal c)
    if c == `Lean.trustCompiler then
      badReduce := badReduce.push s!"{dispConst c} [{mStr}] (Lean.trustCompiler forbidden)"
    else if isNativeDecideAxiomName c then
      badReduce := badReduce.push s!"{dispConst c} [{mStr}] (native_decide axiom forbidden)"
    else if let some (.axiomInfo _) := env.find? c then
      if !std3Axioms.contains c && c != ``sorryAx && !isAllowedBvdAxiom env c then
        badReduce := badReduce.push s!"{dispConst c} [{mStr}] (non-std3 non-bv_decide axiom)"
    if c == `Lean.ofReduceBool || c == `Lean.ofReduceNat then
      for u in allSeenSorted do
        let uEdges ← getEdgesCached env cfg.synthInductAux cache u
        if uEdges.typeDeps.contains c || uEdges.valueDeps.contains c then
          if !isBvdAuxConst env u then
            let uMod := modLabel (← definingModWithPolicy? env allowLocal u)
            badReduce := badReduce.push s!"{dispConst c} used by non-bv_decide decl {dispConst u} [{uMod}]"

  let axiomsOk := nonStd3PerRoot.isEmpty
  let reduceOk := badReduce.isEmpty
  if !axiomsOk then
    ok := false
    reasons := reasons.push s!"NON_STD3_ROOTS={nonStd3PerRoot.size}"
    IO.println s!"ROOT_AXIOMS_STD3=FAIL ({nonStd3PerRoot.size} root(s) outside std3)"
    for (r, axs) in nonStd3PerRoot do
      IO.println s!"  - {dispConst r}: non_std3={axs.map dispConst}"
  else
    IO.println "ROOT_AXIOMS_STD3=PASS (all roots depend only on {propext, Classical.choice, Quot.sound})"

  if !reduceOk then
    ok := false
    reasons := reasons.push s!"REDUCE_VIOLATIONS={badReduce.size}"
    IO.println s!"ROOT_REDUCE_GUARD=FAIL ({badReduce.size} violation(s))"
    for msg in badReduce do
      IO.println s!"  - {msg}"
  else
    IO.println "ROOT_REDUCE_GUARD=PASS (0 native_decide / trustCompiler / unguarded ofReduceBool/ofReduceNat)"

  let mut nonCoreSelf : NameSet := {}
  for c in allSeenSorted do
    let m? ← definingModWithPolicy? env allowLocal c
    match m? with
    | some m => if !isCoreModName m then nonCoreSelf := nonCoreSelf.insert c
    | none   => nonCoreSelf := nonCoreSelf.insert c

  -- Compute `reachesNonCore`: constants in `unionCone` with at least one strict dependency `v != c`
  -- defined outside core (`Init`/`Std`/`Lean`/`Mathlib`/etc.), via reverse propagation.
  let mut revInCone : Std.HashMap Name (Array Name) := {}
  for u in allSeenSorted do
    let ue ← getEdgesCached env cfg.synthInductAux cache u
    for v in ue.typeDeps ++ ue.valueDeps do
      if unionCone.seenSet.contains v && v != u then
        revInCone := pushMapArr revInCone v u
  let mut reachesNonCore : NameSet := {}
  let mut qNc : Array Name := #[]
  for v in allSeenSorted do
    if nonCoreSelf.contains v then
      for u in revInCone.getD v #[] do
        if !reachesNonCore.contains u then
          reachesNonCore := reachesNonCore.insert u
          qNc := qNc.push u
  let mut qi : Nat := 0
  while qi < qNc.size do
    let cur := qNc[qi]!
    qi := qi + 1
    for u in revInCone.getD cur #[] do
      if !reachesNonCore.contains u then
        reachesNonCore := reachesNonCore.insert u
        qNc := qNc.push u

  let mut eModRows : Array String := #[]
  let mut coreLitRows : Array String := #[]
  let mut strLitRows : Array String := #[]
  let mut bvdAuxRows : Array String := #[]

  for c in allSeenSorted do
    let m? ← definingModWithPolicy? env allowLocal c
    let mStr := modLabel m?
    let edges ← getEdgesCached env cfg.synthInductAux cache c
    let scan := scanConstLiterals env c
    if let some m := m? then
      if exemptSpecs.contains m then
        eModRows := eModRows.push s!"E\t{dispConst c}\t{mStr}\t{edges.kind}"
    if nonCoreSelf.contains c && !reachesNonCore.contains c then
      if scan.hasNatLit || scan.hasBitVecLit || scan.hasByteList then
        let mut tags : List String := []
        if scan.hasNatLit then tags := tags ++ ["nat"]
        if scan.hasBitVecLit then tags := tags ++ ["bitvec"]
        if scan.hasByteList then tags := tags ++ ["list"]
        let eFlag := match m? with
          | some m => if exemptSpecs.contains m then "E" else "-"
          | none   => "-"
        coreLitRows := coreLitRows.push s!"{eFlag}\t{dispConst c}\t{mStr}\t{String.intercalate "," tags}"
    for sLit in scan.stringLits do
      let eFlag := match m? with
        | some m => if exemptSpecs.contains m then "E" else "-"
        | none   => "-"
      strLitRows := strLitRows.push s!"{eFlag}\t{dispConst c}\t{mStr}\t\"{escapeOneLine sLit}\""
    if isBvdAuxConst env c then
      bvdAuxRows := bvdAuxRows.push s!"BVD_AUX\t{dispConst c}\t{mStr}\t{edges.kind}"

  IO.println "=== RESIDUAL_REPORT (E1) ==="
  IO.println s!"RESIDUAL_E_MODULE_CONSTS={eModRows.size}"
  for row in eModRows do
    IO.println s!"  {row}"
  IO.println s!"RESIDUAL_CORE_ONLY_LITERAL_CONSTS={coreLitRows.size}"
  for row in coreLitRows do
    IO.println s!"  {row}"
  IO.println s!"RESIDUAL_STRING_LITERALS={strLitRows.size}"
  for row in strLitRows do
    IO.println s!"  {row}"
  IO.println s!"RESIDUAL_BVD_AUX={bvdAuxRows.size}"
  for row in bvdAuxRows do
    IO.println s!"  {row}"

  return (ok, reasons)

def classifyModuleTree (m : Name) : String :=
  let segs := m.toString.splitOn "."
  match segs with
  | [] => "<anon>"
  | [top] => top
  | top :: sub :: _ =>
      if top == "LibsignalBinary" || top == "Symbolic" || top == "Computational" || top == "Arm64" then
        s!"{top}.{sub}"
      else
        top

def isSpecificationsModule (m : Name) : Bool :=
  (m.toString.splitOn ".").contains "Specifications"

/-- Fail closed if `--exempt-specs-file` lists any module without a `Specifications` path segment. -/
def validateExemptSpecsModules (path : FilePath) (exemptSpecs : Std.HashSet Name) : IO Unit := do
  let sorted := exemptSpecs.toArray.qsort (fun a b => a.toString < b.toString)
  for m in sorted do
    unless isSpecificationsModule m do
      throw <| IO.userError s!"{path}: exempt-specs entry '{m}' lacks a 'Specifications' path segment (fail-closed)"

structure CriterionModRow where
  modName         : Name
  modStr          : String
  tree            : String
  nConsts         : Nat
  nTainted        : Nat
  exampleConst    : String
  witnessChain    : String
  inE             : Bool
  isSpecs         : Bool
  deriving Inhabited

structure CriterionSummary where
  defaultClosureSet : Std.HashSet Name := {}
  rows              : Array CriterionModRow := #[]
  d2Findings        : Array CriterionModRow := #[]
  machineLevelMods  : Array CriterionModRow := #[]
  partCMods         : Array CriterionModRow := #[]
  fixedPointOk      : Bool := false
  distinctAllowed   : Std.HashSet Name := {}
  deriving Inhabited

def computeEnvImportClosure (env : Environment) (seedMods : Array Name) : IO (Std.HashSet Name) := do
  let mut nameToIdx : Std.HashMap Name Nat := {}
  for i in [:env.header.moduleNames.size] do
    nameToIdx := nameToIdx.insert env.header.moduleNames[i]! i
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for s in seedMods do
    unless nameToIdx.contains s do
      throw <| IO.userError s!"default-target seed module '{s}' not found in imported Environment"
    unless seen.contains s do
      seen := seen.insert s
      queue := queue.push s
  let mut qi : Nat := 0
  while qi < queue.size do
    let cur := queue[qi]!
    qi := qi + 1
    if let some idx := nameToIdx[cur]? then
      for imp in env.header.moduleData[idx]!.imports do
        let im := imp.module
        if nameToIdx.contains im && !seen.contains im then
          seen := seen.insert im
          queue := queue.push im
  return seen

/-- Reconstruct witness chain `c -> next[c] -> ... -> base` (capped at `<= 8` hops). -/
def formatWitnessChain (witnessNext : Std.HashMap Name Name)
    (defModMap : Std.HashMap Name String) (start : Name) : String := Id.run do
  let mut chain : Array Name := #[start]
  let mut cur := start
  let mut fuel : Nat := witnessNext.size + 2
  while fuel > 0 do
    fuel := fuel - 1
    match witnessNext[cur]? with
    | some nxt =>
        if nxt == cur then break
        chain := chain.push nxt
        cur := nxt
    | none => break
  let endMod := defModMap.getD cur "?"
  let (hops, rendered) := renderTruncatedNodes chain 8
  return s!"[hops={hops}] {rendered} [{endMod}]"

structure CriterionBatchAcc where
  defaultClosureAll : Std.HashSet Name := {}
  analyzedMods      : Std.HashSet Name := {}
  globalUSet        : NameSet := {}
  globalBaseTainted : NameSet := {}
  globalTainted     : NameSet := {}
  globalDist        : Std.HashMap Name Nat := {}
  globalWitnessNext : Std.HashMap Name Name := {}
  globalDefModMap   : Std.HashMap Name String := {}
  globalRows        : Array CriterionModRow := #[]
  distinctAllowed   : Std.HashSet Name := {}
  fixedPointOk      : Bool := true
  allowVal          : AllowBatchValidation := {}
  deriving Inhabited

/-- Analyze one loaded `env` batch incrementally into `CriterionBatchAcc`.
Because `batchClosure` is downward-closed under imports and `analyzedMods` is downward-closed under
`reachesAB` imports, every outgoing edge from a newly analyzed module lands either in `analyzedMods`
(whose taint, shortest distance, and lexicographic `witnessNext` are already final) or in `newU`. -/
unsafe def stepCriterionBatch (acc0 : CriterionBatchAcc) (env : Environment) (cfg : CliConfig)
    (denyPats : Array DenyPattern) (allowMap : Std.HashMap Name String)
    (exemptSpecs : Std.HashSet Name) (batchSeeds : Array Name) : IO CriterionBatchAcc := do
  let allowVal := recordAllowMapInBatchEnv acc0.allowVal env allowMap
  let batchClosure ← computeEnvImportClosure env batchSeeds
  let mut defaultClosureAll := acc0.defaultClosureAll
  for m in batchClosure do
    defaultClosureAll := defaultClosureAll.insert m

  let nMods := env.header.moduleNames.size
  let mut nameToIdx : Std.HashMap Name Nat := {}
  let mut modInAB : Array Bool := Array.replicate nMods false
  for i in [:nMods] do
    let m := env.header.moduleNames[i]!
    nameToIdx := nameToIdx.insert m i
    modInAB := modInAB.set! i (isModDenied denyPats (some m))

  -- Compute whether each module transitively imports a denied module.
  let mut stateArr : Array UInt8 := Array.replicate nMods 0 -- 0=unvisited, 1=false, 2=true
  for i in [:nMods] do
    if stateArr[i]! == 0 then
      let mut stack : Array (Nat × Bool) := #[(i, false)]
      while !stack.isEmpty do
        let (u, expanded) := stack.back!
        stack := stack.pop
        if stateArr[u]! != 0 then continue
        if !expanded then
          stack := stack.push (u, true)
          for imp in env.header.moduleData[u]!.imports do
            if let some v := nameToIdx[imp.module]? then
              if stateArr[v]! == 0 then
                stack := stack.push (v, false)
        else
          let mut r := modInAB[u]!
          if !r then
            for imp in env.header.moduleData[u]!.imports do
              if let some v := nameToIdx[imp.module]? then
                if stateArr[v]! == 2 then
                  r := true
          stateArr := stateArr.set! u (if r then 2 else 1)

  let tBatchStart ← IO.monoMsNow
  let mut modImportFixedOk := true
  let mut newCandModIndices : Array Nat := #[]
  for i in [:nMods] do
    let m := env.header.moduleNames[i]!
    let lhs := stateArr[i]! == 2
    let mut rhs := modInAB[i]!
    if !rhs then
      for imp in env.header.moduleData[i]!.imports do
        if let some v := nameToIdx[imp.module]? then
          if stateArr[v]! == 2 then rhs := true
    if lhs != rhs then modImportFixedOk := false
    if lhs && !modInAB[i]! && batchClosure.contains m && !acc0.analyzedMods.contains m then
      newCandModIndices := newCandModIndices.push i

  if newCandModIndices.isEmpty then
    return { acc0 with
      defaultClosureAll,
      fixedPointOk := acc0.fixedPointOk && modImportFixedOk,
      allowVal
    }

  let cache ← IO.mkRef ({} : Std.HashMap Name ConstEdges)
  let mut defModMemo : Std.HashMap Name (Option Name) := {}
  let mut dReachesMemo : Std.HashMap Name Bool := {}
  let mut analyzedMods := acc0.analyzedMods
  let mut globalUSet := acc0.globalUSet
  let mut globalBaseTainted := acc0.globalBaseTainted
  let mut globalTainted := acc0.globalTainted
  let mut globalDist := acc0.globalDist
  let mut globalWitnessNext := acc0.globalWitnessNext
  let mut globalDefModMap := acc0.globalDefModMap
  let mut globalRows := acc0.globalRows
  let mut distinctAllowed := acc0.distinctAllowed

  let mut newUSet : NameSet := {}
  let mut uWork : Array Name := #[]
  for idx in newCandModIndices do
    analyzedMods := analyzedMods.insert env.header.moduleNames[idx]!
    for c in env.header.moduleData[idx]!.constNames do
      unless globalUSet.contains c || newUSet.contains c do
        newUSet := newUSet.insert c
        uWork := uWork.push c

  let initWorkSize := uWork.size
  let mut precompDeps : Array NameSet := #[]
  if !cfg.legacySlowEdges && initWorkSize > 0 then
    let nSlices : Nat := if initWorkSize < 64 then 1 else 8
    let chunkSize := (initWorkSize + nSlices - 1) / nSlices
    let uSnap := uWork
    let synthFlag := cfg.synthInductAux
    let mut tasks : Array (Task (Array NameSet)) := Array.mkEmpty nSlices
    for s in [:nSlices] do
      let lo := s * chunkSize
      if lo < initWorkSize then
        let hi := Nat.min initWorkSize (lo + chunkSize)
        tasks := tasks.push (Task.spawn (prio := .default) fun _ =>
          computeCriterionSliceDeps env synthFlag uSnap lo hi)
    precompDeps := Array.mkEmpty initWorkSize
    for t in tasks do
      for ds in t.get do
        precompDeps := precompDeps.push ds

  let mut localBaseTainted : NameSet := {}
  let mut revAdj : Std.HashMap Name (Array Name) := {}
  let mut fwdAdj : Std.HashMap Name (Array Name) := {}
  let mut fallbackProjMemo : Std.HashMap (Name × Nat) Name := {}

  let mut wi : Nat := 0
  while wi < uWork.size do
    let curIdx := wi
    let c := uWork[wi]!
    wi := wi + 1
    let m? ← match defModMemo[c]? with
      | some cached => pure cached
      | none =>
          let r ← definingModWithPolicy? env false c
          defModMemo := defModMemo.insert c r
          pure r
    let mStr := modLabel m?
    globalDefModMap := globalDefModMap.insert c mStr
    let deniedSelf := match m? with
      | some m =>
          match nameToIdx[m]? with
          | some midx => modInAB[midx]!
          | none      => isModDenied denyPats (some m)
      | none => false
    if deniedSelf then
      if allowMap.contains c then
        distinctAllowed := distinctAllowed.insert c
      else
        if curIdx < precompDeps.size then
          precompDeps := precompDeps.set! curIdx {}
        localBaseTainted := localBaseTainted.insert c
        globalBaseTainted := globalBaseTainted.insert c
        fwdAdj := fwdAdj.insert c #[]
        continue
    let modOptReachesAB := fun (modOpt : Option Name) =>
      match modOpt with
      | some dm =>
          match nameToIdx[dm]? with
          | some didx => stateArr[didx]! == 2
          | none      => isModDenied denyPats (some dm)
      | none => true
    let mut cTargets : Array Name := #[]
    if cfg.legacySlowEdges then
      let edges ← getEdgesCached env cfg.synthInductAux cache c
      for d in edges.typeDeps ++ edges.valueDeps do
        let dm? ← match defModMemo[d]? with
          | some cached => pure cached
          | none =>
              let r ← definingModWithPolicy? env false d
              defModMemo := defModMemo.insert d r
              pure r
        let rawDm? ← rawModuleOf? env d
        let dReaches := modOptReachesAB dm? || modOptReachesAB rawDm?
        if dReaches then
          cTargets := cTargets.push d
          unless globalUSet.contains d || newUSet.contains d do
            newUSet := newUSet.insert d
            uWork := uWork.push d
    else
      let depSet ← if curIdx < precompDeps.size then do
        let ds := precompDeps[curIdx]!
        precompDeps := precompDeps.set! curIdx {}
        pure ds
      else do
        let (ds, pm') := computeCriterionConstDeps env cfg.synthInductAux fallbackProjMemo c
        fallbackProjMemo := pm'
        pure ds
      for d in depSet do
        let dReaches ← match dReachesMemo[d]? with
          | some cached => pure cached
          | none =>
              let dm? ← match defModMemo[d]? with
                | some cached => pure cached
                | none =>
                    let r ← definingModWithPolicy? env false d
                    defModMemo := defModMemo.insert d r
                    pure r
              -- Realized auxiliaries (`eq_n`, `match_n`, `splitter`, ...) inherit their parent's
              -- module via `definingModWithPolicy?` so benign core realizations are not base-tainted,
              -- but still elaborate in `rawModuleOf?`; traverse whenever either module reaches denied modules.
              let rawDm? ← rawModuleOf? env d
              let r := modOptReachesAB dm? || modOptReachesAB rawDm?
              dReachesMemo := dReachesMemo.insert d r
              pure r
        if dReaches then
          cTargets := cTargets.push d
          unless globalUSet.contains d || newUSet.contains d do
            newUSet := newUSet.insert d
            uWork := uWork.push d
    fwdAdj := fwdAdj.insert c cTargets
    for d in cTargets do
      unless globalUSet.contains d do
        revAdj := pushMapArr revAdj d c
  cache.set {}

  let newUSorted := sortNames newUSet
  let priorTainted := globalTainted

  if cfg.oneStep then
    for c in newUSorted do
      if localBaseTainted.contains c then
        globalTainted := globalTainted.insert c
        globalDist := globalDist.insert c 0
        globalWitnessNext := globalWitnessNext.insert c c
    for c in newUSorted do
      unless globalTainted.contains c do
        let mut bestBase : Option Name := none
        for d in fwdAdj.getD c #[] do
          if globalBaseTainted.contains d then
            match bestBase with
            | none => bestBase := some d
            | some prev => if d.toString < prev.toString then bestBase := some d
        if let some b := bestBase then
          globalTainted := globalTainted.insert c
          globalDist := globalDist.insert c 1
          globalWitnessNext := globalWitnessNext.insert c b
  else
    let mut curLayer : Array Name := #[]
    let mut pendingBuckets : Std.HashMap Nat (Array (Name × Name)) := {}
    let mut maxPendingDist : Nat := 0
    for c in newUSorted do
      if localBaseTainted.contains c then
        globalTainted := globalTainted.insert c
        globalDist := globalDist.insert c 0
        globalWitnessNext := globalWitnessNext.insert c c
        curLayer := curLayer.push c
      else
        let mut bestPrior? : Option (Nat × Name) := none
        for dTarget in fwdAdj.getD c #[] do
          if priorTainted.contains dTarget then
            let candD := globalDist.getD dTarget 0 + 1
            match bestPrior? with
            | none => bestPrior? := some (candD, dTarget)
            | some (prevD, prevT) =>
                if candD < prevD || (candD == prevD && dTarget.toString < prevT.toString) then
                  bestPrior? := some (candD, dTarget)
        if let some (bestD, bestT) := bestPrior? then
          pendingBuckets := pushMapArr pendingBuckets bestD (c, bestT)
          if bestD > maxPendingDist then
            maxPendingDist := bestD

    let mut d : Nat := 0
    while !curLayer.isEmpty || d < maxPendingDist do
      let sortedLayer := curLayer.qsort (fun a b => a.toString < b.toString)
      let mut nextCands : Std.HashMap Name Name := {}
      for v in sortedLayer do
        for u in revAdj.getD v #[] do
          unless globalTainted.contains u do
            match nextCands[u]? with
            | none => nextCands := nextCands.insert u v
            | some prev => if v.toString < prev.toString then nextCands := nextCands.insert u v
      for (u, bestT) in pendingBuckets.getD (d + 1) #[] do
        unless globalTainted.contains u do
          match nextCands[u]? with
          | none => nextCands := nextCands.insert u bestT
          | some prev => if bestT.toString < prev.toString then nextCands := nextCands.insert u bestT
      let sortedNext := nextCands.toArray.qsort (fun a b => a.1.toString < b.1.toString)
      let mut nextLayer : Array Name := #[]
      for (u, bestNext) in sortedNext do
        globalTainted := globalTainted.insert u
        globalDist := globalDist.insert u (d + 1)
        globalWitnessNext := globalWitnessNext.insert u bestNext
        nextLayer := nextLayer.push u
      curLayer := nextLayer
      d := d + 1

  let mut fpMismatches : Nat := 0
  if !cfg.oneStep then
    for c in newUSorted do
      let lhs := globalTainted.contains c
      let rhs := localBaseTainted.contains c || (fwdAdj.getD c #[]).any (fun d => globalTainted.contains d)
      if lhs != rhs then
        fpMismatches := fpMismatches + 1
  let batchFixedOk := modImportFixedOk && (cfg.oneStep || fpMismatches == 0)

  for c in newUSorted do
    globalUSet := globalUSet.insert c

  for idx in newCandModIndices do
    let m := env.header.moduleNames[idx]!
    let mStr := m.toString
    let decls := env.header.moduleData[idx]!.constNames
    let mut nTainted : Nat := 0
    let mut bestConst? : Option (Name × Nat) := none
    for c in decls do
      if globalTainted.contains c then
        nTainted := nTainted + 1
        let dc := globalDist.getD c 0
        match bestConst? with
        | none => bestConst? := some (c, dc)
        | some (prevC, prevD) =>
            if dc < prevD || (dc == prevD && c.toString < prevC.toString) then
              bestConst? := some (c, dc)
    let (exStr, chainStr) := match bestConst? with
      | none => ("-", "-")
      | some (bc, _) => (dispConst bc, formatWitnessChain globalWitnessNext globalDefModMap bc)
    let inE := exemptSpecs.contains m
    let isSpecs := isSpecificationsModule m
    globalRows := globalRows.push {
      modName := m,
      modStr := mStr,
      tree := classifyModuleTree m,
      nConsts := decls.size,
      nTainted := nTainted,
      exampleConst := exStr,
      witnessChain := chainStr,
      inE := inE,
      isSpecs := isSpecs
    }

  let tBatchEnd ← IO.monoMsNow
  IO.eprintln s!"[machine-free-check] criterion batch: seeds={batchSeeds.size} new_cand_mods={newCandModIndices.size} new_u_consts={newUSorted.size} analysis_ms={tBatchEnd - tBatchStart}"

  return {
    defaultClosureAll,
    analyzedMods,
    globalUSet,
    globalBaseTainted,
    globalTainted,
    globalDist,
    globalWitnessNext,
    globalDefModMap,
    globalRows,
    distinctAllowed,
    fixedPointOk := acc0.fixedPointOk && batchFixedOk,
    allowVal
  }

def nameSepChar : Char := Char.ofNat 31
def nameSepStr : String := String.singleton nameSepChar

def escapeBatchField (s : String) : String :=
  if !(s.any (fun c => c == '\\' || c == '\n' || c == '\r' || c == '\t' || c == nameSepChar)) then
    s
  else Id.run do
    let mut buf : Array Char := #[]
    for c in s.toList do
      if c == '\\' then buf := buf.push '\\' |>.push '\\'
      else if c == '\n' then buf := buf.push '\\' |>.push 'n'
      else if c == '\r' then buf := buf.push '\\' |>.push 'r'
      else if c == '\t' then buf := buf.push '\\' |>.push 't'
      else if c == nameSepChar then buf := buf.push '\\' |>.push 'x'
      else buf := buf.push c
    return String.ofList buf.toList

partial def unescapeBatchFieldLoop (acc : Array Char) : List Char → Array Char
  | [] => acc
  | '\\' :: 'n' :: rest => unescapeBatchFieldLoop (acc.push '\n') rest
  | '\\' :: 'r' :: rest => unescapeBatchFieldLoop (acc.push '\r') rest
  | '\\' :: 't' :: rest => unescapeBatchFieldLoop (acc.push '\t') rest
  | '\\' :: 'x' :: rest => unescapeBatchFieldLoop (acc.push nameSepChar) rest
  | '\\' :: '\\' :: rest => unescapeBatchFieldLoop (acc.push '\\') rest
  | c :: rest => unescapeBatchFieldLoop (acc.push c) rest

def unescapeBatchField (s : String) : String :=
  if !(s.contains '\\') then s
  else String.ofList (unescapeBatchFieldLoop #[] s.toList).toList

def encodeNameParts : Name → List String → List String
  | .anonymous, acc => acc
  | .str pre seg, acc => encodeNameParts pre ((s!"s:{escapeBatchField seg}") :: acc)
  | .num pre k, acc => encodeNameParts pre ((s!"n:{k}") :: acc)

def encodeNameExact (n : Name) : String :=
  match n with
  | .anonymous => "a"
  | _ => String.intercalate nameSepStr (encodeNameParts n [])

def decodeNameExact (s : String) : IO Name := do
  if s == "a" then return .anonymous
  let mut cur : Name := .anonymous
  for part in s.splitOn nameSepStr do
    if part.startsWith "s:" then
      cur := Name.mkStr cur (unescapeBatchField (part.drop 2).toString)
    else if part.startsWith "n:" then
      match (part.drop 2).toString.toNat? with
      | some k => cur := Name.mkNum cur k
      | none   => throw <| IO.userError s!"corrupt batch-state numeric Name segment '{part}'"
    else
      throw <| IO.userError s!"corrupt batch-state Name segment '{part}'"
  return cur

def stripCrLf (s : String) : String :=
  let s1 := if s.endsWith "\n" then (s.dropEnd 1).toString else s
  if s1.endsWith "\r" then (s1.dropEnd 1).toString else s1

def saveCriterionBatchAcc (statePath : FilePath) (acc : CriterionBatchAcc) : IO Unit := do
  let tmpPath : FilePath := FilePath.mk (statePath.toString ++ ".tmp")
  IO.FS.withFile tmpPath .write fun h => do
    h.putStrLn s!"FP\t{if acc.fixedPointOk then "1" else "0"}"
    for m in acc.defaultClosureAll.toArray do
      h.putStrLn s!"DC\t{encodeNameExact m}"
    for m in acc.analyzedMods.toArray do
      h.putStrLn s!"AM\t{encodeNameExact m}"
    for c in acc.distinctAllowed.toArray do
      h.putStrLn s!"DA\t{encodeNameExact c}"
    for c in acc.allowVal.foundConsts.toArray do
      h.putStrLn s!"AF\t{encodeNameExact c}"
    for (c, msg) in acc.allowVal.badErrors.toArray do
      h.putStrLn s!"AE\t{encodeNameExact c}\t{escapeBatchField msg}"
    for r in acc.globalRows do
      h.putStrLn s!"ROW\t{encodeNameExact r.modName}\t{escapeBatchField r.modStr}\t{escapeBatchField r.tree}\t{r.nConsts}\t{r.nTainted}\t{escapeBatchField r.exampleConst}\t{escapeBatchField r.witnessChain}\t{if r.inE then "1" else "0"}\t{if r.isSpecs then "1" else "0"}"
    for c in acc.globalUSet do
      let defMod := acc.globalDefModMap.getD c "?"
      let isBase := if acc.globalBaseTainted.contains c then "1" else "0"
      let isTaint := if acc.globalTainted.contains c then "1" else "0"
      let dist := acc.globalDist.getD c 0
      let wn := match acc.globalWitnessNext[c]? with
        | some nxt => encodeNameExact nxt
        | none     => "a"
      h.putStrLn s!"U\t{encodeNameExact c}\t{escapeBatchField defMod}\t{isBase}\t{isTaint}\t{dist}\t{wn}"
  IO.FS.rename tmpPath statePath

def loadCriterionBatchAcc (statePath : FilePath) (summaryOnly : Bool) : IO CriterionBatchAcc := do
  let mut fixedPointOk : Bool := true
  let mut defaultClosureAll : Std.HashSet Name := {}
  let mut analyzedMods : Std.HashSet Name := {}
  let mut distinctAllowed : Std.HashSet Name := {}
  let mut foundConsts : Std.HashSet Name := {}
  let mut badErrors : Std.HashMap Name String := {}
  let mut globalRows : Array CriterionModRow := #[]
  let mut globalUSet : NameSet := {}
  let mut globalBaseTainted : NameSet := {}
  let mut globalTainted : NameSet := {}
  let mut globalDist : Std.HashMap Name Nat := {}
  let mut globalWitnessNext : Std.HashMap Name Name := {}
  let mut globalDefModMap : Std.HashMap Name String := {}
  let h ← IO.FS.Handle.mk statePath .read
  while true do
    let rawLine ← h.getLine
    if rawLine.isEmpty then break
    if summaryOnly && rawLine.startsWith "U\t" then continue
    let line := stripCrLf rawLine
    if line.isEmpty then continue
    let cols := line.splitOn "\t"
    match cols with
    | ["FP", b] => fixedPointOk := (b == "1")
    | ["DC", em] => defaultClosureAll := defaultClosureAll.insert (← decodeNameExact em)
    | ["AM", em] =>
        if !summaryOnly then
          analyzedMods := analyzedMods.insert (← decodeNameExact em)
    | ["DA", ec] => distinctAllowed := distinctAllowed.insert (← decodeNameExact ec)
    | ["AF", ec] => foundConsts := foundConsts.insert (← decodeNameExact ec)
    | ["AE", ec, emsg] => badErrors := badErrors.insert (← decodeNameExact ec) (unescapeBatchField emsg)
    | ["ROW", em, ems, etr, snc, snt, sex, sch, sie, sis] =>
        let some nc := snc.toNat? | throw <| IO.userError s!"corrupt ROW nConsts '{snc}'"
        let some nt := snt.toNat? | throw <| IO.userError s!"corrupt ROW nTainted '{snt}'"
        globalRows := globalRows.push {
          modName := (← decodeNameExact em),
          modStr := unescapeBatchField ems,
          tree := unescapeBatchField etr,
          nConsts := nc,
          nTainted := nt,
          exampleConst := unescapeBatchField sex,
          witnessChain := unescapeBatchField sch,
          inE := (sie == "1"),
          isSpecs := (sis == "1")
        }
    | ["U", ec, edm, sib, sit, sd, ewn] =>
        if !summaryOnly then
          let c ← decodeNameExact ec
          globalUSet := globalUSet.insert c
          globalDefModMap := globalDefModMap.insert c (unescapeBatchField edm)
          if sib == "1" then globalBaseTainted := globalBaseTainted.insert c
          if sit == "1" then
            globalTainted := globalTainted.insert c
            let some dVal := sd.toNat? | throw <| IO.userError s!"corrupt U dist '{sd}'"
            globalDist := globalDist.insert c dVal
            if ewn != "a" then
              globalWitnessNext := globalWitnessNext.insert c (← decodeNameExact ewn)
    | _ => throw <| IO.userError s!"corrupt batch-state line '{line}'"
  return {
    defaultClosureAll,
    analyzedMods,
    globalUSet,
    globalBaseTainted,
    globalTainted,
    globalDist,
    globalWitnessNext,
    globalDefModMap,
    globalRows,
    distinctAllowed,
    fixedPointOk,
    allowVal := { foundConsts, badErrors }
  }

def loadOrderedModArrayFile (path : FilePath) : IO (Array Name) := do
  let raw ← IO.FS.readFile path
  let mut out : Array Name := #[]
  for rawLine in raw.splitOn "\n" do
    let s := rawLine.trimAscii.toString
    if !s.isEmpty then
      out := out.push (parseName s)
  if out.isEmpty then
    throw <| IO.userError s!"empty batch-worker seeds file: {path}"
  return out

def detectCompiledSelfExe? : IO (Option FilePath) := do
  try
    let p ← IO.FS.realPath (FilePath.mk "/proc/self/exe")
    let fn := p.fileName.getD ""
    if !fn.isEmpty && fn != "lean" && !fn.startsWith "lean-" then
      return some p
    return none
  catch _ =>
    return none

def buildBatchWorkerArgs (cfg : CliConfig) (statePath seedsPath : FilePath) : Array String := Id.run do
  let mut a : Array String := #["--criterion"]
  for df in cfg.denyFiles do
    a := a.push "--deny-file" |>.push df.toString
  for gid in cfg.excludedGroups do
    a := a.push "--exclude-deny-group" |>.push gid
  if cfg.noAllow then
    a := a.push "--no-allow"
  else
    for af in cfg.allowFiles do
      a := a.push "--allow-file" |>.push af.toString
  if cfg.subsetAllow then
    a := a.push "--subset-allow"
  if let some ep := cfg.exemptSpecsFile then
    a := a.push "--exempt-specs-file" |>.push ep.toString
  if cfg.oneStep then
    a := a.push "--one-step"
  if cfg.synthInductAux then
    a := a.push "--synth-induct-aux"
  if cfg.legacySlowEdges then
    a := a.push "--legacy-slow-edges"
  a := a.push "--batch-worker-state" |>.push statePath.toString
  a := a.push "--batch-worker-seeds" |>.push seedsPath.toString
  return a

/-- Compute per-module machine-level criterion across per-`lean_lib` seed batches (splitting any
multi-module batch whose roots have colliding private/macro names). When running from a compiled
binary (`mfc_bin_*`) without `--in-process-batches`, each active batch executes in a short-lived
child subprocess so compacted `.olean` `mmap` regions are reclaimed by the OS between batches. -/
unsafe def runCriterionAnalysisBatches (cfg : CliConfig)
    (denyPats : Array DenyPattern) (allowMap : Std.HashMap Name String)
    (exemptSpecs : Std.HashSet Name) (seedBatches : Array (Array Name)) : IO CriterionSummary := do
  let selfExe? ← if cfg.inProcessBatches then pure none else detectCompiledSelfExe?
  let acc ← match selfExe? with
    | some selfExe =>
        let tmpBase := (← IO.getEnv "MFC_TMP_DIR").getD "/tmp"
        let ns ← IO.monoNanosNow
        let rnd ← IO.rand 0 1000000000
        let tmpDir := FilePath.mk tmpBase / s!"mfc_batch_state_{ns}_{rnd}"
        IO.FS.createDirAll tmpDir
        let statePath := tmpDir / "acc.tsv"
        let seedsPath := tmpDir / "seeds.txt"
        try
          let mut closureSeen : Std.HashSet Name := {}
          let mut workStack : Array (Array Name) := seedBatches.reverse
          while !workStack.isEmpty do
            let rawBatch := workStack.back!
            workStack := workStack.pop
            let activeSeeds := rawBatch.filter (fun m => !closureSeen.contains m)
            if activeSeeds.isEmpty then
              continue
            let seedsTxt := String.intercalate "\n" (activeSeeds.toList.map Name.toString) ++ "\n"
            IO.FS.writeFile seedsPath seedsTxt
            let childOut ← IO.Process.output {
              cmd := selfExe.toString,
              args := buildBatchWorkerArgs cfg statePath seedsPath
            }
            if childOut.exitCode == 75 && activeSeeds.size > 1 then
              let mid := activeSeeds.size / 2
              let left := activeSeeds.extract 0 mid
              let right := activeSeeds.extract mid activeSeeds.size
              workStack := workStack.push right
              workStack := workStack.push left
            else if childOut.exitCode != 0 then
              let mut extractedErr : Option String := none
              for rawLine in childOut.stderr.splitOn "\n" do
                let ln := stripCrLf rawLine
                if ln.startsWith "BATCH_WORKER_EXCEPTION:" then
                  extractedErr := some (unescapeBatchField (ln.drop 23).toString)
                else if !ln.isEmpty then
                  IO.eprintln ln
              match extractedErr with
              | some msg => throw <| IO.userError msg
              | none     => throw <| IO.userError s!"batch worker exited with code {childOut.exitCode}"
            else
              if !childOut.stderr.isEmpty then
                IO.eprint childOut.stderr
              let snap ← loadCriterionBatchAcc statePath true
              closureSeen := snap.defaultClosureAll
          if (← statePath.pathExists) then
            loadCriterionBatchAcc statePath true
          else
            pure ({} : CriterionBatchAcc)
        finally
          try IO.FS.removeDirAll tmpDir catch _ => pure ()
    | none =>
        let mut accIn : CriterionBatchAcc := {}
        let mut workStack : Array (Array Name) := seedBatches.reverse
        while !workStack.isEmpty do
          let rawBatch := workStack.back!
          workStack := workStack.pop
          let activeSeeds := rawBatch.filter (fun m => !accIn.defaultClosureAll.contains m)
          if activeSeeds.isEmpty then
            continue
          let envOpt ← try
              enableInitializersExecution
              let env ← importModules (activeSeeds.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
              pure (some env)
            catch e =>
              let msg := toString e
              if msg.contains "environment already contains" && activeSeeds.size > 1 then
                let mid := activeSeeds.size / 2
                let left := activeSeeds.extract 0 mid
                let right := activeSeeds.extract mid activeSeeds.size
                workStack := workStack.push right
                workStack := workStack.push left
                pure none
              else
                throw e
          if let some env := envOpt then
            accIn ← stepCriterionBatch accIn env cfg denyPats allowMap exemptSpecs activeSeeds
        pure accIn

  finalizeAllowBatchValidation acc.allowVal allowMap

  let rows := acc.globalRows.qsort (fun a b => a.modStr < b.modStr)
  let mut d2Findings : Array CriterionModRow := #[]
  let mut machineLevelMods : Array CriterionModRow := #[]
  let mut partCMods : Array CriterionModRow := #[]
  for row in rows do
    if row.nTainted > 0 then
      machineLevelMods := machineLevelMods.push row
      if row.isSpecs && !row.inE then
        d2Findings := d2Findings.push row
      if !row.inE && !row.isSpecs then
        partCMods := partCMods.push row

  return {
    defaultClosureSet := acc.defaultClosureAll,
    rows,
    d2Findings,
    machineLevelMods,
    partCMods,
    fixedPointOk := acc.fixedPointOk,
    distinctAllowed := acc.distinctAllowed
  }

def renderCriterionTsv (rows : Array CriterionModRow) : String := Id.run do
  let mut lines : Array String := #[
    "module\ttree\tn_consts\tn_tainted\texample_tainted_const\twitness_chain\tin_E\tis_Specifications"
  ]
  for r in rows do
    lines := lines.push s!"{r.modStr}\t{r.tree}\t{r.nConsts}\t{r.nTainted}\t{r.exampleConst}\t{r.witnessChain}\t{r.inE}\t{r.isSpecs}"
  return String.intercalate "\n" lines.toList ++ "\n"

def printCriterionStdoutSummary (cs : CriterionSummary) (oneStep : Bool) : IO Unit := do
  let mut treeTotals : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  for r in cs.rows do
    let (cand, mach, clean, inECnt) := treeTotals.getD r.tree (0, 0, 0, 0)
    let mach' := if r.nTainted > 0 then mach + 1 else mach
    let clean' := if r.nTainted == 0 then clean + 1 else clean
    let inE' := if r.inE then inECnt + 1 else inECnt
    treeTotals := treeTotals.insert r.tree (cand + 1, mach', clean', inE')
  let sortedTrees := treeTotals.toArray.qsort (fun a b => a.1 < b.1)
  IO.println "=== CRITERION_BY_TREE ==="
  for (tr, (cand, mach, clean, inECnt)) in sortedTrees do
    IO.println s!"CRITERION_TREE: {tr} candidate_modules={cand} machine_level={mach} clean={clean} in_E={inECnt}"
  if !cs.d2Findings.isEmpty then
    IO.println "=== D2_FINDINGS ==="
    for d in cs.d2Findings do
      IO.println s!"D2_FINDING: {d.modStr} n_tainted={d.nTainted}/{d.nConsts} example={d.exampleConst} chain={d.witnessChain}"
  IO.println "=== CRITERION_SUMMARY ==="
  IO.println s!"SUMMARY_DEFAULT_CLOSURE_MODULES={cs.defaultClosureSet.size}"
  IO.println s!"SUMMARY_CANDIDATE_MODULES={cs.rows.size}"
  IO.println s!"SUMMARY_CRITERION_MODULES={cs.machineLevelMods.size}"
  IO.println s!"SUMMARY_PART_C_MODULES={cs.partCMods.size}"
  IO.println s!"SUMMARY_D2_FINDINGS={cs.d2Findings.size}"
  IO.println s!"SUMMARY_ONE_STEP_DEBUG={oneStep}"
  IO.println s!"SUMMARY_FIXED_POINT={cs.fixedPointOk}"

/-- Collapse `partCRows` into wildcard (`X.*`) and exact module patterns, using `X.*` only when `X`
has at least two segments and two closure modules, all in `partCSet`, and none in `exemptSpecs` or
`Specifications`. -/
def computeCollapsedPartCPatterns (defaultClosure exemptSpecs : Std.HashSet Name)
    (denyPatsAB : Array DenyPattern) (partCRows : Array CriterionModRow) : IO (Array DenyPattern) := do
  let mut partCSet : Std.HashSet String := {}
  for r in partCRows do
    partCSet := partCSet.insert r.modStr

  let mut nonABMods : Array String := #[]
  for m in defaultClosure.toArray do
    unless isModDenied denyPatsAB (some m) do
      nonABMods := nonABMods.push m.toString
  nonABMods := nonABMods.qsort (· < ·)

  let exemptStrs := exemptSpecs.toArray.map (·.toString)

  let mut candPrefixes : Std.HashSet String := {}
  for r in partCRows do
    let segs := r.modStr.splitOn "."
    if segs.length >= 3 then
      for k in [2 : segs.length] do
        let pre := String.intercalate "." (segs.take k)
        if !(pre.splitOn ".").contains "Specifications" then
          candPrefixes := candPrefixes.insert pre

  -- Process shorter prefixes first so maximal subtrees win.
  let sortedPrefixes := candPrefixes.toArray.qsort (fun a b =>
    let la := (a.splitOn ".").length
    let lb := (b.splitOn ".").length
    la < lb || (la == lb && a < b))

  let mut chosenWildcards : Array String := #[]
  for pre in sortedPrefixes do
    if chosenWildcards.any (fun w => pre == w || pre.startsWith (w ++ ".")) then
      continue
    let under := nonABMods.filter (fun m => m == pre || m.startsWith (pre ++ "."))
    let hitsE := exemptStrs.any (fun em => em == pre || em.startsWith (pre ++ "."))
    let hitsSpecs := under.any (fun m => (m.splitOn ".").contains "Specifications")
    if under.size >= 2 && !hitsE && !hitsSpecs && under.all (fun m => partCSet.contains m) then
      chosenWildcards := chosenWildcards.push pre

  let mut outPats : Array DenyPattern := #[]
  for w in chosenWildcards do
    outPats := outPats.push (.prefixWildcard w)
  for r in partCRows do
    unless chosenWildcards.any (fun w => r.modStr == w || r.modStr.startsWith (w ++ ".")) do
      outPats := outPats.push (.exact r.modStr)

  let sortedOut := outPats.qsort (fun a b => a.render < b.render)

  for mStr in nonABMods do
    let covered := sortedOut.any (fun p => p.matchesMod mStr)
    let want := partCSet.contains mStr
    if covered != want then
      throw <| IO.userError s!"internal error in Part-C pattern collapse on '{mStr}': covered={covered}, expected={want}"

  return sortedOut

end MachineFreeCheck

open MachineFreeCheck Lean in
unsafe def main (args : List String) : IO UInt32 := do
  let cfg0 ← match parseCliArgs {} args with
    | .ok c => pure c
    | .error e =>
        IO.eprintln s!"[machine-free-check] error: {e}\n\n{usageText}"
        return 2
  if cfg0.showHelp then
    IO.println usageText
    return 0

  let denyFiles := if cfg0.denyFiles.isEmpty then
      #[System.FilePath.mk "Symbolic/scripts/machine_free_deny.txt"]
    else
      cfg0.denyFiles
  let allowFiles := if cfg0.noAllow then
      #[]
    else if cfg0.allowFiles.isEmpty then
      #[System.FilePath.mk "Symbolic/scripts/machine_free_allow.txt"]
    else
      cfg0.allowFiles
  let cfg := { cfg0 with denyFiles, allowFiles }

  let criterionFamily := cfg.criterion || cfg.emitProofdeps.isSome || cfg.checkProofdeps.isSome
  if cfg.oneStep then
    if !criterionFamily then
      IO.eprintln s!"[machine-free-check] error: --one-step is only valid with --criterion\n\n{usageText}"
      return 2
    if cfg.emitProofdeps.isSome || cfg.checkProofdeps.isSome then
      IO.eprintln "[machine-free-check] error: --one-step cannot be combined with --emit-proofdeps or --check-proofdeps (fail-closed)"
      return 2
  if !criterionFamily then
    if cfg.primaryMod.isNone then
      IO.eprintln s!"[machine-free-check] error: missing <Module.Name>\n\n{usageText}"
      return 2
    if cfg.targets.isEmpty && !cfg.allModuleConsts && !cfg.nonInternalModuleConsts && cfg.gkControl.isNone then
      IO.eprintln s!"[machine-free-check] error: provide target constants or --all-module-consts / --non-internal-module-consts\n\n{usageText}"
      return 2

  let denyPats ← try
      loadDenyPatternsFromFiles cfg.denyFiles cfg.excludedGroups
    catch e =>
      IO.eprintln s!"[machine-free-check] error loading deny list: {e}"
      return 2
  let allowMap0 ← if cfg.noAllow then
      pure ({} : Std.HashMap Name String)
    else
      try
        loadAllowMapFromFiles cfg.allowFiles denyPats
      catch e =>
        IO.eprintln s!"[machine-free-check] error loading allow list: {e}"
        return 2

  let sysroot ← findSysroot
  initSearchPath sysroot
  enableInitializersExecution

  -- Criterion, --emit-proofdeps, and --check-proofdeps modes.
  if criterionFamily then
    let exemptPath := cfg.exemptSpecsFile.getD "Symbolic/scripts/machine_free_exempt_specs.txt"
    let exemptSpecs ← try
        let s ← loadExactModSetFile exemptPath true
        validateExemptSpecsModules exemptPath s
        pure s
      catch e =>
        IO.eprintln s!"[machine-free-check] error loading exempt-specs file: {e}"
        return 2
    if let some statePath := cfg.batchWorkerState then
      let some workerSeedsPath := cfg.batchWorkerSeeds | do
        IO.eprintln "BATCH_WORKER_EXCEPTION:missing --batch-worker-seeds"
        return 76
      let rcWorker ← try
          let activeSeeds ← loadOrderedModArrayFile workerSeedsPath
          let acc0 ← if (← statePath.pathExists) then
              loadCriterionBatchAcc statePath false
            else
              pure ({} : CriterionBatchAcc)
          let envOpt ← try
              enableInitializersExecution
              let env ← importModules (activeSeeds.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
              pure (some env)
            catch e =>
              let msg := toString e
              if msg.contains "environment already contains" && activeSeeds.size > 1 then
                pure none
              else
                throw e
          match envOpt with
          | none => pure (75 : UInt32)
          | some env =>
              let acc1 ← stepCriterionBatch acc0 env cfg denyPats allowMap0 exemptSpecs activeSeeds
              saveCriterionBatchAcc statePath acc1
              pure (0 : UInt32)
        catch e =>
          IO.eprintln s!"BATCH_WORKER_EXCEPTION:{escapeBatchField (toString e)}"
          pure (76 : UInt32)
      return rcWorker
    let some seedsPath := cfg.defaultSeedsFile | do
      IO.eprintln "[machine-free-check] error: --default-target-seeds-file is required for --criterion/--emit-proofdeps/--check-proofdeps"
      return 2
    let seedBatches0 ← try
        loadSeedBatchesFile seedsPath
      catch e =>
        IO.eprintln s!"[machine-free-check] error loading default-target seeds: {e}"
        return 2
    let extraClean := cfg.extraImports.toList.eraseDups.toArray
    let seedBatches := if extraClean.isEmpty then seedBatches0 else seedBatches0.push extraClean
    let mut allSeedModsSeen : Std.HashSet Name := {}
    for batch in seedBatches do
      for m in batch do
        unless allSeedModsSeen.contains m do
          allSeedModsSeen := allSeedModsSeen.insert m
          let existsOlean ← try
              discard <| findOLean m
              pure true
            catch _ =>
              pure false
          unless existsOlean do
            IO.eprintln s!"[machine-free-check] error: no compiled .olean found for module '{m}' on LEAN_PATH"
            return 2

    let cs ← try
        runCriterionAnalysisBatches cfg denyPats allowMap0 exemptSpecs seedBatches
      catch e =>
        let msg := toString e
        if msg.contains "E3_LOCAL_CONST:" then
          IO.println "=== CRITERION_SUMMARY ==="
          IO.println "SUMMARY_STATUS=FAIL"
          IO.println s!"SUMMARY_E3_LOCAL_CONST_FAIL={msg}"
          return 1
        if msg.startsWith "allow entry '" then
          IO.eprintln s!"[machine-free-check] error validating allow list against environment: {e}"
          return 2
        IO.eprintln s!"[machine-free-check] error running criterion analysis: {e}"
        return 2

    if let some tsvPath := cfg.criterionTsv then
      IO.FS.writeFile tsvPath (renderCriterionTsv cs.rows)

    printCriterionStdoutSummary cs cfg.oneStep

    let mut unreached : Array (Name × String) := #[]
    for (ac, rStr) in allowMap0.toArray do
      unless cs.distinctAllowed.contains ac do
        unreached := unreached.push (ac, rStr)
    let sortedUnr := unreached.qsort (fun a b => a.1.toString < b.1.toString)
    let staleAllowFail := !cfg.subsetAllow && !sortedUnr.isEmpty
    IO.println s!"SUMMARY_ALLOW_ENTRIES={allowMap0.size}"
    IO.println s!"SUMMARY_DISTINCT_ALLOWED={cs.distinctAllowed.size}"
    IO.println s!"SUMMARY_UNREACHED_ALLOW={sortedUnr.size}{if cfg.subsetAllow && !sortedUnr.isEmpty then " (permitted by --subset-allow)" else ""}"
    for (uc, rStr) in sortedUnr do
      IO.println s!"  - [UNREACHED] {dispConst uc} : {rStr}"

    if let some outPath := cfg.emitProofdeps then
      if !cs.fixedPointOk || !cs.d2Findings.isEmpty || staleAllowFail then
        IO.println "SUMMARY_EMIT_PROOFDEPS=FAIL"
        return 1
      let headerMeta ← match cfg.emitHeaderMetaFile with
        | some mp => IO.FS.readFile mp
        | none    => pure "# Generated Part-C proof-dependency deny list\n"
      let collapsedPats ← try
          computeCollapsedPartCPatterns cs.defaultClosureSet exemptSpecs denyPats cs.partCMods
        catch e =>
          IO.eprintln s!"[machine-free-check] error collapsing Part-C patterns: {e}"
          return 2
      let mut bodyLines : Array String := #["[group proofdeps]"]
      for p in collapsedPats do
        bodyLines := bodyLines.push p.render
      let fullTxt := headerMeta ++ "\n" ++ String.intercalate "\n" bodyLines.toList ++ "\n"
      IO.FS.writeFile outPath fullTxt
      IO.println s!"SUMMARY_EMIT_PROOFDEPS=PASS (patterns={collapsedPats.size}, covered_modules={cs.partCMods.size}, path={outPath})"
      return 0

    if let some checkPath := cfg.checkProofdeps then
      let actualTxt ← try
          IO.FS.readFile checkPath
        catch e =>
          IO.eprintln s!"[machine-free-check] error reading --check-proofdeps file: {e}"
          return 2
      let checkPats ← try
          loadDenyPatternsFromFiles #[checkPath] #[]
        catch e =>
          IO.eprintln s!"[machine-free-check] error loading --check-proofdeps file: {e}"
          return 2
      let expectedPats ← try
          computeCollapsedPartCPatterns cs.defaultClosureSet exemptSpecs denyPats cs.partCMods
        catch e =>
          IO.eprintln s!"[machine-free-check] error collapsing expected Part-C patterns: {e}"
          return 2
      let mut expectedBodyLines : Array String := #["[group proofdeps]"]
      for p in expectedPats do
        expectedBodyLines := expectedBodyLines.push p.render
      -- Ignore leading `#` header lines; staleness is checked on the recomputed pattern body.
      let actualBodyLines :=
        (actualTxt.splitOn "\n").dropWhile (fun ln =>
          let t := ln.trimAscii.toString
          t.isEmpty || t.startsWith "#")
      let expectedBodyTxt := String.intercalate "\n" expectedBodyLines.toList ++ "\n"
      let actualBodyTxt := String.intercalate "\n" actualBodyLines

      let mut uncovered : Array CriterionModRow := #[]
      for r in cs.partCMods do
        unless checkPats.any (fun p => p.matchesMod r.modStr) do
          uncovered := uncovered.push r
      let mut deniedExempt : Array String := #[]
      for em in exemptSpecs.toArray.qsort (·.toString < ·.toString) do
        let emStr := em.toString
        if checkPats.any (fun p => p.matchesMod emStr) then
          deniedExempt := deniedExempt.push emStr
      let mut nonABClosureMods : Array String := #[]
      let mut staleCoveredClean : Array String := #[]
      for m in cs.defaultClosureSet.toArray.qsort (·.toString < ·.toString) do
        unless isModDenied denyPats (some m) do
          let mStr := m.toString
          nonABClosureMods := nonABClosureMods.push mStr
          if checkPats.any (fun p => p.matchesMod mStr) then
            let isMach := cs.machineLevelMods.any (fun r => r.modName == m)
            if !isMach then
              staleCoveredClean := staleCoveredClean.push mStr
      let mut unmatchedPats : Array String := #[]
      for p in checkPats do
        unless nonABClosureMods.any (fun mStr => p.matchesMod mStr) do
          unmatchedPats := unmatchedPats.push p.render

      let exactTextOk := actualBodyTxt == expectedBodyTxt

      for u in uncovered do
        IO.println s!"UNCOVERED_MACHINE_MODULE: {u.modStr} n_tainted={u.nTainted}/{u.nConsts} example={u.exampleConst} chain={u.witnessChain}"
      for de in deniedExempt do
        IO.println s!"EXEMPT_MODULE_DENIED: {de}"
      for sc in staleCoveredClean do
        IO.println s!"STALE_COVERED_CLEAN_MODULE: {sc}"
      for up in unmatchedPats do
        IO.println s!"UNMATCHED_PROOFDEPS_PATTERN: {up}"
      if !exactTextOk then
        IO.println "PROOFDEPS_BODY_MISMATCH: body patterns/formatting differ from canonical --emit-proofdeps output"

      let checkOk :=
        cs.fixedPointOk &&
        cs.d2Findings.isEmpty &&
        uncovered.isEmpty &&
        deniedExempt.isEmpty &&
        staleCoveredClean.isEmpty &&
        unmatchedPats.isEmpty &&
        exactTextOk &&
        !staleAllowFail
      IO.println s!"SUMMARY_UNCOVERED_MODULES={uncovered.size}"
      IO.println s!"SUMMARY_DENIED_EXEMPT_MODULES={deniedExempt.size}"
      IO.println s!"SUMMARY_STALE_CLEAN_COVERED={staleCoveredClean.size}"
      IO.println s!"SUMMARY_UNMATCHED_PROOFDEPS_PATTERNS={unmatchedPats.size}"
      IO.println s!"SUMMARY_PROOFDEPS_EXACT_MATCH={if exactTextOk then "PASS" else "FAIL"}"
      IO.println s!"SUMMARY_CHECK_PROOFDEPS={if checkOk then "PASS" else "FAIL"}"
      return if checkOk then 0 else 1

    let critOk := cs.fixedPointOk && cs.d2Findings.isEmpty && !staleAllowFail
    IO.println s!"SUMMARY_STATUS={if critOk then "PASS" else "FAIL"}"
    return if critOk then 0 else 1

  -- Root constant-cone audit mode.
  let some primaryMod := cfg.primaryMod | return 2
  let allMods := (#[primaryMod] ++ cfg.extraImports).toList.eraseDups.toArray
  for m in allMods do
    let existsOlean ← try
        discard <| findOLean m
        pure true
      catch _ =>
        pure false
    unless existsOlean do
      IO.eprintln s!"[machine-free-check] error: no compiled .olean found for module '{m}' on LEAN_PATH"
      return 2

  let env0 ← try
      importModules (allMods.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
    catch e =>
      IO.eprintln s!"[machine-free-check] error importing modules {allMods}: {e}"
      return 2

  try
    validateAllowMapInEnv env0 allowMap0
  catch e =>
    IO.eprintln s!"[machine-free-check] error validating allow list against environment: {e}"
    return 2

  let mut resolvedRoots0 : Array Name := #[]
  if cfg.allModuleConsts || cfg.nonInternalModuleConsts then
    let mut modRoots : Array Name := #[]
    for m in allMods do
      if let some idx := env0.header.moduleNames.idxOf? m then
        for c in env0.header.moduleData[idx]!.constNames do
          if cfg.allModuleConsts || !c.isInternal then
            modRoots := modRoots.push c
    resolvedRoots0 := modRoots.qsort (fun a b => a.toString < b.toString)
  for raw in cfg.targets do
    match resolveTargetConst env0 allMods raw with
    | .ok c => resolvedRoots0 := resolvedRoots0.push c
    | .error msg =>
        IO.eprintln s!"[machine-free-check] error: {msg}"
        return 2

  let (env, allowMap, resolvedRoots) ← match cfg.gkControl with
    | none => pure (env0, allowMap0, resolvedRoots0)
    | some cid =>
        try
          applyGkControl cid env0 allowMap0 resolvedRoots0
        catch e =>
          IO.eprintln s!"[machine-free-check] error applying --gk-control {cid}: {e}"
          return 2

  if resolvedRoots.isEmpty then
    IO.eprintln s!"[machine-free-check] error: resolved 0 target constants"
    return 2

  IO.println s!"# machine-free-check: modules={allMods.map Name.toString}, roots={resolvedRoots.size}, deny_patterns={denyPats.size}, allow_entries={allowMap.size}, subset_allow={cfg.subsetAllow}, synth_induct_aux={cfg.synthInductAux}"
  let cache ← IO.mkRef ({} : Std.HashMap Name ConstEdges)
  let runAuditAndUnion : IO
      (Bool × Array (Name × Nat) × Nat × Nat × Std.HashMap Name String × Std.HashMap Name (String × String) × ConeResult) := do
    let mut allRootsClean := true
    let mut failingRoots : Array (Name × Nat) := #[]
    let mut nonInternalTotal : Nat := 0
    let mut nonInternalFailing : Nat := 0
    let mut distinctDenied : Std.HashMap Name String := {}
    let mut distinctAllowed : Std.HashMap Name (String × String) := {}
    for r in resolvedRoots do
      let isNonInt := !r.isInternal
      if isNonInt then
        nonInternalTotal := nonInternalTotal + 1
      let (clean, dHits, aHits) ← auditRoot env cache denyPats allowMap cfg r
      if !clean then
        allRootsClean := false
        failingRoots := failingRoots.push (r, dHits.size)
        if isNonInt then
          nonInternalFailing := nonInternalFailing + 1
      for dh in dHits do
        distinctDenied := distinctDenied.insert dh.constName dh.defMod
      for ah in aHits do
        distinctAllowed := distinctAllowed.insert ah.constName (ah.defMod, ah.reason)
    let uc ← runConeBFS env cfg.gkControl.isSome cfg.synthInductAux cache denyPats allowMap resolvedRoots none
    return (allRootsClean, failingRoots, nonInternalTotal, nonInternalFailing, distinctDenied, distinctAllowed, uc)

  let auditResOpt ← try
      some <$> runAuditAndUnion
    catch e =>
      let msg := toString e
      if msg.contains "E3_LOCAL_CONST:" then
        IO.println "=== SUMMARY ==="
        IO.println "SUMMARY_STATUS=FAIL"
        IO.println "SUMMARY_MACHINE_FREE=no"
        IO.println s!"SUMMARY_E3_LOCAL_CONST_FAIL={msg}"
        return 1
      IO.eprintln s!"[machine-free-check] error during cone walk: {e}"
      return 2
  let some (allRootsClean, failingRoots, nonInternalTotal, nonInternalFailing, distinctDenied, distinctAllowed, unionCone) := auditResOpt
    | return 2
  let unionFixedPoint := unionCone.processed == unionCone.enqueued && unionCone.unexpandedEdges == 0

  let mut rootReportOk := true
  let mut rootReportReasons : Array String := #[]
  if cfg.rootReport then
    let exemptPath := cfg.exemptSpecsFile.getD "Symbolic/scripts/machine_free_exempt_specs.txt"
    let exemptSpecs ← try
        let s ← loadExactModSetFile exemptPath true
        validateExemptSpecsModules exemptPath s
        pure s
      catch e =>
        IO.eprintln s!"[machine-free-check] error loading exempt-specs file: {e}"
        return 2
    let defaultClosure ← match cfg.defaultClosureFile with
      | some cp =>
          try loadExactModSetFile cp true
          catch e =>
            IO.eprintln s!"[machine-free-check] error loading default-target closure: {e}"
            return 2
      | none =>
          match cfg.defaultSeedsFile with
          | some sp =>
              try
                let seeds ← loadExactModArrayFile sp
                computeEnvImportClosure env seeds
              catch e =>
                IO.eprintln s!"[machine-free-check] error computing default-target closure: {e}"
                return 2
          | none =>
              IO.eprintln "[machine-free-check] error: --root-report requires --default-target-closure-file or --default-target-seeds-file"
              return 2
    let (rrOk, rrReasons) ← try
        emitRootReport env cfg.gkControl.isSome cache exemptSpecs defaultClosure cfg resolvedRoots unionCone
      catch e =>
        let msg := toString e
        if msg.contains "E3_LOCAL_CONST:" then
          IO.println "=== SUMMARY ==="
          IO.println "SUMMARY_STATUS=FAIL"
          IO.println "SUMMARY_MACHINE_FREE=no"
          IO.println s!"SUMMARY_E3_LOCAL_CONST_FAIL={msg}"
          return 1
        IO.eprintln s!"[machine-free-check] error in --root-report: {e}"
        return 2
    rootReportOk := rrOk
    rootReportReasons := rrReasons

  let mut inertViolations : Array Name := #[]
  for c in sortNames unionCone.seenSet do
    if isForbiddenInertConst c then
      inertViolations := inertViolations.push c
  let inertOk := inertViolations.isEmpty

  let mut unreachedAllow : Array (Name × String) := #[]
  for (ac, reason) in allowMap.toArray do
    unless distinctAllowed.contains ac do
      unreachedAllow := unreachedAllow.push (ac, reason)
  let sortedUnreached := unreachedAllow.qsort (fun a b => a.1.toString < b.1.toString)
  let staleFailure := !cfg.subsetAllow && !sortedUnreached.isEmpty
  let overallClean := allRootsClean && unionFixedPoint && inertOk && !staleFailure && rootReportOk

  let mut layerParts : List String := []
  for h in [:unionCone.layerCounts.size] do
    layerParts := layerParts ++ [s!"L{h}={unionCone.layerCounts[h]!}"]
  layerParts := layerParts ++ [s!"L{unionCone.layerCounts.size}=0"]
  let layerHistStr := String.intercalate ", " layerParts

  IO.println "=== SUMMARY ==="
  IO.println s!"SUMMARY_STATUS={if overallClean then "PASS" else "FAIL"}"
  IO.println s!"SUMMARY_MACHINE_FREE={if overallClean then "yes" else "no"}"
  IO.println s!"SUMMARY_ROOTS_CHECKED={resolvedRoots.size}"
  IO.println s!"SUMMARY_ROOTS_FAILING={failingRoots.size}"
  if cfg.allModuleConsts || cfg.nonInternalModuleConsts then
    IO.println s!"SUMMARY_NONINTERNAL_ROOTS_CHECKED={nonInternalTotal}"
    IO.println s!"SUMMARY_NONINTERNAL_ROOTS_FAILING={nonInternalFailing}"
  IO.println s!"SUMMARY_UNION_VISITED={unionCone.visited} ({unionCone.buckets.fmt})"
  IO.println s!"SUMMARY_BFS_MAX_HOPS={unionCone.maxHops}"
  IO.println s!"SUMMARY_BFS_LAYERS={layerHistStr}"
  IO.println s!"SUMMARY_BFS_FIXED_POINT={unionFixedPoint} (processed={unionCone.processed}, enqueued={unionCone.enqueued}, frontier_at_termination=0, unexpanded_edges={unionCone.unexpandedEdges})"
  IO.println s!"SUMMARY_INERT_GUARD={if inertOk then "PASS (0 forbidden projections/recursors of ProcessInputs/ProcessInit/Oracle/AuxvConfig/Timespec in closure)" else s!"FAIL ({inertViolations.map dispConst})"}"
  if cfg.rootReport then
    IO.println s!"SUMMARY_ROOT_REPORT={if rootReportOk then "PASS" else s!"FAIL ({String.intercalate ", " rootReportReasons.toList})"}"
  for (fr, cnt) in failingRoots do
    IO.println s!"  - {dispConst fr} (deny_hits={cnt})"
  IO.println s!"SUMMARY_DISTINCT_DENIED={distinctDenied.size}"
  let mut byMod : Std.HashMap String Nat := {}
  for (_, mStr) in distinctDenied.toArray do
    byMod := byMod.insert mStr (byMod.getD mStr 0 + 1)
  let sortedMods := byMod.toArray.qsort (fun a b =>
    a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  if !sortedMods.isEmpty then
    IO.println "SUMMARY_DENIED_BY_MODULE:"
    for (mStr, cnt) in sortedMods do
      IO.println s!"  - {mStr}: {cnt}"
    let sortedConsts := distinctDenied.toArray.qsort (fun a b =>
      a.2 < b.2 || (a.2 == b.2 && a.1.toString < b.1.toString))
    IO.println "SUMMARY_DISTINCT_DENIED_CONSTANTS:"
    for (c, mStr) in sortedConsts do
      IO.println s!"  - {formatChainRaw unionCone.parent c mStr 0}"
  IO.println s!"SUMMARY_ALLOW_ENTRIES={allowMap.size}"
  IO.println s!"SUMMARY_DISTINCT_ALLOWED={distinctAllowed.size}"
  if !distinctAllowed.isEmpty then
    let sortedAllowConsts := distinctAllowed.toArray.qsort (fun a b =>
      a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1.toString < b.1.toString))
    IO.println "SUMMARY_ALLOWED_PATHS:"
    for (c, (mStr, reason)) in sortedAllowConsts do
      IO.println s!"  - {formatChainRaw unionCone.parent c mStr 0} ({reason})"
  IO.println s!"SUMMARY_UNREACHED_ALLOW={sortedUnreached.size}{if cfg.subsetAllow && !sortedUnreached.isEmpty then " (permitted by --subset-allow)" else ""}"
  for (uc, reason) in sortedUnreached do
    IO.println s!"  - [UNREACHED] {dispConst uc} : {reason}"

  return if overallClean then 0 else 1
