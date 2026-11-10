/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import ProofLib.ProofTerm.KernelProfile
import Arm64.Trusted.Spec.SepLogic

/-!
# Static Kernel Hot-Spot Lint

Diagnostic commands `#kernel_lint` and `#kernel_lint_module` (plus strict `!` variants that fail on
findings) inspect proof terms for shapes that force the kernel to unfold or evaluate heavy
constants. A definition is heavy when tagged `@[kernel_heavy]` or when its body has at least
`proofLib.kernelLint.heavyNodes` (default 2000) distinct DAG nodes up to two definitions deep.

Three rules are checked:
- `decide-on-heavy`: `of_decide_eq_true` applied to a proposition mentioning a heavy constant.
- `rw-on-heavy` (opt-in via `proofLib.kernelLint.staticRw`): `congrArg` rewrite steps over heavy
  constants.
- `cast-unfolds-heavy`: definitional-equality sites differing around a heavy constant whose kernel
  re-check takes at least `proofLib.kernelLint.castMs` ms (default 1000; set to 0 for a
  deterministic timing-free check).
-/

namespace ProofLib.ProofTerm

public meta section

open Lean Meta Elab Command

register_option proofLib.kernelLint.castMs : Nat := {
  defValue := 1000
  descr := "`cast-unfolds-heavy` candidates are confirmed by re-checking the site with the kernel; only sites taking at least this many milliseconds are reported (0 reports every candidate)"
}

register_option proofLib.kernelLint.staticRw : Bool := {
  defValue := false
  descr := "also report every `rw` step whose rewritten term mentions a heavy constant (`rw-on-heavy`, static, noisy); by default only the expensive `rw` casts are reported, through `cast-unfolds-heavy`"
}

register_option proofLib.kernelLint.heavyNodes : Nat := {
  defValue := 2000
  descr := "a definition whose body has at least this many distinct nodes (or that mentions such a definition, up to two levels deep) is heavy for `#kernel_lint`"
}

/-- `@[kernel_heavy]`: treat this constant as heavy in `#kernel_lint` regardless of its size. -/
initialize kernelHeavyAttr : TagAttribute ←
  registerTagAttribute `kernel_heavy
    "mark a constant as heavy (expensive for the kernel to unfold) for `#kernel_lint`"

/-- Immediate sub-terms of a node (binder bodies keep their loose bound variables). -/
def exprChildren : Expr → Array Expr
  | .app f a => #[f, a]
  | .lam _ d b _ | .forallE _ d b _ => #[d, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

/-- Number of distinct sub-terms of `e`, stopping once `cap` is reached. -/
def dagSizeUpTo (e : Expr) (cap : Nat) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack : Array Expr := #[e]
  while h : stack.size > 0 do
    if seen.size ≥ cap then break
    let t := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains t then continue
    seen := seen.insert t
    for c in exprChildren t do stack := stack.push c
  return seen.size

abbrev HeavyCache := IO.Ref (Std.HashMap Name Bool)

def bigBody (n : Name) (cap : Nat) : CoreM Bool := do
  let some ci := (← getEnv).find? n | return false
  match ci with
  | .defnInfo d => return dagSizeUpTo d.value cap ≥ cap
  | _ => return false

/-- Constants of `Init`, `Std`, `Lean`, and `Lake` are excluded from heaviness checks because their
    bodies are generic library code. -/
def isCoreConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let root := (env.header.moduleNames[idx.toNat]!).getRoot
    root == `Init || root == `Std || root == `Lean || root == `Lake
  | none => false

/-- Check whether `n` is tagged `@[kernel_heavy]` or reaches a large definition body within `depth`
    unfoldings. -/
partial def isHeavy (cache : HeavyCache) (n : Name) (depth : Nat := 2) : CoreM Bool := do
  if let some b := (← cache.get)[n]? then return b
  let env ← getEnv
  let cap := proofLib.kernelLint.heavyNodes.get (← getOptions)
  let r ← do
    if kernelHeavyAttr.hasTag env n then pure true
    else if isCoreConst env n then pure false
    else if ← bigBody n cap then pure true
    else if depth == 0 then pure false
    else
      match env.find? n with
      | some (.defnInfo d) =>
        let refs := d.value.getUsedConstants
        refs.anyM fun m => if m == n then pure false else isHeavy cache m (depth - 1)
      | _ => pure false
  -- Only cache full-depth answers so a shallow `false` is not reused for a deeper query.
  if depth == 2 then cache.modify (·.insert n r)
  return r

/-- Heavy constants occurring in `e`, sorted by name. -/
def heavyConstsIn (cache : HeavyCache) (e : Expr) : CoreM (List Name) := do
  let mut out := #[]
  for n in (constsOf e).toList do
    if ← isHeavy cache n then out := out.push n
  return (out.qsort (·.toString < ·.toString)).toList

structure LintFinding where
  decl : Name
  rule : String
  msg : MessageData

/-- Minimal differing sub-term pairs of `a` and `b` (up to `limit`), paired with the sibling
    arguments and head of their enclosing application. -/
partial def diffPairs (a b : Expr) (siblings : Array Expr := #[]) (limit : Nat := 16)
    (acc : Array (Expr × Expr × Array Expr) := #[]) : Array (Expr × Expr × Array Expr) :=
  if acc.size ≥ limit || a == b then acc
  else match a, b with
  | .mdata _ a', _ => diffPairs a' b siblings limit acc
  | _, .mdata _ b' => diffPairs a b' siblings limit acc
  | .app .., .app .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if fa == fb && as.size == bs.size then
      (List.range as.size).foldl (init := acc) fun acc i =>
        let sib := (as.toList.eraseIdx i).toArray.push fa
        diffPairs as[i]! bs[i]! sib limit acc
    else acc.push (a, b, siblings)
  | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ =>
    diffPairs b₁ b₂ siblings limit (diffPairs d₁ d₂ siblings limit acc)
  | _, _ => acc.push (a, b, siblings)

def lintConst (cache : HeavyCache) (ci : ConstantInfo) : MetaM (Array LintFinding) := do
  let out ← IO.mkRef (#[] : Array LintFinding)
  let push (rule : String) (msg : MessageData) : MetaM Unit :=
    out.modify (·.push { decl := ci.name, rule, msg })
  let ppC (e : Expr) : MetaM MessageData :=
    withOptions (fun o => o.setBool `pp.deepTerms false |>.set `pp.deepTerms.threshold (6 : Nat)
        |>.setBool `pp.proofs false) do return m!"{(← ppExpr e).pretty 100000}"
  let handlers : SiteHandlers := {
    app := fun e => do
      if e.isAppOfArity ``of_decide_eq_true 3 then
        let p := e.getArg! 0
        let hs ← heavyConstsIn cache p
        unless hs.isEmpty do
          push "decide-on-heavy" m!"`decide` makes the kernel evaluate `{← ppC p}` \
            (heavy: {hs}); prove it with rewriting lemmas (e.g. `simp only [arm64_norm]`) instead"
      if proofLib.kernelLint.staticRw.get (← getOptions) && e.isAppOfArity ``congrArg 6 then
        match e.getArg! 4 with
        | .lam `_a _ _ _ =>
          let lhs := e.getArg! 2
          let hs ← heavyConstsIn cache lhs
          unless hs.isEmpty do
            push "rw-on-heavy" m!"`rw` rewrites `{← ppC lhs}`, a term over heavy constants \
              {hs}: if the goal's occurrence differs from it (e.g. through an `abbrev`), the \
              kernel compares the two by evaluating them; close the goal with `simp only [...]` / \
              the generated lemmas (or drop the hand-written side-condition proof and use the \
              default autoParam)"
        | _ => pure ()
    defEq := fun kind head i expected actual => do
      -- `decide p = true` against `true = true` is already reported by `decide-on-heavy`.
      if let some (_, l, _) := expected.eq? then
        if l.isAppOf ``Decidable.decide then return
      -- Flag minimal differing pairs that mention a heavy constant on one side only, or whose
      -- enclosing application has a heavy sibling that the kernel may unfold.
      let mut hsSet : NameSet := {}
      for (x, y, sib) in diffPairs expected actual do
        let (onlyX, onlyY) := diffConsts x y (k := 64)
        for n in onlyX ++ onlyY do
          if ← isHeavy cache n then hsSet := hsSet.insert n
        for sb in sib do
          for n in ← heavyConstsIn cache sb do hsSet := hsSet.insert n
      let hs := (hsSet.toList.toArray.qsort (·.toString < ·.toString))
      unless hs.isEmpty do
        -- Most candidates are discharged cheaply by projection or pointer equality, so confirm with
        -- a timed kernel check.
        let castNs := proofLib.kernelLint.castMs.get (← getOptions) * 1000000
        if castNs > 0 then
          let env ← getEnv
          let lctx ← getLCtx
          let (_, ns) ← timed fun t => kernelDefEqAt env lctx actual expected t
          if ns < castNs then return
        let site := match kind with
          | "arg" => s!"argument {i} of `{head}`"
          | "let" => "a `let` value"
          | _ => "the declaration's type"
        push "cast-unfolds-heavy" m!"{site} ({siteProvenance head expected}): expected and actual types \
          differ around heavy constants {hs.toList}, and the kernel takes over \
          {proofLib.kernelLint.castMs.get (← getOptions)} ms to compare them; state the step \
          through a lemma generic in the differing parts (generic transport), or prove it with \
          rewriting lemmas (`simp only [...]`) instead of `rw` / `change` / `dsimp`\
          \n    expected: {← ppC expected}\n    actual:   {← ppC actual}" }
  walkDecl handlers ci
  out.get

def reportLint (scope : String) (cis : Array ConstantInfo) (strict : Bool) :
    CommandElabM Unit := do
  let cache ← IO.mkRef {}
  let mut findings := #[]
  for ci in cis do
    findings := findings ++ (← liftTermElabM <| lintConst cache ci)
  let owners := findings.foldl (fun s f => s.insert (ownerKey f.decl)) ({} : NameSet)
  let mut msg := m!"[kernel_lint] scope={scope} decls={cis.size} findings={findings.size} \
    in_decls={owners.size}"
  -- Include the discovery index in the sort key because `Array.qsort` is not stable.
  let keyed := findings.mapIdx fun i f => ((ownerKey f.decl).toString, f.rule, i, f)
  let sorted := keyed.qsort fun (da, ra, ia, _) (db, rb, ib, _) =>
    da < db || (da == db && (ra < rb || (ra == rb && ia < ib)))
  for (_, _, _, f) in sorted do
    msg := msg ++ m!"\n[kernel_lint] {ownerKey f.decl} {f.rule}: {f.msg}"
  if strict && !findings.isEmpty then throwError msg else logInfo msg

/-- `#kernel_lint d1 d2 ...`: lint the proof terms of the named declarations and their auxiliary
    declarations for shapes that make the kernel unfold heavy constants. -/
syntax (name := kernelLintCmd) "#kernel_lint " (ppSpace ident)+ : command
/-- `#kernel_lint!`: like `#kernel_lint`, but raises an error when there is a finding. -/
syntax (name := kernelLintStrictCmd) "#kernel_lint! " (ppSpace ident)+ : command
/-- `#kernel_lint_module [Mod.Prefix]`: lint every declaration of the matching imported modules,
    or of the current file when omitted. -/
syntax (name := kernelLintModuleCmd) "#kernel_lint_module" (ppSpace ident)? : command
/-- `#kernel_lint_module!`: like `#kernel_lint_module`, but raises an error when there is a finding. -/
syntax (name := kernelLintModuleStrictCmd) "#kernel_lint_module!" (ppSpace ident)? : command

def namedWithAux (ids : Array Ident) : CommandElabM (Array ConstantInfo) := do
  let cis ← ids.mapM resolveDecl
  let owners : NameSet := cis.foldl (fun s ci => s.insert (ownerKey ci.name)) {}
  let all ← liftCoreM <| auxConstsOf owners (cis.map (·.name))
  let named : NameSet := cis.foldl (fun s ci => s.insert ci.name) {}
  let aux := all.filter fun a => !named.contains a.name
  return cis ++ aux

@[command_elab kernelLintCmd] def elabKernelLint : CommandElab
  | `(#kernel_lint $ids*) => do reportLint "explicit" (← namedWithAux ids) false
  | _ => throwUnsupportedSyntax

@[command_elab kernelLintStrictCmd] def elabKernelLintStrict : CommandElab
  | `(#kernel_lint! $ids*) => do reportLint "explicit" (← namedWithAux ids) true
  | _ => throwUnsupportedSyntax

@[command_elab kernelLintModuleCmd] def elabKernelLintModule : CommandElab
  | `(#kernel_lint_module $[$pfx?]?) => do
    let scope := match pfx? with | some p => s!"module {p.getId}" | none => "current file"
    reportLint scope (← declsInScope (pfx?.map (·.getId))) false
  | _ => throwUnsupportedSyntax

@[command_elab kernelLintModuleStrictCmd] def elabKernelLintModuleStrict : CommandElab
  | `(#kernel_lint_module! $[$pfx?]?) => do
    let scope := match pfx? with | some p => s!"module {p.getId}" | none => "current file"
    reportLint scope (← declsInScope (pfx?.map (·.getId))) true
  | _ => throwUnsupportedSyntax

end

end ProofLib.ProofTerm
