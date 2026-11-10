/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# Full-Application Matching for Specification Predicates

Metaprogramming helpers (`constArity`, `isFullApp?`, and `namedArg?`) that match fully applied
specification predicates by their declared binder list and fail closed if the argument count
differs from `constArity`.
-/

public meta section

namespace ProofLib.SpecShape

open Lean Meta

/-- Binder names of the declared type of `c`, in order (all binder kinds, including
    `optParam` / `autoParam` / instance binders). Empty if `c` is not in the environment. -/
def constBinderNames (c : Name) : CoreM (Array Name) := do
  let some ci := (← getEnv).find? c | return #[]
  let rec go (ty : Expr) (acc : Array Name) : Array Name :=
    match ty with
    | .forallE n _ b _ => go b (acc.push n)
    | .mdata _ b => go b acc
    | _ => acc
  return go ci.type #[]

/-- Number of syntactic `∀` binders in the declared type of `c`: the argument count of a full
    application of `c` (a `Prop`-valued predicate is always fully applied in a goal or
    hypothesis type, because elaboration inserts `optParam` defaults). Returns `0` if `c` is not in
    the environment. -/
def constArity (c : Name) : CoreM Nat :=
  return (← constBinderNames c).size

/-- `true` iff `e` (after stripping `mdata`) is `c` applied to exactly `constArity c` arguments.
    Throws if the head is `c` but the argument count differs, so callers fail closed instead of
    skipping a goal whose shape they no longer recognize. -/
def isFullApp? (e : Expr) (c : Name) : CoreM Bool := do
  let e := e.consumeMData
  unless e.isAppOf c do return false
  let n ← constArity c
  if n == 0 then
    throwError "SpecShape: `{c}` is not in the environment"
  let k := e.getAppNumArgs
  unless k == n do
    throwError "SpecShape: unrecognized spec shape: `{c}` applied to {k} arguments, but its \
      declared type has {n} binders{indentExpr e}"
  return true

/-- `true` iff `e` is a full application (`isFullApp?`) of one of `cs`. -/
def isFullAppOfAny? (e : Expr) (cs : Array Name) : CoreM Bool :=
  cs.anyM (isFullApp? e)

/-- The argument of the full application `e` of `c` bound to binder `n` in `c`'s declared type.
    Returns `none` if `e` is not headed by `c` or `c` has no binder named `n`; throws (via
    `isFullApp?`) if `e` is headed by `c` with the wrong argument count. -/
def namedArg? (e : Expr) (c : Name) (n : Name) : CoreM (Option Expr) := do
  let e := e.consumeMData
  unless ← isFullApp? e c do return none
  let names ← constBinderNames c
  let some i := names.idxOf? n | return none
  return e.getArg! i

/-- Like `namedArg?`, but throws if the binder is missing (a renamed binder must be fixed at the
    call site, not skipped). -/
def namedArg! (e : Expr) (c : Name) (n : Name) : CoreM Expr := do
  match ← namedArg? e c n with
  | some a => return a
  | none => throwError "SpecShape: `{e.getAppFn}` has no binder `{n}` (expected head `{c}`)"

end ProofLib.SpecShape

end
