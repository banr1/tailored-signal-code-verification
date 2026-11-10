/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# `maxRecDepth` Diagnostics for ProofLib Tactics

Failure-path diagnostics for `arm64_norm`, `wp_steps`, and `wp_step` when Lean raises a
`maxRecDepth` runtime exception. Identifies the deepest goal, hypothesis, or `let` value via
memoized argument-nesting depth (`exprDepthInfo`, which does not saturate at 255 like
`Expr.approxDepth`), reports the most frequent head constant along a deepest path, and suggests
targeted remedies (`maxRecDepthContextReport`).
-/

public meta section

namespace ProofLib.MaxRecDepthDiag

open Lean Meta Elab Tactic

/-- Tag attached to ProofLib diagnostics that were produced in place of a `maxRecDepth` error,
    so enclosing tactics can still recognize the underlying cause. -/
def diagTag : Name := `ProofLib.maxRecDepthDiag

/-- True when `msg` carries a `maxRecDepth` tag: the raw runtime tag, the `nested.` form that
    `simp` wraps it in, or a ProofLib diagnostic produced from one (`diagTag`). -/
def msgIsMaxRecDepth (msg : MessageData) : Bool :=
  msg.hasTag fun n =>
    n == `runtime.maxRecDepth || n == `nested.runtime.maxRecDepth || n == diagTag

/-- True when `ex` is (or wraps) a `maxRecDepth` exception. -/
def isMaxRecDepthEx (ex : Exception) : Bool :=
  ex.isMaxRecDepth || msgIsMaxRecDepth ex.toMessageData

/-- Run `act` with a fresh recursion-depth budget (the current option value, with the counter
    reset) so the diagnostic itself does not re-trigger the limit it is reporting. -/
def withFreshRecDepth {m : Type → Type} [Monad m] [MonadWithReaderOf Core.Context m]
    {α : Type} (act : m α) : m α :=
  withTheReader Core.Context (fun ctx => { ctx with currRecDepth := 0 }) act

/-- Argument-nesting depth of `e` (bounded by `fuel`), together with the head constant that occurs
    most often along one deepest root-to-leaf path and its count. An application spine
    `f a_1 ... a_n` adds one level per nested argument, so left-associated `State` update towers
    have depth proportional to their length. -/
structure DepthInfo where
  depth : Nat
  head? : Option Name := none
  headCount : Nat := 0
  deriving Inhabited

private abbrev DepthM := StateM (Std.HashMap Expr (Nat × Option Expr))

private partial def depthAux (fuel : Nat) (e : Expr) : DepthM Nat := do
  if fuel == 0 then return 0
  if let some (d, _) := (← get).get? e then return d
  let (d, child?) ← match e with
    | .app f a => do
      let df ← depthAux fuel f
      let da ← depthAux (fuel - 1) a
      pure (if da + 1 > df then (da + 1, some a) else (df, some f))
    | .lam _ t b _ | .forallE _ t b _ => do
      let dt ← depthAux (fuel - 1) t
      let db ← depthAux (fuel - 1) b
      pure (if dt > db then (dt + 1, some t) else (db + 1, some b))
    | .letE _ _ v b _ => do
      let dv ← depthAux (fuel - 1) v
      let db ← depthAux (fuel - 1) b
      pure (if dv > db then (dv + 1, some v) else (db + 1, some b))
    | .mdata _ b => do pure (← depthAux fuel b, some b)
    | .proj _ _ b => do pure ((← depthAux (fuel - 1) b) + 1, some b)
    | _ => pure (0, none)
  modify (·.insert e (d, child?))
  return d

/-- Compute `DepthInfo` for `e` (callers instantiate metavariables first). -/
def exprDepthInfo (e : Expr) (fuel : Nat := 100000) : DepthInfo := Id.run do
  let (d, memo) := (depthAux fuel e).run {}
  -- Walk one deepest path, counting the head constant of each application spine on it once
  -- (at the spine top, i.e. not when the path moves from `f a` to `f`).
  let mut counts : Std.HashMap Name Nat := {}
  let mut cur := e
  let mut spineTop := true
  let mut steps := 0
  while steps < fuel do
    steps := steps + 1
    if spineTop && cur.isApp then
      if let some c := cur.getAppFn.constName? then
        counts := counts.insert c (counts.getD c 0 + 1)
    match memo.get? cur with
    | some (_, some next) =>
      spineTop := !(cur.isApp && next == cur.appFn!)
      cur := next
    | _ => break
  let mut head? : Option Name := none
  let mut headCount := 0
  for (c, n) in counts.toList do
    if n > headCount then
      head? := some c
      headCount := n
  return { depth := d, head?, headCount }

/-- A goal or hypothesis location ranked by term depth. -/
structure DeepLoc where
  /-- `goal`, `hypothesis h`, or `let value of h`. -/
  label : MessageData
  /-- User-facing name of the hypothesis (none for the goal). -/
  hyp? : Option Name
  /-- True for the value of a `let`-bound local (zeta-delta unfolding target). -/
  isLetValue : Bool
  info : DepthInfo

/-- Rank the goal, every non-implementation-detail hypothesis type, and every `let` value in the
    context of `g` by structural depth (deepest first). -/
def rankDeepLocs (g : MVarId) : MetaM (Array DeepLoc) := g.withContext do
  let mut locs : Array DeepLoc := #[]
  let gTy ← instantiateMVars (← g.getType)
  locs := locs.push { label := m!"the goal", hyp? := none, isLetValue := false,
                      info := exprDepthInfo gTy }
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    locs := locs.push { label := m!"hypothesis `{decl.userName}`", hyp? := some decl.userName,
                        isLetValue := false, info := exprDepthInfo ty }
    if let some v := decl.value? (allowNondep := true) then
      let v ← instantiateMVars v
      locs := locs.push { label := m!"the value of `let` local `{decl.userName}`",
                          hyp? := some decl.userName, isLetValue := true,
                          info := exprDepthInfo v }
  return locs.qsort (fun a b => a.info.depth > b.info.depth)

/-- Depth at or above which a term is called "deep" in the diagnostic. Lean's default
    `maxRecDepth` is 512 and traversals of a term typically use several frames per level. -/
def deepThreshold : Nat := 64

private def describeLoc (l : DeepLoc) : MessageData :=
  let headPart := match l.info.head? with
    | some h => m!", most frequent head on the deepest path: `{h}` ×{l.info.headCount}"
    | none => m!""
  m!"{l.label} (term depth {l.info.depth}{headPart})"

private def stateUpdateHeads : List String :=
  ["writeReg64", "writeReg32", "writeReg", "writeBytes", "writeMem", "setFlags", "setPC",
   "writeVReg", "write64", "write32", "write8", "write16"]

private def isStateUpdateHead (n : Name) : Bool :=
  match n with
  | .str _ s => stateUpdateHeads.contains s
  | _ => false

/-- Build the "where" and "hint" part of a `maxRecDepth` diagnostic from the context of `g`:
    the deepest locations (at most `maxLocs`) and remedies matched to what was found.
    `rewriteLoopHint` is the tactic-specific hint shown when no deep term explains the failure. -/
def maxRecDepthContextReport (g : MVarId) (rewriteLoopHint : MessageData)
    (maxLocs : Nat := 3) : MetaM MessageData := withFreshRecDepth do
  let locs ← rankDeepLocs g
  let deepest? := locs[0]?
  let deepLocs := (locs.filter (·.info.depth ≥ deepThreshold)).extract 0 maxLocs
  let shown := if deepLocs.isEmpty then locs.extract 0 1 else deepLocs
  let mut msg : MessageData :=
    if shown.isEmpty then m!""
    else m!"\ndeepest term{if shown.size > 1 then "s" else ""}: " ++
      MessageData.joinSep (shown.toList.map describeLoc) m!"; "
  let mut hints : Array MessageData := #[]
  if deepLocs.isEmpty then
    let maxDepth : Nat := (deepest?.map (·.info.depth)).getD 0
    hints := hints.push m!"no term in the goal or context is deep (max depth {maxDepth}), so this is most likely a rewrite loop: {rewriteLoopHint}"
  else
    if deepLocs.any (fun l => (l.info.head?.map isStateUpdateHead).getD false) then
      hints := hints.push m!"a long state-update tower is being traversed: collapse it with a commutation / read-over-write lemma (e.g. a `writeReg64_comm`-style lemma) or bind the intermediate state with `generalize hs : <tower> = s'` (or `obtain ⟨s', hs⟩ : ∃ s', s' = <tower> := ⟨_, rfl⟩`) before normalizing"
    if deepLocs.any (·.isLetValue) then
      hints := hints.push m!"a `let`-bound local has a deep value that `simp`/`rw`/unification unfold (zeta-delta): `clear_value` it, or restate it as an opaque `obtain ⟨x, hx⟩ : ∃ x, x = <value> := ⟨_, rfl⟩`"
    hints := hints.push m!"generalize (`generalize hx : <deep subterm> = x at h ⊢`) or pre-fold the deep subterm, and restrict the rewrite to one location (`simp only [...] at h`) instead of `at *`"
  hints := hints.push m!"`set_option maxRecDepth N` is not the fix: it only moves the limit (and on a rewrite loop just delays the failure); shrink the term or break the loop instead"
  for h in hints do
    msg := msg ++ m!"\nhint: " ++ h
  return msg

end ProofLib.MaxRecDepthDiag

end
