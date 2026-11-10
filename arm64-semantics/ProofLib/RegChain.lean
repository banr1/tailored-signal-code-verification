/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
import Arm64.Trusted.Spec.SepLogic

/-!
# Register-Chain Closure

Provides the `reg_chain`, `reg_chain?`, and `reg_rw` tactics over a proof-producing union-find of
local equations (including equations inside conjunctions and conjunction-valued definitions such as
`CalleeSavedPreserved`). Nodes are keyed after unfolding small zero-arity `@[reducible]`
abbreviations, and `reg_chain` closes equality leaves by `Eq.trans`, `Eq.symm`, and bounded
`congrArg` without invoking `simp`.
-/

namespace ProofLib.RegChain

public meta section

open Lean Meta Elab Tactic

/-- Maximum nesting of `∧` explored in hypotheses and goals. -/
def andDepth : Nat := 64
/-- Maximum number of nested definition unfoldings (`CallingConventionPreserved` -> ...) per path. -/
def unfoldFuel : Nat := 3
/-- Maximum depth of goal-directed congruence (`f a = f b` from `a = b`). -/
def congrDepth : Nat := 3
/-- Maximum `Expr.approxDepth` of the body of a constant unfolded by node normalisation. -/
def abbrevMaxDepth : UInt32 := 8

/-- A local equation `prf : lhs = rhs` at type `α` in universe `u`. -/
structure Fact where
  prf : Expr
  α : Expr
  u : Level
  lhs : Expr
  rhs : Expr
  deriving Inhabited

/-- Proof-forest edge from a node to its parent, justified by `facts[fact]`; `fwd` means the fact
    reads `node = parent` (otherwise `parent = node`). -/
structure Edge where
  parent : Nat
  fact : Nat
  fwd : Bool
  deriving Inhabited

/-- Union-find with proofs over the equations of one local context. -/
structure Index where
  facts : Array Fact := #[]
  /-- Normalised key of every node. -/
  keys : Array Expr := #[]
  /-- First original term seen for every node (used by the `isDefEq` fallback and by `reg_rw`). -/
  origs : Array Expr := #[]
  byKey : Std.HashMap Expr Nat := {}
  parent : Array (Option Edge) := #[]
  size : Array Nat := #[]
  /-- Non-equational leaves of the hypotheses (raw type -> proof), for `assumption`-like leaves. -/
  props : Std.HashMap Expr Expr := {}
  deriving Inhabited

/-! ## Normalisation -/

/-- Body of a zero-arity, non-instance, reducible constant with a small non-function value. -/
def smallAbbrev? (env : Environment) (c : Name) (us : List Level) : Option Expr :=
  match env.find? c with
  | some (.defnInfo d) =>
    if getReducibilityStatusCore env c != .reducible || isInstanceCore env c then none
    else if d.value.isLambda || d.value.approxDepth > abbrevMaxDepth then none
    else some (d.value.instantiateLevelParams d.levelParams us)
  | _ => none

/-- Node key: instantiate metavariables, drop metadata, unfold small reducible abbreviations
    (recursively, e.g. `Reg.x19 -> Reg.gpr 19#5`). Definitionally equal to the input. -/
partial def canon (e : Expr) : MetaM Expr := do
  let e ← if e.hasMVar then instantiateMVars e else pure e
  let env ← getEnv
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    e.replace fun
      | .mdata _ b => some (go fuel b)
      | .const c us =>
        if fuel == 0 then none else (smallAbbrev? env c us).map (go (fuel - 1))
      | _ => none
  return go 4 e

/-- If `c` is a definition `fun x1 ... xn => body` whose body is an `And` or an `Eq` (and `c` is not
    `@[irreducible]`), return its value (instantiated at `us`) and `n`. -/
def conjDef? (c : Name) (us : List Level) : MetaM (Option (Expr × Nat)) := do
  let env ← getEnv
  let some (.defnInfo d) := env.find? c | return none
  if getReducibilityStatusCore env c == .irreducible then return none
  let mut body := d.value
  let mut n := 0
  while body.isLambda do
    body := body.bindingBody!
    n := n + 1
  let hd := body.getAppFn
  if hd.isConstOf ``And || hd.isConstOf ``Eq then
    return some (d.value.instantiateLevelParams d.levelParams us, n)
  return none

/-- Unfold the head of `ty` once if it is a conjunction/equation-valued definition. -/
def unfoldConj? (ty : Expr) : MetaM (Option Expr) := do
  let .const c us := ty.getAppFn | return none
  if c == ``And || c == ``Eq then return none
  let some (v, n) ← conjDef? c us | return none
  if ty.getAppNumArgs != n then return none
  return some (v.beta ty.getAppArgs)

/-! ## Building the index -/

/-- Node of `e`, creating it if needed. -/
def Index.intern (ix : Index) (e : Expr) : MetaM (Index × Nat) := do
  let k ← canon e
  if let some i := ix.byKey[k]? then return (ix, i)
  let i := ix.keys.size
  return ({ ix with keys := ix.keys.push k, origs := ix.origs.push e, byKey := ix.byKey.insert k i,
                    parent := ix.parent.push none, size := ix.size.push 1 }, i)

/-- Root of `i` (no path compression: the forest edges carry proofs). -/
partial def Index.root (ix : Index) (i : Nat) : Nat :=
  match ix.parent[i]! with
  | some e => ix.root e.parent
  | none => i

/-- Make `i` the root of its tree by reversing the edges on the path to the old root. -/
partial def Index.reroot (ix : Index) (i : Nat) : Index :=
  match ix.parent[i]! with
  | none => ix
  | some e =>
    let ix := ix.reroot e.parent
    -- now `e.parent` is a root: point it at `i` with the reversed edge
    let sz := ix.size[e.parent]!
    { ix with parent := (ix.parent.set! e.parent (some { parent := i, fact := e.fact, fwd := !e.fwd })).set! i none,
              size := (ix.size.set! i sz) }

/-- Record the fact with index `fi` (already pushed) between nodes `a` and `b`. -/
def Index.union (ix : Index) (fi a b : Nat) : Index :=
  let ra := ix.root a
  let rb := ix.root b
  if ra == rb then ix
  else
    let sa := ix.size[ra]!
    let sb := ix.size[rb]!
    if sa ≤ sb then
      -- hang `a`'s tree below `b`
      let ix := ix.reroot a
      { ix with parent := ix.parent.set! a (some { parent := b, fact := fi, fwd := true }),
                size := ix.size.set! rb (sa + sb) }
    else
      let ix := ix.reroot b
      { ix with parent := ix.parent.set! b (some { parent := a, fact := fi, fwd := false }),
                size := ix.size.set! ra (sa + sb) }

/-- Collect the equations in `prf : ty` (also inside `∧` and inside `∧`/`=`-valued definitions);
    other propositions go to `props`. No normalisation happens here (it is cheap). -/
partial def collectHyp (prf ty : Expr) (depth fuel : Nat)
    (acc : Array Fact × Std.HashMap Expr Expr) : MetaM (Array Fact × Std.HashMap Expr Expr) := do
  let ty := ty.consumeMData
  let ty ← if ty.hasMVar then instantiateMVars ty else pure ty
  match ty.getAppFn with
  | .const ``Eq [u] =>
    if ty.getAppNumArgs != 3 then return acc
    let args := ty.getAppArgs
    return (acc.1.push ⟨prf, args[0]!, u, args[1]!, args[2]!⟩, acc.2)
  | .const ``And _ =>
    if ty.getAppNumArgs != 2 || depth == 0 then return acc
    let A := ty.appFn!.appArg!
    let B := ty.appArg!
    let acc ← collectHyp (mkApp3 (mkConst ``And.left) A B prf) A (depth - 1) fuel acc
    collectHyp (mkApp3 (mkConst ``And.right) A B prf) B (depth - 1) fuel acc
  | .const _ _ =>
    if fuel > 0 then
      if let some ty' ← unfoldConj? ty then
        return ← collectHyp prf ty' depth (fuel - 1) acc
    return (acc.1, acc.2.insert ty prf)
  | _ => return (acc.1, acc.2.insert ty prf)

def headOf (e : Expr) : Expr := e.consumeMData.getAppFn

/-- Heads of the equation sides of a goal (through `∧` and `∧`/`=`-valued definitions) and of
    their sub-terms up to the congruence depth. Used to index only the relevant equations. -/
partial def goalHeads (ty : Expr) (depth fuel : Nat) (acc : Std.HashSet Expr) :
    MetaM (Std.HashSet Expr) := do
  let ty := ty.consumeMData
  let ty ← if ty.hasMVar then instantiateMVars ty else pure ty
  let rec sub (n : Nat) (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
    let e := e.consumeMData
    let acc := acc.insert e.getAppFn
    if n == 0 then acc else e.getAppArgs.foldl (fun acc a => sub (n - 1) a acc) acc
  match ty.getAppFn with
  | .const ``Eq _ =>
    if ty.getAppNumArgs != 3 then return acc
    return sub (congrDepth + 1) ty.appArg! (sub (congrDepth + 1) ty.appFn!.appArg! acc)
  | .const ``And _ =>
    if ty.getAppNumArgs != 2 || depth == 0 then return acc
    goalHeads ty.appArg! (depth - 1) fuel (← goalHeads ty.appFn!.appArg! (depth - 1) fuel acc)
  | .const _ _ =>
    if fuel > 0 then
      if let some ty' ← unfoldConj? ty then return ← goalHeads ty' depth (fuel - 1) acc
    return acc
  | _ => return acc

/-- Index of the local context (and of the extra proof terms `extra`). With `onlyExtra`, the local
    context is ignored. With `goal? := some G`, only the equations connected to `G` through shared
    head symbols are normalised and merged (the others cannot occur in a proof of `G`'s leaves,
    up to the `isDefEq` fallback of `find?`). Must run in the goal's local context. -/
def Index.build (extra : Array Expr := #[]) (onlyExtra := false) (goal? : Option Expr := none) :
    MetaM Index := do
  let mut acc : Array Fact × Std.HashMap Expr Expr := (#[], {})
  unless onlyExtra do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := d.type
      if ty.isSort || ty.isForall then continue
      acc ← collectHyp d.toExpr ty andDepth unfoldFuel acc
  for p in extra do
    acc ← collectHyp p (← inferType p) andDepth unfoldFuel acc
  let (facts, props) := acc
  -- relevance filter: breadth-first over head symbols, starting from the goal's
  let mut keep : Array Bool := Array.replicate facts.size goal?.isNone
  if let some goal := goal? then
    let mut byHead : Std.HashMap Expr (Array Nat) := {}
    for h : i in [:facts.size] do
      let f := facts[i]
      byHead := byHead.insert (headOf f.lhs) ((byHead.getD (headOf f.lhs) #[]).push i)
      byHead := byHead.insert (headOf f.rhs) ((byHead.getD (headOf f.rhs) #[]).push i)
    let mut seen ← goalHeads goal andDepth unfoldFuel {}
    let mut work : Array Expr := seen.toArray
    while h : work.size > 0 do
      let hd := work[work.size - 1]
      work := work.pop
      for i in byHead.getD hd #[] do
        if keep[i]! then continue
        keep := keep.set! i true
        for hd' in [headOf facts[i]!.lhs, headOf facts[i]!.rhs] do
          unless seen.contains hd' do
            seen := seen.insert hd'
            work := work.push hd'
  let mut ix : Index := { props }
  for h : i in [:facts.size] do
    unless keep[i]! do continue
    let f := facts[i]
    let (ix1, a) ← ix.intern f.lhs
    let (ix2, b) ← ix1.intern f.rhs
    ix := ix2
    if a == b then continue
    let fi := ix.facts.size
    ix := { ix with facts := ix.facts.push f }
    ix := ix.union fi a b
  return ix

/-! ## Proofs from the forest -/

structure Pf where
  prf : Expr
  α : Expr
  u : Level
  lhs : Expr
  rhs : Expr

/-- Proof along one edge, oriented `node -> parent` when `up`, else `parent -> node`. -/
def Index.edgePf (ix : Index) (e : Edge) (up : Bool) : Pf :=
  let f := ix.facts[e.fact]!
  if up == e.fwd then ⟨f.prf, f.α, f.u, f.lhs, f.rhs⟩
  else ⟨mkApp4 (mkConst ``Eq.symm [f.u]) f.α f.lhs f.rhs f.prf, f.α, f.u, f.rhs, f.lhs⟩

/-- `p.trans q` (the middle terms agree up to node normalisation, which is definitional). -/
def Pf.trans (p q : Pf) : Pf :=
  ⟨mkApp6 (mkConst ``Eq.trans [p.u]) p.α p.lhs p.rhs q.rhs p.prf q.prf, p.α, p.u, p.lhs, q.rhs⟩

/-- `p.prf`, stated exactly as `s = t` when its endpoints differ syntactically from `s`/`t` (they
    are then equal up to node normalisation, i.e. definitionally). -/
def Pf.toGoal (p : Pf) (s t : Expr) : Expr :=
  if p.lhs == s && p.rhs == t then p.prf
  else mkExpectedTypeHintCore p.prf (mkApp3 (mkConst ``Eq [p.u]) p.α s t) Level.zero

partial def Index.pathUp (ix : Index) (i : Nat) (acc : Array (Nat × Edge) := #[]) :
    Array (Nat × Edge) :=
  match ix.parent[i]! with
  | some e => ix.pathUp e.parent (acc.push (i, e))
  | none => acc

/-- Chain proof between nodes `i` and `j` of the same tree (`none` if `i = j` or different trees). -/
def Index.chain? (ix : Index) (i j : Nat) : Option Pf := Id.run do
  if i == j then return none
  let pi := ix.pathUp i
  let pj := ix.pathUp j
  let rooti := if h : pi.size > 0 then pi[pi.size - 1].2.parent else i
  let rootj := if h : pj.size > 0 then pj[pj.size - 1].2.parent else j
  if rooti != rootj then return none
  -- strip the common suffix (shared path above the lowest common ancestor)
  let mut a := pi.size
  let mut b := pj.size
  while a > 0 && b > 0 && pi[a - 1]!.1 == pj[b - 1]!.1 do
    a := a - 1
    b := b - 1
  let mut acc : Option Pf := none
  for k in [:a] do
    let p := ix.edgePf pi[k]!.2 true
    acc := some (match acc with | none => p | some q => q.trans p)
  for k' in [:b] do
    let k := b - 1 - k'
    let p := ix.edgePf pj[k]!.2 false
    acc := some (match acc with | none => p | some q => q.trans p)
  return acc

def sameHead (k k' : Expr) : Bool :=
  k.isApp && k'.isApp && k.getAppFn == k'.getAppFn && k.getAppNumArgs == k'.getAppNumArgs

/-- Cheap filter for the `isDefEq` fallback: same head and arity, equal free-variable arguments. -/
def sameSkeleton (e e' : Expr) : Bool :=
  e.getAppFn == e'.getAppFn && e.getAppNumArgs == e'.getAppNumArgs &&
    (e.getAppArgs.zip e'.getAppArgs).all fun (x, y) => !(x.isFVar && y.isFVar && x != y)

/-- Node of `e` if any: by normalised key, else by reducible `isDefEq` against nodes with the
    same skeleton (at most 64 candidates). -/
def Index.find? (ix : Index) (e : Expr) : MetaM (Option Nat) := do
  let k ← canon e
  if let some i := ix.byKey[k]? then return some i
  let mut tried := 0
  for h : i in [:ix.keys.size] do
    if tried ≥ 64 then break
    if sameSkeleton k ix.keys[i] then
      tried := tried + 1
      if ← withReducible (withNewMCtxDepth (isDefEq e ix.origs[i]!)) then return some i
  return none

def Index.members (ix : Index) (i : Nat) : Array Nat := Id.run do
  let r := ix.root i
  let mut out := #[]
  for j in [:ix.keys.size] do
    if ix.root j == r then out := out.push j
  return out

mutual

/-- Proof of `s = t` from the index: same node (refl), forest chain, or (up to `depth` levels)
    congruence, also through a class member of `s` (resp. `t`) with the head of `t` (resp. `s`). -/
partial def Index.proveEq? (ix : Index) (s t : Expr) (depth := congrDepth) : MetaM (Option Expr) := do
  let ks ← canon s
  let kt ← canon t
  if ks == kt then return some (← mkEqRefl s)
  let i? ← ix.find? s
  let j? ← ix.find? t
  if let some i := i? then
    if let some j := j? then
      if i == j then return some (← mkEqRefl s)
      if let some p := ix.chain? i j then
        return some (p.toGoal s t)
  if depth == 0 then return none
  if let some p ← ix.congr? s t ks kt depth then return some p
  -- `s ~ m` and `m = t` by congruence, for a member `m` of `s`'s class with `t`'s head
  if let some i := i? then
    for m in ix.members i do
      if m == i || !sameHead ix.keys[m]! kt then continue
      if let some q ← ix.congr? ix.origs[m]! t ix.keys[m]! kt depth then
        let some p := ix.chain? i m | continue
        return some (← mkEqTrans (p.toGoal s ix.origs[m]!) q)
  if let some j := j? then
    for m in ix.members j do
      if m == j || !sameHead ix.keys[m]! ks then continue
      if let some q ← ix.congr? s ix.origs[m]! ks ix.keys[m]! depth then
        let some p := ix.chain? m j | continue
        return some (← mkEqTrans q (p.toGoal ix.origs[m]! t))
  return none

/-- Goal-directed congruence `f a1 ... an = f b1 ... bn` from provable `ai = bi` (only at argument
    positions no later argument depends on). `ks`/`kt` are the normalised `s`/`t`. -/
partial def Index.congr? (ix : Index) (s t ks kt : Expr) (depth : Nat) : MetaM (Option Expr) := do
  if !sameHead ks kt then return none
  -- Decompose the original terms: they must agree on arity and normalised head, which keys
  -- alone do not guarantee (normalisation can unfold an abbreviation in head position).
  let s := s.consumeMData
  let t := t.consumeMData
  let f := s.getAppFn
  let as := s.getAppArgs
  let bs := t.getAppArgs
  if as.size != bs.size || (← canon f) != (← canon t.getAppFn) then return none
  let info ← getFunInfoNArgs f as.size
  let mut acc : Option Expr := none
  for h : i in [:as.size] do
    let a := as[i]
    let b := bs[i]!
    if (← canon a) == (← canon b) then continue
    if let some pi := info.paramInfo[i]? then
      if pi.hasFwdDeps then return none
    let some hab ← ix.proveEq? a b (depth - 1) | return none
    let pre := bs[:i].toArray
    let post := as[i+1:].toArray
    let motive := Expr.lam `x (← inferType a) (mkAppN ((mkAppN f pre).app (.bvar 0)) post) .default
    let step ← mkCongrArg motive hab
    acc := some (← match acc with | none => pure step | some q => mkEqTrans q step)
  let some p := acc | return none
  return some (mkExpectedTypeHintCore p (← mkEq s t) Level.zero)

end

/-! ## Closing goals -/

/-- Split goal conjunctions (also behind `∧`/`=`-valued definitions), close the equation leaves
    from `ix`, and return the leaves that could not be closed. Runs in `g`'s context. -/
partial def Index.closeGoal (ix : Index) (g : MVarId) (depth := andDepth) (fuel := unfoldFuel) :
    MetaM (List MVarId) := g.withContext do
  let ty := (← g.getType).consumeMData
  let ty ← if ty.hasMVar then instantiateMVars ty else pure ty
  match ty.getAppFn with
  | .const ``And _ =>
    if ty.getAppNumArgs == 2 && depth > 0 then
      let A := ty.appFn!.appArg!
      let B := ty.appArg!
      let ga ← mkFreshExprSyntheticOpaqueMVar A
      let gb ← mkFreshExprSyntheticOpaqueMVar B
      g.assign (mkApp4 (mkConst ``And.intro) A B ga gb)
      return (← ix.closeGoal ga.mvarId! (depth - 1) fuel) ++ (← ix.closeGoal gb.mvarId! (depth - 1) fuel)
  | .const ``Eq _ =>
    if ty.getAppNumArgs == 3 then
      if let some p ← ix.proveEq? ty.appFn!.appArg! ty.appArg! then
        g.assign p
        return []
  | .const ``True _ =>
    g.assign (mkConst ``True.intro)
    return []
  | .const _ _ =>
    if fuel > 0 then
      if let some ty' ← unfoldConj? ty then
        let g' ← mkFreshExprSyntheticOpaqueMVar ty'
        g.assign g'
        return ← ix.closeGoal g'.mvarId! depth (fuel - 1)
  | _ => pure ()
  if let some p := ix.props[ty]? then
    g.assign p
    return []
  return [g]

/-- MetaM entry point: index `g`'s local context (plus `extra`), split `g`'s conjunctions and close
    every equation leaf it can. Returns the leaves left open (e.g. for `omega` or `bv_omega`). -/
def closeLeaves (g : MVarId) (extra : Array Expr := #[]) (onlyExtra := false) : MetaM (List MVarId) :=
  g.withContext do
    let ix ← Index.build extra onlyExtra (some (← instantiateMVars (← g.getType)))
    ix.closeGoal g

/-! ## `reg_rw`: rewrite to class representatives -/

/-- Rank of a term for `reg_rw`: the latest local-context position among its free variables
    (`-1`-like `0` when closed), then its size. Smaller is preferred. -/
def rank (e : Expr) : MetaM (Nat × Nat) := do
  let lctx ← getLCtx
  let fvs := (collectFVars {} e).fvarIds
  let mut m := 0
  for fv in fvs do
    if let some d := lctx.find? fv then m := max m (d.index + 1)
  return (m, e.approxDepth.toNat)

/-- Rewrite the goal so that every subterm that lies in a non-trivial class is replaced by the class
    representative: the member with the earliest free variables (or, with `newest`, the latest,
    e.g. the current state's register), ties broken by size. Occurrences of bare free variables and
    of closed terms are left alone. Returns the new goal (or `none` if nothing changed). -/
def regRw (g : MVarId) (extra : Array Expr := #[]) (onlyExtra := false) (newest := false) :
    MetaM (Option MVarId) :=
  g.withContext do
    let ix ← Index.build extra onlyExtra
    let mut rep : Std.HashMap Nat (Nat × (Nat × Nat)) := {}
    for h : i in [:ix.keys.size] do
      let r := ix.root i
      if r == i && ix.size[i]! == 1 then continue
      let rk ← rank ix.origs[i]!
      match rep[r]? with
      | some (_, rk') =>
        let better := if newest then rk.1 > rk'.1 || (rk.1 == rk'.1 && rk.2 < rk'.2)
          else rk.1 < rk'.1 || (rk.1 == rk'.1 && rk.2 < rk'.2)
        if better then rep := rep.insert r (i, rk)
      | none => rep := rep.insert r (i, rk)
    let target ← instantiateMVars (← g.getType)
    -- only subterms whose head is the head of some node can be nodes (avoids normalising the
    -- whole goal)
    let mut heads : Std.HashSet Expr := {}
    for h : i in [:ix.keys.size] do
      heads := heads.insert ix.keys[i].getAppFn |>.insert ix.origs[i]!.getAppFn
    -- collect the maximal subterms of the goal that are nodes with a better representative
    let mut todo : Array (Expr × Nat × Nat) := #[]
    let mut seen : Std.HashSet Expr := {}
    let mut work : Array Expr := #[target]
    while h : work.size > 0 do
      let e := work[work.size - 1]
      work := work.pop
      if seen.contains e then continue
      seen := seen.insert e
      if e.hasLooseBVars then
        -- cannot be abstracted as a closed term; look inside
        pure ()
      else if heads.contains e.getAppFn && !e.isFVar && e.hasFVar then
        -- bare variables and closed terms (literals) are never rewritten: they are the values the
        -- other members are rewritten *to*, and rewriting `0#64` or `entry` into a register read
        -- of some state would only obscure the goal
        if let some i := ix.byKey[← canon e]? then
          if let some (ri, _) := rep[ix.root i]? then
            if ri != i then
              todo := todo.push (e, i, ri)
              continue
      match e with
      | .app f a => work := work.push a |>.push f
      | .lam _ t b _ | .forallE _ t b _ => work := work.push b |>.push t
      | .letE _ t v b _ => work := work.push b |>.push v |>.push t
      | .mdata _ b | .proj _ _ b => work := work.push b
      | _ => pure ()
    if todo.isEmpty then return none
    let mut g := g
    let mut changed := false
    for (e, i, ri) in todo do
      let some p := ix.chain? i ri | continue
      let p := p.toGoal e ix.origs[ri]!
      let tgt ← instantiateMVars (← g.getType)
      -- An occurrence may have disappeared through an earlier rewrite, or not be abstractable
      -- (motive not type correct): skip it instead of failing the whole tactic.
      let some r ← (try some <$> g.rewrite tgt p catch _ => pure none) | continue
      g ← g.replaceTargetEq r.eNew r.eqProof
      changed := true
    return if changed then some g else none

/-! ## Tactics -/

/-- Close an equation goal, or a conjunction of equations (also behind definitions such as
    `CalleeSavedPreserved`), by chaining local equations: `Eq.trans`/`Eq.symm` chains along a
    proof-producing union-find, plus `congrArg` for `f a = f b`. `reg_chain [h, ...]` adds proof
    terms; `reg_chain only [h, ...]` uses only them. Fails listing the leaves it could not close. -/
syntax (name := regChainTac) "reg_chain" (&" only")? (" [" term,* "]")? : tactic
/-- `reg_chain` that also logs `Try this: exact ...` with the proof term it built. -/
syntax (name := regChainQTac) "reg_chain?" (&" only")? (" [" term,* "]")? : tactic
/-- Rewrite the goal: replace every subterm that is in a non-trivial class of the local equations
    by its class representative (the member whose free variables were introduced earliest, or a
    closed term; with `reg_rw ←`, the member whose free variables were introduced last, e.g. the
    current state). Fails if nothing changes. -/
syntax (name := regRwTac) "reg_rw" (" ←")? (&" only")? (" [" term,* "]")? : tactic

def elabExtra (ts : Array Term) : TacticM (Array Expr) :=
  withMainContext <| ts.mapM fun t => do instantiateMVars (← elabTerm t none)

def evalRegChain (report onlyExtra : Bool) (ts : Array Term) : TacticM Unit := do
  let extra ← elabExtra ts
  let g ← getMainGoal
  let rest ← closeLeaves g extra onlyExtra
  unless rest.isEmpty do
    let tys ← rest.mapM fun m => do return m!"{indentExpr (← instantiateMVars (← m.getType))}"
    throwError "reg_chain: could not close {rest.length} leaf goal(s):{MessageData.joinSep tys ""}"
  replaceMainGoal []
  if report then
    let pf ← instantiateMVars (mkMVar g)
    g.withContext do logInfo m!"Try this: exact {pf}"

def parseTail (stx : Syntax) : Bool × Array Term :=
  (!stx[1].isNone, if stx[2].isNone then #[] else stx[2][1].getSepArgs.map (⟨·⟩))

@[tactic regChainTac] def elabRegChain : Tactic := fun stx => do
  let (o, ts) := parseTail stx
  evalRegChain false o ts

@[tactic regChainQTac] def elabRegChainQ : Tactic := fun stx => do
  let (o, ts) := parseTail stx
  evalRegChain true o ts

@[tactic regRwTac] def elabRegRw : Tactic := fun stx => do
  let newest := !stx[1].isNone
  let (o, ts) := parseTail (mkNullNode #[stx[0], stx[2], stx[3]])
  let extra ← elabExtra ts
  let some g' ← regRw (← getMainGoal) extra o newest | throwError "reg_rw: nothing to rewrite"
  replaceMainGoal [g']

end

end ProofLib.RegChain
