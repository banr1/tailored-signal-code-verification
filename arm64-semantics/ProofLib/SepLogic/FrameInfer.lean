/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.Exists
public import ProofLib.SepLogic.Solver
public import ProofLib.SepLogic.Stack
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.OmegaBounded
import Arm64.Trusted.Spec.SepLogic

/-!
# Frame Inference with Metavariable Backtracking

Implements the `sep_frame`, `sep_frame?`, and `sep_frame_apply` tactics along with the
`SepFrameInfer.frameProc` hook for separation-logic frame inference and cancellation over
`m ⊨ G`, `∀ R, m ⊨ P ∗ R → m ⊨ G`, `P ⊢ G`, `P = G`, and `SepFrame Sub Full ?F` goals.

Both `∗`-trees are reified into atom lists with normalized keys (canonical base-plus-offset
addresses and evaluated sizes), greedy exact cancellation runs first, and remaining goal atoms are
matched by bounded depth-first search with metavariable backtracking, region carving and merging,
and reflective AC certificates.
-/

namespace ProofLib

open Arm64

@[expose] public section

universe u

namespace SepFrameInfer

/-! ## Kernel lemmas used by the solver -/

theorem entails_congr_right {P A B : SepProp} (h : P ⊢ A) (e : A = B) : P ⊢ B := e ▸ h

theorem eq_congr_right {P A B : SepProp} (h : P = A) (e : A = B) : P = B := h.trans e

theorem pure_intro_eq {φ : Prop} (hφ : φ) (R : SepProp) : R = (⌜φ⌝ ∗ R) :=
  (pure_sepConj_of_true hφ R).symm

/-- Carve `[b, b + k)` out of `memRegion a n` where `b = a + off`, leaving `off` bytes before
    and `r` bytes after. -/
theorem memRegion_carve (a b c : BitVec 64) (n off k r : Nat)
    (hb : a + BitVec.ofNat 64 off = b) (hc : b + BitVec.ofNat 64 k = c)
    (hn : off + k + r = n) (hle : n ≤ 2 ^ 64) :
    memRegion a n = memRegion a off ∗ (memRegion b k ∗ memRegion c r) := by
  subst hb hc hn
  rw [Nat.add_assoc, memRegion_split a off (k + r) (by omega),
    memRegion_split (a + BitVec.ofNat 64 off) k r (by omega)]

theorem memRegion_carve_left (a c : BitVec 64) (n k r : Nat)
    (hc : a + BitVec.ofNat 64 k = c) (hn : k + r = n) (hle : n ≤ 2 ^ 64) :
    memRegion a n = memRegion a k ∗ memRegion c r := by
  subst hc hn
  exact memRegion_split a k r hle

theorem memRegion_carve_right (a b : BitVec 64) (n off k : Nat)
    (hb : a + BitVec.ofNat 64 off = b) (hn : off + k = n) (hle : n ≤ 2 ^ 64) :
    memRegion a n = memRegion a off ∗ memRegion b k := by
  subst hb hn
  exact memRegion_split a off k hle

theorem memRegion_merge (a b : BitVec 64) (n k N : Nat)
    (hb : a + BitVec.ofNat 64 n = b) (hN : n + k = N) (hle : N ≤ 2 ^ 64) :
    memRegion a n ∗ memRegion b k = memRegion a N :=
  (memRegion_carve_right a b N n k hb hN hle).symm

end SepFrameInfer

end

public meta section

namespace SepFrameInfer

open Lean Meta Elab Tactic
open SepSolver

register_option proofLib.sepFrameMaxSteps : Nat := {
  defValue := 4096
  descr := "maximum number of candidate (goal atom, hypothesis atom) pairings `sep_frame` tries \
    during its backtracking search before giving up"
}

/-! ## Judgments: `m ⊨ _`, `P ⊢ _`, `P = _` -/

/-- The judgment a proof is built for: `m ⊨ X` (`sat m`), `P0 ⊢ X` (`ent P0`), or `P0 = X`
    (`eq P0`). -/
inductive Judg where
  | sat (m : Expr)
  | ent (P0 : Expr)
  | eq (P0 : Expr)
  deriving Inhabited

def Judg.type : Judg → Expr → Expr
  | .sat m, X => mkSat X m
  | .ent P0, X => mkApp2 (mkConst ``Arm64.SepProp.Entails) P0 X
  | .eq P0, X => mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Arm64.SepProp) P0 X

def Judg.refl : Judg → Option Expr
  | .sat _ => none
  | .ent P0 => some (mkApp (mkConst ``Entails.refl) P0)
  | .eq P0 => some (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Arm64.SepProp) P0)

def Judg.transport (j : Judg) (A B e h : Expr) : Expr :=
  match j with
  | .sat m => mkAppN (mkConst ``Satisfies.congr_prop) #[m, A, B, e, h]
  | .ent P0 => mkAppN (mkConst ``entails_congr_right) #[P0, A, B, h, e]
  | .eq P0 => mkAppN (mkConst ``eq_congr_right) #[P0, A, B, h, e]

def Judg.transportOpt (j : Judg) (A B : Expr) (e? : Option Expr) (h : Expr) : Expr :=
  match e? with
  | some e => j.transport A B e h
  | none => h

/-- Transport `h : J A` to `J B` when `A` and `B` have the same atom multiset. -/
def Judg.ac? (j : Judg) (A B h : Expr) : MetaM (Option Expr) := do
  let A ← instantiateMVars A
  let B ← instantiateMVars B
  match j with
  | .sat m => satAC? m A B h
  | _ =>
    if A == B then return some h
    let some (tbl, tA, tB) ← reifyPermTbl? A B | return none
    let e ← eqACOfTbl A B tbl tA tB
    return some (j.transport A B e h)

def Judg.pureIntro (j : Judg) (φ hφ R h : Expr) : Expr :=
  let pφ := mkApp (mkConst ``Arm64.SepProp.pure) φ
  j.transport R (mkSep pφ R) (mkApp3 (mkConst ``pure_intro_eq) φ hφ R) h

def Judg.existsIntro (j : Judg) (u : Level) (α f w R h : Expr) : MetaM Expr := do
  match j with
  | .sat m => return mkAppN (mkConst ``Satisfies.sepExists_intro [u]) #[α, f, R, m, w, h]
  | .ent P0 => return mkAppN (mkConst ``Entails.sepExists_intro_frame [u]) #[α, f, P0, R, w, h]
  | .eq _ => throwError "sep_frame: cannot introduce an `∃∗` witness in an equation goal"

/-! ## Atom keys (normalized forms with proofs) -/

def transOpt (p1? p2? : Option Expr) : MetaM (Option Expr) := mkEqTransOpt p1? p2?

def reflHint (e e' : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl e') (← mkEq e e')

/-- Evaluate a closed 64-bit address built from literals with `+` and `-`. -/
partial def evalBV64Arith? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if e.hasFVar || e.hasMVar then return none
  if let some v ← evalBV64Lit? e then return some v
  let m := 1 <<< 64
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let some a ← evalBV64Arith? (e.getArg! 4) | return none
    let some b ← evalBV64Arith? (e.getArg! 5) | return none
    return some ((a + b) % m)
  if e.isAppOfArity ``HSub.hSub 6 then
    let some a ← evalBV64Arith? (e.getArg! 4) | return none
    let some b ← evalBV64Arith? (e.getArg! 5) | return none
    return some ((a + m - b) % m)
  return none

def isBV64Arith (e : Expr) : Bool :=
  (e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6) &&
    (e.getArg! 0).isAppOfArity ``BitVec 1

/-- Replace closed literal leaves of an address by canonical `BitVec.ofNat 64 v` literals. -/
partial def canonLits (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if !e.hasFVar && !e.hasMVar then
    if let some v ← evalBV64Arith? e then
      return mkCanonBV64Lit v
  if isBV64Arith e then
    let args := e.getAppArgs
    let l ← canonLits args[4]!
    let r ← canonLits args[5]!
    return mkAppN e.getAppFn (args.set! 4 l |>.set! 5 r)
  return e

/-- Reassociate a top-level `x + (y + c)` with literal `c` and non-literal `x`, `y` to
    `(x + y) + c`, with a proof. -/
def reassocAddLit (e : Expr) : MetaM (Expr × Option Expr) := do
  unless e.isAppOfArity ``HAdd.hAdd 6 && (e.getArg! 0).isAppOfArity ``BitVec 1 do return (e, none)
  let x := e.getArg! 4
  let r := e.getArg! 5
  unless r.isAppOfArity ``HAdd.hAdd 6 do return (e, none)
  let y := r.getArg! 4
  let c := r.getArg! 5
  if (← evalBV64Lit? c).isNone || (← evalBV64Lit? x).isSome || (← evalBV64Lit? y).isSome then
    return (e, none)
  let e' ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[x, y], c]
  return (e', some (← mkEqSymm (← mkAppM ``BitVec.add_assoc #[x, y, c])))

/-- Canonical base-plus-offset form of a 64-bit address, with a proof `e = e'`. -/
def canonAddr (e : Expr) : MetaM (Expr × Option Expr) := do
  let e ← instantiateMVars e
  let e := stripMData e
  let e1 ← canonLits e
  let p1? ← if e1 == e then pure none else pure (some (← reflHint e e1))
  let (e1', p1'?) ← reassocAddLit e1
  let (e2, p2?) ← normAddrMeta e1'
  return (e2, ← transOpt (← transOpt p1? p1'?) p2?)

/-- Split a canonical address into `(base, offset mod 2^64)`; absolute addresses use base `0`. -/
def baseOff (e : Expr) : MetaM (Expr × Nat) := do
  let m := 1 <<< 64
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if let some v ← evalBV64Lit? (e.getArg! 5) then return (e.getArg! 4, v % m)
  if e.isAppOfArity ``HSub.hSub 6 then
    if let some v ← evalBV64Lit? (e.getArg! 5) then return (e.getArg! 4, (m - v % m) % m)
  if let some v ← evalBV64Lit? e then return (mkNatLit 0, v)
  return (e, 0)

def addrAdd (a : Expr) (off : Nat) : MetaM (Expr × Expr) := do
  let sum ← mkAppM ``HAdd.hAdd #[a, mkCanonBV64Lit off]
  let (c, p?) ← canonAddr sum
  match p? with
  | some p => return (c, p)
  | none => return (c, ← mkEqRefl c)

def isRegionAtom (e : Expr) : Bool :=
  e.isAppOfArity ``Arm64.memRegion 2

/-- Unfold one step of a reducible constant (`abbrev`, excluding structure projections) or a
    let-bound local (`set F : SepProp := ...`), stopping at primitive separation-logic atoms.
    Plain `def`s remain opaque. -/
def unfoldReducibleStep? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData.headBeta
  if isPrimSepAtom e then return none
  let r? ← match e.getAppFn with
    | .fvar fv => do
      let some v ← fv.getValue? | pure none
      pure (some (mkAppN v e.getAppArgs).headBeta)
    | .const name _ => do
      if name == ``Arm64.SepProp.sepConj || name == ``Arm64.SepProp.emp ||
          name == ``Arm64.SepProp.pure || name == ``Arm64.SepProp.sepExists then
        return none
      if (← isProjectionFn name) then return none
      unless (← getReducibilityStatus name) == .reducible do return none
      withReducible (unfoldDefinition? e)
    | _ => pure none
  let some r := r? | return none
  return some (← instantiateMVars r).consumeMData.headBeta

/-- Unfold reducible (`abbrev`) and let-bound local wrappers around a single separation-logic atom
    to their underlying atom, stopping before `∗`-trees (`expandProjTree` handles bundles). -/
partial def unfoldReducibleAtom (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  if fuel == 0 then return e
  let some e' ← unfoldReducibleStep? e | return e
  if e'.isAppOfArity ``Arm64.SepProp.sepConj 2 || e'.isConstOf ``Arm64.SepProp.emp then return e
  unfoldReducibleAtom e' (fuel - 1)

def congrApp (f : Expr) (args : Array Expr) (news : Array Expr) (prfs : Array (Option Expr)) :
    MetaM (Expr × Option Expr) := do
  if prfs.all Option.isNone then return (mkAppN f news, none)
  let mut prf ← mkEqRefl f
  for a in args, p? in prfs do
    match p? with
    | some p => prf ← mkCongr prf p
    | none => prf ← mkCongrFun prf a
  return (mkAppN f news, some prf)

/-- Compute the matching key of an atom and a proof `atom = key`. -/
def atomKey (e0 : Expr) : MetaM (Expr × Option Expr) := do
  let e := (stripMData (← instantiateMVars e0)).headBeta
  let mut cur := e
  let mut prf? : Option Expr := none
  let e1 ← unfoldReducibleAtom cur
  if e1 != cur then
    prf? := some (← reflHint cur e1)
    cur := e1
  if !isPrimSepAtom cur then
    let (e2, p2?) ← normSepPropMeta cur
    prf? ← transOpt prf? p2?
    cur := e2
  if proofLib.frameSplitContainers.get (← getOptions) then
    if let some (rhsNorm, eqPrf) ← expandStackFrameAtAtom? metaDisch cur then
      prf? ← transOpt prf? (some eqPrf)
      cur := rhsNorm
    else if let some (q, wExpr, some hCell) ← memRegionOrExistsCellInfo? cur then
      prf? ← transOpt prf? (some (← mkEqSymm hCell))
      cur := mkApp2 (mkConst ``Arm64.memRegion) q wExpr
  if !isPrimSepAtom cur then return (cur, prf?)
  let args := cur.getAppArgs
  if args.size == 0 then return (cur, prf?)
  let (a', pa?) ← canonAddr args[0]!
  let mut news := args.set! 0 a'
  let mut prfs : Array (Option Expr) := (Array.replicate args.size none).set! 0 pa?
  if isRegionAtom cur then
    let n := args[1]!
    if !n.hasFVar && !n.hasMVar then
      if let some v ← evalNatLitSolver? n then
        let n' := toExpr v
        if n' != n then
          news := news.set! 1 n'
          prfs := prfs.set! 1 (some (← reflHint n n'))
  let (key, pk?) ← congrApp cur.getAppFn args news prfs
  return (key, ← transOpt prf? pk?)

/-- Eta-expand structure-typed metavariable discriminants of a stuck `match` application into
    constructor applications of fresh metavariables. Returns `true` if something was expanded. -/
def etaExpandMatchDiscrs (e : Expr) : MetaM Bool := do
  let .const name _ := e.getAppFn | return false
  let some info ← getMatcherInfo? name | return false
  let args := e.getAppArgs
  let mut changed := false
  for k in [:info.numDiscrs] do
    let some d := args[info.numParams + 1 + k]? | continue
    let d ← instantiateMVars d
    unless d.isMVar do continue
    let ty ← whnfD (← inferType d)
    let .const sName lvls := ty.getAppFn | continue
    unless isStructure (← getEnv) sName do continue
    let ctor := getStructureCtor (← getEnv) sName
    let ctorE := mkAppN (mkConst ctor.name lvls) (ty.getAppArgs.extract 0 ctor.numParams)
    let (fields, _, _) ← forallMetaTelescope (← inferType ctorE)
    let val := mkAppN ctorE fields
    if ← withAssignableSyntheticOpaque (isDefEq d val) then changed := true
  return changed

/-- Unfold a structure projection applied to a concrete definition (such as `spec.pre x s`) to the
    underlying field, beta-reduced, with pattern-matching lambdas reduced. -/
def unfoldProjAtom? (e : Expr) : MetaM (Option Expr) := do
  let .const name _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  if info.fromClass then return none
  let args := e.getAppArgs
  if args.size ≤ info.numParams then return none
  let s ← whnfD args[info.numParams]!
  unless s.isAppOf info.ctorName do return none
  let sArgs := s.getAppArgs
  let some field := sArgs[info.numParams + info.i]? | return none
  let r := (mkAppN field (args.extract (info.numParams + 1) args.size)).headBeta
  if r.isAppOfArity ``Arm64.SepProp.sepConj 2 then return some r
  let r' ← whnfCore r
  if (← etaExpandMatchDiscrs r') then
    return some (← whnfCore (← instantiateMVars r'))
  return some r'

/-- Unfold an application of a reducible constant (`abbrev`) or let-bound local (`set F := ...`)
    when its body unfolds to a `∗`-tree or `emp`. Single-atom `abbrev`s remain folded in the tree
    and are unfolded in `atomKey` instead; plain `def`s remain opaque. -/
partial def unfoldAbbrevAtom? (e : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let some r ← unfoldReducibleStep? e | return none
  if r.isAppOfArity ``Arm64.SepProp.sepConj 2 || r.isConstOf ``Arm64.SepProp.emp then
    return some r
  unfoldAbbrevAtom? r (fuel - 1)

/-- Recursively unfold projection atoms and multi-atom abbreviations in a `∗`-tree. -/
partial def expandProjTree (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    return mkSep (← expandProjTree (e.getArg! 0) fuel) (← expandProjTree (e.getArg! 1) fuel)
  if fuel == 0 then return e
  if let some e' ← unfoldProjAtom? (stripMData e) then
    return ← expandProjTree e' (fuel - 1)
  if let some e' ← unfoldAbbrevAtom? (stripMData e) then
    return ← expandProjTree e' (fuel - 1)
  return e

def projStructArg? (e : Expr) : MetaM (Option Expr) := do
  if let .proj _ _ s := e then return some s
  let .const name _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  if info.fromClass then return none
  return e.getAppArgs[info.numParams]?

/-- Reduce projections of constructor applications in `e`. -/
def reduceCtorProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if let some s ← projStructArg? t then
      if s.getAppFn.isConst && (← isConstructorApp s) then
        return .done (← withReducible (whnf t))
    return .continue)

/-- Eta-expand structure-typed metavariables occurring as projection arguments in `e` into
    constructor applications of fresh metavariables, and reduce the resulting projections. -/
partial def etaExpandProjMVars (e : Expr) (fuel : Nat := 4) : MetaM Expr := do
  if fuel == 0 then return e
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr e fun t => do
    if let some s ← projStructArg? t then
      let s ← instantiateMVars s
      if s.isMVar then found.modify (·.push s)
  let ms ← found.get
  if ms.isEmpty then return e
  let mut changed := false
  for mv in ms do
    if ← mv.mvarId!.isAssigned then continue
    let ty ← whnfD (← inferType mv)
    let .const sName lvls := ty.getAppFn | continue
    unless isStructure (← getEnv) sName do continue
    unless (getStructureFields (← getEnv) sName).size ≤ 8 do continue
    let ctor := getStructureCtor (← getEnv) sName
    let ctorE := mkAppN (mkConst ctor.name lvls) (ty.getAppArgs.extract 0 ctor.numParams)
    let (fields, _, _) ← forallMetaTelescope (← inferType ctorE)
    if ← withAssignableSyntheticOpaque (isDefEq mv (mkAppN ctorE fields)) then changed := true
  unless changed do return e
  let e ← reduceCtorProjs (← instantiateMVars e)
  etaExpandProjMVars e (fuel - 1)

/-! ## Hypothesis atoms and search state -/

/-- A hypothesis atom (or a piece carved from one). -/
structure HAtom where
  /-- The atom as it occurs in the hypothesis tree. -/
  expr : Expr
  /-- Its matching key. -/
  key : Expr
  /-- Proof `expr = key` (`none`: syntactically equal). -/
  keyPrf? : Option Expr
  deriving Inhabited

/-- How a hypothesis atom was consumed. -/
inductive Use where
  /-- Unused (part of the frame). -/
  | free
  /-- Matches goal atom `gi`; `prf?` proves `expr = goal atom` (`none`: defeq at reducible). -/
  | goal (gi : Nat) (prf? : Option Expr)
  /-- Carved into `pieces` (hypothesis indices); `eq : key = rhs`, `rhs` a `∗`-tree of the pieces. -/
  | carved (pieces : Array Nat) (rhs eq : Expr)
  /-- Part of merge number `k`. -/
  | merged (k : Nat)
  deriving Inhabited

/-- A merge: pieces (hypothesis indices, in tree order) and `eq : p1 ∗ (p2 ∗ ...) = key of goal gi`. -/
structure Merge where
  pieces : Array Nat
  eq : Expr
  gi : Nat
  deriving Inhabited

structure SState where
  hyps : Array HAtom
  uses : Array Use
  merges : Array Merge := #[]
  /-- Deferred side goals `(mvar, type)` produced by argument-wise congruence. -/
  side : Array (Expr × Expr) := #[]
  deriving Inhabited

structure Ctx where
  goals : Array Expr
  /-- Precomputed keys of goal atoms without metavariables. -/
  closedKeys : Array (Option (Expr × Option Expr))
  maxSteps : Nat
  steps : IO.Ref Nat
  /-- Deepest failure: `(matched goal count, goal atom, normalized key)`. -/
  failure : IO.Ref (Nat × Option (Expr × Expr))
  /-- Last deferred value side condition that could not be proved. -/
  sideFail : IO.Ref (Option Expr)

def Ctx.goalKey (ctx : Ctx) (gi : Nat) : MetaM (Expr × Expr × Option Expr) := do
  let g ← instantiateMVars ctx.goals[gi]!
  if let some (some (k, p?)) := ctx.closedKeys[gi]? then return (g, k, p?)
  let (k, p?) ← atomKey g
  return (g, k, p?)

def isFrameMVar (e : Expr) : Bool := e.consumeMData.isMVar

/-- Fast compatibility filter for a `(hypothesis key, goal key)` pair. -/
def compatible (hk gk : Expr) : Bool :=
  let gf := gk.getAppFn
  if gf.isMVar then true
  else if gk.isFVar || hk.isFVar then hk == gk
  else if hk.getAppFn != gf || hk.getAppNumArgs != gk.getAppNumArgs then false
  else if isPrimSepAtom gk then
    let ha := hk.getArg! 0
    let ga := gk.getArg! 0
    if !ha.hasMVar && !ga.hasMVar && ha != ga then false
    else if isRegionAtom gk then
      let hn := hk.getArg! 1
      let gn := gk.getArg! 1
      !(!hn.hasMVar && !gn.hasMVar && hn.isAppOf ``OfNat.ofNat && gn.isAppOf ``OfNat.ofNat && hn != gn)
    else true
  else true

/-- Argument-wise congruence `hk = gk`: arguments with metavariables are unified; differing closed
    arguments become deferred side goals (never the address of a points-to or region atom). -/
def congrDeferred? (hk gk : Expr) : MetaM (Option (Expr × Array (Expr × Expr))) := do
  unless hk.getAppFn == gk.getAppFn && hk.getAppNumArgs == gk.getAppNumArgs do return none
  unless hk.getAppFn.isConst do return none
  let prim := isPrimSepAtom gk
  let hs := hk.getAppArgs
  let gs := gk.getAppArgs
  for a in hs, b in gs do
    if a.hasMVar || b.hasMVar then
      unless ← withReducibleAndInstances (isDefEq a b) do return none
  let mut prf ← mkEqRefl hk.getAppFn
  let mut side : Array (Expr × Expr) := #[]
  let mut idx := 0
  for a0 in hs, b0 in gs do
    let a ← instantiateMVars a0
    let b ← instantiateMVars b0
    if a == b then
      prf ← mkCongrFun prf a
    else if ← withReducibleAndInstances (isDefEq a b) then
      prf ← mkCongrFun prf a
    else if (prim && idx == 0) || a.hasMVar || b.hasMVar then
      return none
    else
      let ty ← mkEq a b
      let mv ← mkFreshExprMVar ty
      side := side.push (mv, ty)
      prf ← mkCongr prf mv
    idx := idx + 1
  return some (prf, side)

def Ctx.tick (ctx : Ctx) : MetaM Unit := do
  let n ← ctx.steps.get
  if n ≥ ctx.maxSteps then
    throwError "sep_frame: search budget exhausted after {n} candidate pairings \
      (raise `proofLib.sepFrameMaxSteps`, or give some frame/ghost arguments explicitly)"
  ctx.steps.set (n + 1)

/-- Try to match goal atom `gi` (instantiated `g`, key `gk`, proof `gp? : g = gk`) with
    hypothesis atom `i`. -/
def tryMatch (st : SState) (gi : Nat) (g gk : Expr) (gp? : Option Expr) (i : Nat)
    (deferOnly : Bool) : MetaM (Option SState) := do
  let h := st.hyps[i]!
  let symmG? ← match gp? with
    | some p => pure (some (← mkEqSymm p))
    | none => pure none
  let done (prf? : Option Expr) (side : Array (Expr × Expr)) : SState :=
    { st with uses := st.uses.set! i (.goal gi prf?), side := st.side ++ side }
  if deferOnly then
    if let some (pc, side) ← congrDeferred? h.key gk then
      return some (done (← transOpt (← transOpt h.keyPrf? (some pc)) symmG?) side)
    return none
  if h.expr == g then return some (done none #[])
  if h.key == gk then return some (done (← transOpt h.keyPrf? symmG?) #[])
  if ← withReducibleAndInstances (isDefEq h.key gk) then
    let g' ← instantiateMVars g
    if h.expr == g' then return some (done none #[])
    let gk' ← instantiateMVars gk
    let mid? ← if h.key == gk' then pure none else pure (some (← reflHint h.key gk'))
    let p? ← transOpt (← transOpt h.keyPrf? mid?) symmG?
    let p? ← match p? with
      | some p => pure (some p)
      | none => pure (some (← reflHint h.expr g'))
    return some (done p? #[])
  if !g.getAppFn.isMVar then
    if ← withReducibleAndInstances (isDefEq h.expr g) then
      let g' ← instantiateMVars g
      let p? ← if h.expr == g' then pure none else pure (some (← reflHint h.expr g'))
      return some (done p? #[])
  return none

/-- Candidate hypothesis atoms for a goal key, exact matches first. -/
def candidates (st : SState) (g gk : Expr) : Array Nat := Id.run do
  let mut best : Array Nat := #[]
  let mut rest : Array Nat := #[]
  for i in [:st.hyps.size] do
    if let .free := st.uses[i]! then
      let h := st.hyps[i]!
      if h.expr == g || h.key == gk then best := best.push i
      else if compatible h.key gk then rest := rest.push i
  return best ++ rest

def natLit? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?

/-- Closed region data of a key: `(address, base, offset, length)`. -/
def regionData? (k : Expr) : MetaM (Option (Expr × Expr × Nat × Nat)) := do
  unless isRegionAtom k do return none
  let a := k.getArg! 0
  if a.hasMVar then return none
  let some n := natLit? (k.getArg! 1) | return none
  let (b, o) ← baseOff a
  return some (a, b, o, n)

def memR (a : Expr) (len : Nat) : Expr := mkApp2 (mkConst ``Arm64.memRegion) a (toExpr len)

def le2pow64 (n : Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LE.le
    #[toExpr n, ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]])

/-- Build the carving equation `memRegion ha n = rhs` isolating `[gb, gb + k)` at offset `off`,
    returning `(rhs, eq, pieces)` or `none` if the addresses do not fold. -/
def carveEq? (ha gb : Expr) (n off k : Nat) : MetaM (Option (Expr × Expr × Array Expr)) := do
  let r := n - off - k
  let hle ← le2pow64 n
  let natEq (lhs : Expr) : MetaM Expr := do reflHint lhs (toExpr n)
  if off == 0 then
    let (c, hc) ← addrAdd ha k
    let hn ← natEq (← mkAppM ``HAdd.hAdd #[toExpr k, toExpr r])
    let eq := mkAppN (mkConst ``memRegion_carve_left)
      #[ha, c, toExpr n, toExpr k, toExpr r, hc, hn, hle]
    return some (mkSep (memR ha k) (memR c r), eq, #[memR ha k, memR c r])
  let (b', hb) ← addrAdd ha off
  unless b' == gb do return none
  if r == 0 then
    let hn ← natEq (← mkAppM ``HAdd.hAdd #[toExpr off, toExpr k])
    let eq := mkAppN (mkConst ``memRegion_carve_right)
      #[ha, gb, toExpr n, toExpr off, toExpr k, hb, hn, hle]
    return some (mkSep (memR ha off) (memR gb k), eq, #[memR ha off, memR gb k])
  let (c, hc) ← addrAdd gb k
  let hn ← natEq (← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[toExpr off, toExpr k], toExpr r])
  let eq := mkAppN (mkConst ``memRegion_carve)
    #[ha, gb, c, toExpr n, toExpr off, toExpr k, toExpr r, hb, hc, hn, hle]
  return some (mkSep (memR ha off) (mkSep (memR gb k) (memR c r)), eq,
    #[memR ha off, memR gb k, memR c r])

/-- Carve goal region `gi` out of a larger free hypothesis region (all alternatives). -/
def carveAlternatives (st : SState) (gi : Nat) (gk : Expr) (gp? : Option Expr) :
    MetaM (Array SState) := do
  let some (gb, gbase, goff, k) ← regionData? gk | return #[]
  if k == 0 then return #[]
  let m := 1 <<< 64
  let mut out : Array SState := #[]
  for i in [:st.hyps.size] do
    unless st.uses[i]! matches .free do continue
    let h := st.hyps[i]!
    let some (ha, hbase, hoff, n) ← regionData? h.key | continue
    unless hbase == gbase do continue
    let off := (goff + m - hoff) % m
    unless off + k ≤ n && !(off == 0 && k == n) do continue
    let some (rhs, eq, pieces) ← carveEq? ha gb n off k | continue
    let base := st.hyps.size
    let newHyps := pieces.map fun p => ({ expr := p, key := p, keyPrf? := none } : HAtom)
    let idxs := (List.range pieces.size).toArray.map (base + ·)
    let mut uses := st.uses.set! i (.carved idxs rhs eq) ++ Array.replicate pieces.size Use.free
    let some j := pieces.findIdx? (· == gk) | continue
    let symmG? ← match gp? with
      | some p => pure (some (← mkEqSymm p))
      | none => pure none
    uses := uses.set! (base + j) (.goal gi symmG?)
    out := out.push { st with hyps := st.hyps ++ newHyps, uses }
  return out

/-- Merge adjacent free hypothesis regions into goal region `gi`. -/
def mergeAlternative? (st : SState) (gi : Nat) (gk : Expr) : MetaM (Option SState) := do
  let some (_, gbase, goff, k) ← regionData? gk | return none
  let m := 1 <<< 64
  let mut regs : Array (Nat × Expr × Nat × Nat) := #[]
  for i in [:st.hyps.size] do
    unless st.uses[i]! matches .free do continue
    let some (ha, hbase, hoff, n) ← regionData? st.hyps[i]!.key | continue
    if hbase == gbase && n > 0 then regs := regs.push (i, ha, hoff, n)
  let mut cur := goff
  let mut remaining := k
  let mut chain : Array (Nat × Expr × Nat) := #[]
  let mut taken : Array Nat := #[]
  while remaining > 0 do
    let some (i, ha, _, n) := regs.find? fun (i, _, o, n) =>
        o == cur && n ≤ remaining && !taken.contains i
      | return none
    chain := chain.push (i, ha, n)
    taken := taken.push i
    cur := (cur + n) % m
    remaining := remaining - n
  unless chain.size ≥ 2 do return none
  let (_, aLast, nLast) := chain.back!
  let mut accTree := memR aLast nLast
  let mut accAddr := aLast
  let mut accLen := nLast
  let mut accEq? : Option Expr := none
  for t in (List.range (chain.size - 1)).reverse do
    let (_, a, n) := chain[t]!
    let (b', hb) ← addrAdd a n
    unless b' == accAddr do return none
    let N := n + accLen
    let hN ← reflHint (← mkAppM ``HAdd.hAdd #[toExpr n, toExpr accLen]) (toExpr N)
    let hle ← le2pow64 N
    let mergeEq := mkAppN (mkConst ``memRegion_merge) #[a, accAddr, toExpr n, toExpr accLen, toExpr N, hb, hN, hle]
    let pa := memR a n
    let lhsTree := mkSep pa accTree
    let step ← match accEq? with
      | some e => mkEqTrans (← mkCongrArg (mkApp (mkConst ``Arm64.SepProp.sepConj) pa) e) mergeEq
      | none => pure mergeEq
    accTree := lhsTree
    accAddr := a
    accLen := N
    accEq? := some step
  let some eq := accEq? | return none
  unless memR accAddr accLen == gk do return none
  let kIdx := st.merges.size
  let mut uses := st.uses
  for (i, _, _) in chain do
    uses := uses.set! i (.merged kIdx)
  return some { st with uses, merges := st.merges.push { pieces := chain.map (·.1), eq, gi } }

/-- Discharge deferred value side goals of a complete matching; returns `false` on failure. -/
def dischargeSide (ctx : Ctx) (disch : Disch) (st : SState) : TacticM Bool := do
  let leaveSide := proofLib.frameSplitLeaveSideGoals.get (← getOptions)
  for (mv, ty) in st.side do
    if ← mv.mvarId!.isAssigned then continue
    let ty ← instantiateMVars ty
    match ← disch ty with
    | some p => mv.mvarId!.assign p
    | none =>
      if leaveSide && !ty.hasExprMVar then continue
      ctx.sideFail.set (some ty)
      return false
  return true

/-- Depth-first search with backtracking over the remaining goal atoms. Exact matches of all
    candidates are tried before matches that defer value equalities; a complete matching is
    accepted only if its deferred value side conditions are provable. -/
partial def search (ctx : Ctx) (disch : Disch) (st : SState) (remaining : List Nat) (depth : Nat) :
    TacticM (Option SState) := do
  if remaining.isEmpty then
    if ← dischargeSide ctx disch st then return some st else return none
  let mut best : Option (Nat × Expr × Expr × Option Expr × Array Nat) := none
  for gi in remaining do
    let (g, gk, gp?) ← ctx.goalKey gi
    let cs := candidates st g gk
    let better := match best with
      | none => true
      | some (_, bg, _, _, bcs) => cs.size < bcs.size || (cs.size == bcs.size && bg.hasMVar && !g.hasMVar)
    if better then best := some (gi, g, gk, gp?, cs)
    if cs.isEmpty then break
  let some (gi, g, gk, gp?, cs) := best | return none
  let rest := remaining.erase gi
  let allowDefer := (cs.size == 1 || isPrimSepAtom gk) && proofLib.frameSplitNearMiss.get (← getOptions)
  for deferPass in (if allowDefer then [false, true] else [false]) do
    for i in cs do
      ctx.tick
      let saved ← saveState
      if let some st' ← tryMatch st gi g gk gp? i deferPass then
        if let some r ← search ctx disch st' rest (depth + 1) then return some r
      saved.restore
  for st' in ← carveAlternatives st gi gk gp? do
    ctx.tick
    let saved ← saveState
    if let some r ← search ctx disch st' rest (depth + 1) then return some r
    saved.restore
  if let some st' ← mergeAlternative? st gi gk then
    ctx.tick
    let saved ← saveState
    if let some r ← search ctx disch st' rest (depth + 1) then return some r
    saved.restore
  let (d, _) ← ctx.failure.get
  if depth ≥ d then ctx.failure.set (depth, some (g, gk))
  return none

/-! ## Proof construction -/

/-- Replace the atoms of a `∗`-tree (in `atoms` order) by `repl k = (new, proof atom = new)`,
    returning the new tree and a congruence proof. -/
partial def replaceAtomsCongr (e : Expr) (repl : Nat → MetaM (Expr × Option Expr)) :
    MetaM (Expr × Option Expr) := do
  let r ← (go e).run 0
  return r.1
where
  go (e : Expr) : StateRefT Nat MetaM (Expr × Option Expr) := do
    let e := e.consumeMData.headBeta
    if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
      let l := e.getArg! 0
      let r := e.getArg! 1
      let (l', pl?) ← go l
      let (r', pr?) ← go r
      let fn := mkConst ``Arm64.SepProp.sepConj
      let e' := mkApp2 fn l' r'
      if pl?.isNone && pr?.isNone then return (e', none)
      let p1 ← match pl? with
        | some p => mkCongrArg fn p
        | none => mkEqRefl (mkApp fn l')
      let p2 ← match pr? with
        | some p => mkCongr p1 p
        | none => mkCongrFun p1 r'
      return (e', some p2)
    let e := (stripMData e).headBeta
    if e.isConstOf ``Arm64.SepProp.emp then return (e, none)
    let k ← get
    set (k + 1)
    repl k

/-- The final form of hypothesis atom `i` (a `∗`-tree after carving) and a proof `expr = form`. -/
partial def finalForm (ctx : Ctx) (st : SState) (i : Nat) : MetaM (Expr × Option Expr) := do
  let h := st.hyps[i]!
  match st.uses[i]! with
  | .free => return (h.expr, none)
  | .merged _ => return (h.key, h.keyPrf?)
  | .goal gi prf? =>
    match prf? with
    | some p => return (← instantiateMVars ctx.goals[gi]!, some p)
    | none => return (h.expr, none)
  | .carved pieces rhs eq =>
    let (rhs', pr?) ← replaceAtomsCongr rhs fun k => finalForm ctx st pieces[k]!
    let p ← transOpt (← transOpt h.keyPrf? (some eq)) pr?
    return (rhs', p)

def removeOnce (as xs : Array Expr) : Option (Array Expr) := Id.run do
  let mut as := as
  for x in xs do
    let some i := as.findIdx? (· == x) | return none
    as := as.eraseIdx! i
  return some as

/-- Expand pure and existential atoms of goal `G`, returning the spatial goal and a continuation
    transforming a proof of `J spatial` into a proof of `J G`. -/
partial def expandGoalJ (j : Judg) (G : Expr) (pures : IO.Ref (Array (Expr × Expr)))
    (shouldOpenExists : Expr → MetaM Bool := fun _ => pure true) :
    MetaM (Expr × (Expr → MetaM Expr)) := do
  let G := (← instantiateMVars G).consumeMData
  let as := atoms G
  let mut idx? : Option Nat := none
  for hi : i in [:as.size] do
    let a := as[i]
    if a.isAppOfArity ``Arm64.SepProp.pure 1 then
      idx? := some i
      break
    if a.isAppOfArity ``Arm64.SepProp.sepExists 2 && !(j matches .eq _) then
      if ← shouldOpenExists a then
        idx? := some i
        break
  let some i := idx? | return (G, pure)
  let a := as[i]!
  let rest := mkSepList (as.eraseIdx! i)
  let ac (p : Expr) : MetaM Expr := do
    let some r ← j.ac? (mkSep a rest) G p
      | throwError "sep_frame: internal error (AC transport after goal expansion)"
    return r
  if a.isAppOfArity ``Arm64.SepProp.pure 1 then
    let φ := a.getArg! 0
    let hφ ← mkFreshExprMVar φ
    pures.modify (·.push (hφ, φ))
    let (G', k) ← expandGoalJ j rest pures shouldOpenExists
    return (G', fun p => do
      let p ← k p
      ac (j.pureIntro φ hφ rest p))
  else
    let α := a.getArg! 0
    let f := a.getArg! 1
    let w ← mkFreshExprMVar α
    let (G', k) ← expandGoalJ j (mkSep (f.beta #[w]).headBeta rest) pures shouldOpenExists
    let u ← getLevel α
    return (G', fun p => do
      let p ← k p
      let p' ← j.existsIntro u α f w rest p
      ac (← mkExpectedTypeHint p' (j.type (mkSep a rest))))

/-- Result of the solver: proof term, optional inferred frame, and remaining side goals. -/
structure Result where
  proof : Expr
  frame : Option Expr
  sideGoals : Array MVarId := #[]

def failureMsg (ctx : Ctx) (st : SState) : MetaM MessageData := do
  let (_, fail?) ← ctx.failure.get
  let free := (List.range st.hyps.size).toArray.filterMap fun i =>
    if st.uses[i]! matches .free then some st.hyps[i]!.expr else none
  let freeKeys := (List.range st.hyps.size).toArray.filterMap fun i =>
    if st.uses[i]! matches .free then some st.hyps[i]!.key else none
  let freeMsg := if free.isEmpty then m!"(none)"
    else MessageData.joinSep (free.toList.map toMessageData) m!", "
  if let some ty ← ctx.sideFail.get then
    return m!"sep_frame: cannot prove the value side condition{indentExpr ty}"
  match fail? with
  | some (g, gk) =>
    let normMsg := if g == gk then m!"" else m!"\n(normalized:{indentExpr gk})"
    let nonMemRegFreeKeys := freeKeys.filter fun k => !(k.consumeMData.isAppOfArity ``Arm64.memRegion 2)
    let hints ← explainAtomMismatchHints gk nonMemRegFreeKeys
    let hintSuffix :=
      if hints.isEmpty then m!""
      else m!"\n" ++ MessageData.joinSep hints.toList m!"\n"
    return m!"sep_frame: no hypothesis atom matches goal atom{indentExpr g}{normMsg}\n\
      unmatched hypothesis atoms: {freeMsg}{hintSuffix}"
  | none => return m!"sep_frame: no match found; unmatched hypothesis atoms: {freeMsg}"

/-- Solve `J G` from `hP : J P`, throwing an error on failure. -/
def solve (disch : Disch) (j : Judg) (P hP G : Expr) : TacticM Result := do
  let P ← instantiateMVars P
  let G ← instantiateMVars G
  let P0 ← reduceCtorProjs (← zetaReduce (← expandProjTree P))
  let G0 ← reduceCtorProjs (← etaExpandProjMVars (← zetaReduce (← expandProjTree G)))
  let P' ← expandSepUnfoldTree P0 G0
  let hP ← if P' == P then pure hP else do pure (j.transport P P' (← reflHint P P') hP)
  let G' ← expandSepUnfoldTree G0 P0
  let pures ← IO.mkRef #[]
  let shouldOpenExists (a : Expr) : MetaM Bool := do
    unless proofLib.frameSplitContainers.get (← getOptions) do return true
    let some (q, _, _) ← memRegionOrExistsCellInfo? a | return true
    let (qb, _) ← baseOff (← canonAddr q).1
    let pAtoms := atoms P'
    let hasRegionAtBase ← pAtoms.anyM fun pa => do
      let pa := stripMData pa
      if pa.isAppOfArity ``Arm64.memRegion 2 || pa.isAppOfArity ``Arm64.stackFrameAt 2 ||
          pa.isAppOfArity ``Arm64.stackFrame16At 1 || pa.isAppOfArity ``Arm64.stackFrame32At 1 then
        let (pb, _) ← baseOff (← canonAddr (pa.getArg! 0)).1
        return pb == qb
      return false
    let hasPointsToAtBase ← pAtoms.anyM fun pa => do
      let pa := stripMData pa
      if let some (_, _, addr) := pointsToAtomInfo? pa then
        let (pb, _) ← baseOff (← canonAddr addr).1
        return pb == qb
      return false
    return !(hasRegionAtBase && !hasPointsToAtBase)
  let (Gs, k) ← expandGoalJ j G' pures shouldOpenExists
  let PPrev := P'
  let (P', hPB?) ← preSplitPointsToBytes (liftTacDisch disch) PPrev none Gs
  let hP := j.transportOpt PPrev P' hPB? hP
  let hypAtoms := atoms P'
  let goalAtoms := atoms (← instantiateMVars Gs)
  let mut hyps : Array HAtom := #[]
  for a in hypAtoms do
    let (key, p?) ← atomKey a
    hyps := hyps.push { expr := a, key, keyPrf? := p? }
  let mut frames : Array Expr := #[]
  let mut spatial : Array Expr := #[]
  for a in goalAtoms do
    if isFrameMVar a then frames := frames.push a.consumeMData else spatial := spatial.push a
  let mut closedKeys : Array (Option (Expr × Option Expr)) := #[]
  for g in spatial do
    if g.hasMVar then closedKeys := closedKeys.push none
    else closedKeys := closedKeys.push (some (← atomKey g))
  let ctx : Ctx := {
    goals := spatial, closedKeys
    maxSteps := proofLib.sepFrameMaxSteps.get (← getOptions)
    steps := ← IO.mkRef 0
    failure := ← IO.mkRef (0, none)
    sideFail := ← IO.mkRef none }
  let mut st0 : SState := { hyps, uses := Array.replicate hyps.size .free }
  let mut remaining : List Nat := []
  for gi in [:spatial.size] do
    let g := spatial[gi]!
    let mut done := false
    if let some (some (gk, gp?)) := closedKeys[gi]? then
      if let some i := (List.range st0.hyps.size).find? fun i =>
          st0.uses[i]! matches .free && (st0.hyps[i]!.expr == g || st0.hyps[i]!.key == gk) then
        let h := st0.hyps[i]!
        let prf? ← if h.expr == g then pure none else do
          let symmG? ← match gp? with
            | some p => pure (some (← mkEqSymm p))
            | none => pure none
          transOpt h.keyPrf? symmG?
        st0 := { st0 with uses := st0.uses.set! i (.goal gi prf?) }
        done := true
    unless done do remaining := remaining ++ [gi]
  let res ← withAssignableSyntheticOpaque (search ctx disch st0 remaining 0)
  let some st := res | throwError (← failureMsg ctx st0)
  let (cur, e1?) ← replaceAtomsCongr P' fun k => finalForm ctx st k
  let mut h := j.transportOpt P' cur e1? hP
  let mut cur := cur
  for mg in st.merges do
    let keys := mg.pieces.map fun i => st.hyps[i]!.key
    let some rest := removeOnce (atoms (← instantiateMVars cur)) keys
      | throwError "sep_frame: internal error (merge pieces not found)"
    let restE := mkSepList rest
    let A := mkSepList keys
    let some hA ← j.ac? cur (mkSep A restE) h
      | throwError "sep_frame: internal error (AC before merge)"
    let g ← instantiateMVars spatial[mg.gi]!
    let (_, gk, gp?) ← ctx.goalKey mg.gi
    let _ := gk
    let eqG ← match gp? with
      | some p => mkEqTrans mg.eq (← mkEqSymm p)
      | none => pure mg.eq
    let eqTree ← mkCongrFun (← mkCongrArg (mkConst ``Arm64.SepProp.sepConj) eqG) restE
    h := j.transport (mkSep A restE) (mkSep g restE) eqTree hA
    cur := mkSep g restE
  let leftovers := (List.range st.hyps.size).toArray.filterMap fun i =>
    if st.uses[i]! matches .free then some st.hyps[i]!.expr else none
  let mut frameVal? : Option Expr := none
  if let some f := frames[0]? then
    let val := mkSepList leftovers
    unless ← withAssignableSyntheticOpaque (isDefEq f val) do
      throwError "sep_frame: cannot assign the frame{indentExpr f}\nto{indentExpr val}"
    frameVal? := some val
    for f' in frames.extract 1 frames.size do
      unless ← withAssignableSyntheticOpaque (isDefEq f' (mkConst ``Arm64.SepProp.emp)) do
        throwError "sep_frame: cannot assign the extra frame{indentExpr f'} to `emp`"
  let Gs ← instantiateMVars Gs
  let spatialPrf ←
    if frames.isEmpty && !leftovers.isEmpty then
      match j with
      | .sat m =>
        let L := mkSepList leftovers
        let some p ← j.ac? cur (mkSep Gs L) h
          | throwError "sep_frame: internal error (final AC)"
        pure (mkAppN (mkConst ``Satisfies.of_sep_left) #[m, Gs, L, p])
      | _ =>
        let L := MessageData.joinSep (leftovers.toList.map toMessageData) m!", "
        throwError "sep_frame: unmatched hypothesis atoms in an entailment/equation goal without \
          a frame metavariable: {L}"
    else
      let some p ← j.ac? cur Gs h | throwError "sep_frame: internal error (final AC)"
      pure p
  let leaveSide := proofLib.frameSplitLeaveSideGoals.get (← getOptions)
  let mut openSideMVars : Array MVarId := #[]
  for (mv, ty) in st.side do
    if ← mv.mvarId!.isAssigned then continue
    let ty ← instantiateMVars ty
    if let some p ← disch ty then
      mv.mvarId!.assign p
    else if leaveSide && !ty.hasExprMVar then
      openSideMVars := openSideMVars.push mv.mvarId!
    else
      throwError "sep_frame: cannot prove the value side condition{indentExpr ty}"
  for (hφ, φ) in ← pures.get do
    let φ ← instantiateMVars φ
    let some p ← proveConj disch φ
      | throwError "sep_frame: cannot prove the pure side condition{indentExpr φ}"
    hφ.mvarId!.assign p
  let prf ← instantiateMVars (← k spatialPrf)
  let prf ← if G' == G then pure prf else mkExpectedTypeHint prf (← instantiateMVars (j.type G))
  if prf.hasExprMVar then
    let ms ← getMVars prf
    let unexplained := ms.filter fun m => !openSideMVars.contains m
    unless unexplained.isEmpty do
      let names ← unexplained.mapM fun m => return m!"{mkMVar m} : {← instantiateMVars (← m.getType)}"
      throwError "sep_frame: underdetermined metavariables (ghosts or witnesses) remain: \
        {MessageData.joinSep names.toList m!", "}"
  return { proof := prf, frame := ← frameVal?.mapM instantiateMVars, sideGoals := openSideMVars }

/-! ## Frame-procedure hook -/

/-- A frame procedure: given a discharger, a memory `m`, a hypothesis `h : m ⊨ P`, and a goal
    `m ⊨ G`, return a proof of `m ⊨ G` assigning metavariables in `G`, or `none`. -/
abbrev FrameProc := Disch → (m P h G : Expr) → TacticM (Option Expr)

/-- Backtracking frame procedure (`sep_frame`); restores metavariable state on failure. -/
def frameProc : FrameProc := fun disch m P h G => do
  let saved ← Tactic.saveState
  try
    let r ← solve disch (.sat m) P h G
    unless r.sideGoals.isEmpty do
      saved.restore
      return none
    return some r.proof
  catch _ =>
    saved.restore
    return none

/-- Find the most recent hypothesis `h : m' ⊨ P` matching `m`, trying `findSatHyp?`
    (reducible defeq) first and falling back to default transparency. -/
def findSatHypForFrame? (m : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some res ← findSatHyp? m then return some res
  let m := stripMData m
  for decl in (← getLCtx).decls.toList.reverse do
    let some decl := decl | continue
    if decl.isImplementationDetail then continue
    let ty := stripMData (← instantiateMVars decl.type)
    if ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 then
      if ← isDefEq (ty.getArg! 1) m then
        let m' ← instantiateMVars m
        let h ← if ty.getArg! 1 == m' then pure decl.toExpr
          else mkExpectedTypeHint decl.toExpr (mkApp2 (mkConst ``Arm64.SepProp.Satisfies) (ty.getArg! 0) m')
        return some (h, ty.getArg! 0)
  return none

/-- Close the main goal `m ⊨ G` from the latest hypothesis over `m` using the backtracking frame
    solver; returns `false` (restoring state) on mismatch or failure. -/
def closeSatBacktrack? (disch : Disch) : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let ty := stripMData (← instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 do return false
    let m := ty.getArg! 1
    let some (h, P) ← findSatHypForFrame? m | return false
    let m ← instantiateMVars m
    let saved ← Tactic.saveState
    try
      let r ← solve disch (.sat m) P h (ty.getArg! 0)
      g.assign r.proof
      replaceMainGoal r.sideGoals.toList
      return true
    catch _ =>
      saved.restore
      return false

/-! ## Tactic front end -/

def defaultDisch : TacticM Disch := do
  return tacDisch (← `(tactic| first
    | rfl | assumption | decide | (wp_omega_bounded; done) | (simp_all; done) | (bv_fallback; done)))

/-- Close the main goal with the frame solver; returns the inferred frame if any. -/
def sepFrameCore (disch : Disch) : TacticM (Option Expr) := do
  let g ← getMainGoal
  let (_, g) ← g.intros
  replaceMainGoal [g]
  g.withContext do
    let ty := stripMData (← instantiateMVars (← g.getType))
    let ty ← if ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 || ty.isAppOfArity ``Arm64.SepProp.Entails 2 ||
        ty.isAppOfArity ``Eq 3 || ty.isAppOfArity ``SepFrame 3 then pure ty else whnfR ty
    if ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 then
      let G := ty.getArg! 0
      let m := ty.getArg! 1
      let some (h, P) ← findSatHypForFrame? m | throwError "sep_frame: no hypothesis `{m} ⊨ _`"
      let m ← instantiateMVars m
      let r ← solve disch (.sat m) P h G
      g.assign r.proof
      replaceMainGoal r.sideGoals.toList
      return r.frame
    if ty.isAppOfArity ``Arm64.SepProp.Entails 2 then
      let P := ty.getArg! 0
      let j := Judg.ent P
      let r ← solve disch j P (j.refl.get!) (ty.getArg! 1)
      g.assign r.proof
      replaceMainGoal r.sideGoals.toList
      return r.frame
    if ty.isAppOfArity ``SepFrame 3 then
      let sub := ty.getArg! 0
      let full := ty.getArg! 1
      let fr := ty.getArg! 2
      let j := Judg.eq full
      let r ← solve disch j full (j.refl.get!) (mkSep sub fr)
      g.assign (← mkAppM ``SepFrame.mk #[r.proof])
      replaceMainGoal r.sideGoals.toList
      return r.frame
    if let some (α, lhs, rhs) := ty.eq? then
      if α.isConstOf ``Arm64.SepProp then
        let j := Judg.eq lhs
        let r ← solve disch j lhs (j.refl.get!) rhs
        g.assign r.proof
        replaceMainGoal r.sideGoals.toList
        return r.frame
    let shapeHint :=
      if ty.getAppFn.constName?.any isSepWPHeadName then
        m!"\nhint: goal is a `SepWP` weakest precondition; use `wp_done` (at target PC), `wp_steps`, or `wp_conv_pre => ...` to rewrite the precondition"
      else m!""
    throwError "sep_frame: expected a goal `m ⊨ Q`, `∀ R, m ⊨ P ∗ R → m ⊨ Q`, `P ⊢ Q`, \
      `P = Q` or `SepFrame Sub Full F` (goal head: `{goalHeadDesc ty}`), got{indentExpr ty}{shapeHint}"

/-- Close a separation-logic goal by frame inference with bounded backtracking:
    `m ⊨ Q` (from the latest hypothesis `m ⊨ P`), `∀ R, m ⊨ P ∗ R → m ⊨ Q`, `P ⊢ Q`, `P = Q`,
    or `SepFrame Sub Full F`. `Q` may contain ghost metavariables inside atoms and a naked
    metavariable atom receiving the unmatched hypothesis atoms. Value equalities and pure atoms
    are discharged by `rfl`, `assumption`, `decide`, `wp_omega_bounded`, `simp_all`, or
    `bv_fallback`, or by a custom `(disch := tac)`. `stackAt`/`memRegion` atoms may be carved
    from or merged into adjacent regions with literal offsets. -/
syntax (name := sepFrameTac) "sep_frame" (" (" &"disch" " := " tacticSeq ")")? : tactic

/-- Like `sep_frame`, additionally logging the inferred frame. -/
syntax (name := sepFrameQTac) "sep_frame?" (" (" &"disch" " := " tacticSeq ")")? : tactic

def dischOf (stx? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Disch := do
  match stx? with
  | some t => return tacDisch (← `(tactic| ($t)))
  | none => defaultDisch

elab_rules : tactic
  | `(tactic| sep_frame $[(disch := $t)]?) => do
    let _ ← sepFrameCore (← dischOf t)

elab_rules : tactic
  | `(tactic| sep_frame? $[(disch := $t)]?) => do
    let g ← getMainGoal
    let fr ← sepFrameCore (← dischOf t)
    g.withContext do
      match fr with
      | some f => logInfo m!"sep_frame: frame := {f}"
      | none => logInfo m!"sep_frame: no frame metavariable (unmatched atoms dropped)"

/-- Apply `v` to the main goal like `apply`, proving `SepProp` arguments that do not unify
    syntactically equal by `sep_frame` (assigning frame metavariables in `v`'s conclusion). -/
def sepFrameApplyCore (disch : Disch) (v : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let T := (← instantiateMVars (← g.getType)).consumeMData
    let vT ← instantiateMVars (← inferType v)
    let (mvs, bis, body) ← forallMetaTelescope vT
    let body := body.consumeMData
    unless body.getAppFn == T.getAppFn && body.getAppNumArgs == T.getAppNumArgs do
      throwError "sep_frame_apply: the conclusion{indentExpr body}\ndoes not have the head of the \
        goal{indentExpr T}"
    let tArgs := T.getAppArgs
    let bArgs := body.getAppArgs
    let sepTy := mkConst ``Arm64.SepProp
    let mut sepIdx : Array Nat := #[]
    for i in [:tArgs.size] do
      if ← isDefEq (← inferType tArgs[i]!) sepTy then
        sepIdx := sepIdx.push i
      else unless ← isDefEq tArgs[i]! bArgs[i]! do
        throwError "sep_frame_apply: cannot unify argument {i}{indentExpr bArgs[i]!}\nwith\
          {indentExpr tArgs[i]!}"
    let mut cur := T
    let mut prf? : Option Expr := none
    for i in sepIdx do
      let a ← instantiateMVars tArgs[i]!
      let b ← instantiateMVars bArgs[i]!
      if ← withReducible (isDefEq a b) then continue
      let j := Judg.eq a
      let r ← solve disch j a (j.refl.get!) b
      let b ← instantiateMVars b
      let curArgs := (← instantiateMVars cur).getAppArgs
      let motive ← withLocalDeclD `X sepTy fun x =>
        mkLambdaFVars #[x] (mkAppN cur.getAppFn (curArgs.set! i x))
      let next := mkAppN cur.getAppFn (curArgs.set! i b)
      let step ← mkCongrArg motive r.proof
      prf? ← transOpt prf? (some step)
      cur := next
    for mv in mvs, bi in bis do
      if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
        mv.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType mv)))
    let pf := mkAppN v mvs
    let pf ← match prf? with
      | some e => mkEqMPR e pf
      | none => pure pf
    g.assign pf
    let newGoals ← mvs.filterMapM fun mv => do
      if ← mv.mvarId!.isAssigned then return none else return some mv.mvarId!
    replaceMainGoal newGoals.toList

/-- Apply `e` (typically a frame rule with the frame argument omitted) to the goal, proving
    `SepProp` arguments equal via `sep_frame` (`P = P0 ∗ ?F`) to assign the frame. Remaining
    explicit premises become new goals. -/
syntax (name := sepFrameApplyTac) "sep_frame_apply " term (" (" &"disch" " := " tacticSeq ")")? :
  tactic

elab_rules : tactic
  | `(tactic| sep_frame_apply $e $[(disch := $t)]?) => withMainContext do
    let v ← elabTermForApply e (mayPostpone := true)
    Term.synthesizeSyntheticMVarsNoPostponing
    sepFrameApplyCore (← dischOf t) (← instantiateMVars v)

end SepFrameInfer

end

end ProofLib
