/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public meta import ProofLib.Meta.ToExpr
public meta import Arm64.Trusted.Spec.Hoare
public import Arm64
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Solver
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPp
public import ProofLib.VCGen
public meta import ProofLib.SpecShape
import Arm64.Trusted.Spec.SepLogic

/-!
# Specification Audit Commands

Diagnostic commands and predicates for checking subroutine specifications (`Arm64.Spec.NonVacuous`):
- `#spec_nonvacuous <spec>` (and strict `#spec_nonvacuous!`): checks pairwise disjointness of
  spatial footprint atoms (`SepBlock`) and non-contradiction of pure conditions (`⌜φ⌝` together
  with `s0.spAligned`) via bounded static witness search and decision procedures. Two blocks on
  distinct symbolic base pointers are treated as potentially disjoint unless the pure hypotheses
  force them to alias; higher-order or recursive predicates and non-linear arithmetic exceeding
  the heartbeat budget are not model-checked in full.
- `#spec_smoke <progOrCode> <entry> <spec>` (and `#spec_smoke <fnCode> <spec>`, `#spec_smoke!`,
  tactic `spec_smoke`): runs bounded forward symbolic execution (`wp_init` / `wp_start`,
  `wp_steps`, `wp_if`) under a heartbeat cap and reports reached return paths or the first stuck
  PC, decoded instruction, and missing points-to cell.
- `#spec_lint <spec>` (and `#spec_lint!`): inspects elaborated `Spec` terms for input-pinned or
  guard-only preconditions, aliased symbolic allocation pointers in `post`, and deallocation specs
  that retain freed pointer ownership.
- `#spec_audit_env`: emits `SPEC_AUDIT_ENV_JSON|...` coverage and lint metadata, failing closed
  on theorems whose conclusion mentions a spec predicate (`specHeads`) in an unrecognized shape.

Non-bang commands log via `logInfo` and never fail the build under `warningAsError := true`.
-/

namespace ProofLib

open Lean Elab Tactic Meta
open Arm64

@[expose] public section

/-- Mathematical non-vacuity proposition for an `Arm64.Spec`: there exist ghost state `x : α`,
    an AAPCS64-aligned entry state `s0 : State`, and a memory `m` satisfying `spec.pre x s0`. -/
def _root_.Arm64.Spec.NonVacuous {α : Type} (spec : Spec α) : Prop :=
  ∃ (x : α) (s0 : Arm64.State), s0.spAligned = true ∧ (s0.mem ⊨ spec.pre x s0)

end

public meta section

namespace SpecAudit

/-- Primitive `SepProp` constants that should not be unfolded when expanding user-defined
    separation-logic helper predicates. -/
private def primitiveSepConsts : Array Name := #[
  ``SepProp.emp, ``SepProp.pure, ``SepProp.sepConj, ``SepProp.sepImp, ``SepProp.bupd,
  ``SepProp.sepExists, ``SepProp.complementSep,
  ``ghostMapAuth, ``ghostMapElem,
  ``Arm64.pointsTo8, ``Arm64.pointsTo16, ``Arm64.pointsTo32, ``Arm64.pointsTo64,
  ``Arm64.pointsTo128, ``Arm64.pointsToBytes, ``Arm64.pointsToWords64,
  ``Arm64.pointsTo8RO, ``Arm64.pointsTo16RO, ``Arm64.pointsTo32RO, ``Arm64.pointsTo64RO,
  ``Arm64.pointsTo128RO, ``Arm64.pointsToBytesRO, ``Arm64.pointsToWords64RO,
  ``Arm64.pointsTo8ProtNone, ``Arm64.pointsToBytesProtNone,
  ``Arm64.pointsTo8Lazy, ``Arm64.pointsTo16Lazy, ``Arm64.pointsTo32Lazy,
  ``Arm64.pointsTo64Lazy, ``Arm64.pointsTo128Lazy,
  ``Arm64.regionBlock, ``Arm64.regionBlockRO, ``Arm64.regionBlockProtNone,
  ``Arm64.memRegion, ``Arm64.memRegionProtNone, ``Arm64.memRegionLazy,
  ``Arm64.memMapped, ``Arm64.anyHeap,
  ``Arm64.stackFrame16At, ``Arm64.stackFrame32At
]

/-- Collect non-primitive constants whose return type is `SepProp` (or `Arm64.CType.SemType` /
    `Arm64.CType.ValType` descriptors used in `c_type_spec`) appearing in `e`.
    When `keepStackFrameAt` is `true`, `stackFrameAt` is left folded so that `extractBlockInfo?`
    can treat it as the block `[sp - n, sp)` instead of dropping an opaque `ite` expansion. -/
private def collectUserSepDefs (e : Expr) (includeAllocSeq : Bool := false)
    (keepStackFrameAt : Bool := false) : MetaM (Array Ident) := do
  let env ← getEnv
  let ref ← IO.mkRef (#[] : Array Ident)
  e.forEach fun sub => do
    if let .const nm _ := sub then
      if !primitiveSepConsts.contains nm && nm != ``Arm64.stackFrame &&
          !(keepStackFrameAt && nm == ``Arm64.stackFrameAt) then
        if let some info := env.find? nm then
          let allowRec := includeAllocSeq && nm == `ProofLib.Allocator.allocSeq
          if info.hasValue && (!(isRecCore env nm) || allowRec) then
            let retTy := info.type.getForallBody
            if retTy.isConstOf ``Arm64.SepProp ||
               retTy.isAppOf `Arm64.CType.SemType ||
               retTy.isAppOf `Arm64.CType.ValType then
              let arr ← ref.get
              if !arr.any (·.getId == nm) then
                ref.set (arr.push (mkIdent nm))
  ref.get

/-- Flatten a `SepProp` expression `e` across `∗` (`SepProp.sepConj`), checking syntactic
    `SepProp.sepConj` / `SepProp.emp` / `SepProp.pure` / primitive spatial predicates before
    calling `whnf` so complex spatial payloads (such as `pointsToBytes` with `List.take`) are
    never unfolded by unconstrained `whnf`. -/
partial def flattenSepConj (e : Expr) (fuel : Nat := 8) : MetaM (Array Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isConstOf ``Arm64.SepProp.emp then
    return #[]
  if e.isAppOfArity ``Arm64.SepProp.bupd 1 then
    return ← flattenSepConj (e.getArg! 0) fuel
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    let lhs ← flattenSepConj (e.getArg! 0) fuel
    let rhs ← flattenSepConj (e.getArg! 1) fuel
    return lhs ++ rhs
  if primitiveSepConsts.any (fun nm => e.isAppOf nm) ||
     e.isAppOf ``Arm64.stackFrame || e.isAppOfArity ``Arm64.stackFrameAt 2 ||
     e.isAppOf ``ite then
    return #[e]
  if fuel == 0 then
    return #[e]
  let eWhnf ← withReducible (whnf e)
  if eWhnf != e then
    return ← flattenSepConj eWhnf (fuel - 1)
  if let some eUnf ← unfoldDefinition? e then
    return ← flattenSepConj eUnf (fuel - 1)
  return #[e]

private partial def isAtomicSymTerm (env : Environment) (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ => true
  | .proj _ _ b => isAtomicSymTerm env b
  | e' =>
    if (e'.isAppOfArity ``Arm64.State.readReg64 2 || e'.isAppOfArity ``Arm64.State.readReg32 2) &&
       (e'.getArg! 0).consumeMData.isFVar && !(e'.getArg! 1).hasFVar then
      true
    else if let .const declName _ := e'.getAppFn then
      if let some info := env.getProjectionFnInfo? declName then
        if !info.fromClass && e'.getAppNumArgs == info.numParams + 1 then
          isAtomicSymTerm env (e'.getArg! info.numParams)
        else
          false
      else
        false
    else
      false

private def toSigned64 (u : Nat) : Int :=
  let m := 2 ^ 64
  let u' := u % m
  if u' >= 2 ^ 63 then (u' : Int) - (m : Int) else (u' : Int)

private partial def decomposeAddrSigned (e : Expr) : MetaM (Expr × Int) := do
  let (b, uOff) ← sepAddrBaseOff e
  return (b, toSigned64 uOff)

/-- Normalize an expression `e` using the current local context's pure equalities and
    `wp_norm` / `arm64_norm` rules without re-compiling all local hypotheses into `simp` via `*`. -/
private def normExprInGoal (g : MVarId) (e : Expr) : TacticM Expr := do
  g.withContext do
    tryCatchRuntimeEx (do
      let env ← getEnv
      let lctx ← getLCtx
      let mut eSub ← instantiateMVars e
      -- Substitute local equalities `lhs = rhs` where `lhs` is an atomic term or `List.length _`
      -- and `rhs` does not mention `State` or `lhs`.
      let mut stateFVars : Std.HashSet FVarId := {}
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          let ty ← instantiateMVars decl.type
          if ty.consumeMData.isConstOf ``Arm64.State then
            stateFVars := stateFVars.insert decl.fvarId
      let mentionsState (x : Expr) : Bool :=
        (x.find? fun sub =>
          match sub.fvarId? with
          | some fid => stateFVars.contains fid
          | none => false).isSome
      let mentionsSub (haystack needle : Expr) : Bool :=
        (haystack.find? fun sub => sub.consumeMData == needle).isSome
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          if let some val := decl.value? then
            let val ← instantiateMVars val
            if !mentionsState val && val.approxDepth < 32 then
              eSub := eSub.replace fun sub =>
                if sub.fvarId? == some decl.fvarId then some val else none
          else
            let ty ← instantiateMVars decl.type
            if let some (_, lhs0, rhs0) := ty.consumeMData.eq? then
              let lhs := lhs0.consumeMData
              let rhs := rhs0.consumeMData
              let isSubstTarget (x : Expr) : Bool :=
                let x := x.consumeMData
                isAtomicSymTerm env x || x.isAppOfArity ``List.length 2 ||
                x.isAppOfArity ``Arm64.State.readReg64 2 || x.isAppOfArity ``Arm64.State.readReg32 2 ||
                ((x.isAppOfArity ``BitVec.truncate 3 || x.isAppOfArity ``BitVec.setWidth 3) &&
                 (x.getArg! 2).consumeMData.isAppOfArity ``Arm64.State.readReg64 2)
              if isSubstTarget lhs && !mentionsState rhs && !mentionsSub rhs lhs && rhs.approxDepth < 32 then
                eSub := eSub.replace fun sub => if sub.consumeMData == lhs then some rhs else none
              else if isSubstTarget rhs && !mentionsState lhs && !mentionsSub lhs rhs &&
                      (!isAtomicSymTerm env lhs || mentionsState rhs) && lhs.approxDepth < 32 then
                eSub := eSub.replace fun sub => if sub.consumeMData == rhs then some lhs else none
      let eSubClean := eSub.consumeMData
      if eSubClean.isConst ||
         isAtomicSymTerm env eSubClean ||
         eSubClean.rawNatLit?.isSome ||
         eSubClean.nat?.isSome ||
         (evalBitVecLitPure? eSubClean).isSome ||
         (eSubClean.isAppOfArity ``Arm64.State.sp 1 && (eSubClean.getArg! 0).consumeMData.isFVar) then
        return eSub
      let ty ← inferType eSub
      if !mentionsState eSubClean && ty.consumeMData.isAppOfArity ``BitVec 1 then
        let (normE, _) ← SepSolver.normAddrMeta eSub
        if !normE.hasMVar then
          return normE
      let rhsMVar ← mkFreshExprMVar ty
      let eqTy ← mkEq eSub rhsMVar
      let eqGoal ← mkFreshExprMVar eqTy
      let saved ← getGoals
      setGoals [eqGoal.mvarId!]
      let useStar := mentionsState eSubClean
      let ok ← withCurrHeartbeats do
        tryTacticQuiet do
          if useStar then
            let _ ← tryTacticQuiet (evalTactic (← `(tactic| (
              conv =>
                lhs
                simp (config := { decide := true }) only [Prod.fst, Prod.snd, List.length_nil, wp_norm, arm64_norm, *]
            ))))
          else
            let _ ← tryTacticQuiet (evalTactic (← `(tactic| (
              conv =>
                lhs
                simp (config := { decide := true }) only [Prod.fst, Prod.snd, List.length_nil, wp_norm, arm64_norm]
            ))))
          if !(← getGoals).isEmpty then
            evalTactic (← `(tactic| rfl))
      setGoals saved
      if ok then
        return ← instantiateMVars rhsMVar
      else
        return ← instantiateMVars eSub
    ) (fun _ => instantiateMVars e)


/-- Information about a spatial block in a precondition or postcondition. -/
structure SpatialBlockInfo where
  atom : Expr
  base : Expr
  normBase : Expr
  anchor : Expr
  offset : Int
  lenExpr : Expr
  lenNat? : Option Nat
  isReadOnly : Bool := false
  deriving Inhabited

/-- Extract `SpatialBlockInfo` for a spatial atom `atom` in goal `g`.
    When `unwrapOptIte` is `true`, optional regions `if c then emp else blk` (such as
    `Allocator.optRegion`) are unwrapped to `blk`. -/
private partial def extractBlockInfo? (g : MVarId) (atom : Expr)
    (unwrapOptIte : Bool := false) : TacticM (Option SpatialBlockInfo) := do
  g.withContext do
    let atom := (← instantiateMVars atom).consumeMData
    if unwrapOptIte && atom.isAppOfArity ``ite 5 then
      let tBr := (atom.getArg! 3).consumeMData
      let eBr := (atom.getArg! 4).consumeMData
      if tBr.isConstOf ``Arm64.SepProp.emp then
        return ← extractBlockInfo? g eBr true
      else if eBr.isConstOf ``Arm64.SepProp.emp then
        return ← extractBlockInfo? g tBr true
    let mut baseOpt : Option Expr := none
    let mut lenOpt : Option Expr := none
    let mut isRO : Bool := false
    if let some blk ← SepSolver.blockOf? atom then
      baseOpt := some blk.base
      lenOpt := some blk.len
    else if atom.isAppOfArity ``Arm64.stackFrameAt 2 then
      -- `stackFrameAt sp n` owns `[sp - n, sp)` (`stackFrameAt_eq_memRegion`), whatever its
      -- internal slot expansion; `n = 0` gives a zero-length block, which never overlaps.
      let sp := atom.getArg! 0
      let n := atom.getArg! 1
      baseOpt := some (← mkAppM ``HSub.hSub #[sp, ← mkAppM ``BitVec.ofNat #[toExpr (64 : Nat), n]])
      lenOpt := some n
    else if atom.isAppOfArity ``Arm64.pointsToWords64 2 then
      let b := atom.getArg! 0
      let ws := atom.getArg! 1
      let lenE ← mkAppM ``HMul.hMul #[toExpr (8 : Nat), ← mkAppM ``List.length #[ws]]
      baseOpt := some b
      lenOpt := some lenE
    else if atom.isAppOfArity ``Arm64.pointsTo8RO 2 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (1 : Nat))
      isRO := true
    else if atom.isAppOfArity ``Arm64.pointsTo16RO 2 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (2 : Nat))
      isRO := true
    else if atom.isAppOfArity ``Arm64.pointsTo32RO 2 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (4 : Nat))
      isRO := true
    else if atom.isAppOfArity ``Arm64.pointsTo64RO 2 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (8 : Nat))
      isRO := true
    else if atom.isAppOfArity ``Arm64.pointsTo128RO 2 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (16 : Nat))
      isRO := true
    else if atom.isAppOfArity ``Arm64.pointsToBytesRO 2 then
      let b := atom.getArg! 0
      let bs := atom.getArg! 1
      let lenE ← mkAppM ``List.length #[bs]
      baseOpt := some b
      lenOpt := some lenE
      isRO := true
    else if atom.isAppOfArity ``Arm64.pointsToWords64RO 2 then
      let b := atom.getArg! 0
      let ws := atom.getArg! 1
      let lenE ← mkAppM ``HMul.hMul #[toExpr (8 : Nat), ← mkAppM ``List.length #[ws]]
      baseOpt := some b
      lenOpt := some lenE
      isRO := true
    else if atom.isAppOfArity ``Arm64.regionBlockRO 3 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (atom.getArg! 1)
      isRO := true
    else if atom.isAppOfArity ``Arm64.pointsTo8Lazy 1 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (1 : Nat))
    else if atom.isAppOfArity ``Arm64.pointsTo16Lazy 1 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (2 : Nat))
    else if atom.isAppOfArity ``Arm64.pointsTo32Lazy 1 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (4 : Nat))
    else if atom.isAppOfArity ``Arm64.pointsTo64Lazy 1 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (8 : Nat))
    else if atom.isAppOfArity ``Arm64.pointsTo128Lazy 1 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (16 : Nat))
    else if atom.isAppOfArity ``Arm64.memRegionLazy 2 || atom.isAppOfArity ``Arm64.memRegionProtNone 2 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (atom.getArg! 1)
    else if atom.isAppOfArity ``Arm64.regionBlockProtNone 3 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (atom.getArg! 1)
    else if atom.isAppOfArity ``Arm64.pointsTo8ProtNone 2 then
      baseOpt := some (atom.getArg! 0)
      lenOpt := some (toExpr (1 : Nat))
    else if atom.isAppOfArity ``Arm64.pointsToBytesProtNone 2 then
      let b := atom.getArg! 0
      let bs := atom.getArg! 1
      let lenE ← mkAppM ``List.length #[bs]
      baseOpt := some b
      lenOpt := some lenE
    let some base := baseOpt | return none
    let some lenExpr := lenOpt | return none
    let normBase ← normExprInGoal g base
    let normLen ← normExprInGoal g lenExpr
    let (anchor, offset) ← decomposeAddrSigned normBase
    let lenNat? ← evalNatLit? normLen
    return some {
      atom := atom
      base := base
      normBase := normBase
      anchor := anchor
      offset := offset
      lenExpr := normLen
      lenNat? := lenNat?
      isReadOnly := isRO
    }

private def formatAnchorOff (anchor : Expr) (off : Int) : MessageData :=
  if off == 0 then
    m!"{anchor}"
  else if off > 0 then
    m!"{anchor} + {off}"
  else
    m!"{anchor} - {-off}"

private def withGoalCtx (g : MVarId) (msg : MessageData) : MetaM MessageData :=
  g.withContext (addMessageContextFull msg)

private def formatPC (g : MVarId) (pcExpr : Expr) : MetaM MessageData := do
  g.withContext do
    let pcExpr ← instantiateMVars pcExpr
    if let some (64, v) ← evalBitVecLit? pcExpr then
      let hex := String.ofList (Nat.toDigits 16 v)
      return m!"0x{hex}#64"
    addMessageContextFull m!"{pcExpr}"

/-- Configuration for `#spec_nonvacuous` and `#spec_nonvacuous!`. -/
structure SpecNonVacuousConfig where
  /-- When `true`, try a fast concrete page-aligned witness (`0x1000`, `0x2000`, ...) before
      invoking `bv_decide`. Defaults to `false`; even when `true`, `bv_decide` is still run
      whenever no concrete witness is verified. -/
  smallBounds : Bool := false
  /-- Page step used when assigning small concrete addresses (`0x1000`, `0x2000`, ...). -/
  pageStep : Nat := 0x1000
  /-- Invoke full 64-bit `bv_decide` even when `smallBounds` is enabled. -/
  fullBvDecide : Bool := false
  /-- With `smallBounds`, also flag non-contradictory specs for which no concrete pure witness
      was found (used by regression tests to pin that the fast witness path is taken; without a
      witness the spatial check falls back to one tactic call per block pair, which is slow). -/
  requireWitness : Bool := false
  /-- Per-query heartbeat budget (in thousands, like `maxHeartbeats`) for each forced-overlap
      query between two spatial blocks. `0` (the default) gives every query the enclosing
      command's full `maxHeartbeats` budget. A query that exhausts its budget is inconclusive,
      and an inconclusive overlap query always makes the result `FLAGGED` (fail closed): raise
      `set_option maxHeartbeats N in` (or this field) until the audit completes. -/
  overlapHeartbeats : Nat := 0
  deriving Inhabited, Repr

declare_config_elab elabSpecNonVacuousConfig SpecNonVacuousConfig

private partial def collectSymbolicTerms (e : Expr) :
    MetaM (Array (Expr × Nat) × Array Expr × Array (Expr × Expr)) := do
  let env ← getEnv
  let bvRef ← IO.mkRef (#[] : Array (Expr × Nat))
  let natRef ← IO.mkRef (#[] : Array Expr)
  let listRef ← IO.mkRef (#[] : Array (Expr × Expr))
  let rec visit (t : Expr) : MetaM Unit := do
    let t := t.consumeMData
    if !t.hasFVar || t.hasLooseBVars then
      return
    if isAtomicSymTerm env t then
      let ty ← whnfR (← inferType t)
      if ty.isAppOfArity ``BitVec 1 then
        let wExpr ← whnf (ty.getArg! 0)
        let w? := wExpr.rawNatLit? <|>
          (if wExpr.isAppOfArity ``OfNat.ofNat 3 then (wExpr.getArg! 1).rawNatLit? else none)
        if let some w := w? then
          let cur ← bvRef.get
          unless cur.any (fun (existing, _) => existing == t) do
            bvRef.set (cur.push (t, w))
          return
      else if ty.isConstOf ``Nat then
        let cur ← natRef.get
        unless cur.any (fun existing => existing == t) do
          natRef.set (cur.push t)
        return
      else if ty.isAppOfArity ``List 1 then
        let elemTy := ty.getArg! 0
        let cur ← listRef.get
        unless cur.any (fun (existing, _) => existing == t) do
          listRef.set (cur.push (t, elemTy))
        return
    match t with
    | .app f a => visit f; visit a
    | .proj _ _ s => visit s
    | .letE _ ty v b _ => visit ty; visit v; visit b
    | .forallE _ d b _ => visit d; visit b
    | .lam _ d b _ => visit d; visit b
    | _ => Pure.pure ()
  visit e
  return (← bvRef.get, ← natRef.get, ← listRef.get)

private def mkListLitExpr (elemTy : Expr) (elems : List Expr) : MetaM Expr := do
  let u ← getDecLevel elemTy
  let nilE := mkApp (mkConst ``List.nil [u]) elemTy
  let consFn := mkApp (mkConst ``List.cons [u]) elemTy
  return elems.foldr (fun x acc => mkApp2 consFn x acc) nilE

private partial def evalGroundNat? (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  let e0 := e.consumeMData
  if e0.isAppOfArity ``List.length 2 then
    let xs := (e0.getArg! 1).consumeMData
    if xs.isAppOfArity ``List.replicate 3 then
      return ← evalGroundNat? (xs.getArg! 1)
  tryCatchRuntimeEx (do
    if let some n ← evalNatLit? e then return some n
    let eWhnf ← withCurrHeartbeats (withTransparency .all (whnf e))
    if let some n := eWhnf.rawNatLit?.orElse (fun _ => eWhnf.nat?) then return some n
    return none
  ) (fun _ => Pure.pure none)

private def evalGroundBv64? (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  tryCatchRuntimeEx (do
    if let some (64, v) ← evalBitVecLit? e then return some v
    let toNatE ← mkAppM ``BitVec.toNat #[e]
    evalGroundNat? toNatE
  ) (fun _ => Pure.pure none)

private partial def extractBasePtr (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 then
    extractBasePtr (e.getArg! 4)
  else
    e

private partial def stripBvNatCast (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.toNat 2 then
    stripBvNatCast (e.getArg! 1)
  else if e.isAppOfArity ``BitVec.zeroExtend 3 ||
          e.isAppOfArity ``BitVec.setWidth 3 ||
          e.isAppOfArity ``BitVec.truncate 3 then
    stripBvNatCast (e.getArg! 2)
  else
    e

private def extractIneqPair? (p : Expr) : Option (Expr × Expr) :=
  let p := p.consumeMData
  if p.isAppOfArity ``LE.le 4 || p.isAppOfArity ``LT.lt 4 then
    some ((p.getArg! 2).consumeMData, (p.getArg! 3).consumeMData)
  else if p.isAppOfArity ``GE.ge 4 || p.isAppOfArity ``GT.gt 4 then
    some ((p.getArg! 3).consumeMData, (p.getArg! 2).consumeMData)
  else if let some (_, cmp0, b0) := p.eq? then
    let cmp := cmp0.consumeMData
    let b := b0.consumeMData
    if cmp.isAppOfArity ``BitVec.ult 3 || cmp.isAppOfArity ``BitVec.ule 3 ||
       cmp.isAppOfArity ``BitVec.slt 3 || cmp.isAppOfArity ``BitVec.sle 3 then
      if b.isConstOf ``Bool.true then
        some ((cmp.getArg! 1).consumeMData, (cmp.getArg! 2).consumeMData)
      else if b.isConstOf ``Bool.false then
        some ((cmp.getArg! 2).consumeMData, (cmp.getArg! 1).consumeMData)
      else
        none
    else
      none
  else if p.isAppOfArity ``Not 1 then
    let inner := (p.getArg! 0).consumeMData
    if inner.isAppOfArity ``LE.le 4 || inner.isAppOfArity ``LT.lt 4 then
      some ((inner.getArg! 3).consumeMData, (inner.getArg! 2).consumeMData)
    else if inner.isAppOfArity ``GE.ge 4 || inner.isAppOfArity ``GT.gt 4 then
      some ((inner.getArg! 2).consumeMData, (inner.getArg! 3).consumeMData)
    else if let some (_, cmp0, b0) := inner.eq? then
      let cmp := cmp0.consumeMData
      let b := b0.consumeMData
      if b.isConstOf ``Bool.true &&
         (cmp.isAppOfArity ``BitVec.ult 3 || cmp.isAppOfArity ``BitVec.ule 3) then
        some ((cmp.getArg! 2).consumeMData, (cmp.getArg! 1).consumeMData)
      else
        none
    else
      none
  else
    none

private def isWideBitVecTy (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  ty.isAppOfArity ``BitVec 1 &&
    match (ty.getArg! 0).consumeMData.nat? <|> (ty.getArg! 0).consumeMData.rawNatLit? with
    | some w => w > 8
    | none => true

/-- `true` iff `e` contains a `∀` / `∃` binder over a wide `BitVec w` domain. Core's
    `BitVec.instDecidableForallBitVec` (and the `∃` analogue) make such propositions `Decidable` by
    enumerating all `2 ^ w` values, so `decide` (or `simp (config := { decide := true })`) on a
    ground instance (e.g. `∀ p : BitVec 64, M p = some ind → ...` once the witness search has
    substituted concrete lists) never finishes. -/
private def hasWideBitVecBinder (e : Expr) : Bool :=
  (e.find? fun s =>
    match s with
    | .forallE _ d _ _ => isWideBitVecTy d
    | _ => (s.isAppOfArity ``Exists 2 || s.isAppOfArity ``Subtype 2) && isWideBitVecTy (s.getArg! 0)
  ).isSome

/-- `true` iff the proposition `e` contains a genuine quantifier (a `∀` over a non-`Prop` domain
    or an `∃`). `#spec_nonvacuous` cannot refute or witness such facts with its decision procedures
    (`omega` / `bv_decide` treat them as opaque atoms), so they are reported separately. -/
private partial def hasQuantifierProp (e : Expr) : MetaM Bool := do
  match e.consumeMData with
  | .forallE _ d b _ =>
    if d.hasLooseBVars then return true
    if !(← isProp d) then return true
    if ← hasQuantifierProp d then return true
    hasQuantifierProp b
  | .app f a =>
    let e' := e.consumeMData
    if e'.isAppOfArity ``Exists 2 then return true
    if ← hasQuantifierProp f then return true
    hasQuantifierProp a
  | .lam _ _ b _ => hasQuantifierProp b
  | .letE _ _ v b _ =>
    if ← hasQuantifierProp v then return true
    hasQuantifierProp b
  | _ => return false

/-- Run `x` with a fresh budget of `hbRaw` raw heartbeats (the unit of
    `Core.Context.maxHeartbeats`, i.e. `1000 *` the `maxHeartbeats` option; `0` = unlimited).
    Returns `none` if `x` throws (in particular when the heartbeat budget or the recursion limit is
    exhausted), so callers can distinguish "inconclusive" from a definite answer.

    Note: `set_option maxHeartbeats N in <tac>` inside an `evalTactic` call does not bound
    `<tac>`: `withOptions` refreshes `Core.Context.maxRecDepth` but not `Core.Context.maxHeartbeats`,
    so such a tactic runs under the enclosing command's budget (and the heartbeats it burns are
    charged to the enclosing command even when the error is caught). -/
private def withRealHeartbeatBudgetRaw? {α : Type} (hbRaw : Nat) (x : TacticM α) :
    TacticM (Option α) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <|
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hbRaw }) (some <$> x))
    (fun _ => Pure.pure none)

/-- `withRealHeartbeatBudgetRaw?` with a budget `hb` in thousands (like `maxHeartbeats`),
    returning `fallback` if the budget (or the recursion limit) is exhausted. Only use this where
    `fallback` is the conservative answer (e.g. "no witness found"). -/
private def withRealHeartbeatBudget {α : Type} (hb : Nat) (fallback : α) (x : TacticM α) :
    TacticM α := do
  return (← withRealHeartbeatBudgetRaw? (hb * 1000) x).getD fallback

/-- Try to constructively satisfy all pure `Prop` hypotheses in `gPure` by eliminating
    trivial `State` (`s0`) register/alignment bindings, assigning page-aligned addresses
    (`0x1000#64`, `0x2000#64`, ...) to spatial base pointers, propagating definitional equalities,
    assigning small inequality-ordered values to scalar `BitVec`/`Nat` parameters, and
    instantiating `List` variables with concrete list literals.
    Returns `some substFn` ONLY if `Meta.check` and elaborator `decide`/`simp` verify that the
    resulting ground witness satisfies the conjunction of all pure hypotheses. -/
private partial def tryBoundedPureWitness? (gPure : MVarId) (spatialBasePtrs : Array Expr := #[])
    (pageStep : Nat := 0x1000) (spatialExpr? : Option Expr := none) : TacticM (Option (Expr → Expr)) := do
  withoutModifyingState do
    gPure.withContext do
      let lctx ← getLCtx
      let mut stateFVars : Std.HashSet FVarId := {}
      let mut letBindings : Array (FVarId × Expr) := #[]
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          let ty ← instantiateMVars decl.type
          if ty.consumeMData.isConstOf ``Arm64.State then
            stateFVars := stateFVars.insert decl.fvarId
          if let some val := decl.value? then
            letBindings := letBindings.push (decl.fvarId, ← instantiateMVars val)
      let mentionsState (e : Expr) : Bool :=
        (e.find? fun sub =>
          match sub.fvarId? with
          | some fid => stateFVars.contains fid
          | none => false).isSome
      let mut regBindings : Array (Expr × Expr) := #[]
      let mut rawProps : Array Expr := #[]
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.hasValue then
          let ty ← instantiateMVars decl.type
          if ← isProp ty then
            rawProps := rawProps.push ty
      let mut propTypes : Array Expr := #[]
      for ty0 in rawProps do
        let ty := ty0.consumeMData
        let isSpAligned :=
          match ty.eq? with
          | some (_, lhs, rhs) =>
            let l := lhs.consumeMData
            let r := rhs.consumeMData
            l.isAppOfArity ``Arm64.State.spAligned 1 && r.isConstOf ``Bool.true
          | none => false
        if isSpAligned then
          continue
        let mut boundAsNewReg := false
        if let some (_, lhs0, rhs0) := ty.eq? then
          let lhs := lhs0.consumeMData
          let rhs := rhs0.consumeMData
          let extractRegReadKey? (e : Expr) : Option Expr :=
            let e := e.consumeMData
            if e.isAppOfArity ``Arm64.State.readReg64 2 &&
               mentionsState (e.getArg! 0) && !mentionsState (e.getArg! 1) then
              some e
            else if e.isAppOfArity ``Arm64.State.readReg32 2 &&
                    mentionsState (e.getArg! 0) && !mentionsState (e.getArg! 1) then
              some (mkApp2 (mkConst ``Arm64.State.readReg64) (e.getArg! 0) (e.getArg! 1))
            else if (e.isAppOfArity ``BitVec.truncate 3 || e.isAppOfArity ``BitVec.setWidth 3) then
              let inner := stripBvNatCast e
              if (inner.isAppOfArity ``Arm64.State.readReg64 2 ||
                  inner.isAppOfArity ``Arm64.State.readReg32 2) &&
                 mentionsState (inner.getArg! 0) && !mentionsState (inner.getArg! 1) then
                some (mkApp2 (mkConst ``Arm64.State.readReg64) (inner.getArg! 0) (inner.getArg! 1))
              else
                none
            else
              none
          if let some key := extractRegReadKey? lhs then
            if !mentionsState rhs && !regBindings.any (fun (k, _) => k == lhs || k == key) then
              regBindings := regBindings.push (lhs, rhs)
              if key != lhs then
                let widened ← mkAppM ``BitVec.setWidth #[toExpr (64 : Nat), rhs]
                regBindings := regBindings.push (key, widened)
              boundAsNewReg := true
          else if let some key := extractRegReadKey? rhs then
            if !mentionsState lhs && !regBindings.any (fun (k, _) => k == rhs || k == key) then
              regBindings := regBindings.push (rhs, lhs)
              if key != rhs then
                let widened ← mkAppM ``BitVec.setWidth #[toExpr (64 : Nat), lhs]
                regBindings := regBindings.push (key, widened)
              boundAsNewReg := true
        unless boundAsNewReg do
          propTypes := propTypes.push ty
      let env ← getEnv
      let hasStructProj :=
        propTypes.any fun p =>
          (p.find? fun s =>
            s.isProj ||
            match s.getAppFn.constName? with
            | some c =>
              match env.getProjectionFnInfo? c with
              | some info => !info.fromClass
              | none => false
            | none => false).isSome
      let spConst :=
        if hasStructProj || spatialBasePtrs.size > 4 || rawProps.size > 20 then toExpr (0x800000#64)
        else toExpr (0x80000#64)
      let baseSubst (e0 : Expr) : Expr := Id.run do
        let mut e := e0
        for (fid, val) in letBindings do
          if !mentionsState val then
            e := e.replace fun sub => if sub.fvarId? == some fid then some val else none
        e := e.replace fun sub =>
          let sub0 := sub.consumeMData
          if let some (_, rhs) := regBindings.find? (fun (k, _) => k == sub0) then
            some rhs
          else if sub0.isAppOfArity ``Arm64.State.readReg32 2 &&
                  mentionsState (sub0.getArg! 0) && !mentionsState (sub0.getArg! 1) then
            let r64 := mkApp2 (mkConst ``Arm64.State.readReg64) (sub0.getArg! 0) (sub0.getArg! 1)
            let base64 := match regBindings.find? (fun (k, _) => k == r64) with
              | some (_, rhs) => rhs
              | none => r64
            some (mkApp3 (mkConst ``BitVec.setWidth) (toExpr (64 : Nat)) (toExpr (32 : Nat)) base64)
          else if sub0.isAppOfArity ``Arm64.State.sp 1 && mentionsState (sub0.getArg! 0) then
            some spConst
          else if sub0.isAppOfArity ``Arm64.State.spAligned 1 && mentionsState (sub0.getArg! 0) then
            some (mkConst ``Bool.true)
          else
            none
        return e
      let spatialBasePtrs := spatialBasePtrs.map baseSubst
      -- After `rcases` unpacks the ghost tuple `a`, `Decidable` instance arguments of
      -- `ite`/`dite` may still mention the original tuple (`instDecidableEqBitVec _ (a.1) ...`),
      -- making `mid = if idx = 6 then 5 else 6` look self-referential to the dependent-equation
      -- scan. Re-synthesize those instances from the (already unpacked) condition.
      let canonIteInsts (e : Expr) : MetaM Expr :=
        Meta.transform e (post := fun sub => do
          if (sub.isAppOfArity ``ite 5 || sub.isAppOfArity ``dite 5) then
            let c := sub.getArg! 1
            if let some inst ← (try synthInstance? (mkApp (mkConst ``Decidable) c) catch _ => Pure.pure none) then
              let args := sub.getAppArgs
              return .done (mkAppN sub.getAppFn (args.set! 2 inst))
          return .continue)
      let props0 ←
        if propTypes.isEmpty then Pure.pure #[mkConst ``True]
        else (propTypes.map baseSubst).mapM fun p => do
          try canonIteInsts p catch _ => Pure.pure p
      let mut conj0 := props0[0]!
      for i in [1:props0.size] do
        conj0 := mkApp2 (mkConst ``And) conj0 props0[i]!
      let stripRegReads (x : Expr) : Expr :=
        x.replace fun sub =>
          let sub0 := sub.consumeMData
          if sub0.isAppOfArity ``Arm64.State.readReg64 2 && !mentionsState (sub0.getArg! 1) then
            some (toExpr 0#64)
          else
            none
      if mentionsState (stripRegReads conj0) then
        return none
      let collectRoot :=
        match spatialExpr? with
        | some s => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkSort 0) (mkConst ``Arm64.SepProp) conj0 (baseSubst s)
        | none => conj0
      let (bvTerms, natTerms, listTerms) ← collectSymbolicTerms collectRoot
      let ptrStep := if hasStructProj || bvTerms.size > 16 then max pageStep 0x10000 else pageStep
      let mentionsSub (haystack needle : Expr) : Bool :=
        (haystack.find? fun sub => sub.consumeMData == needle).isSome
      let isKnownScalar (x : Expr) : Bool :=
        bvTerms.any (fun (t, _) => t == x) || natTerms.contains x
      let fixedRef ← IO.mkRef (#[] : Array (Expr × Nat))
      let minBvRef ← IO.mkRef (#[] : Array (Expr × Nat))
      let mustSetRef ← IO.mkRef (#[] : Array (Expr × Nat))
      let mustClearRef ← IO.mkRef (#[] : Array (Expr × Nat))
      let avoidRef ← IO.mkRef (#[] : Array (Expr × Nat))
      let fixedNatRef ← IO.mkRef (#[] : Array (Expr × Nat))
      let extraIneqRef ← IO.mkRef (#[] : Array Expr)
      let depRef ← IO.mkRef (#[] : Array (Expr × Expr))
      let isZeroLit (x : Expr) : Bool :=
        match evalBitVecLitPure? x with
        | some (_, 0) => true
        | _ => x.rawNatLit? == some 0
      let orMask (ref : IO.Ref (Array (Expr × Nat))) (k : Expr) (m : Nat) : MetaM Unit := do
        let cur ← ref.get
        if let some idx := cur.findIdx? (fun (x, _) => x == k) then
          let (_, old) := cur[idx]!
          ref.set (cur.set! idx (k, old ||| m))
        else
          ref.set (cur.push (k, m))
      let maxBound (ref : IO.Ref (Array (Expr × Nat))) (k : Expr) (v : Nat) : MetaM Unit := do
        let cur ← ref.get
        if let some idx := cur.findIdx? (fun (x, _) => x == k) then
          let (_, old) := cur[idx]!
          ref.set (cur.set! idx (k, max old v))
        else
          ref.set (cur.push (k, v))
      let rec findMaskTargetScalar? (e : Expr) : Option Expr :=
        let s := stripBvNatCast e
        if isKnownScalar s && !spatialBasePtrs.contains s then some s
        else if s.isAppOfArity ``HAnd.hAnd 6 || s.isAppOfArity ``HOr.hOr 6 then
          findMaskTargetScalar? (s.getArg! 4) <|> findMaskTargetScalar? (s.getArg! 5)
        else none
      let rec collectMaskLits (e : Expr) : MetaM Nat := do
        let e := e.consumeMData
        if let some (_, v) ← evalBitVecLit? e then return v
        if e.isAppOfArity ``HOr.hOr 6 || e.isAppOfArity ``HAnd.hAnd 6 then
          return (← collectMaskLits (e.getArg! 4)) ||| (← collectMaskLits (e.getArg! 5))
        return 0
      let addDepEq (lhs rhs : Expr) : MetaM Unit := do
        let cur ← depRef.get
        if isKnownScalar lhs && !isZeroLit rhs && !mentionsSub rhs lhs &&
           !cur.any (fun (k, _) => k == lhs) &&
           !cur.any (fun (_, v) => mentionsSub v lhs) then
          depRef.set (cur.push (lhs, rhs))
      let recordNeq (lhs0 rhs0 : Expr) : MetaM Unit := do
        let lhs := lhs0.consumeMData
        let rhs := rhs0.consumeMData
        if (lhs.isAppOfArity ``HAnd.hAnd 6 && isZeroLit rhs) || (rhs.isAppOfArity ``HAnd.hAnd 6 && isZeroLit lhs) then
          let andExpr := if lhs.isAppOfArity ``HAnd.hAnd 6 then lhs else rhs
          if let some x := findMaskTargetScalar? (andExpr.getArg! 4) then
            let m ← collectMaskLits (andExpr.getArg! 5)
            if m != 0 then orMask mustSetRef x m
        else if isKnownScalar (stripBvNatCast lhs) then
          if let some (_, v) ← evalBitVecLit? rhs then
            avoidRef.modify (·.push (stripBvNatCast lhs, v))
        else if isKnownScalar (stripBvNatCast rhs) then
          if let some (_, v) ← evalBitVecLit? lhs then
            avoidRef.modify (·.push (stripBvNatCast rhs, v))
      let rec scanBoolConj (b0 : Expr) : MetaM Unit := do
        let b := b0.consumeMData
        if b.isAppOfArity ``Bool.and 2 || b.isAppOfArity ``Bool.or 2 then
          scanBoolConj (b.getArg! 0)
          scanBoolConj (b.getArg! 1)
        else
          let eqTrue ← mkEq b (mkConst ``Bool.true)
          extraIneqRef.modify (·.push eqTrue)
          if b.isAppOfArity ``_root_.bne 4 then
            recordNeq (b.getArg! 2) (b.getArg! 3)
      let rec scanConjunctsForEqs (p : Expr) : MetaM Unit := do
        let p := p.consumeMData
        if p.isAppOfArity ``And 2 then
          scanConjunctsForEqs (p.getArg! 0)
          scanConjunctsForEqs (p.getArg! 1)
        else if let some (_, l0, r0) := p.ne? then
          recordNeq l0 r0
        else if p.isAppOfArity ``Not 1 then
          let inner := (p.getArg! 0).consumeMData
          if let some (_, l0, r0) := inner.eq? then
            recordNeq l0 r0
        else if let some (_, lhs0, rhs0) := p.eq? then
          let lhs := lhs0.consumeMData
          let rhs := rhs0.consumeMData
          if lhs.isAppOfArity ``_root_.bne 4 && rhs.isConstOf ``Bool.true then
            recordNeq (lhs.getArg! 2) (lhs.getArg! 3)
          else if lhs.isAppOfArity ``BEq.beq 4 && rhs.isConstOf ``Bool.false then
            recordNeq (lhs.getArg! 2) (lhs.getArg! 3)
          else if (lhs.isAppOfArity ``BitVec.setWidth 3 || lhs.isAppOfArity ``BitVec.truncate 3) &&
             isKnownScalar (lhs.getArg! 2).consumeMData then
            if let some (_, v) ← evalBitVecLit? rhs then
              fixedRef.modify (·.push ((lhs.getArg! 2).consumeMData, v))
          else if (rhs.isAppOfArity ``BitVec.setWidth 3 || rhs.isAppOfArity ``BitVec.truncate 3) &&
                  isKnownScalar (rhs.getArg! 2).consumeMData then
            if let some (_, v) ← evalBitVecLit? lhs then
              fixedRef.modify (·.push ((rhs.getArg! 2).consumeMData, v))
          else if lhs.isAppOfArity ``HAnd.hAnd 6 && (findMaskTargetScalar? (lhs.getArg! 4)).isSome then
            let x := (findMaskTargetScalar? (lhs.getArg! 4)).get!
            if let some (_, v) ← evalBitVecLit? rhs then
              if v == 0 then
                let m ← collectMaskLits (lhs.getArg! 5)
                if m != 0 then orMask mustClearRef x m
              else
                orMask mustSetRef x v
          else if lhs.isAppOfArity ``BitVec.getLsbD 3 && isKnownScalar (lhs.getArg! 1).consumeMData then
            if let some b ← evalNatLit? (lhs.getArg! 2) then
              if rhs.isConstOf ``Bool.true then
                orMask mustSetRef (lhs.getArg! 1).consumeMData (1 <<< b)
              else if rhs.isConstOf ``Bool.false then
                orMask mustClearRef (lhs.getArg! 1).consumeMData (1 <<< b)
          else if lhs.isAppOfArity ``BitVec.ofNat 2 && natTerms.contains (lhs.getArg! 1).consumeMData then
            if let some (_, v) ← evalBitVecLit? rhs then
              fixedNatRef.modify (·.push ((lhs.getArg! 1).consumeMData, v))
          else if rhs.isAppOfArity ``BitVec.ofNat 2 && natTerms.contains (rhs.getArg! 1).consumeMData then
            if let some (_, v) ← evalBitVecLit? lhs then
              fixedNatRef.modify (·.push ((rhs.getArg! 1).consumeMData, v))
          else if isKnownScalar lhs && (!isZeroLit rhs || (!lhs.isFVar && !spatialBasePtrs.contains lhs)) then
            if isZeroLit rhs then
              if natTerms.contains lhs then fixedNatRef.modify (·.push (lhs, 0))
              else fixedRef.modify (·.push (lhs, 0))
            else if let some (_, v) ← evalBitVecLit? rhs then
              if natTerms.contains lhs then fixedNatRef.modify (·.push (lhs, v))
              else fixedRef.modify (·.push (lhs, v))
            else if !spatialBasePtrs.contains lhs then
              addDepEq lhs rhs
            else if isKnownScalar rhs && !spatialBasePtrs.contains rhs && !isZeroLit lhs then
              addDepEq rhs lhs
          else if isKnownScalar rhs && (!isZeroLit lhs || (!rhs.isFVar && !spatialBasePtrs.contains rhs)) then
            if isZeroLit lhs then
              if natTerms.contains rhs then fixedNatRef.modify (·.push (rhs, 0))
              else fixedRef.modify (·.push (rhs, 0))
            else if let some (_, v) ← evalBitVecLit? lhs then
              if natTerms.contains rhs then fixedNatRef.modify (·.push (rhs, v))
              else fixedRef.modify (·.push (rhs, v))
            else if !spatialBasePtrs.contains rhs then
              addDepEq rhs lhs
          else if rhs.isConstOf ``Bool.true &&
                  !lhs.isAppOf ``BitVec.ult && !lhs.isAppOf ``BitVec.ule &&
                  !lhs.isAppOf ``BitVec.slt && !lhs.isAppOf ``BitVec.sle &&
                  !lhs.isAppOf ``BEq.beq && !lhs.isAppOf ``_root_.bne &&
                  !lhs.isAppOf ``BitVec.getLsbD then
            if let some lhsU ← unfoldDefinition? lhs then
              scanBoolConj lhsU
          else if !isKnownScalar lhs && !lhs.isAppOf ``OfNat.ofNat then
            if let some (_, v) := evalBitVecLitPure? rhs then
              if let some lhsU ← unfoldDefinition? lhs then
                let lhsW := lhsU.consumeMData
                if lhsW.isAppOfArity ``ite 5 then
                  if let some (_, tv) := evalBitVecLitPure? (lhsW.getArg! 3) then
                    if tv == v then
                      if let some (_, bLhs, bRhs) := (lhsW.getArg! 1).consumeMData.eq? then
                        if bRhs.consumeMData.isConstOf ``Bool.true then
                          scanBoolConj bLhs
              -- A literal RHS only implies per-variable lower bounds for non-arithmetic heads
              -- (projections, casts, user helpers); `x + y = v` / `x ^^^ y = v` imply none.
              let arithHead := lhs.isAppOf ``HAdd.hAdd || lhs.isAppOf ``HSub.hSub ||
                lhs.isAppOf ``HMul.hMul || lhs.isAppOf ``HXor.hXor || lhs.isAppOf ``HOr.hOr
              unless arithHead do
                lhs.forEach fun arg => do
                  let s := stripBvNatCast arg
                  if isKnownScalar s && !spatialBasePtrs.contains s && !natTerms.contains s then
                    maxBound minBvRef s v
      for p in props0 do
        let pClean := p.consumeMData
        if pClean.isAppOfArity ``Or 2 then
          scanConjunctsForEqs (pClean.getArg! 0)
        else
          scanConjunctsForEqs pClean
      let fixedBvVal ← fixedRef.get
      let mustSetVal ← mustSetRef.get
      let mustClearVal ← mustClearRef.get
      let avoidBvVal ← avoidRef.get
      let fixedNatVal ← fixedNatRef.get
      let extraIneqProps ← extraIneqRef.get
      let depEquations ← depRef.get
      let mut bvRanks : Array Nat := Array.replicate bvTerms.size 0
      let mut ineqEdges : Array (Nat × Nat) := #[]
      let mut cap64Vars : Array Expr := #[]
      let mut natCapVars : Array Expr := #[]
      let rec collectComplementAddPairs (e : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
        let e := e.consumeMData
        let acc :=
          if e.isAppOfArity ``HAdd.hAdd 6 then
            let a := (e.getArg! 4).consumeMData
            let b := (e.getArg! 5).consumeMData
            if a.isAppOfArity ``Complement.complement 3 then
              acc.push (stripBvNatCast (a.getArg! 2), stripBvNatCast b)
            else if b.isAppOfArity ``Complement.complement 3 then
              acc.push (stripBvNatCast (b.getArg! 2), stripBvNatCast a)
            else
              acc
          else
            acc
        match e with
        | .app f x => collectComplementAddPairs x (collectComplementAddPairs f acc)
        | _ => acc
      for p in props0 ++ extraIneqProps do
        let pClean := p.consumeMData
        if !pClean.isAppOfArity ``Or 2 then
          for (u, v) in collectComplementAddPairs pClean #[] do
            if let some iu := bvTerms.findIdx? (fun (t, _) => t == u) then
              if let some iv := bvTerms.findIdx? (fun (t, _) => t == v) then
                if iu != iv && !ineqEdges.contains (iu, iv) then
                  ineqEdges := ineqEdges.push (iu, iv)
          if let some (lhs, rhs) := extractIneqPair? pClean then
            let isStrictIneq := pClean.isAppOfArity ``LT.lt 4 || pClean.isAppOfArity ``GT.gt 4
            let lhsHasAddMul :=
              (lhs.find? fun s =>
                let s := s.consumeMData
                s.isAppOf ``HAdd.hAdd || s.isAppOf ``HMul.hMul).isSome
            let lhsHasBv := bvTerms.any (fun (bt, _) => mentionsSub lhs bt)
            let lhsHasNat := natTerms.any (fun nt => mentionsSub lhs nt)
            for nt in natTerms do
              if mentionsSub rhs nt && !mentionsSub lhs nt && !natCapVars.contains nt &&
                 !fixedNatVal.any (fun (k, _) => k == nt) &&
                 (lhsHasBv || lhsHasAddMul || (isStrictIneq && lhsHasNat)) then
                natCapVars := natCapVars.push nt
            let u := stripBvNatCast lhs
            let v := stripBvNatCast rhs
            let iv? := bvTerms.findIdx? (fun (t, _) => t == v) <|>
              (if v.isAppOfArity ``HSub.hSub 6 then
                 let vPos := stripBvNatCast (v.getArg! 4)
                 bvTerms.findIdx? (fun (t, _) => t == vPos)
               else none)
            if let some iv := iv? then
              let (tv, _) := bvTerms[iv]!
              if v.isAppOfArity ``HSub.hSub 6 then
                bvRanks := bvRanks.set! iv (max bvRanks[iv]! 2)
                let vNeg := (v.getArg! 5).consumeMData
                for ib in [:bvTerms.size] do
                  let (tb, _) := bvTerms[ib]!
                  if ib != iv && mentionsSub vNeg tb then
                    ineqEdges := ineqEdges.push (ib, iv)
              if depEquations.any (fun (k, _) => mentionsSub u k) then
                cap64Vars := cap64Vars.push tv
              if let some iu := bvTerms.findIdx? (fun (t, _) => t == u) then
                if iu != iv then
                  ineqEdges := ineqEdges.push (iu, iv)
              else if let some litVal := (evalBitVecLitPure? u).map Prod.snd <|> evalNatLitPure? u then
                -- `k ≤ x` / `k ≤ x.toNat` with a `BitVec` or `Nat` literal `k`: lower-bound `x`.
                if litVal > 2 && !spatialBasePtrs.contains tv then
                  maxBound minBvRef tv (if isStrictIneq then litVal + 1 else litVal)
              else
                for iu in [:bvTerms.size] do
                  let (tu, _) := bvTerms[iu]!
                  if iu != iv && mentionsSub lhs tu && !mentionsSub lhs tv then
                    ineqEdges := ineqEdges.push (iu, iv)
                let hasLargeAddLit :=
                  (lhs.find? fun s =>
                    match evalBitVecLitPure? s with
                    | some (_, n) => n > 2
                    | none => false).isSome
                if hasLargeAddLit then
                  bvRanks := bvRanks.set! iv (max bvRanks[iv]! 3)
      let minBvVal ← minBvRef.get
      for _ in [:4] do
        for (iu, iv) in ineqEdges do
          let rNew := max bvRanks[iv]! (bvRanks[iu]! + 1)
          bvRanks := bvRanks.set! iv rNew
      let applyMap (m : Array (Expr × Expr)) (e : Expr) : Expr :=
        if m.isEmpty then e
        else e.replace fun sub =>
          let sub0 := sub.consumeMData
          match m.find? (fun (k, _) => k == sub0) with
          | some (_, v) => some v
          | none => none
      let rec findListLenEq? (xs : Expr) (p : Expr) : Option Expr :=
        let p := p.consumeMData
        if p.isAppOfArity ``And 2 then
          findListLenEq? xs (p.getArg! 0) <|> findListLenEq? xs (p.getArg! 1)
        else if p.isAppOfArity ``Or 2 then
          findListLenEq? xs (p.getArg! 0)
        else if let some (_, lhs0, rhs0) := p.eq? then
          let lhs := lhs0.consumeMData
          let rhs := rhs0.consumeMData
          if lhs.isAppOfArity ``List.length 2 && (lhs.getArg! 1).consumeMData == xs then
            some rhs
          else if rhs.isAppOfArity ``List.length 2 && (rhs.getArg! 1).consumeMData == xs then
            some lhs
          else
            none
        else
          none
      let needsNonEmptyList (xs : Expr) (c : Expr) : Bool :=
        (c.find? fun sub =>
          let sub := sub.consumeMData
          if let some (lhs, rhs) := extractIneqPair? sub then
            rhs.isAppOfArity ``List.length 2 && (rhs.getArg! 1).consumeMData == xs &&
            !mentionsSub lhs xs
          else if let some (_, l0, r0) := sub.ne? <|> (if sub.isAppOfArity ``Not 1 then (sub.getArg! 0).consumeMData.eq? else none) then
            let l := l0.consumeMData
            let r := r0.consumeMData
            (l == xs && r.isAppOf ``List.nil) ||
            (r == xs && l.isAppOf ``List.nil) ||
            (l.isAppOfArity ``List.length 2 && (l.getArg! 1).consumeMData == xs) ||
            (r.isAppOfArity ``List.length 2 && (r.getArg! 1).consumeMData == xs) ||
            (l.isAppOf ``BitVec.ofNat && mentionsSub l xs && isZeroLit r) ||
            (r.isAppOf ``BitVec.ofNat && mentionsSub r xs && isZeroLit l)
          else
            false).isSome
      let tryCandidate (useRelRank : Bool) (baseRankShift : Nat) :
          TacticM (Option (Expr → Expr)) := do
        let mut indepMap : Array (Expr × Expr) := #[]
        for idx in [:bvTerms.size] do
          let (term, w) := bvTerms[idx]!
          if !useRelRank || !depEquations.any (fun (k, _) => k == term) then
            let rawVal0 : Nat :=
              if let some (_, fv) := fixedBvVal.find? (fun (k, _) => k == term) then
                fv
              else if w == 64 && spatialBasePtrs.contains term then
                if !useRelRank then (idx + 1) * ptrStep
                else (bvRanks[idx]! * bvTerms.size + idx + 1) * ptrStep
              else if !useRelRank then
                if w == 64 then (idx + 1) * pageStep else idx + 1
              else if w == 64 && cap64Vars.contains term then
                pageStep
              else
                let r := bvRanks[idx]! + baseRankShift
                match r with
                | 0 => 1
                | 1 => 2
                | 2 => 4
                | 3 => 32
                | _ => 64
            let rawVal : Nat :=
              if fixedBvVal.any (fun (k, _) => k == term) then rawVal0
              else match minBvVal.find? (fun (k, _) => k == term) with
                | some (_, lb) => max rawVal0 lb
                | none => rawVal0
            let setM := (mustSetVal.find? (fun (k, _) => k == term)).map Prod.snd |>.getD 0
            let clrM := (mustClearVal.find? (fun (k, _) => k == term)).map Prod.snd |>.getD 0
            let maskedVal :=
              if setM != 0 || clrM != 0 then
                (rawVal ||| setM) - ((rawVal ||| setM) &&& clrM)
              else
                rawVal
            let val :=
              if avoidBvVal.any (fun (k, av) => k == term && av == maskedVal) then
                maskedVal + 1
              else
                maskedVal
            indepMap := indepMap.push (term, toExpr (BitVec.ofNat w val))
        let natVal : Nat := if !useRelRank || baseRankShift == 0 then 1 else 2
        for term in natTerms do
          if !useRelRank || !depEquations.any (fun (k, _) => k == term) then
            let nv :=
              if let some (_, fnv) := fixedNatVal.find? (fun (k, _) => k == term) then
                fnv
              else if useRelRank && natCapVars.contains term then
                8 * pageStep
              else
                natVal
            indepMap := indepMap.push (term, toExpr nv)
        let mut depMap : Array (Expr × Expr) := #[]
        if useRelRank then
          for (lhs, rhs) in depEquations do
            let rhsSub := applyMap depMap (applyMap indepMap rhs)
            depMap := depMap.push (lhs, rhsSub)
        let scalarSubst (e : Expr) : Expr := applyMap depMap (applyMap indepMap e)
        let propsScalar := props0.map scalarSubst
        let conjScalar := scalarSubst conj0
        let mut listMap : Array (Expr × Expr) := #[]
        let mut hasLargeReplicate := false
        let rec mkDefaultElemFor (elemTy : Expr) : MetaM (Option Expr) := do
          let elemTyClean := elemTy.consumeMData
          if elemTyClean.isAppOfArity ``BitVec 1 then
            let wExpr ← whnf (elemTyClean.getArg! 0)
            let ew := (wExpr.rawNatLit? <|>
              (if wExpr.isAppOfArity ``OfNat.ofNat 3 then (wExpr.getArg! 1).rawNatLit? else none)).getD 8
            Pure.pure (some (toExpr (BitVec.ofNat ew 1)))
          else if elemTyClean.isConstOf ``Nat then
            Pure.pure (some (toExpr (1 : Nat)))
          else if elemTyClean.isConstOf ``UInt8 then
            Pure.pure (some (mkApp (mkConst ``UInt8.ofNat) (mkNatLit 0)))
          else if elemTyClean.isAppOfArity ``Prod 2 then
            let tyA := elemTyClean.appFn!.appArg!
            let tyB := elemTyClean.appArg!
            match ← mkDefaultElemFor tyA, ← mkDefaultElemFor tyB with
            | some a, some b =>
              let uA ← getDecLevel tyA
              let uB ← getDecLevel tyB
              Pure.pure (some (mkApp4 (mkConst ``Prod.mk [uA, uB]) tyA tyB a b))
            | _, _ => Pure.pure none
          else
            Pure.pure none
        let mkListWitnessFor (elemTy : Expr) (k : Nat) : MetaM Expr := do
          let elemLit := (← mkDefaultElemFor elemTy).getD (toExpr (1#8))
          if k ≤ 16 then
            mkListLitExpr elemTy (List.replicate k elemLit)
          else do
            let u ← getDecLevel elemTy
            Pure.pure (mkApp3 (mkConst ``List.replicate [u]) elemTy (toExpr k) elemLit)
        let mut deferredLists : Array (Expr × Expr) := #[]
        for (xs, elemTy) in listTerms do
          let mut hasEq := false
          let mut lenOpt : Option Nat := none
          for p in propsScalar do
            if lenOpt.isNone then
              let pSub := applyMap listMap p
              if let some rhs := findListLenEq? xs pSub then
                hasEq := true
                if let some k ← evalGroundNat? rhs then
                  if k ≤ 65536 then
                    lenOpt := some k
          if hasEq && lenOpt.isNone && !needsNonEmptyList xs conjScalar then
            deferredLists := deferredLists.push (xs, elemTy)
          else
            let k := match lenOpt with
              | some n => n
              | none => if needsNonEmptyList xs conjScalar then 1 else 0
            if k > 256 then
              hasLargeReplicate := true
            let listLit ← mkListWitnessFor elemTy k
            listMap := listMap.push (xs, listLit)
        for (xs, elemTy) in deferredLists do
          let mut lenOpt : Option Nat := none
          for p in propsScalar do
            if lenOpt.isNone then
              let pSub := applyMap listMap p
              if let some rhs := findListLenEq? xs pSub then
                if let some k ← evalGroundNat? rhs then
                  if k ≤ 65536 then
                    lenOpt := some k
          let k := match lenOpt with
            | some n => n
            | none => if needsNonEmptyList xs conjScalar then 1 else 0
          if k > 256 then
            hasLargeReplicate := true
          let listLit ← mkListWitnessFor elemTy k
          listMap := listMap.push (xs, listLit)
        let fullSubst (e : Expr) : Expr :=
          applyMap listMap (scalarSubst (baseSubst e))
        let conjFinal := applyMap listMap conjScalar
        if conjFinal.hasFVar || conjFinal.hasMVar then
          return none
        let conjWellTyped ← try
          Meta.check conjFinal
          Pure.pure true
        catch _ =>
          Pure.pure false
        if !conjWellTyped then
          return none
        let witMVar ← mkFreshExprMVar conjFinal
        setGoals [witMVar.mvarId!]
        let wideBinder := hasWideBitVecBinder conjFinal
        let ok ← if wideBinder then
          -- `decide` would enumerate all `2 ^ w` values via `BitVec.instDecidableForallBitVec`;
          -- only accept the witness if plain `simp` closes it (under a real heartbeat budget).
          withRealHeartbeatBudget 20000 false <|
            tryTacticQuiet (evalTactic (← `(tactic|
              (simp only [List.length_replicate, wp_norm, arm64_norm]; done))))
        else
          tryCatchRuntimeEx (
            withCurrHeartbeats do
              if hasLargeReplicate then
                tryTacticQuiet (evalTactic (← `(tactic| (
                  set_option maxHeartbeats 15000 in
                  (try simp (config := { decide := false }) only [List.length_replicate]
                   first
                     | done
                     | decide
                     | (simp (config := { decide := true }) only [List.length_replicate, wp_norm, arm64_norm]; done))
                ))))
              else
                tryTacticQuiet (evalTactic (← `(tactic| (
                  set_option maxHeartbeats 15000 in
                  first
                    | decide
                    | (simp (config := { decide := true }) only [wp_norm, arm64_norm]; done)
                ))))
          ) (fun _ => Pure.pure false)
        if ok then
          return some fullSubst
        else
          return none
      if let some substFn ← tryCandidate (useRelRank := true) (baseRankShift := 0) then
        return some substFn
      if let some substFn ← tryCandidate (useRelRank := false) (baseRankShift := 0) then
        return some substFn
      if let some substFn ← tryCandidate (useRelRank := true) (baseRankShift := 1) then
        return some substFn
      return none

/-- Result of running `#spec_nonvacuous` on a `Spec`. `notes` records sound reductions applied
    before checking (e.g. ghost lists specialized to `[]`); they are appended to the message. -/
inductive NonVacuousResult where
  /-- `numOpaque` counts quantified pure hypotheses (`∀ x : τ, ...` / `∃ x, ...`) that were neither
      refuted nor satisfied by a verified ground witness: the check is refutation-only for them.
      (`ok` is only returned when every forced-overlap query completed: an inconclusive query,
      e.g. one that exhausted its heartbeat budget, always yields `flagged`.) -/
  | ok (numSpatial : Nat) (numPure : Nat) (numOpaque : Nat) (notes : Array MessageData := #[])
  | flagged (reasons : Array MessageData) (notes : Array MessageData := #[])

/-- Render `#spec_nonvacuous` notes as a trailing `(note: ...)` list (empty when there are none,
    so messages of specs without notes are unchanged). -/
def formatNonVacuousNotes (notes : Array MessageData) : MessageData :=
  if notes.isEmpty then m!""
  else MessageData.joinSep (notes.toList.map fun n => m!"\n  (note: {n})") ""

private partial def hasDefaultWitnessElem (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  ty.isAppOfArity ``BitVec 1 || ty.isConstOf ``Nat || ty.isConstOf ``UInt8 ||
    (ty.isAppOfArity ``Prod 2 && hasDefaultWitnessElem ty.appFn!.appArg! &&
      hasDefaultWitnessElem ty.appArg!)

private def isUserRecursivePred (env : Environment) (nm : Name) : Bool :=
  match env.find? nm with
  | some (.defnInfo info) =>
    let retTy := info.type.getForallBody.consumeMData
    (retTy.isProp || retTy.isConstOf ``Arm64.SepProp) &&
    (info.value.find? fun s =>
      match s.constName? with
      | some c => c.isStr && (c.getString! == "brecOn" || c.getString! == "binductionOn" ||
          c == ``WellFounded.fix)
      | none => false).isSome
  | _ => false

private def reduceProdMkProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun sub => do
    let pick (b : Expr) (i : Nat) : Option Expr :=
      let b := b.consumeMData
      if b.isAppOfArity ``Prod.mk 4 && i < 2 then some (b.getArg! (2 + i)) else none
    match sub with
    | .proj ``Prod i b => return match pick b i with | some r => .done r | none => .continue
    | _ =>
      if sub.isAppOfArity ``Prod.fst 3 then
        if let some r := pick (sub.getArg! 2) 0 then return .done r
      if sub.isAppOfArity ``Prod.snd 3 then
        if let some r := pick (sub.getArg! 2) 1 then return .done r
      return .continue)

/-- Find a local `x : List α` (with no default element witness for `α`) that occurs in `e`
    only as a direct argument of user-defined recursive predicates (so specializing it to
    `[]` cannot conflict with other facts about `x`, e.g. `x.length = n`). Returns `x` and the
    predicates. -/
private def findRecListGhost? (e : Expr) : MetaM (Option (FVarId × Array Name)) := do
  let env ← getEnv
  let ref ← IO.mkRef (#[] : Array (FVarId × Name))
  e.forEach fun sub => do
    if let .const nm _ := sub.getAppFn then
      if sub.isApp && isUserRecursivePred env nm then
        for arg in sub.getAppArgs do
          if let .fvar fid := arg.consumeMData then
            ref.modify (·.push (fid, nm))
  let pairs ← ref.get
  let mut tried : Array FVarId := #[]
  for (fid, _) in pairs do
    if tried.contains fid then continue
    tried := tried.push fid
    let some decl := (← getLCtx).find? fid | continue
    if decl.isLet then continue
    let ty ← whnfR (← instantiateMVars decl.type)
    unless ty.isAppOfArity ``List 1 do continue
    if hasDefaultWitnessElem (ty.getArg! 0) then continue
    let fns := (pairs.filter (·.1 == fid)).foldl
      (fun acc (_, nm) => if acc.contains nm then acc else acc.push nm) #[]
    -- Erase the qualifying predicate applications; `x` must not occur anywhere else.
    -- (`rcases` can leave projections of the re-assembled ghost tuple, e.g.
    -- `(x, rest).2.1` in `Decidable` instances; reduce those first.)
    let erased := (← reduceProdMkProjs e).replace fun sub =>
      match sub.getAppFn with
      | .const nm _ =>
        if fns.contains nm && sub.getAppArgs.any (·.consumeMData == mkFVar fid) then
          some (mkConst ``True)
        else none
      | _ => none
    if erased.containsFVar fid then continue
    return some (fid, fns)
  return none

/-- Specialize every ghost `List` variable that is passed directly to a user-defined recursive
    predicate in hypothesis `hypName` (and whose element type the witness search cannot
    instantiate) to `[]`, keeping only the `nil` case of `cases`, then rewrite those predicates
    with their equation lemmas so they reduce to their base case. Sound for an `OK` verdict:
    the main goal after specialization implies the original one (a model of the specialized
    precondition is a model of the original). Returns human-readable notes. -/
private def specializeRecListGhosts (hypName : Name) : TacticM (Array MessageData) := do
  let mut notes : Array MessageData := #[]
  for _ in [:8] do
    let goals ← getGoals
    if goals.isEmpty then break
    let g ← getMainGoal
    let found? ← g.withContext do
      let some decl := (← getLCtx).findFromUserName? hypName | return none
      let some (fid, fns) ← findRecListGhost? (← instantiateMVars decl.type) | return none
      let ty ← instantiateMVars (← fid.getDecl).type
      let note ← addMessageContextFull
        m!"ghost `{mkFVar fid} : {ty}` passed to recursive {fns.toList.map mkConst} specialized to `[]`"
      return some (fid, fns, note)
    let some (fid, fns, note) := found? | break
    let subgoals ← try g.cases fid catch _ => break
    let some nilCase := subgoals.find? (·.ctorName == some ``List.nil) | break
    setGoals [nilCase.mvarId]
    notes := notes.push note
    let hypId := mkIdent hypName
    let fnIds : Array Ident := fns.map mkIdent
    let _ ← withCurrHeartbeats do
      tryTacticQuiet (evalTactic (← `(tactic|
        simp only [$[$fnIds:ident],*] at $hypId:ident)))
  return notes

private def NonVacuousResult.okMsg (spec : Syntax) (numSpatial numPure numOpaque : Nat) :
    MessageData :=
  let base := m!"[spec_nonvacuous] OK ({spec}): {numSpatial} spatial block(s) pairwise disjoint, {numPure} pure hypothesis(es) non-contradictory."
  if numOpaque == 0 then base
  else base ++ m!" Note: {numOpaque} quantified pure hypothesis(es) were not refuted but also not witnessed (treated as opaque); prove satisfiability separately for a full non-vacuity guarantee."

private def unfoldUserPropToAndOrExists? (ty : Expr) : MetaM (Option Expr) := do
  let ty := ty.consumeMData
  let fn := ty.getAppFn.consumeMData
  unless fn.isConst do return none
  if ty.isAppOf ``And || ty.isAppOf ``Exists || ty.isAppOf ``Or || ty.isAppOf ``Not ||
     ty.isAppOf ``Eq || ty.isAppOf ``Ne || ty.isAppOf ``LE.le || ty.isAppOf ``LT.lt ||
     ty.isAppOf ``GE.ge || ty.isAppOf ``GT.gt || ty.isAppOf ``Arm64.HookSat ||
     (ty.find? fun s => s.isConstOf ``Arm64.State.mem || s.isConstOf ``Arm64.Memory).isSome then
    return none
  if let some ty' ← unfoldDefinition? ty then
    let ty' := ty'.consumeMData
    if ty'.isAppOfArity ``And 2 || ty'.isAppOfArity ``Exists 2 then
      return some ty'
  return none

private partial def mentionsStateSp (s0Fid : FVarId) (e : Expr) : Bool :=
  let e := e.consumeMData
  if !e.hasFVar then false
  else if e.isFVar then e.fvarId! == s0Fid
  else if (e.isAppOfArity ``Arm64.State.mem 1 || e.isAppOfArity ``Arm64.State.spAligned 1) &&
          (e.getArg! 0).consumeMData == .fvar s0Fid then
    false
  else if (e.isAppOfArity ``Arm64.State.readReg64 2 || e.isAppOfArity ``Arm64.State.readReg32 2) &&
          (e.getArg! 0).consumeMData == .fvar s0Fid &&
          (e.getArg! 1).consumeMData.isAppOfArity ``Arm64.Reg.gpr 1 then
    mentionsStateSp s0Fid (e.getArg! 1)
  else if e.isAppOfArity ``Arm64.State.readReg 3 &&
          (e.getArg! 0).consumeMData == .fvar s0Fid &&
          (e.getArg! 2).consumeMData.isAppOfArity ``Arm64.Reg.gpr 1 then
    mentionsStateSp s0Fid (e.getArg! 1) || mentionsStateSp s0Fid (e.getArg! 2)
  else
    match e with
    | .app f a => mentionsStateSp s0Fid f || mentionsStateSp s0Fid a
    | .lam _ t b _ | .forallE _ t b _ => mentionsStateSp s0Fid t || mentionsStateSp s0Fid b
    | .letE _ t v b _ => mentionsStateSp s0Fid t || mentionsStateSp s0Fid v || mentionsStateSp s0Fid b
    | .proj _ _ b => mentionsStateSp s0Fid b
    | _ => false

private partial def mentionsStateNonMem (s0Fid : FVarId) (e : Expr) : Bool :=
  let e := e.consumeMData
  if !e.hasFVar then false
  else if e.isFVar then e.fvarId! == s0Fid
  else if (e.isAppOfArity ``Arm64.State.mem 1 || e.isAppOfArity ``Arm64.State.spAligned 1) &&
          (e.getArg! 0).consumeMData == .fvar s0Fid then
    false
  else
    match e with
    | .app f a => mentionsStateNonMem s0Fid f || mentionsStateNonMem s0Fid a
    | .lam _ t b _ | .forallE _ t b _ => mentionsStateNonMem s0Fid t || mentionsStateNonMem s0Fid b
    | .letE _ t v b _ => mentionsStateNonMem s0Fid t || mentionsStateNonMem s0Fid v || mentionsStateNonMem s0Fid b
    | .proj _ _ b => mentionsStateNonMem s0Fid b
    | _ => false

private partial def extractGprReadIdx? (s0Fid : FVarId) (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if (e.isAppOfArity ``BitVec.truncate 3 || e.isAppOfArity ``BitVec.setWidth 3) then
    extractGprReadIdx? s0Fid (e.getArg! 2)
  else if (e.isAppOfArity ``Arm64.State.readReg64 2 || e.isAppOfArity ``Arm64.State.readReg32 2) &&
          (e.getArg! 0).consumeMData == .fvar s0Fid then
    let r := (e.getArg! 1).consumeMData
    if r.isAppOfArity ``Arm64.Reg.gpr 1 then
      match evalBitVecLitPure? (r.getArg! 0) with
      | some (_, idx) => some idx
      | none => none
    else none
  else none

private partial def countGprReads (s0Fid : FVarId) (e : Expr)
    (acc : Std.HashMap Nat Nat) : Std.HashMap Nat Nat :=
  let e := e.consumeMData
  if !e.hasFVar then acc
  else if (e.isAppOfArity ``Arm64.State.readReg64 2 || e.isAppOfArity ``Arm64.State.readReg32 2) &&
          (e.getArg! 0).consumeMData == .fvar s0Fid then
    let r := (e.getArg! 1).consumeMData
    let acc :=
      if r.isAppOfArity ``Arm64.Reg.gpr 1 then
        match evalBitVecLitPure? (r.getArg! 0) with
        | some (_, idx) => acc.insert idx (acc.getD idx 0 + 1)
        | none => acc
      else acc
    countGprReads s0Fid r acc
  else
    match e with
    | .app f a => countGprReads s0Fid a (countGprReads s0Fid f acc)
    | .lam _ t b _ | .forallE _ t b _ => countGprReads s0Fid b (countGprReads s0Fid t acc)
    | .letE _ t v b _ =>
      countGprReads s0Fid b (countGprReads s0Fid v (countGprReads s0Fid t acc))
    | .proj _ _ b => countGprReads s0Fid b acc
    | _ => acc

/-- Core non-vacuity check on `specTerm : Term`. -/
def checkSpecNonVacuous (specStx : Syntax) (cfg : SpecNonVacuousConfig := {}) :
    TermElabM NonVacuousResult := do
  let specExpr0 ← Term.elabTermAndSynthesize specStx none
  let specTy0 ← inferType specExpr0
  forallTelescopeReducing specTy0 fun params bodyTy => do
    let appSpec := mkAppN specExpr0 params
    let bodyTyWhnf ← whnfR bodyTy
    unless bodyTyWhnf.isAppOfArity ``Arm64.Spec 1 do
      return .flagged #[← addMessageContextFull m!"expected a term of type `Arm64.Spec α`, got `{bodyTy}`"]
    let alpha := bodyTyWhnf.getArg! 0
    let stateTy := mkConst ``Arm64.State
    let goalType ← withLocalDeclD `a alpha fun a =>
      withLocalDeclD `s0 stateTy fun s0 => do
      let spAlignedEq ← mkEq (mkApp (mkConst ``Arm64.State.spAligned) s0) (mkConst ``Bool.true)
      withLocalDeclD `hsp_align spAlignedEq fun hsp =>
      withLocalDeclD `hpre (mkApp2 (mkConst ``Arm64.SepProp.Satisfies)
        (mkApp4 (mkConst ``Arm64.Spec.pre) alpha appSpec a s0)
        (mkApp (mkConst ``Arm64.State.mem) s0)) fun hpre => do
        mkForallFVars #[a, s0, hsp, hpre] (mkConst ``False)
    let mvar ← mkFreshExprMVar goalType
    let res ← (do
      let aId := mkIdent `a
      let s0Id := mkIdent `s0
      let hspId := mkIdent `hsp_align
      let hpreId := mkIdent `hpre
      evalTactic (← `(tactic| intro $aId:ident $s0Id:ident $hspId:ident $hpreId:ident))
      -- Unpack `Prod` / `PUnit` ghost tuples on `a` BEFORE unfolding `hpre` so `rcases`
      -- does not repeatedly re-typecheck a huge unfolded separation-logic term.
      let mut prodProgress := true
      while prodProgress do
        prodProgress := false
        let mvarId ← getMainGoal
        let lctx ← mvarId.withContext getLCtx
        for decl in lctx do
          if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
            let ty ← mvarId.withContext (whnf (← instantiateMVars decl.type))
            if ty.isAppOfArity ``Prod 2 then
              let id := mkIdent decl.userName
              let id1 ← freshIdent `a
              let id2 ← freshIdent `a_rest
              if ← tryTacticQuiet (evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩))) then
                prodProgress := true
                break
            else if ty.isAppOfArity ``PUnit 0 then
              let id := mkIdent decl.userName
              if ← tryTacticQuiet (evalTactic (← `(tactic| rcases $id:ident with ⟨⟩))) then
                prodProgress := true
                break
      evalTactic (← `(tactic| wp_unfold_specs))
      -- Ghost `List` variables (with no default element witness) that drive user-defined
      -- recursive predicates (`ChainPre ... levels`, `ChainOk ... levels`) would otherwise leave
      -- those predicates opaque, defeat the concrete witness search, and push the spatial check
      -- into its slow per-pair fallback. Specialize them to `[]` (sound for `OK`: a witness of
      -- the specialized instance is a witness of the spec) and report it in the message.
      let specNotes ← specializeRecListGhosts `hpre
      -- Unfold non-primitive SepProp definitions in `hpre` (up to 4 rounds), except `stackFrame` and
      -- `stackFrameAt`: a frame that the `simp` below cannot expand into slots (symbolic size)
      -- must still reach `extractBlockInfo?` as the block `[sp - n, sp)`, not an opaque term
      for _ in [:4] do
        let g0 ← getMainGoal
        let userSepDefs ← g0.withContext do
          if let some decl := (← getLCtx).findFromUserName? `hpre then
            collectUserSepDefs (← instantiateMVars decl.type) (keepStackFrameAt := true)
          else
            Pure.pure #[]
        if userSepDefs.isEmpty then
          break
        for id in userSepDefs do
          let _ ← tryTacticQuiet (evalTactic (← `(tactic| dsimp only [$id:ident] at $hpreId:ident)))
      -- `-reduceStackFrameAt`: keep each literal-size `stackFrameAt sp n` as one block instead of
      -- `n / 8` slot atoms, which would make the pairwise overlap check quadratic in frame size
      let _ ← withCurrHeartbeats do
        tryTacticQuiet (evalTactic (← `(tactic|
          simp (config := { decide := true }) only [
            stackFrame, stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
            satisfies_bupd,
            satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc,
            satisfies_pure, satisfies_emp, sepExists_sepConj_left, sepExists_sepConj_right,
            satisfies_sepExists, sepConj_assoc, emp_sepConj, sepConj_emp,
            Arm64.Spec.split,
            ← disjointRegions_iff_disjoint64, ← disjointRegions_iff_disjoint128,
            Arm64.CalleeSavedPreserved, Prod.fst, Prod.snd, wp_norm, arm64_norm,
            -ProofLib.reduceStackFrameAt] at $hpreId:ident)))
      -- Split `And` and `Exists` hypotheses in `lctx` without re-running `simp` on every split conjunct
      let mut splitProgress := true
      while splitProgress do
        splitProgress := false
        let mvarId ← getMainGoal
        let lctx ← mvarId.withContext getLCtx
        for decl in lctx do
          if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
            let ty ← mvarId.withContext (instantiateMVars decl.type)
            if ty.isAppOfArity ``And 2 then
              let id := mkIdent decl.userName
              let h1 ← freshIdent `h
              if ← tryTacticQuiet (evalTactic (← `(tactic| rcases $id:ident with ⟨$h1:ident, $id:ident⟩))) then
                splitProgress := true
                break
            else if ty.isAppOfArity ``Exists 2 then
              let id := mkIdent decl.userName
              let vId ← freshIdent `v_ex
              if ← tryTacticQuiet (evalTactic (← `(tactic| rcases $id:ident with ⟨$vId:ident, $id:ident⟩))) then
                splitProgress := true
                break
            else if !ty.isAppOf ``Arm64.SepProp.Satisfies &&
                    !ty.isAppOf ``Arm64.DisjointRegions &&
                    !ty.isAppOf ``Arm64.Memory.Disjoint64 &&
                    !ty.isAppOf ``Arm64.Memory.Disjoint128 &&
                    !ty.isAppOf ``Arm64.CalleeSavedPreserved then
              let andTy? ← mvarId.withContext do
                if let some t ← unfoldToAndIfPossible? ty then Pure.pure (some t)
                else unfoldUserPropToAndOrExists? ty
              if let some andTy := andTy? then
                let g' ← mvarId.changeLocalDecl decl.fvarId andTy
                replaceMainGoal [g']
                let id := mkIdent decl.userName
                let _ ← withCurrHeartbeats do
                  tryTacticQuiet (evalTactic (← `(tactic|
                    simp (config := { decide := true }) only [
                      ← disjointRegions_iff_disjoint64, ← disjointRegions_iff_disjoint128,
                      Arm64.CalleeSavedPreserved, Prod.fst, Prod.snd, wp_norm, arm64_norm] at $id:ident)))
                let h1 ← freshIdent `h
                if ← tryTacticQuiet (evalTactic (← `(tactic| rcases $id:ident with ⟨$h1:ident, $id:ident⟩))) then
                  splitProgress := true
                  break
      if (← getGoals).isEmpty then
        return NonVacuousResult.flagged #[m!"precondition reduces directly to `False`"] specNotes
      let g ← getMainGoal
      let mut reasons : Array MessageData := #[]
      let (satFVar?, satProp?, numPureHyps, pureFVars, allPureFVars, spInPure, s0Fid?, quantFVars) ← g.withContext do
        let lctx ← getLCtx
        let s0Fid? := (lctx.findFromUserName? `s0).map LocalDecl.fvarId
        let mut satFVar? : Option FVarId := none
        let mut satProp? : Option Expr := none
        let mut pureDecls : Array (FVarId × Expr) := #[]
        let mut gprCounts : Std.HashMap Nat Nat := {}
        for decl in lctx do
          if !decl.isImplementationDetail && !decl.isAuxDecl then
            let ty ← instantiateMVars decl.type
            if ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 then
              satFVar? := some decl.fvarId
              let p := ty.getArg! 0
              satProp? := some p
              if let some s0Fid := s0Fid? then
                gprCounts := countGprReads s0Fid p gprCounts
            else if ← isProp ty then
              pureDecls := pureDecls.push (decl.fvarId, ty)
              if let some s0Fid := s0Fid? then
                gprCounts := countGprReads s0Fid ty gprCounts
        let isUniqueGprBinding (ty : Expr) : Bool :=
          match s0Fid?, ty.eq? with
          | some s0Fid, some (_, lhs, rhs) =>
            let l := lhs.consumeMData
            let r := rhs.consumeMData
            match extractGprReadIdx? s0Fid l with
            | some idx => r.isFVar && r.fvarId! != s0Fid && gprCounts.getD idx 0 == 1
            | none =>
              match extractGprReadIdx? s0Fid r with
              | some idx => l.isFVar && l.fvarId! != s0Fid && gprCounts.getD idx 0 == 1
              | none => false
          | _, _ => false
        let mut pureCount : Nat := 0
        let mut quantFVars : Array FVarId := #[]
        let mut fvars : Std.HashSet FVarId := {}
        let mut allFvars : Std.HashSet FVarId := {}
        let mut spInPure : Bool := false
        for (fid, ty) in pureDecls do
          pureCount := pureCount + 1
          let tyUnf ← match ← unfoldDefinition? ty.consumeMData with
            | some t => Pure.pure t
            | none => Pure.pure ty
          if (← hasQuantifierProp ty) || (← hasQuantifierProp tyUnf) then
            quantFVars := quantFVars.push fid
          if let some s0Fid := s0Fid? then
            if mentionsStateSp s0Fid ty then
              spInPure := true
          if !ty.isAppOf ``Eq || !(ty.getArg! 1).isAppOf ``Arm64.State.spAligned then
            let s := collectFVars {} ty
            for hfid in s.fvarSet do
              allFvars := allFvars.insert hfid
            if !isUniqueGprBinding ty then
              for hfid in s.fvarSet do
                if some hfid == s0Fid? then
                  if let some s0Fid := s0Fid? then
                    if mentionsStateNonMem s0Fid ty then
                      fvars := fvars.insert hfid
                else
                  fvars := fvars.insert hfid
        Pure.pure (satFVar?, satProp?, pureCount, fvars, allFvars, spInPure, s0Fid?, quantFVars)
      let rawAtoms ← match satProp? with
        | some P => g.withContext (flattenSepConj P)
        | none => Pure.pure #[]
      let mut blocks : Array SpatialBlockInfo := #[]
      for atom in rawAtoms do
        if atom.isAppOfArity ``Arm64.SepProp.pure 1 then
          let p := atom.getArg! 0
          if p.isConstOf ``False then
            reasons := reasons.push (← withGoalCtx g m!"precondition contains `⌜False⌝`")
        else if let some info ← extractBlockInfo? g atom then
          blocks := blocks.push info
      let mut spatialBasePtrs : Array Expr := #[]
      for b in blocks do
        let bp := extractBasePtr b.normBase
        unless spatialBasePtrs.contains bp do
          spatialBasePtrs := spatialBasePtrs.push bp
      let gPure ← match satFVar? with
        | some fid => g.tryClear fid
        | none => Pure.pure g
      let witnessFull? ←
        if cfg.smallBounds && !cfg.fullBvDecide then
          tryBoundedPureWitness? gPure spatialBasePtrs cfg.pageStep satProp?
        else
          Pure.pure none
      -- Only a witness that satisfies all pure hypotheses (including quantified ones) may be used
      -- to discharge the pairwise-overlap checks below: a witness that ignores a quantified
      -- hypothesis says nothing about overlap forced through that hypothesis.
      let witnessSubst? := witnessFull?
      let pureContradictory ←
        if witnessFull?.isSome then
          Pure.pure false
        else
          withoutModifyingState do
            setGoals [gPure]
            let fastRefuted ← withCurrHeartbeats do
              tryTacticQuiet (evalTactic (← `(tactic| (
                set_option maxHeartbeats 50000 in
                first
                  | contradiction
                  | assumption
                  | decide
                  | omega
                  | (bv_arith; done)
                  | (wp_bv_omega; done)
              ))))
            if fastRefuted then
              Pure.pure true
            else
              withCurrHeartbeats do
                tryTacticQuiet (evalTactic (← `(tactic| (
                  set_option maxHeartbeats 150000 in
                  first
                    | (bv_decide; done)
                    | (simp (config := { decide := true }) only [wp_norm, arm64_norm] at *;
                       first | contradiction | decide | omega | (bv_arith; done) | (wp_bv_omega; done) | (bv_decide; done))
                ))))
      if pureContradictory then
        reasons := reasons.push (← withGoalCtx g m!"contradictory pure precondition (pure hypotheses prove `False`)")
      else if cfg.smallBounds && cfg.requireWitness && witnessSubst?.isNone then
        reasons := reasons.push m!"no concrete small-bounds witness found for the pure precondition (requireWitness)"
      let mut witnessRanges : Array (Option (Nat × Nat)) := Array.replicate blocks.size none
      if let some substFn := witnessSubst? then
        for idx in [:blocks.size] do
          let b := blocks[idx]!
          let range? ← g.withContext do
            if let some addrNat ← evalGroundBv64? (substFn b.normBase) then
              let lenNat? ← match b.lenNat? with
                | some n => Pure.pure (some n)
                | none => evalGroundNat? (substFn b.lenExpr)
              if let some lenNat := lenNat? then
                if addrNat + lenNat ≤ 2 ^ 64 then
                  Pure.pure (some (addrNat, lenNat))
                else
                  Pure.pure none
              else
                Pure.pure none
            else
              Pure.pure none
          witnessRanges := witnessRanges.set! idx range?
      -- First block pair whose forced-overlap query was inconclusive (budget exhausted), and the
      -- number of pairs left unchecked after it. Any inconclusive pair makes the result `FLAGGED`.
      let activePureFVars := if pureContradictory then allPureFVars else pureFVars
      let anchorInPure (anchor : Expr) : Bool :=
        let a := anchor.consumeMData
        match s0Fid? with
        | some s0Fid =>
          if a.isAppOfArity ``Arm64.State.sp 1 && (a.getArg! 0).consumeMData == Expr.fvar s0Fid then
            spInPure
          else
            (collectFVars {} a).fvarSet.any (fun fid => activePureFVars.contains fid)
        | none =>
          (collectFVars {} a).fvarSet.any (fun fid => activePureFVars.contains fid)
      let ovTac ← if quantFVars.isEmpty then
          `(tactic| (
            dsimp only [Arm64.DisjointRegions, Arm64.InRegion] at *
            first
              | done
              | omega
              | (bv_arith; done)
              | (wp_bv_omega; done)))
        else
          `(tactic| (
            dsimp only [Arm64.DisjointRegions, Arm64.InRegion] at *
            first
              | done
              | omega
              | (bv_arith; done)
              | (wp_bv_omega; done)
              | (simp only [Nat.lt_one_iff, forall_eq, forall_const, exists_const,
                    exists_prop, and_self, and_true, true_and, implies_true] at *
                 first
                   | done
                   | omega
                   | (bv_arith; done)
                   | (wp_bv_omega; done))))
      let mut inconclusive? : Option MessageData := none
      let mut uncheckedPairs : Nat := 0
      for h1 : i in [:blocks.size] do
        let b1 := blocks[i]
        if let some n1 := b1.lenNat? then
          if n1 > 2 ^ 64 then
            reasons := reasons.push (← withGoalCtx g m!"spatial region `{b1.atom}` has length {n1} > 2^64 (vacuous)")
        let b1InPure := anchorInPure b1.anchor
        for h2 : j in [i + 1 : blocks.size] do
          let b2 := blocks[j]
          -- Two read-only blocks (`↦ᵣ`) are duplicable and may share `.rodata` addresses
          if !(b1.isReadOnly && b2.isReadOnly) then
            let sameAnchor ← g.withContext do
              if b1.anchor == b2.anchor then Pure.pure true
              else withReducible (isDefEq b1.anchor b2.anchor)
            let mut overlapped := false
            if sameAnchor then
              match b1.lenNat?, b2.lenNat? with
              | some n1, some n2 =>
                if n1 > 0 && n2 > 0 then
                  let lo := max b1.offset b2.offset
                  let hi := min (b1.offset + (n1 : Int)) (b2.offset + (n2 : Int))
                  if lo < hi then
                    overlapped := true
                    let r1 := formatAnchorOff b1.anchor b1.offset
                    let r2 := formatAnchorOff b2.anchor b2.offset
                    reasons := reasons.push (← withGoalCtx g
                      m!"overlapping spatial regions on `{b1.anchor}`: `{b1.atom}` ([{r1}, +{n1})) and `{b2.atom}` ([{r2}, +{n2}))")
              | _, _ =>
                if b1.offset == b2.offset then
                  overlapped := true
                  reasons := reasons.push (← withGoalCtx g
                    m!"overlapping spatial regions at `{b1.normBase}`: `{b1.atom}` and `{b2.atom}`")
            if !overlapped && !sameAnchor then
              -- If `b1` and `b2` are disjoint in the ground witness model of the pure
              -- hypotheses, the pure hypotheses cannot logically entail `¬ DisjointRegions b1 b2`.
              let witnessDisjoint : Bool :=
                match witnessRanges[i]!, witnessRanges[j]! with
                | some (a1, l1), some (a2, l2) =>
                  l1 == 0 || l2 == 0 || a1 + l1 ≤ a2 || a2 + l2 ≤ a1
                | _, _ => false
              if !witnessDisjoint then
                let b2InPure := anchorInPure b2.anchor
                if b1InPure && b2InPure then
                  if inconclusive?.isSome then
                    -- The result is already `FLAGGED` (fail closed); count the remaining pairs
                    -- in the reason instead of spending another full budget on each of them.
                    uncheckedPairs := uncheckedPairs + 1
                    continue
                  let forcedOverlap? ← withoutModifyingState do
                    gPure.withContext do
                      let disjProp := mkApp4 (mkConst ``Arm64.DisjointRegions) b1.normBase b1.lenExpr b2.normBase b2.lenExpr
                      let notDisj := mkNot disjProp
                      let mvarDisj ← mkFreshExprMVar notDisj
                      setGoals [mvarDisj.mvarId!]
                      let budgetRaw ← if cfg.overlapHeartbeats == 0 then
                          Pure.pure (← readThe Core.Context).maxHeartbeats
                        else Pure.pure (cfg.overlapHeartbeats * 1000)
                      withRealHeartbeatBudgetRaw? budgetRaw <|
                        tryTacticQuiet (evalTactic ovTac)
                  match forcedOverlap? with
                  | some true =>
                    reasons := reasons.push (← withGoalCtx g
                      m!"pure hypotheses force spatial overlap between `{b1.atom}` and `{b2.atom}`")
                  | some false => Pure.pure ()
                  | none =>
                    inconclusive? := some (← withGoalCtx g m!"`{b1.atom}` and `{b2.atom}`")
      if let some pairMsg := inconclusive? then
        let budgetMsg := if cfg.overlapHeartbeats == 0 then
            m!"the command's `maxHeartbeats` budget"
          else m!"its `overlapHeartbeats := {cfg.overlapHeartbeats}` budget"
        reasons := reasons.push
          m!"inconclusive forced-overlap query between {pairMsg} (exhausted {budgetMsg}); {uncheckedPairs} further block pair(s) not checked. Raise `set_option maxHeartbeats N in` (or `overlapHeartbeats`) so that every pair is checked"
      if reasons.isEmpty then
        return NonVacuousResult.ok blocks.size numPureHyps
          (if witnessFull?.isSome then 0 else quantFVars.size) specNotes
      else
        return NonVacuousResult.flagged reasons specNotes
    ).run { elaborator := .anonymous } |>.run' { goals := [mvar.mvarId!] }
    return res

/-- Check that `<spec>`'s precondition is non-vacuous (pairwise-disjoint spatial footprint and
    non-contradictory pure conditions). Logs diagnostics via `logInfo` and never fails the build. -/
syntax (name := specNonvacuousCmd) "#spec_nonvacuous " (Lean.Parser.Tactic.optConfig)? term : command

/-- Strict variant of `#spec_nonvacuous` that throws an error when vacuity is detected. -/
syntax (name := specNonvacuousBangCmd) "#spec_nonvacuous! " (Lean.Parser.Tactic.optConfig)? term : command

@[command_elab specNonvacuousCmd]
def elabSpecNonvacuous : Command.CommandElab
  | `(#spec_nonvacuous $[$cfgStx?]? $spec:term) => do
    let res ← Command.liftTermElabM do
      try
        let cfg ← match cfgStx? with
          | some cfgStx => (elabSpecNonVacuousConfig cfgStx).run { elaborator := .anonymous } |>.run' { goals := [] }
          | none => Pure.pure {}
        checkSpecNonVacuous spec cfg
      catch e =>
        return .flagged #[m!"elaboration/check error: {e.toMessageData}"]
    match res with
    | .ok numSpatial numPure numOpaque notes =>
      logInfo (NonVacuousResult.okMsg spec numSpatial numPure numOpaque ++ formatNonVacuousNotes notes)
    | .flagged reasons notes =>
      let bulletList := MessageData.joinSep (reasons.toList.map fun r => m!"\n  - {r}") ""
      logInfo m!"[spec_nonvacuous] FLAGGED ({spec}):{bulletList}{formatNonVacuousNotes notes}"
  | _ => throwUnsupportedSyntax

@[command_elab specNonvacuousBangCmd]
def elabSpecNonvacuousBang : Command.CommandElab
  | `(#spec_nonvacuous! $[$cfgStx?]? $spec:term) => do
    let res ← Command.liftTermElabM do
      let cfg ← match cfgStx? with
        | some cfgStx => (elabSpecNonVacuousConfig cfgStx).run { elaborator := .anonymous } |>.run' { goals := [] }
        | none => Pure.pure {}
      checkSpecNonVacuous spec cfg
    match res with
    | .ok numSpatial numPure numOpaque notes =>
      logInfo (NonVacuousResult.okMsg spec numSpatial numPure numOpaque ++ formatNonVacuousNotes notes)
    | .flagged reasons notes =>
      let bulletList := MessageData.joinSep (reasons.toList.map fun r => m!"\n  - {r}") ""
      throwError m!"[spec_nonvacuous] FLAGGED ({spec}):{bulletList}{formatNonVacuousNotes notes}"
  | _ => throwUnsupportedSyntax

/-! ## Symbolic Execution Smoke Checker -/

/-- Outcome of a single execution path explored by `#spec_smoke`. -/
inductive SmokePathOutcome where
  | returned (pc : MessageData) (postClosed : Bool) (pathConds : Array MessageData)
  | stuck (pc : MessageData) (inst? : Option MessageData) (reason : MessageData) (pathConds : Array MessageData)
  | reachedCall (pc : MessageData) (pathConds : Array MessageData)
  | branchLimit (pc : MessageData) (cond : MessageData) (pathConds : Array MessageData)
  | heartbeatLimit (pc : MessageData) (pathConds : Array MessageData)
  deriving Inhabited

/-- If `progExpr` is a canonical `<codeName>` (or `<codeName>.rebase ...`) that has `<codeName>_tree`
    and `<codeName>_fetch_at` in the environment, try to decode the instruction at `pcExpr` and
    assert a local fetch hypothesis so `wpStepCore` can step without needing `*Fns.lean`. -/
private def tryAssertTreeFetch (progExpr pcExpr : Expr) : TacticM (Option Expr) := do
  let g ← getMainGoal
  g.withContext do
    let env ← getEnv
    let codeConst? : Option Name :=
      if progExpr.isConst then some progExpr.constName!
      else if progExpr.isAppOfArity ``Program.rebase 4 && (progExpr.getArg! 0).isConst then
        some (progExpr.getArg! 0).constName!
      else none
    let some codeName := codeConst? | return none
    let treeName := codeName.appendAfter "_tree"
    let fetchAtName := codeName.appendAfter "_fetch_at"
    unless (env.find? treeName).isSome && (env.find? fetchAtName).isSome do
      return none
    let some (64, offVal) ← evalBitVecLit? pcExpr | return none
    let offExpr := toExpr offVal
    let decodeCall := mkApp2 (mkConst ``ProofLib.ProgramReflection.WordTree.fetchDecodeAt)
      (mkConst treeName) offExpr
    let decoded ← withTransparency .all (whnf decodeCall)
    unless decoded.isAppOfArity ``Option.some 2 do return none
    let instExpr := decoded.getArg! 1
    if progExpr.isConst then
      let fetchGoalTy ← mkEq
        (mkApp2 (mkConst ``Program.fetch) progExpr (toExpr (BitVec.ofNat 64 offVal)))
        (← mkAppM ``Option.some #[instExpr])
      let hDecode ← mkEqRefl decoded
      let hoffTy ← mkAppM ``LT.lt #[offExpr, toExpr (2 ^ 64 : Nat)]
      let hoffMVar ← mkFreshExprMVar hoffTy
      let saved ← getGoals
      setGoals [hoffMVar.mvarId!]
      let okOff ← tryTacticQuiet (evalTactic (← `(tactic| decide)))
      setGoals saved
      if okOff then
        let prf := mkApp4 (mkConst fetchAtName) offExpr instExpr hDecode (← instantiateMVars hoffMVar)
        if ← isDefEq (← inferType prf) fetchGoalTy then
          let nm ← g.withContext do return (← getLCtx).getUnusedName `_h_tree_fetch
          let g' ← g.assert nm fetchGoalTy prf
          let (_, g'') ← g'.intro1P
          replaceMainGoal [g'']
    return some instExpr

private def fetchInstrAtPC? (progExpr pcExpr : Expr) : TacticM (Option Expr) := do
  if let some inst ← tryAssertTreeFetch progExpr pcExpr then
    return some inst
  let g ← getMainGoal
  g.withContext do
    let savedGoals ← getGoals
    let instMVar ← mkFreshExprMVar (mkConst ``Instr)
    let someInst ← mkAppM ``Option.some #[instMVar]
    let fetchLhs := mkApp2 (mkConst ``Program.fetch) progExpr pcExpr
    let fetchGoalTy ← mkEq fetchLhs someInst
    let fetchGoal ← mkFreshExprMVar fetchGoalTy
    setGoals [fetchGoal.mvarId!]
    let ok ←
      if ← tryCloseFetchFromHasCode then
        Pure.pure true
      else if ← tryTacticQuiet (evalTactic (← `(tactic| wp_focus_close wp_assumption))) then
        Pure.pure true
      else if (← evalBitVecLit? pcExpr).isSome then
        tryTacticQuiet (evalTactic (← `(tactic| wp_focus_close (
          (conv => lhs; simp (config := { decide := true }) only [arm64_norm]);
          rfl))))
      else
        Pure.pure false
    setGoals savedGoals
    if ok then
      return some (← instantiateMVars instMVar)
    else
      return none

private def extractInstrAddrMode? (instExpr : Expr) : MetaM (Option (Expr × Nat × Bool)) := do
  let instExpr ← instantiateMVars instExpr
  let opFn := instExpr.getAppFn
  let isPair :=
    opFn.isConstOf ``Instr.ldp || opFn.isConstOf ``Instr.stp ||
    opFn.isConstOf ``Instr.ldpSimd || opFn.isConstOf ``Instr.stpSimd
  let memSizeBytes (szExpr : Expr) : Nat :=
    match szExpr.constName? with
    | some ``MemWidth.B8  => 1
    | some ``MemWidth.H16 => 2
    | some ``MemWidth.W32 => 4
    | _                   => 8
  let elemBytes : Nat :=
    if instExpr.isAppOfArity ``Instr.ldr 5 then
      memSizeBytes (instExpr.getArg! 1)
    else if instExpr.isAppOfArity ``Instr.str 3 then
      memSizeBytes (instExpr.getArg! 0)
    else if instExpr.isAppOfArity ``Instr.ldp 5 then
      if instExpr.getArg! 1 == mkConst ``Bool.true || instExpr.getArg! 0 == mkConst ``RegWidth.W32
      then 4 else 8
    else if instExpr.isAppOfArity ``Instr.stp 4 then
      if instExpr.getArg! 0 == mkConst ``RegWidth.W32 then 4 else 8
    else if opFn.isConstOf ``Instr.ldrSimd || opFn.isConstOf ``Instr.strSimd ||
            opFn.isConstOf ``Instr.ldpSimd || opFn.isConstOf ``Instr.stpSimd then
      let sz := instExpr.getArg! 0
      if sz == mkConst ``SimdMemSize.B8 then 1
      else if sz == mkConst ``SimdMemSize.H16 then 2
      else if sz == mkConst ``SimdMemSize.S32 then 4
      else if sz == mkConst ``SimdMemSize.Q128 then 16
      else 8
    else if opFn.isConstOf ``Instr.ldarStlr || opFn.isConstOf ``Instr.ldxr ||
            opFn.isConstOf ``Instr.stxr then
      memSizeBytes (instExpr.getArg! 0)
    else 8
  if instExpr.isAppOfArity ``Instr.ldarStlr 4 then
    let rn := instExpr.getArg! 2
    return some (mkApp2 (mkConst ``AddrMode.Offset) rn (toExpr 0#64), elemBytes, false)
  if instExpr.isAppOfArity ``Instr.ldxr 4 then
    let rn := instExpr.getArg! 2
    return some (mkApp2 (mkConst ``AddrMode.Offset) rn (toExpr 0#64), elemBytes, false)
  if instExpr.isAppOfArity ``Instr.stxr 5 then
    let rn := instExpr.getArg! 3
    return some (mkApp2 (mkConst ``AddrMode.Offset) rn (toExpr 0#64), elemBytes, false)
  for arg in instExpr.getAppArgs do
    let argTy ← inferType arg
    if argTy.isConstOf ``AddrMode then
      return some (arg, elemBytes, isPair)
  return none

private def isAddrCoveredBy (g : MVarId) (ea : Expr) (accessBytes : Nat) (P : Expr) : TacticM Bool := do
  let (eaAnchor, eaOff) ← g.withContext (decomposeAddrSigned ea)
  for atom in SepSolver.atoms P do
    if let some blk ← extractBlockInfo? g atom then
      let same ← g.withContext do
        if eaAnchor == blk.anchor then Pure.pure true
        else withReducible (isDefEq eaAnchor blk.anchor)
      if same then
        if let some n := blk.lenNat? then
          if blk.offset ≤ eaOff && eaOff + (accessBytes : Int) ≤ blk.offset + (n : Int) then
            return true
        else if blk.offset == eaOff then
          return true
      let defEqBase ← g.withContext (withReducible (isDefEq blk.normBase ea))
      if defEqBase then return true
  return false

private def diagnoseStuckGoal (progExpr pcExpr : Expr) : TacticM (Option MessageData × MessageData) := do
  let g ← getMainGoal
  let inst? ← fetchInstrAtPC? progExpr pcExpr
  let some instExpr := inst?
    | return (none, ← withGoalCtx g m!"could not fetch/decode instruction at PC {← formatPC g pcExpr}")
  let instMsg ← withGoalCtx g m!"{instExpr}"
  let ty ← g.withContext (instantiateMVars (← g.getType))
  let sExpr := ty.getArg! 2
  let pExpr := ty.getArg! 3
  if let some (addrModeExpr, elemBytes, isPair) ← g.withContext (extractInstrAddrMode? instExpr) then
    let rawEa ← g.withContext do
      let evalApp := mkApp2 (mkConst ``Arm64.evalAddrMode) sExpr addrModeExpr
      mkAppM ``Prod.fst #[evalApp]
    let ea ← normExprInGoal g rawEa
    let cov1 ← isAddrCoveredBy g ea elemBytes pExpr
    if !cov1 then
      return (some instMsg, ← withGoalCtx g m!"no cell at {ea} in {pExpr}")
    if isPair then
      let rawEa2 ← g.withContext (mkAppM ``HAdd.hAdd #[ea, toExpr (BitVec.ofNat 64 elemBytes)])
      let ea2 ← normExprInGoal g rawEa2
      let cov2 ← isAddrCoveredBy g ea2 elemBytes pExpr
      if !cov2 then
        return (some instMsg, ← withGoalCtx g m!"no cell at {ea2} in {pExpr}")
  let saved ← saveState
  let errMsg ← try
    let _ ← wpStepCore
    withGoalCtx g m!"step succeeded unexpectedly"
  catch e =>
    restoreState saved
    withGoalCtx g e.toMessageData
  return (some instMsg, errMsg)

private partial def smokeExplore (startHb maxHb : Nat) (stepFuel branchFuel : Nat)
    (pathConds : Array MessageData) : TacticM (Array SmokePathOutcome) := do
  let gs ← getGoals
  if gs.isEmpty then
    return #[.returned m!"0x0#64" true pathConds]
  let g0 ← getMainGoal
  let (_, targetPcExpr, pcExpr0) ← getSepWPStateAndPC
  let pcMsg0 ← formatPC g0 pcExpr0
  let curHb ← IO.getNumHeartbeats
  if curHb - startHb > maxHb then
    return #[.heartbeatLimit pcMsg0 pathConds]
  if stepFuel == 0 then
    return #[.stuck pcMsg0 none m!"step limit reached" pathConds]
  let atTarget ← withoutModifyingState do
    tryTacticQuiet do
      if ← isDefEq pcExpr0 targetPcExpr then Pure.pure () else throwError "not at target"
  if atTarget then
    let postClosed ← withoutModifyingState do
      tryTacticQuiet do
        evalTactic (← `(tactic| wp_done))
        unless (← getGoals).isEmpty do throwError "unsolved postcondition"
    return #[.returned pcMsg0 postClosed pathConds]
  -- If `pcExpr0` is an `ite c t e`, try deterministic resolution in `wpStepCore` first; else `wp_if`
  if pcExpr0.isAppOfArity ``ite 5 then
    let c := pcExpr0.getArg! 1
    let cMsg ← withGoalCtx g0 m!"{c}"
    let savedIte ← saveState
    let steppedDet? : Option Bool ← try
      some <$> wpStepCore
    catch _ =>
      restoreState savedIte
      Pure.pure none
    if let some isBl := steppedDet? then
      if isBl then
        let gBl ← getMainGoal
        let (_, _, newPc) ← getSepWPStateAndPC
        return #[.reachedCall (← formatPC gBl newPc) pathConds]
      return ← smokeExplore startHb maxHb (stepFuel - 1) branchFuel pathConds
    if branchFuel == 0 then
      return #[.branchLimit pcMsg0 cMsg pathConds]
    let savedSplit ← saveState
    let splitOk ← tryTacticQuiet (evalTactic (← `(tactic| wp_if)))
    if !splitOk then
      restoreState savedSplit
      return #[.stuck pcMsg0 none (← withGoalCtx g0 m!"failed to split conditional branch `{c}`") pathConds]
    let gsSplit ← getGoals
    match gsSplit with
    | gThen :: gElse :: _ =>
      let cThenMsg ← withGoalCtx gThen m!"{c}"
      let cElseMsg ← withGoalCtx gElse m!"{mkNot c}"
      setGoals [gThen]
      let outThen ← smokeExplore startHb maxHb (stepFuel - 1) (branchFuel - 1) (pathConds.push cThenMsg)
      setGoals [gElse]
      let outElse ← smokeExplore startHb maxHb (stepFuel - 1) (branchFuel - 1) (pathConds.push cElseMsg)
      return outThen ++ outElse
    | _ =>
      return #[.stuck pcMsg0 none m!"unexpected subgoals from `wp_if`" pathConds]
  let (progExpr, _, pcExpr) ← getSepWPStateAndPC
  let _ ← tryAssertTreeFetch progExpr pcExpr
  let saved ← saveState
  let stepped? : Option Bool ← try
    some <$> wpStepCore
  catch _ =>
    restoreState saved
    Pure.pure none
  match stepped? with
  | some true =>
    let gBl ← getMainGoal
    let (_, _, newPc) ← getSepWPStateAndPC
    return #[.reachedCall (← formatPC gBl newPc) pathConds]
  | some false =>
    smokeExplore startHb maxHb (stepFuel - 1) branchFuel pathConds
  | none =>
    let gStuck ← getMainGoal
    let pcMsg ← formatPC gStuck pcExpr
    let (inst?, reason) ← diagnoseStuckGoal progExpr pcExpr
    return #[.stuck pcMsg inst? reason pathConds]

private def buildSmokeGoalType (progOrCodeStx : Syntax) (entryOptStx : Option Syntax)
    (specStx : Syntax) : TermElabM (Expr × Bool) := do
  let progOrCode ← Term.elabTermAndSynthesize progOrCodeStx none
  let pocTy ← whnfR (← inferType progOrCode)
  let spec0 ← Term.elabTermAndSynthesize specStx none
  let specTy0 ← inferType spec0
  forallTelescopeReducing specTy0 fun params specBodyTy => do
    let specBodyTyWhnf ← whnfR specBodyTy
    unless specBodyTyWhnf.isAppOfArity ``Arm64.Spec 1 do
      throwError "expected a `Spec` term, got `{specBodyTy}`"
    let alpha := specBodyTyWhnf.getArg! 0
    let resolveEntryForProg (progE : Expr) : TermElabM Expr := do
      match entryOptStx with
      | some entryStx =>
        let e ← Term.elabTermAndSynthesize entryStx none
        let eTy ← whnfR (← inferType e)
        if eTy.isConstOf ``String then
          return mkApp2 (mkConst ``Arm64.Program.fnAddr) progE e
        else
          return e
      | none =>
        if pocTy.isConstOf ``Arm64.FnCode then
          let fcWhnf ← whnf progOrCode
          if fcWhnf.isAppOfArity ``Arm64.FnCode.mk 3 then
            let fnNameE := fcWhnf.getArg! 0
            let pinE ← whnf (fcWhnf.getArg! 2)
            if pinE.isAppOfArity ``Arm64.FnPin.addr 1 then
              return pinE.getArg! 0
            else
              return mkApp2 (mkConst ``Arm64.Program.fnAddr) progE fnNameE
        throwError "entry symbol or address is required when the first argument is not an `FnCode`"
    let bindBaseToProg (progE : Expr) : MetaM (Expr × Array Expr) := do
      let progBase := mkApp (mkConst ``Arm64.Program.base) progE
      let mut args : Array Expr := #[]
      let mut keptParams : Array Expr := #[]
      for p in params do
        let decl ← p.fvarId!.getDecl
        if (decl.userName == `base || decl.userName == `b) && decl.type.isAppOfArity ``BitVec 1 then
          args := args.push progBase
        else
          args := args.push p
          keptParams := keptParams.push p
      return (mkAppN spec0 args, keptParams)
    if pocTy.isConstOf ``Arm64.FnCode then
      let goal ← withLocalDeclD `prog (mkConst ``Arm64.Program) fun progE => do
        let holdsTy := mkApp2 (mkConst ``Arm64.FnCode.holds) progOrCode progE
        withLocalDeclD `h_code holdsTy fun hCode => do
          let entryE ← resolveEntryForProg progE
          let (specForProg, keptParams) ← bindBaseToProg progE
          let subOk := mkApp4 (mkConst ``Arm64.subroutine_ok) alpha progE entryE specForProg
          mkForallFVars ((keptParams.push progE).push hCode) subOk
      return (goal, true)
    else if pocTy.isAppOfArity ``List 1 && (pocTy.getArg! 0).isConstOf ``Arm64.FnCode then
      let goal ← withLocalDeclD `prog (mkConst ``Arm64.Program) fun progE => do
        let bundleTy := mkApp2 (mkConst ``Arm64.Program.hasCodeBundle) progE progOrCode
        withLocalDeclD `h_code bundleTy fun hCode => do
          let entryE ← resolveEntryForProg progE
          let (specForProg, keptParams) ← bindBaseToProg progE
          let subOk := mkApp4 (mkConst ``Arm64.subroutine_ok) alpha progE entryE specForProg
          mkForallFVars ((keptParams.push progE).push hCode) subOk
      return (goal, true)
    else
      let progE :=
        if pocTy.isConstOf ``Arm64.Obj.LinkedImage then
          mkApp (mkConst ``Arm64.Obj.LinkedImage.toProgram) progOrCode
        else
          progOrCode
      let entryE ← resolveEntryForProg progE
      let (specForProg, keptParams) ← bindBaseToProg progE
      let subOk := mkApp4 (mkConst ``Arm64.subroutine_ok) alpha progE entryE specForProg
      let goal ← mkForallFVars keptParams subOk
      return (goal, false)

/-- Default raw heartbeat budget for `#spec_smoke` (~50M raw heartbeats, corresponding to
    `set_option maxHeartbeats 50000`). -/
private def defaultSmokeMaxHeartbeats : Nat := 50000000

/-- Run the smoke check on `(progOrCode, entryOpt, spec)` and return all path outcomes. -/
def runSpecSmoke (progOrCodeStx : Syntax) (entryOptStx : Option Syntax) (specStx : Syntax) :
    TermElabM (Array SmokePathOutcome) := do
  let (goalType, hasCodeHyp) ← buildSmokeGoalType progOrCodeStx entryOptStx specStx
  let mvar ← mkFreshExprMVar goalType
  let startHb ← IO.getNumHeartbeats
  let maxHb := defaultSmokeMaxHeartbeats
  let outcomes ← (do
    withCurrHeartbeats do
      -- Introduce any outer parameters and `(prog : Program) (h_code : ...)` up to `subroutine_ok`
      while true do
        let g ← getMainGoal
        let ty ← g.withContext (whnfCore (← instantiateMVars (← g.getType)))
        if ← SpecShape.isFullAppOfAny? ty #[``Arm64.subroutine_ok, ``Arm64.Program.subroutineOk] then
          break
        if ty.isForall then
          let binderName :=
            if ty.bindingName!.isAnonymous || ty.bindingName!.hasMacroScopes then `h_param
            else ty.bindingName!
          let (_, g') ← g.intro binderName
          replaceMainGoal [g']
        else
          break
      let gSub ← getMainGoal
      let isSplit ← gSub.withContext do
        let ty ← whnfCore (← instantiateMVars (← gSub.getType))
        if ← SpecShape.isFullApp? ty ``Arm64.subroutine_ok then
          specIsSplit (← SpecShape.namedArg! ty ``Arm64.subroutine_ok `spec)
        else
          Pure.pure false
      let aId := mkIdent `a
      let s0Id := mkIdent `s0
      if isSplit then
        evalTactic (← `(tactic| wp_start $aId:ident $s0Id:ident))
      else
        evalTactic (← `(tactic| wp_init $aId:ident $s0Id:ident))
      -- Normalize `hpc : s0.pc = ...` if it uses `fnAddr` on a concrete `Program` (no `h_code` hyp)
      if !hasCodeHyp then
        let hpcId := mkIdent `hpc
        let _ ← tryTacticQuiet (evalTactic (← `(tactic|
          simp (config := { decide := true }) only [Program.fnAddr, wp_norm, arm64_norm] at $hpcId:ident)))
        let gHpc ← getMainGoal
        let _ ← tryTacticQuiet <| gHpc.withContext do
          let some decl := (← getLCtx).findFromUserName? `hpc | return
          let ty ← instantiateMVars decl.type
          let some (_, lhs, rhs) := ty.eq? | return
          if !rhs.hasFVar && !rhs.hasMVar && (← evalBitVecLit? rhs).isNone then
            let natExpr ← mkAppM ``BitVec.toNat #[rhs]
            let natWhnf ← withTransparency .all (whnf natExpr)
            if let some offVal := natWhnf.rawNatLit?.orElse (fun _ => natWhnf.nat?) then
              let litExpr := toExpr (BitVec.ofNat 64 offVal)
              let eqGoal ← mkEq lhs litExpr
              let prf ← mkExpectedTypeHint (← mkEqTrans decl.toExpr (← mkEqRefl litExpr)) eqGoal
              let g' ← gHpc.replace decl.fvarId prf eqGoal
              replaceMainGoal [g'.mvarId]
      let gWP ← getMainGoal
      let userSepDefs ← gWP.withContext do
        let ty ← instantiateMVars (← gWP.getType)
        -- `wp_init` / `wp_start` always produce a `SepWP` goal; anything else is a shape this
        -- smoke check does not understand, so fail closed instead of skipping the unfolding.
        let some P ← SpecShape.namedArg? ty ``ProofLib.SepWP `P |
          throwError "[spec_smoke] unrecognized spec shape after `wp_init`: expected a `SepWP` \
            goal, got{indentExpr ty}"
        collectUserSepDefs P
      if !userSepDefs.isEmpty then
        -- 1-based `conv => arg` position of `SepWP`'s `P` binder (not a literal, so a signature
        -- change cannot silently retarget the unfolding)
        let pPos := Syntax.mkNumLit (toString
          (((← SpecShape.constBinderNames ``ProofLib.SepWP).idxOf? `P).getD 3 + 1))
        for id in userSepDefs do
          let _ ← tryTacticQuiet (evalTactic (← `(tactic| (
            conv => arg $pPos:num; dsimp only [$id:ident]
          ))))
        let _ ← tryTacticQuiet (evalTactic (← `(tactic| (
          conv => arg $pPos:num; simp (config := { decide := true }) only [
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
            emp_sepConj, sepConj_emp, wp_norm, arm64_norm]
        ))))
      smokeExplore startHb maxHb 64 4 #[]
  ).run { elaborator := .anonymous } |>.run' { goals := [mvar.mvarId!] }
  return outcomes

private def formatPathConds (conds : Array MessageData) : MessageData :=
  if conds.isEmpty then
    m!"(unconditional)"
  else
    m!"[{MessageData.joinSep conds.toList ", "}]"

/-- Format `Array SmokePathOutcome` into a human-readable summary and return `(hasStuck, msg)`. -/
def formatSmokeOutcomes (header : MessageData) (outcomes : Array SmokePathOutcome) :
    Bool × MessageData := Id.run do
  let mut hasStuck := false
  let mut numReturned : Nat := 0
  let mut numClosed : Nat := 0
  let mut lines : List MessageData := []
  for idx in [:outcomes.size] do
    let out : SmokePathOutcome := outcomes[idx]!
    let pathNum : Nat := idx + 1
    match out with
    | SmokePathOutcome.returned pc postClosed conds =>
      numReturned := numReturned + 1
      if postClosed then numClosed := numClosed + 1
      let status := if postClosed then "returned & postcondition closed" else "returned (postcondition not auto-closed)"
      lines := lines ++ [m!"\n  - path {pathNum} {formatPathConds conds}: {status} at PC {pc}"]
    | SmokePathOutcome.stuck pc inst? reason conds =>
      hasStuck := true
      let instMsg := match inst? with
        | some i => m!" ({i})"
        | none => m!""
      lines := lines ++ [m!"\n  - path {pathNum} {formatPathConds conds}: STUCK at PC {pc}{instMsg}: {reason}"]
    | SmokePathOutcome.reachedCall pc conds =>
      lines := lines ++ [m!"\n  - path {pathNum} {formatPathConds conds}: reached call/stub at PC {pc}"]
    | SmokePathOutcome.branchLimit pc c conds =>
      lines := lines ++ [m!"\n  - path {pathNum} {formatPathConds conds}: branch depth limit at PC {pc} on `{c}`"]
    | SmokePathOutcome.heartbeatLimit pc conds =>
      hasStuck := true
      lines := lines ++ [m!"\n  - path {pathNum} {formatPathConds conds}: heartbeat limit reached at PC {pc}"]
  let tag := if hasStuck then "STUCK" else "OK"
  let summary := m!"[spec_smoke] {tag} ({header}): {numReturned}/{outcomes.size} path(s) reached return ({numClosed} closed postcondition){MessageData.joinSep lines ""}"
  (hasStuck, summary)

/-- Run `wp_init` + `wp_steps` (with bounded branch splitting) on a program/code and spec under a
    heartbeat cap, reporting either the first stuck PC + instruction + missing points-to cell or
    the reached spec paths. Never errors the build. -/
syntax (name := specSmokeCmd3) "#spec_smoke " term:max ppSpace term:max ppSpace term:max : command
syntax (name := specSmokeCmd2) "#spec_smoke " term:max ppSpace term:max : command
syntax (name := specSmokeBangCmd3) "#spec_smoke! " term:max ppSpace term:max ppSpace term:max : command
syntax (name := specSmokeBangCmd2) "#spec_smoke! " term:max ppSpace term:max : command

@[command_elab specSmokeCmd3]
def elabSpecSmoke3 : Command.CommandElab
  | `(#spec_smoke $p:term $e:term $s:term) => do
    let msg ← Command.liftTermElabM do
      try
        let outs ← runSpecSmoke p (some e) s
        return (formatSmokeOutcomes m!"{p} {e} {s}" outs).2
      catch ex =>
        return m!"[spec_smoke] ERROR ({p} {e} {s}): {ex.toMessageData}"
    logInfo msg
  | _ => throwUnsupportedSyntax

@[command_elab specSmokeCmd2]
def elabSpecSmoke2 : Command.CommandElab
  | `(#spec_smoke $p:term $s:term) => do
    let msg ← Command.liftTermElabM do
      try
        let outs ← runSpecSmoke p none s
        return (formatSmokeOutcomes m!"{p} {s}" outs).2
      catch ex =>
        return m!"[spec_smoke] ERROR ({p} {s}): {ex.toMessageData}"
    logInfo msg
  | _ => throwUnsupportedSyntax

@[command_elab specSmokeBangCmd3]
def elabSpecSmokeBang3 : Command.CommandElab
  | `(#spec_smoke! $p:term $e:term $s:term) => do
    let (hasStuck, msg) ← Command.liftTermElabM do
      let outs ← runSpecSmoke p (some e) s
      return formatSmokeOutcomes m!"{p} {e} {s}" outs
    if hasStuck then
      throwError msg
    else
      logInfo msg
  | _ => throwUnsupportedSyntax

@[command_elab specSmokeBangCmd2]
def elabSpecSmokeBang2 : Command.CommandElab
  | `(#spec_smoke! $p:term $s:term) => do
    let (hasStuck, msg) ← Command.liftTermElabM do
      let outs ← runSpecSmoke p none s
      return formatSmokeOutcomes m!"{p} {s}" outs
    if hasStuck then
      throwError msg
    else
      logInfo msg
  | _ => throwUnsupportedSyntax

/-- Tactic form `spec_smoke`: runs bounded symbolic execution from the current `subroutine_ok` or
    `SepWP` goal without modifying proof state, logging the smoke report via `logInfo`. -/
elab "spec_smoke" : tactic => do
  let saved ← saveState
  let startHb ← IO.getNumHeartbeats
  try
    let g0 ← getMainGoal
    let ty0 ← g0.withContext (whnfCore (← instantiateMVars (← g0.getType)))
    if ← SpecShape.isFullAppOfAny? ty0 #[``Arm64.subroutine_ok, ``Arm64.Program.subroutineOk] then
      let isSplit ← g0.withContext do
        if ← SpecShape.isFullApp? ty0 ``Arm64.subroutine_ok then
          specIsSplit (← SpecShape.namedArg! ty0 ``Arm64.subroutine_ok `spec)
        else
          Pure.pure false
      let aId := mkIdent `a
      let s0Id := mkIdent `s0
      if isSplit then
        evalTactic (← `(tactic| wp_start $aId:ident $s0Id:ident))
      else
        evalTactic (← `(tactic| wp_init $aId:ident $s0Id:ident))
    let outs ← smokeExplore startHb defaultSmokeMaxHeartbeats 64 4 #[]
    let (_, msg) := formatSmokeOutcomes m!"current goal" outs
    logInfo msg
  catch e =>
    logInfo m!"[spec_smoke] ERROR: {e.toMessageData}"
  finally
    restoreState saved

/-! ## Specification Linting and Environment Metadata -/

/-- A precondition-pinning or guard-only warning detected by inspecting the elaborated `Expr`
    of a `Spec` precondition. -/
structure SpecLintIssue where
  kind : String
  detail : MessageData
  deriving Inhabited

private def pointerFieldNames : Array String := #[
  "strm", "ptr", "buf", "version", "tif", "state", "src", "dst",
  "inp", "outp", "handle", "ctx"
]

private def lenFieldNames : Array String := #[
  "len", "length", "count", "size", "avail_in", "avail_out"
]

private def extractFieldOrVarNames (e : Expr) : MetaM (Array String) := do
  let env ← getEnv
  let lctx ← getLCtx
  let ref ← IO.mkRef (#[] : Array String)
  let pushStr (s : String) : IO Unit := do
    let arr ← ref.get
    if !s.isEmpty && !arr.contains s then
      ref.set (arr.push s)
  e.forEach fun sub => do
    match sub with
    | .proj typeName idx _ =>
      let fields := getStructureFieldsFlattened env typeName false
      if h : idx < fields.size then
        pushStr fields[idx].toString
    | .const nm _ =>
      if let .str _ s := nm then
        pushStr s
    | .fvar fvarId =>
      if let some decl := lctx.find? fvarId then
        pushStr decl.userName.toString
    | _ => Pure.pure ()
  ref.get

private def evalSmallNatOrBv? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some (_, v) ← evalBitVecLit? e then
    return some v
  if let some n := e.nat? then
    return some n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (e.getArg! 1).nat? then
      return some n
  if e.isConstOf ``Nat.zero then
    return some 0
  return none

private def isNullOrZeroExpr (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isAppOf ``Option.none then return true
  if let some 0 ← evalSmallNatOrBv? e then return true
  return false

private def isPointerOrInputExpr (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if (e.find? fun sub => sub.isAppOf ``HAdd.hAdd || sub.isAppOf ``HSub.hSub || sub.isAppOf ``HMul.hMul).isSome then
    return false
  if e.isAppOfArity ``Arm64.State.readReg64 2 || e.isAppOfArity ``Arm64.State.readReg32 2 then
    let reg := e.getArg! 1
    if reg.isConstOf ``Arm64.Reg.x0 ||
       (reg.isAppOfArity ``Arm64.Reg.gpr 1 && (reg.getArg! 0 == toExpr 0#5)) then
      return true
  let names ← extractFieldOrVarNames e
  if names.any (fun n => lenFieldNames.contains n) then
    return false
  return names.any (fun n => pointerFieldNames.contains n)

private def isLenOrCountExpr (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if (e.find? fun sub => sub.isAppOf ``HAdd.hAdd || sub.isAppOf ``HMul.hMul).isSome then
    return false
  let names ← extractFieldOrVarNames e
  return names.any (fun n => lenFieldNames.contains n)

private def isPow2OverflowBound (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isAppOfArity ``HPow.hPow 6 then
    if let (some 2, some p) := (← evalSmallNatOrBv? (e.getArg! 4), ← evalSmallNatOrBv? (e.getArg! 5)) then
      if p == 64 || p == 32 then return true
  if let some v ← evalSmallNatOrBv? e then
    if v == 2 ^ 64 || v == 2 ^ 32 then return true
  return false

private def lintPureHypExpr (g : MVarId) (ty : Expr) : MetaM (Array SpecLintIssue) := g.withContext do
  let ty ← instantiateMVars ty
  let mut issues : Array SpecLintIssue := #[]
  if let some (_, lhs, rhs) := ty.eq? then
    if lhs.isAppOf ``Arm64.State.spAligned then
      return #[]
    if (← isNullOrZeroExpr rhs) && (← isPointerOrInputExpr lhs) then
      issues := issues.push {
        kind := "input-pinned-null"
        detail := ← withGoalCtx g m!"precondition pins input to NULL/0 (`{ty}`)"
      }
    else if (← isNullOrZeroExpr lhs) && (← isPointerOrInputExpr rhs) then
      issues := issues.push {
        kind := "input-pinned-null"
        detail := ← withGoalCtx g m!"precondition pins input to NULL/0 (`{ty}`)"
      }
    else if (← isNullOrZeroExpr rhs) && (← isLenOrCountExpr lhs) then
      issues := issues.push {
        kind := "input-pinned-small-len"
        detail := ← withGoalCtx g m!"precondition restricts length/count to small/empty case (`{ty}`)"
      }
    else if (← isNullOrZeroExpr lhs) && (← isLenOrCountExpr rhs) then
      issues := issues.push {
        kind := "input-pinned-small-len"
        detail := ← withGoalCtx g m!"precondition restricts length/count to small/empty case (`{ty}`)"
      }
    else if rhs.isConstOf ``Bool.true &&
            (lhs.isAppOfArity ``BitVec.ult 3 || lhs.isAppOfArity ``BitVec.ule 3) then
      let bvLhs := lhs.getArg! 1
      let bvRhs := lhs.getArg! 2
      if let some k ← evalSmallNatOrBv? bvRhs then
        if k ≤ 16 && (← isLenOrCountExpr bvLhs) then
          issues := issues.push {
            kind := "input-pinned-small-len"
            detail := ← withGoalCtx g m!"precondition restricts length/count to small/empty case (`{ty}`)"
          }
  if ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``LE.le 4 then
    let lhs := ty.getArg! 2
    let rhs := ty.getArg! 3
    if let some k ← evalSmallNatOrBv? rhs then
      if k ≤ 16 && (← isLenOrCountExpr lhs) then
        issues := issues.push {
          kind := "input-pinned-small-len"
          detail := ← withGoalCtx g m!"precondition restricts length/count to small/empty case (`{ty}`)"
        }
    if (← isPow2OverflowBound lhs) &&
       (rhs.find? fun sub => sub.isAppOf ``HMul.hMul || sub.isAppOf ``HAdd.hAdd).isSome then
      issues := issues.push {
        kind := "input-pinned-overflow"
        detail := ← withGoalCtx g m!"precondition restricts inputs to overflow case (`{ty}`)"
      }
  if (ty.find? fun sub => sub.isAppOf ``Arm64.HookSat).isSome then
    let names ← extractFieldOrVarNames ty
    let hasZeroName := names.any fun n =>
      let nl := n.toLower
      (nl.splitOn "zero").length > 1 || (nl.splitOn "null").length > 1
    if hasZeroName then
      issues := issues.push {
        kind := "hook-fixed-zero"
        detail := ← withGoalCtx g m!"hook/callee fixed to return 0/NULL (`{ty}`)"
      }
  return issues

private def addLocalVarToGoal (g : MVarId) (name : Name) (type : Expr) : MetaM (Expr × MVarId) :=
  g.withContext do
    withLocalDeclD name type fun x => do
      let mvarNew ← mkFreshExprMVar (← g.getType)
      return (x, mvarNew.mvarId!)

private partial def collectSepAtomsUnwrapping (g : MVarId) (e : Expr) :
    TacticM (MVarId × Array Expr) := do
  let e ← g.withContext (instantiateMVars e)
  let e := e.consumeMData
  if e.isConstOf ``Arm64.SepProp.emp then
    return (g, #[])
  if e.isAppOfArity ``Arm64.SepProp.bupd 1 then
    return ← collectSepAtomsUnwrapping g (e.getArg! 0)
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    let (g1, a1) ← collectSepAtomsUnwrapping g (e.getArg! 0)
    let (g2, a2) ← collectSepAtomsUnwrapping g1 (e.getArg! 1)
    return (g2, a1 ++ a2)
  if e.isAppOfArity ``Arm64.SepProp.sepExists 2 then
    let domTy := e.getArg! 0
    let fn := (e.getArg! 1).consumeMData
    let binderName := match fn with
      | .lam nm _ _ _ => if nm.isAnonymous || nm.hasMacroScopes then `x_ex else nm
      | _ => `x_ex
    let (xExpr, g1) ← addLocalVarToGoal g binderName domTy
    let body := fn.beta #[xExpr]
    return ← collectSepAtomsUnwrapping g1 body
  if e.isAppOfArity ``ite 5 then
    let tBr := (e.getArg! 3).consumeMData
    let eBr := (e.getArg! 4).consumeMData
    if tBr.isConstOf ``Arm64.SepProp.emp then
      return ← collectSepAtomsUnwrapping g eBr
    else if eBr.isConstOf ``Arm64.SepProp.emp then
      return ← collectSepAtomsUnwrapping g tBr
  return (g, #[e])

private def unfoldAndExtractBlocks (g : MVarId) (memExpr sepExpr : Expr) :
    TacticM (MVarId × Array Expr × Array SpatialBlockInfo) := do
  let satTy := mkApp2 (mkConst ``Arm64.SepProp.Satisfies) sepExpr memExpr
  let (hSatExpr, g1) ← addLocalVarToGoal g `_h_lint_sep satTy
  let hSatId := mkIdent `_h_lint_sep
  let savedGoals ← getGoals
  setGoals [g1]
  let _ ← tryTacticQuiet (evalTactic (← `(tactic| wp_unfold_specs)))
  for _ in [:4] do
    let gCur ← getMainGoal
    let defs ← gCur.withContext do
      if let some decl := (← getLCtx).findFromUserName? `_h_lint_sep then
        collectUserSepDefs (← instantiateMVars decl.type) (includeAllocSeq := true)
      else
        Pure.pure #[]
    if defs.isEmpty then
      break
    for id in defs do
      let _ ← tryTacticQuiet (evalTactic (← `(tactic| dsimp only [$id:ident] at $hSatId:ident)))
  let _ ← tryTacticQuiet (evalTactic (← `(tactic|
    simp (config := { decide := true }) only [
      stackFrame, stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      pointsToBytes_nil, pointsToBytesRO_nil, memRegion_zero, satisfies_bupd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      emp_sepConj, sepConj_emp, Arm64.Spec.split] at $hSatId:ident)))
  let gUnfolded ← getMainGoal
  setGoals savedGoals
  let unfoldedSep ← gUnfolded.withContext do
    if let some decl := (← getLCtx).findFromUserName? `_h_lint_sep then
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``Arm64.SepProp.Satisfies 2 then
        Pure.pure (ty.getArg! 0)
      else
        Pure.pure sepExpr
    else
      Pure.pure sepExpr
  let gClean ← gUnfolded.tryClear hSatExpr.fvarId!
  let (gAtoms, atoms) ← collectSepAtomsUnwrapping gClean unfoldedSep
  let mut blocks : Array SpatialBlockInfo := #[]
  for atom in atoms do
    if !atom.isAppOfArity ``Arm64.SepProp.pure 1 then
      if let some info ← extractBlockInfo? gAtoms atom (unwrapOptIte := true) then
        blocks := blocks.push info
  return (gAtoms, atoms, blocks)

private def isSymbolicAllocCall (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  unless e.isApp do return false
  let fn := e.getAppFn.consumeMData
  if let .const nm _ := fn then
    let s := nm.toString.toLower
    return (s.splitOn "alloc").length > 1 ||
           (s.splitOn "malloc").length > 1 ||
           (s.splitOn "calloc").length > 1 ||
           (s.splitOn "realloc").length > 1 ||
           (s.splitOn "newptr").length > 1
  if fn.isFVar || fn.isProj then
    let fnTy ← whnfR (← inferType fn)
    if fnTy.isForall then
      let names ← extractFieldOrVarNames fn
      return names.any fun n =>
        let nl := n.toLower
        (nl.splitOn "alloc").length > 1 ||
        (nl.splitOn "malloc").length > 1 ||
        (nl.splitOn "calloc").length > 1 ||
        (nl.splitOn "realloc").length > 1 ||
        (nl.splitOn "ptr").length > 1 ||
        (nl.splitOn "buf").length > 1
  return false

private def isStackAnchor (anchor : Expr) : MetaM Bool := do
  let a := anchor.consumeMData
  if a.isAppOf ``Arm64.State.sp then return true
  if (a.find? fun sub => sub.isAppOf ``Arm64.State.sp).isSome then return true
  let names ← extractFieldOrVarNames a
  return names.any fun n => n == "sp" || n == "sp0"

private def splitSpecNameTokens (s : String) : List String := Id.run do
  let chars := s.toList
  let mut tokens : Array String := #[]
  let mut curr : Array Char := #[]
  for i in [:chars.length] do
    let c := chars[i]!
    if !c.isAlphanum then
      if !curr.isEmpty then
        tokens := tokens.push (String.ofList curr.toList).toLower
        curr := #[]
    else
      let prev? := if i > 0 then some chars[i - 1]! else none
      let next? := if i + 1 < chars.length then some chars[i + 1]! else none
      let isBoundary :=
        match prev? with
        | some p =>
          p.isAlphanum &&
          ((p.isLower && c.isUpper) ||
           (p.isUpper && c.isUpper && (next?.map Char.isLower).getD false))
        | none => false
      if isBoundary && !curr.isEmpty then
        tokens := tokens.push (String.ofList curr.toList).toLower
        curr := #[c]
      else
        curr := curr.push c
  if !curr.isEmpty then
    tokens := tokens.push (String.ofList curr.toList).toLower
  return tokens.toList

/-- Check whether a lowercase word token represents a `free` word (including C library prefixed
    forms like `zfree` / `widgetfree`, excluding `lockfree` / `waitfree` / `hookfree`
    and non-deallocation words like `freeze` / `freed`). -/
private def isFreeWordToken (tok : String) : Bool :=
  tok == "free" ||
  (tok.endsWith "free" && tok != "lockfree" && tok != "waitfree" && tok != "hookfree" && tok != "carefree")

private def isDeallocSpecName (nm? : Option Name) : Bool :=
  match nm? with
  | none => false
  | some nm =>
    let last := match nm with | .str _ l => l | _ => nm.toString
    let tokens := splitSpecNameTokens last
    let sLower := last.toLower
    let hasDealloc := tokens.any fun t =>
      isFreeWordToken t || t == "cleanup" || t == "close" || t == "destroy" || t == "dealloc"
    let isExcluded :=
      tokens.contains "null" || tokens.contains "zero" ||
      (sLower.splitOn "hookfree").length > 1 ||
      (sLower.splitOn "lockfree").length > 1 ||
      (sLower.splitOn "waitfree").length > 1
    hasDealloc && !isExcluded

private def isFreeSpecName (nm? : Option Name) : Bool :=
  match nm? with
  | none => false
  | some nm =>
    let last := match nm with | .str _ l => l | _ => nm.toString
    let tokens := splitSpecNameTokens last
    let sLower := last.toLower
    let hasFree := tokens.any isFreeWordToken
    let isExcluded :=
      tokens.contains "null" || tokens.contains "zero" ||
      (sLower.splitOn "hookfree").length > 1 ||
      (sLower.splitOn "lockfree").length > 1 ||
      (sLower.splitOn "waitfree").length > 1
    hasFree && !isExcluded

/-- Inspect an elaborated `Spec` expression for input-pinning or guard-only precondition constraints,
    aliased symbolic allocation pointers in `post`, and `*free*`/`*cleanup*`/`*close*` specs that
    retain freed pointer ownership in `post`. -/
def lintSpecExpr (specExpr0 : Expr) : TermElabM (Array SpecLintIssue) := do
  let specName? := specExpr0.getAppFn.constName?
  let specTy0 ← inferType specExpr0
  forallTelescopeReducing specTy0 fun params bodyTy => do
    let appSpec := mkAppN specExpr0 params
    let bodyTyWhnf ← whnfR bodyTy
    unless bodyTyWhnf.isAppOfArity ``Arm64.Spec 1 do
      return #[]
    let alpha := bodyTyWhnf.getArg! 0
    let stateTy := mkConst ``Arm64.State
    let goalType ← withLocalDeclD `a alpha fun a =>
      withLocalDeclD `s0 stateTy fun s0 =>
      withLocalDeclD `hpre (mkApp2 (mkConst ``Arm64.SepProp.Satisfies)
        (mkApp4 (mkConst ``Arm64.Spec.pre) alpha appSpec a s0)
        (mkApp (mkConst ``Arm64.State.mem) s0)) fun hpre => do
        mkForallFVars #[a, s0, hpre] (mkConst ``False)
    let mvar ← mkFreshExprMVar goalType
    let issues ← (do
      let aId := mkIdent `a
      let s0Id := mkIdent `s0
      let hpreId := mkIdent `hpre
      evalTactic (← `(tactic| (
        intro $aId:ident $s0Id:ident $hpreId:ident
        wp_unfold_specs
      )))
      let g0 ← getMainGoal
      let userSepDefs ← g0.withContext do
        if let some decl := (← getLCtx).findFromUserName? `hpre then
          collectUserSepDefs (← instantiateMVars decl.type)
        else
          Pure.pure #[]
      for id in userSepDefs do
        let _ ← tryTacticQuiet (evalTactic (← `(tactic| (
          conv at $hpreId:ident => dsimp only [$id:ident]
        ))))
      let _ ← tryTacticQuiet (evalTactic (← `(tactic| (
        simp only [
          satisfies_bupd,
          satisfies_pure_sepConj, satisfies_sepConj_pure, satisfies_sepConj_pure_assoc,
          satisfies_pure, satisfies_emp, sepConj_assoc, emp_sepConj, sepConj_emp,
          Arm64.Spec.split] at $hpreId:ident
      ))))
      -- Split `And` and `Exists` hypotheses without cross-hypothesis `simp` substitution
      let mut splitProgress := true
      while splitProgress do
        splitProgress := false
        let g ← getMainGoal
        let lctx ← g.withContext getLCtx
        for decl in lctx do
          if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
            let ty ← g.withContext (instantiateMVars decl.type)
            if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then
              let id := mkIdent decl.userName
              let h1 ← freshIdent `h_lint
              if ← tryTacticQuiet (evalTactic (← `(tactic| rcases $id:ident with ⟨$h1:ident, $id:ident⟩))) then
                splitProgress := true
                break
      let g ← getMainGoal
      let lctx ← g.withContext getLCtx
      let mut found : Array SpecLintIssue := #[]
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          let ty ← g.withContext (instantiateMVars decl.type)
          if ← g.withContext (Meta.isProp ty) then
            let newIssues ← lintPureHypExpr g ty
            for iss in newIssues do
              if !found.any (fun x => x.kind == iss.kind) then
                found := found.push iss
      let (aExpr?, s0Expr?) ← g.withContext do
        let lctx ← getLCtx
        let aE := (lctx.findFromUserName? `a).map LocalDecl.toExpr
        let s0E := (lctx.findFromUserName? `s0).map LocalDecl.toExpr
        Pure.pure (aE, s0E)
      if let (some aExpr, some s0Expr) := (aExpr?, s0Expr?) then
        let (sfExpr, g1) ← addLocalVarToGoal g `sf stateTy
        let s0Mem := mkApp (mkConst ``Arm64.State.mem) s0Expr
        let sfMem := mkApp (mkConst ``Arm64.State.mem) sfExpr
        let preSep := mkApp4 (mkConst ``Arm64.Spec.pre) alpha appSpec aExpr s0Expr
        let postSep := mkApp5 (mkConst ``Arm64.Spec.post) alpha appSpec aExpr s0Expr sfExpr
        let (gPost, postAtoms, postBlocks) ← unfoldAndExtractBlocks g1 sfMem postSep
        for h1 : i in [:postBlocks.size] do
          let b1 := postBlocks[i]
          for h2 : j in [i + 1 : postBlocks.size] do
            let b2 := postBlocks[j]
            if !b1.isReadOnly && !b2.isReadOnly then
              let sameAnchor ← gPost.withContext do
                if b1.anchor == b2.anchor then Pure.pure true
                else withReducible (isDefEq b1.anchor b2.anchor)
              if sameAnchor then
                let isOverlap : Bool := match b1.lenNat?, b2.lenNat? with
                  | some 0, _ | _, some 0 => false
                  | some n1, some n2 =>
                    let lo := max b1.offset b2.offset
                    let hi := min (b1.offset + (n1 : Int)) (b2.offset + (n2 : Int))
                    lo < hi
                  | _, _ => b1.offset == b2.offset
                if isOverlap && !found.any (fun x => x.kind == "post-aliased-alloc") then
                  found := found.push {
                    kind := "post-aliased-alloc"
                    detail := ← withGoalCtx gPost
                      m!"postcondition contains aliased/overlapping spatial blocks at `{b1.anchor}` (`{b1.atom}` and `{b2.atom}`)"
                  }
        if !found.any (fun x => x.kind == "post-aliased-alloc") then
          let mut allocCells : Array (Expr × Expr) := #[]
          for atom in postAtoms do
            if atom.isAppOfArity ``Arm64.pointsTo64 2 then
              let normVal ← normExprInGoal gPost (atom.getArg! 1)
              if ← gPost.withContext (isSymbolicAllocCall normVal) then
                for (prevAtom, prevVal) in allocCells do
                  let sameVal ← gPost.withContext do
                    if prevVal == normVal then Pure.pure true
                    else withReducible (isDefEq prevVal normVal)
                  if sameVal && !found.any (fun x => x.kind == "post-aliased-alloc") then
                    found := found.push {
                      kind := "post-aliased-alloc"
                      detail := ← withGoalCtx gPost
                        m!"postcondition aliases multiple pointer cells (`{prevAtom}` and `{atom}`) to the same symbolic allocation `{normVal}`"
                    }
                allocCells := allocCells.push (atom, normVal)
        if isDeallocSpecName specName? && !found.any (fun x => x.kind == "post-retains-freed-ptr") then
          let (gPost, _, preBlocks) ← unfoldAndExtractBlocks gPost s0Mem preSep
          let mut preHeapBlocks : Array SpatialBlockInfo := #[]
          for b in preBlocks do
            if !b.isReadOnly && !(← gPost.withContext (isStackAnchor b.anchor)) then
              preHeapBlocks := preHeapBlocks.push b
          let mut postHeapBlocks : Array SpatialBlockInfo := #[]
          for b in postBlocks do
            if !b.isReadOnly && !(← gPost.withContext (isStackAnchor b.anchor)) then
              postHeapBlocks := postHeapBlocks.push b
          if preHeapBlocks.isEmpty then
            if isFreeSpecName specName? then
              found := found.push {
                kind := "post-retains-freed-ptr"
                detail := ← withGoalCtx gPost
                  m!"deallocation spec `{specExpr0}` consumes no non-stack heap ownership in `pre`"
              }
          else
            let mut allRetained := true
            for bPre in preHeapBlocks do
              let mut retained := false
              for bPost in postHeapBlocks do
                let same ← gPost.withContext do
                  if bPre.anchor == bPost.anchor then Pure.pure true
                  else withReducible (isDefEq bPre.anchor bPost.anchor)
                if same && bPre.offset == bPost.offset then
                  retained := true
                  break
              if !retained then
                allRetained := false
                break
            if allRetained then
              found := found.push {
                kind := "post-retains-freed-ptr"
                detail := ← withGoalCtx gPost
                  m!"deallocation spec `{specExpr0}` leaves freed pointer ownership (`{preHeapBlocks[0]!.atom}`) in `post`"
              }
      return found
    ).run { elaborator := .anonymous } |>.run' { goals := [mvar.mvarId!] }
    return issues

/-- Check a `Spec` term for input-pinning or guard-only precondition constraints via `Expr` inspection. -/
def lintSpecPrecondition (specStx : Syntax) : TermElabM (Array SpecLintIssue) := do
  let specExpr0 ← Term.elabTermAndSynthesize specStx none
  lintSpecExpr specExpr0

/-- Check `<spec>`'s precondition for input-pinning (`strm = 0`, `len < 16`, overflow-only bounds,
    or zero-fixed hooks) using Lean metaprogramming. Logs via `logInfo` and never fails the build. -/
syntax (name := specLintCmd) "#spec_lint " term : command

/-- Strict variant of `#spec_lint` that throws an error if any precondition-pinning warning is found. -/
syntax (name := specLintBangCmd) "#spec_lint! " term : command

@[command_elab specLintCmd]
def elabSpecLint : Command.CommandElab
  | `(#spec_lint $spec:term) => do
    let issues ← Command.liftTermElabM do
      try
        lintSpecPrecondition spec
      catch _ =>
        return #[]
    if issues.isEmpty then
      logInfo m!"[spec_lint] OK ({spec}): no precondition-pinning warnings."
    else
      let bullets := MessageData.joinSep (issues.toList.map fun i => m!"\n  - [{i.kind}] {i.detail}") ""
      logInfo m!"[spec_lint] FLAGGED ({spec}):{bullets}"
  | _ => throwUnsupportedSyntax

@[command_elab specLintBangCmd]
def elabSpecLintBang : Command.CommandElab
  | `(#spec_lint! $spec:term) => do
    let issues ← Command.liftTermElabM (lintSpecPrecondition spec)
    if issues.isEmpty then
      logInfo m!"[spec_lint] OK ({spec}): no precondition-pinning warnings."
    else
      let bullets := MessageData.joinSep (issues.toList.map fun i => m!"\n  - [{i.kind}] {i.detail}") ""
      throwError m!"[spec_lint] FLAGGED ({spec}):{bullets}"
  | _ => throwUnsupportedSyntax

private def exprStringLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

private partial def evalStringExpr? (e : Expr) : MetaM (Option String) := do
  let e := e.consumeMData
  if let some s := exprStringLit? e then
    return some s
  if e.isAppOfArity ``HAppend.hAppend 6 then
    if let some s1 ← evalStringExpr? (e.getArg! 4) then
      if let some s2 ← evalStringExpr? (e.getArg! 5) then
        return some (s1 ++ s2)
  if e.isAppOfArity ``Append.append 4 then
    if let some s1 ← evalStringExpr? (e.getArg! 2) then
      if let some s2 ← evalStringExpr? (e.getArg! 3) then
        return some (s1 ++ s2)
  if e.isAppOfArity ``String.append 2 then
    if let some s1 ← evalStringExpr? (e.getArg! 0) then
      if let some s2 ← evalStringExpr? (e.getArg! 1) then
        return some (s1 ++ s2)
  let e' ← whnfD e
  if e' != e then
    return ← evalStringExpr? e'
  return none

private def evalFnPinExpr (e : Expr) : MetaM Arm64.FnPin := do
  let e ← whnf e
  if e.isAppOfArity ``Arm64.FnPin.off 1 then
    if let some off ← evalNatLit? (e.getArg! 0) then
      return .off off
  else if e.isAppOfArity ``Arm64.FnPin.addr 1 then
    if let some (64, a) ← evalBitVecLit? (e.getArg! 0) then
      return .addr (BitVec.ofNat 64 a)
  return .none

private partial def countListCons (e : Expr) (acc : Nat := 0) : Nat :=
  let e := e.consumeMData
  if e.isAppOfArity ``List.cons 3 then
    countListCons (e.getArg! 2) (acc + 1)
  else
    acc

private def evalFnCodeExpr? (e : Expr) : MetaM (Option (String × Nat × Arm64.FnPin)) := do
  let e ← whnf e
  if !e.isAppOfArity ``Arm64.FnCode.mk 3 then
    return none
  let some fnName ← evalStringExpr? (e.getArg! 0) | return none
  let wordsExpr := (e.getArg! 1).consumeMData
  let totalInsns ← do
    if let some words ← evalWordListExpr? wordsExpr then
      pure words.size
    else
      countListCons <$> whnf wordsExpr
  let pin ← evalFnPinExpr (e.getArg! 2)
  return some (fnName, totalInsns, pin)

private partial def collectListElems (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``List.cons 3 then
    collectListElems (e.getArg! 2) (acc.push (e.getArg! 1))
  else
    acc

private def findFnAddrSym? (e : Expr) : Option String := Id.run do
  if e.isAppOfArity ``Arm64.Program.fnAddr 2 then
    if let some s := exprStringLit? (e.getArg! 1) then
      return some s
  if let some sub := e.find? (fun sub => sub.isAppOfArity ``Arm64.Program.fnAddr 2) then
    return exprStringLit? (sub.getArg! 1)
  return none

/-- Correctness predicates recognized by `#spec_audit_env` as the conclusion of a proof theorem,
    with the binder names (in the predicate's declared type, looked up by
    `SpecShape.namedArg!`) of the entry argument and the spec / postcondition argument. -/
def specHeads : Array (Name × Name × Name) := #[
  (``Arm64.subroutine_ok, `entry_pc, `spec),
  (``Arm64.safe_subroutine_ok, `entry_pc, `spec),
  (``Arm64.raw_subroutine_ok, `entry_pc, `spec),
  (``Arm64.exit_ok, `entry_pc, `spec),
  (``ProofLib.SepWP, `s, `post),
  (``ProofLib.SepWPp, `s, `Q)]

/-- Non-spec companion conjuncts that appear alongside `subroutine_ok` inside standard statement
    wrappers (`EntrySafe`'s `safe_until_pc` half, `library_ok`'s `addr? = some a` witness,
    `NonVacuous` side-conditions, or nullable callback guards `fn ≠ 0`). -/
private partial def isValidSpecCompanion (ty : Expr) (fuel : Nat := 6) : MetaM Bool :=
  withReducible <| forallTelescopeReducing ty fun _ body => do
    let body ← whnfR body
    if (body.find? (fun s =>
        s.isAppOf ``Arm64.safe_until_pc ||
        s.isAppOf ``Arm64.safe_until ||
        s.isAppOf ``Arm64.Spec.NonVacuous ||
        s.isAppOf ``Ne ||
        s.isAppOf ``Eq ||
        s.isAppOf ``Exists)).isSome then
      return true
    if fuel == 0 || !body.getAppFn.isConst then return false
    match ← withDefault (unfoldDefinition? body) with
    | some body' => isValidSpecCompanion body' (fuel - 1)
    | none => return false

/-- Peel statement wrappers (`Program.subroutineOk`, `EntrySafe`, `EntryListSafe`, `library_ok`,
    `*Stmt` definitions, multi-entry conjunctions) until each leaf conclusion is headed by one of
    `isHead`. Throws `"unrecognized spec shape"` if a conclusion mentions a spec predicate (`isHead`)
    in a shape that cannot be decomposed to `isHead`-headed leaves. -/
partial def collectSpecConclusions (ty : Expr) (isHead : Expr → Bool) (fuel : Nat := 12) :
    MetaM (Array Expr) :=
  withReducible <| forallTelescopeReducing ty fun xs body => do
    let body ← whnfR body
    if isHead body then
      return #[← mkForallFVars xs body]
    if body.isAppOfArity ``Exists 2 then
      let predWhnf ← whnfR (body.getArg! 1)
      if predWhnf.isLambda then
        return ← withLocalDeclD predWhnf.bindingName! predWhnf.bindingDomain! fun x => do
          collectSpecConclusions
            (← mkForallFVars (xs.push x) (predWhnf.bindingBody!.instantiate1 x)) isHead fuel
    if body.isAppOfArity ``And 2 then
      let lTy ← mkForallFVars xs (body.getArg! 0)
      let rTy ← mkForallFVars xs (body.getArg! 1)
      let lOut ← collectSpecConclusions lTy isHead fuel
      let rOut ← collectSpecConclusions rTy isHead fuel
      if lOut.isEmpty && rOut.isEmpty then return #[]
      if !lOut.isEmpty && !rOut.isEmpty then return lOut ++ rOut
      if !lOut.isEmpty && (← isValidSpecCompanion rTy) then return lOut
      if !rOut.isEmpty && (← isValidSpecCompanion lTy) then return rOut
      throwError "unrecognized spec shape: conjunction with non-spec conjunct{indentExpr body}"
    if body.isAppOfArity ``Or 2 then
      let lTy ← mkForallFVars xs (body.getArg! 0)
      let rTy ← mkForallFVars xs (body.getArg! 1)
      return (← collectSpecConclusions lTy isHead fuel) ++
             (← collectSpecConclusions rTy isHead fuel)
    if fuel == 0 || !body.getAppFn.isConst then
      if (body.find? isHead).isSome then
        throwError "unrecognized spec shape: conclusion mentions a spec predicate but is not \
          headed by one{indentExpr body}"
      return #[]
    match ← withDefault (unfoldDefinition? body) with
    | some body' => collectSpecConclusions (← mkForallFVars xs body') isHead (fuel - 1)
    | none =>
      if (body.find? isHead).isSome then
        throwError "unrecognized spec shape: conclusion mentions a spec predicate but is not \
          headed by one{indentExpr body}"
      return #[]

/-- Inspect the current Lean `Environment` for all `FnCode` / `Obj.ObjectInfo` / `Obj.LinkedImage`
    definitions, `BitVec 64` address constants, `*Code_fnOff_*` theorems, `subroutine_ok` proof
    theorems, and `Spec` precondition lint warnings, and emit a single
    `SPEC_AUDIT_ENV_JSON|<json>` line via `logInfo`. -/
syntax (name := specAuditEnvCmd) "#spec_audit_env" : command

@[command_elab specAuditEnvCmd]
def elabSpecAuditEnv : Command.CommandElab
  | `(#spec_audit_env) => do
    let json ← Command.liftTermElabM do
      let env ← getEnv
      let mut allConsts : Array ConstantInfo := #[]
      for (_, ci) in env.constants.map₂ do
        allConsts := allConsts.push ci
      for h : idx in [:env.header.moduleNames.size] do
        let modName := env.header.moduleNames[idx]
        let root := modName.getRoot
        if root == `Examples || root == `Testing then
          if h2 : idx < env.header.moduleData.size then
            for ci in env.header.moduleData[idx].constants do
              allConsts := allConsts.push ci

      let mut fnCodesJson : Array Json := #[]
      let mut seenFnNames : Std.HashSet String := {}
      let mut fnCodeByConst : Std.HashMap Name String := {}
      let mut addrToFn : Std.HashMap Nat String := {}
      let mut addrDefsJson : Array Json := #[]
      let mut fnOffByConst : Std.HashMap Name String := {}

      for ci in allConsts do
        match ci with
        | .defnInfo dv =>
          if dv.type.isConstOf ``Arm64.FnCode then
            if let some (fnName, totalInsns, pin) ← evalFnCodeExpr? dv.value then
              let baseAddr? : Option Nat := match pin with
                | .addr a => some a.toNat
                | _ => none
              let codeOff? : Option Nat := match pin with
                | .off o => some o
                | _ => none
              fnCodeByConst := fnCodeByConst.insert dv.name fnName
              if let some a := baseAddr? then
                addrToFn := addrToFn.insert a fnName
              seenFnNames := seenFnNames.insert fnName
              fnCodesJson := fnCodesJson.push (Json.mkObj [
                ("const", Json.str dv.name.toString),
                ("name", Json.str fnName),
                ("total_insns", Json.num totalInsns),
                ("base_addr", match baseAddr? with | some a => Json.num a | none => Json.null),
                ("code_offset", match codeOff? with | some o => Json.num o | none => Json.null)
              ])
          else if dv.type.isConstOf ``Arm64.Obj.ObjectInfo then
            let v := dv.value.consumeMData
            if v.isAppOf ``Arm64.Obj.ObjectInfo.mk && v.getAppNumArgs ≥ 3 then
              for item in collectListElems (v.getArg! 1) do
                let item := item.consumeMData
                if item.isAppOfArity ``Prod.mk 4 then
                  if let some sym ← evalStringExpr? (item.getArg! 2) then
                    let byteLen := countListCons (item.getArg! 3)
                    if byteLen > 0 && byteLen % 4 == 0 && !seenFnNames.contains sym then
                      seenFnNames := seenFnNames.insert sym
                      let totalInsns : Nat := byteLen / 4
                      fnCodesJson := fnCodesJson.push (Json.mkObj [
                        ("const", Json.str dv.name.toString),
                        ("name", Json.str sym),
                        ("total_insns", Json.num totalInsns),
                        ("base_addr", Json.null),
                        ("code_offset", Json.null)
                      ])
              for item in collectListElems (v.getArg! 2) do
                let item := item.consumeMData
                if item.isAppOfArity ``Prod.mk 4 then
                  if let some sym ← evalStringExpr? (item.getArg! 2) then
                    let rhs := (item.getArg! 3).consumeMData
                    if rhs.isAppOfArity ``Prod.mk 4 then
                      let byteLen := countListCons (rhs.getArg! 2)
                      if byteLen > 0 && byteLen % 4 == 0 && !seenFnNames.contains sym then
                        seenFnNames := seenFnNames.insert sym
                        let totalInsns : Nat := byteLen / 4
                        fnCodesJson := fnCodesJson.push (Json.mkObj [
                          ("const", Json.str dv.name.toString),
                          ("name", Json.str sym),
                          ("total_insns", Json.num totalInsns),
                          ("base_addr", Json.null),
                          ("code_offset", Json.null)
                        ])
              if v.getAppNumArgs ≥ 4 then
                for item in collectListElems (v.getArg! 3) do
                  let item := item.consumeMData
                  if item.isAppOfArity ``Arm64.Obj.SymCodeInfo.mk 3 then
                    if let some sym ← evalStringExpr? (item.getArg! 0) then
                      let byteLen := countListCons (item.getArg! 1)
                      if byteLen > 0 && byteLen % 4 == 0 && !seenFnNames.contains sym then
                        seenFnNames := seenFnNames.insert sym
                        let totalInsns : Nat := byteLen / 4
                        fnCodesJson := fnCodesJson.push (Json.mkObj [
                          ("const", Json.str dv.name.toString),
                          ("name", Json.str sym),
                          ("total_insns", Json.num totalInsns),
                          ("base_addr", Json.null),
                          ("code_offset", Json.null)
                        ])
          else if dv.type.isConstOf ``Arm64.Obj.LinkedImage then
            let v := dv.value.consumeMData
            if v.isAppOfArity ``Arm64.Obj.LinkedImage.mk 13 then
              let codeLen := countListCons (v.getArg! 0)
              let mut stubMin : Option Nat := none
              for item in collectListElems (v.getArg! 11) do
                let item := item.consumeMData
                if item.isAppOfArity ``Prod.mk 4 then
                  if let some off ← evalNatLit? (item.getArg! 3) then
                    stubMin := match stubMin with
                      | none => some off
                      | some m => some (Nat.min m off)
              let codeEnd := stubMin.getD codeLen
              let mut codeSyms : Array (String × Nat) := #[]
              for item in collectListElems (v.getArg! 9) do
                let item := item.consumeMData
                if item.isAppOfArity ``Prod.mk 4 then
                  if let some sym ← evalStringExpr? (item.getArg! 2) then
                    if let some off ← evalNatLit? (item.getArg! 3) then
                      if off < codeEnd then
                        codeSyms := codeSyms.push (sym, off)
              let sortedSyms := codeSyms.qsort (fun a b => a.2 < b.2)
              for h : i in [:sortedSyms.size] do
                let (sym, off) := sortedSyms[i]
                if !seenFnNames.contains sym then
                  let mut nextOff := codeEnd
                  for h2 : j in [i + 1 : sortedSyms.size] do
                    let (_, o2) := sortedSyms[j]
                    if o2 > off then
                      nextOff := o2
                      break
                  let totalInsns := (nextOff - off) / 4
                  if totalInsns > 0 then
                    seenFnNames := seenFnNames.insert sym
                    fnCodesJson := fnCodesJson.push (Json.mkObj [
                      ("const", Json.str dv.name.toString),
                      ("name", Json.str sym),
                      ("total_insns", Json.num totalInsns),
                      ("base_addr", Json.null),
                      ("code_offset", Json.num off)
                    ])
          else if dv.type.isAppOfArity ``BitVec 1 then
            if let some (64, v) ← evalBitVecLit? (mkConst dv.name) then
              if let .str _ shortName := dv.name then
                addrDefsJson := addrDefsJson.push (Json.mkObj [
                  ("name", Json.str shortName),
                  ("full_name", Json.str dv.name.toString),
                  ("addr", Json.num v)
                ])
        | .thmInfo tv =>
          if let some (_, lhs, _) := tv.type.eq? then
            if lhs.isAppOfArity ``Arm64.Program.fnOff 2 then
              if let some sym := exprStringLit? (lhs.getArg! 1) then
                fnOffByConst := fnOffByConst.insert tv.name sym
        | _ => Pure.pure ()

      -- Unfold statement wrappers (`Program.subroutineOk`, `*Stmt` defs, `∀ base, ...`) until the
      -- conclusion is headed by one of `specHeads`; a conclusion that still mentions a spec head
      -- without being a full application is reported in `unrecognized` (fail closed).
      let mut thmsJson : Array Json := #[]
      let mut unrecognizedJson : Array Json := #[]
      let mut referencedSpecMods : Std.HashSet Name := {}
      for (declName, ci) in env.constants.map₂ do
        if let .thmInfo tv := ci then
          -- Compiler-generated auxiliary lemmas (`proof_1`, `_private`, ...) are inspected but never
          -- reported as unrecognized.
          let reportUnrec := !declName.isInternalDetail
          let isSpecHead (e : Expr) : Bool :=
            match e.consumeMData.getAppFn.constName? with
            | some c => specHeads.any (·.1 == c)
            | none => false
          let mut concls : Array Expr := #[]
          try
            concls ← withCurrHeartbeats (collectSpecConclusions tv.type isSpecHead)
          catch ex =>
            if reportUnrec then
              unrecognizedJson := unrecognizedJson.push (Json.mkObj [
                ("decl", Json.str declName.toString),
                ("reason", Json.str (← ex.toMessageData.toString))])
          for thmType in concls do
            let mut thmEntry? : Option (Option Name × Json) := none
            try
              thmEntry? ← withCurrHeartbeats <| withReducible (forallTelescope thmType fun xs bodyWhnf => do
                let some (headC, entryN, specN) := specHeads.find? (fun (c, _, _) =>
                    bodyWhnf.consumeMData.isAppOf c) |
                  return none
                let entryExpr ← SpecShape.namedArg! bodyWhnf headC entryN
                let specExpr ← whnfR (← SpecShape.namedArg! bodyWhnf headC specN)
                let mut fnSym? : Option String :=
                  (findFnAddrSym? entryExpr).orElse (fun _ => findFnAddrSym? thmType)
                if fnSym?.isNone then
                  if let some (64, addrVal) ← evalBitVecLit? entryExpr then
                    fnSym? := addrToFn[addrVal]?
                if fnSym?.isNone then
                  for x in xs do
                    let xTy ← whnfR (← inferType x)
                    if xTy.isAppOfArity ``Arm64.FnCode.holds 2 then
                      if let some fnC := (xTy.getArg! 0).constName? then
                        if let some s := fnCodeByConst[fnC]? then
                          fnSym? := some s
                          break
                    else if xTy.isAppOfArity ``Arm64.Program.codeAt 3 ||
                            xTy.isAppOfArity ``Arm64.Program.codeAtOff 4 ||
                            xTy.isAppOfArity ``Arm64.Program.codeAtAddr 4 then
                      if let some s := exprStringLit? (xTy.getArg! 1) then
                        fnSym? := some s
                        break
                if fnSym?.isNone then
                  for usedC in tv.value.getUsedConstants do
                    if let some s := fnOffByConst[usedC]? then
                      fnSym? := some s
                      break
                let specConstName? : Option Name :=
                  match specExpr.getAppFn.constName? with
                  | some sc =>
                    if sc == ``Arm64.Spec.mk || sc == ``Arm64.Spec.split then none
                    else some sc
                  | none => none
                let shortDecl := match declName with | .str _ s => s | _ => declName.toString
                return some (specConstName?, Json.mkObj [
                  ("decl", Json.str declName.toString),
                  ("short_decl", Json.str shortDecl),
                  ("fn", match fnSym? with | some s => Json.str s | none => Json.null),
                  ("spec", match specConstName? with | some s => Json.str s.toString | none => Json.null)
                ]))
            catch ex =>
              if reportUnrec then
                unrecognizedJson := unrecognizedJson.push (Json.mkObj [
                  ("decl", Json.str declName.toString),
                  ("reason", Json.str (← ex.toMessageData.toString))])
            if let some (specName?, je) := thmEntry? then
              thmsJson := thmsJson.push je
              if let some sc := specName? then
                if let some modIdx := env.getModuleIdxFor? sc then
                  if h : modIdx.toNat < env.header.moduleNames.size then
                    referencedSpecMods := referencedSpecMods.insert env.header.moduleNames[modIdx.toNat]

      let mut lintWarningsJson : Array Json := #[]
      let mut seenSpecs : Std.HashSet Name := {}
      let directImportNames : Array Name := env.header.imports.map (·.module)
      let mut specConsts : Array (Name × Option Name) := #[]
      for (declName, ci) in env.constants.map₂ do
        if let .defnInfo dv := ci then
          let fb := dv.type.getForallBody
          if fb.isAppOfArity ``Arm64.Spec 1 || fb.isAppOfArity ``Arm64.BaseSpec 1 then
            specConsts := specConsts.push (declName, none)
      for h : idx in [:env.header.moduleNames.size] do
        let modName := env.header.moduleNames[idx]
        let isRelevantMod :=
          directImportNames.contains modName || referencedSpecMods.contains modName
        if isRelevantMod && (modName.toString.endsWith "Spec" || modName.getRoot == `Examples || modName.getRoot == `Testing) then
          if h2 : idx < env.header.moduleData.size then
            for ci in env.header.moduleData[idx].constants do
              if let .defnInfo dv := ci then
                let fb := dv.type.getForallBody
                if fb.isAppOfArity ``Arm64.Spec 1 || fb.isAppOfArity ``Arm64.BaseSpec 1 then
                  specConsts := specConsts.push (dv.name, some modName)

      for (specName, modName?) in specConsts do
        if !seenSpecs.contains specName && !specName.isInternalDetail then
          seenSpecs := seenSpecs.insert specName
          let issues ← try
            lintSpecExpr (mkConst specName)
          catch _ =>
            Pure.pure #[]
          if !issues.isEmpty then
            let lineNum : Nat := match ← Lean.findDeclarationRanges? specName with
              | some dr => dr.range.pos.line
              | none => 0
            let shortSpec := match specName with | .str _ s => s | _ => specName.toString
            let modStr := match modName? with
              | some m => (m.toString.replace "." "/") ++ ".lean"
              | none => ""
            for iss in issues do
              let msgStr ← iss.detail.toString
              lintWarningsJson := lintWarningsJson.push (Json.mkObj [
                ("spec", Json.str shortSpec),
                ("full_spec", Json.str specName.toString),
                ("module_file", Json.str modStr),
                ("line", Json.num lineNum),
                ("kind", Json.str iss.kind),
                ("message", Json.str msgStr)
              ])

      return Json.mkObj [
        ("fncodes", Json.arr fnCodesJson),
        ("addr_defs", Json.arr addrDefsJson),
        ("theorems", Json.arr thmsJson),
        ("lint_warnings", Json.arr lintWarningsJson),
        ("unrecognized", Json.arr unrecognizedJson)
      ]
    logInfo m!"SPEC_AUDIT_ENV_JSON|{json.compress}"
    -- Fail closed: a theorem whose statement mentions a spec predicate in a shape this command
    -- does not understand is an error, not a silent omission from the coverage report.
    if let .ok (.arr unrec) := json.getObjVal? "unrecognized" then
      for u in unrec do
        let d := (u.getObjValAs? String "decl").toOption.getD "?"
        let r := (u.getObjValAs? String "reason").toOption.getD "?"
        logError m!"[spec_audit_env] {d}: {r}"
  | _ => throwUnsupportedSyntax

end SpecAudit

end

end ProofLib
