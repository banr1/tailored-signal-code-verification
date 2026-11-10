/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.BV.ArithLemmas
public import ProofLib.BV.ArithAttr
import Arm64.Trusted.Spec.SepLogic

/-!
# `bv_arith` Core: Relevance Filter and Normalization

`MetaM` utilities for `bv_arith`: closed literal evaluation, arithmetic atom collection, transitive
hypothesis relevance filtering (`relevantFilter`, `pruneDangling`), and `@[bv_arith_norm]`
hypothesis normalization (`mkNormCtx`, `normalizeHyp`).
-/

public meta section

namespace ProofLib.BV.Arith
open Lean Meta

initialize registerTraceClass `bv_arith
initialize registerTraceClass `bv_solve
initialize registerTraceClass `bv_arith.perf

/-- Time a phase of `bv_arith` (visible with `trace.profiler` / `trace.bv_arith.perf`). -/
def perf {α} (name : String) (k : MetaM α) : MetaM α :=
  withTraceNode `bv_arith.perf (fun _ => return m!"{name}") k

/-! ## Literal helpers -/

/-- Evaluate a closed `Nat` expression built from literals and `+ - * / % ^`. -/
partial def evalNat? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[.const ``Nat [], n, _]) => evalNat? n
    | (``Nat.succ, #[a]) => (· + 1) <$> evalNat? a
    | (``HAdd.hAdd, #[.const ``Nat [], _, _, _, a, b]) => (· + ·) <$> evalNat? a <*> evalNat? b
    | (``HSub.hSub, #[.const ``Nat [], _, _, _, a, b]) => (· - ·) <$> evalNat? a <*> evalNat? b
    | (``HMul.hMul, #[.const ``Nat [], _, _, _, a, b]) => (· * ·) <$> evalNat? a <*> evalNat? b
    | (``HDiv.hDiv, #[.const ``Nat [], _, _, _, a, b]) => (· / ·) <$> evalNat? a <*> evalNat? b
    | (``HMod.hMod, #[.const ``Nat [], _, _, _, a, b]) => (· % ·) <$> evalNat? a <*> evalNat? b
    | (``HPow.hPow, #[.const ``Nat [], .const ``Nat [], _, _, a, b]) => do
      let a ← evalNat? a; let b ← evalNat? b
      if b > 4096 then none else some (a ^ b)
    | _ => none

/-- `BitVec` width as a literal, if it is one. -/
def bvWidth? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``BitVec, #[w]) => return evalNat? w
  | _ => return none

/-- Value of a literal `BitVec w` term (`5#64`, `(5 : BitVec 64)`, `BitVec.ofNat 64 5`). -/
def bvLit? (e : Expr) : Option Nat :=
  match e.consumeMData.getAppFnArgs with
  | (``OfNat.ofNat, #[ty, n, _]) =>
    match ty.getAppFnArgs with
    | (``BitVec, #[w]) => do let w ← evalNat? w; let n ← evalNat? n; some (n % 2 ^ w)
    | _ => none
  | (``BitVec.ofNat, #[w, n]) => do let w ← evalNat? w; let n ← evalNat? n; some (n % 2 ^ w)
  | _ => none

/-! ## Atoms and relevance -/

/-- Heads whose arguments are looked through when collecting atoms. -/
def arithHeads : NameSet := NameSet.empty
  |>.insert ``HAdd.hAdd |>.insert ``HSub.hSub |>.insert ``HMul.hMul |>.insert ``HDiv.hDiv
  |>.insert ``HMod.hMod |>.insert ``HPow.hPow |>.insert ``Neg.neg |>.insert ``HShiftLeft.hShiftLeft
  |>.insert ``HShiftRight.hShiftRight |>.insert ``HAnd.hAnd |>.insert ``HOr.hOr
  |>.insert ``HXor.hXor |>.insert ``Complement.complement |>.insert ``HAppend.hAppend
  |>.insert ``BitVec.toNat |>.insert ``BitVec.toInt |>.insert ``BitVec.ofNat
  |>.insert ``BitVec.ofInt |>.insert ``BitVec.setWidth |>.insert ``BitVec.zeroExtend
  |>.insert ``BitVec.truncate |>.insert ``BitVec.signExtend |>.insert ``BitVec.extractLsb'
  |>.insert ``BitVec.extractLsb |>.insert ``BitVec.ult |>.insert ``BitVec.ule
  |>.insert ``BitVec.slt |>.insert ``BitVec.sle |>.insert ``BitVec.msb
  |>.insert ``BitVec.getLsbD |>.insert ``BitVec.sdiv |>.insert ``BitVec.smod
  |>.insert ``BitVec.srem |>.insert ``BitVec.rotateLeft |>.insert ``BitVec.rotateRight
  |>.insert ``BitVec.sshiftRight |>.insert ``BitVec.sshiftRight'
  |>.insert ``Nat.cast |>.insert ``Int.toNat |>.insert ``Int.natAbs |>.insert ``OfNat.ofNat
  |>.insert ``Eq |>.insert ``Ne |>.insert ``LT.lt |>.insert ``LE.le |>.insert ``GT.gt
  |>.insert ``GE.ge |>.insert ``Not |>.insert ``And |>.insert ``Or |>.insert ``Iff
  |>.insert ``decide |>.insert ``BEq.beq |>.insert ``bne |>.insert ``not |>.insert ``and
  |>.insert ``or |>.insert ``ite |>.insert ``Bool.true |>.insert ``Bool.false
  |>.insert ``Nat.succ |>.insert ``Nat.pred |>.insert ``Nat.min |>.insert ``Nat.max
  |>.insert ``Min.min |>.insert ``Max.max |>.insert ``Fin.val

/-- Collect maximal non-arithmetic, non-ground subterms of `e`. -/
partial def collectAtoms (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
  let e := e.consumeMData
  if !e.hasFVar && !e.hasMVar then acc
  else match e with
    | .fvar _ | .mvar _ => acc.insert e
    | .app .. =>
      let fn := e.getAppFn
      match fn with
      | .const n _ =>
        if arithHeads.contains n then
          e.getAppArgs.foldl (fun acc a => collectAtoms a acc) acc
        else acc.insert e
      | _ => acc.insert e
    | _ => acc.insert e

/-- Fast syntactic check whether `ty` is an arithmetic proposition usable by `bv_arith`. -/
@[expose] partial def isArithProp (ty : Expr) : MetaM Bool := do
  let ty := ty.consumeMData
  match ty.getAppFnArgs with
  | (``Not, #[p]) => isArithProp p
  | (``And, #[p, q]) => return (← isArithProp p) || (← isArithProp q)
  | (``Or, #[p, q]) | (``Iff, #[p, q]) =>
    return (← isArithProp p) && (← isArithProp q)
  | (``Eq, #[α, _, _]) | (``Ne, #[α, _, _]) => isArithType α
  | (``LT.lt, #[α, _, _, _]) | (``LE.le, #[α, _, _, _])
  | (``GT.gt, #[α, _, _, _]) | (``GE.ge, #[α, _, _, _]) => isArithType α
  | (``False, _) | (``True, _) => return true
  | _ =>
    if ty.isArrow then
      return ty.bindingBody!.isConstOf ``False && (← isArithProp ty.bindingDomain!)
    return false
where
  isArithType (α : Expr) : MetaM Bool := do
    let α := α.consumeMData
    if α.isConstOf ``Nat || α.isConstOf ``Int || α.isConstOf ``Bool then return true
    return α.isAppOfArity ``BitVec 1

/-- Keep elements of `cands` that are ground or transitively share atoms with `seed`. -/
def relevantFilter (seed : Std.HashSet Expr) (cands : Array (FVarId × Expr)) :
    Array (FVarId × Expr) := Id.run do
  let atomsOf := cands.map fun (_, ty) => collectAtoms ty {}
  let mut atoms := seed
  let mut keep := atomsOf.map (·.isEmpty)
  let mut changed := true
  while changed do
    changed := false
    for i in [:cands.size] do
      if !keep[i]! then
        let as := atomsOf[i]!
        if as.toList.any atoms.contains then
          keep := keep.set! i true
          for a in as.toList do atoms := atoms.insert a
          changed := true
  let mut out := #[]
  for i in [:cands.size] do
    if keep[i]! then out := out.push cands[i]!
  return out

private def eqSides? (ty : Expr) : Option (Expr × Expr) :=
  match ty.consumeMData.getAppFnArgs with
  | (``Eq, #[_, l, r]) => some (l.consumeMData, r.consumeMData)
  | _ => none

/-- Iteratively drop dangling equations `t = e` (or `e = t`) where `t` is an application atom
not in `seed` and occurring in no other kept hypothesis. Such equations constrain nothing (any
model of the remaining facts extends via `t := e`) and otherwise introduce extra atoms and wrap
facts in `omega`. -/
def pruneDangling (seed : Std.HashSet Expr) (hs : Array (FVarId × Expr)) :
    Array (FVarId × Expr) := Id.run do
  let atomsOf := hs.map fun (_, ty) => collectAtoms ty {}
  let mut keep := hs.map fun _ => true
  let mut changed := true
  while changed do
    changed := false
    let mut cnt : Std.HashMap Expr Nat := {}
    for i in [:hs.size] do
      if keep[i]! then
        for a in atomsOf[i]!.toList do cnt := cnt.insert a (cnt.getD a 0 + 1)
    for i in [:hs.size] do
      if !keep[i]! then continue
      let some (l, r) := eqSides? hs[i]!.2 | continue
      let dangles (t : Expr) : Bool :=
        t.isApp && !seed.contains t && atomsOf[i]!.contains t && cnt.getD t 0 == 1 &&
          !(collectAtoms (if t == l then r else l) {}).contains t
      if dangles l || dangles r then
        keep := keep.set! i false
        for a in atomsOf[i]!.toList do cnt := cnt.insert a (cnt.getD a 1 - 1)
        changed := true
  let mut out := #[]
  for i in [:hs.size] do
    if keep[i]! then out := out.push hs[i]!
  return out

/-- `BitVec`-valued operations that emit node facts with modular wrapping (`% 2^w`, `Int.emod`,
or bit-blasting bounds). Excludes `BitVec.ofNat` and literals. -/
def bvNodeHeads : NameSet := NameSet.empty
  |>.insert ``HAdd.hAdd |>.insert ``HSub.hSub |>.insert ``HMul.hMul |>.insert ``HDiv.hDiv
  |>.insert ``HMod.hMod |>.insert ``Neg.neg |>.insert ``HShiftLeft.hShiftLeft
  |>.insert ``HShiftRight.hShiftRight |>.insert ``HAnd.hAnd |>.insert ``HOr.hOr
  |>.insert ``HXor.hXor |>.insert ``Complement.complement |>.insert ``HAppend.hAppend
  |>.insert ``BitVec.setWidth |>.insert ``BitVec.zeroExtend |>.insert ``BitVec.truncate
  |>.insert ``BitVec.signExtend |>.insert ``BitVec.extractLsb' |>.insert ``BitVec.extractLsb
  |>.insert ``BitVec.sdiv |>.insert ``BitVec.smod |>.insert ``BitVec.srem
  |>.insert ``BitVec.rotateLeft |>.insert ``BitVec.rotateRight |>.insert ``BitVec.sshiftRight
  |>.insert ``BitVec.sshiftRight'

/-- Syntactic check that `ty` contains no `BitVec` arithmetic node from `bvNodeHeads`, so adding
it introduces no modular-wrapping case splits in `omega`. -/
def bvNodeFree (ty : Expr) : Bool :=
  (ty.find? fun e =>
    match e.getAppFn with
    | .const n _ =>
      bvNodeHeads.contains n && e.getAppNumArgs > 0 &&
        (e.getAppArgs[0]!.isAppOfArity ``BitVec 1 ||
          -- `BitVec.*` functions take the width first; their result is a `BitVec`
          n.getPrefix == `BitVec)
    | _ => false).isNone

/-- All arithmetic-shaped local hypotheses (instantiated types), excluding `exclude`. -/
def arithHyps (exclude : Option FVarId := none) : MetaM (Array (FVarId × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if some d.fvarId == exclude then continue
    let ty ← instantiateMVars d.type
    if ← isArithProp ty then
      out := out.push (d.fvarId, ty)
    else
      let ty' ← whnfR ty
      if ty' != ty && (← isArithProp ty') then out := out.push (d.fvarId, ty)
  return out

/-! ## Normalization simp set -/

attribute [bv_arith_norm] norm_ult_true norm_ule_true norm_ult_false norm_ule_false
  norm_slt_true norm_sle_true norm_slt_false norm_sle_false norm_bv_eq norm_bv_lt norm_bv_le
  norm_beq_true norm_beq_false norm_bne_true norm_bne_false norm_decide_true norm_decide_false
  norm_not_true norm_not_false norm_and_true norm_and_false norm_or_true norm_or_false
  norm_ne_true norm_ne_false norm_true_eq norm_false_eq ne_eq ge_iff_le gt_iff_lt Nat.not_lt
  Nat.not_le Int.not_lt Int.not_le Classical.not_not BitVec.zeroExtend_eq_setWidth
  BitVec.truncate_eq_setWidth

/-- Simp context for hypothesis normalization built from the persistent `bv_arith_norm` extension. -/
def mkNormCtx : MetaM Simp.Context := do
  let some ext ← getSimpExtension? `bv_arith_norm | throwError "bv_arith: simp set missing"
  let thms ← ext.getTheorems
  let cfg : Simp.Config := { zeta := false, proj := false, decide := false, arith := false,
                             iota := false, zetaDelta := false }
  Simp.mkContext (config := cfg)
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- Replace reducible abbreviations `BitVec.zeroExtend` and `BitVec.truncate` with
`BitVec.setWidth` (definitionally equal; `simp` discrimination trees unfold reducible heads on
lemma LHSs, so `zeroExtend_eq_setWidth` alone makes no progress). -/
partial def unfoldWidthAbbrevs (e : Expr) : Expr :=
  e.replace fun t =>
    if t.isAppOfArity ``BitVec.zeroExtend 3 || t.isAppOfArity ``BitVec.truncate 3 then
      let args := t.getAppArgs
      some (mkAppN (mkConst ``BitVec.setWidth) (args.map unfoldWidthAbbrevs))
    else none

/-- Normalize `h : ty`; returns `none` if it simplifies to `True`. -/
def normalizeHyp (ctx : Simp.Context) (h : Expr) (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let (r, _) ← simp ty ctx
  if r.expr.isTrue then return none
  let h ← match r.proof? with
    | none => pure h
    | some pf => mkEqMP pf h
  let ty' := unfoldWidthAbbrevs r.expr
  if r.proof?.isNone && ty' == ty then return some (h, ty)
  return some (mkExpectedPropHint h ty', ty')

end ProofLib.BV.Arith
