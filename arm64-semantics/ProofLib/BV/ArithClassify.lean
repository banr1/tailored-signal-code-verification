/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.ArithCore
import Arm64.Trusted.Spec.SepLogic

/-!
# Goal Classifier and Concrete Evaluator for `bv_solve` and `decideProp?`

Syntactic feature scanner (`scanFeatures`, `classify`) selecting a solver for `bv_solve`, and
concrete model search (`eval`, `evalVerdict`) filtering unprovable branch and audit queries in
`decideProp?`. Neither constructs proof terms directly, so heuristic imprecision affects only
completeness, never soundness.
-/

public meta section

namespace ProofLib.BV.Arith
open Lean Meta

inductive GoalClass where
  | ground | linearEq | linearArith | bitwise | symbolicShift | unsupported
  deriving BEq, Repr, Inhabited

instance : ToString GoalClass where
  toString
    | .ground => "ground" | .linearEq => "linearEq" | .linearArith => "linearArith"
    | .bitwise => "bitwise" | .symbolicShift => "symbolicShift" | .unsupported => "unsupported"

structure Features where
  hasAtoms := false
  symShift := false
  /-- Bit-level structure outside the `omega` translation: xor, general `&&&`/`|||`, `++`, `~~~`,
  `msb`/`getLsbD`/`x[i]`, signed ops, and any other `BitVec.*` function
  (`clz`, `reverse`, ...). -/
  bitwise := false
  nonlinear := false      -- `x * y`, `x / y`, `x % y` with both sides non-literal
  /-- `Nat`/`Int` atoms not of the form `t.toNat` (and not just the argument of `BitVec.ofNat`). -/
  natIntAtoms := false
  nonLinOps := false      -- ops outside `bv_lin`'s fragment (anything but + - neg *c <<<c ofNat)
  /-- `t.toNat` / `t.toInt` of a non-literal `t`: `Nat`/`Int`-level reasoning, which `bv_decide`
  handles poorly (it often abstracts such facts and reports spurious counterexamples). -/
  toNat := false
  deriving Inhabited

def isLitNat (e : Expr) : Bool := (evalNat? e).isSome || (bvLit? e).isSome

partial def scanFeatures (e : Expr) (f : Features) : MetaM Features := do
  let e := e.consumeMData
  if !e.hasFVar && !e.hasMVar then return f
  let fn := e.getAppFn
  let args := e.getAppArgs
  let some n := fn.constName? |
    return { f with hasAtoms := true, natIntAtoms := f.natIntAtoms || (← isNatInt e) }
  if !arithHeads.contains n then
    -- `x[i]` on a `BitVec`, any other `BitVec.*` operation: bit-level structure
    if n == ``GetElem.getElem && args.size > 0 && args[0]!.isAppOfArity ``BitVec 1 then
      return { f with hasAtoms := true, bitwise := true, nonLinOps := true,
                      natIntAtoms := f.natIntAtoms || !(args.getD 6 (mkNatLit 0)).isFVar }
    if (`BitVec).isPrefixOf n && (← isBV e) then
      return (← args.foldlM (fun f a => scanFeatures a f)
        { f with hasAtoms := true, bitwise := true, nonLinOps := true })
    return { f with hasAtoms := true, natIntAtoms := f.natIntAtoms || (← isNatInt e) }
  let mut f := f
  match n, args with
  | ``HShiftLeft.hShiftLeft, #[_, _, _, _, _, s] | ``HShiftRight.hShiftRight, #[_, _, _, _, _, s] =>
    if !isLitNat s then f := { f with symShift := true }
  | ``BitVec.rotateLeft, #[_, _, s] | ``BitVec.rotateRight, #[_, _, s]
  | ``BitVec.sshiftRight, #[_, _, s] =>
    f := { f with bitwise := true, nonLinOps := true, symShift := f.symShift || !isLitNat s }
  | ``BitVec.sshiftRight', _ => f := { f with symShift := true }
  | ``HMul.hMul, #[_, _, _, _, a, b] | ``HDiv.hDiv, #[_, _, _, _, a, b]
  | ``HMod.hMod, #[_, _, _, _, a, b] =>
    if !isLitNat a && !isLitNat b then f := { f with nonlinear := true }
    if n != ``HMul.hMul then f := { f with nonLinOps := true }
  | ``HAnd.hAnd, #[_, _, _, _, a, b] =>
    f := { f with nonLinOps := true, bitwise := f.bitwise || !(isMask a || isMask b) }
  | ``HOr.hOr, _ | ``HXor.hXor, _ | ``HAppend.hAppend, _ | ``BitVec.signExtend, _
  | ``BitVec.sdiv, _ | ``BitVec.srem, _ | ``BitVec.smod, _ | ``BitVec.getLsbD, _
  | ``BitVec.msb, _ | ``BitVec.extractLsb, _ | ``Complement.complement, _ =>
    f := { f with bitwise := true, nonLinOps := true }
  | ``ite, #[α, _, _, _, _] =>
    -- `bv_arith` translates `ite` over `BitVec` as a case split
    if (← whnfR α).isAppOfArity ``BitVec 1 then f := { f with nonLinOps := true }
  | ``BitVec.ofNat, #[_, x] =>
    -- `BitVec.ofNat w n` with `n` an opaque `Nat` atom is itself just a `BitVec` atom
    if x.consumeMData.isFVar || !(arithHeads.contains (x.getAppFn.constName?.getD .anonymous)) then
      return { f with hasAtoms := f.hasAtoms || x.hasFVar || x.hasMVar }
  | ``BitVec.setWidth, _ | ``BitVec.zeroExtend, _ | ``BitVec.truncate, _
  | ``BitVec.extractLsb', _ | ``BitVec.ult, _ | ``BitVec.ule, _ | ``BitVec.slt, _
  | ``BitVec.sle, _ | ``LT.lt, _ | ``LE.le, _ | ``GT.gt, _ | ``GE.ge, _ =>
    f := { f with nonLinOps := true }
  | ``BitVec.toNat, #[_, a] | ``BitVec.toInt, #[_, a] =>
    f := { f with nonLinOps := true, toNat := f.toNat || a.hasFVar || a.hasMVar }
  | _, _ => pure ()
  for a in args do f ← scanFeatures a f
  return f
where
  isNatInt (e : Expr) : MetaM Bool := do
    let ty ← whnfR (← inferType e)
    return ty.isConstOf ``Nat || ty.isConstOf ``Int
  isBV (e : Expr) : MetaM Bool := do
    try return (← whnfR (← inferType e)).isAppOfArity ``BitVec 1 catch _ => return false
  /-- `2^n - 1` or a contiguous run `(2^k - 1) * 2^lo` (both have exact `bv_arith` node facts). -/
  isMask (e : Expr) : Bool := match bvLit? e with
    | some m =>
      let r := if m == 0 then 0 else m / 2 ^ (Nat.log2 (m &&& (2 ^ (Nat.log2 m + 1) - m)))
      2 ^ Nat.log2 (r + 1) == r + 1
    | none => false

/-- Is `p` a `BitVec` (dis)equality? -/
def isBVEqGoal (p : Expr) : MetaM Bool := do
  let p := p.consumeMData
  let p := if p.isAppOfArity ``Not 1 then p.appArg! else p
  match p.getAppFnArgs with
  | (``Eq, #[α, _, _]) | (``Ne, #[α, _, _]) => return (← whnfR α).isAppOfArity ``BitVec 1
  | _ => return false

/-! ## Concrete evaluator -/

inductive Val where
  | bv (w n : Nat) | nat (n : Nat) | int (i : Int) | bool (b : Bool)
  deriving BEq, Inhabited

def Val.toNat? : Val → Option Nat
  | .nat n => some n | .bv _ n => some n | _ => none

def toIntW (w n : Nat) : Int := if 2 * n < 2 ^ w then n else (n : Int) - 2 ^ w

def asBV : Option Val → Option (Nat × Nat) | some (.bv w n) => some (w, n) | _ => none
def asBool : Option Val → Option Bool | some (.bool b) => some b | _ => none
def asNat : Option Val → Option Nat | some (.nat n) => some n | _ => none

/-- A `BitVec` literal with its width. -/
def bvLitW? (e : Expr) : Option (Nat × Nat) :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[ty, _, _]) => match ty.getAppFnArgs with
    | (``BitVec, #[w]) => do return (← evalNat? w, ← bvLit? e)
    | _ => none
  | (``BitVec.ofNat, #[w, _]) => do return (← evalNat? w, ← bvLit? e)
  | _ => none

partial def eval (asg : Std.HashMap Expr Val) (e : Expr) : Option Val := do
  let e := e.consumeMData
  if let some v := asg[e]? then return v
  if let some (w, n) := bvLitW? e then return .bv w n
  let args := e.getAppArgs
  let ev := eval asg
  let bool2 (f : Bool → Bool → Bool) (a b : Expr) : Option Val := do
    let x ← asBool (ev a); let y ← asBool (ev b); return .bool (f x y)
  match e.getAppFn.constName?.getD .anonymous, args with
  | ``True, _ => return .bool true
  | ``False, _ => return .bool false
  | ``Bool.true, _ => return .bool true
  | ``Bool.false, _ => return .bool false
  | ``OfNat.ofNat, #[ty, n, _] =>
    let n ← evalNat? n
    if ty.isConstOf ``Nat then return .nat n
    if ty.isConstOf ``Int then return .int n
    none
  | ``Not, #[a] | ``not, #[a] => let x ← asBool (ev a); return .bool !x
  | ``And, #[a, b] | ``and, #[a, b] => bool2 (· && ·) a b
  | ``Or, #[a, b] | ``or, #[a, b] => bool2 (· || ·) a b
  | ``Iff, #[a, b] => bool2 (· == ·) a b
  | ``decide, #[p, _] => ev p
  | ``Eq, #[_, a, b] | ``BEq.beq, #[_, _, a, b] => return .bool ((← ev a) == (← ev b))
  | ``Ne, #[_, a, b] | ``bne, #[_, _, a, b] => return .bool ((← ev a) != (← ev b))
  | ``LT.lt, #[_, _, a, b] => cmp (· < ·) (· < ·) (← ev a) (← ev b)
  | ``LE.le, #[_, _, a, b] => cmp (· ≤ ·) (· ≤ ·) (← ev a) (← ev b)
  | ``GT.gt, #[_, _, a, b] => cmp (· < ·) (· < ·) (← ev b) (← ev a)
  | ``GE.ge, #[_, _, a, b] => cmp (· ≤ ·) (· ≤ ·) (← ev b) (← ev a)
  | ``BitVec.ult, #[_, a, b] => cmp (· < ·) (· < ·) (← ev a) (← ev b)
  | ``BitVec.ule, #[_, a, b] => cmp (· ≤ ·) (· ≤ ·) (← ev a) (← ev b)
  | ``BitVec.slt, #[_, a, b] => do
    let (w, x) ← asBV (ev a); let (_, y) ← asBV (ev b); return .bool (toIntW w x < toIntW w y)
  | ``BitVec.sle, #[_, a, b] => do
    let (w, x) ← asBV (ev a); let (_, y) ← asBV (ev b); return .bool (toIntW w x ≤ toIntW w y)
  | ``BitVec.toNat, #[_, a] => let (_, x) ← asBV (ev a); return .nat x
  | ``BitVec.toInt, #[_, a] => let (w, x) ← asBV (ev a); return .int (toIntW w x)
  | ``BitVec.ofNat, #[w, n] =>
    let w ← evalNat? w; let n ← (← ev n).toNat?; return .bv w (n % 2 ^ w)
  | ``BitVec.setWidth, #[_, v, a] | ``BitVec.zeroExtend, #[_, v, a] | ``BitVec.truncate, #[_, v, a] =>
    let v ← evalNat? v; let (_, x) ← asBV (ev a); return .bv v (x % 2 ^ v)
  | ``BitVec.extractLsb', #[_, s, m, a] =>
    let s ← evalNat? s; let m ← evalNat? m; let (_, x) ← asBV (ev a)
    return .bv m ((x / 2 ^ s) % 2 ^ m)
  | ``Nat.cast, #[r, _, a] =>
    -- the target type matters: `((n : Nat) : BitVec w)` wraps, `((n : Nat) : Int)` does not
    let n ← (← ev a).toNat?
    if r.consumeMData.isConstOf ``Int then return .int n
    if r.consumeMData.isConstOf ``Nat then return .nat n
    match r.consumeMData.getAppFnArgs with
    | (``BitVec, #[w]) => let w ← evalNat? w; return .bv w (n % 2 ^ w)
    | _ => none
  | ``HPow.hPow, #[_, _, _, _, a, b] =>
    let x ← asNat (ev a); let y ← asNat (ev b)
    if y > 4096 then none else return .nat (x ^ y)
  | ``Neg.neg, #[_, _, a] => match ← ev a with
    | .bv w x => return .bv w ((2 ^ w - x) % 2 ^ w)
    | .int i => return .int (-i)
    | _ => none
  | ``Complement.complement, #[_, _, a] => let (w, x) ← asBV (ev a); return .bv w (2 ^ w - 1 - x)
  | ``HAdd.hAdd, #[_, _, _, _, a, b] => arith (· + ·) (· + ·) (← ev a) (← ev b)
  | ``HSub.hSub, #[_, _, _, _, a, b] => match ← ev a, ← ev b with
    | .bv w x, .bv _ y => return .bv w ((x + 2 ^ w - y) % 2 ^ w)
    | .nat x, .nat y => return .nat (x - y)
    | .int x, .int y => return .int (x - y)
    | _, _ => none
  | ``HMul.hMul, #[_, _, _, _, a, b] => arith (· * ·) (· * ·) (← ev a) (← ev b)
  | ``HDiv.hDiv, #[_, _, _, _, a, b] => arith (· / ·) (· / ·) (← ev a) (← ev b)
  | ``HMod.hMod, #[_, _, _, _, a, b] => arith (· % ·) (· % ·) (← ev a) (← ev b)
  | ``HAnd.hAnd, #[_, _, _, _, a, b] => bits (· &&& ·) (← ev a) (← ev b)
  | ``HOr.hOr, #[_, _, _, _, a, b] => bits (· ||| ·) (← ev a) (← ev b)
  | ``HXor.hXor, #[_, _, _, _, a, b] => bits (· ^^^ ·) (← ev a) (← ev b)
  | ``HShiftLeft.hShiftLeft, #[_, _, _, _, a, s] =>
    let (w, x) ← asBV (ev a); let s ← (← ev s).toNat?
    return .bv w (if s ≥ w then 0 else (x <<< s) % 2 ^ w)
  | ``HShiftRight.hShiftRight, #[_, _, _, _, a, s] =>
    let (w, x) ← asBV (ev a); let s ← (← ev s).toNat?
    return .bv w (if s ≥ w then 0 else x >>> s)
  | ``Int.ofNat, #[a] => let n ← (← ev a).toNat?; return .int n
  | ``Int.toNat, #[a] => match ← ev a with | .int i => return .nat i.toNat | _ => none
  | ``Int.natAbs, #[a] => match ← ev a with | .int i => return .nat i.natAbs | _ => none
  | ``BitVec.ofInt, #[w, a] => match ← ev a with
    | .int i => let w ← evalNat? w; return .bv w (i % (2 ^ w : Nat)).toNat
    | _ => none
  | ``BitVec.getLsbD, #[_, a, i] =>
    let (_, x) ← asBV (ev a); let i ← (← ev i).toNat?; return .bool (x.testBit i)
  | ``BitVec.getMsbD, #[w, a, i] =>
    let w ← evalNat? w; let (_, x) ← asBV (ev a); let i ← (← ev i).toNat?
    return .bool (decide (i < w) && x.testBit (w - 1 - i))
  | ``BitVec.msb, #[_, a] =>
    let (w, x) ← asBV (ev a); return .bool (decide (0 < w) && x.testBit (w - 1))
  | ``GetElem.getElem, #[c, _, _, _, _, a, i, _] =>
    -- `x[i]` on a `BitVec` (`i < w` is guaranteed by the proof argument)
    if !c.consumeMData.isAppOfArity ``BitVec 1 then none
    let (_, x) ← asBV (ev a); let i ← (← ev i).toNat?; return .bool (x.testBit i)
  | ``BitVec.signExtend, #[_, v, a] =>
    let v ← evalNat? v; let (w, x) ← asBV (ev a)
    return .bv v ((toIntW w x) % (2 ^ v : Nat)).toNat
  | ``BitVec.extractLsb, #[_, hi, lo, a] =>
    let hi ← evalNat? hi; let lo ← evalNat? lo; let (_, x) ← asBV (ev a)
    let m := hi - lo + 1
    return .bv m ((x / 2 ^ lo) % 2 ^ m)
  | ``HAppend.hAppend, #[_, _, _, _, a, b] =>
    let (w, x) ← asBV (ev a); let (v, y) ← asBV (ev b); return .bv (w + v) (x * 2 ^ v + y)
  | ``BitVec.rotateLeft, #[_, a, s] =>
    let (w, x) ← asBV (ev a); let s ← (← ev s).toNat?
    if w == 0 then return .bv 0 0
    let r := s % w
    return .bv w (((x <<< r) ||| (x >>> (w - r))) % 2 ^ w)
  | ``BitVec.rotateRight, #[_, a, s] =>
    let (w, x) ← asBV (ev a); let s ← (← ev s).toNat?
    if w == 0 then return .bv 0 0
    let r := s % w
    return .bv w (((x >>> r) ||| (x <<< (w - r))) % 2 ^ w)
  | ``BitVec.sshiftRight, #[_, a, s] =>
    let (w, x) ← asBV (ev a); let s ← (← ev s).toNat?
    return .bv w ((toIntW w x / ((2 ^ min s w : Nat) : Int)) % (2 ^ w : Nat)).toNat
  | ``BitVec.sshiftRight', #[_, _, a, s] =>
    let (w, x) ← asBV (ev a); let (_, s) ← asBV (ev s)
    return .bv w ((toIntW w x / ((2 ^ min s w : Nat) : Int)) % (2 ^ w : Nat)).toNat
  | ``BitVec.udiv, #[_, a, b] =>
    let (w, x) ← asBV (ev a); let (_, y) ← asBV (ev b); return .bv w (x / y)
  | ``BitVec.umod, #[_, a, b] =>
    let (w, x) ← asBV (ev a); let (_, y) ← asBV (ev b); return .bv w (x % y)
  | ``Bool.xor, #[a, b] => bool2 (· != ·) a b
  | ``ite, #[_, c, _, t, f] => let b ← asBool (ev c); if b then ev t else ev f
  | ``cond, #[_, c, t, f] => let b ← asBool (ev c); if b then ev t else ev f
  | ``Nat.succ, #[a] => let n ← asNat (ev a); return .nat (n + 1)
  | ``Nat.pred, #[a] => let n ← asNat (ev a); return .nat (n - 1)
  | ``Nat.min, #[a, b] => let x ← asNat (ev a); let y ← asNat (ev b); return .nat (min x y)
  | ``Nat.max, #[a, b] => let x ← asNat (ev a); let y ← asNat (ev b); return .nat (max x y)
  | ``Min.min, #[ty, _, a, b] | ``Max.max, #[ty, _, a, b] =>
    -- only `Nat`/`Int` (the `BitVec` instances are not needed and easy to get wrong)
    let isMin := e.getAppFn.constName? == some ``Min.min
    if ty.consumeMData.isConstOf ``Nat then
      let x ← asNat (ev a); let y ← asNat (ev b); return .nat (if isMin then min x y else max x y)
    if ty.consumeMData.isConstOf ``Int then match ← ev a, ← ev b with
      | .int x, .int y => return .int (if isMin then min x y else max x y)
      | _, _ => none
    none
  | _, _ => if let some n := evalNat? e then return .nat n else none
where
  cmp (fn : Nat → Nat → Bool) (fi : Int → Int → Bool) : Val → Val → Option Val
    | .nat x, .nat y | .bv _ x, .bv _ y => some (.bool (fn x y))
    | .int x, .int y => some (.bool (fi x y))
    | _, _ => none
  arith (fn : Nat → Nat → Nat) (fi : Int → Int → Int) : Val → Val → Option Val
    | .nat x, .nat y => some (.nat (fn x y))
    | .bv w x, .bv _ y => some (.bv w (fn x y % 2 ^ w))
    | .int x, .int y => some (.int (fi x y))
    | _, _ => none
  bits (fn : Nat → Nat → Nat) : Val → Val → Option Val
    | .bv w x, .bv _ y => some (.bv w (fn x y % 2 ^ w))
    | .nat x, .nat y => some (.nat (fn x y))
    | _, _ => none

/-- A closed proposition that evaluates to `False` (e.g. `1#64 = 0#64`): as a goal, only a
contradiction among the hypotheses can close it, exactly like `False`. -/
def isFalseGround (p : Expr) : Bool :=
  !p.hasFVar && !p.hasMVar && eval {} p == some (.bool false)

/-- Classify goal `p` given its relevant hypothesis types.

* no atoms anywhere: `ground`;
* symbolic `x * y`, `x / y`, `x % y` in the goal: `unsupported` (outside `omega`, and
  bit-blasting a 64-bit multiplier is hopeless: `(a+b)*(a-b) = a*a-b*b` takes >10s in
  `bv_decide`); in hypotheses they are just `omega` atoms;
* opaque goal (`False`, a closed false proposition, or a non-arithmetic `Prop`, so the hypotheses
  must be contradictory): `Nat`/`Int` atoms, symbolic `*`/`/`/`%` or `t.toNat`/`t.toInt` in the
  hypotheses gives `linearArith`, else bit-level structure in the
  hypotheses gives `bitwise`/`symbolicShift`, else `linearArith`;
* bit-level goal: `bitwise`/`symbolicShift`, or `linearArith` if it has `Nat`/`Int` atoms;
* arithmetic goal with bit-level relevant hypotheses and none of the `omega`-only features above:
  `bitwise`;
* else `linearEq` (a hypothesis-free `BitVec` `=`/`≠` in `bv_lin`'s fragment) or `linearArith`.
-/
def classify (p : Expr) (hyps : Array Expr) : MetaM GoalClass := do
  let opaq := p.consumeMData.isFalse || !(← isArithProp p) || isFalseGround p
  let fg ← if opaq then pure {} else scanFeatures p {}
  let mut fh : Features := {}
  for h in hyps do fh ← scanFeatures h fh
  if !fg.hasAtoms && !fh.hasAtoms then return .ground
  -- a symbolic product in the goal itself is hopeless for both solvers
  if fg.nonlinear then return .unsupported
  -- symbolic `*`/`/`/`%` in hypotheses: `omega` treats them as atoms, `bv_decide` cannot
  let natInt := fg.natIntAtoms || fh.natIntAtoms || fh.nonlinear || fh.toNat
  let bitClass (sym : Bool) : GoalClass := if sym then .symbolicShift else .bitwise
  if opaq then
    if natInt then return .linearArith
    if fh.bitwise || fh.symShift then return bitClass fh.symShift
    return .linearArith
  if fg.bitwise || fg.symShift then
    return if fg.natIntAtoms then .linearArith else bitClass fg.symShift
  -- arithmetic goal: bit-level structure in relevant hypotheses needs `bv_decide`, unless
  -- `Nat`/`Int` atoms (which only `omega` understands) occur
  if (fh.bitwise || fh.symShift) && !natInt then return bitClass fh.symShift
  if !fg.nonLinOps && hyps.isEmpty && (← isBVEqGoal p) then return .linearEq
  return .linearArith

inductive Verdict where
  /-- Satisfying vectors disagree: neither `p` nor `¬p` follows from the hypotheses. -/
  | undetermined
  /-- All satisfying vectors agree on this value (no proof; a hint for which side to try). -/
  | likely (b : Bool)
  /-- No satisfying vector found, or some term could not be evaluated. -/
  | unknown
  deriving BEq, Inhabited

/-- Numerals (`Nat` literals and `BitVec` literal values) occurring in `e`. -/
partial def literalsIn (e : Expr) (acc : Array Nat) : Array Nat :=
  if acc.size > 16 then acc else
  match bvLit? e with
  | some n => acc.push n
  | none => match evalNat? e with
    | some n => acc.push n
    | none => match e with
      | .app f a => literalsIn a (literalsIn f acc)
      | .mdata _ b => literalsIn b acc
      | _ => acc

/-- Candidate values for an atom of type `ty`; `lits` are numerals from the problem (each
`k` contributes `k-1, k, k+1`, so `x = 5`-style conditions are hit). -/
def candidates (ty : Expr) (lits : Array Nat := #[]) : MetaM (Option (Array Val)) := do
  let extra := lits.foldl (fun acc k => acc ++ #[k, k + 1, k - 1]) #[]
  let ty ← whnfR ty
  if ty.isConstOf ``Nat then
    return some ((#[0, 1, 2, 3, 7, 8, 15, 16, 100, 255, 4096, 2 ^ 32, 2 ^ 63, 123456789] ++ extra).map .nat)
  if ty.isConstOf ``Int then
    return some ((#[0, 1, -1, 7, -8, 100, -4096, 2 ^ 40] ++ extra.map Int.ofNat).map .int)
  if ty.isConstOf ``Bool then return some #[.bool false, .bool true]
  if ty.isProp then return some #[.bool false, .bool true]
  if let some w := (← bvWidth? ty) then
    let m := 2 ^ w
    let pows := #[8, 16, 32, 63].foldl (fun acc k => acc ++ #[2 ^ k - 1, 2 ^ k, 2 ^ k + 1]) #[]
    let vs := #[0, 1, 2, 7, 8, 16, 255, 4096, 2 ^ (w / 2) + 5, m / 2, m / 2 - 1, m - 1, m - 8,
      m - 16, 0x1234567 % m, 0xdead_beef_0000 % m] ++ pows ++ extra
    return some (vs.map (.bv w <| · % m))
  return none

/-! ## Model search for `evalVerdict`

A *model* is a total assignment of the atoms (maximal subterms the evaluator does not look
through) under which every hypothesis evaluates to `true`. Models are built per round by
propagation instead of pure guessing: equations `t = e` (and bounds `t < e`, ...) whose one side
evaluates are *solved* for the other side by inverting the evaluator's operations
(`solveFor`), iterated to a fixpoint; when stuck, one unassigned atom gets a structured or
random value. Every candidate is then re-checked by plain evaluation of all hypotheses and the
goal, so the search heuristics only affect completeness, never the meaning of a found model. -/

namespace Model

/-- Heads `eval` interprets but `collectAtoms` treats as atoms: looked through here so that e.g.
`x[3]` and `x` are not independent. -/
def evalHeads : NameSet := NameSet.empty
  |>.insert ``GetElem.getElem |>.insert ``BitVec.getMsbD |>.insert ``BitVec.udiv
  |>.insert ``BitVec.umod |>.insert ``Bool.xor |>.insert ``cond |>.insert ``Int.ofNat
  |>.insert ``True |>.insert ``False

/-- An instance argument such as `instDecidableEqBitVec x y`: not a value, never an atom. -/
def isInstArg (e : Expr) : Bool := match e.consumeMData.getAppFn with
  | .const n _ => match n with
    | .str _ s => s.startsWith "inst"
    | _ => false
  | _ => false

/-- Atoms as seen by the model search: `collectAtoms`, also looking through `evalHeads`. -/
partial def atomsOf (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
  let e := e.consumeMData
  if !e.hasFVar && !e.hasMVar then acc
  else match e.getAppFn with
    | .const n _ =>
      if e.isApp && (arithHeads.contains n || evalHeads.contains n) then
        -- instance arguments (`instDecidableLtBitVec x y`) are not values
        e.getAppArgs.foldl (fun acc a => if isInstArg a then acc else atomsOf a acc) acc
      else acc.insert e
    | _ => acc.insert e

def isAtom (e : Expr) : Bool :=
  (e.hasFVar || e.hasMVar) && match e.getAppFn with
    | .const n _ => !(e.isApp && (arithHeads.contains n || evalHeads.contains n))
    | _ => true

def sameSort : Val → Val → Bool
  | .bv w _, .bv v _ => w == v | .nat _, .nat _ | .int _, .int _ | .bool _, .bool _ => true
  | _, _ => false

def nextSeed (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- 64 pseudo-random bits from `seed` (two LCG steps; the low bits of one step are weak). -/
def rbits (seed : Nat) : Nat := (nextSeed seed / 2 ^ 32) * 2 ^ 32 + nextSeed (nextSeed seed) / 2 ^ 32

def vsub : Val → Val → Option Val
  | .bv w x, .bv _ y => some (.bv w ((x + 2 ^ w - y) % 2 ^ w))
  | .int x, .int y => some (.int (x - y))
  | .nat x, .nat y => if y ≤ x then some (.nat (x - y)) else none
  | _, _ => none

def vadd : Val → Val → Option Val
  | .bv w x, .bv _ y => some (.bv w ((x + y) % 2 ^ w))
  | .int x, .int y => some (.int (x + y))
  | .nat x, .nat y => some (.nat (x + y))
  | _, _ => none

/-- Extend `asg` so that `eval asg e = some y`, inverting the operations on the (unique)
unevaluable path of `e`; free bits are filled from `seed`. `none` if this is impossible or not
supported. The result is re-checked by the caller (`steerStep` only accepts progress, and
`evalVerdict` re-evaluates every fact), so a wrong inverse costs completeness only. -/
partial def solveFor (asg : Std.HashMap Expr Val) (e : Expr) (y : Val) (seed : Nat) :
    Option (Std.HashMap Expr Val) := do
  let e := e.consumeMData
  if let some v := eval asg e then
    return ← if v == y then some asg else none
  if isAtom e then
    -- atoms keep the sort of their type; `y` comes from the other side of a homogeneous fact
    return asg.insert e y
  let r := rbits seed
  let s' := nextSeed seed
  let args := e.getAppArgs
  let ev := eval asg
  match e.getAppFn.constName?.getD .anonymous, args with
  | ``BitVec.setWidth, #[w, _, a] | ``BitVec.zeroExtend, #[w, _, a]
  | ``BitVec.truncate, #[w, _, a] =>
    let w ← evalNat? w; let (v, yv) ← asBV (some y)
    let x := if w ≤ v then yv else yv + (r % 2 ^ (w - v)) * 2 ^ v
    guard (x < 2 ^ w && x % 2 ^ v == yv)
    solveFor asg a (.bv w x) s'
  | ``BitVec.signExtend, #[w, _, a] =>
    let w ← evalNat? w; let (v, yv) ← asBV (some y)
    let x := if w ≤ v then yv % 2 ^ w else yv + (r % 2 ^ (w - v)) * 2 ^ v
    guard (((toIntW w x) % (2 ^ v : Nat)).toNat == yv)
    solveFor asg a (.bv w x) s'
  | ``BitVec.extractLsb', #[n, st, _, a] =>
    let n ← evalNat? n; let st ← evalNat? st; let (m, yv) ← asBV (some y)
    let x := ((r % 2 ^ st) + yv * 2 ^ st + (rbits s' % 2 ^ n) / 2 ^ (st + m) * 2 ^ (st + m)) % 2 ^ n
    guard ((x / 2 ^ st) % 2 ^ m == yv)
    solveFor asg a (.bv n x) (nextSeed s')
  | ``HAdd.hAdd, #[_, _, _, _, a, b] =>
    match ev a, ev b with
    | some va, none => solveFor asg b (← vsub y va) s'
    | none, some vb => solveFor asg a (← vsub y vb) s'
    | _, _ => none
  | ``HSub.hSub, #[_, _, _, _, a, b] =>
    match ev a, ev b with
    | some va, none => solveFor asg b (← vsub va y) s'
    | none, some vb => solveFor asg a (← vadd y vb) s'
    | _, _ => none
  | ``HXor.hXor, #[_, _, _, _, a, b] =>
    match ev a, ev b, y with
    | some (.bv w m), none, .bv _ yv => solveFor asg b (.bv w (yv ^^^ m)) s'
    | none, some (.bv w m), .bv _ yv => solveFor asg a (.bv w (yv ^^^ m)) s'
    | _, _, _ => none
  | ``HAnd.hAnd, #[_, _, _, _, a, b] =>
    let (t, m) ← match ev a, ev b with
      | some va, none => some (b, va) | none, some vb => some (a, vb) | _, _ => none
    let (w, mv) ← asBV (some m); let (_, yv) ← asBV (some y)
    guard (yv &&& mv == yv)
    solveFor asg t (.bv w ((yv ||| (r % 2 ^ w &&& (2 ^ w - 1 - mv))) % 2 ^ w)) s'
  | ``HOr.hOr, #[_, _, _, _, a, b] =>
    let (t, m) ← match ev a, ev b with
      | some va, none => some (b, va) | none, some vb => some (a, vb) | _, _ => none
    let (w, mv) ← asBV (some m); let (_, yv) ← asBV (some y)
    guard (yv &&& mv == mv)
    solveFor asg t (.bv w ((yv ^^^ mv) ||| (r % 2 ^ w &&& mv))) s'
  | ``HShiftLeft.hShiftLeft, #[_, _, _, _, a, k] =>
    let k ← (← ev k).toNat?; let (w, yv) ← asBV (some y)
    let x := if k ≥ w then r % 2 ^ w else (yv >>> k) + (r % 2 ^ k) * 2 ^ (w - k)
    guard ((if k ≥ w then 0 else (x <<< k) % 2 ^ w) == yv)
    solveFor asg a (.bv w x) s'
  | ``HShiftRight.hShiftRight, #[_, _, _, _, a, k] =>
    let k ← (← ev k).toNat?; let (w, yv) ← asBV (some y)
    let x := if k ≥ w then r % 2 ^ w else ((yv <<< k) + r % 2 ^ k) % 2 ^ w
    guard ((if k ≥ w then 0 else x >>> k) == yv)
    solveFor asg a (.bv w x) s'
  | ``HMul.hMul, #[_, _, _, _, a, b] =>
    let (t, m) ← match ev a, ev b with
      | some va, none => some (b, va) | none, some vb => some (a, vb) | _, _ => none
    match m, y with
    | .bv w k, .bv _ yv => guard (k != 0 && yv % k == 0); solveFor asg t (.bv w (yv / k)) s'
    | .nat k, .nat yv => guard (k != 0 && yv % k == 0); solveFor asg t (.nat (yv / k)) s'
    | _, _ => none
  | ``BitVec.toNat, #[w, a] =>
    let w ← evalNat? w; let yv ← asNat (some y); guard (yv < 2 ^ w); solveFor asg a (.bv w yv) s'
  | ``BitVec.toInt, #[w, a] =>
    let w ← evalNat? w
    let .int i := y | none
    let x := (i % (2 ^ w : Nat)).toNat
    guard (toIntW w x == i)
    solveFor asg a (.bv w x) s'
  | ``BitVec.ofNat, #[_, n] =>
    let (_, yv) ← asBV (some y); solveFor asg n (.nat yv) s'
  | ``Nat.cast, #[_, _, n] | ``Int.ofNat, #[n] =>
    match y with
    | .int i => guard (0 ≤ i); solveFor asg n (.nat i.toNat) s'
    | .bv _ yv => solveFor asg n (.nat yv) s'
    | _ => none
  | ``Neg.neg, #[_, _, a] =>
    match y with
    | .bv w yv => solveFor asg a (.bv w ((2 ^ w - yv) % 2 ^ w)) s'
    | .int i => solveFor asg a (.int (-i)) s'
    | _ => none
  | ``Complement.complement, #[_, _, a] =>
    let (w, yv) ← asBV (some y); solveFor asg a (.bv w (2 ^ w - 1 - yv)) s'
  | ``Nat.succ, #[a] =>
    let yv ← asNat (some y); guard (yv > 0); solveFor asg a (.nat (yv - 1)) s'
  | ``HAppend.hAppend, #[ta, tb, _, _, a, b] =>
    let wa ← match ta.consumeMData.getAppFnArgs with | (``BitVec, #[w]) => evalNat? w | _ => none
    let wb ← match tb.consumeMData.getAppFnArgs with | (``BitVec, #[w]) => evalNat? w | _ => none
    let (_, yv) ← asBV (some y)
    let asg ← solveFor asg a (.bv wa (yv / 2 ^ wb)) s'
    solveFor asg b (.bv wb (yv % 2 ^ wb)) (nextSeed s')
  | _, _ => none

/-- A fact usable to steer the search: `l = r`, or `l < r` / `l ≤ r` (`strict`). -/
inductive Steer where
  | eq (l r : Expr)
  | le (strict : Bool) (l r : Expr)
  deriving Inhabited

mutual
/-- Steering facts implied by `e` evaluating to `pos` (conjunctions split, negations pushed
into comparisons; anything else contributes nothing). -/
partial def steersOf (e : Expr) (pos : Bool) (acc : Array Steer) : Array Steer :=
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Not, #[a]) | (``not, #[a]) => steersOf a (!pos) acc
  | (``And, #[a, b]) | (``and, #[a, b]) => if pos then steersOf b pos (steersOf a pos acc) else acc
  | (``Or, #[a, b]) | (``or, #[a, b]) => if pos then acc else steersOf b pos (steersOf a pos acc)
  | (``decide, #[a, _]) => steersOf a pos acc
  | (``Eq, #[_, a, b]) | (``BEq.beq, #[_, _, a, b]) => eqSteer a b pos acc
  | (``Ne, #[_, a, b]) | (``bne, #[_, _, a, b]) => eqSteer a b (!pos) acc
  | (``LT.lt, #[_, _, a, b]) | (``BitVec.ult, #[_, a, b]) =>
    acc.push (if pos then .le true a b else .le false b a)
  | (``LE.le, #[_, _, a, b]) | (``BitVec.ule, #[_, a, b]) =>
    acc.push (if pos then .le false a b else .le true b a)
  | (``GT.gt, #[_, _, a, b]) => acc.push (if pos then .le true b a else .le false a b)
  | (``GE.ge, #[_, _, a, b]) => acc.push (if pos then .le false b a else .le true a b)
  | _ =>
    -- an opaque `Prop`/`Bool` atom: pin its truth value
    if isAtom e then acc.push (.eq e (if pos then mkConst ``True else mkConst ``False)) else acc

/-- `a = b` known to evaluate to `pos`; `b`/`a` a `Bool`/`Prop` literal recurses. -/
partial def eqSteer (a b : Expr) (pos : Bool) (acc : Array Steer) : Array Steer :=
  match boolLit? b, boolLit? a with
  | some v, _ => steersOf a (pos == v) acc
  | none, some v => steersOf b (pos == v) acc
  | none, none => if pos then acc.push (.eq a b) else acc
where
  boolLit? (e : Expr) : Option Bool :=
    match e.consumeMData.getAppFn.constName? with
    | some ``Bool.true | some ``True => some true
    | some ``Bool.false | some ``False => some false
    | _ => none
end

/-- A value above (`up`) or below `v`, strictly if `strict`; `none` at the end of the range. -/
def pickNear (v : Val) (up strict : Bool) (r : Nat) : Option Val :=
  let d := (if strict then 1 else 0) + (if r % 3 == 0 then 0 else if r % 3 == 1 then 1 else r % 1000)
  match v with
  | .nat x => if up then some (.nat (x + d)) else if d ≤ x then some (.nat (x - d)) else
      if strict && x == 0 then none else some (.nat 0)
  | .int x => some (.int (if up then x + d else x - d))
  | .bv w x =>
    if up then (if x + d < 2 ^ w then some (.bv w (x + d)) else
      if strict && x + 1 ≥ 2 ^ w then none else some (.bv w (2 ^ w - 1)))
    else (if d ≤ x then some (.bv w (x - d)) else if strict && x == 0 then none else some (.bv w 0))
  | _ => none

/-- One propagation step over `steers`: the first steer with exactly one evaluable side that can
be solved for the other side. With `fwdOnly`, only sides that are atoms are solved (definitions
`t = e` are applied in dependency order, nothing is inverted). -/
def steerStep (asg : Std.HashMap Expr Val) (steers : Array Steer) (seed : Nat)
    (fwdOnly : Bool := false) : Option (Std.HashMap Expr Val) := Id.run do
  let mut seed := seed
  -- pass 0 solves only atom sides (definitions, in dependency order); pass 1 inverts operations
  for pass in [0, 1] do
   if pass == 1 && fwdOnly then break
   for st in steers do
    seed := nextSeed seed
    let ok (e : Expr) : Bool := pass == 1 || isAtom e.consumeMData
    let r? : Option (Std.HashMap Expr Val) := match st with
      | .eq l r => match eval asg l, eval asg r with
        | some vl, none => if ok r then solveFor asg r vl seed else none
        | none, some vr => if ok l then solveFor asg l vr seed else none
        | _, _ => none
      | .le strict l r => match eval asg l, eval asg r with
        | some vl, none => do guard (ok r); solveFor asg r (← pickNear vl true strict (rbits seed)) (nextSeed seed)
        | none, some vr => do guard (ok l); solveFor asg l (← pickNear vr false strict (rbits seed)) (nextSeed seed)
        | _, _ => none
    if let some a := r? then
      if a.size > asg.size then return some a
  return none

end Model

open Model in
/-- Evaluate `p` against `hyps` by searching for concrete models (see `Model`).
`undetermined` means two total assignments were found that make every hypothesis evaluate to
`true` and `p` evaluate to `true` resp. `false`; since the evaluator is exact on the operations
it interprets, neither `p` nor `¬p` then follows from `hyps` (with the atoms uninterpreted). -/
def evalVerdict (p : Expr) (hyps : Array Expr) (rounds : Nat := 12) : MetaM Verdict := do
  let mut atomSet : Std.HashSet Expr := atomsOf p {}
  for h in hyps do atomSet := atomsOf h atomSet
  -- `let` variables are not free: their definitions are extra facts
  let mut facts := hyps
  let mut work := atomSet.toArray
  let mut done : Std.HashSet Expr := {}
  while h : work.size > 0 do
    let a := work[work.size - 1]
    work := work.pop
    if done.contains a then continue
    done := done.insert a
    if let .fvar id := a then
      if let some v ← id.getValue? then
        let some eq ← observing? (mkEq a v) | return .unknown
        facts := facts.push eq
        for b in (atomsOf v {}).toList do
          if !atomSet.contains b then atomSet := atomSet.insert b; work := work.push b
  let atoms := atomSet.toArray
  let lits := facts.foldl (fun acc h => literalsIn h acc) (literalsIn p #[])
  let mut cands := #[]
  for a in atoms do
    let some c ← candidates (← inferType a) lits | return .unknown
    if c.isEmpty then return .unknown
    cands := cands.push c
  let hSteers := facts.foldl (fun acc h => steersOf h true acc) #[]
  let posSteers := steersOf p true #[] ++ hSteers
  let negSteers := steersOf p false #[] ++ hSteers
  -- atoms that are one side of an equation whose other side is not a bare atom: computed, not guessed
  let defined : Std.HashSet Expr := hSteers.foldl (init := {}) fun acc st => match st with
    | .eq l r =>
      let l := l.consumeMData; let r := r.consumeMData
      if isAtom l && !isAtom r then acc.insert l else if isAtom r && !isAtom l then acc.insert r else acc
    | _ => acc
  let mut seen : Option Bool := none
  let mut seed : Nat := 0x9e3779b9
  for r in [:rounds] do
    -- no model of the hypotheses after half of the budget: give up (cost control)
    if seen.isNone && 2 * r ≥ rounds then break
    seed := nextSeed seed
    -- alternate: plain hypotheses, steered towards `p`, steered towards `¬p`; each both with
    -- full inversion and forward-only (the latter keeps definitional chains `y = f x` satisfiable
    -- when inverting `f` would need a lucky value, e.g. `signExtend`)
    let fwdOnly := (r / 3) % 2 == 1
    let steers := match r % 3 with
      | 0 => hSteers | 1 => (if seen == some true then negSteers else posSteers)
      | _ => (if seen == some false then posSteers else negSteers)
    let mut asg : Std.HashMap Expr Val := {}
    for _ in [:2 * atoms.size + 2] do
      seed := nextSeed seed
      if let some a := steerStep asg steers seed fwdOnly then asg := a; continue
      -- stuck: give an unassigned atom (from a rotating start, atoms defined by an equation
      -- last) a candidate value
      let free (k : Nat) := !asg.contains atoms[k]!
      let rot (k : Nat) := (k + r) % atoms.size
      let some i := ((List.range atoms.size).find? fun k => free (rot k) && !defined.contains atoms[rot k]!)
          <|> ((List.range atoms.size).find? fun k => free (rot k)) | break
      let k := rot i
      let c := cands[k]!
      let rb := rbits seed
      let v := if r == 0 then c[0]! else match c[rb % c.size]!, rb % 4 with
        | .bv w _, 0 => .bv w (rbits (nextSeed seed) % 2 ^ w)
        | v, _ => v
      asg := asg.insert atoms[k]! v
    -- complete the assignment (propagation may have left atoms unconstrained)
    for k in [:atoms.size] do
      if !asg.contains atoms[k]! then asg := asg.insert atoms[k]! cands[k]![0]!
    -- reject ill-sorted assignments (a wrong inverse in `solveFor`)
    if (List.range atoms.size).any fun k => !sameSort (asg.getD atoms[k]! default) cands[k]![0]! then
      continue
    let mut sat := true
    for h in facts do
      match eval asg h with
      | some (.bool true) => pure ()
      | some (.bool false) => sat := false; break
      | _ => return .unknown
    if !sat then continue
    let some (.bool b) := eval asg p | return .unknown
    match seen with
    | none => seen := some b
    | some b' => if b != b' then return .undetermined
  return match seen with | some b => .likely b | none => .unknown

end ProofLib.BV.Arith
