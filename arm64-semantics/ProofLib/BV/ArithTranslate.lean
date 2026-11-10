/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.ArithCore
public import ProofLib.BV.ArithClassify
import Arm64.Trusted.Spec.SepLogic

/-!
# `bv_arith` Translation and Interval Analysis

Translates `BitVec` arithmetic goals and relevant hypotheses into `Nat` relations for `omega`.
Uses a bounded two-step interval analysis (`ub` and `lb`) over indexed relational hypotheses to
discharge no-overflow side conditions and emit mod-free `toNat` node equations before falling back
to deferred `% 2^w` wrapping facts.
-/

public meta section

namespace ProofLib.BV.Arith
open Lean Meta

/-- A relational `Nat` fact `lhs R rhs` with its proof. `kind`: 0 `<`, 1 `≤`, 2 `=`. -/
structure RelFact where
  lhs : Expr
  rhs : Expr
  kind : Nat
  pf : Expr

structure TState where
  facts : Array Expr := #[]
  byLhs : Std.HashMap Expr (Array RelFact) := {}
  byRhs : Std.HashMap Expr (Array RelFact) := {}
  visited : Std.HashSet Expr := {}
  ubCache : Std.HashMap (Expr × Nat) (Option (Nat × Expr)) := {}
  /-- `(x - y).toNat ↦ (pf : (x-y).toNat + b = a, a, b)` for no-wrap subtraction nodes. -/
  subNodes : Std.HashMap Expr (Expr × Expr × Expr) := {}
  /-- Node equations `t.toNat ↦ (rhs, pf : t.toNat = rhs)`. `rhs` mentions only `toNat` of strict
  subterms of `t`, so following them terminates and costs no fact-following depth. -/
  nodeEq : Std.HashMap Expr (Expr × Expr) := {}
  /-- Wrapping node facts (one `%` each), withheld from the first `omega` attempt. -/
  deferred : Array Expr := #[]
  /-- Facts `x + y < s` / `x + y ≤ s`, indexed by each summand: `x ↦ (y, true, f)`,
  `y ↦ (x, false, f)` (for sum monotonicity in the interval analysis). -/
  sumIdx : Std.HashMap Expr (Array (Expr × Bool × RelFact)) := {}
  /-- Normalization simp context, for `ite` conditions met during the traversal. -/
  normCtx : Option Simp.Context := none

abbrev TransM := StateRefT TState MetaM

/-! ## Expression builders -/

def natTy : Expr := mkConst ``Nat
def mkNatLe (a b : Expr) : Expr := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat) a b
def mkNatLt (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) natTy (mkConst ``instLTNat) a b
def mkNatEq (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) natTy a b
def lit (n : Nat) : Expr := mkNatLit n

def eqByRfl (a b : Expr) : Expr :=
  mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [1]) natTy a) (mkNatEq a b)

def leLit (k m : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit k) (lit m) (mkApp2 (mkConst ``Eq.refl [1])
    (mkConst ``Bool) (mkConst ``Bool.true))
def ltLit (k m : Nat) : Expr :=
  mkExpectedPropHint (leLit (k + 1) m) (mkNatLt (lit k) (lit m))

def recordFact (pf : Expr) : TransM Unit :=
  modify fun s => { s with facts := s.facts.push pf }

partial def indexFact (pf ty : Expr) : TransM Unit := do
  let ty := ty.consumeMData
  match ty.getAppFnArgs with
  | (``And, #[p, q]) =>
    indexFact (mkApp3 (mkConst ``And.left) p q pf) p
    indexFact (mkApp3 (mkConst ``And.right) p q pf) q
  | (``LT.lt, #[α, _, a, b]) => if α.isConstOf ``Nat then
      add { lhs := a, rhs := b, kind := 0, pf }; summands a b 0 pf
  | (``LE.le, #[α, _, a, b]) => if α.isConstOf ``Nat then
      add { lhs := a, rhs := b, kind := 1, pf }; summands a b 1 pf
  | (``Eq, #[α, a, b]) =>
    if α.isConstOf ``Nat then
      add { lhs := a, rhs := b, kind := 2, pf }
      add { lhs := b, rhs := a, kind := 2, pf := mkApp4 (mkConst ``Eq.symm [1]) natTy a b pf }
  | _ => pure ()
where
  add (f : RelFact) : TransM Unit := modify fun s => { s with
    byLhs := s.byLhs.insert f.lhs ((s.byLhs.getD f.lhs #[]).push f)
    byRhs := s.byRhs.insert f.rhs ((s.byRhs.getD f.rhs #[]).push f)
    ubCache := {} }
  /-- For `l R s` with `l = x + y` (Nat), index the summand facts `x R s`, `y R s`
  (recursively). Only used by the interval analysis; not passed to `omega`. -/
  summands (l s : Expr) (kind : Nat) (pf : Expr) : TransM Unit := do
    let .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) α) _) _) _) x) y := l.consumeMData
      | return
    unless α.isConstOf ``Nat do return
    let (nl, nr) := if kind == 0 then (``summand_lt_left, ``summand_lt_right)
      else (``summand_le_left, ``summand_le_right)
    let px := mkApp4 (mkConst nl) x y s pf
    let py := mkApp4 (mkConst nr) x y s pf
    let f : RelFact := { lhs := l, rhs := s, kind, pf }
    modify fun st =>
      let idx := st.sumIdx.insert x ((st.sumIdx.getD x #[]).push (y, true, f))
      { st with sumIdx := idx.insert y ((idx.getD y #[]).push (x, false, f)) }
    add { lhs := x, rhs := s, kind, pf := px }; summands x s kind px
    add { lhs := y, rhs := s, kind, pf := py }; summands y s kind py

/-! ## Interval analysis -/

def better (a b : Option (Nat × Expr)) (lower := false) : Option (Nat × Expr) :=
  match a, b with
  | none, x | x, none => x
  | some (x, px), some (y, py) =>
    if lower then (if x ≥ y then some (x, px) else some (y, py))
    else (if x ≤ y then some (x, px) else some (y, py))

/-- Rewrite the summands of a `Nat` sum along mod-free node equations (`t.toNat = rhs` with
`rhs` not a `%`), recursively. Returns `(e', pf : e = e')` if anything changed. -/
partial def canonSum (e : Expr) : TransM (Option (Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
    unless α.isConstOf ``Nat do return none
    let ra ← canonSum a; let rb ← canonSum b
    if ra.isNone && rb.isNone then return none
    let refl x := mkApp2 (mkConst ``Eq.refl [1]) natTy x
    let (a', pa) := ra.getD (a, refl a); let (b', pb) := rb.getD (b, refl b)
    return some (mkNatAdd a' b', mkAppN (mkConst ``congr_add) #[a, a', b, b', pa, pb])
  | (``BitVec.toNat, #[_, _]) =>
    let some (r, pf) := (← get).nodeEq[e]? | return none
    if r.isAppOf ``HMod.hMod then return none
    match ← canonSum r with
    | some (r', pr) => return some (r', mkApp6 (mkConst ``Eq.trans [1]) natTy e r r' pf pr)
    | none => return some (r, pf)
  | _ => return none

def structLe (b c : Expr) : Option Expr :=
  if b == c then some (mkApp (mkConst ``Nat.le_refl) c)
  else match b.getAppFnArgs with
    | (``HSub.hSub, #[α, _, _, _, c', x]) =>
      if α.isConstOf ``Nat && c' == c then some (mkApp2 (mkConst ``Nat.sub_le) c x) else none
    | _ => none

mutual
/-- Upper bound `e ≤ k` (`k` literal) with proof. `d` bounds fact-following depth. -/
partial def ub (e : Expr) (d : Nat := 2) : TransM (Option (Nat × Expr)) := do
  if let some k := evalNat? e then
    return some (k, mkExpectedPropHint (mkApp (mkConst ``Nat.le_refl) e) (mkNatLe e (lit k)))
  if let some r := (← get).ubCache[(e, d)]? then return r
  let mut best : Option (Nat × Expr) := none
  if let some (r, pf) := (← get).nodeEq[e]? then
    if let some (k, pk) ← ub r d then
      best := some (k, mkApp5 (mkConst ``ub_trans) e r (lit k) (mkApp3 (mkConst ``ub_of_eq) e r pf) pk)
  if d > 0 then
    for f in (← get).byLhs.getD e #[] do
      let some (k, pk) ← ub f.rhs (d - 1) | continue
      match f.kind with
      | 0 => if k > 0 then
          best := better best (some (k - 1, mkApp7 (mkConst ``ub_trans_lt) e f.rhs (lit k)
            (lit (k - 1)) f.pf pk (eqByRfl (lit k) (mkNatAdd (lit (k - 1)) (lit 1)))))
      | 1 => best := better best (some (k, mkApp5 (mkConst ``ub_trans) e f.rhs (lit k) f.pf pk))
      | _ => best := better best (some (k, mkApp5 (mkConst ``ub_trans) e f.rhs (lit k)
            (mkApp3 (mkConst ``ub_of_eq) e f.rhs f.pf) pk))
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) => if α.isConstOf ``Nat then
      if let (some (k, pa), some (l, pb)) := (← ub a d, ← ub b d) then
        best := better best (some (k + l, mkAppN (mkConst ``ub_add)
          #[a, b, lit k, lit l, lit (k + l), pa, pb, eqByRfl (mkNatAdd (lit k) (lit l)) (lit (k + l))]))
      if let some (e', pe) ← canonSum e then
        if let some (k, pk) ← ub e' d then
          best := better best (some (k, mkApp5 (mkConst ``ub_of_eq_trans) e e' (lit k) pe pk))
      if d > 0 then
        for (c, isLeft, f) in (← get).sumIdx.getD a #[] do
          if !isLeft then continue
          let some hb := structLe b c | continue
          best := better best (← mono false a b c hb f d)
        for (c, isLeft, f) in (← get).sumIdx.getD b #[] do
          if isLeft then continue
          let some ha := structLe a c | continue
          best := better best (← mono true b a c ha f d)
  | (``HMul.hMul, #[α, _, _, _, a, b]) => if α.isConstOf ``Nat then
      if let (some (k, pa), some (l, pb)) := (← ub a d, ← ub b d) then
        best := better best (some (k * l, mkAppN (mkConst ``ub_mul)
          #[a, b, lit k, lit l, lit (k * l), pa, pb, eqByRfl (mkNatMul (lit k) (lit l)) (lit (k * l))]))
  | (``HDiv.hDiv, #[α, _, _, _, a, b]) => if α.isConstOf ``Nat then
      if let some (k, pa) ← ub a d then
        if let some p := evalNat? b then
          best := better best (some (k / p, mkAppN (mkConst ``ub_div_lit)
            #[a, lit k, b, lit (k / p), pa, eqByRfl (mkApp6 (mkConst ``HDiv.hDiv [0, 0, 0]) natTy natTy natTy
              (mkApp2 (mkConst ``instHDiv [0]) natTy (mkConst ``Nat.instDiv)) (lit k) b) (lit (k / p))]))
        else best := better best (some (k, mkApp4 (mkConst ``ub_div) a b (lit k) pa))
  | (``HMod.hMod, #[α, _, _, _, a, b]) => if α.isConstOf ``Nat then
      if let some p := evalNat? b then
        if p > 0 then
          best := better best (some (p - 1, mkApp4 (mkConst ``ub_mod_lit) a b (lit (p - 1))
            (ltLit 0 p |> fun pf => mkExpectedPropHint pf (mkNatLt (lit 0) b)) |>
            fun f => mkApp f (eqByRfl b (mkNatAdd (lit (p - 1)) (lit 1)))))
      if let some (k, pa) ← ub a d then
        best := better best (some (k, mkApp4 (mkConst ``ub_mod) a b (lit k) pa))
  | (``HSub.hSub, #[α, _, _, _, a, b]) => if α.isConstOf ``Nat then
      if let some (k, pa) ← ub a d then
        best := better best (some (k, mkApp4 (mkConst ``ub_sub) a b (lit k) pa))
  | (``BitVec.toNat, #[w, x]) =>
      if let some wn := evalNat? w then
        if wn ≤ 4096 then
          let m := 2 ^ wn - 1
          best := better best (some (m, mkApp4 (mkConst ``ub_toNat) w x (lit m)
            (eqByRfl (mkNatPow (lit 2) w) (mkNatAdd (lit m) (lit 1)))))
      if let some (pf, a, b) := (← get).subNodes[e]? then
        if let (some (k, pa), some (l, pb)) := (← ub a d, ← lb b d) then
          best := better best (some (k - l, mkAppN (mkConst ``ub_subnode)
            #[e, a, b, lit k, lit l, lit (k - l), pf, pa, pb,
              eqByRfl (mkNatSub (lit k) (lit l)) (lit (k - l))]))
  | _ => pure ()
  modify fun s => { s with ubCache := s.ubCache.insert (e, d) best }
  return best

/-- From `hb : b ≤ c` and the sum fact `f : a + c R s` (`c + a R s` if `swap`), bound
`a + b` (`b + a`) by an upper bound of `s`. -/
partial def mono (swap : Bool) (a b c hb : Expr) (f : RelFact) (d : Nat) :
    TransM (Option (Nat × Expr)) := do
  let some (k, pk) ← ub f.rhs (d - 1) | return none
  match f.kind with
  | 0 =>
    if k == 0 then return none
    let n := if swap then ``ub_sum_mono_lt' else ``ub_sum_mono_lt
    return some (k - 1, mkAppN (mkConst n) #[a, b, c, f.rhs, lit k, lit (k - 1), hb, f.pf, pk,
      eqByRfl (lit k) (mkNatAdd (lit (k - 1)) (lit 1))])
  | 1 =>
    let n := if swap then ``ub_sum_mono_le' else ``ub_sum_mono_le
    return some (k, mkAppN (mkConst n) #[a, b, c, f.rhs, lit k, hb, f.pf, pk])
  | _ => return none

/-- Lower bound `k ≤ e` with proof (always succeeds; default `0`). -/
partial def lb (e : Expr) (d : Nat := 2) : TransM (Option (Nat × Expr)) := do
  if let some k := evalNat? e then
    return some (k, mkExpectedPropHint (mkApp (mkConst ``Nat.le_refl) e) (mkNatLe (lit k) e))
  let mut best : Option (Nat × Expr) := some (0, mkApp (mkConst ``lb_zero) e)
  if let some (r, pf) := (← get).nodeEq[e]? then
    if let some (k, pk) ← lb r d then
      best := better (lower := true) best
        (some (k, mkApp5 (mkConst ``lb_trans) e r (lit k) (mkApp3 (mkConst ``lb_of_eq) e r pf) pk))
  if d > 0 then
    for f in (← get).byRhs.getD e #[] do
      let some (k, pk) ← lb f.lhs (d - 1) | continue
      match f.kind with
      | 0 => best := better (lower := true) best (some (k + 1, mkAppN (mkConst ``lb_trans_lt)
            #[e, f.lhs, lit k, lit (k + 1), f.pf, pk, eqByRfl (mkNatAdd (lit k) (lit 1)) (lit (k + 1))]))
      | 1 => best := better (lower := true) best (some (k, mkApp5 (mkConst ``lb_trans) e f.lhs (lit k) f.pf pk))
      | _ => best := better (lower := true) best (some (k, mkApp5 (mkConst ``lb_trans) e f.lhs (lit k)
            (mkApp3 (mkConst ``lb_of_eq) e f.lhs (mkApp4 (mkConst ``Eq.symm [1]) natTy f.lhs e f.pf)) pk))
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) => if α.isConstOf ``Nat then
      if let (some (k, pa), some (l, pb)) := (← lb a d, ← lb b d) then
        best := better (lower := true) best (some (k + l, mkAppN (mkConst ``lb_add)
          #[a, b, lit k, lit l, lit (k + l), pa, pb, eqByRfl (mkNatAdd (lit k) (lit l)) (lit (k + l))]))
  | (``HMul.hMul, #[α, _, _, _, a, b]) => if α.isConstOf ``Nat then
      if let (some (k, pa), some (l, pb)) := (← lb a d, ← lb b d) then
        best := better (lower := true) best (some (k * l, mkAppN (mkConst ``lb_mul)
          #[a, b, lit k, lit l, lit (k * l), pa, pb, eqByRfl (mkNatMul (lit k) (lit l)) (lit (k * l))]))
  | _ => pure ()
  return best
end

/-- Prove `lhs < rhs` with `rhs` closed, from an upper bound on `lhs`. -/
def proveLtLit (lhs rhs : Expr) : TransM (Option Expr) := do
  let some m := evalNat? rhs | return none
  let some (k, pk) ← ub lhs | return none
  if k < m then
    return some (mkApp5 (mkConst ``lt_of_ub) lhs (lit k) rhs pk
      (mkExpectedPropHint (ltLit k m) (mkNatLt (lit k) rhs)))
  return none

/-- Prove `b ≤ a` from a direct fact or from `U(b) ≤ L(a)`. -/
def proveLe (b a : Expr) : TransM (Option Expr) := do
  for f in (← get).byLhs.getD b #[] do
    if f.rhs == a then
      match f.kind with
      | 0 => return some (mkApp3 (mkConst ``Nat.le_of_lt) b a f.pf)
      | 1 => return some f.pf
      | _ => return some (mkApp3 (mkConst ``Nat.le_of_eq) b a f.pf)
  -- relational: `a = b * p` (`p ≥ 1` literal) from a node equation, e.g. `y.toNat ≤ (y <<< 4).toNat`
  if let some (r, pf) := (← get).nodeEq.get? a then
    if let (``HMul.hMul, #[_, _, _, _, b', p]) := r.getAppFnArgs then
      if b' == b then
        if let some pn := evalNat? p then
          if 1 ≤ pn then
            return some (mkAppN (mkConst ``le_of_eq_mul) #[a, b, p, pf, leLit 1 pn])
  let some (k, pb) ← ub b | return none
  let some (l, pa) ← lb a | return none
  if k ≤ l then
    return some (mkAppN (mkConst ``le_of_bounds) #[a, b, lit k, lit l, pb, pa, leLit k l])
  return none

/-! ## Node facts -/

/-- Record node fact `pf` and index it for the interval analysis. With `defer`, the fact is put
in `deferred` (used only by the second `omega` stage) instead of `facts`. -/
def emit (pf : Expr) (defer := false) : TransM Unit := do
  if defer then modify fun s => { s with deferred := s.deferred.push pf } else recordFact pf
  let ty ← instantiateMVars (← inferType pf)
  match ty.consumeMData.getAppFnArgs with
  | (``Eq, #[α, l, r]) =>
    if α.isConstOf ``Nat && l.isAppOfArity ``BitVec.toNat 2 then
      modify fun s => { s with nodeEq := s.nodeEq.insert l (r, pf), ubCache := {} }
    else indexFact pf ty
  | _ => indexFact pf ty

/-- Discharge the side condition of a no-wrap node lemma (last explicit argument). -/
def proveSide (p : Expr) : TransM (Option Expr) := do
  match p.consumeMData.getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => proveLtLit a b
  | (``LE.le, #[_, _, b, a]) => proveLe b a
  | _ => return none

/-- `nowrap h` if the side condition `h` is provable, else `wrap`. Returns `(pf, nowrap?)`. -/
def tryNoWrap (nowrap wrap : Expr) : TransM (Expr × Bool) := do
  if let .forallE _ p _ _ ← whnfR (← inferType nowrap) then
    if let some h ← proveSide p then return (mkApp nowrap h, true)
  return (wrap, false)

/-- `tryNoWrap`, then `emit` (deferring the wrapping variant). Returns `(pf, nowrap?)`. -/
def emitNoWrap (nowrap wrap : Expr) : TransM (Expr × Bool) := do
  let (pf, ok) ← tryNoWrap nowrap wrap
  emit pf (defer := !ok)
  return (pf, ok)

def bvWidthExpr? (t : Expr) : MetaM (Option Expr) := do
  match (← whnfR (← inferType t)).getAppFnArgs with
  | (``BitVec, #[w]) => return some w
  | _ => return none

def toNatOf (w x : Expr) : Expr := mkApp2 (mkConst ``BitVec.toNat) w x

/-- Value of a `BitVec` literal, or of a closed `BitVec` term the evaluator can compute (e.g.
`~~~65535#64 &&& ~~~4294901760#64 ||| 983040#64`). Such terms are treated as literals: their
`toNat` equation is closed by kernel `rfl` (bitwise `Nat` ops are GMP-accelerated). -/
def closedLit? (e : Expr) : Option Nat :=
  match bvLit? e with
  | some k => some k
  | none =>
    if e.hasFVar || e.hasMVar || e.approxDepth > 64 then none
    else match eval {} e with
      | some (.bv _ n) => some n
      | _ => none

mutual
/-- Emit the node fact for `t.toNat` (and recursively for its operands). -/
partial def visit (t : Expr) : TransM Unit := do
  let t := t.consumeMData
  if (← get).visited.contains t then return
  modify fun s => { s with visited := s.visited.insert t }
  let some w ← bvWidthExpr? t | return
  if let some k := closedLit? t then
    emit (eqByRfl (toNatOf w t) (lit k)); return
  let bin (nw wr : Name) (x y : Expr) : TransM (Expr × Bool × Expr × Expr) := do
    let (a, ha) ← opnd x; let (b, hb) ← opnd y
    let args := #[w, x, y, a, b, ha, hb]
    let (pf, ok) ← emitNoWrap (mkAppN (mkConst nw) args) (mkAppN (mkConst wr) args)
    return (pf, ok, a, b)
  match t.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) => discard <| bin ``node_add_nowrap ``node_add_wrap x y
  | (``HSub.hSub, #[_, _, _, _, x, y]) =>
    let (pf, ok, a, b) ← bin ``node_sub_nowrap ``node_sub_wrap x y
    if ok then modify fun s => { s with subNodes := s.subNodes.insert (toNatOf w t) (pf, a, b) }
  | (``HMul.hMul, #[_, _, _, _, x, y]) => discard <| bin ``node_mul_nowrap ``node_mul_wrap x y
  | (``HShiftLeft.hShiftLeft, #[_, β, _, _, x, n]) => shift true β x n
  | (``HShiftRight.hShiftRight, #[_, β, _, _, x, n]) => shift false β x n
  | (``BitVec.ofNat, #[_, n]) =>
    collect n
    discard <| emitNoWrap (mkApp2 (mkConst ``node_ofNat_nowrap) w n)
      (mkApp2 (mkConst ``node_ofNat_wrap) w n)
  | (``BitVec.setWidth, #[w', v, x]) =>
    let (a, ha) ← opnd x
    let args := #[w', v, x, a, ha]
    discard <| emitNoWrap (mkAppN (mkConst ``node_setWidth_nowrap) args)
      (mkAppN (mkConst ``node_setWidth_wrap) args)
  | (``HDiv.hDiv, #[_, _, _, _, x, y]) =>
    let (a, ha) ← opnd x; let (b, hb) ← opnd y
    emit (mkAppN (mkConst ``node_udiv) #[w, x, y, a, b, ha, hb])
  | (``HMod.hMod, #[_, _, _, _, x, y]) =>
    let (a, ha) ← opnd x; let (b, hb) ← opnd y
    emit (mkAppN (mkConst ``node_umod) #[w, x, y, a, b, ha, hb])
  | (``Neg.neg, #[_, _, x]) =>
    let (a, ha) ← opnd x; emit (mkAppN (mkConst ``node_neg) #[w, x, a, ha]) (defer := true)
  | (``Complement.complement, #[_, _, x]) =>
    let (a, ha) ← opnd x; emit (mkAppN (mkConst ``node_not) #[w, x, a, ha])
  | (``HAnd.hAnd, #[_, _, _, _, x, y]) =>
    if let some n := mask? y then
      let (a, ha) ← opnd x
      emit (mkAppN (mkConst ``node_and_mask) #[w, x, y, a, lit n, ha, maskPf w y n])
    else if let some n := mask? x then
      let (b, hb) ← opnd y
      emit (mkAppN (mkConst ``node_and_mask') #[w, x, y, b, lit n, hb, maskPf w x n])
    else if let some (lo, k) := range? y then
      let (a, ha) ← opnd x
      emit (mkAppN (mkConst ``node_and_range) (#[w, x, y, a] ++ rangeArgs w y lo k ha))
    else if let some (lo, k) := range? x then
      let (b, hb) ← opnd y
      emit (mkAppN (mkConst ``node_and_range') (#[w, x, y, b] ++ rangeArgs w x lo k hb))
    else
      let (a, ha) ← opnd x; let (b, hb) ← opnd y
      emit (mkAppN (mkConst ``node_and_le) #[w, x, y, a, b, ha, hb])
  | (``HOr.hOr, #[_, _, _, _, x, y]) =>
    visit x; visit y; emit (mkApp3 (mkConst ``node_or_le) w x y)
  | (``ite, #[_, c, inst, x, y]) =>
    let some ctx := (← get).normCtx | return
    let (r, _) ← simp c ctx
    let c' := r.expr
    if ← isArithProp c' then
      let eqTy ← mkEq c c'
      let hc := match r.proof? with
        | some p => p
        | none => mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [1]) (mkSort .zero) c) eqTy
      emit (mkAppN (mkConst ``node_ite) #[w, c, c', inst, x, y, hc])
      collect c'
    else
      emit (mkAppN (mkConst ``node_ite') #[w, c, inst, x, y])
    visit x; visit y
  | (``BitVec.extractLsb', #[w', s, m, x]) =>
    if let some sn := evalNat? s then
      if sn ≤ 4096 then
        let (a, ha) ← opnd x
        emit (mkAppN (mkConst ``node_extract)
          #[w', s, m, x, a, lit (2 ^ sn), ha, eqByRfl (mkNatPow (lit 2) s) (lit (2 ^ sn))])
  | _ => pure ()
where
  mask? (y : Expr) : Option Nat := do
    let m ← closedLit? y
    let n := Nat.log2 (m + 1)
    if 2 ^ n == m + 1 then some n else none
  /-- `m = (2^k - 1) * 2^lo` with `lo ≥ 1`, `k ≥ 1` (contiguous run of ones not at bit 0). -/
  range? (y : Expr) : Option (Nat × Nat) := do
    let m ← closedLit? y
    if m == 0 || m % 2 == 1 then none
    let lo := (List.range 4096).find? (fun i => (m >>> i) % 2 == 1) |>.getD 0
    if lo == 0 || lo > 4096 then none
    let r := m >>> lo
    let k := Nat.log2 (r + 1)
    if 2 ^ k == r + 1 then some (lo, k) else none
  /-- Arguments `p q lo k h hp hq hy` of `node_and_range` for mask `y` (with `h` the operand
  equation). -/
  rangeArgs (w y : Expr) (lo k : Nat) (h : Expr) : Array Expr :=
    let p := lit (2 ^ lo); let q := lit (2 ^ k)
    #[p, q, lit lo, lit k, h, eqByRfl (mkNatPow (lit 2) (lit lo)) p,
      eqByRfl (mkNatPow (lit 2) (lit k)) q,
      eqByRfl (toNatOf w y) (mkNatMul (mkNatSub q (lit 1)) p)]
  maskPf (w y : Expr) (n : Nat) : Expr :=
    eqByRfl (mkNatAdd (toNatOf w y) (lit 1)) (mkNatPow (lit 2) (lit n))
  shift (left : Bool) (β x n : Expr) : TransM Unit := do
    let some w ← bvWidthExpr? x | return
    if β.isConstOf ``Nat then
      let some k := evalNat? n | return
      if k > 4096 then return
      let (a, ha) ← opnd x
      let hp := eqByRfl (mkNatPow (lit 2) n) (lit (2 ^ k))
      let args := #[w, x, n, a, lit (2 ^ k), ha, hp]
      if left then
        discard <| emitNoWrap (mkAppN (mkConst ``node_shl_nowrap) args)
          (mkAppN (mkConst ``node_shl_wrap) args)
      else emit (mkAppN (mkConst ``node_shr) args)
    else
      let some k := bvLit? n | return
      if k > 4096 then return
      let some v ← bvWidthExpr? n | return
      let (a, ha) ← opnd x
      let hp := eqByRfl (mkNatPow (lit 2) (toNatOf v n)) (lit (2 ^ k))
      let args := #[w, v, x, n, a, lit (2 ^ k), ha, hp]
      if left then
        discard <| emitNoWrap (mkAppN (mkConst ``node_shlbv_nowrap) args)
          (mkAppN (mkConst ``node_shlbv_wrap) args)
      else emit (mkAppN (mkConst ``node_shrbv) args)

partial def opnd (x : Expr) : TransM (Expr × Expr) := do
  let some w ← bvWidthExpr? x | throwError "bv_arith: not a BitVec {x}"
  let tn := toNatOf w x
  if let some k := closedLit? x then return (lit k, eqByRfl tn (lit k))
  visit x
  return (tn, mkApp2 (mkConst ``Eq.refl [1]) natTy tn)

partial def collect (e : Expr) : TransM Unit := do
  match e.getAppFnArgs with
  | (``BitVec.toNat, #[_, x]) => visit x
  | (``BitVec.toInt, #[w, x]) =>
    let key := mkApp2 (mkConst ``BitVec.toInt) w x
    unless (← get).visited.contains key do
      modify fun s => { s with visited := s.visited.insert key }
      -- visit first so that the interval analysis can bound `x.toNat` for the no-wrap form
      visit x
      let (pf, _) ← tryNoWrap (mkApp2 (mkConst ``node_toInt_nowrap) w x)
        (mkApp2 (mkConst ``node_toInt) w x)
      emit pf
  | _ =>
    match e with
    | .app f a => collect f; collect a
    | .mdata _ b => collect b
    | _ => pure ()
end

/-! ## Pipeline -/

/-- Normalize `hyps`, emit node facts and run `omega` for goal `g : False`.

`stages`: `.first` runs `omega` without the deferred wrapping node facts, `.full` with all facts,
`.both` tries `.first` and then `.full` if there are deferred facts. -/
inductive Stages | first | full | both
  deriving BEq

/-- Facts `x = v` (proof: `rfl`, by zeta-delta) for the let-bound local variables `x := v` of
arithmetic type that occur in `tys`, transitively through their values. `omega` treats a let
variable as an opaque atom, so without these it cannot relate e.g. `words_bytes := words * 8`. -/
partial def letFacts (tys : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let mut todo := tys.foldl (fun acc ty => collectAtoms ty acc) {} |>.toArray
  let mut seen : Std.HashSet FVarId := {}
  let mut out := #[]
  while todo.size > 0 do
    let a := todo.back!
    todo := todo.pop
    let .fvar fv := a | continue
    if seen.contains fv then continue
    seen := seen.insert fv
    let some v := (← fv.getDecl).value? | continue
    let v ← instantiateMVars v
    let α ← instantiateMVars (← inferType a)
    unless ← isArithProp.isArithType α do continue
    let ty ← mkEq a v
    out := out.push (mkExpectedPropHint (← mkEqRefl a) ty, ty)
    todo := todo ++ (collectAtoms v {}).toArray
  return out

def arithRun (g : MVarId) (hyps : Array (FVarId × Expr)) (nCands : Nat)
    (stages : Stages := .both) : MetaM Unit :=
  g.withContext do
    let ctx ← mkNormCtx
    let mut facts := #[]
    let lets ← perf "letFacts" <| letFacts (hyps.map (·.2))
    for (pf, ty) in hyps.map (fun (fv, ty) => (Expr.fvar fv, ty)) ++ lets do
      match ← perf "normalize" <| normalizeHyp ctx pf ty with
      | none => pure ()
      | some (pf, ty') =>
        if ty'.isFalse then
          g.assign (← mkFalseElim (← g.getType) pf); return
        facts := facts.push (pf, ty')
    let ((), s) ← perf "collect" <| (do
        for (pf, ty) in facts do recordFact pf; indexFact pf ty
        for (_, ty) in facts do collect ty : TransM Unit).run { normCtx := some ctx }
    trace[bv_arith] "{hyps.size} relevant of {nCands} arithmetic hyps; {s.facts.size} facts \
      (+{s.deferred.size} deferred):\
      {indentD (MessageData.joinSep (← (s.facts ++ s.deferred).toList.mapM fun f => do
        return m!"{← inferType f}") Format.line)}"
    let type ← g.getType
    let run (fs : Array Expr) : MetaM Unit := do
      let g' ← mkFreshExprSyntheticOpaqueMVar type
      perf s!"omega ({fs.size} facts)" <| Lean.Elab.Tactic.Omega.omega fs.toList g'.mvarId!
      g.assign (← perf "auxTheorem" <| mkAuxTheorem type (← instantiateMVars g') (zetaDelta := true))
    let full := s.facts ++ s.deferred
    let err (e : Exception) : MetaM Unit := do
      let msgStr ← e.toMessageData.toString
      let hasModWrap := (msgStr.splitOn "18446744073709551616").length > 1 ||
        (msgStr.splitOn "4294967296").length > 1
      let hint := if hasModWrap then
        "\nhint: omega counterexample involves 2^64 / 2^32 modular wraparound; supply an overflow bound (or rewrite with BitVec.toNat_add_of_lt / BitVec.toNat_sub_of_le), or use bv_lin for bitwise/ring identities"
      else ""
      throwError "bv_arith failed ({hyps.size} relevant hyps, {full.size} facts): \
        {e.toMessageData}{hint}"
    match stages with
    | .first => try run s.facts catch e => err e
    | .full => try run full catch e => err e
    | .both =>
      if s.deferred.isEmpty then try run s.facts catch e => err e
      else
        let st ← saveState
        try run s.facts
        catch _ =>
          st.restore
          trace[bv_arith] "retrying with {s.deferred.size} deferred wrapping facts"
          try run full catch e => err e

/-- Close `g` by `bv_arith`: relevance filter, normalization, node facts, `omega`.

The negated goal seeds the relevance filter. If it has no arithmetic content (goal `False` or an
opaque `Prop`), all arithmetic hypotheses are used. The first `omega` call omits wrapping node
facts (`(x + y).toNat = (a + b) % 2^w`, ...), which are expensive case splits and rarely needed;
on failure, one more call is made with everything: all facts, and with `retryAll` (default) all
arithmetic hypotheses if the filter dropped some (contexts contradictory independently of the
goal). So `bv_arith` makes at most two `omega` calls. -/
def arithCore1 (g : MVarId) (retryAll := true) : MetaM Unit := do
  let (_, g) ← g.intros
  -- the goal is literally a hypothesis (typically an opaque `Prop` such as `P_Eq`)
  if ← perf "assumption" <| withReducible g.assumptionCore then return
  let lastBefore := (← g.getDecl).lctx.lastDecl.map (·.fvarId)
  let some g ← g.withContext g.falseOrByContra | return
  g.withContext do
    let newH := (← getLCtx).lastDecl.filter fun d => some d.fvarId != lastBefore
    let cands ← perf "arithHyps" <| arithHyps (newH.map (·.fvarId))
    let mut seed : Option (FVarId × Expr) := none
    if let some d := newH then
      let seedTy ← instantiateMVars d.type
      if ← isArithProp seedTy then
        -- a ground seed (e.g. `¬ 1#64 = 0#64`) has no atoms to filter by
        if !(collectAtoms seedTy {}).isEmpty then seed := some (d.fvarId, seedTy)
    let some (sfv, sty) := seed | arithRun g (pruneDangling {} cands) cands.size
    let seedAtoms := collectAtoms sty {}
    -- stage 0: only *cheap* hypotheses (no `BitVec` arithmetic nodes, so no wrapping case
    -- splits), relevance-filtered among themselves. In large proof contexts the relevant set
    -- also contains earlier `BitVec` equations (`x + n - 1 = x + m`, ...) whose wrap facts make
    -- `omega` exponentially slower, while the goal typically needs only bounds and `Nat` facts.
    let cheapCands := cands.filter fun (_, ty) => bvNodeFree ty
    let cheap := pruneDangling seedAtoms (relevantFilter seedAtoms cheapCands)
    let relevant := relevantFilter seedAtoms cands
    let filtered := pruneDangling seedAtoms relevant
    if cheap.size < filtered.size then
      let s ← saveState
      try
        return ← perf "stage cheap" <| arithRun g ((cheap).push (sfv, sty)) cands.size
      catch _ =>
        s.restore
    if !retryAll || relevant.size == cands.size then
      return ← arithRun g ((filtered).push (sfv, sty)) cands.size
    let s ← saveState
    try arithRun g ((filtered).push (sfv, sty)) cands.size (stages := .first)
    catch e =>
      s.restore
      try arithRun g ((pruneDangling seedAtoms cands).push (sfv, sty)) cands.size (stages := .full)
      catch _ => throw e

/-- `arithCore1` on each conjunct of the goal (after `intros`): one small `omega` problem per
conjunct (with its own relevance filter) instead of one large case split over `¬(p ∧ q ∧ ...)`. -/
partial def arithCore (g : MVarId) (retryAll := true) : MetaM Unit := do
  let (_, g) ← g.intros
  let ty ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``And 2 then
    let [g1, g2] ← g.withContext (g.apply (mkConst ``And.intro))
      | throwError "bv_arith: And.intro failed"
    arithCore g1 retryAll; arithCore g2 retryAll
  else arithCore1 g retryAll

end ProofLib.BV.Arith
