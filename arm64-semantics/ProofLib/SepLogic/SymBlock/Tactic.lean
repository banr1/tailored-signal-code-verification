/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.SymBlock.Spine
public meta import ProofLib.SepLogic.SymBlock.Spine
public import ProofLib.SepLogic.SymBlock.Reify
public import ProofLib.SepLogic.SymWP
public import ProofLib.BV.Linear
public import ProofLib.BV.Arith
import Arm64.Trusted.Spec.SepLogic

/-!
# Reflective Block Symbolic Execution: `sym_block`

Tactic front end (`sym_block`, `sym_block n`, `sym_block (hints := "t n")`) for the reflective block
executor in `ProofLib.SepLogic.SymBlock.Block`. Reifies spatial points-to atoms and register/SP/PC
hypotheses into an `SState`, runs `stepSymInsn` natively to select cell indices (modulo associative
linear address normalization) and branch directions (`t` taken, `n` not taken), and closes the block
with `SymBlock.SepWP_block_spine` or `SymBlock.SepWPp_block_spine`.
-/

public meta section

namespace ProofLib.SymBlock

open Lean Meta Elab Tactic Arm64

deriving instance Lean.ToExpr for CW
deriving instance Lean.ToExpr for SExpr, SCond
deriving instance Lean.ToExpr for VExpr
deriving instance Lean.ToExpr for NVal
deriving instance Lean.ToExpr for Cell
deriving instance Lean.ToExpr for SPc
deriving instance Lean.ToExpr for SFlags
deriving instance Lean.ToExpr for SState
deriving instance Lean.ToExpr for SProp
deriving instance Lean.ToExpr for Hint

namespace Tac

/-! ## Canonicalizers -/

/-- Canonical form used to choose hints and predict when an obligation holds by `rfl`.
    Every rewrite here is a definitional unfolding of `SExpr.eval` (no propositional rewrites such as
    associativity, `x + 0`, or `x - c = x + (-c)`, which would trigger unary `Nat` recursion in the
    kernel). -/
partial def canon : SExpr → SExpr
  | .add a b => .add (canon a) (canon b)
  | .sub a b => .sub (canon a) (canon b)
  | .and a b => .and (canon a) (canon b)
  | .or a b => .or (canon a) (canon b)
  | .xor a b => .xor (canon a) (canon b)
  | .mul a b => .mul (canon a) (canon b)
  | .shl a k => .shl (canon a) k
  | .lshr a k => .lshr (canon a) k
  | .shlBV a b =>
    match canon b with
    | .const c => canon (.shl a c.toNat)
    | b' => .shlBV (canon a) b'
  | .lshrBV a b =>
    match canon b with
    | .const c => canon (.lshr a c.toNat)
    | b' => .lshrBV (canon a) b'
  | .shiftVal .W64 a .LSL k => .shl (canon a) (k % 64)
  | .shiftVal .W64 a .LSR k => .lshr (canon a) (k % 64)
  | .addSub .W64 .ADD a b => canon (.add a b)
  | .addSub .W64 .SUB a b => canon (.sub a b)
  | .logical .W64 .AND a b => .and (canon a) (canon b)
  | .logical .W64 .ORR a b => .or (canon a) (canon b)
  | .logical .W64 .EOR a b => .xor (canon a) (canon b)
  | .bitfield .W64 .UBFM d s immr imms =>
    let r := immr % 64
    let m := imms % 64
    if m + 1 = 64 then canon (.lshr s r)
    else if r > m ∧ m + 1 = r then canon (.shl s (64 - r))
    else if m ≥ r then
      .and (canon (.lshr s r)) (.const (BitVec.ofNat 64 (Nat.shiftLeft 1 (m - r + 1) - 1)))
    else .bitfield .W64 .UBFM (canon d) (canon s) immr imms
  | .bitfield w op d s immr imms => .bitfield w op (canon d) (canon s) immr imms
  | .pageOf a => .pageOf (canon a)
  | .lo12Of a => .lo12Of (canon a)
  | .zext32 a => .zext32 (canon a)
  | .sext bits a => .sext bits (canon a)
  | e => e

/-- Advisor prediction that `a.eval env = b.eval env` holds definitionally. -/
def defeqPred (a b : SExpr) : Bool := a == b || canon a == canon b

/-- Canonical 64-bit linear combination `∑ cᵢ * atomᵢ + const` for advisor cell matching
    (associative, commutative, and distributive over `BitVec 64` constants; never used to predict
    `Eq.refl`). -/
structure LinSExpr64 where
  terms : Array (SExpr × BitVec 64)
  const : BitVec 64
  deriving BEq

private partial def collectLin64 (scale : BitVec 64) (e : SExpr)
    (acc : Array (SExpr × BitVec 64) × BitVec 64) : Array (SExpr × BitVec 64) × BitVec 64 :=
  if scale == 0#64 then acc else
  match e with
  | .const c => (acc.1, acc.2 + scale * c)
  | .add a b =>
    let acc1 := collectLin64 scale a acc
    collectLin64 scale b acc1
  | .sub a b =>
    let acc1 := collectLin64 scale a acc
    collectLin64 (-scale) b acc1
  | .mul (.const k) b => collectLin64 (scale * k) b acc
  | .mul a (.const k) => collectLin64 (scale * k) a acc
  | .shl a k =>
    if k < 64 then collectLin64 (scale * (1#64 <<< k)) a acc
    else acc
  | .addSub .W64 .ADD a b =>
    let acc1 := collectLin64 scale a acc
    collectLin64 scale b acc1
  | .addSub .W64 .SUB a b =>
    let acc1 := collectLin64 scale a acc
    collectLin64 (-scale) b acc1
  | .shiftVal .W64 a .LSL k =>
    collectLin64 (scale * (1#64 <<< (k % 64))) a acc
  | .extendVal .W64 a .UXTX k =>
    if k < 64 then collectLin64 (scale * (1#64 <<< k)) a acc
    else addAtom acc scale (canon e)
  | .extendVal .W64 a .SXTX k =>
    if k < 64 then collectLin64 (scale * (1#64 <<< k)) a acc
    else addAtom acc scale (canon e)
  | _ => addAtom acc scale (canon e)
where
  addAtom (acc : Array (SExpr × BitVec 64) × BitVec 64) (s : BitVec 64) (atom : SExpr) :
      Array (SExpr × BitVec 64) × BitVec 64 :=
    match acc.1.findIdx? (·.1 == atom) with
    | some idx =>
      let (a0, c0) := acc.1[idx]!
      let c1 := c0 + s
      if c1 == 0#64 then (acc.1.eraseIdxIfInBounds idx, acc.2)
      else (acc.1.set! idx (a0, c1), acc.2)
    | none => (acc.1.push (atom, s), acc.2)

/-- Normalize a 64-bit `SExpr` modulo `+`/`-`/constant-scale associativity and commutativity
    so e.g. `(sp - 96) + 16` and `sp - 80` match the same spatial cell. -/
def matchCanon (e : SExpr) : LinSExpr64 :=
  let (ts, c) := collectLin64 1#64 (canon e) (#[], 0#64)
  let sorted := ts.qsort fun (a1, _) (a2, _) => toString (repr a1) < toString (repr a2)
  { terms := sorted, const := c }

/-! ## Reification -/

structure RState where
  leaves : Array Expr := #[]
  atoms : Array Expr := #[]
  leaves8 : Array Expr := #[]
  leaves16 : Array Expr := #[]
  leaves32 : Array Expr := #[]
  leaves128 : Array Expr := #[]
  tpidrE : Expr := mkConst ``Unit.unit

abbrev RM := StateRefT RState MetaM

def leaf (e : Expr) : RM SExpr := do
  let st ← get
  match st.leaves.findIdx? (· == e) with
  | some i => return .var i
  | none =>
    set { st with leaves := st.leaves.push e }
    return .var st.leaves.size

def leafNIdx (w : CW) (e : Expr) : RM Nat := do
  let st ← get
  let arr := match w with
    | .b8 => st.leaves8
    | .b16 => st.leaves16
    | .b32 => st.leaves32
    | .b128 => st.leaves128
  match arr.findIdx? (· == e) with
  | some i => return i
  | none =>
    match w with
    | .b8 => set { st with leaves8 := arr.push e }
    | .b16 => set { st with leaves16 := arr.push e }
    | .b32 => set { st with leaves32 := arr.push e }
    | .b128 => set { st with leaves128 := arr.push e }
    return arr.size

def leafN (w : CW) (e : Expr) : RM NVal := do
  return .leaf (← leafNIdx w e)

def leaf128 (e : Expr) : RM VExpr := do
  return .var (← leafNIdx .b128 e)

/-- Extract `(width, value)` from a syntactic `BitVec` numeral (`BitVec.ofNat w v` or
    `@OfNat.ofNat (BitVec w) v _`). -/
def evalSyntaxBvLit? (e : Expr) : Option (Nat × Nat) :=
  if let some wv := evalBitVecLitPure? e then some wv
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty := (e.getArg! 0).consumeMData
    if ty.isAppOfArity ``BitVec 1 then
      if let (some w, some n) := (evalNatLitPure? (ty.getArg! 0), evalNatLitPure? (e.getArg! 1)) then
        some (w, n % (1 <<< w))
      else none
    else none
  else none

/-- Reify a `BitVec 64` term. Unknown subterms become leaves (always sound: a leaf evaluates to
    itself). -/
partial def reify (e : Expr) : RM SExpr := do
  let e := (← instantiateMVars e).consumeMData
  if let some (64, n) := evalSyntaxBvLit? e then
    return .const (BitVec.ofNat 64 n)
  let st ← get
  if e == st.tpidrE then
    return .tpidr0
  let bin (k : SExpr → SExpr → SExpr) : RM SExpr := do
    return k (← reify (e.getArg! 4)) (← reify (e.getArg! 5))
  if e.isAppOfArity ``HAdd.hAdd 6 then bin .add
  else if e.isAppOfArity ``HSub.hSub 6 then bin .sub
  else if e.isAppOfArity ``HAnd.hAnd 6 then bin .and
  else if e.isAppOfArity ``HOr.hOr 6 then bin .or
  else if e.isAppOfArity ``HXor.hXor 6 then bin .xor
  else if e.isAppOfArity ``HMul.hMul 6 then bin .mul
  else if e.isAppOfArity ``Obj.pageOf 1 then return .pageOf (← reify (e.getArg! 0))
  else if e.isAppOfArity ``Obj.lo12Of 1 then return .lo12Of (← reify (e.getArg! 0))
  else if e.isAppOfArity ``BitVec.zeroExtend 3 then
    if let (some wFrom, some 64) :=
        (evalNatLitPure? (e.getArg! 0), evalNatLitPure? (e.getArg! 1)) then
      let inner := (e.getArg! 2).consumeMData
      if wFrom == 32 && inner.isAppOfArity ``BitVec.truncate 3 then
        if let (some 64, some 32) :=
            (evalNatLitPure? (inner.getArg! 0), evalNatLitPure? (inner.getArg! 1)) then
          return .zext32 (← reify (inner.getArg! 2))
      if wFrom == 32 then
        if let some i := st.leaves32.findIdx? (· == inner) then
          return .zleaf .b32 i
      else if wFrom == 16 then
        if let some i := st.leaves16.findIdx? (· == inner) then
          return .zleaf .b16 i
      else if wFrom == 8 then
        if let some i := st.leaves8.findIdx? (· == inner) then
          return .zleaf .b8 i
    leaf e
  else if e.isAppOfArity ``BitVec.signExtend 3 then
    if let (some wFrom, some 64) :=
        (evalNatLitPure? (e.getArg! 0), evalNatLitPure? (e.getArg! 1)) then
      let inner := (e.getArg! 2).consumeMData
      if inner.isAppOfArity ``BitVec.truncate 3 then
        if let (some 64, some wTr) :=
            (evalNatLitPure? (inner.getArg! 0), evalNatLitPure? (inner.getArg! 1)) then
          if wTr == wFrom then
            return .sext wFrom (← reify (inner.getArg! 2))
    leaf e
  else if e.isAppOfArity ``BitVec.extractLsb' 4 then
    let src := (e.getArg! 1).consumeMData
    if let (some 128, some startBit, some 64) :=
        (evalNatLitPure? (e.getArg! 0), evalNatLitPure? (e.getArg! 2), evalNatLitPure? (e.getArg! 3)) then
      if startBit == 0 then
        if let some i := st.leaves128.findIdx? (· == src) then
          return .lo128 i
      else if startBit == 64 then
        if let some i := st.leaves128.findIdx? (· == src) then
          return .hi128 i
    leaf e
  else if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 || e.isAppOfArity ``HShiftRight.hShiftRight 6 then
    let isL := e.isAppOfArity ``HShiftLeft.hShiftLeft 6
    let amtTy := (e.getArg! 1).consumeMData
    if amtTy.isAppOfArity ``BitVec 1 then
      bin (if isL then .shlBV else .lshrBV)
    else if amtTy.isConstOf ``Nat then
      match (e.getArg! 5).rawNatLit? <|> (e.getArg! 5).nat? with
      | some k => return (if isL then SExpr.shl else SExpr.lshr) (← reify (e.getArg! 4)) k
      | none => leaf e
    else leaf e
  else leaf e

/-- Reify a `BitVec 128` term into a `VExpr`. -/
def reifyV128 (e : Expr) : RM VExpr := do
  let e := (← instantiateMVars e).consumeMData
  if let some (128, n) := evalSyntaxBvLit? e then
    return .const (BitVec.ofNat 128 n)
  if e.isAppOfArity ``HAppend.hAppend 6 then
    let ty0 := (e.getArg! 0).consumeMData
    let ty1 := (e.getArg! 1).consumeMData
    if ty0.isAppOfArity ``BitVec 1 && ty1.isAppOfArity ``BitVec 1 then
      if let (some 64, some 64) :=
          (evalNatLitPure? (ty0.getArg! 0), evalNatLitPure? (ty1.getArg! 0)) then
        return .pair64 (← reify (e.getArg! 4)) (← reify (e.getArg! 5))
  leaf128 e

/-- Flatten an arbitrary `∗` tree left-to-right. -/
partial def flattenSepTree (P : Expr) : Array Expr :=
  let P := P.consumeMData
  if P.isAppOfArity ``SepProp.sepConj 2 then
    flattenSepTree (P.getArg! 0) ++ flattenSepTree (P.getArg! 1)
  else #[P]

/-- True if `P` has any left-nested `∗` (`(A ∗ B) ∗ C`). When false, `cellsProp` is
    definitionally equal to `P` and `hP` is `Eq.refl P`. -/
partial def hasLeftNestedSep (P : Expr) : Bool :=
  let P := P.consumeMData
  if P.isAppOfArity ``SepProp.sepConj 2 then
    (P.getArg! 0).consumeMData.isAppOfArity ``SepProp.sepConj 2 || hasLeftNestedSep (P.getArg! 1)
  else false

private def rightNestSep (atoms : Array Expr) : Expr :=
  if atoms.isEmpty then mkConst ``SepProp.emp
  else atoms.pop.foldr (fun a acc => mkApp2 (mkConst ``SepProp.sepConj) a acc) atoms.back!

private partial def concatRightNestedSep (ls : Array Expr) (RFlat : Expr) : MetaM (Expr × Expr) := do
  if ls.size ≤ 1 then
    let l0 := ls[0]!
    let res := mkApp2 (mkConst ``SepProp.sepConj) l0 RFlat
    return (res, ← mkEqRefl res)
  else
    let l0 := ls[0]!
    let lsTail := ls.extract 1 ls.size
    let lTailFlat := rightNestSep lsTail
    let (restFlat, hRest) ← concatRightNestedSep lsTail RFlat
    let hAssoc := mkApp3 (mkConst ``Arm64.sepConj_assoc) l0 lTailFlat RFlat
    let hCongr ← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) l0) hRest
    let res := mkApp2 (mkConst ``SepProp.sepConj) l0 restFlat
    return (res, ← mkEqTrans hAssoc hCongr)

/-- Flatten an arbitrary `∗` tree into right-nested form with a linear-size proof `P = PFlat`. -/
partial def flattenSepWithProof (P : Expr) : MetaM (Array Expr × Expr × Expr) := do
  let P0 := P.consumeMData
  if P0.isAppOfArity ``SepProp.sepConj 2 then
    let L := P0.getArg! 0
    let R := P0.getArg! 1
    let (ls, _, hL) ← flattenSepWithProof L
    let (rs, rFlat, hR) ← flattenSepWithProof R
    let hLR ← mkCongr (← mkCongrArg (mkConst ``SepProp.sepConj) hL) hR
    let (combFlat, hCat) ← concatRightNestedSep ls rFlat
    return (ls ++ rs, combFlat, ← mkEqTrans hLR hCat)
  else
    return (#[P], P, ← mkEqRefl P)

/-! ## Pretty-Printing Symbolic Values -/

def bvLit (w n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit n)

mutual
  partial def pretty (leaves : RState) (e : SExpr) : MetaM Expr := do
    let p := pretty leaves
    match e with
    | .var i => return leaves.leaves[i]!
    | .const c => return bvLit 64 c.toNat
    | .add a b => mkAppM ``HAdd.hAdd #[← p a, ← p b]
    | .sub a b => mkAppM ``HSub.hSub #[← p a, ← p b]
    | .and a b => mkAppM ``HAnd.hAnd #[← p a, ← p b]
    | .or a b => mkAppM ``HOr.hOr #[← p a, ← p b]
    | .xor a b => mkAppM ``HXor.hXor #[← p a, ← p b]
    | .mul a b => mkAppM ``HMul.hMul #[← p a, ← p b]
    | .shl a k => mkAppM ``HShiftLeft.hShiftLeft #[← p a, mkNatLit k]
    | .lshr a k => mkAppM ``HShiftRight.hShiftRight #[← p a, mkNatLit k]
    | .shlBV a b => mkAppM ``HShiftLeft.hShiftLeft #[← p a, ← p b]
    | .lshrBV a b => mkAppM ``HShiftRight.hShiftRight #[← p a, ← p b]
    | .zext32 a =>
      mkAppM ``BitVec.zeroExtend #[mkNatLit 64, ← mkAppM ``BitVec.truncate #[mkNatLit 32, ← p a]]
    | .sext bits a =>
      mkAppM ``BitVec.signExtend #[mkNatLit 64, ← mkAppM ``BitVec.truncate #[mkNatLit bits, ← p a]]
    | .extendVal w a ext amount =>
      return mkApp4 (mkConst ``Arm64.extendVal) (toExpr w) (← p a) (toExpr ext) (mkNatLit amount)
    | .addSub w op a b =>
      mkAppM ``Prod.fst #[← mkAppM ``evalAddSub #[toExpr w, toExpr op, ← p a, ← p b,
        ← mkAppOptM ``Option.none #[mkConst ``Bool]]]
    | .logical w op a b =>
      mkAppM ``Prod.fst #[← mkAppM ``evalLogical #[toExpr w, toExpr op, ← p a, ← p b,
        mkConst ``PState.zero]]
    | .shiftVal w a op k => return mkApp4 (mkConst ``Arm64.shiftVal) (toExpr w) (← p a) (toExpr op) (mkNatLit k)
    | .bitfield w op d s immr imms =>
      return mkApp6 (mkConst ``evalBitfield) (toExpr w) (toExpr op) (← p d) (← p s) (mkNatLit immr)
        (mkNatLit imms)
    | .dataProc1 w op a =>
      return mkApp3 (mkConst ``evalDataProc1Val) (toExpr w) (toExpr op) (← p a)
    | .dataProc3 w op rn rm ra =>
      return mkApp5 (mkConst ``evalDataProc3Val) (toExpr w) (toExpr op) (← p rn) (← p rm) (← p ra)
    | .zleaf w i =>
      let leafE := match w with
        | .b8 => leaves.leaves8[i]!
        | .b16 => leaves.leaves16[i]!
        | .b32 => leaves.leaves32[i]!
        | .b128 => leaves.leaves128[i]!
      mkAppM ``BitVec.zeroExtend #[mkNatLit 64, leafE]
    | .lo128 i => mkAppM ``BitVec.extractLsb' #[leaves.leaves128[i]!, mkNatLit 0, mkNatLit 64]
    | .hi128 i => mkAppM ``BitVec.extractLsb' #[leaves.leaves128[i]!, mkNatLit 64, mkNatLit 64]
    | .tpidr0 => return leaves.tpidrE
    | .pageOf a => return mkApp (mkConst ``Obj.pageOf) (← p a)
    | .lo12Of a => return mkApp (mkConst ``Obj.lo12Of) (← p a)
    | .ite c t f => do
      let condEq ← mkAppM ``Eq #[← prettyCond leaves c, toExpr true]
      mkAppM ``ite #[condEq, ← p t, ← p f]

  partial def prettyCond (leaves : RState) (c : SCond) : MetaM Expr := do
    let p := pretty leaves
    let p32 (e : SExpr) : MetaM Expr := do
      match canon e with
      | .const v => return bvLit 32 (v.truncate 32).toNat
      | e' => mkAppM ``BitVec.truncate #[mkNatLit 32, ← p e']
    let pc := prettyCond leaves
    match c with
    | .tt => return toExpr true
    | .ff => return toExpr false
    | .eq64 a b => mkAppM ``BEq.beq #[← p (canon a), ← p (canon b)]
    | .eq32 a b => do
      mkAppM ``BEq.beq #[← p32 a, ← p32 b]
    | .ult64 a b => mkAppM ``BitVec.ult #[← p (canon a), ← p (canon b)]
    | .ule64 a b => mkAppM ``BitVec.ule #[← p (canon a), ← p (canon b)]
    | .slt64 a b => mkAppM ``BitVec.slt #[← p (canon a), ← p (canon b)]
    | .sle64 a b => mkAppM ``BitVec.sle #[← p (canon a), ← p (canon b)]
    | .ult32 a b => do
      mkAppM ``BitVec.ult #[← p32 a, ← p32 b]
    | .ule32 a b => do
      mkAppM ``BitVec.ule #[← p32 a, ← p32 b]
    | .slt32 a b => do
      mkAppM ``BitVec.slt #[← p32 a, ← p32 b]
    | .sle32 a b => do
      mkAppM ``BitVec.sle #[← p32 a, ← p32 b]
    | .msb32 a => do
      mkAppM ``BitVec.msb #[← p32 a]
    | .msb64 a => mkAppM ``BitVec.msb #[← p (canon a)]
    | .addC32 a b => do
      let awc ← mkAppM ``Arm64.AddWithCarry32 #[← p32 a, ← p32 b, toExpr false]
      return mkProj ``Arm64.PState 2 (mkProj ``Prod 1 awc)
    | .addC64 a b => do
      let awc ← mkAppM ``Arm64.AddWithCarry64 #[← p (canon a), ← p (canon b), toExpr false]
      return mkProj ``Arm64.PState 2 (mkProj ``Prod 1 awc)
    | .addV32 a b => do
      let awc ← mkAppM ``Arm64.AddWithCarry32 #[← p32 a, ← p32 b, toExpr false]
      return mkProj ``Arm64.PState 3 (mkProj ``Prod 1 awc)
    | .addV64 a b => do
      let awc ← mkAppM ``Arm64.AddWithCarry64 #[← p (canon a), ← p (canon b), toExpr false]
      return mkProj ``Arm64.PState 3 (mkProj ``Prod 1 awc)
    | .subV32 a b => do
      let bNot ← mkAppM ``Complement.complement #[← p32 b]
      let awc ← mkAppM ``Arm64.AddWithCarry32 #[← p32 a, bNot, toExpr true]
      return mkProj ``Arm64.PState 3 (mkProj ``Prod 1 awc)
    | .subV64 a b => do
      let bNot ← mkAppM ``Complement.complement #[← p (canon b)]
      let awc ← mkAppM ``Arm64.AddWithCarry64 #[← p (canon a), bNot, toExpr true]
      return mkProj ``Arm64.PState 3 (mkProj ``Prod 1 awc)
    | .bit a k => mkAppM ``BitVec.getLsbD #[← p (canon a), mkNatLit k]
    | .not c => mkAppM ``not #[← pc c]
    | .and a b => mkAppM ``and #[← pc a, ← pc b]
    | .or a b => mkAppM ``or #[← pc a, ← pc b]
end

/-- Pretty value: canonical form (definitionally equal to the raw evaluation). -/
def prettyC (leaves : RState) (e : SExpr) : MetaM Expr := pretty leaves (canon e)

/-- Pretty 128-bit SIMD value (definitionally equal to `VExpr.eval env v`). -/
def prettyV128 (leaves : RState) : VExpr → MetaM Expr
  | .var i => return leaves.leaves128[i]!
  | .const v => return bvLit 128 v.toNat
  | .pair64 hi lo => do mkAppM ``HAppend.hAppend #[← prettyC leaves hi, ← prettyC leaves lo]

/-- Pretty flags (definitionally equal to `SFlags.denote env ps0`), in the `evalAddSub` /
    `evalLogical` form the stepping tactics evaluate. -/
partial def prettyFlags (leaves : RState) (ps0 : Expr) : SFlags → MetaM Expr
  | .orig => pure ps0
  | .addSubOr w op a b prev => do
    let r ← mkAppM ``evalAddSub #[toExpr w, toExpr op, ← prettyC leaves a, ← prettyC leaves b,
      ← mkAppOptM ``Option.none #[mkConst ``Bool]]
    mkAppM ``Option.getD #[← mkAppM ``Prod.snd #[r], ← prettyFlags leaves ps0 prev]
  | .logicalOr w op a b prev => do
    let r ← mkAppM ``evalLogical #[toExpr w, toExpr op, ← prettyC leaves a, ← prettyC leaves b,
      mkConst ``PState.zero]
    mkAppM ``Option.getD #[← mkAppM ``Prod.snd #[r], ← prettyFlags leaves ps0 prev]

/-- Pretty non-doubleword value. -/
def prettyN (leaves : RState) (w : CW) : NVal → MetaM Expr
  | .leaf i => return match w with
    | .b8 => leaves.leaves8[i]!
    | .b16 => leaves.leaves16[i]!
    | .b32 => leaves.leaves32[i]!
    | .b128 => leaves.leaves128[i]!
  | .trunc e => do mkAppM ``BitVec.truncate #[mkNatLit w.bits, ← prettyC leaves e]
  | .v128 v => do
    let ve ← prettyV128 leaves v
    match w with
    | .b128 => return ve
    | _ => mkAppM ``BitVec.truncate #[mkNatLit w.bits, ve]

/-- The points-to constant of a non-doubleword width and read-only flag. -/
def cwPtConst : CW → Bool → Name
  | .b8, false => ``pointsTo8
  | .b16, false => ``pointsTo16
  | .b32, false => ``pointsTo32
  | .b128, false => ``pointsTo128
  | .b8, true => ``pointsTo8RO
  | .b16, true => ``pointsTo16RO
  | .b32, true => ``pointsTo32RO
  | .b128, true => ``pointsTo128RO

/-- If `bE` is `X + c₁` with `c₁` a 64-bit literal, return `X + (c₁ + o)` (folded literal) and a
    proof of `bE + o = X + (c₁ + o)` (by `BitVec.add_assoc`; the literal fold is definitional). -/
def pcAt (bE : Expr) (o : BitVec 64) : MetaM (Option (Expr × Expr)) := do
  let bE' ← instantiateMVars bE
  unless bE'.isAppOfArity ``HAdd.hAdd 6 do return none
  let x := bE'.getArg! 4
  let some (64, c1) ← evalBitVecLit? (bE'.getArg! 5) | return none
  let norm ← mkAppM ``HAdd.hAdd #[x, bvLit 64 ((c1 + o.toNat) % 2 ^ 64)]
  let assoc ← mkAppM ``BitVec.add_assoc #[x, bE'.getArg! 5, bvLit 64 o.toNat]
  let ty ← mkEq (← mkAppM ``HAdd.hAdd #[bE, bvLit 64 o.toNat]) norm
  return some (norm, ← mkExpectedTypeHint assoc ty)

/-- Evaluate a closed `BitVec` expression to `(width, value)` structurally in `MetaM`,
    unfolding transparent `abbrev`/`def` constants without expanding `BitVec` arithmetic into
    unary `Nat` recursion. -/
partial def evalGroundBv? (e : Expr) (fuel : Nat := 32) : MetaM (Option (Nat × Nat)) := do
  if let some wv := evalSyntaxBvLit? e then return some wv
  if fuel == 0 || e.hasFVar || e.hasMVar then return none
  let e := (← instantiateMVars e).consumeMData
  if let some wv := evalSyntaxBvLit? e then return some wv
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if let (some (w1, v1), some (w2, v2)) :=
        (← evalGroundBv? (e.getArg! 4) (fuel - 1), ← evalGroundBv? (e.getArg! 5) (fuel - 1)) then
      if w1 == w2 then return some (w1, (v1 + v2) % (1 <<< w1))
  if e.isAppOfArity ``BitVec.add 3 then
    if let (some w, some (_, v1), some (_, v2)) :=
        (← evalNatLit? (e.getArg! 0),
         ← evalGroundBv? (e.getArg! 1) (fuel - 1),
         ← evalGroundBv? (e.getArg! 2) (fuel - 1)) then
      return some (w, (v1 + v2) % (1 <<< w))
  if e.isAppOfArity ``HSub.hSub 6 then
    if let (some (w1, v1), some (w2, v2)) :=
        (← evalGroundBv? (e.getArg! 4) (fuel - 1), ← evalGroundBv? (e.getArg! 5) (fuel - 1)) then
      if w1 == w2 then
        let m := 1 <<< w1
        return some (w1, (v1 + m - (v2 % m)) % m)
  if e.isAppOfArity ``BitVec.sub 3 then
    if let (some w, some (_, v1), some (_, v2)) :=
        (← evalNatLit? (e.getArg! 0),
         ← evalGroundBv? (e.getArg! 1) (fuel - 1),
         ← evalGroundBv? (e.getArg! 2) (fuel - 1)) then
      let m := 1 <<< w
      return some (w, (v1 + m - (v2 % m)) % m)
  if e.isAppOfArity ``HMul.hMul 6 then
    if let (some (w1, v1), some (w2, v2)) :=
        (← evalGroundBv? (e.getArg! 4) (fuel - 1), ← evalGroundBv? (e.getArg! 5) (fuel - 1)) then
      if w1 == w2 then return some (w1, (v1 * v2) % (1 <<< w1))
  if e.isAppOfArity ``BitVec.mul 3 then
    if let (some w, some (_, v1), some (_, v2)) :=
        (← evalNatLit? (e.getArg! 0),
         ← evalGroundBv? (e.getArg! 1) (fuel - 1),
         ← evalGroundBv? (e.getArg! 2) (fuel - 1)) then
      return some (w, (v1 * v2) % (1 <<< w))
  if e.isAppOfArity ``HAnd.hAnd 6 then
    if let (some (w1, v1), some (w2, v2)) :=
        (← evalGroundBv? (e.getArg! 4) (fuel - 1), ← evalGroundBv? (e.getArg! 5) (fuel - 1)) then
      if w1 == w2 then return some (w1, (v1 &&& v2) % (1 <<< w1))
  if e.isAppOfArity ``HOr.hOr 6 then
    if let (some (w1, v1), some (w2, v2)) :=
        (← evalGroundBv? (e.getArg! 4) (fuel - 1), ← evalGroundBv? (e.getArg! 5) (fuel - 1)) then
      if w1 == w2 then return some (w1, (v1 ||| v2) % (1 <<< w1))
  if e.isAppOfArity ``HXor.hXor 6 then
    if let (some (w1, v1), some (w2, v2)) :=
        (← evalGroundBv? (e.getArg! 4) (fuel - 1), ← evalGroundBv? (e.getArg! 5) (fuel - 1)) then
      if w1 == w2 then return some (w1, (v1 ^^^ v2) % (1 <<< w1))
  if e.isAppOfArity ``Neg.neg 3 then
    if let some (w, v) ← evalGroundBv? (e.getArg! 2) (fuel - 1) then
      let m := 1 <<< w
      return some (w, (m - (v % m)) % m)
  if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 || e.isAppOfArity ``HShiftRight.hShiftRight 6 then
    let isL := e.isAppOfArity ``HShiftLeft.hShiftLeft 6
    if let some (w, v) ← evalGroundBv? (e.getArg! 4) (fuel - 1) then
      let amtTy := (e.getArg! 1).consumeMData
      let amt? ←
        if amtTy.isConstOf ``Nat then evalNatLit? (e.getArg! 5)
        else if amtTy.isAppOfArity ``BitVec 1 then
          pure ((← evalGroundBv? (e.getArg! 5) (fuel - 1)).map (·.2))
        else pure none
      if let some amt := amt? then
        return some (w, (if isL then v <<< amt else v >>> amt) % (1 <<< w))
  if e.isAppOfArity ``BitVec.zeroExtend 3 || e.isAppOfArity ``BitVec.truncate 3 ||
      e.isAppOfArity ``BitVec.setWidth 3 then
    if let (some w, some (_, v)) :=
        (← evalNatLit? (e.getArg! 1), ← evalGroundBv? (e.getArg! 2) (fuel - 1)) then
      return some (w, v % (1 <<< w))
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let (some w, some v) :=
        (← evalNatLit? (e.getArg! 0), ← evalNatLit? (e.getArg! 1)) then
      return some (w, v % (1 <<< w))
  if let some e' ← unfoldDefinition? e then
    if e' != e then
      if let some wv ← evalGroundBv? e' (fuel - 1) then
        return some wv
  evalBitVecLit? e

/-- Evaluate a closed `BitVec 64` expression to its `Nat` value (`< 2^64`). -/
def evalGroundBv64? (e : Expr) : MetaM (Option Nat) := do
  match ← evalGroundBv? e with
  | some (64, v) => return some v
  | _ => return none

/-- Normalize named offset `abbrev`s / closed `BitVec 64` subexpressions in a PC expression `e`
    (such as `entry + myOff` or `(entry + myOff) + 4#64`) to a syntactic `BitVec 64` numeral
    offset `entry + bvLit 64 c`, returning `(eNorm, prf : e = eNorm)` when any rewrite happened. -/
partial def normalizePcExpr (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e := (← instantiateMVars e).consumeMData
  if (evalSyntaxBvLit? e).isSome then return none
  if !e.hasFVar && !e.hasMVar then
    let some c ← evalGroundBv64? e | return none
    let lit := bvLit 64 c
    if e == lit then return none
    let some hEq ← (try some <$> mkKernelDecideEqProof e lit catch _ => pure none) | return none
    return some (lit, hEq)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let lhs := (e.getArg! 4).consumeMData
    let rhs := (e.getArg! 5).consumeMData
    let (lhs', hLhs?) ← match ← normalizePcExpr lhs with
      | some (l', h) => pure (l', some h)
      | none => pure (lhs, none)
    let (rhs', hRhs?) ←
      if (evalSyntaxBvLit? rhs).isSome then pure (rhs, none)
      else match ← evalGroundBv64? rhs with
        | some c =>
          let lit := bvLit 64 c
          match ← (try some <$> mkKernelDecideEqProof rhs lit catch _ => pure none) with
          | some h => pure (lit, some h)
          | none => pure (rhs, none)
        | none => pure (rhs, none)
    let (e1, h1?) ← match hLhs?, hRhs? with
      | none, none => pure (e, none)
      | some hL, some hR =>
        let e1 := mkAppN e.getAppFn (e.getAppArgs.set! 4 lhs' |>.set! 5 rhs')
        let hL1 ← mkCongrArg (mkAppN e.getAppFn #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3]) hL
        pure (e1, some (← mkCongr hL1 hR))
      | some hL, none =>
        let e1 := mkAppN e.getAppFn (e.getAppArgs.set! 4 lhs')
        let hL1 ← mkCongrArg (mkAppN e.getAppFn #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3]) hL
        pure (e1, some (← mkCongrFun hL1 rhs))
      | none, some hR =>
        let e1 := mkAppN e.getAppFn (e.getAppArgs.set! 5 rhs')
        let h1 ← mkCongrArg (mkAppN e.getAppFn (e.getAppArgs.take 5)) hR
        pure (e1, some h1)
    if lhs'.isAppOfArity ``HAdd.hAdd 6 then
      let off0 := (lhs'.getArg! 5).consumeMData
      if let (some (64, _), some (64, c1)) := (evalSyntaxBvLit? off0, evalSyntaxBvLit? rhs') then
        if let some (e2, h2) ← pcAt lhs' (BitVec.ofNat 64 c1) then
          let hTotal ← match h1? with
            | some h1 => mkEqTrans h1 h2
            | none => pure h2
          return some (e2, hTotal)
    return h1?.map (e1, ·)
  if e.isAppOfArity ``HSub.hSub 6 then
    let rhs := (e.getArg! 5).consumeMData
    if (evalSyntaxBvLit? rhs).isNone then
      if let some c ← evalGroundBv64? rhs then
        let lit := bvLit 64 c
        if let some hR ← (try some <$> mkKernelDecideEqProof rhs lit catch _ => pure none) then
          let e1 := mkAppN e.getAppFn (e.getAppArgs.set! 5 lit)
          let h1 ← mkCongrArg (mkAppN e.getAppFn (e.getAppArgs.take 5)) hR
          return some (e1, h1)
  return none

/-! ## Instruction Fetch Indexing -/

partial def flatConjuncts (ty prf : Expr) (acc : Array (Expr × Expr) := #[]) :
    MetaM (Array (Expr × Expr)) := do
  let ty ← instantiateMVars ty
  let tyC := ty.consumeMData
  if tyC.isAppOfArity ``And 2 then
    let a := tyC.getArg! 0
    let b := tyC.getArg! 1
    let pa := mkApp3 (mkConst ``And.left) a b prf
    let pb := mkApp3 (mkConst ``And.right) a b prf
    let acc ← flatConjuncts a pa acc
    flatConjuncts b pb acc
  else
    return acc.push (ty, prf)

structure FetchKey where
  prog : Expr
  pc : Expr
  deriving BEq, Hashable

structure FetchOffKey where
  prog : Expr
  base : Expr
  off : UInt64
  deriving BEq, Hashable

/-- Pre-indexed local `prog.fetch pc = some inst` hypotheses built once at `sym_block` entry
    so instruction fetches hit in $O(1)$ without scanning the local context per step. -/
structure FetchIndex where
  exact : Std.HashMap FetchKey (Expr × Expr) := {}
  byOff : Std.HashMap FetchOffKey (Expr × Expr × Expr) := {}

/-- Scan `getLCtx` once to index all local `prog.fetch pc = some inst` hypotheses. -/
def buildFetchIndex : MetaM FetchIndex := do
  let mut idx : FetchIndex := {}
  let insertEntry (idx : FetchIndex) (progE pcE instE prf : Expr) : FetchIndex :=
    let idx := { idx with exact := idx.exact.insert { prog := progE, pc := pcE } (instE, prf) }
    if pcE.isAppOfArity ``HAdd.hAdd 6 then
      let bE := (pcE.getArg! 4).consumeMData
      let offE := (pcE.getArg! 5).consumeMData
      match evalSyntaxBvLit? offE with
      | some (64, off) =>
        { idx with
          byOff := idx.byOff.insert { prog := progE, base := bE, off := off.toUInt64 }
            (pcE, instE, prf) }
      | _ => idx
    else
      { idx with
        byOff := idx.byOff.insert { prog := progE, base := pcE, off := 0 } (pcE, instE, prf) }
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for (cTy, cPrf) in ← flatConjuncts d.type d.toExpr do
      let some (_, lhs, rhs) := cTy.consumeMData.eq? | continue
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      unless lhs.isAppOfArity ``Program.fetch 2 && rhs.isAppOfArity ``Option.some 2 do continue
      let progE := (lhs.getArg! 0).consumeMData
      let pcE := (lhs.getArg! 1).consumeMData
      let instE := rhs.getArg! 1
      let prf := cPrf
      idx := insertEntry idx progE pcE instE prf
      if let some (pcNorm, hPc) ← normalizePcExpr pcE then
        let hFetch ← mkCongrArg (mkApp (mkConst ``Program.fetch) progE) hPc
        let prfNorm ← mkEqTrans (← mkEqSymm hFetch) prf
        idx := insertEntry idx progE pcNorm instE prfNorm
  return idx

private def lookupFetchIndex (fidx : FetchIndex) (progExpr pcCand : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let pKey := progExpr.consumeMData
  let pcKey := pcCand.consumeMData
  if let some (instE, prf) := fidx.exact.get? { prog := pKey, pc := pcKey } then
    return some (instE, prf)
  if pcKey.isAppOfArity ``HAdd.hAdd 6 then
    let bE := (pcKey.getArg! 4).consumeMData
    let offE := (pcKey.getArg! 5).consumeMData
    if let some (64, off) := evalSyntaxBvLit? offE then
      if let some (pcIdx, instE, prf) :=
          fidx.byOff.get? { prog := pKey, base := bE, off := off.toUInt64 } then
        if pcIdx == pcKey then
          return some (instE, prf)
        else if off == 0 && pcIdx == bE then
          let hZero ← mkAppM ``BitVec.add_zero #[bE]
          let hCongr ← mkCongrArg (mkApp (mkConst ``Program.fetch) progExpr) hZero
          return some (instE, ← mkEqTrans hCongr prf)
        else if ← isDefEq pcCand pcIdx then
          return some (instE, prf)
  if let some (pcIdx, instE, prf) :=
      fidx.byOff.get? { prog := pKey, base := pcKey, off := 0 } then
    if pcIdx == pcKey then
      return some (instE, prf)
    else if pcIdx.isAppOfArity ``HAdd.hAdd 6 then
      let hZero ← mkAppM ``BitVec.add_zero #[pcCand]
      let hCongr ← mkCongrArg (mkApp (mkConst ``Program.fetch) progExpr) (← mkEqSymm hZero)
      return some (instE, ← mkEqTrans hCongr prf)
    else if ← isDefEq pcCand pcIdx then
      return some (instE, prf)
  return none

/-- Fetch the instruction at `pc` using the $O(1)$ pre-indexed local fetch map first, falling back
    to `hasCode` / `wp_assumption` / ground `rfl`. Returns `(instExpr, proof)`. -/
def fetchAt (fidx : FetchIndex) (progExpr pcExpr : Expr) : TacticM (Option (Expr × Expr)) := do
  if let some res ← lookupFetchIndex fidx progExpr pcExpr then
    return some res
  if let some (pcNorm, hPc) ← normalizePcExpr pcExpr then
    if let some (instE, prfNorm) ← lookupFetchIndex fidx progExpr pcNorm then
      let hFetch ← mkCongrArg (mkApp (mkConst ``Program.fetch) progExpr) hPc
      return some (instE, ← mkEqTrans hFetch prfNorm)
  let saved ← getGoals
  let instMVar ← mkFreshExprMVar (mkConst ``Instr)
  let someInst ← mkAppM ``Option.some #[instMVar]
  let fetchGoalTy ← mkEq (mkApp2 (mkConst ``Program.fetch) progExpr pcExpr) someInst
  let fetchGoal ← mkFreshExprMVar fetchGoalTy
  setGoals [fetchGoal.mvarId!]
  -- Nested `else do` blocks keep the fallbacks lazy (conditions of `if ... else if <- c`
  -- are hoisted before the `if`).
  let ok ←
    if ← tryCloseFetchFromHasCode then pure true
    else do
    if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_assumption))) then
      pure true
    else do
    if (← evalBitVecLit? pcExpr).isSome || (← evalPCBaseOff? pcExpr).isSome then
      tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (
        (conv => lhs; simp (config := { decide := true }) only [arm64_norm]);
        rfl))))
    else pure false
  setGoals saved
  if ok then return some (← instantiateMVars instMVar, ← instantiateMVars fetchGoal)
  else return none

/-! ## Obligation Discharge -/

register_option symBlock.probeBudget : Nat := {
  defValue := 300
  descr := "heartbeat budget (in thousands) for each advisor attempt to discharge an obligation \
    or decide a branch (0 = no limit beyond `maxHeartbeats`). A failed attempt only shortens the \
    block."
}

partial def splitAndHyps (g : MVarId) (skip : Std.HashSet FVarId := {}) : MetaM MVarId := do
  let some fvarId ← g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail || skip.contains d.fvarId then continue
      let ty ← instantiateMVars d.type
      if ty.consumeMData.isAppOfArity ``And 2 then
        return some d.fvarId
    return none
  | return g
  try
    let #[sub] ← g.cases fvarId
      | return g
    splitAndHyps sub.mvarId skip
  catch _ =>
    splitAndHyps g (skip.insert fvarId)

private partial def isHeavyHyp (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  ty.isAppOf ``SepProp.Satisfies ||
  ty.isAppOf ``Program.hasCode ||
  ty.isAppOf ``Program.hasWords ||
  ty.isAppOf ``Program.codeAt ||
  ty.isAppOf ``Arm64.DisjointRegions ||
  ty.isAppOf ``Arm64.Memory.Disjoint64 ||
  ty.isAppOf ``Arm64.Memory.Disjoint128 ||
  ty.isAppOf ``Arm64.CalleeSavedPreserved ||
  ty.isAppOf ``Arm64.CallingConventionPreserved ||
  ty.isAppOf ``Arm64.StackPreserved ||
  ty.isAppOf ``Arm64.SubroutinePost ||
  ty.isAppOf ``Arm64.subroutine_ok ||
  ty.isAppOf ``Program.subroutineOk ||
  ty.isAppOf ``ProofLib.SepWP ||
  ty.isAppOf ``ProofLib.SepWPp ||
  (if ty.isAppOfArity ``Not 1 then isHeavyHyp (ty.getArg! 0) else false) ||
  match ty.eq? with
  | some (_, lhs, rhs) =>
    let lhs := lhs.consumeMData
    let rhs := rhs.consumeMData
    lhs.isAppOfArity ``Program.fetch 2 || lhs.isAppOfArity ``Program.fnAddr 2 ||
    rhs.isAppOfArity ``Program.fnAddr 2 || lhs.isAppOfArity ``Program.externAt? 2 ||
    lhs.isAppOfArity ``State.pc 1 || lhs.isAppOfArity ``State.status 1
  | none => false

private def clearIrrelevantHyps (g : MVarId) : MetaM MVarId := do
  let fvars ← g.withContext do
    let mut out : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if isHeavyHyp ty then
        out := out.push d.fvarId
    return out
  let mut gCur := g
  for fv in fvars.reverse do
    gCur ← gCur.tryClear fv
  return gCur

private def unwrapProdSnd? (s : Expr) : Option Expr :=
  let s := s.consumeMData
  match s with
  | .proj ``Prod 1 awc => some awc
  | _ => if s.isAppOfArity ``Prod.snd 3 then some (s.getArg! 2) else none

private def unwrapPStateProj? (e : Expr) : Option (Bool × Expr) :=
  let e := e.consumeMData
  match e with
  | .proj ``Arm64.PState 2 s => (unwrapProdSnd? s).map fun awc => (false, awc)
  | .proj ``Arm64.PState 3 s => (unwrapProdSnd? s).map fun awc => (true, awc)
  | _ =>
    if e.isAppOfArity ``Arm64.PState.c 1 then
      (unwrapProdSnd? (e.getArg! 0)).map fun awc => (false, awc)
    else if e.isAppOfArity ``Arm64.PState.v 1 then
      (unwrapProdSnd? (e.getArg! 0)).map fun awc => (true, awc)
    else
      none

private def matchAwcProj? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (isV, awcRaw) := unwrapPStateProj? e | return none
  let awc := awcRaw.consumeMData
  let subInner? (b : Expr) : Option Expr :=
    let bC := b.consumeMData
    if bC.isAppOfArity ``Complement.complement 3 then some (bC.getArg! 2)
    else if bC.isAppOfArity ``BitVec.not 2 then some (bC.getArg! 1)
    else none
  if awc.isAppOfArity ``Arm64.AddWithCarry64 3 then
    let a := awc.getArg! 0
    let b := awc.getArg! 1
    let carry := awc.getArg! 2 |>.consumeMData
    if !isV && carry.isConstOf ``Bool.false then
      return some (← mkAppM ``BitVec.uaddOverflow #[a, b],
        mkApp2 (mkConst ``ProofLib.SymBlock.adds64_c) a b)
    else if isV && carry.isConstOf ``Bool.false then
      return some (← mkAppM ``BitVec.saddOverflow #[a, b],
        mkApp2 (mkConst ``ProofLib.SymBlock.adds64_v) a b)
    else if isV && carry.isConstOf ``Bool.true then
      if let some bInner := subInner? b then
        return some (← mkAppM ``BitVec.ssubOverflow #[a, bInner],
          mkApp2 (mkConst ``ProofLib.SymBlock.subs64_v) a bInner)
    return none
  else if awc.isAppOfArity ``Arm64.AddWithCarry32 3 then
    let a := awc.getArg! 0
    let b := awc.getArg! 1
    let carry := awc.getArg! 2 |>.consumeMData
    if !isV && carry.isConstOf ``Bool.false then
      return some (← mkAppM ``BitVec.uaddOverflow #[a, b],
        mkApp2 (mkConst ``ProofLib.SymBlock.adds32_c) a b)
    else if isV && carry.isConstOf ``Bool.false then
      return some (← mkAppM ``BitVec.saddOverflow #[a, b],
        mkApp2 (mkConst ``ProofLib.SymBlock.adds32_v) a b)
    else if isV && carry.isConstOf ``Bool.true then
      if let some bInner := subInner? b then
        return some (← mkAppM ``BitVec.ssubOverflow #[a, bInner],
          mkApp2 (mkConst ``ProofLib.SymBlock.subs32_v) a bInner)
    return none
  return none

private partial def rewriteAwcInBool (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some res ← matchAwcProj? e then
    return some res
  let eC := e.consumeMData
  if eC.isAppOfArity ``not 1 then
    if let some (a', ha) ← rewriteAwcInBool (eC.getArg! 0) then
      return some (mkApp (mkConst ``not) a', ← mkCongrArg (mkConst ``not) ha)
    return none
  if eC.isAppOfArity ``and 2 || eC.isAppOfArity ``or 2 then
    let fn := eC.getAppFn
    let a := eC.getArg! 0
    let b := eC.getArg! 1
    let ra? ← rewriteAwcInBool a
    let rb? ← rewriteAwcInBool b
    match ra?, rb? with
    | none, none => return none
    | some (a', ha), none =>
      let h1 ← mkCongrArg fn ha
      return some (mkApp2 fn a' b, ← mkCongrFun h1 b)
    | none, some (b', hb) =>
      return some (mkApp2 fn a b', ← mkCongrArg (mkApp fn a) hb)
    | some (a', ha), some (b', hb) =>
      let h1 ← mkCongrArg fn ha
      return some (mkApp2 fn a' b', ← mkCongr h1 hb)
  return none

private def rewriteAwcGoal (g : MVarId) : MetaM MVarId := do
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := tgt.eq? | return g
    let some (lhs', hl) ← rewriteAwcInBool lhs | return g
    let eqFn := tgt.appFn!.appFn!
    let h1 ← mkCongrArg eqFn hl
    let hTgt ← mkCongrFun h1 rhs
    g.replaceTargetEq (mkApp2 eqFn lhs' rhs) hTgt

private def tryAssumption (g : MVarId) : MetaM Bool :=
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let dTy ← instantiateMVars d.type
      if dTy == tgt || (← withReducible <| isDefEq dTy tgt) then
        g.assign (mkFVar d.fvarId)
        return true
    return false

private def isBoolEq (e : Expr) : Bool :=
  match e.consumeMData.eq? with
  | some (ty, _, _) => ty.consumeMData.isConstOf ``Bool
  | none => false

private def needsGoalSimp (e : Expr) : Bool :=
  (e.find? fun sub => match sub with
    | .const n _ =>
      n == ``Prod.snd || n == ``Arm64.PState.c || n == ``Arm64.PState.v ||
      n == ``Arm64.AddWithCarry64 || n == ``Arm64.AddWithCarry32 ||
      n == ``Arm64.evalLogical || n == ``Arm64.shiftVal ||
      n == ``Arm64.shift32 || n == ``Arm64.shift64 ||
      n == ``BitVec.getLsbD || n == ``BitVec.ofNatLT ||
      n == ``not || n == ``and || n == ``or ||
      n == ``BEq.beq || n == ``bne
    | _ => false).isSome

private def mkSimpCtxFor (decls : List Name) (thmsList : List Name) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for d in decls do
    thms ← thms.addDeclToUnfold d
  for n in thmsList do
    thms ← thms.addConst n
  Simp.mkContext (simpTheorems := #[thms])

private def arithDecls : List Name :=
  [``BitVec.uaddOverflow, ``BitVec.ult, ``BitVec.ule,
   ``BitVec.zeroExtend, ``BitVec.truncate]

private def arithThms : List Name :=
  [``BitVec.msb_eq_decide, ``BitVec.toNat_add, ``BitVec.toNat_sub,
   ``BitVec.ofNatLT_eq_ofNat,
   ``BitVec.toNat_ofNat, ``BitVec.toNat_setWidth,
   ``ge_iff_le, ``gt_iff_lt,
   ``Bool.not_true, ``Bool.not_false, ``Bool.not_eq_true, ``Bool.not_eq_false,
   ``Bool.and_true, ``Bool.true_and, ``Bool.and_false, ``Bool.false_and,
   ``Bool.or_true, ``Bool.true_or, ``Bool.or_false, ``Bool.false_or, ``Bool.not_not,
   ``Bool.false_eq_true, ``Bool.true_eq_false,
   ``Bool.or_eq_true, ``Bool.or_eq_false_iff,
   ``Bool.and_eq_true, ``Bool.and_eq_false_iff,
   ``decide_eq_true_eq, ``decide_eq_false_iff_not]

private def overflowDecls : List Name :=
  arithDecls ++ [``BitVec.slt, ``BitVec.sle]

private def overflowThms : List Name :=
  [``ProofLib.SymBlock.saddOverflow_64_eq, ``ProofLib.SymBlock.saddOverflow_32_eq,
   ``BitVec.ssubOverflow_eq, ``BitVec.toInt_eq_toNat_cond] ++ arithThms

private def relevantArithFVars (g : MVarId) (tgt : Expr) : MetaM (Array FVarId) :=
  g.withContext do
    let tgtHasReg := (tgt.find? fun sub => match sub with
      | .const n _ =>
        n == ``Arm64.State.readReg64 || n == ``Arm64.State.readVReg128 || n == ``Arm64.State.tpidrEl0
      | _ => false).isSome
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let dTy ← instantiateMVars d.type
      if !tgtHasReg then
        if let some (_, lhs, _) := dTy.consumeMData.eq? then
          let lhs := lhs.consumeMData
          if lhs.isAppOf ``Arm64.State.readReg64 ||
             lhs.isAppOf ``Arm64.State.readVReg128 ||
             lhs.isAppOf ``Arm64.State.tpidrEl0 then
            continue
      out := out.push d.fvarId
    return out

def proveByTactics (ty : Expr) : TacticM (Option Expr) := do
  let budget := symBlock.probeBudget.get (← getOptions)
  let tryProbe (tac : TacticM Unit) : TacticM Bool :=
    tryTacticCatchRuntimeBool do
      if budget == 0 then
        tac
      else
        withCurrHeartbeats <|
          withTheReader Core.Context (fun c => { c with maxHeartbeats := budget * 1000 }) tac
  let mv ← mkFreshExprMVar ty
  let gSplit ← rewriteAwcGoal (← clearIrrelevantHyps (← splitAndHyps mv.mvarId!))
  let saved ← getGoals
  setGoals [gSplit]
  let tgtAfter ← gSplit.withContext do instantiateMVars (← gSplit.getType)
  let hasAwc := (tgtAfter.find? fun e =>
    e.isConstOf ``Arm64.AddWithCarry64 || e.isConstOf ``Arm64.AddWithCarry32).isSome
  let attempt : TacticM Bool := do
    if ← tryAssumption gSplit then
      return true
    if !tgtAfter.hasFVar then
      if ← tryProbe do evalTactic (← `(tactic| decide)) then
        return true
    if !isBoolEq tgtAfter then
      if ← tryProbe do evalTactic (← `(tactic| (bv_lin; done))) then
        return true
    let mut gBase := gSplit
    if needsGoalSimp tgtAfter then
      let goalSimp := tryProbe do
        evalTactic (← `(tactic|
          simp only [Prod.snd, Arm64.PState.c, Arm64.PState.v,
            ProofLib.SymBlock.adds64_c, ProofLib.SymBlock.adds32_c,
            ProofLib.SymBlock.adds64_v, ProofLib.SymBlock.adds32_v,
            ProofLib.SymBlock.subs64_v, ProofLib.SymBlock.subs32_v,
            ProofLib.SymBlock.getLsbD_eq_testBit_toNat,
            BitVec.ofNatLT_eq_ofNat,
            Arm64.evalLogical, Arm64.shiftVal, Arm64.shift32, Arm64.shift64,
            Bool.not_true, Bool.not_false, Bool.not_eq_true, Bool.not_eq_false,
            Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and,
            Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.not_not,
            Bool.false_eq_true, Bool.true_eq_false,
            beq_self_eq_true, bne_self_eq_false]))
      if ← goalSimp then
        if (← getUnsolvedGoals).isEmpty then return true
        gBase ← getMainGoal
        if ← tryAssumption gBase then
          return true
        if !isBoolEq (← gBase.withContext do instantiateMVars (← gBase.getType)) then
          if ← tryProbe do evalTactic (← `(tactic| (bv_lin; done))) then
            return true
        setGoals [gBase]
        if ← tryProbe do evalTactic (← `(tactic| (wp_omega_bounded; done))) then
          return true
        if !hasAwc then
          setGoals [gBase]
          if ← tryProbe do evalTactic (← `(tactic| (bv_bits; done))) then
            return true
    setGoals [gBase]
    let fvars ← relevantArithFVars gBase tgtAfter
    let simpClosed ← tryProbe do
      let arithCtx ← mkSimpCtxFor arithDecls arithThms
      match (← simpGoal gBase arithCtx (fvarIdsToSimp := fvars)).1 with
      | none => pure ()
      | some (_, gSimp) =>
        setGoals [gSimp]
        evalTactic (← `(tactic| first | omega | (wp_omega_bounded; done)))
    if simpClosed then
      return true
    let hasSignedOverflow ← gBase.withContext do
      let check (e : Expr) : Bool :=
        (e.find? fun c =>
          c.isConstOf ``BitVec.saddOverflow || c.isConstOf ``BitVec.ssubOverflow).isSome
      if check tgtAfter then return true
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if check (← instantiateMVars d.type) then return true
      return false
    if hasSignedOverflow then
      setGoals [gBase]
      let ssubClosed ← tryProbe do
        let ssubOnlyCtx ← mkSimpCtxFor []
          [``BitVec.ssubOverflow_eq, ``BitVec.msb_eq_decide,
           ``Bool.not_true, ``Bool.not_false, ``Bool.not_eq_true, ``Bool.not_eq_false,
           ``Bool.and_true, ``Bool.true_and, ``Bool.and_false, ``Bool.false_and,
           ``Bool.or_true, ``Bool.true_or, ``Bool.or_false, ``Bool.false_or, ``Bool.not_not,
           ``Bool.false_eq_true, ``Bool.true_eq_false,
           ``Bool.or_eq_true, ``Bool.or_eq_false_iff,
           ``Bool.and_eq_true, ``Bool.and_eq_false_iff,
           ``decide_eq_true_eq, ``decide_eq_false_iff_not]
        match (← simpGoal gBase ssubOnlyCtx (fvarIdsToSimp := fvars)).1 with
        | none => pure ()
        | some (_, gSimp) =>
          setGoals [gSimp]
          evalTactic (← `(tactic| (bv_arith; done)))
      if ssubClosed then
        return true
      setGoals [gBase]
      let ovfClosed ← tryProbe do
        let ovfCtx ← mkSimpCtxFor overflowDecls overflowThms
        match (← simpGoal gBase ovfCtx (fvarIdsToSimp := fvars)).1 with
        | none => pure ()
        | some (_, gSimp) =>
          setGoals [gSimp]
          evalTactic (← `(tactic| first | omega | (wp_omega_bounded; done)))
      if ovfClosed then
        return true
    setGoals [gBase]
    if ← tryProbe do evalTactic (← `(tactic| (wp_omega_bounded; done))) then
      return true
    if !hasAwc then
      setGoals [gBase]
      if ← tryProbe do
          evalTactic (← `(tactic|
            (try simp_all only [BitVec.uaddOverflow_eq]); first | (bv_bits; done) | (bv_solve; done))) then
        return true
    return false
  let ok ← tryTacticCatchRuntimeBool do
    if budget == 0 then
      if !(← attempt) then throwError "proveByTactics failed"
    else
      withCurrHeartbeats <|
        withTheReader Core.Context (fun c => { c with maxHeartbeats := budget * 4 * 1000 }) do
          if !(← attempt) then throwError "proveByTactics failed"
  setGoals saved
  if ok then return some (← instantiateMVars mv) else return none

private def mkAligned16Prop (xE : Expr) : MetaM Expr := do
  mkEq (← mkAppM ``BEq.beq #[← mkAppM ``HAnd.hAnd #[xE, bvLit 64 15], bvLit 64 0]) (toExpr true)

private partial def proveAligned16? (aE : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let aE ← instantiateMVars aE
  let tgtTy ← mkAligned16Prop aE
  if !aE.hasFVar && !aE.hasMVar then
    if let some v ← evalGroundBv64? aE then
      if v % 16 == 0 then
        let lhs ← mkAppM ``BEq.beq #[← mkAppM ``HAnd.hAnd #[aE, bvLit 64 15], bvLit 64 0]
        if let some h ← (try some <$> mkKernelDecideEqProof lhs (toExpr true) catch _ => pure none) then
          return some (← mkExpectedTypeHint h tgtTy)
  let mut conjs : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    conjs ← flatConjuncts d.type d.toExpr conjs
  for (ty, prf) in conjs do
    let tyC := ty.consumeMData
    if let some (_, lhs, rhs) := tyC.eq? then
      let lhsC := lhs.consumeMData
      let rhsC := rhs.consumeMData
      if rhsC.isConstOf ``Bool.true then
        if lhsC.isAppOfArity ``Arm64.State.spAligned 1 then
          let sSp := mkApp (mkConst ``Arm64.State.sp) (lhsC.getArg! 0)
          if ← isDefEq sSp aE then
            return some (← mkExpectedTypeHint prf tgtTy)
        if lhsC.isAppOfArity ``BEq.beq 4 && (← evalGroundBv64? (lhsC.getArg! 3)) == some 0 then
          let andC := (lhsC.getArg! 2).consumeMData
          if andC.isAppOfArity ``HAnd.hAnd 6 && (← evalGroundBv64? (andC.getArg! 5)) == some 15 then
            if ← isDefEq (andC.getArg! 4) aE then
              return some (← mkExpectedTypeHint prf tgtTy)
      if (← evalGroundBv64? rhsC) == some 0 then
        if lhsC.isAppOfArity ``HAnd.hAnd 6 && (← evalGroundBv64? (lhsC.getArg! 5)) == some 15 then
          let x := lhsC.getArg! 4
          if ← isDefEq x aE then
            let iffPrf ← mkAppOptM ``beq_iff_eq #[none, none, none, some lhsC, some rhsC]
            let beqPrf ← mkAppM ``Iff.mpr #[iffPrf, prf]
            return some (← mkExpectedTypeHint beqPrf tgtTy)
  if let some (aNorm, hEq) ← normalizePcExpr aE then
    if let some pfNorm ← proveAligned16? aNorm (fuel - 1) then
      let fn ← withLocalDeclD `z (mkApp (mkConst ``BitVec) (mkNatLit 64)) fun z => do
        mkLambdaFVars #[z] (← mkAligned16Prop z)
      let hPropEq ← mkCongrArg fn hEq
      return some (← mkEqMPR hPropEq pfNorm)
  let aC := aE.consumeMData
  if aC.isAppOfArity ``HAdd.hAdd 6 || aC.isAppOfArity ``HSub.hSub 6 then
    let isSub := aC.isAppOfArity ``HSub.hSub 6
    let x := aC.getArg! 4
    let c := aC.getArg! 5
    if let some cVal ← evalGroundBv64? c then
      if cVal % 16 == 0 then
        let hcLhs ← mkAppM ``BEq.beq #[← mkAppM ``HAnd.hAnd #[c, bvLit 64 15], bvLit 64 0]
        if let some hc ← (try some <$> mkKernelDecideEqProof hcLhs (toExpr true) catch _ => pure none) then
          if let some hx ← proveAligned16? x (fuel - 1) then
            let thm := if isSub then ``ProofLib.SymBlock.aligned16_sub else ``ProofLib.SymBlock.aligned16_add
            let pf := mkApp4 (mkConst thm) x c hc hx
            return some (← mkExpectedTypeHint pf tgtTy)
  for (ty, prf) in conjs do
    if let some (eqTy, lhs, rhs) := ty.consumeMData.eq? then
      let eqTyC := eqTy.consumeMData
      if eqTyC.isAppOfArity ``BitVec 1 && evalNatLitPure? (eqTyC.getArg! 0) == some 64 then
        if (← isDefEq lhs aE) && !(← isDefEq rhs aE) then
          if let some pfRhs ← proveAligned16? rhs (fuel - 1) then
            let fn ← withLocalDeclD `z (mkApp (mkConst ``BitVec) (mkNatLit 64)) fun z => do
              mkLambdaFVars #[z] (← mkAligned16Prop z)
            let hPropEq ← mkCongrArg fn prf
            return some (← mkEqMPR hPropEq pfRhs)
        else if (← isDefEq rhs aE) && !(← isDefEq lhs aE) then
          if let some pfLhs ← proveAligned16? lhs (fuel - 1) then
            let fn ← withLocalDeclD `z (mkApp (mkConst ``BitVec) (mkNatLit 64)) fun z => do
              mkLambdaFVars #[z] (← mkAligned16Prop z)
            let hPropEq ← mkCongrArg fn (← mkEqSymm prf)
            return some (← mkEqMPR hPropEq pfLhs)
  return none

/-- Pretty statement of an obligation (definitionally equal to `SProp.denote env p`). -/
def prettyObl (leaves : RState) : SProp → MetaM Expr
  | .eq a b => do mkEq (← prettyC leaves a) (← prettyC leaves b)
  | .ne a b => do mkAppM ``Ne #[← prettyC leaves a, ← prettyC leaves b]
  | .ult a b v => do mkEq (← mkAppM ``BitVec.ult #[← prettyC leaves a, ← prettyC leaves b]) (toExpr v)
  | .ule a b v => do mkEq (← mkAppM ``BitVec.ule #[← prettyC leaves a, ← prettyC leaves b]) (toExpr v)
  | .slt a b v => do mkEq (← mkAppM ``BitVec.slt #[← prettyC leaves a, ← prettyC leaves b]) (toExpr v)
  | .sle a b v => do mkEq (← mkAppM ``BitVec.sle #[← prettyC leaves a, ← prettyC leaves b]) (toExpr v)
  | .aligned16 a => do mkAligned16Prop (← prettyC leaves a)
  | .cond c v => do mkEq (← prettyCond leaves c) (toExpr v)

/-- Try to prove obligation `p`; uses kernel `Eq.refl` when the advisor predicts defeq,
    sub-millisecond reflective linear normalization (`ProofLib.BV.Lin.proveEq?` / `proveNe?`) for
    associative/commutative `BitVec` (in)equalities, and bounded tactics as fallback. -/
def proveObl (leaves : RState) (p : SProp) : TacticM (Option Expr) := do
  match p with
  | .eq a b =>
    if defeqPred a b then
      return some (← mkEqRefl (← prettyC leaves a))
    let aE ← prettyC leaves a
    let bE ← prettyC leaves b
    if let some pf ← ProofLib.BV.Lin.proveEq? aE bE then
      return some (← mkExpectedTypeHint pf (← mkEq aE bE))
  | .ne a b =>
    let aE ← prettyC leaves a
    let bE ← prettyC leaves b
    if let some pf ← ProofLib.BV.Lin.proveNe? aE bE then
      return some (← mkExpectedTypeHint pf (← mkAppM ``Ne #[aE, bE]))
  | .aligned16 a =>
    let aE ← prettyC leaves a
    if let some pf ← proveAligned16? aE then
      return some pf
  | _ => pure ()
  proveByTactics (← prettyObl leaves p)

/-! ## Hint Selection -/

/-- Match any 64-bit cell (mutable or read-only) at address `ea`. -/
def findCell (cells : List Cell) (ea : SExpr) : Option Nat :=
  let cea := matchCanon ea
  cells.findIdx? fun c => match c with
    | .pt64 _ a _ => a == ea || matchCanon a == cea
    | _ => false

/-- Match a writable (`ro = false`) 64-bit cell at address `ea`. -/
def findCellMut (cells : List Cell) (ea : SExpr) : Option Nat :=
  let cea := matchCanon ea
  cells.findIdx? fun c => match c with
    | .pt64 false a _ => a == ea || matchCanon a == cea
    | _ => false

/-- Match any non-doubleword cell (mutable or read-only) of width `w` at address `ea`. -/
def findCellN (cells : List Cell) (w : CW) (ea : SExpr) : Option Nat :=
  let cea := matchCanon ea
  cells.findIdx? fun c => match c with
    | .ptN w' _ a _ => w' == w && (a == ea || matchCanon a == cea)
    | _ => false

/-- Match a writable (`ro = false`) non-doubleword cell of width `w` at address `ea`. -/
def findCellNMut (cells : List Cell) (w : CW) (ea : SExpr) : Option Nat :=
  let cea := matchCanon ea
  cells.findIdx? fun c => match c with
    | .ptN w' false a _ => w' == w && (a == ea || matchCanon a == cea)
    | _ => false

/-- True if `cells` contains a read-only (`ro = true`) cell at address `ea` (for diagnostics). -/
def hasReadOnlyCellAt (cells : List Cell) (ea : SExpr) : Bool :=
  let cea := matchCanon ea
  cells.any fun c => match c with
    | .pt64 true a _ => a == ea || matchCanon a == cea
    | .ptN _ true a _ => a == ea || matchCanon a == cea
    | _ => false

def chooseHint (base : SExpr) (leaves : RState) (ss : SState) (op : MOp) (forced : List Bool) :
    TacticM (Option (Hint × List Bool × Option (Array Expr))) := do
  match op with
  | .ldr .W64 .X64 _ am =>
    match symAddr ss am with
    | some (ea, _) => return (findCell ss.cells ea).map fun k => (.cell k, forced, none)
    | none => return none
  | .str .X64 _ am =>
    match symAddr ss am with
    | some (ea, _) => return (findCellMut ss.cells ea).map fun k => (.cell k, forced, none)
    | none => return none
  | .ldp .W64 false _ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      match findCell ss.cells ea, findCell ss.cells (mkAdd ea (.const 8#64)) with
      | some k1, some k2 => return some (.cell2 k1 k2, forced, none)
      | _, _ => return none
    | none => return none
  | .ldp .W32 false _ _ am | .ldp .W64 true _ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      match findCellN ss.cells .b32 ea, findCellN ss.cells .b32 (mkAdd ea (.const 4#64)) with
      | some k1, some k2 => return some (.cell2 k1 k2, forced, none)
      | _, _ => return none
    | none => return none
  | .stp .W64 _ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      match findCellMut ss.cells ea, findCellMut ss.cells (mkAdd ea (.const 8#64)) with
      | some k1, some k2 =>
        if k1 == k2 then return none else return some (.cell2 k1 k2, forced, none)
      | _, _ => return none
    | none => return none
  | .stp .W32 _ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      match findCellNMut ss.cells .b32 ea, findCellNMut ss.cells .b32 (mkAdd ea (.const 4#64)) with
      | some k1, some k2 =>
        if k1 == k2 then return none else return some (.cell2 k1 k2, forced, none)
      | _, _ => return none
    | none => return none
  | .ldrN _ cw _ am | .ldrS _ cw _ am =>
    match symAddr ss am with
    | some (ea, _) => return (findCellN ss.cells cw ea).map fun k => (.cell k, forced, none)
    | none => return none
  | .strN cw _ am =>
    match symAddr ss am with
    | some (ea, _) => return (findCellNMut ss.cells cw ea).map fun k => (.cell k, forced, none)
    | none => return none
  | .ldrSimdQ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      if let some k := findCellN ss.cells .b128 ea then
        return some (.cell k, forced, none)
      match findCell ss.cells ea, findCell ss.cells (mkAdd ea (.const 8#64)) with
      | some k1, some k2 => return some (.cell2 k1 k2, forced, none)
      | _, _ => return none
    | none => return none
  | .strSimdQ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      if let some k := findCellNMut ss.cells .b128 ea then
        return some (.cell k, forced, none)
      match findCellMut ss.cells ea, findCellMut ss.cells (mkAdd ea (.const 8#64)) with
      | some k1, some k2 =>
        if k1 == k2 then return none else return some (.cell2 k1 k2, forced, none)
      | _, _ => return none
    | none => return none
  | .ldpSimdQ _ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      match findCellN ss.cells .b128 ea, findCellN ss.cells .b128 (mkAdd ea (.const 16#64)) with
      | some k1, some k2 => return some (.cell2 k1 k2, forced, none)
      | _, _ =>
        match findCell ss.cells ea, findCell ss.cells (mkAdd ea (.const 8#64)),
              findCell ss.cells (mkAdd ea (.const 16#64)), findCell ss.cells (mkAdd ea (.const 24#64)) with
        | some k1, some k2, some k3, some k4 => return some (.cell4 k1 k2 k3 k4, forced, none)
        | _, _, _, _ => return none
    | none => return none
  | .stpSimdQ _ _ am =>
    match symAddr ss am with
    | some (ea, _) =>
      match findCellNMut ss.cells .b128 ea, findCellNMut ss.cells .b128 (mkAdd ea (.const 16#64)) with
      | some k1, some k2 =>
        if k1 == k2 then return none else return some (.cell2 k1 k2, forced, none)
      | _, _ =>
        match findCellMut ss.cells ea, findCellMut ss.cells (mkAdd ea (.const 8#64)),
              findCellMut ss.cells (mkAdd ea (.const 16#64)),
              findCellMut ss.cells (mkAdd ea (.const 24#64)) with
        | some k1, some k2, some k3, some k4 =>
          if k1 == k2 || k1 == k3 || k1 == k4 || k2 == k3 || k2 == k4 || k3 == k4 then
            return none
          else
            return some (.cell4 k1 k2 k3 k4, forced, none)
        | _, _, _, _ => return none
    | none => return none
  | .condSelect _ _ _ _ _ cond =>
    match flagsCond? ss.flags cond with
    | some _ => return some (.none, forced, none)
    | none => return none
  | .bcond .. | .cbz .. | .cbnz .. | .tbz .. =>
    match forced with
    | t :: rest => return some (.br t, rest, none)
    | [] =>
      for t in [false, true] do
        if let some (_, obl) := stepOp base ss op (.br t) then
          let mut prfs : Array Expr := #[]
          for p in obl do
            match ← proveObl leaves p with
            | some pk => prfs := prfs.push pk
            | none => break
          if prfs.size == obl.length then return some (.br t, [], some prfs)
      return none
  | _ => return some (.none, forced, none)

private def extractLo12Target? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Obj.lo12Of 1 then
    return some (e.getArg! 0)
  if e.isAppOfArity ``BitVec.truncate 3 || e.isAppOfArity ``BitVec.setWidth 3 then
    let inner := (e.getArg! 2).consumeMData
    if inner.isAppOfArity ``Obj.lo12Of 1 then
      return some (inner.getArg! 0)
  return none

private def extractAddrLo12? (e : Expr) : MetaM (Option (Reg × Expr × Expr)) := do
  let some (c, args) ← Reify.ctor? e | return none
  unless c.name == ``AddrMode.Offset do return none
  let rnE := args[0]!
  let some rn ← Reify.reg? rnE | return none
  let some tE ← extractLo12Target? args[1]! | return none
  return some (rn, rnE, tE)

/-- Reify an elaborated `Instr` term into a `SymInsn` (and its `Expr` representation), recognizing
    relocated `ADRP` (`pageOf target - pageOf pc`) and `:lo12:` (`lo12Of target`) instructions before
    falling back to `Reify.instr?`. -/
def reifySymInsn? (instE : Expr) : RM (Option (SymInsn × Expr)) := do
  let some (c, args) ← Reify.ctor? instE | return none
  if c.name == ``Instr.adr then
    let some true ← Reify.bool? args[0]! | pure ()
    let rdE := args[1]!
    if let some rd ← Reify.reg? rdE then
      let bvE := args[2]!.consumeMData
      if bvE.isAppOfArity ``HSub.hSub 6 then
        let lhs := (bvE.getArg! 4).consumeMData
        let rhs := (bvE.getArg! 5).consumeMData
        if lhs.isAppOfArity ``Obj.pageOf 1 && rhs.isAppOfArity ``Obj.pageOf 1 then
          let tS ← reify (lhs.getArg! 0)
          return some (.adrpSym rd tS, mkApp2 (mkConst ``SymInsn.adrpSym) rdE (toExpr tS))
  if c.name == ``Instr.addSubImm then
    let some .W64 ← Reify.width? args[0]! | pure ()
    let some .ADD ← Reify.addSubOp? args[1]! | pure ()
    let rdE := args[2]!
    let rnE := args[3]!
    if let (some rd, some rn, some tE, some false) :=
        (← Reify.reg? rdE, ← Reify.reg? rnE, ← extractLo12Target? args[4]!, ← Reify.bool? args[5]!) then
      let tS ← reify tE
      return some (.addLo12Sym rd rn tS,
        mkApp3 (mkConst ``SymInsn.addLo12Sym) rdE rnE (toExpr tS))
  if c.name == ``Instr.ldr then
    let rtE := args[3]!
    if let (some w, some sz, some false, some rt, some (rn, rnE, tE)) :=
        (← Reify.width? args[0]!, ← Reify.memSize? args[1]!, ← Reify.bool? args[2]!,
         ← Reify.reg? rtE, ← extractAddrLo12? args[4]!) then
      let tS ← reify tE
      match w, sz with
      | .W64, .X64 =>
        return some (.ldr64Lo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.ldr64Lo12Sym) rtE rnE (toExpr tS))
      | .W32, .W32 =>
        return some (.ldr32Lo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.ldr32Lo12Sym) rtE rnE (toExpr tS))
      | .W32, .H16 =>
        return some (.ldr16Lo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.ldr16Lo12Sym) rtE rnE (toExpr tS))
      | .W32, .B8 =>
        return some (.ldrbLo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.ldrbLo12Sym) rtE rnE (toExpr tS))
      | _, _ => pure ()
  if c.name == ``Instr.str then
    let rtE := args[1]!
    if let (some sz, some rt, some (rn, rnE, tE)) :=
        (← Reify.memSize? args[0]!, ← Reify.reg? rtE, ← extractAddrLo12? args[2]!) then
      let tS ← reify tE
      match sz with
      | .X64 =>
        return some (.str64Lo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.str64Lo12Sym) rtE rnE (toExpr tS))
      | .W32 =>
        return some (.str32Lo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.str32Lo12Sym) rtE rnE (toExpr tS))
      | .H16 =>
        return some (.str16Lo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.str16Lo12Sym) rtE rnE (toExpr tS))
      | .B8 =>
        return some (.strbLo12Sym rt rn tS,
          mkApp3 (mkConst ``SymInsn.strbLo12Sym) rtE rnE (toExpr tS))
  let some inst ← Reify.instr? instE | return none
  return some (.plain inst, mkApp (mkConst ``SymInsn.plain) instE)

def chooseHintSymInsn (base : SExpr) (leaves : RState) (ss : SState) (si : SymInsn)
    (forced : List Bool) : TacticM (Option (Hint × List Bool × Option (Array Expr))) := do
  match si with
  | .plain i =>
    match lower i with
    | some op => chooseHint base leaves ss op forced
    | none => return none
  | .ldr64Lo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCell ss.cells ea).map fun k => (.cell k, forced, none)
  | .str64Lo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCellMut ss.cells ea).map fun k => (.cell k, forced, none)
  | .ldr32Lo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCellN ss.cells .b32 ea).map fun k => (.cell k, forced, none)
  | .str32Lo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCellNMut ss.cells .b32 ea).map fun k => (.cell k, forced, none)
  | .ldr16Lo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCellN ss.cells .b16 ea).map fun k => (.cell k, forced, none)
  | .str16Lo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCellNMut ss.cells .b16 ea).map fun k => (.cell k, forced, none)
  | .ldrbLo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCellN ss.cells .b8 ea).map fun k => (.cell k, forced, none)
  | .strbLo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    return (findCellNMut ss.cells .b8 ea).map fun k => (.cell k, forced, none)
  | .adrpSym .. | .addLo12Sym .. =>
    return some (.none, forced, none)

def isSimdSymInsn : SymInsn → Bool
  | .plain i =>
    match lower i with
    | some (.ldrSimdQ ..) | some (.strSimdQ ..) | some (.ldpSimdQ ..) | some (.stpSimdQ ..) => true
    | _ => false
  | _ => false

/-- Classify why `chooseHintSymInsn` returned `none` for diagnostic stop messages. -/
def classifyHintFailure (ss : SState) (si : SymInsn) (o : BitVec 64) : String :=
  match si with
  | .plain i =>
    match lower i with
    | some (.bcond ..) | some (.cbz ..) | some (.cbnz ..) | some (.tbz ..) =>
      s!"undecided branch at +{o.toHex}"
    | some (.condSelect ..) =>
      s!"undecided conditional select at +{o.toHex}"
    | some (.str _ _ am) | some (.stp _ _ _ am) | some (.strN _ _ am)
    | some (.strSimdQ _ am) | some (.stpSimdQ _ _ am) =>
      match symAddr ss am with
      | some (ea, _) =>
        if hasReadOnlyCellAt ss.cells ea then s!"cannot store to read-only cell at +{o.toHex}"
        else s!"no matching writable cell at +{o.toHex}"
      | none => s!"no matching cell at +{o.toHex}"
    | _ => s!"no matching cell at +{o.toHex}"
  | .str64Lo12Sym _ rn target | .str32Lo12Sym _ rn target
  | .str16Lo12Sym _ rn target | .strbLo12Sym _ rn target =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    if hasReadOnlyCellAt ss.cells ea then s!"cannot store to read-only cell at +{o.toHex}"
    else s!"no matching writable cell at +{o.toHex}"
  | _ => s!"no matching cell at +{o.toHex}"

/-! ## Block Tactic Entry Point -/

def isSpRegExpr (r : Expr) : MetaM Bool := do
  let r := r.consumeMData
  if r.isConstOf ``Reg.sp then return true
  if r.hasFVar || r.hasMVar then return false
  return (← whnfR r).isConstOf ``Reg.sp

def isSpProjOf (s e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isAppOfArity ``State.sp 1 && e.getArg! 0 == s then
    return true
  if e.isAppOfArity ``State.readReg64 2 && e.getArg! 0 == s then
    return ← isSpRegExpr (e.getArg! 1)
  return false

/-- Find `st.sp = rhs` or `st.readReg64 .sp = rhs` hypotheses (including inside `∧` conjuncts)
    for `st ∈ {sE, sB}`, returning `(st, rhs, prf : State.sp st = rhs)`. Prefers `sE` over `sB`
    and skips trivial self-equalities `st.sp = st.sp` / `st.sp = st.readReg64 .sp`. -/
def spFact? (sE sB : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut fallbackSB? : Option (Expr × Expr × Expr) := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for (cTy, cPrf) in ← flatConjuncts d.type d.toExpr do
      let some (_, lhs, rhs) := cTy.consumeMData.eq? | continue
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      let st? ←
        if ← isSpProjOf sE lhs then pure (some sE)
        else if sB == sE then pure none
        else do
        if ← isSpProjOf sB lhs then pure (some sB)
        else pure none
      let some st := st? | continue
      if ← isSpProjOf st rhs then continue
      let cPrf'? ←
        if lhs.isAppOfArity ``State.sp 1 then
          pure (some cPrf)
        else
          let spEqTy ← mkEq (← mkAppM ``State.sp #[st]) rhs
          if ← isDefEq (← inferType cPrf) spEqTy then
            pure (some (← mkExpectedTypeHint cPrf spEqTy))
          else
            pure none
      let some cPrf' := cPrf'? | continue
      if st == sE then
        return some (st, rhs, cPrf')
      else if fallbackSB?.isNone then
        fallbackSB? := some (st, rhs, cPrf')
  return fallbackSB?

/-- Find `st.pc = rhs` hypotheses (including inside `∧` conjuncts) for `st ∈ {sE, sB}`,
    returning `(st, rhs, prf : State.pc st = rhs)`. Prefers `sE` over `sB`. -/
def pcFact? (sE sB : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut fallbackSB? : Option (Expr × Expr × Expr) := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for (cTy, cPrf) in ← flatConjuncts d.type d.toExpr do
      let some (_, lhs, rhs) := cTy.consumeMData.eq? | continue
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      unless lhs.isAppOfArity ``State.pc 1 do continue
      let st := lhs.getArg! 0
      if st == sE then
        return some (sE, rhs, cPrf)
      else if sB != sE && st == sB && fallbackSB?.isNone then
        fallbackSB? := some (sB, rhs, cPrf)
  return fallbackSB?

/-- Find `st.status = .Running` hypotheses (including inside `∧` conjuncts) for `st ∈ {sE, sB}`,
    returning `(st, prf : State.status st = .Running)`. Prefers `sE` over `sB`. -/
def statusFact? (sE sB : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut fallbackSB? : Option (Expr × Expr) := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for (cTy, cPrf) in ← flatConjuncts d.type d.toExpr do
      let some (_, lhs, rhs) := cTy.consumeMData.eq? | continue
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      unless lhs.isAppOfArity ``State.status 1 && rhs.isConstOf ``ExecStatus.Running do continue
      let st := lhs.getArg! 0
      if st == sE then
        return some (sE, cPrf)
      else if sB != sE && st == sB && fallbackSB?.isNone then
        fallbackSB? := some (sB, cPrf)
  return fallbackSB?

/-- Find `s.readReg64 r = e` hypotheses (including inside `∧` conjuncts); returns `(gprIndex, rhs, proof)`. -/
def regFacts (s : Expr) : MetaM (Array (Nat × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for (cTy, cPrf) in ← flatConjuncts d.type d.toExpr do
      let some (_, lhs, rhs) := cTy.consumeMData.eq? | continue
      let lhs := lhs.consumeMData
      unless lhs.isAppOfArity ``State.readReg64 2 && lhs.getArg! 0 == s do continue
      let r ← whnfR (lhs.getArg! 1)
      unless r.isAppOfArity ``Reg.gpr 1 do continue
      let some (5, i) := evalSyntaxBvLit? (r.getArg! 0).consumeMData | continue
      if i < 31 then out := out.push (i, rhs, cPrf)
  return out

/-- Find `s.readVReg128 idx = e` hypotheses (including inside `∧` conjuncts); returns `(vregIndex, rhs, proof)`. -/
def vregFacts (s : Expr) : MetaM (Array (Nat × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for (cTy, cPrf) in ← flatConjuncts d.type d.toExpr do
      let some (_, lhs, rhs) := cTy.consumeMData.eq? | continue
      let lhs := lhs.consumeMData
      unless lhs.isAppOfArity ``State.readVReg128 2 && lhs.getArg! 0 == s do continue
      let idxE ← whnfR (lhs.getArg! 1)
      let some (5, i) := evalSyntaxBvLit? idxE.consumeMData | continue
      if i < 32 then out := out.push (i, rhs, cPrf)
  return out

/-- Find a hypothesis of type `ty` (syntactic match after instantiation). -/
def findHyp (p : Expr → Bool) : MetaM (Option LocalDecl) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if p (← instantiateMVars d.type).consumeMData then return some d
  return none

register_option symBlock.report : Bool := {
  defValue := false
  descr := "sym_block: log the number of instructions executed, the stop reason, and advisor time"
}

register_option symBlock.kcheck : Bool := {
  defValue := false
  descr := "sym_block: kernel-check each proof component separately (debugging / profiling)"
}

/-- Add `prf : ty` (abstracted over the local context) as an auxiliary theorem and report the
    kernel time. Debugging aid for locating expensive or failing components. -/
def kcheck (nm : String) (ty prf : Expr) : MetaM Unit := do
  let ty ← instantiateMVars ty
  let prf ← instantiateMVars prf
  let lctx ← getLCtx
  let mut used : FVarIdSet := (collectFVars {} (mkApp ty prf)).fvarSet
  for d in lctx.decls.toList.reverse.filterMap id do
    if used.contains d.fvarId then
      used := used.insertMany (collectFVars {} d.type).fvarSet.toList
  let xs := lctx.getFVars.filter (used.contains ·.fvarId!)
  let t ← mkForallFVars xs ty
  let v ← mkLambdaFVars xs prf
  let name ← mkFreshUserName (Name.mkSimple s!"_symblock_kcheck_{nm}")
  let t0 ← IO.monoMsNow
  match (← getEnv).addDeclCore 0 (maxRecDepth.get (← getOptions)).toUSize
      (.thmDecl { name, levelParams := [], type := t, value := v }) none with
  | .ok _ => logInfo m!"sym_block kcheck {nm}: ok ({(← IO.monoMsNow) - t0} ms)"
  | .error e =>
    logInfo m!"sym_block kcheck {nm}: FAILED ({(← IO.monoMsNow) - t0} ms): {e.toMessageData (← getOptions)}"

def mkAndIntro (a b pa pb : Expr) : Expr := mkApp4 (mkConst ``And.intro) a b pa pb

/-- Peel a write spine `((s.writeReg64 r v).writeVReg128 q w).setTpidrEl0 t |>.setPC pc |>.setMem m`
    (any order, also `setPState`) down to its base. Returns `(base, gprWrites, vregWrites, tpidrSet?, pcSet?)`. -/
partial def peelSpine (e : Expr)
    (acc : Array (Expr × Expr) := #[])
    (vacc : Array (Expr × Expr) := #[])
    (tpidr? : Option Expr := none)
    (pc? : Option Expr := none) :
    Expr × Array (Expr × Expr) × Array (Expr × Expr) × Option Expr × Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``State.writeReg64 3 then
    peelSpine (e.getArg! 0) (acc.push (e.getArg! 1, e.getArg! 2)) vacc tpidr? pc?
  else if e.isAppOfArity ``State.writeVReg128 3 then
    peelSpine (e.getArg! 0) acc (vacc.push (e.getArg! 1, e.getArg! 2)) tpidr? pc?
  else if e.isAppOfArity ``ProofLib.setTpidrEl0 2 then
    peelSpine (e.getArg! 0) acc vacc (tpidr?.orElse fun _ => some (e.getArg! 1)) pc?
  else if e.isAppOfArity ``State.setPC 2 then
    peelSpine (e.getArg! 0) acc vacc tpidr? (pc?.orElse fun _ => some (e.getArg! 1))
  else if e.isAppOfArity ``State.setMem 2 || e.isAppOfArity ``State.setPState 2 then
    peelSpine (e.getArg! 0) acc vacc tpidr? pc?
  else (e, acc, vacc, tpidr?, pc?)

/-- The general-purpose register index (`< 31`) written by `r`, if any. -/
def gprIdx? (r : Expr) : MetaM (Option Nat) := do
  let r ← whnfR r
  unless r.isAppOfArity ``Reg.gpr 1 do return none
  let some (5, i) := evalSyntaxBvLit? (r.getArg! 0).consumeMData | return none
  return if i < 31 then some i else none

/-- Origin of an initial spatial atom so `PF` preserves exact `↦₁₆` / `↦₁₂₈` / `↦ᵣ` constructors
    and user address expressions. -/
inductive CellOrigin where
  | pt64 (ro : Bool) (addrE valE : Expr)
  | ptN (w : CW) (ro : Bool) (addrE valE : Expr)
  | opaque (atomE : Expr)
  deriving Inhabited

/-- Match a recognized spatial points-to atom `a` into `(is64, width, ro, addrE, valE)`. -/
def matchPointsToAtom? (a : Expr) : Option (Bool × CW × Bool × Expr × Expr) :=
  let a := a.consumeMData
  if a.isAppOfArity ``pointsTo64 2 then some (true, .b128, false, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo64RO 2 then some (true, .b128, true, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo8 2 then some (false, .b8, false, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo8RO 2 then some (false, .b8, true, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo16 2 then some (false, .b16, false, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo16RO 2 then some (false, .b16, true, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo32 2 then some (false, .b32, false, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo32RO 2 then some (false, .b32, true, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo128 2 then some (false, .b128, false, a.getArg! 0, a.getArg! 1)
  else if a.isAppOfArity ``pointsTo128RO 2 then some (false, .b128, true, a.getArg! 0, a.getArg! 1)
  else none

def symBlockCore (maxSteps : Nat) (forced0 : List Bool) : TacticM Unit := do
  let tSetup0 ← IO.monoNanosNow
  let g ← getMainGoal
  g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let (isPanicWP, progE, tgtE, sE, PE, postE, qpE?, oomE) ←
    if ty.isAppOfArity ``SepWP 6 then
      pure (false, ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, none, ty.getArg! 5)
    else if ty.isAppOfArity ``SepWPp 7 then
      pure (true, ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4,
        some (ty.getArg! 5), ty.getArg! 6)
    else
      throwError "sym_block: goal is not `SepWP` or `SepWPp`"
  let (sB, writes, vwrites, tpidrSet?, pcSet?) := peelSpine sE
  unless sB.isFVar do throwError "sym_block: the state must be a variable or a write spine over one (got {sE})"
  let mut written : Array (Nat × Expr) := #[]
  let mut spW? : Option Expr := none
  for (r, v) in writes do
    if let some i ← gprIdx? r then
      unless written.any (·.1 == i) do written := written.push (i, v)
    else if (← whnfR r).isConstOf ``Reg.sp then
      if spW?.isNone then spW? := some v
    else throwError "sym_block: unsupported register write {r} in the state spine"
  let mut vwritten : Array (Nat × Expr) := #[]
  for (idxE, v) in vwrites do
    let idxW ← whnfR idxE
    let some (5, i) := evalSyntaxBvLit? idxW.consumeMData
      | throwError "sym_block: unsupported SIMD register index {idxE} in the state spine"
    unless i < 32 do throwError "sym_block: SIMD register index {i} out of bounds"
    unless vwritten.any (·.1 == i) do vwritten := vwritten.push (i, v)
  let some (stRun, hrunRaw) ← statusFact? sE sB
    | throwError "sym_block: missing `{sB}.status = .Running`"
  let hrunPrf ←
    if stRun == sE then
      pure hrunRaw
    else
      match ← ProofLib.extractStateStatusProof sE with
      | some (_, hSpine) => mkEqTrans hSpine hrunRaw
      | none => pure hrunRaw
  let pcFactRes? ← if pcSet?.isNone then pcFact? sE sB else pure none
  let (bE, hpcBase) ← match pcSet?, pcFactRes? with
    | some p, _ => pure (p, ← mkEqRefl p)
    | none, some (stPc, r, cPrf) =>
      if stPc == sE then
        pure (r, ← mkEqSymm cPrf)
      else
        match ← ProofLib.extractStatePCProof sE with
        | some (_, hSpine) => pure (r, ← mkEqSymm (← mkEqTrans hSpine cPrf))
        | none => pure (r, ← mkEqSymm cPrf)
    | none, none => do
      let pc ← mkAppM ``State.pc #[sB]
      pure (pc, ← mkEqRefl pc)
  let (bE, hpcBase) ← match ← normalizePcExpr bE with
    | some (bNorm, hNorm) => pure (bNorm, ← mkEqTrans (← mkEqSymm hNorm) hpcBase)
    | none => pure (bE, hpcBase)
  let tpidrBaseE ← mkAppM ``State.tpidrEl0 #[sB]
  let tpidrD? ← findHyp fun t => match t.eq? with
      | some (_, l, _) => l.isAppOfArity ``State.tpidrEl0 1 && l.getArg! 0 == sB
      | none => false
  let fidx ← buildFetchIndex
  let hasFetchFor (pcCand : Expr) : MetaM Bool := do
    let pK := progE.consumeMData
    let pcK := pcCand.consumeMData
    if fidx.exact.contains { prog := pK, pc := pcK } ||
       fidx.byOff.contains { prog := pK, base := pcK, off := 0 } then
      return true
    if pcK.isAppOfArity ``HAdd.hAdd 6 then
      let bK := (pcK.getArg! 4).consumeMData
      let offK := (pcK.getArg! 5).consumeMData
      if let some (64, off) := evalSyntaxBvLit? offK then
        if fidx.byOff.contains { prog := pK, base := bK, off := off.toUInt64 } then
          return true
      else if let some off ← evalGroundBv64? offK then
        if fidx.byOff.contains { prog := pK, base := bK, off := off.toUInt64 } then
          return true
    if !pcK.hasFVar && !pcK.hasMVar then
      if let some c ← evalGroundBv64? pcK then
        let lit := bvLit 64 c
        if fidx.exact.contains { prog := pK, pc := lit } ||
           fidx.byOff.contains { prog := pK, base := lit, off := 0 } then
          return true
    return false
  let (bE, hpcBase) ← do
    if ← hasFetchFor bE then
      pure (bE, hpcBase)
    else
      let mut resolved := (bE, hpcBase)
      let mut found := false
      for d in ← getLCtx do
        if found || d.isImplementationDetail then continue
        for (cTy, cPrf) in ← flatConjuncts d.type d.toExpr do
          if found then break
          if let some (_, l, r) := cTy.consumeMData.eq? then
            let l := l.consumeMData
            let r := r.consumeMData
            let tryCand (cand : Expr) (hCandToOld : Expr) : MetaM (Option (Expr × Expr)) := do
              let (candN, hFull) ← match ← normalizePcExpr cand with
                | some (cn, hCn) => pure (cn, ← mkEqTrans (← mkEqSymm hCn) hCandToOld)
                | none => pure (cand, hCandToOld)
              if ← hasFetchFor candN then return some (candN, hFull)
              return none
            if l == bE then
              if let some res ← tryCand r (← mkEqTrans (← mkEqSymm cPrf) hpcBase) then
                resolved := res; found := true
            else if r == bE then
              if let some res ← tryCand l (← mkEqTrans cPrf hpcBase) then
                resolved := res; found := true
            else if bE.isAppOfArity ``HAdd.hAdd 6 then
              let bBase := (bE.getArg! 4).consumeMData
              let bOff := bE.getArg! 5
              if l == bBase then
                let cand := mkAppN bE.getAppFn (bE.getAppArgs.set! 4 r)
                let hAdd := mkAppN bE.getAppFn (bE.getAppArgs.take 4)
                let hEq ← mkCongrFun (← mkCongrArg hAdd (← mkEqSymm cPrf)) bOff
                if let some res ← tryCand cand (← mkEqTrans hEq hpcBase) then
                  resolved := res; found := true
              else if r == bBase then
                let cand := mkAppN bE.getAppFn (bE.getAppArgs.set! 4 l)
                let hAdd := mkAppN bE.getAppFn (bE.getAppArgs.take 4)
                let hEq ← mkCongrFun (← mkCongrArg hAdd cPrf) bOff
                if let some res ← tryCand cand (← mkEqTrans hEq hpcBase) then
                  resolved := res; found := true
      pure resolved
  let tgtNormE := match ← normalizePcExpr tgtE with
    | some (t', _) => t'
    | none => tgtE
  let tgtCands : Array Expr ← (do
    let mut cands := #[tgtNormE]
    let pushNorm (e : Expr) (arr : Array Expr) : MetaM (Array Expr) := do
      let eN := match ← normalizePcExpr e with | some (en, _) => en | none => e
      return if arr.contains eN then arr else arr.push eN
    if tgtNormE.isFVar then
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        for (cTy, _) in ← flatConjuncts d.type d.toExpr do
          if let some (_, l, r) := cTy.consumeMData.eq? then
            let l := l.consumeMData
            let r := r.consumeMData
            if l == tgtNormE && r != tgtNormE then
              cands ← pushNorm r cands
            else if r == tgtNormE && l != tgtNormE then
              cands ← pushNorm l cands
    else if tgtNormE.isAppOfArity ``HAdd.hAdd 6 then do
      let tBase := (tgtNormE.getArg! 4).consumeMData
      if tBase.isFVar then
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          for (cTy, _) in ← flatConjuncts d.type d.toExpr do
            if let some (_, l, r) := cTy.consumeMData.eq? then
              let l := l.consumeMData
              let r := r.consumeMData
              if l == tBase && r != tBase then do
                let cand := mkAppN tgtNormE.getAppFn (tgtNormE.getAppArgs.set! 4 r)
                cands ← pushNorm cand cands
              else if r == tBase && l != tBase then do
                let cand := mkAppN tgtNormE.getAppFn (tgtNormE.getAppArgs.set! 4 l)
                cands ← pushNorm cand cands
    return cands : MetaM _)
  let reachedTarget (pcCand : Expr) : MetaM Bool := do
    for t in tgtCands do
      if ← ProofLib.pcReachedTarget pcCand t then
        return true
    return false
  -- At `target` with no fetchable instruction, succeed as a 0-step no-op; if an instruction is
  -- fetchable (loop header `start = target`), step forward until `target` is reached again.
  let mut firstFetch? : Option (Expr × Expr) := none
  if ← reachedTarget bE then
    match ← fetchAt fidx progE bE with
    | none => return ()
    | some fr0 => firstFetch? := some fr0
  let (atomsE, hPFlat?) ←
    if hasLeftNestedSep PE then
      let (atoms, _, hEq) ← flattenSepWithProof PE
      pure (atoms, some hEq)
    else
      pure (flattenSepTree PE, none)
  let facts := (← regFacts sB).filter fun (i, _, _) => !written.any (·.1 == i)
  let vfacts := (← vregFacts sB).filter fun (i, _, _) => !vwritten.any (·.1 == i)
  let spWNorm? : Option (Expr × Expr) ← match spW? with
    | some v => pure (← normalizePcExpr v)
    | none => pure none
  let spFactRes? ← do
    if spW?.isNone then
      match ← spFact? sE sB with
      | some (stSp, rhs, cPrf) =>
        match ← normalizePcExpr rhs with
        | some (rhsN, hRhs) => pure (some (stSp, rhsN, ← mkEqTrans cPrf hRhs))
        | none => pure (some (stSp, rhs, cPrf))
      | none => pure none
    else pure none
  let initRState : RState := { tpidrE := tpidrBaseE }
  let ((regs, tpidrS, htpidr, spE, cells, cellOrigins, baseS), rst) ← (do
      -- Pre-register narrow/128-bit cell value leaves so cell addresses referencing `x32.zeroExtend 64`
      -- or `q128.extractLsb' 0 64` reify to `.zleaf` / `.lo128` / `.hi128` regardless of atom order.
      for a in atomsE do
        if let some (false, w, _, _, valE) := matchPointsToAtom? a then
          discard <| leafNIdx w valE
      let mut regs : Array SExpr := #[]
      for i in [0:31] do
        match written.find? (·.1 == i), facts.find? (·.1 == i) with
        | some (_, v), _ => regs := regs.push (← reify v)
        | none, some (_, rhs, _) => regs := regs.push (← reify rhs)
        | none, none =>
          let r := if i == 30 then mkConst ``Reg.lr else mkApp (mkConst ``Reg.gpr) (bvLit 5 i)
          regs := regs.push (← leaf (mkApp2 (mkConst ``State.readReg64) sB r))
      let (tpidrS, htpidr) ← match tpidrSet?, tpidrD? with
        | some vE, _ =>
          let ts ← reify vE
          pure (ts, ← mkEqRefl vE)
        | none, some d =>
          let some (_, _, rhs) := (← instantiateMVars d.type).consumeMData.eq? | unreachable!
          let ts ← reify rhs
          pure (ts, ← mkEqSymm d.toExpr)
        | none, none =>
          pure (.tpidr0, ← mkEqRefl tpidrBaseE)
      let sp ← match spW?, spWNorm?, spFactRes? with
        | some _, some (vN, _), _ => reify vN
        | some v, none, _ => reify v
        | none, _, some (_, rhs, _) => reify rhs
        | none, _, none => leaf (← mkAppM ``State.sp #[sB])
      let mut cells : Array Cell := #[]
      let mut origins : Array CellOrigin := #[]
      for a in atomsE do
        if let some (is64, w, ro, addrE, valE) := matchPointsToAtom? a then
          if is64 then
            cells := cells.push (.pt64 ro (← reify addrE) (← reify valE))
            origins := origins.push (.pt64 ro addrE valE)
          else
            cells := cells.push (.ptN w ro (← reify addrE) (← leafN w valE))
            origins := origins.push (.ptN w ro addrE valE)
        else
          let st ← get
          set { st with atoms := st.atoms.push a }
          cells := cells.push (.opaque st.atoms.size)
          origins := origins.push (.opaque a)
      let baseS ← reify bE
      return (regs, tpidrS, htpidr, sp, cells, origins, baseS) : RM _).run initRState
  let mut rst := rst
  let mut ss0 : SState := {
    regs := regs.toList
    vregs := []
    sp := spE
    tpidr := tpidrS
    pc := .rel 0
    flags := .orig
    cells := cells.toList
  }
  let mut ss := ss0
  let activateVRegs (rstCur : RState) (s0Cur sCur : SState) : MetaM (RState × SState × SState) := do
    if !s0Cur.vregs.isEmpty then
      return (rstCur, s0Cur, sCur)
    let (vregs0, rst') ← (do
      let mut vr : Array VExpr := #[]
      for i in [0:32] do
        match vwritten.find? (·.1 == i), vfacts.find? (·.1 == i) with
        | some (_, v), _ => vr := vr.push (← reifyV128 v)
        | none, some (_, rhs, _) => vr := vr.push (← reifyV128 rhs)
        | none, none =>
          vr := vr.push (← leaf128 (mkApp2 (mkConst ``State.readVReg128) sB (bvLit 5 i)))
      return vr : RM _).run rstCur
    let vrList := vregs0.toList
    return (rst', { s0Cur with vregs := vrList }, { sCur with vregs := vrList })
  if !vwritten.isEmpty || !vfacts.isEmpty then
    let (rst', ss0', ss') ← activateVRegs rst ss0 ss
    rst := rst'; ss0 := ss0'; ss := ss'
  let mut hints : Array Hint := #[]
  let mut obls : Array SProp := #[]
  let mut oblPrfs : Array Expr := #[]
  let mut tbl : Array (BitVec 64 × SymInsn × Expr × Option (Expr × Expr) × Expr) := #[]
  let mut forced := forced0
  let mut stop := "step limit"
  let mut fetchNs : Nat := 0
  let mut evalNs : Nat := 0
  let tAdv0 ← IO.monoNanosNow
  for _ in [0:maxSteps] do
    let .rel o := ss.pc | stop := "computed jump / return"; break
    let (si?, opName, ok) ← match tbl.find? (·.1 == o) with
      | some (_, si, _, _, _) => pure (some si, `unknown, true)
      | none =>
        let pcRaw ← if o == 0 then pure bE else mkAppM ``HAdd.hAdd #[bE, bvLit 64 o.toNat]
        let norm? ← if o == 0 then pure none else pcAt bE o
        let pcE := match norm? with | some (n, _) => n | none => pcRaw
        let fr ←
          if o == 0 && firstFetch?.isSome then
            let res := firstFetch?
            firstFetch? := none
            pure res
          else
            let tf0 ← IO.monoNanosNow
            let r ← fetchAt fidx progE pcE
            fetchNs := fetchNs + ((← IO.monoNanosNow) - tf0)
            pure r
        match fr with
        | some (instE, prfRaw) =>
          let te0 ← IO.monoNanosNow
          let (si?, rst') ← (reifySymInsn? instE).run rst
          rst := rst'
          evalNs := evalNs + ((← IO.monoNanosNow) - te0)
          let opN : Name := ((instE.getAppArgs.back?.map (·.getAppFn.constName?)).join).getD `unknown
          match si? with
          | some (si, siE) =>
            tbl := tbl.push (o, si, siE, norm?, prfRaw)
            pure (some si, opN, true)
          | none => pure (none, opN, true)
        | none => pure (none, `unknown, false)
    unless ok do stop := s!"no fetch at +{o.toHex}"; break
    let some si := si? | stop := s!"unsupported instruction at +{o.toHex}: {opName}"; break
    if isSimdSymInsn si && ss.vregs.isEmpty then
      let (rst', ss0', ss') ← activateVRegs rst ss0 ss
      rst := rst'; ss0 := ss0'; ss := ss'
    let some (h, forced', prfs?) ← chooseHintSymInsn baseS rst ss si forced
      | stop := classifyHintFailure ss si o; break
    let some (ss', o') := stepSymInsn baseS ss si h | stop := s!"symbolic rule failed at +{o.toHex}: {opName}"; break
    let mut prfs : Array Expr := prfs?.getD #[]
    if prfs?.isNone then
      for p in o' do
        match ← proveObl rst p with
        | some pk => prfs := prfs.push pk
        | none => break
    if prfs.size < o'.length then
      if forced.length != forced'.length then
        throwError "sym_block: could not discharge obligation {← prettyObl rst o'[prfs.size]!}"
      stop := s!"unprovable obligation at +{o.toHex}"; break
    forced := forced'
    ss := ss'; hints := hints.push h; obls := obls ++ o'.toArray; oblPrfs := oblPrfs ++ prfs
    let curPcE ← match ss.pc with
      | .rel oNext =>
        if oNext == 0 then pure bE
        else
          match ← pcAt bE oNext with
          | some (norm, _) => pure norm
          | none =>
            let raw ← mkAppM ``HAdd.hAdd #[bE, bvLit 64 oNext.toNat]
            match ← normalizePcExpr raw with
            | some (norm, _) => pure norm
            | none => pure raw
      | .abs e =>
        let raw ← prettyC rst e
        match ← normalizePcExpr raw with
        | some (norm, _) => pure norm
        | none => pure raw
    if ← reachedTarget curPcE then
      stop := "reached target PC"; break
  if hints.isEmpty then throwError "sym_block: no instruction could be executed ({stop})"
  let leaves := rst
  let advNs := (← IO.monoNanosNow) - tAdv0
  let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let envE := mkAppN (mkConst ``Env.mk) #[
    ← mkListLit bv64 rst.leaves.toList,
    ← mkListLit (mkConst ``SepProp) rst.atoms.toList,
    ← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 8)) rst.leaves8.toList,
    ← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 16)) rst.leaves16.toList,
    ← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 32)) rst.leaves32.toList,
    ← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 128)) rst.leaves128.toList,
    tpidrBaseE
  ]
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) bv64 (mkConst ``SymInsn)
  let tblE ← mkListLit pairTy (tbl.toList.map fun (o, _, siE, _, _) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) bv64 (mkConst ``SymInsn) (toExpr o) siE)
  let mut htbl := mkConst ``True.intro
  let mut htblTy := mkConst ``True
  for (o, si, siE, norm?, prfRaw) in tbl.reverse do
    let boE ← mkAppM ``HAdd.hAdd #[bE, toExpr o]
    let pcE := match norm? with | some (n, _) => n | none => if o == 0 then bE else boE
    let hPcEq? : Option Expr ← match norm? with
      | some (_, hEq) => pure (some hEq)
      | none => if o == 0 then some <$> mkAppM ``BitVec.add_zero #[bE] else pure none
    let insnAt (p : Expr) : Expr := mkApp3 (mkConst ``SymInsn.toInstr) envE p siE
    let a ← mkEq (mkApp2 (mkConst ``Program.fetch) progE boE) (← mkAppM ``Option.some #[insnAt boE])
    let prf ← match hPcEq?, si with
      | none, _ => pure prfRaw
      | some hPcEq, .adrpSym .. =>
        let pcProp ← mkEq (mkApp2 (mkConst ``Program.fetch) progE pcE) (← mkAppM ``Option.some #[insnAt pcE])
        let motive ← withLocalDeclD `pc bv64 fun pcV => do
          let lhs := mkApp2 (mkConst ``Program.fetch) progE pcV
          let rhs ← mkAppM ``Option.some #[insnAt pcV]
          mkLambdaFVars #[pcV] (← mkEq lhs rhs)
        let h := mkApp6 (mkConst ``congrArg [1, 1]) bv64 (mkSort 0) boE pcE motive hPcEq
        pure (mkApp4 (mkConst ``Eq.mpr [0]) a pcProp h prfRaw)
      | some hPcEq, _ =>
        mkEqTrans (← mkCongrArg (mkApp (mkConst ``Program.fetch) progE) hPcEq) prfRaw
    htbl := mkAndIntro a htblTy prf htbl
    htblTy := mkAnd a htblTy
  let mut hregs := mkConst ``True.intro
  for i' in [0:31] do
    let i := 30 - i'
    let rest := regs.toList.drop (i + 1)
    let restTy := mkApp4 (mkConst ``RegsAgree) sE envE (mkNatLit (i + 1)) (toExpr rest)
    let ai ← mkEq (mkApp2 (mkConst ``State.readReg64) sE (mkApp (mkConst ``Reg.gpr) (bvLit 5 i)))
      (mkApp2 (mkConst ``SExpr.eval) envE (toExpr regs[i]!))
    let pi ← match facts.find? (·.1 == i) with
      | some (_, _, prf) => pure prf
      | none => mkEqRefl (mkApp2 (mkConst ``State.readReg64) sE (mkApp (mkConst ``Reg.gpr) (bvLit 5 i)))
    hregs := mkAndIntro ai restTy pi hregs
  let ss0E := toExpr ss0
  let ssFE := toExpr ss
  let vregsListTy := mkApp (mkConst ``List [0]) (mkConst ``VExpr)
  let (hvregs, hvval) ←
    if ss0.vregs.isEmpty then
      let emptyV := toExpr ([] : List VExpr)
      let p1 ← mkEq emptyV emptyV
      let p2 ← mkEq (mkNatLit 0) (mkNatLit 32)
      pure (mkConst ``True.intro, mkApp3 (mkConst ``Or.inl) p1 p2 (← mkEqRefl emptyV))
    else
      let mut hvr := mkConst ``True.intro
      let vregsArr := ss0.vregs.toArray
      for i' in [0:32] do
        let i := 31 - i'
        let rest := ss0.vregs.drop (i + 1)
        let restTy := mkApp4 (mkConst ``VRegsAgree) sE envE (mkNatLit (i + 1)) (toExpr rest)
        let ai ← mkEq (mkApp2 (mkConst ``State.readVReg128) sE (bvLit 5 i))
          (mkApp2 (mkConst ``VExpr.eval) envE (toExpr vregsArr[i]!))
        let pi ← match vfacts.find? (·.1 == i) with
          | some (_, _, prf) => pure prf
          | none => mkEqRefl (mkApp2 (mkConst ``State.readVReg128) sE (bvLit 5 i))
        hvr := mkAndIntro ai restTy pi hvr
      let p1 ← mkEq (mkApp (mkConst ``SState.vregs) ss0E) (toExpr ([] : List VExpr))
      let p2 ← mkEq (mkNatLit 32) (mkNatLit 32)
      pure (hvr, mkApp3 (mkConst ``Or.inr) p1 p2 (← mkEqRefl (mkNatLit 32)))
  let _ := vregsListTy
  let hlen ← mkEqRefl (mkNatLit 31)
  let hvlen_eq ← mkEqRefl (mkNatLit ss0.vregs.length)
  let hsp ← match spWNorm?, spFactRes? with
    | some (_, hVNorm), _ =>
      let hspTy ← mkEq (mkApp2 (mkConst ``SExpr.eval) envE (toExpr spE)) (← mkAppM ``State.sp #[sE])
      mkExpectedTypeHint (← mkEqSymm hVNorm) hspTy
    | none, none => mkEqRefl (← mkAppM ``State.sp #[sE])
    | none, some (stSp, _, cPrf) =>
      let hspTy ← mkEq (mkApp2 (mkConst ``SExpr.eval) envE (toExpr spE)) (← mkAppM ``State.sp #[sE])
      let rawPrf ←
        if stSp == sE then
          mkEqSymm cPrf
        else
          match ← ProofLib.extractStateSPProof sE with
          | some (_, hSpine) => mkEqSymm (← mkEqTrans hSpine cPrf)
          | none => mkEqSymm cPrf
      unless ← isDefEq (← inferType rawPrf) hspTy do
        throwError "sym_block: failed to align initial SP proof ({← inferType rawPrf} vs {hspTy})"
      mkExpectedTypeHint rawPrf hspTy
  let hpc ← mkEqTrans (← mkAppM ``BitVec.add_zero #[bE]) hpcBase
  let hfl ← mkEqRefl (toExpr SFlags.orig)
  let hs := mkAppN (mkConst ``toState_self)
    #[ss0E, bE, envE, sE, hregs, hlen, hvregs, hvval, hsp, htpidr, hpc, hfl, hrunPrf]
  let hP ← match hPFlat? with
    | none => mkEqRefl PE
    | some hEq =>
      mkExpectedTypeHint hEq (← mkEq PE (mkApp2 (mkConst ``cellsProp) envE (mkApp (mkConst ``SState.cells) ss0E)))
  let hintsE := toExpr hints.toList
  let oblE := toExpr obls.toList
  let resE := toExpr (some (ss, obls.toList))
  let hrun ← mkEqRefl resE
  let baseE := toExpr baseS
  let hbase ← mkEqRefl bE
  let mut hobl := mkConst ``True.intro
  for k' in [0:obls.size] do
    let k := obls.size - 1 - k'
    let p := obls[k]!
    let pk := oblPrfs[k]!
    let restTy := mkApp2 (mkConst ``allHold) envE (toExpr (obls.toList.drop (k + 1)))
    let pTy := mkApp2 (mkConst ``SProp.denote) envE (toExpr p)
    if symBlock.kcheck.get (← getOptions) then
      kcheck s!"obl{k}" pTy pk
      logInfo m!"  obligation {k}: {← prettyObl leaves p}"
    hobl := mkAndIntro pTy restTy pk hobl
  let memTy := mkConst ``Memory
  let changed := changedRegs ss0 ss
  let changedV := changedVRegs ss0 ss
  let mkNext (pcOverride : Option Expr) : MetaM Expr := withLocalDeclD `m memTy fun m => do
    let mut st := sE
    for i in changed do
      let r := if i == 30 then mkConst ``Reg.lr else mkApp (mkConst ``Reg.gpr) (bvLit 5 i)
      st := mkApp3 (mkConst ``State.writeReg64) st r (← prettyC leaves (ss.reg i))
    for i in changedV do
      st := mkApp3 (mkConst ``State.writeVReg128) st (bvLit 5 i) (← prettyV128 leaves (ss.vreg i))
    if ss.sp != ss0.sp then
      st := mkApp3 (mkConst ``State.writeReg64) st (mkConst ``Reg.sp) (← prettyC leaves ss.sp)
    if ss.tpidr != ss0.tpidr then
      st := mkApp2 (mkConst ``ProofLib.setTpidrEl0) st (← prettyC leaves ss.tpidr)
    if ss.flags != ss0.flags then
      st := mkApp2 (mkConst ``State.setPState) st
        (← prettyFlags leaves (← mkAppM ``State.pstate #[sE]) ss.flags)
    let pcE ← match pcOverride, ss.pc with
      | some p, _ => pure p
      | none, .rel o => mkAppM ``HAdd.hAdd #[bE, bvLit 64 o.toNat]
      | none, .abs e => prettyC leaves e
    st := mkApp2 (mkConst ``State.setPC) st pcE
    st := mkApp2 (mkConst ``State.setMem) st m
    let mut atomsF : Array Expr := #[]
    for k in [0:ss.cells.length] do
      if ss.cells[k]! == ss0.cells[k]! then
        atomsF := atomsF.push atomsE[k]!
      else
        match ss.cells[k]!, cellOrigins[k]! with
        | .pt64 ro _ v, CellOrigin.pt64 _ addrE _ =>
          let ptName := if ro then ``pointsTo64RO else ``pointsTo64
          atomsF := atomsF.push (mkApp2 (mkConst ptName) addrE (← prettyC leaves v))
        | .pt64 ro a v, _ =>
          let ptName := if ro then ``pointsTo64RO else ``pointsTo64
          atomsF := atomsF.push (mkApp2 (mkConst ptName) (← prettyC leaves a) (← prettyC leaves v))
        | .ptN w ro _ v, CellOrigin.ptN _ _ addrE _ =>
          atomsF := atomsF.push (mkApp2 (mkConst (cwPtConst w ro)) addrE (← prettyN leaves w v))
        | .ptN w ro a v, _ =>
          atomsF := atomsF.push (mkApp2 (mkConst (cwPtConst w ro)) (← prettyC leaves a) (← prettyN leaves w v))
        | .opaque j, _ =>
          atomsF := atomsF.push rst.atoms[j]!
    let PF := if atomsF.isEmpty then mkConst ``SepProp.emp else
      atomsF.pop.foldr (fun a acc => mkApp2 (mkConst ``SepProp.sepConj) a acc) atomsF.back!
    let wpApp := if isPanicWP then
      mkAppN (mkConst ``SepWPp) #[progE, tgtE, st, PF, postE, qpE?.get!, oomE]
    else
      mkApp6 (mkConst ``SepWP) progE tgtE st PF postE oomE
    mkForallFVars #[m] wpApp
  let nextTy ← mkNext none
  -- When the entry PC is `X + c₁` and the final PC is `(X + c₁) + c₂`, present the goal at
  -- `X + (c₁ + c₂)` (the form the fetch closers recognise) via `BitVec.add_assoc`.
  let pcNorm? ← match ss.pc with
    | .rel o => if o == 0 then pure none else pcAt bE o
    | .abs _ => pure none
  let next ← match pcNorm? with
    | none => mkFreshExprSyntheticOpaqueMVar nextTy (← g.getTag)
    | some (norm, hEq) => do
      let niceTy ← mkNext (some norm)
      let next' ← mkFreshExprSyntheticOpaqueMVar niceTy (← g.getTag)
      let motive ← withLocalDeclD `pc bv64 fun pcV => do
        mkLambdaFVars #[pcV] (← mkNext (some pcV))
      let h := mkApp6 (mkConst ``congrArg [1, 1]) bv64 (mkSort 0) (← mkAppM ``HAdd.hAdd #[bE, bvLit 64 (match ss.pc with | .rel o => o.toNat | _ => 0)]) norm motive hEq
      pure (mkApp4 (mkConst ``Eq.mpr [0]) nextTy niceTy h next')
  let nextGoal := match pcNorm? with
    | none => next
    | some _ => (next.getAppArgs.back!)
  let prf := if isPanicWP then
    mkAppN (mkConst ``SepWPp_block_spine)
      #[progE, tgtE, bE, envE, tblE, hintsE, ss0E, ssFE, oblE, sE, PE, postE, qpE?.get!, oomE,
        baseE, hbase, htbl, hlen, hvval, hvlen_eq, hs, hP, hrun, hobl, next]
  else
    mkAppN (mkConst ``SepWP_block_spine)
      #[progE, tgtE, bE, envE, tblE, hintsE, ss0E, ssFE, oblE, sE, PE, postE, oomE,
        baseE, hbase, htbl, hlen, hvval, hvlen_eq, hs, hP, hrun, hobl, next]
  if symBlock.kcheck.get (← getOptions) then
    kcheck "tbl" (mkApp4 (mkConst ``TblOK) progE bE envE tblE) htbl
    kcheck "hs" (← mkEq (mkApp5 (mkConst ``SState.toState) ss0E bE envE sE (← mkAppM ``State.mem #[sE])) sE) hs
    kcheck "hP" (← mkEq PE (mkApp2 (mkConst ``cellsProp) envE (mkApp (mkConst ``SState.cells) ss0E))) hP
    kcheck "hrun" (← mkEq (mkApp4 (mkConst ``run) baseE tblE hintsE ss0E) resE) hrun
    kcheck "hobl" (mkApp2 (mkConst ``allHold) envE oblE) hobl
    let expTy ← withLocalDeclD `m (mkConst ``Memory) fun m => do
      let wpExp := if isPanicWP then
        mkAppN (mkConst ``SepWPp) #[progE, tgtE,
          mkAppN (mkConst ``spine) #[ss0E, ssFE, bE, envE, sE, m],
          mkApp2 (mkConst ``cellsProp) envE (mkApp (mkConst ``SState.cells) ssFE),
          postE, qpE?.get!, oomE]
      else
        mkApp6 (mkConst ``SepWP) progE tgtE
          (mkAppN (mkConst ``spine) #[ss0E, ssFE, bE, envE, sE, m])
          (mkApp2 (mkConst ``cellsProp) envE (mkApp (mkConst ``SState.cells) ssFE)) postE oomE
      mkForallFVars #[m] wpExp
    kcheck "next" expTy (← mkSorry nextTy false)
  g.assign prf
  let (_, g') ← nextGoal.mvarId!.intro `m
  replaceMainGoal [g']
  if symBlock.report.get (← getOptions) then
    let line := (← getFileMap).toPosition ((← getRef).getPos?.getD 0) |>.line
    let buildNs := (← IO.monoNanosNow) - tAdv0 - advNs
    logInfo m!"sym_block (line {line}): {hints.size} instructions, {obls.size} obligations, {tbl.size} fetches; stopped: {stop}; setup {(tAdv0 - tSetup0) / 1000000} ms, advisor {advNs / 1000000} ms (fetch {fetchNs / 1000000} ms, instruction eval {evalNs / 1000000} ms), proof assembly {buildNs / 1000000} ms"

end Tac

/-- Symbolically execute up to `num` instructions on a `SepWP` or `SepWPp` goal using the
    reflective block checker, with optional branch hints `(hints := "t n")`. -/
syntax (name := symBlock) "sym_block" (" (" &"hints" " := " str ")")? (ppSpace num)? : tactic

@[tactic symBlock] def evalSymBlock : Tactic := fun stx => do
  let forced : List Bool :=
    (((stx[1].getArgs.findSome? (·.isStrLit?)).getD "").splitOn " ").filterMap fun w =>
      if w == "t" then some true else if w == "n" then some false else none
  let n := match stx[2].getOptional? with
    | some k => k.isNatLit?.getD 1000
    | none => 1000
  Tac.symBlockCore n forced

end ProofLib.SymBlock
