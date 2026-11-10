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
public meta import ProofLib.MaxRecDepthDiag
public meta import Arm64.Trusted.ISA.Decode
public meta import Arm64.Trusted.ISA.Eval
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.Meta.ToExpr
public import ProofLib.SimpAttrs
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Simulation
public import ProofLib.Hoare.Loop
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Solver
public import ProofLib.ObjectLoad
public import ProofLib.BV.Linear
public import ProofLib.SepLogic.CondClassify
public import ProofLib.RelocDecode
import Arm64.Trusted.Spec.SepLogic

/-!
# ARM64 State-Spine Normalization and Step Tactics

Implements explicit `O(spine)` `State` projection and memory-forwarding pre-simprocs (`reduceState*`,
`reduceMemRead*`, `proveMemEqExpr?`) registered in `arm64_norm` / `wp_norm`, together with low-level
symbolic execution and framing tactics (`arm64_step`, `arm64_step_inst`, `arm64_sep_close`,
`arm64_bv`, `arm64_decide_code`, `arm64_code_at`, and `#arm64_check_no_rfl_state_lemmas`).

## Covered Instruction Classes

Beyond the base integer/branch ISA, `arm64_norm` normalizes these instruction classes, which
optimizing compilers (e.g. `rustc`) commonly emit:

- unscaled `LDUR`/`STUR` (`AddrMode.UnscaledOffset`, including negative `simm9` offsets) at all of
  the byte/halfword/word/doubleword sizes,
- `LDAR`/`LDARB`/`LDARH`/`STLR`/`STLRB`/`STLRH` (identical memory effects to their plain
  counterparts under this sequentially consistent model) and `DMB`/`DSB`/`ISB` (pure `PC` advances),
- `MRS`/`MSR` on `tpidr_el0`,
- SIMD/FP `LDR`/`STR`/`LDP`/`STP` at `q`/`d`/`s` widths with 128-bit memory forwarding and
  `Memory.Disjoint128` framing,
- `FMOV` between GPRs and vector lanes, `DUP`/`INS`/`UMOV`, and vector `EOR`/`AND`/`ORR`/`ADD`.

## Known Limitation: AES Rounds

`AESE`/`AESD`/`AESMC`/`AESIMC` are not normalized by `arm64_norm`. Their semantics
(`Arm64.evalAesOp`) go through the FIPS-197 S-box tables and `GF(2^8)` multiplication, and giving
`simp` a usable closed form for them is a research problem of its own. Step AES round instructions
explicitly (`arm64_step_inst`) and reason about `Arm64.evalAesOp` directly.
-/

namespace ProofLib

open Lean Elab Tactic Meta
open Arm64

public meta section

attribute [arm64_norm]
  Arm64.bitvec_add_zero
  Arm64.emp_sepConj Arm64.sepConj_emp Arm64.pure_true
  Arm64.satisfies_emp Arm64.satisfies_pure
  Arm64.satisfies_pure_sepConj Arm64.satisfies_sepConj_pure Arm64.satisfies_sepConj_pure_assoc
  Arm64.sepExists_sepConj_left Arm64.sepExists_sepConj_right Arm64.satisfies_sepExists
  Arm64.sepConj_assoc

/-- Bubble `⌜φ⌝` to the left of separating conjunctions (`P ∗ ⌜φ⌝ = ⌜φ⌝ ∗ P` and
    `P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q)`) when `P` is not itself `⌜_⌝`, so `satisfies_pure_sepConj`
    can extract all pure conjuncts from `m ⊨ ...` regardless of depth. -/
simproc [arm64_norm] reduceSepConjPureBubble (SepProp.sepConj _ _) := fun e => do
  if !e.isAppOfArity ``SepProp.sepConj 2 then return .continue
  let p := e.getArg! 0
  let q := e.getArg! 1
  if p.isAppOfArity ``SepProp.pure 1 then return .continue
  if q.isAppOfArity ``SepProp.pure 1 then
    let newExpr := mkApp2 (mkConst ``SepProp.sepConj) q p
    let prf := mkApp2 (mkConst ``Arm64.sepConj_comm) p q
    return .visit { expr := newExpr, proof? := some prf }
  if q.isAppOfArity ``SepProp.sepConj 2 then
    let q1 := q.getArg! 0
    let q2 := q.getArg! 1
    if q1.isAppOfArity ``SepProp.pure 1 then
      let phi := q1.getArg! 0
      let pq2 := mkApp2 (mkConst ``SepProp.sepConj) p q2
      let newExpr := mkApp2 (mkConst ``SepProp.sepConj) q1 pq2
      let prf := mkApp3 (mkConst ``ProofLib.sepConj_pure_left_comm) p phi q2
      return .visit { expr := newExpr, proof? := some prf }
  return .continue

/-- Kernel-checked proof of `lhs = rhs` by `decide`: `of_decide_eq_true (Eq.refl true)`.
    The kernel re-evaluates the `Decidable` instance, so (unlike `Lean.ofReduceBool`) no
    compiler trust is introduced and `leanprover/comparator` accepts the result. -/
def mkKernelDecideEqProof (lhs rhs : Expr) : MetaM Expr := do
  mkDecideProof (← mkEq lhs rhs)

/-- Pure `O(1)` fast path for extracting a `Nat` literal from a raw `.lit (.natVal n)` or `OfNat.ofNat _ n _`. -/
@[inline] def evalNatLitPure? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.isAppOfArity ``OfNat.ofNat 3 then (e.getArg! 1).rawNatLit?
  else none

/-- Pure `O(1)` fast path for extracting `(width, value)` from `BitVec.ofNat w v` when `w` and `v` are numerals. -/
@[inline] def evalBitVecLitPure? (e : Expr) : Option (Nat × Nat) :=
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some w := evalNatLitPure? (e.getArg! 0) then
      if let some v := evalNatLitPure? (e.getArg! 1) then
        some (w, v % (1 <<< w))
      else none
    else none
  else none

/-- Evaluate a closed `Nat` expression to a concrete `Nat` literal if and only if its leaves
    reduce to literals. Arithmetic operators (`+`, `-`, `*`, `/`, `%`, `<<<`, `>>>`, `^`, `succ`)
    are evaluated structurally in `MetaM` instead of via `whnf`, preventing `whnf` from unfolding
    `Nat.add` / `Nat.mod` in unary (`Nat.rec`) when an inner subterm such as `Program.fnOff` has
    been marked `[irreducible]`. -/
partial def evalNatLit? (e : Expr) : MetaM (Option Nat) := do
  if let some n := evalNatLitPure? e then return some n
  if let some n ← getNatValue? e then return some n
  if e.hasFVar || e.hasMVar then return none
  if e.isAppOfArity ``Nat.succ 1 then
    return (· + 1) <$> (← evalNatLit? (e.getArg! 0))
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a + b)
  if e.isAppOfArity ``Nat.add 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a + b)
  if e.isAppOfArity ``HSub.hSub 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a - b)
  if e.isAppOfArity ``Nat.sub 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a - b)
  if e.isAppOfArity ``HMul.hMul 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a * b)
  if e.isAppOfArity ``Nat.mul 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a * b)
  if e.isAppOfArity ``HDiv.hDiv 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a / b)
  if e.isAppOfArity ``Nat.div 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a / b)
  if e.isAppOfArity ``HMod.hMod 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a % b)
  if e.isAppOfArity ``Nat.mod 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a % b)
  if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a <<< b)
  if e.isAppOfArity ``Nat.shiftLeft 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a <<< b)
  if e.isAppOfArity ``HShiftRight.hShiftRight 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a >>> b)
  if e.isAppOfArity ``Nat.shiftRight 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a >>> b)
  if e.isAppOfArity ``HPow.hPow 6 then
    let some a ← evalNatLit? (e.getArg! 4) | return none
    let some b ← evalNatLit? (e.getArg! 5) | return none
    return some (a ^ b)
  if e.isAppOfArity ``Nat.pow 2 then
    let some a ← evalNatLit? (e.getArg! 0) | return none
    let some b ← evalNatLit? (e.getArg! 1) | return none
    return some (a ^ b)
  let e' ← withTransparency .default (whnf e)
  if let some n := e'.rawNatLit? then return some n
  getNatValue? e'

/-- Extract `(width, value)` when `e` is a ground `BitVec` literal (or `abbrev`, `Program.fnAddr`, addition, or negation thereof). -/
partial def evalBitVecLit? (e : Expr) : MetaM (Option (Nat × Nat)) := do
  if let some wv := evalBitVecLitPure? e then return some wv
  if e.hasFVar || e.hasMVar then return none
  let e' ← if e.isConst || (e.isAppOfArity ``Program.fnAddr 2 && !(e.getArg! 0).hasFVar) then
    withTransparency .default (whnf e)
  else
    pure e
  if let some wv := evalBitVecLitPure? e' then return some wv
  if e'.isAppOfArity ``BitVec.ofNat 2 then
    if let some w ← evalNatLit? (e'.getArg! 0) then
      if let some v ← evalNatLit? (e'.getArg! 1) then
        return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``BitVec.ofFin 2 then
    if let some w ← evalNatLit? (e'.getArg! 0) then
      let finExpr ← whnf (e'.getArg! 1)
      if finExpr.isAppOfArity ``Fin.mk 3 then
        if let some v ← evalNatLit? (finExpr.getArg! 1) then
          return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``HAdd.hAdd 6 then
    if let some (w1, v1) ← evalBitVecLit? (e'.getArg! 4) then
      if let some (w2, v2) ← evalBitVecLit? (e'.getArg! 5) then
        if w1 == w2 then
          return some (w1, (v1 + v2) % (1 <<< w1))
  if e'.isAppOfArity ``Int64.toBitVec 1 then
    let inner := e'.getArg! 0
    if inner.isAppOfArity ``Int64.ofBitVec 1 then
      return ← evalBitVecLit? (inner.getArg! 0)
    if inner.isAppOfArity ``Int64.ofUInt64 1 then
      let u := inner.getArg! 0
      if u.isAppOfArity ``UInt64.ofBitVec 1 then
        return ← evalBitVecLit? (u.getArg! 0)
  if e'.isAppOfArity ``Neg.neg 3 then
    let inner := e'.getArg! 2
    if inner.isAppOfArity ``BitVec.ofNat 2 then
      if let some w ← evalNatLit? (inner.getArg! 0) then
        if let some v ← evalNatLit? (inner.getArg! 1) then
          let m := 1 <<< w
          return some (w, (m - (v % m)) % m)
  if e'.isAppOfArity ``BitVec.zeroExtend 3 || e'.isAppOfArity ``BitVec.truncate 3 ||
      e'.isAppOfArity ``BitVec.setWidth 3 then
    if let some w ← evalNatLit? (e'.getArg! 1) then
      if let some (_, v) ← evalBitVecLit? (e'.getArg! 2) then
        return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
    if let some (w, v) ← evalBitVecLit? (e'.getArg! 4) then
      if let some amt ← evalNatLit? (e'.getArg! 5) then
        return some (w, (v <<< amt) % (1 <<< w))
  if e'.isAppOfArity ``HShiftRight.hShiftRight 6 then
    if let some (w, v) ← evalBitVecLit? (e'.getArg! 4) then
      if let some amt ← evalNatLit? (e'.getArg! 5) then
        return some (w, (v >>> amt) % (1 <<< w))
  return none

/-- Reduce `(BitVec.toNat lit)` in the shift-amount argument of `shiftVal` to a clean `Nat` numeral
    before `shiftVal` unfolds, so `x <<< 0` and `x >>> 1` simplify without touching standalone `v.toNat`. -/
simproc ↓ [arm64_norm, wp_norm] reduceShiftValToNat (shiftVal _ _ _ _) := fun e => do
  if e.getAppNumArgs != 4 then return .continue
  let amt := e.getArg! 3
  if amt.isAppOfArity ``BitVec.toNat 2 then
    if let some (_, v) ← evalBitVecLit? (amt.getArg! 1) then
      let newExpr := mkApp4 e.getAppFn (e.getArg! 0) (e.getArg! 1) (e.getArg! 2) (toExpr v)
      return .visit { expr := newExpr }
  return .continue

/-- Construct a canonical `BitVec.ofNat w v` expression using `OfNat.ofNat` numerals (`toExpr : Nat → Expr`)
    instead of `mkRawNatLit` so it matches surface syntax `v#w` and `DiscrTree` keys. -/
@[inline] def mkCanonBitVecLit (w v : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (toExpr w) (toExpr (v % (1 <<< w)))

/-- Reduce `a + b` on ground `BitVec` literals (e.g. `0x10000#64 + 4#64` -> `0x10004#64`)
    so concrete `PC` values immediately match generated `@[arm64_norm]` fetch-decode lemmas. -/
simproc [arm64_norm, wp_norm] reduceBitVecAdd (_ + _) := fun e => do
  if e.getAppNumArgs != 6 then return .continue
  if let some (w1, v1) ← evalBitVecLit? (e.getArg! 4) then
    if let some (w2, v2) ← evalBitVecLit? (e.getArg! 5) then
      if w1 == w2 then
        return .done { expr := mkCanonBitVecLit w1 (v1 + v2) }
  return .continue

/-- Reduce `a - b` on ground `BitVec` literals (e.g. `19#64 - 16#64` -> `3#64`). -/
simproc [arm64_norm, wp_norm] reduceBitVecSub (_ - _) := fun e => do
  if e.getAppNumArgs != 6 then return .continue
  if let some (w1, v1) ← evalBitVecLit? (e.getArg! 4) then
    if let some (w2, v2) ← evalBitVecLit? (e.getArg! 5) then
      if w1 == w2 then
        let m := 1 <<< w1
        return .done { expr := mkCanonBitVecLit w1 ((v1 + m - (v2 % m)) % m) }
  return .continue

/-- Reduce `8 * v.toNat` on ground `BitVec` literals so in-bounds sub-slice bit offsets
    (`8 * (off2 - off1).toNat`) simplify to concrete `Nat` literals without touching standalone `v.toNat`. -/
simproc [arm64_norm, wp_norm] reduceMul8BitVecToNat (8 * BitVec.toNat _) := fun e => do
  if e.getAppNumArgs != 6 then return .continue
  let rhs := e.getArg! 5
  if rhs.getAppNumArgs != 2 then return .continue
  if let some (_, v) ← evalBitVecLit? (rhs.getArg! 1) then
    return .done { expr := toExpr (8 * v) }
  return .continue

/-- If `s` is a non-PC state-update constructor along a `State` spine, return its parent `State` argument. -/
def stateSpineParent? (s : Expr) (includeSetStatus : Bool := true) : Option Expr :=
  if s.isAppOfArity ``State.writeReg64 3 ||
     s.isAppOfArity ``State.writeReg32 3 ||
     s.isAppOfArity ``State.writeReg 4 ||
     s.isAppOfArity ``State.writeVReg128 3 ||
     s.isAppOfArity ``State.writeVReg64 3 ||
     s.isAppOfArity ``State.writeVReg32 3 ||
     s.isAppOfArity ``State.setMem 2 ||
     s.isAppOfArity ``State.setPState 2 ||
     s.isAppOfArity ``State.setBrk 2 ||
     s.isAppOfArity ``State.setPhysMemAvail 2 ||
     s.isAppOfArity ``State.setFs 2 ||
     s.isAppOfArity ``State.nextOracle 1 ||
     s.isAppOfArity ``State.stepExclOracle 1 ||
     s.isAppOfArity ``State.stepExclLoop 1 ||
     s.isAppOfArity ``State.appendTrace 2 ||
     (includeSetStatus && s.isAppOfArity ``State.setStatus 2) ||
     s.isAppOfArity ``State.setFpsr 2 ||
     s.isAppOfArity ``State.orFpsr 2 ||
     s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
    some (s.getArg! 0)
  else
    none

/-- Combine a 1-step spine field equality `stepPrf : proj s = proj s'` with the recursive spine
    extraction `rec? : Option (finalExpr × (proj s' = finalExpr))`. -/
def chainSpineStep (projConst : Name) (s' stepPrf : Expr)
    (rec? : Option (Expr × Expr)) : MetaM (Option (Expr × Expr)) := do
  match rec? with
  | some (finalExpr, restPrf) =>
    return some (finalExpr, ← mkEqTrans stepPrf restPrf)
  | none =>
    return some (mkApp (mkConst projConst) s', stepPrf)

/-- Walk the spine of a symbolic `State` expression to extract `(pcExpr, prf : s.pc = pcExpr)`
    using explicit `State.pc_*` field lemmas instead of `rfl` (which would trigger `O(2^N)`
    structure eta on `State` inside the kernel). -/
partial def extractStatePCProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.setPC 2 then
    let s' := s.getArg! 0
    let pc := s.getArg! 1
    return some (pc, mkApp2 (mkConst ``State.pc_setPC) s' pc)
  if s.isAppOfArity ``State.advancePC 1 then
    let s' := s.getArg! 0
    let stepPrf := mkApp (mkConst ``State.pc_advancePC) s'
    let four := toExpr (4#64)
    match ← extractStatePCProof s' with
    | some (innerExpr, innerPrf) =>
      let addExpr ← mkAppM ``HAdd.hAdd #[innerExpr, four]
      let bv64Ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
      let addFourFn ← withLocalDeclD `x bv64Ty fun x => do
        mkLambdaFVars #[x] (← mkAppM ``HAdd.hAdd #[x, four])
      let congPrf ← mkCongrArg addFourFn innerPrf
      return some (addExpr, ← mkEqTrans stepPrf congPrf)
    | none =>
      let inner := mkApp (mkConst ``State.pc) s'
      let addExpr ← mkAppM ``HAdd.hAdd #[inner, four]
      return some (addExpr, stepPrf)
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pc_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pc_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.pc_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pc_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pc_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pc_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.pc_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.pc_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.pc_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``ProofLib.pc_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pc_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.pc s' stepPrf (← extractStatePCProof s')
  else
    return none


/-- Pre-`simproc` that projects `State.pc` across chains of state updates before `simp`
    descends into register or memory arguments, emitting an explicit `State.pc_*` proof chain. -/
simproc ↓ [arm64_norm, wp_norm] reduceStatePC (State.pc _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (pcExpr, prf) ← extractStatePCProof (e.getArg! 0) then
    return .visit { expr := pcExpr, proof? := some prf }
  return .continue

/-- Walk the spine of a symbolic `State` expression to extract `.status` without traversing
    register values or memory stores. -/
partial def extractStateStatusExpr (s : Expr) : Option Expr :=
  if s.isAppOfArity ``State.setStatus 2 then
    some (s.getArg! 1)
  else if s.isAppOfArity ``State.advancePC 1 || s.isAppOfArity ``State.setPC 2 then
    let s' := s.getArg! 0
    some ((extractStateStatusExpr s').getD (mkApp (mkConst ``State.status) s'))
  else if let some s' := stateSpineParent? s (includeSetStatus := false) then
    some ((extractStateStatusExpr s').getD (mkApp (mkConst ``State.status) s'))
  else
    none

/-- Walk the spine of a symbolic `State` expression to extract `(stExpr, prf : s.status = stExpr)`
    using explicit `State.status_*` field lemmas. -/
partial def extractStateStatusProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.setStatus 2 then
    let s' := s.getArg! 0
    let st := s.getArg! 1
    return some (st, mkApp2 (mkConst ``State.status_setStatus) s' st)
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.status_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.status_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.status_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.status_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.status_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.status_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.status_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.status_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.status_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.status_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``ProofLib.status_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.status_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.status s' stepPrf (← extractStateStatusProof s')
  else
    return none

/-- Pre-`simproc` that projects `State.status` across chains of state updates before `simp`
    descends into register or memory arguments, emitting an explicit `State.status_*` proof chain. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateStatus (State.status _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (stExpr, prf) ← extractStateStatusProof (e.getArg! 0) then
    return .visit { expr := stExpr, proof? := some prf }
  return .continue

/-- Pure `O(1)` recognizer for `RegWidth` / `Width` constants (`.W64`, `.W32`). -/
@[inline] def evalRegWidthPure? (w : Expr) : Option RegWidth :=
  if w.isConstOf ``RegWidth.W64 then some .W64
  else if w.isConstOf ``RegWidth.W32 then some .W32
  else none

def evalRegWidth? (w : Expr) : MetaM (Option RegWidth) := do
  if let some rw := evalRegWidthPure? w then return some rw
  if w.hasFVar || w.hasMVar then return none
  let w' ← whnf w
  return evalRegWidthPure? w'

/-- Pure `O(1)` classifier for ground `Reg` expressions (`Reg.x0`, `Reg.sp`, `Reg.xzr`,
    `Reg.gpr`, `Reg.fromZRBits`, `Reg.fromSPBits`). -/
partial def evalRegKindPure? (r : Expr) : Option Reg :=
  if r.isConstOf ``Reg.sp then some .sp
  else if r.isConstOf ``Reg.xzr then some .xzr
  else if r.isAppOfArity ``Reg.gpr 1 || r.isAppOfArity ``Reg.fromZRBits 1 then
    match evalBitVecLitPure? (r.getArg! 0) with
    | some (5, v) => some (if v == 31 then .xzr else .gpr (BitVec.ofNat 5 v))
    | _ => none
  else if r.isAppOfArity ``Reg.fromSPBits 1 then
    match evalBitVecLitPure? (r.getArg! 0) with
    | some (5, v) => some (if v == 31 then .sp else .gpr (BitVec.ofNat 5 v))
    | _ => none
  else if let .const nm _ := r then
    match nm with
    | ``Reg.x0  => some (.gpr 0#5)
    | ``Reg.x1  => some (.gpr 1#5)
    | ``Reg.x2  => some (.gpr 2#5)
    | ``Reg.x3  => some (.gpr 3#5)
    | ``Reg.x4  => some (.gpr 4#5)
    | ``Reg.x5  => some (.gpr 5#5)
    | ``Reg.x6  => some (.gpr 6#5)
    | ``Reg.x7  => some (.gpr 7#5)
    | ``Reg.x8  => some (.gpr 8#5)
    | ``Reg.x9  => some (.gpr 9#5)
    | ``Reg.x10 => some (.gpr 10#5)
    | ``Reg.x11 => some (.gpr 11#5)
    | ``Reg.x12 => some (.gpr 12#5)
    | ``Reg.x13 => some (.gpr 13#5)
    | ``Reg.x14 => some (.gpr 14#5)
    | ``Reg.x15 => some (.gpr 15#5)
    | ``Reg.x16 => some (.gpr 16#5)
    | ``Reg.x17 => some (.gpr 17#5)
    | ``Reg.x18 => some (.gpr 18#5)
    | ``Reg.x19 => some (.gpr 19#5)
    | ``Reg.x20 => some (.gpr 20#5)
    | ``Reg.x21 => some (.gpr 21#5)
    | ``Reg.x22 => some (.gpr 22#5)
    | ``Reg.x23 => some (.gpr 23#5)
    | ``Reg.x24 => some (.gpr 24#5)
    | ``Reg.x25 => some (.gpr 25#5)
    | ``Reg.x26 => some (.gpr 26#5)
    | ``Reg.x27 => some (.gpr 27#5)
    | ``Reg.x28 => some (.gpr 28#5)
    | ``Reg.x29 | ``Reg.fp => some (.gpr 29#5)
    | ``Reg.x30 | ``Reg.lr => some (.gpr 30#5)
    | _ => none
  else
    none

/-- Classify a ground `Reg` expression into `.gpr idx` (`idx < 31`), `.sp`, or `.xzr`. Falls back
    to `whnf` on closed terms the pure classifier does not recognize. -/
partial def evalRegKind? (r : Expr) : MetaM (Option Reg) := do
  if let some rk := evalRegKindPure? r then return some rk
  if r.isAppOfArity ``Reg.gpr 1 || r.isAppOfArity ``Reg.fromZRBits 1 then
    if let some (5, v) ← evalBitVecLit? (r.getArg! 0) then
      return some (if v == 31 then .xzr else .gpr (BitVec.ofNat 5 v))
  if r.isAppOfArity ``Reg.fromSPBits 1 then
    if let some (5, v) ← evalBitVecLit? (r.getArg! 0) then
      return some (if v == 31 then .sp else .gpr (BitVec.ofNat 5 v))
  if r.hasFVar || r.hasMVar || r.hasLooseBVars then return none
  let wrapperArg? : Option Nat :=
    if r.isAppOfArity ``Reg.gpr 1 || r.isAppOfArity ``Reg.fromZRBits 1 ||
        r.isAppOfArity ``Reg.fromSPBits 1 then some 0
    else none
  if let some i := wrapperArg? then
    let a := r.getArg! i
    let a' ← whnf a
    if a' != a then return ← evalRegKind? (mkAppN r.getAppFn (r.getAppArgs.set! i a'))
  if r.isConst || r.isApp then
    let r' ← whnf r
    if r' != r then return ← evalRegKind? r'
  return none

/-- Canonicalize `Reg` expression `r` given its `evalRegKind?` classification. -/
@[inline] def canonRegExpr (rk : Reg) : Expr :=
  match rk with
  | .sp => mkConst ``Reg.sp
  | .xzr => mkConst ``Reg.xzr
  | .gpr idx => mkApp (mkConst ``Reg.gpr) (mkCanonBitVecLit 5 idx.toNat)

/-- Pre-`dsimproc` that short-circuits `Reg.gpr (BitVec.ofNat 5 idx)` (normalizing raw `.lit`
    indices to `OfNat.ofNat`) so `simp` does not descend into `BitVec.ofNat`, `5`, and `idx`
    at every register read/write node. -/
dsimproc ↓ [arm64_norm, wp_norm] reduceRegGprCanon (Reg.gpr _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (5, v) := evalBitVecLitPure? (e.getArg! 0) then
    return .done (mkApp (mkConst ``Reg.gpr) (mkCanonBitVecLit 5 v))
  return .continue

end

@[expose] public section

def Reg.isSp : Reg → Bool
  | .sp => true
  | _ => false

def Reg.isZeroReg : Reg → Bool
  | .xzr => true
  | .gpr idx => idx == 31#5
  | .sp => false

def Reg.isGprIdx (r : Reg) (idx : BitVec 5) : Bool :=
  match r with
  | .gpr i => i == idx
  | _ => false

def RegWidth.isW64 : RegWidth → Bool
  | .W64 => true
  | .W32 => false

theorem State.sp_writeReg64_of_isSp_true (s : Arm64.State) (r : Reg) (v : BitVec 64)
    (hr : Reg.isSp r = true) :
    (s.writeReg64 r v).sp = v := by
  cases s; cases r with
  | sp => rfl
  | gpr _ | xzr => contradiction

theorem State.sp_writeReg64_of_isSp_false (s : Arm64.State) (r : Reg) (v : BitVec 64)
    (hr : Reg.isSp r = false) :
    (s.writeReg64 r v).sp = s.sp := by
  cases s; cases r with
  | sp => contradiction
  | gpr _ | xzr => rfl

theorem State.sp_writeReg32_of_isSp_true (s : Arm64.State) (r : Reg) (v : BitVec 32)
    (hr : Reg.isSp r = true) :
    (s.writeReg32 r v).sp = v.zeroExtend 64 :=
  State.sp_writeReg64_of_isSp_true s r (v.zeroExtend 64) hr

theorem State.sp_writeReg32_of_isSp_false (s : Arm64.State) (r : Reg) (v : BitVec 32)
    (hr : Reg.isSp r = false) :
    (s.writeReg32 r v).sp = s.sp :=
  State.sp_writeReg64_of_isSp_false s r (v.zeroExtend 64) hr

theorem State.sp_writeReg_w64_of_isSp_true (s : Arm64.State) (w : Width) (r : Reg) (v : BitVec 64)
    (hw : RegWidth.isW64 w = true) (hr : Reg.isSp r = true) :
    (s.writeReg w r v).sp = v := by
  cases w with
  | W64 => exact State.sp_writeReg64_of_isSp_true s r v hr
  | W32 => contradiction

theorem State.sp_writeReg_w32_of_isSp_true (s : Arm64.State) (w : Width) (r : Reg) (v : BitVec 64)
    (hw : RegWidth.isW64 w = false) (hr : Reg.isSp r = true) :
    (s.writeReg w r v).sp = (v.truncate 32).zeroExtend 64 := by
  cases w with
  | W64 => contradiction
  | W32 => exact State.sp_writeReg64_of_isSp_true s r ((v.truncate 32).zeroExtend 64) hr

theorem State.sp_writeReg_of_isSp_false (s : Arm64.State) (w : Width) (r : Reg) (v : BitVec 64)
    (hr : Reg.isSp r = false) :
    (s.writeReg w r v).sp = s.sp := by
  cases w <;> exact State.sp_writeReg64_of_isSp_false s r _ hr

theorem State.readReg64_writeVReg64 (s : Arm64.State) (idx : BitVec 5) (v : BitVec 64) (r : Reg) :
    (s.writeVReg64 idx v).readReg64 r = s.readReg64 r := by
  cases s; rfl

theorem State.readReg64_writeVReg32 (s : Arm64.State) (idx : BitVec 5) (v : BitVec 32) (r : Reg) :
    (s.writeVReg32 idx v).readReg64 r = s.readReg64 r := by
  cases s; rfl

theorem State.readReg64_writeReg64_gpr_same (s : Arm64.State) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hr : Reg.isGprIdx r idx = true) (h31 : (idx == 31#5) = false) :
    (s.writeReg64 r v).readReg64 (.gpr idx) = v := by
  cases s; cases r with
  | gpr idxW =>
    simp only [Reg.isGprIdx, beq_iff_eq] at hr
    subst hr
    simp [Arm64.State.writeReg64, Arm64.State.readReg64, RegFile.read, RegFile.write, h31]
  | sp | xzr => contradiction

theorem State.readReg64_writeReg64_gpr_ne (s : Arm64.State) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hr : Reg.isGprIdx r idx = false) (h31 : (idx == 31#5) = false) :
    (s.writeReg64 r v).readReg64 (.gpr idx) = s.readReg64 (.gpr idx) := by
  cases s; cases r with
  | xzr => rfl
  | sp => rfl
  | gpr idxW =>
    simp only [Reg.isGprIdx] at hr
    have hne : idx ≠ idxW := by
      intro h; subst h; simp at hr
    cases h31w : (idxW == 31#5) <;>
      simp [Arm64.State.writeReg64, Arm64.State.readReg64, RegFile.read, RegFile.write, h31, h31w, hne]

theorem State.readReg64_writeReg32_gpr_same (s : Arm64.State) (r : Reg) (idx : BitVec 5) (v : BitVec 32)
    (hr : Reg.isGprIdx r idx = true) (h31 : (idx == 31#5) = false) :
    (s.writeReg32 r v).readReg64 (.gpr idx) = v.zeroExtend 64 :=
  State.readReg64_writeReg64_gpr_same s r idx (v.zeroExtend 64) hr h31

theorem State.readReg64_writeReg32_gpr_ne (s : Arm64.State) (r : Reg) (idx : BitVec 5) (v : BitVec 32)
    (hr : Reg.isGprIdx r idx = false) (h31 : (idx == 31#5) = false) :
    (s.writeReg32 r v).readReg64 (.gpr idx) = s.readReg64 (.gpr idx) :=
  State.readReg64_writeReg64_gpr_ne s r idx (v.zeroExtend 64) hr h31

theorem State.readReg64_writeReg_w64_gpr_same (s : Arm64.State) (w : Width) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hw : RegWidth.isW64 w = true) (hr : Reg.isGprIdx r idx = true) (h31 : (idx == 31#5) = false) :
    (s.writeReg w r v).readReg64 (.gpr idx) = v := by
  cases w with
  | W64 => exact State.readReg64_writeReg64_gpr_same s r idx v hr h31
  | W32 => contradiction

theorem State.readReg64_writeReg_w32_gpr_same (s : Arm64.State) (w : Width) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hw : RegWidth.isW64 w = false) (hr : Reg.isGprIdx r idx = true) (h31 : (idx == 31#5) = false) :
    (s.writeReg w r v).readReg64 (.gpr idx) = (v.truncate 32).zeroExtend 64 := by
  cases w with
  | W64 => contradiction
  | W32 => exact State.readReg64_writeReg64_gpr_same s r idx ((v.truncate 32).zeroExtend 64) hr h31

theorem State.readReg64_writeReg_gpr_ne (s : Arm64.State) (w : Width) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hr : Reg.isGprIdx r idx = false) (h31 : (idx == 31#5) = false) :
    (s.writeReg w r v).readReg64 (.gpr idx) = s.readReg64 (.gpr idx) := by
  cases w <;> exact State.readReg64_writeReg64_gpr_ne s r idx _ hr h31

theorem State.readReg64_of_isZeroReg (s : Arm64.State) (r : Reg) (hr : Reg.isZeroReg r = true) :
    s.readReg64 r = 0#64 := by
  cases s; cases r with
  | xzr => rfl
  | sp => contradiction
  | gpr idx => simp only [Reg.isZeroReg] at hr; simp [Arm64.State.readReg64, hr]

theorem State.readReg64_of_isSp (s : Arm64.State) (r : Reg) (v : BitVec 64)
    (hr : Reg.isSp r = true) (hsp : s.sp = v) :
    s.readReg64 r = v := by
  cases r with
  | sp => rw [← hsp]; cases s; rfl
  | gpr _ | xzr => contradiction

theorem State.readReg64_of_isGprIdx (s : Arm64.State) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hr : Reg.isGprIdx r idx = true) (hval : s.readReg64 (.gpr idx) = v) :
    s.readReg64 r = v := by
  cases r with
  | gpr i =>
    simp only [Reg.isGprIdx, beq_iff_eq] at hr
    subst hr; exact hval
  | sp | xzr => contradiction

theorem State.readReg32_of_isZeroReg (s : Arm64.State) (r : Reg) (hr : Reg.isZeroReg r = true) :
    s.readReg32 r = 0#32 := by
  cases s; cases r with
  | xzr => rfl
  | sp => contradiction
  | gpr idx => simp only [Reg.isZeroReg] at hr; simp [Arm64.State.readReg32, Arm64.State.readReg64, hr]

theorem State.readReg32_of_isSp (s : Arm64.State) (r : Reg) (v : BitVec 64)
    (hr : Reg.isSp r = true) (hsp : s.sp = v) :
    s.readReg32 r = v.truncate 32 := by
  cases r with
  | sp => rw [← hsp]; cases s; rfl
  | gpr _ | xzr => contradiction

theorem State.readReg32_of_isGprIdx (s : Arm64.State) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hr : Reg.isGprIdx r idx = true) (hval : s.readReg64 (.gpr idx) = v) :
    s.readReg32 r = v.truncate 32 := by
  cases r with
  | gpr i =>
    simp only [Reg.isGprIdx, beq_iff_eq] at hr
    subst hr; rw [← hval]; cases s; rfl
  | sp | xzr => contradiction

theorem State.readReg_of_isZeroReg (s : Arm64.State) (w : Width) (r : Reg) (hr : Reg.isZeroReg r = true) :
    s.readReg w r = 0#64 := by
  cases w with
  | W64 => exact State.readReg64_of_isZeroReg s r hr
  | W32 =>
    change (s.readReg32 r).zeroExtend 64 = 0#64
    rw [State.readReg32_of_isZeroReg s r hr]; rfl

theorem State.readReg_w64_of_isSp (s : Arm64.State) (w : Width) (r : Reg) (v : BitVec 64)
    (hw : RegWidth.isW64 w = true) (hr : Reg.isSp r = true) (hsp : s.sp = v) :
    s.readReg w r = v := by
  cases w with
  | W64 => exact State.readReg64_of_isSp s r v hr hsp
  | W32 => contradiction

theorem State.readReg_w32_of_isSp (s : Arm64.State) (w : Width) (r : Reg) (v : BitVec 64)
    (hw : RegWidth.isW64 w = false) (hr : Reg.isSp r = true) (hsp : s.sp = v) :
    s.readReg w r = (v.truncate 32).zeroExtend 64 := by
  cases w with
  | W64 => contradiction
  | W32 =>
    change (s.readReg32 r).zeroExtend 64 = (v.truncate 32).zeroExtend 64
    rw [State.readReg32_of_isSp s r v hr hsp]

theorem State.readReg_w64_of_isGprIdx (s : Arm64.State) (w : Width) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hw : RegWidth.isW64 w = true) (hr : Reg.isGprIdx r idx = true) (hval : s.readReg64 (.gpr idx) = v) :
    s.readReg w r = v := by
  cases w with
  | W64 => exact State.readReg64_of_isGprIdx s r idx v hr hval
  | W32 => contradiction

theorem State.readReg_w32_of_isGprIdx (s : Arm64.State) (w : Width) (r : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hw : RegWidth.isW64 w = false) (hr : Reg.isGprIdx r idx = true) (hval : s.readReg64 (.gpr idx) = v) :
    s.readReg w r = (v.truncate 32).zeroExtend 64 := by
  cases w with
  | W64 => contradiction
  | W32 =>
    change (s.readReg32 r).zeroExtend 64 = (v.truncate 32).zeroExtend 64
    rw [State.readReg32_of_isGprIdx s r idx v hr hval]

theorem State.writeReg64_of_isZeroReg (s : Arm64.State) (r : Reg) (v : BitVec 64)
    (hr : Reg.isZeroReg r = true) :
    s.writeReg64 r v = s := by
  cases s; cases r with
  | xzr => rfl
  | sp => contradiction
  | gpr idx => simp only [Reg.isZeroReg] at hr; simp [Arm64.State.writeReg64, hr]

theorem State.writeReg32_of_isZeroReg (s : Arm64.State) (r : Reg) (v : BitVec 32)
    (hr : Reg.isZeroReg r = true) :
    s.writeReg32 r v = s :=
  State.writeReg64_of_isZeroReg s r (v.zeroExtend 64) hr

theorem State.writeReg_of_isZeroReg (s : Arm64.State) (w : Width) (r : Reg) (v : BitVec 64)
    (hr : Reg.isZeroReg r = true) :
    s.writeReg w r v = s := by
  cases w <;> exact State.writeReg64_of_isZeroReg s r _ hr

end

public meta section

def reflBoolTrueExpr : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

def reflBoolFalseExpr : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false)

/-- Walk the spine of a symbolic `State` expression to extract `(spExpr, prf : s.sp = spExpr)`
    using explicit `State.sp_*` field lemmas instead of `rfl`. -/
partial def extractStateSPProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.writeReg64 3 then
    let s' := s.getArg! 0
    let r := s.getArg! 1
    let v := s.getArg! 2
    let some rk ← evalRegKind? r | return none
    if rk == .sp then
      return some (v, mkApp4 (mkConst ``State.sp_writeReg64_of_isSp_true) s' r v reflBoolTrueExpr)
    let stepPrf := mkApp4 (mkConst ``State.sp_writeReg64_of_isSp_false) s' r v reflBoolFalseExpr
    return ← chainSpineStep ``State.sp s' stepPrf (← extractStateSPProof s')
  if s.isAppOfArity ``State.writeReg32 3 then
    let s' := s.getArg! 0
    let r := s.getArg! 1
    let v := s.getArg! 2
    let some rk ← evalRegKind? r | return none
    if rk == .sp then
      let ext := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) v
      return some (ext, mkApp4 (mkConst ``State.sp_writeReg32_of_isSp_true) s' r v reflBoolTrueExpr)
    let stepPrf := mkApp4 (mkConst ``State.sp_writeReg32_of_isSp_false) s' r v reflBoolFalseExpr
    return ← chainSpineStep ``State.sp s' stepPrf (← extractStateSPProof s')
  if s.isAppOfArity ``State.writeReg 4 then
    let s' := s.getArg! 0
    let w := s.getArg! 1
    let r := s.getArg! 2
    let v := s.getArg! 3
    let some rw ← evalRegWidth? w | return none
    let some rk ← evalRegKind? r | return none
    if rk == .sp then
      match rw with
      | .W64 =>
        return some (v, mkApp6 (mkConst ``State.sp_writeReg_w64_of_isSp_true) s' w r v reflBoolTrueExpr reflBoolTrueExpr)
      | .W32 =>
        let trunc := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) v
        let ext := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) trunc
        return some (ext, mkApp6 (mkConst ``State.sp_writeReg_w32_of_isSp_true) s' w r v reflBoolFalseExpr reflBoolTrueExpr)
    let stepPrf := mkApp5 (mkConst ``State.sp_writeReg_of_isSp_false) s' w r v reflBoolFalseExpr
    return ← chainSpineStep ``State.sp s' stepPrf (← extractStateSPProof s')
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.sp_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.sp_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.sp_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.sp_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.sp_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.sp_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.sp_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``ProofLib.sp_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.sp_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.sp s' stepPrf (← extractStateSPProof s')
  else
    return none


/-- Pre-`simproc` that projects `State.sp` across chains of state updates before `simp`
    descends into register or memory arguments. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateSP (State.sp _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (spExpr, prf) ← extractStateSPProof (e.getArg! 0) then
    return .visit { expr := spExpr, proof? := some prf }
  return .continue

/-- Combine a 1-step spine register-read equality `stepPrf : s.readReg64 canonReg = s'.readReg64 canonReg`
    with the recursive spine extraction `rec? : Option (finalExpr × (s'.readReg64 canonReg = finalExpr))`. -/
def chainReadReg64SpineStep (s' canonReg stepPrf : Expr)
    (rec? : Option (Expr × Expr)) : MetaM (Option (Expr × Expr)) := do
  match rec? with
  | some (finalExpr, restPrf) =>
    return some (finalExpr, ← mkEqTrans stepPrf restPrf)
  | none =>
    return some (mkApp2 (mkConst ``State.readReg64) s' canonReg, stepPrf)

/-- Walk the spine of a symbolic `State` expression to extract
    `(valExpr, prf : s.readReg64 (.gpr idx) = valExpr)` (`idx < 31`) using explicit
    `State.readReg64_*` lemmas instead of `rfl`. -/
partial def extractStateReadReg64GprProof (s : Expr) (idx : BitVec 5) (canonIdx canonReg : Expr) :
    MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.writeReg64 3 then
    let s' := s.getArg! 0
    let r := s.getArg! 1
    let v := s.getArg! 2
    let some rk ← evalRegKind? r | return none
    if rk == .gpr idx then
      return some (v, mkApp6 (mkConst ``State.readReg64_writeReg64_gpr_same)
        s' r canonIdx v reflBoolTrueExpr reflBoolFalseExpr)
    let stepPrf := mkApp6 (mkConst ``State.readReg64_writeReg64_gpr_ne)
      s' r canonIdx v reflBoolFalseExpr reflBoolFalseExpr
    return ← chainReadReg64SpineStep s' canonReg stepPrf
      (← extractStateReadReg64GprProof s' idx canonIdx canonReg)
  if s.isAppOfArity ``State.writeReg32 3 then
    let s' := s.getArg! 0
    let r := s.getArg! 1
    let v := s.getArg! 2
    let some rk ← evalRegKind? r | return none
    if rk == .gpr idx then
      let ext := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) v
      return some (ext, mkApp6 (mkConst ``State.readReg64_writeReg32_gpr_same)
        s' r canonIdx v reflBoolTrueExpr reflBoolFalseExpr)
    let stepPrf := mkApp6 (mkConst ``State.readReg64_writeReg32_gpr_ne)
      s' r canonIdx v reflBoolFalseExpr reflBoolFalseExpr
    return ← chainReadReg64SpineStep s' canonReg stepPrf
      (← extractStateReadReg64GprProof s' idx canonIdx canonReg)
  if s.isAppOfArity ``State.writeReg 4 then
    let s' := s.getArg! 0
    let w := s.getArg! 1
    let r := s.getArg! 2
    let v := s.getArg! 3
    let some rw ← evalRegWidth? w | return none
    let some rk ← evalRegKind? r | return none
    if rk == .gpr idx then
      match rw with
      | .W64 =>
        return some (v, mkApp8 (mkConst ``State.readReg64_writeReg_w64_gpr_same)
          s' w r canonIdx v reflBoolTrueExpr reflBoolTrueExpr reflBoolFalseExpr)
      | .W32 =>
        let trunc := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) v
        let ext := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) trunc
        return some (ext, mkApp8 (mkConst ``State.readReg64_writeReg_w32_gpr_same)
          s' w r canonIdx v reflBoolFalseExpr reflBoolTrueExpr reflBoolFalseExpr)
    let stepPrf := mkApp7 (mkConst ``State.readReg64_writeReg_gpr_ne)
      s' w r canonIdx v reflBoolFalseExpr reflBoolFalseExpr
    return ← chainReadReg64SpineStep s' canonReg stepPrf
      (← extractStateReadReg64GprProof s' idx canonIdx canonReg)
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.readReg64_advancePC) s' canonReg)
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setPC) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.readReg64_writeVReg128) s' (s.getArg! 1) (s.getArg! 2) canonReg)
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.readReg64_writeVReg64) s' (s.getArg! 1) (s.getArg! 2) canonReg)
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.readReg64_writeVReg32) s' (s.getArg! 1) (s.getArg! 2) canonReg)
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setMem) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setPState) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setBrk) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setPhysMemAvail) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setFs) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.readReg64_nextOracle) s' canonReg)
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.readReg64_stepExclOracle) s' canonReg)
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.readReg64_stepExclLoop) s' canonReg)
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_appendTrace) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setStatus) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``ProofLib.readReg64_setTpidrEl0) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_setFpsr) s' (s.getArg! 1) canonReg)
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.readReg64_orFpsr) s' (s.getArg! 1) canonReg)
    else
      none
  if let some (s', stepPrf) := step? then
    chainReadReg64SpineStep s' canonReg stepPrf
      (← extractStateReadReg64GprProof s' idx canonIdx canonReg)
  else
    return none


/-- Extract `(spExpr, prf : s.sp = spExpr)`, falling back to `Eq.refl (s.sp)` when `s` is not a spine. -/
def extractStateSPProofOrRefl (s : Expr) : MetaM (Expr × Expr) := do
  if let some res ← extractStateSPProof s then
    return res
  let sp0 := mkApp (mkConst ``State.sp) s
  return (sp0, ← mkEqRefl sp0)

/-- Extract `(valExpr, prf : s.readReg64 (.gpr idx) = valExpr)`, falling back to `Eq.refl` when `s` is not a spine. -/
def extractStateReadReg64GprProofOrRefl (s : Expr) (idx : BitVec 5) (canonIdx canonReg : Expr) :
    MetaM (Expr × Expr) := do
  if let some res ← extractStateReadReg64GprProof s idx canonIdx canonReg then
    return res
  let val0 := mkApp2 (mkConst ``State.readReg64) s canonReg
  return (val0, ← mkEqRefl val0)

/-- Pre-`simproc` that projects `State.readReg64` across chains of state updates in `O(spine)`
    using explicit `State.readReg64_*` lemmas instead of `rfl`. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateReadReg64 (State.readReg64 _ _) := fun e => do
  if e.getAppNumArgs != 2 then return .continue
  let s := e.getArg! 0
  let r := e.getArg! 1
  let some rk ← evalRegKind? r | return .continue
  match rk with
  | .xzr =>
    let z := mkCanonBitVecLit 64 0
    let prf := mkApp3 (mkConst ``State.readReg64_of_isZeroReg) s r reflBoolTrueExpr
    return .done { expr := z, proof? := some prf }
  | .sp =>
    let (spExpr, hSp) ← extractStateSPProofOrRefl s
    let prf := mkApp5 (mkConst ``State.readReg64_of_isSp) s r spExpr reflBoolTrueExpr hSp
    return .visit { expr := spExpr, proof? := some prf }
  | .gpr idx =>
    let canonIdx := mkCanonBitVecLit 5 idx.toNat
    let canonReg := mkApp (mkConst ``Reg.gpr) canonIdx
    if let some (valExpr, hVal) ← extractStateReadReg64GprProof s idx canonIdx canonReg then
      let prf := mkApp6 (mkConst ``State.readReg64_of_isGprIdx) s r canonIdx valExpr reflBoolTrueExpr hVal
      return .visit { expr := valExpr, proof? := some prf }
    if r != canonReg then
      let target := mkApp2 (mkConst ``State.readReg64) s canonReg
      let prf := mkApp6 (mkConst ``State.readReg64_of_isGprIdx) s r canonIdx target reflBoolTrueExpr (← mkEqRefl target)
      return .continue (some { expr := target, proof? := some prf })
    return .continue

/-- Pre-`simproc` that projects `State.readReg32` across chains of state updates in `O(spine)`
    before `simp` descends into the state argument `s`. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateReadReg32 (State.readReg32 _ _) := fun e => do
  if e.getAppNumArgs != 2 then return .continue
  let s := e.getArg! 0
  let r := e.getArg! 1
  let some rk ← evalRegKind? r | return .continue
  match rk with
  | .xzr =>
    let z := mkCanonBitVecLit 32 0
    let prf := mkApp3 (mkConst ``State.readReg32_of_isZeroReg) s r reflBoolTrueExpr
    return .done { expr := z, proof? := some prf }
  | .sp =>
    let (spExpr, hSp) ← extractStateSPProofOrRefl s
    let target := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) spExpr
    let prf := mkApp5 (mkConst ``State.readReg32_of_isSp) s r spExpr reflBoolTrueExpr hSp
    return .visit { expr := target, proof? := some prf }
  | .gpr idx =>
    let canonIdx := mkCanonBitVecLit 5 idx.toNat
    let canonReg := mkApp (mkConst ``Reg.gpr) canonIdx
    let (val64, hVal) ← extractStateReadReg64GprProofOrRefl s idx canonIdx canonReg
    let target := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) val64
    let prf := mkApp6 (mkConst ``State.readReg32_of_isGprIdx) s r canonIdx val64 reflBoolTrueExpr hVal
    return .visit { expr := target, proof? := some prf }

/-- Pre-`simproc` that projects `State.readReg` (`W32` and `W64`) across chains of state updates
    in `O(spine)` before `simp` descends into the state argument `s`. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateReadReg (State.readReg _ _ _) := fun e => do
  if e.getAppNumArgs != 3 then return .continue
  let s := e.getArg! 0
  let w := e.getArg! 1
  let r := e.getArg! 2
  let some rw ← evalRegWidth? w | return .continue
  let some rk ← evalRegKind? r | return .continue
  match rk with
  | .xzr =>
    let z := mkCanonBitVecLit 64 0
    let prf := mkApp4 (mkConst ``State.readReg_of_isZeroReg) s w r reflBoolTrueExpr
    return .done { expr := z, proof? := some prf }
  | .sp =>
    let (spExpr, hSp) ← extractStateSPProofOrRefl s
    match rw with
    | .W64 =>
      let prf := mkApp7 (mkConst ``State.readReg_w64_of_isSp) s w r spExpr reflBoolTrueExpr reflBoolTrueExpr hSp
      return .visit { expr := spExpr, proof? := some prf }
    | .W32 =>
      let trunc := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) spExpr
      let target := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) trunc
      let prf := mkApp7 (mkConst ``State.readReg_w32_of_isSp) s w r spExpr reflBoolFalseExpr reflBoolTrueExpr hSp
      return .visit { expr := target, proof? := some prf }
  | .gpr idx =>
    let canonIdx := mkCanonBitVecLit 5 idx.toNat
    let canonReg := mkApp (mkConst ``Reg.gpr) canonIdx
    let (val64, hVal) ← extractStateReadReg64GprProofOrRefl s idx canonIdx canonReg
    match rw with
    | .W64 =>
      let prf := mkApp8 (mkConst ``State.readReg_w64_of_isGprIdx) s w r canonIdx val64 reflBoolTrueExpr reflBoolTrueExpr hVal
      return .visit { expr := val64, proof? := some prf }
    | .W32 =>
      let trunc := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) val64
      let target := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) trunc
      let prf := mkApp8 (mkConst ``State.readReg_w32_of_isGprIdx) s w r canonIdx val64 reflBoolFalseExpr reflBoolTrueExpr hVal
      return .visit { expr := target, proof? := some prf }

/-- Pre-`dsimproc`s that canonicalize `Reg.fromZRBits` / `Reg.fromSPBits` in 1 step at type `Reg`
    (returning `.done` so `simp` does not descend into the `BitVec 5` index). -/
dsimproc ↓ [arm64_norm, wp_norm] reduceRegFromZRBits (Reg.fromZRBits _) := fun e => do
  let some rk := evalRegKindPure? e | return .continue
  return .done (canonRegExpr rk)

dsimproc ↓ [arm64_norm, wp_norm] reduceRegFromSPBits (Reg.fromSPBits _) := fun e => do
  let some rk := evalRegKindPure? e | return .continue
  return .done (canonRegExpr rk)

/-- Pre-`simproc` on `State.writeReg` that discards writes to `.xzr` top-down before simplifying
    `val` (e.g. `CMP`, `CMN`, `TST`) using `State.writeReg_of_isZeroReg`. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateWriteRegXzr (State.writeReg _ _ _ _) := fun e => do
  if e.getAppNumArgs != 4 then return .continue
  let r := e.getArg! 2
  let some rk := evalRegKindPure? r | return .continue
  if rk != .xzr then return .continue
  let s := e.getArg! 0
  let w := e.getArg! 1
  let val := e.getArg! 3
  let prf := mkApp5 (mkConst ``State.writeReg_of_isZeroReg) s w r val reflBoolTrueExpr
  return .visit { expr := s, proof? := some prf }

/-- Pre-`simproc` on `State.writeReg32` that discards writes to `.xzr` top-down before simplifying
    `val` using `State.writeReg32_of_isZeroReg`. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateWriteReg32Xzr (State.writeReg32 _ _ _) := fun e => do
  if e.getAppNumArgs != 3 then return .continue
  let r := e.getArg! 1
  let some rk := evalRegKindPure? r | return .continue
  if rk != .xzr then return .continue
  let s := e.getArg! 0
  let val := e.getArg! 2
  let prf := mkApp4 (mkConst ``State.writeReg32_of_isZeroReg) s r val reflBoolTrueExpr
  return .visit { expr := s, proof? := some prf }

/-- Pre-`simproc` on `State.writeReg64` that discards writes to `.xzr` top-down before simplifying
    `val` using `State.writeReg64_of_isZeroReg`. -/
simproc ↓ [arm64_norm, wp_norm] reduceStateWriteReg64Xzr (State.writeReg64 _ _ _) := fun e => do
  if e.getAppNumArgs != 3 then return .continue
  let r := e.getArg! 1
  let some rk := evalRegKindPure? r | return .continue
  if rk != .xzr then return .continue
  let s := e.getArg! 0
  let val := e.getArg! 2
  let prf := mkApp4 (mkConst ``State.writeReg64_of_isZeroReg) s r val reflBoolTrueExpr
  return .visit { expr := s, proof? := some prf }

/-- Walk the spine of a symbolic `State` expression to extract `(memExpr, prf : s.mem = memExpr)`
    using explicit `State.mem_*` field lemmas instead of `rfl`. -/
partial def extractStateMemProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.setMem 2 then
    let s' := s.getArg! 0
    let m := s.getArg! 1
    return some (m, mkApp2 (mkConst ``State.mem_setMem) s' m)
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.mem_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.mem_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.mem_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.mem_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.mem_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.mem_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.mem_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.mem_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.mem_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.mem_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``ProofLib.mem_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.mem_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.mem s' stepPrf (← extractStateMemProof s')
  else
    return none


simproc ↓ [arm64_norm, wp_norm] reduceStateMem (State.mem _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (memExpr, prf) ← extractStateMemProof (e.getArg! 0) then
    return .visit { expr := memExpr, proof? := some prf }
  return .continue

/-- Walk the spine of a symbolic `State` expression to extract `(psExpr, prf : s.pstate = psExpr)`
    using explicit `State.pstate_*` field lemmas instead of `rfl`. -/
partial def extractStatePStateProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.setPState 2 then
    let s' := s.getArg! 0
    let ps := s.getArg! 1
    return some (ps, mkApp2 (mkConst ``State.pstate_setPState) s' ps)
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.pstate_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pstate_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pstate_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.pstate_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pstate_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pstate_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.pstate_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.pstate_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.pstate_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.pstate_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``ProofLib.pstate_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.pstate_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.pstate s' stepPrf (← extractStatePStateProof s')
  else
    return none

simproc ↓ [arm64_norm, wp_norm] reduceStatePState (State.pstate _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (psExpr, prf) ← extractStatePStateProof (e.getArg! 0) then
    return .visit { expr := psExpr, proof? := some prf }
  return .continue

/-- Walk the spine of a symbolic `State` expression to extract `(brkExpr, prf : s.brk = brkExpr)`
    using explicit `State.brk_*` field lemmas instead of `rfl`. -/
partial def extractStateBrkProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.setBrk 2 then
    let s' := s.getArg! 0
    let b := s.getArg! 1
    return some (b, mkApp2 (mkConst ``State.brk_setBrk) s' b)
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brk_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brk_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brk_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.brk_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brk_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brk_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brk_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brk_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brk_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brk_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brk_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.brk s' stepPrf (← extractStateBrkProof s')
  else
    return none

simproc ↓ [arm64_norm, wp_norm] reduceStateBrk (State.brk _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (brkExpr, prf) ← extractStateBrkProof (e.getArg! 0) then
    return .visit { expr := brkExpr, proof? := some prf }
  return .continue

/-- Walk the spine of a symbolic `State` expression to extract `(bsExpr, prf : s.brkStart = bsExpr)`
    using explicit `State.brkStart_*` field lemmas instead of `rfl`. -/
partial def extractStateBrkStartProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brkStart_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brkStart_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brkStart_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.brkStart_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brkStart_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brkStart_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.brkStart_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brkStart_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brkStart_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.brkStart_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.brkStart_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.brkStart s' stepPrf (← extractStateBrkStartProof s')
  else
    return none

simproc ↓ [arm64_norm, wp_norm] reduceStateBrkStart (State.brkStart _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (bsExpr, prf) ← extractStateBrkStartProof (e.getArg! 0) then
    return .visit { expr := bsExpr, proof? := some prf }
  return .continue


/-- Walk the spine of a symbolic `State` expression to extract `(oExpr, prf : s.oracle = oExpr)`
    using explicit `State.oracle_*` field lemmas instead of `rfl`. -/
partial def extractStateOracleProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.nextOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.oracle_nextOracle) s')
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.oracle_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.oracle_stepExclLoop) s')
    else if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.oracle_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracle_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracle_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.oracle_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracle_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracle_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracle_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracle_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.oracle s' stepPrf (← extractStateOracleProof s')
  else
    return none

simproc ↓ [arm64_norm, wp_norm] reduceStateOracle (State.oracle _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (oExpr, prf) ← extractStateOracleProof (e.getArg! 0) then
    return .visit { expr := oExpr, proof? := some prf }
  return .continue

/-- Walk the spine of a symbolic `State` expression to extract `(idxExpr, prf : s.oracleIdx = idxExpr)`
    using explicit `State.oracleIdx_*` field lemmas instead of `rfl`. -/
partial def extractStateOracleIdxProof (s : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.nextOracle 1 then
    let s' := s.getArg! 0
    let stepPrf := mkApp (mkConst ``State.oracleIdx_nextOracle) s'
    let one := mkNatLit 1
    match ← extractStateOracleIdxProof s' with
    | some (innerExpr, innerPrf) =>
      let addExpr ← mkAppM ``HAdd.hAdd #[innerExpr, one]
      let addOneFn ← withLocalDeclD `x (mkConst ``Nat) fun x => do
        mkLambdaFVars #[x] (← mkAppM ``HAdd.hAdd #[x, one])
      let congPrf ← mkCongrArg addOneFn innerPrf
      return some (addExpr, ← mkEqTrans stepPrf congPrf)
    | none =>
      let inner := mkApp (mkConst ``State.oracleIdx) s'
      let addExpr ← mkAppM ``HAdd.hAdd #[inner, one]
      return some (addExpr, stepPrf)
  let step? : Option (Expr × Expr) :=
    if s.isAppOfArity ``State.advancePC 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.oracleIdx_advancePC) s')
    else if s.isAppOfArity ``State.setPC 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setPC) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.writeReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracleIdx_writeReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracleIdx_writeReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeReg 4 then
      let s' := s.getArg! 0
      some (s', mkApp4 (mkConst ``State.oracleIdx_writeReg) s' (s.getArg! 1) (s.getArg! 2) (s.getArg! 3))
    else if s.isAppOfArity ``State.writeVReg128 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracleIdx_writeVReg128) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg64 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracleIdx_writeVReg64) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.writeVReg32 3 then
      let s' := s.getArg! 0
      some (s', mkApp3 (mkConst ``State.oracleIdx_writeVReg32) s' (s.getArg! 1) (s.getArg! 2))
    else if s.isAppOfArity ``State.setMem 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setMem) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPState 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setPState) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setBrk 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setBrk) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setPhysMemAvail 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setPhysMemAvail) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFs 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setFs) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.stepExclOracle 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.oracleIdx_stepExclOracle) s')
    else if s.isAppOfArity ``State.stepExclLoop 1 then
      let s' := s.getArg! 0
      some (s', mkApp (mkConst ``State.oracleIdx_stepExclLoop) s')
    else if s.isAppOfArity ``State.appendTrace 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_appendTrace) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setStatus 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setStatus) s' (s.getArg! 1))
    else if s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setTpidrEl0) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.setFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_setFpsr) s' (s.getArg! 1))
    else if s.isAppOfArity ``State.orFpsr 2 then
      let s' := s.getArg! 0
      some (s', mkApp2 (mkConst ``State.oracleIdx_orFpsr) s' (s.getArg! 1))
    else
      none
  if let some (s', stepPrf) := step? then
    chainSpineStep ``State.oracleIdx s' stepPrf (← extractStateOracleIdxProof s')
  else
    return none

simproc ↓ [arm64_norm, wp_norm] reduceStateOracleIdx (State.oracleIdx _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  let s := e.getArg! 0
  if let some (idxExpr, prf) ← extractStateOracleIdxProof s then
    return .visit { expr := idxExpr, proof? := some prf }
  return .continue

/-- `mkBaseOffEqProof?` via `ProofLib.BV.Lin.diffConst?`: if `a - b` normalizes to a constant
    `c` (`0 ≤ c < 2^64`), return `(c#64, haPrf, c)` with `haPrf : b + c#64 = a`. The proof is a
    kernel-checked reflective normal-form comparison. -/
def mkBaseOffEqProofLin? (b a : Expr) : MetaM (Option (Expr × Expr × Nat)) := do
  let some (c, pf) ← ProofLib.BV.Lin.diffConst? a b | return none
  -- `pf : a = b + c` with `c` the numeral `ProofLib.BV.Lin.mkBVLit w c`
  let some (_, _, rhs) := (← inferType pf).eq? | return none
  return some (rhs.appArg!, ← mkEqSymm pf, c)

/-- If `a` is at a constant non-negative offset `offNat` from region base `b`, return
    `some (offExpr, haPrf, offNat)` where `haPrf : b + offExpr = a`. -/
def mkBaseOffEqProof? (b a : Expr) : MetaM (Option (Expr × Expr × Nat)) := do
  if a == b then
    let offExpr := toExpr (0#64)
    let haPrf := mkApp2 (mkConst ``Arm64.bitvec_add_zero) (toExpr 64) b
    return some (offExpr, haPrf, 0)
  if a.isAppOfArity ``HAdd.hAdd 6 && a.getArg! 4 == b then
    if let some (64, offNat) ← evalBitVecLit? (a.getArg! 5) then
      let offExpr := a.getArg! 5
      let haPrf ← mkEqRefl a
      return some (offExpr, haPrf, offNat)
  if b.isAppOfArity ``HSub.hSub 6 then
    let x := b.getArg! 4
    let c1 := b.getArg! 5
    if let some (64, v1) ← evalBitVecLit? c1 then
      if a.isAppOfArity ``HSub.hSub 6 && a.getArg! 4 == x then
        let c2 := a.getArg! 5
        if let some (64, v2) ← evalBitVecLit? c2 then
          if v2 <= v1 then
            let offNat := v1 - v2
            let offExpr := toExpr (BitVec.ofNat 64 offNat)
            let haPrf := mkApp5 (mkConst ``ProofLib.sub_add_eq_sub) x c1 offExpr c2 (← mkEqRefl (mkConst ``true))
            return some (offExpr, haPrf, offNat)
      else if a.isAppOfArity ``HAdd.hAdd 6 && (a.getArg! 4).isAppOfArity ``HSub.hSub 6 && (a.getArg! 4).getArg! 4 == x then
        let c2 := (a.getArg! 4).getArg! 5
        let c3 := a.getArg! 5
        if let some (64, v2) ← evalBitVecLit? c2 then
          if let some (64, v3) ← evalBitVecLit? c3 then
            if v2 <= v1 + v3 && v1 + v3 - v2 < (1 <<< 64) then
              let offNat := v1 + v3 - v2
              let offExpr := toExpr (BitVec.ofNat 64 offNat)
              let haPrf := mkApp6 (mkConst ``ProofLib.sub_add_eq_sub_add) x c1 offExpr c2 c3 (← mkEqRefl (mkConst ``true))
              return some (offExpr, haPrf, offNat)
  if b.isAppOfArity ``HAdd.hAdd 6 then
    let x := b.getArg! 4
    let c1 := b.getArg! 5
    if let some (64, v1) ← evalBitVecLit? c1 then
      if a.isAppOfArity ``HAdd.hAdd 6 && a.getArg! 4 == x then
        let c2 := a.getArg! 5
        if let some (64, v2) ← evalBitVecLit? c2 then
          if v1 <= v2 then
            let offNat := v2 - v1
            let offExpr := toExpr (BitVec.ofNat 64 offNat)
            let haPrf := mkApp5 (mkConst ``ProofLib.add_add_eq_add) x c1 offExpr c2 (← mkEqRefl (mkConst ``true))
            return some (offExpr, haPrf, offNat)
  -- General path: `a - b` normalizes to a constant in the certified linear normal form
  -- (any `+`/`-`/constant-`*`/`<<<` shape, atoms in any order).
  mkBaseOffEqProofLin? b a

def disjointRegionsReadWriteLemma? (readBytes writeBytes : Nat) : Option Name :=
  match readBytes, writeBytes with
  | 1, 1   => some ``Arm64.Memory.read8_write8_of_disjointRegions_left
  | 1, 2   => some ``Arm64.Memory.read8_write16_of_disjointRegions_left
  | 1, 4   => some ``Arm64.Memory.read8_write32_of_disjointRegions_left
  | 1, 8   => some ``Arm64.Memory.read8_write64_of_disjointRegions_left
  | 1, 16  => some ``ProofLib.read8_write128_of_disjointRegions_l
  | 2, 1   => some ``Arm64.Memory.read16_write8_of_disjointRegions_left
  | 2, 2   => some ``Arm64.Memory.read16_write16_of_disjointRegions_left
  | 2, 4   => some ``Arm64.Memory.read16_write32_of_disjointRegions_left
  | 2, 8   => some ``Arm64.Memory.read16_write64_of_disjointRegions_left
  | 2, 16  => some ``ProofLib.read16_write128_of_disjointRegions_l
  | 4, 1   => some ``Arm64.Memory.read32_write8_of_disjointRegions_left
  | 4, 2   => some ``Arm64.Memory.read32_write16_of_disjointRegions_left
  | 4, 4   => some ``Arm64.Memory.read32_write32_of_disjointRegions_left
  | 4, 8   => some ``Arm64.Memory.read32_write64_of_disjointRegions_left
  | 4, 16  => some ``ProofLib.read32_write128_of_disjointRegions_l
  | 8, 1   => some ``Arm64.Memory.read64_write8_of_disjointRegions_left
  | 8, 2   => some ``Arm64.Memory.read64_write16_of_disjointRegions_left
  | 8, 4   => some ``Arm64.Memory.read64_write32_of_disjointRegions_left
  | 8, 8   => some ``Arm64.Memory.read64_write64_of_disjoint64_left
  | 8, 16  => some ``ProofLib.read64_write128_of_disjointRegions_l
  | 16, 1  => some ``ProofLib.read128_write8_of_disjointRegions_l
  | 16, 2  => some ``ProofLib.read128_write16_of_disjointRegions_l
  | 16, 4  => some ``ProofLib.read128_write32_of_disjointRegions_l
  | 16, 8  => some ``ProofLib.read128_write64_of_disjointRegions_l
  | 16, 16 => some ``ProofLib.read128_write128_of_disjoint128
  | _, _   => none

def extractDisjointRegionsArgs? (ty : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if ty.isAppOfArity ``Arm64.DisjointRegions 4 then
    some (ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3)
  else if ty.isAppOfArity ``Arm64.Memory.Disjoint64 2 then
    some (ty.getArg! 0, toExpr (8 : Nat), ty.getArg! 1, toExpr (8 : Nat))
  else if ty.isAppOfArity ``Arm64.Memory.Disjoint128 2 then
    some (ty.getArg! 0, toExpr (16 : Nat), ty.getArg! 1, toExpr (16 : Nat))
  else
    none

/-- Try to prove `(m.writeW a1 v).readR a2 = m.readR a2` from a `DisjointRegions` proof `prf : ty`
    (or a structure hypothesis whose fields contain `DisjointRegions`). -/
partial def tryDisjointRegionsReadWrite? (readBytes writeBytes : Nat) (lemmaName : Name)
    (m a1 a2 v prf ty : Expr) (depth : Nat := 2) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  if let some (b1, n1Expr, b2, n2Expr) := extractDisjointRegionsArgs? ty then
    if let some n1Val ← evalNatLit? n1Expr then
      if let some n2Val ← evalNatLit? n2Expr then
        if n1Val <= (1 <<< 64) && n2Val <= (1 <<< 64) then
          if let some (off1Expr, ha1Prf, off1Nat) ← mkBaseOffEqProof? b1 a1 then
            if off1Nat + writeBytes <= n1Val then
              if let some (off2Expr, ha2Prf, off2Nat) ← mkBaseOffEqProof? b2 a2 then
                if off2Nat + readBytes <= n2Val then
                  let subPrf := mkAppN (mkConst ``Arm64.DisjointRegions.sub_at)
                    #[b1, b2, n1Expr, n2Expr, prf, toExpr writeBytes, toExpr readBytes,
                      a1, a2, off1Expr, off2Expr, ha1Prf, ha2Prf, ← mkEqRefl (mkConst ``true)]
                  return some (mkApp5 (mkConst lemmaName) m a1 a2 v subPrf)
          if let some (off2Expr, ha1Prf, off2Nat) ← mkBaseOffEqProof? b2 a1 then
            if off2Nat + writeBytes <= n2Val then
              if let some (off1Expr, ha2Prf, off1Nat) ← mkBaseOffEqProof? b1 a2 then
                if off1Nat + readBytes <= n1Val then
                  let subPrf := mkAppN (mkConst ``Arm64.DisjointRegions.sub_at_symm)
                    #[b1, b2, n1Expr, n2Expr, prf, toExpr writeBytes, toExpr readBytes,
                      a1, a2, off1Expr, off2Expr, ha1Prf, ha2Prf, ← mkEqRefl (mkConst ``true)]
                  return some (mkApp5 (mkConst lemmaName) m a1 a2 v subPrf)
    return none
  if depth > 0 && ty.getAppFn.isConst then
    let cName := ty.getAppFn.constName!
    let env ← getEnv
    if isStructure env cName && cName != ``BitVec && cName != ``Fin then
      for fieldName in getStructureFields env cName do
        let projOpt ← try
          let projExpr ← mkProjection prf fieldName
          let projTy ← inferType projExpr
          pure (some (projExpr, projTy))
        catch _ =>
          pure none
        if let some (projExpr, projTy) := projOpt then
          if let some res ← tryDisjointRegionsReadWrite? readBytes writeBytes lemmaName m a1 a2 v projExpr projTy (depth - 1) then
            return some res
  return none

def extractMemWriteApp? (memExpr : Expr) : Option (Nat × Expr × Expr × Expr) :=
  if memExpr.isAppOfArity ``Memory.write64 3 then
    some (8, memExpr.getArg! 0, memExpr.getArg! 1, memExpr.getArg! 2)
  else if memExpr.isAppOfArity ``Memory.write32 3 then
    some (4, memExpr.getArg! 0, memExpr.getArg! 1, memExpr.getArg! 2)
  else if memExpr.isAppOfArity ``Memory.write16 3 then
    some (2, memExpr.getArg! 0, memExpr.getArg! 1, memExpr.getArg! 2)
  else if memExpr.isAppOfArity ``Memory.write8 3 then
    some (1, memExpr.getArg! 0, memExpr.getArg! 1, memExpr.getArg! 2)
  else if memExpr.isAppOfArity ``Memory.write128 3 then
    some (16, memExpr.getArg! 0, memExpr.getArg! 1, memExpr.getArg! 2)
  else
    none

def reduceReadWriteDisjointRegionsAux (readConst : Name) (readBytes : Nat) (e : Expr) : SimpM Simp.Step := do
  if !e.isAppOfArity readConst 2 then return .continue
  let memExpr := e.getArg! 0
  let a2 := e.getArg! 1
  let some (writeBytes, m, a1, v) := extractMemWriteApp? memExpr | return .continue
  if a1 == a2 then return .continue
  let some lemmaName := disjointRegionsReadWriteLemma? readBytes writeBytes | return .continue
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      if let some prf ← tryDisjointRegionsReadWrite? readBytes writeBytes lemmaName m a1 a2 v decl.toExpr decl.type then
        return .visit { expr := mkApp2 (mkConst readConst) m a2, proof? := some prf }
  return .continue

/-- Reduce `(m.writeW a1 v).readR a2` to `m.readR a2` across all widths `R, W ∈ {8, 16, 32, 64, 128}`
    whenever any `DisjointRegions` hypothesis (or `Disjoint` structure field) in the local context separates `a1` and `a2`. -/
simproc [arm64_norm] reduceRead8WriteDisjointRegions (Memory.read8 _ _) :=
  reduceReadWriteDisjointRegionsAux ``Memory.read8 1

simproc [arm64_norm] reduceRead16WriteDisjointRegions (Memory.read16 _ _) :=
  reduceReadWriteDisjointRegionsAux ``Memory.read16 2

simproc [arm64_norm] reduceRead32WriteDisjointRegions (Memory.read32 _ _) :=
  reduceReadWriteDisjointRegionsAux ``Memory.read32 4

simproc [arm64_norm] reduceRead64WriteDisjointRegions (Memory.read64 _ _) :=
  reduceReadWriteDisjointRegionsAux ``Memory.read64 8

simproc [arm64_norm] reduceRead128WriteDisjointRegions (Memory.read128 _ _) :=
  reduceReadWriteDisjointRegionsAux ``Memory.read128 16

/-- `simproc` that evaluates `decode w` on 32-bit machine code words in compiled `MetaM` and
    replaces it with the concrete `Option Instr` AST. The equation is justified by a
    kernel-checked `decide` proof (no `Lean.ofReduceBool`). -/
simproc [arm64_norm] reduceDecode (decode _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  let rawArg := e.getArg! 0
  let arg ← whnf rawArg
  if arg.isAppOfArity ``BitVec.ofNat 2 then
    if let some v ← evalNatLit? (arg.getArg! 1) then
      let res := Arm64.decode (BitVec.ofNat 32 v)
      let resExpr := toExpr res
      let prf ← mkKernelDecideEqProof e resExpr
      return .done { expr := resExpr, proof? := some prf }
  return .continue

/-- Reduce `BitVec.ofNat w exp` when `exp` is a compound ground `Nat` expression (e.g. bitfield masks). -/
simproc [arm64_norm] reduceBitVecOfNat (BitVec.ofNat _ _) := fun e => do
  if e.getAppNumArgs != 2 then return .continue
  let wExpr := e.getArg! 0
  let nExpr := e.getArg! 1
  if nExpr.isAppOfArity ``OfNat.ofNat 3 then return .continue
  if let some w ← evalNatLit? wExpr then
    if let some n ← evalNatLit? nExpr then
      return .done { expr := toExpr (BitVec.ofNat w n) }
  return .continue

/-- Evaluate `pageAlignUp n` (the `mmap` length rounding) when `n` is a ground `Nat` expression
    (e.g. `(4#64).toNat`). -/
simproc [arm64_norm] reducePageAlignUp (pageAlignUp _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  let arg := e.getArg! 0
  if let some n ← evalNatLit? arg then
    return .done { expr := mkNatLit (pageAlignUp n) }
  if arg.isAppOfArity ``BitVec.toNat 2 then
    if let some (_, v) ← evalBitVecLit? (arg.getArg! 1) then
      return .done { expr := mkNatLit (pageAlignUp v) }
  return .continue

/-- Reduce `BitVec.zeroExtend w v` / `BitVec.truncate w v` when `v` is a ground `BitVec` literal. -/
simproc [arm64_norm] reduceBitVecZeroExtend (BitVec.zeroExtend _ _) := fun e => do
  if e.getAppNumArgs != 3 then return .continue
  if let some w ← evalNatLit? (e.getArg! 1) then
    if let some (_, v) ← evalBitVecLit? (e.getArg! 2) then
      return .done { expr := toExpr (BitVec.ofNat w v) }
  return .continue

/-- Reduce `Memory.readBytes m base v.toNat` when `v` is a ground `BitVec` literal. -/
simproc [arm64_norm] reduceReadBytesToNat (Memory.readBytes _ _ (BitVec.toNat _)) := fun e => do
  if e.getAppNumArgs != 3 then return .continue
  let cntExpr := e.getArg! 2
  if cntExpr.getAppNumArgs != 2 then return .continue
  if let some (_, v) ← evalBitVecLit? (cntExpr.getArg! 1) then
    return .visit { expr := mkApp3 e.getAppFn (e.getArg! 0) (e.getArg! 1) (mkNatLit v) }
  return .continue

/-- Reduce `x <<< exp` when `x` and `exp : Nat` are ground literals, or when `exp : Nat` is a
    compound ground `Nat` expression (e.g. `64 - 48 % 64`). -/
simproc [arm64_norm] reduceHShiftLeft (_ <<< _) := fun e => do
  if e.getAppNumArgs != 6 then return .continue
  if let some (w, v) ← evalBitVecLit? e then
    return .done { expr := toExpr (BitVec.ofNat w v) }
  let rhs := e.getArg! 5
  if rhs.isAppOfArity ``OfNat.ofNat 3 then return .continue
  let rhsTy ← inferType rhs
  if rhsTy.isConstOf ``Nat then
    if let some n ← evalNatLit? rhs then
      let rhs' ← mkNumeral rhsTy n
      return .done { expr := mkApp (mkAppN e.getAppFn (e.getAppArgs.extract 0 5)) rhs' }
  return .continue

/-- Reduce `x >>> exp` when `x` and `exp : Nat` are ground literals, or when `exp : Nat` is a
    compound ground `Nat` expression (e.g. `8 % 64`). -/
simproc [arm64_norm] reduceHShiftRight (_ >>> _) := fun e => do
  if e.getAppNumArgs != 6 then return .continue
  if let some (w, v) ← evalBitVecLit? e then
    return .done { expr := toExpr (BitVec.ofNat w v) }
  let rhs := e.getArg! 5
  if rhs.isAppOfArity ``OfNat.ofNat 3 then return .continue
  let rhsTy ← inferType rhs
  if rhsTy.isConstOf ``Nat then
    if let some n ← evalNatLit? rhs then
      let rhs' ← mkNumeral rhsTy n
      return .done { expr := mkApp (mkAppN e.getAppFn (e.getAppArgs.extract 0 5)) rhs' }
  return .continue

/-- If the main goal is an implication `s.spAligned = true → ...` (or its unfolded form
    `(s.sp &&& 0b1111#64 == 0#64) = true → ...`), automatically introduce the SP alignment
    hypothesis into the local context and normalize it. -/
def introSpAlignedIfPresent : TacticM Unit := do
  let gs ← getGoals
  let g :: rest := gs | return
  let isSpAlignImp ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if let .forallE _ dom body _ := ty then
      if !body.hasLooseBVars then
        let dom := (← instantiateMVars dom).consumeMData
        if (dom.find? (·.isConstOf ``State.spAligned)).isSome then
          return true
        let body := body.consumeMData
        if body.isAppOf ``Arm64.reaches_pc || body.isAppOf ``Arm64.exits_with then
          if (dom.find? (·.isConstOf ``State.sp)).isSome &&
             (dom.find? (·.isConstOf ``HAnd.hAnd)).isSome then
            return true
    return false
  if isSpAlignImp then
    let (_, g') ← g.intro `_hsp_align
    setGoals (g' :: rest)
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [State.spAligned] at *)))

/-- Find which locations make `simp (config := { decide := true }) only [arm64_norm]` exceed
    `maxRecDepth` on their own, by re-running it on the goal and on each hypothesis separately
    (at most `maxTries` locations). State is restored after every probe. -/
def arm64NormMaxRecDepthCulprits (maxTries : Nat := 48) : TacticM (Array MessageData) := do
  let g ← getMainGoal
  let hyps ← g.withContext do
    let mut hs : Array (TSyntax `ident) := #[]
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.userName.hasMacroScopes then
        hs := hs.push (mkIdent decl.userName)
    pure hs
  let probes : Array (MessageData × TacticM Unit) :=
    #[(m!"the goal", do evalTactic (← `(tactic|
        simp (config := { decide := true }) only [arm64_norm])))] ++
    hyps.map fun h => (m!"hypothesis `{h.getId}`", do evalTactic (← `(tactic|
        simp (config := { decide := true }) only [arm64_norm] at $h:ident)))
  let mut culprits := #[]
  for (label, probe) in probes.extract 0 maxTries do
    let saved ← saveState
    -- `tryCatchRuntimeEx` also catches ordinary errors (e.g. "simp made no progress").
    let hit ← MaxRecDepthDiag.withFreshRecDepth <|
      MonadRuntimeException.tryCatchRuntimeEx (do probe; pure false)
        (fun ex => pure (MaxRecDepthDiag.isMaxRecDepthEx ex))
    saved.restore (restoreInfo := true)
    if hit then culprits := culprits.push label
  return culprits

/-- Implementation of `arm64_norm`: `simp (config := { decide := true }) only [arm64_norm] at *`,
    but a `maxRecDepth` failure is rethrown with the location(s) that trigger it, the deepest
    terms in the context, and concrete remedies. The rethrown error keeps the
    `nested.runtime.maxRecDepth` tag, so `try` / `first` still propagate it exactly like the
    plain `simp` error. -/
def arm64NormCore : TacticM Unit := do
  let saved ← saveState
  MonadRuntimeException.tryCatchRuntimeEx
    (evalTactic (← `(tactic| simp (config := { decide := true }) only [arm64_norm] at *)))
    fun ex => do
      unless MaxRecDepthDiag.isMaxRecDepthEx ex do throw ex
      saved.restore (restoreInfo := true)
      let g ← getMainGoal
      let culprits ← arm64NormMaxRecDepthCulprits
      let report ← MaxRecDepthDiag.maxRecDepthContextReport g
        m!"the `arm64_norm` lemmas are meant to be confluent on their own, so check extra lemmas or simp sets combined with them in an enclosing `simp [..., arm64_norm]` (e.g. width or literal normalization sets that rewrite the same subterms back and forth), and drop them or apply them in a separate `simp only` call"
      let where_ : MessageData :=
        if culprits.isEmpty then m!" (no single location reaches the limit on its own; the combined `at *` traversal does)"
        else m!" while normalizing " ++ MessageData.joinSep culprits.toList m!", "
      throw <| .error (← getRef) <| .tagged `nested.runtime.maxRecDepth <|
        .tagged MaxRecDepthDiag.diagTag <|
        m!"arm64_norm: maximum recursion depth (`maxRecDepth`) reached{where_}" ++ report

/-- Normalize ARM64 state, register, flag, and memory expressions
    (`simp (config := { decide := true }) only [arm64_norm] at *`). On `maxRecDepth` it reports
    which goal/hypothesis triggers it, the deepest terms, and how to shrink them. -/
elab "arm64_norm" : tactic => arm64NormCore

/-- Split hypothesis `h` only while its type is a syntactic `And`, without unfolding `DisjointRegions`. -/
def arm64SplitDisjointHypImpl (h : Ident) : TacticM Unit := do
  let mut progress := true
  while progress do
    progress := false
    let mvarId ← getMainGoal
    let lctx ← mvarId.withContext getLCtx
    if let some decl := lctx.findFromUserName? h.getId then
      let ty ← mvarId.withContext (instantiateMVars decl.type)
      if ty.isAppOfArity ``And 2 then
        if (← tryTactic (evalTactic (← `(tactic| rcases $h:ident with ⟨_, $h:ident⟩)))) then
          progress := true

elab "arm64_split_disjoint_hyp_internal " h:ident : tactic =>
  arm64SplitDisjointHypImpl h

macro "arm64_stack_preserved_internal" : tactic =>
  `(tactic| (
    intro _parent_len _h_stack_bound _h_stack_disjoint
    try simp (config := { decide := true }) only [arm64_norm, *] at _h_stack_disjoint
    arm64_split_disjoint_hyp_internal _h_stack_disjoint
    repeat' (first
      | exact Arm64.StackPreserved.rfl
      | with_reducible assumption
      | apply Arm64.StackPreserved.write64
      | apply Arm64.StackPreserved.write32
      | apply Arm64.StackPreserved.write16
      | apply Arm64.StackPreserved.write8
      | apply Arm64.StackPreserved.write128)
    all_goals (
      first
        | done
        | with_reducible assumption
        | (exact ⟨by with_reducible assumption, by with_reducible assumption⟩)
        | (apply Arm64.DisjointRegions.of_stack_frame_bv _h_stack_bound (by decide);
           simp only [Arm64.sub_add_left_cancel, Arm64.sub_add_add_left_cancel,
                      Arm64.sub_sub_left_cancel, Arm64.sub_sub_add_left_cancel,
                      ProofLib.bitvec_add_neg_eq_sub, arm64_norm];
           first | decide | bv_omega)
        | (simp only [Arm64.DisjointRegions] at *; bv_omega; done)
        | assumption
        | (bv_fallback; done)
        | (omega; done)
    )
  ))

/-- Add the content facts (`Memory.read*` equalities) and pairwise `DisjointRegions` facts of the
    blocks of every `m ⊨ Full` hypothesis to the local context (`SepSolver.blockFacts`). -/
def extractSepHypFacts : TacticM Unit := do
  let mvarId0 ← getMainGoal
  let newProofs ← mvarId0.withContext do
    let lctx ← getLCtx
    let mut newProofs : Array (Name × Expr × Expr × Bool) := #[]
    let mut idx : Nat := 0
    for decl in lctx do
      if decl.isImplementationDetail || decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      unless ty.isAppOfArity ``SepProp.Satisfies 2 do continue
      let (reads, disj) ← SepSolver.blockFacts (ty.getArg! 1) (ty.getArg! 0) decl.toExpr
      for (prfs, isRead) in [(reads, true), (disj, false)] do
        for prf in prfs do
          let t ← instantiateMVars (← inferType prf)
          if lctx.any (fun d => !d.isImplementationDetail && d.type == t) ||
              newProofs.any (fun (_, _, pt, _) => pt == t) then continue
          idx := idx + 1
          let nm := Name.mkSimple s!"{if isRead then "_h_sep_read_" else "_h_sep_disj_"}{idx}"
          newProofs := newProofs.push (nm, prf, t, isRead)
    return newProofs
  if newProofs.isEmpty then return
  let mut mvarId ← getMainGoal
  let mut readIdents : Array (TSyntax `ident) := #[]
  for (nm, prf, ty, isRead) in newProofs do
    mvarId ← mvarId.assert nm ty prf
    let (_, mvarId') ← mvarId.intro1P
    mvarId := mvarId'
    if isRead then
      readIdents := readIdents.push (mkIdent nm)
  replaceMainGoal [mvarId]
  if !readIdents.isEmpty then
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [arm64_norm] at $[$readIdents:ident]*)))

end

@[expose] public section

@[simp, arm64_norm]
theorem bitvec_sub_add_cancel (x c : BitVec 64) : (x - c) + c = x := by
  bv_lin

@[simp, arm64_norm]
theorem bitvec_add_sub_cancel (x c : BitVec 64) : (x + c) - c = x := by
  bv_lin

theorem bitvec_sub16_add8 (x : BitVec 64) : (x - 16#64) + 8#64 = x - 8#64 := by
  bv_lin

theorem bitvec_sub8_add8 (x : BitVec 64) : (x - 8#64) + 8#64 = x := by
  bv_lin

theorem bitvec_sub32_add8 (x : BitVec 64) : (x - 32#64) + 8#64 = x - 24#64 := by
  bv_lin

theorem bitvec_sub32_add16 (x : BitVec 64) : (x - 32#64) + 16#64 = x - 16#64 := by
  bv_lin

theorem bitvec_sub32_add24 (x : BitVec 64) : (x - 32#64) + 24#64 = x - 8#64 := by
  bv_lin

theorem bitvec_sub16_sub16 (x : BitVec 64) : x - 16#64 - 16#64 = x - 32#64 := by
  bv_lin

theorem bitvec_sub16_sub8 (x : BitVec 64) : x - 16#64 - 8#64 = x - 24#64 := by
  bv_lin

end

public meta section

/-- Prove an `InRegion` or offset bound subgoal for `AgreesOutside` write stepping. -/
def proveRegionWriteBound? (goalTy : Expr) : TacticM (Option Expr) := do
  let g0 ← getMainGoal
  let mvar ← g0.withContext (mkFreshExprMVar goalTy)
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  let ok ← tryTactic do
    evalTactic (← `(tactic| (
      try simp (config := { decide := true }) only [
        Arm64.InRegion, Arm64.sub_add_left_cancel, Arm64.sub_add_add_left_cancel,
        Arm64.sub_sub_left_cancel, Arm64.sub_sub_add_left_cancel,
        ProofLib.bitvec_add_neg_eq_sub, BitVec.sub_self,
        bitvec_sub16_add8, bitvec_sub8_add8, bitvec_sub16_sub16, bitvec_sub16_sub8,
        bitvec_sub32_add8, bitvec_sub32_add16, bitvec_sub32_add24,
        arm64_norm])))
    let gs ← getGoals
    match gs with
    | [] => pure ()
    | [g] =>
      let t ← g.withContext do instantiateMVars (← g.getType)
      if t.isConstOf ``False then throwError "false bound"
      -- `trivial` at reducible transparency: its `contradiction` step otherwise unifies
      -- hypothesis pairs at default transparency.
      evalTactic (← `(tactic| first | with_reducible trivial | decide | bv_omega_fast | omega | bv_omega))
      if !(← getGoals).isEmpty then throwError "unsolved bound"
    | _ => throwError "multiple goals"
  setGoals savedGoals
  if ok then
    return some (← g0.withContext (instantiateMVars mvar))
  else
    return none

/-- Try to extend `hag : AgreesOutside mStart mPrev base len` across one store `(wName, mNext, wAddr, wVal)`. -/
def stepAgreesOutsideWrite? (mStart mPrev base len hag : Expr)
    (wName : Name) (wAddr wVal : Expr) : TacticM (Option Expr) := do
  let g0 ← getMainGoal
  if wName == ``Arm64.Memory.write8 then
    let hbTy := mkApp3 (mkConst ``Arm64.InRegion) base len wAddr
    let some hbPrf ← proveRegionWriteBound? hbTy | return none
    return ← g0.withContext do
      observing? (mkAppOptM ``ProofLib.AgreesOutside.write8
        #[some mStart, some mPrev, some base, some len, some wAddr, some wVal, some hag, some hbPrf])
  let (wBytes, lemmaName) :=
    if wName == ``Arm64.Memory.write16 then (2, ``ProofLib.AgreesOutside.write16)
    else if wName == ``Arm64.Memory.write32 then (4, ``ProofLib.AgreesOutside.write32)
    else if wName == ``Arm64.Memory.write64 then (8, ``ProofLib.AgreesOutside.write64)
    else (16, ``ProofLib.AgreesOutside.write128)
  let (hbTy, hlenTy) ← g0.withContext do
    let diff ← mkAppM ``HSub.hSub #[wAddr, base]
    let diffNat ← mkAppM ``BitVec.toNat #[diff]
    let lhs ← mkAppM ``HAdd.hAdd #[diffNat, toExpr wBytes]
    let hbTy ← mkAppM ``LE.le #[lhs, len]
    let twoPow64 ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]
    let hlenTy ← mkAppM ``LE.le #[len, twoPow64]
    return (hbTy, hlenTy)
  let some hbPrf ← proveRegionWriteBound? hbTy | return none
  let some hlenPrf ← proveRegionWriteBound? hlenTy | return none
  g0.withContext do
    observing? (mkAppOptM lemmaName
      #[some mStart, some mPrev, some base, some len, some wAddr, some wVal, some hag, some hbPrf, some hlenPrf])

/-- Discharge a separation-logic side condition `φ` (a value equality from cancellation, or a
    content predicate such as `m.read64 a = v`) using definitional equality, `arm64_norm`,
    `bv_fallback` (kernel-only), or `bv_omega`. -/
def proveSepSide? (φ : Expr) : TacticM (Option Expr) := do
  let g0 ← getMainGoal
  g0.withContext do
    let φ ← instantiateMVars φ
    if let some (_, lhs, rhs) := φ.eq? then
      if ← withReducible (isDefEq lhs rhs) then return some (← mkEqRefl lhs)
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ← withReducible (isDefEq ty φ) then
          return some decl.toExpr
    let mvar ← mkFreshExprMVar φ
    let savedGoals ← getGoals
    setGoals [mvar.mvarId!]
    let t0 ← IO.monoMsNow
    let ok ← tryTacticQuiet do
      let _ ← tryTacticQuiet <| do
        let _ ← tryTacticQuiet <| evalTactic (← `(tactic|
          simp (config := { decide := true }) only [wp_norm, arm64_norm, *]))
        -- `bv_omega` cannot use shifts by symbolic amounts (`x <<< k` becomes
        -- `x.toNat * 2 ^ k.toNat`) and takes seconds to fail on them: go to `bv_decide`.
        let symShift ← match ← getGoals with
          | [g] => g.withContext do
              Pure.pure (CondClassify.hasSymbolicShift (← instantiateMVars (← g.getType)))
          | _ => Pure.pure false
        if symShift then
          evalTactic (← `(tactic|
            first
              | done
              | with_reducible rfl
              | with_reducible assumption
              | (omega; done)
              | (try dsimp only [subsPState64, addsPState64, subsPState32, addsPState32, AddWithCarry64, AddWithCarry32, ConditionHolds, rev64, rev32_64, rev16_64];
                 first | (bv_fallback; done) | (split <;> (try split) <;> first | done | with_reducible rfl | (bv_fallback; done)))
              | (split <;> (try split) <;> first | done | with_reducible rfl | with_reducible assumption | (omega; done))))
        else
          evalTactic (← `(tactic|
            first
              | done
              | with_reducible rfl
              | with_reducible assumption
              | (bv_omega_fast; done)
              | (wp_bv_omega; done)
              | (omega; done)
              | (split <;> (try split) <;> first | done | with_reducible rfl | with_reducible assumption | (bv_omega_fast; done) | (wp_bv_omega; done) | (omega; done))
              | (try dsimp only [subsPState64, addsPState64, subsPState32, addsPState32, AddWithCarry64, AddWithCarry32, ConditionHolds, rev64, rev32_64, rev16_64];
                 first | (bv_fallback; done) | (split <;> (try split) <;> first | done | with_reducible rfl | (bv_fallback; done)))))
      if !(← getGoals).isEmpty then
        evalTactic (← `(tactic| (
          try dsimp only [subsPState64, addsPState64, subsPState32, addsPState32, AddWithCarry64, AddWithCarry32, ConditionHolds, rev64, rev32_64, rev16_64] at *
          try simp (config := { decide := true }) only [wp_norm, arm64_norm, *] at *
          first
            | done
            | with_reducible rfl
            | with_reducible assumption
            | (bv_fallback; done)
            | (bv_omega; done)
            | (omega; done)
            | assumption
            | rfl
            | (split <;> (try split) <;> first | done | with_reducible rfl | with_reducible assumption | (bv_fallback; done) | (bv_omega; done) | (omega; done) | assumption | rfl))))
      if !(← getGoals).isEmpty then throwError "unsolved side condition"
    setGoals savedGoals
    CondClassify.reportTiming `sepSide ok ((← IO.monoMsNow) - t0) φ
    if ok then return some (← instantiateMVars mvar) else return none

private partial def flattenSepConjDiag (e : Expr) (fuel : Nat := 128) : List Expr :=
  if fuel == 0 then [e]
  else
    let e' := e.consumeMData
    if e'.isAppOfArity ``SepProp.sepConj 2 then
      flattenSepConjDiag (e'.getArg! 0) (fuel - 1) ++ flattenSepConjDiag (e'.getArg! 1) (fuel - 1)
    else if e'.isConstOf ``SepProp.emp then
      []
    else
      [e]

private def eraseFirstExprDiag (x : Expr) : List Expr → Option (List Expr)
  | [] => none
  | y :: ys =>
    if x == y then some ys
    else (eraseFirstExprDiag x ys).map (y :: ·)

private def diffSepConjDiag (targetFull curFull : Expr) : MessageData :=
  let targetAtoms := flattenSepConjDiag targetFull
  let curAtoms := flattenSepConjDiag curFull
  let (unmatchedTarget, unmatchedCur) :=
    targetAtoms.foldl (init := (([] : List Expr), curAtoms)) fun (unmatchedT, remC) t =>
      match eraseFirstExprDiag t remC with
      | some remC' => (unmatchedT, remC')
      | none => (unmatchedT ++ [t], remC)
  let fmtList (xs : List Expr) : MessageData :=
    if xs.isEmpty then m!"(none)"
    else MessageData.joinSep (xs.map toMessageData) m!", "
  m!"\n  unmatched in target:  {fmtList unmatchedTarget}\n  unmatched in context: {fmtList unmatchedCur}"

/-- Close a separation-logic postcondition goal `m_goal ⊨ TargetFull`:
    1. Peel the `Memory.write*` stores off `m_goal` back to a hypothesis `m_init ⊨ InitFull` and
       step them forward (`SepSolver.stepWrite?`: exact-width stores update the owning block,
       other stores are batched into an `AgreesOutside` update of the enclosing block).
    2. Prove `TargetFull` from the resulting assertion with the generic entailment solver
       (`SepSolver.entail?`), discharging value side conditions with `proveSepSide?`. -/
elab "arm64_sep_close" : tactic => do
  let mvarId0 ← getMainGoal
  let goalTy0 ← mvarId0.withContext do instantiateMVars (← mvarId0.getType)
  if !goalTy0.isAppOfArity ``SepProp.Satisfies 2 then
    let hint := match goalTy0.consumeMData.getAppFn.constName? with
      | some (.str _ "Entails") =>
        m!"\nhint: goal is an entailment (`P ⊢ Q`); use `sep_entail` instead of `arm64_sep_close`"
      | some (.str _ "SepWP") | some (.str _ "SepWPp") =>
        m!"\nhint: goal is a `SepWP` weakest precondition; use `wp_done` (at target PC) or `wp_steps` instead of `arm64_sep_close`"
      | _ =>
        m!"\nhint: `arm64_sep_close` requires a goal of shape `m ⊨ P` (`SepProp.Satisfies P m`); use `sep_entail` for `P ⊢ Q` or `wp_done` for `SepWP`"
    throwError "arm64_sep_close: goal is not SepProp.Satisfies\n  actual goal:{indentExpr goalTy0}{hint}"
  let targetFull := goalTy0.getArg! 0
  let mGoal := goalTy0.getArg! 1
  if targetFull.isConstOf ``SepProp.emp then
    evalTactic (← `(tactic| exact Arm64.satisfies_emp _))
    return
  let (writes, mInit) := SepSolver.peelWrites mGoal
  mvarId0.withContext do
    let mut found : Option (Expr × Expr × Expr × Nat) := none
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          let fullHyp := ty.getArg! 0
          let mHyp := ty.getArg! 1
          if ← withReducible (isDefEq mHyp mGoal) then
            found := some (decl.toExpr, mGoal, fullHyp, writes.size)
            break
          else if ← withReducible (isDefEq mHyp mInit) then
            found := some (decl.toExpr, mInit, fullHyp, 0)
    if found.isNone then
      if let some (h, P) ← SepSolver.findSatHyp? mInit then
        found := some (h, mInit, P, 0)
    let some (initPrf, initMem, initFull, start) := found
      | throwError "arm64_sep_close: no matching `m ⊨ ...` hypothesis found in context"
    let mut curPrf := initPrf
    let mut curMem := initMem
    let mut curFull := initFull
    let mut i := start
    while i < writes.size do
      let some (n, mem', P', prf) ←
          SepSolver.stepWrite? stepAgreesOutsideWrite? curMem curFull curPrf writes i
        | throwError "arm64_sep_close: failed to step write at {writes[i]!.2.2.1} in {curFull}"
      curPrf := prf
      curMem := mem'
      curFull := P'
      i := i + n
    let some prf ← SepSolver.entail? proveSepSide? mGoal curFull curPrf targetFull
      | throwError "arm64_sep_close: cannot prove{diffSepConjDiag targetFull curFull}\ntarget:{indentExpr targetFull}\nfrom{indentExpr curFull}\nhint: prove unmatched value/address equalities or instantiate existentials before calling `arm64_sep_close`, or use `sep_entail`"
    mvarId0.assign prf
  replaceMainGoal []

/-- Instantiate one existential quantifier in the goal whose body mentions `SepProp.Satisfies`,
    or fail if the main goal is not such an existential (so `repeat'` terminates). -/
elab "arm64_instantiate_sep_exists" : tactic => do
  let g ← getMainGoal
  let nextGoal ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    if !(ty.isAppOfArity ``Exists 2 && (ty.find? (·.isConstOf ``SepProp.Satisfies)).isSome) then
      throwError "arm64_instantiate_sep_exists: not an existential containing SepProp.Satisfies"
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let wMVar ← mkFreshExprMVar α
    let bodyTy := p.beta #[wMVar]
    let hMVar ← mkFreshExprMVar bodyTy (kind := .syntheticOpaque)
    let prf ← mkAppOptM ``Exists.intro #[some α, some p, some wMVar, some hMVar]
    g.assign prf
    return hMVar.mvarId!
  replaceMainGoal [nextGoal]

def arm64CanonIteImpl : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    if (ty.find? fun e => e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5).isNone then return
    let ty' ← Meta.transform ty (post := fun e => do
      if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
        let c := e.getArg! 1
        let inst := e.getArg! 2
        let instTy ← instantiateMVars (← inferType inst)
        if instTy.isAppOfArity ``Decidable 1 && instTy.getArg! 0 == c then
          return .done e
        if let some inst' ← (try some <$> synthInstance (mkApp (mkConst ``Decidable) c)
            catch _ => pure none) then
          if ← withDefault (isDefEq inst inst') then
            let args := e.getAppArgs
            return .done (mkAppN e.getAppFn (args.set! 2 inst'))
      return .done e)
    if ty' != ty then
      replaceMainGoal [← g.replaceTargetDefEq ty']

elab "arm64_canon_ite_internal" : tactic => arm64CanonIteImpl

/-- Discharge BitVec, arithmetic, and separation-logic verification conditions after symbolic execution. -/
macro "arm64_bv" : tactic =>
  `(tactic| (
    try dsimp only [Arm64.CallingConventionPreserved, Arm64.CalleeSavedPreserved, Arm64.SubroutinePost] at *
    try simp (config := { decide := true }) only [arm64_norm, *] at *
    try dsimp only [subsPState64, addsPState64, subsPState32, addsPState32, AddWithCarry64, AddWithCarry32, ConditionHolds, rev64, rev32_64, rev16_64] at *
    repeat' (first | apply And.intro | arm64_instantiate_sep_exists)
    all_goals try arm64_canon_ite_internal
    try all_goals (try arm64_sep_close)
    -- Default-transparency `assumption` comes after the decision procedures: on unreachable
    -- paths it would otherwise try to unify e.g. `s0.mem.zeroFill a 65536 ⊨ R` with
    -- `hpre : s0.mem ⊨ R`, unfolding `zeroFill` tens of thousands of times before failing.
    -- `trivial` is likewise run at reducible transparency: its `contradiction` step otherwise
    -- unifies hypothesis pairs at default transparency.
    all_goals (
      first
        | done
        | (arm64_sep_close; done)
        | with_reducible assumption
        | (arm64_stack_preserved_internal; done)
        | (bv_fallback; done)
        | (bv_omega; done)
        | (omega; done)
        | assumption
        | with_reducible trivial
        | rfl
        | (split <;> first | done | (arm64_sep_close; done) | with_reducible assumption | (arm64_stack_preserved_internal; done) | (bv_fallback; done) | (bv_omega; done) | (omega; done) | assumption | with_reducible trivial | rfl)
    )
  ))

/-- Close a `reaches_pc` goal that has reached its target PC by reflexivity and `arm64_norm`
    (discharging the PC and `.Running` goals, and closing the postcondition if `arm64_norm` solves it). -/
macro "arm64_refl" : tactic =>
  `(tactic| (
    apply reaches_pc_refl
    · simp (config := { decide := true }) only [arm64_norm, *]
    · simp (config := { decide := true }) only [arm64_norm, *]
    try (simp (config := { decide := true }) only [arm64_norm, *]; done)))

/-- Replace reduced `BitVec.ofFin (Fin.mk val isLt)` and raw `Nat` constructors with clean `BitVec.ofNat` / `OfNat.ofNat` numerals,
    and canonicalize negative 64-bit offsets (`val >= 2^63` with `2^64 - val <= 2^32`) as `-(negMag#64)` so `bitvec_add_neg_eq_sub` applies. -/
partial def cleanReducedExpr (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  if ty.isAppOfArity ``BitVec 1 then
    if let some (w, v) ← evalBitVecLit? e then
      if w == 64 && v >= (1 <<< 63) && ((1 <<< 64) - v) <= (1 <<< 32) then
        let negMag := (1 <<< 64) - v
        return ← mkAppM ``Neg.neg #[mkCanonBitVecLit 64 negMag]
      else
        return mkCanonBitVecLit w v
    let eWhnf ← whnf e
    if eWhnf.isAppOfArity ``BitVec.ofFin 2 then
      let finExpr ← whnf (eWhnf.getArg! 1)
      if finExpr.isAppOfArity ``Fin.mk 3 then
        if let some v ← getNatValue? (finExpr.getArg! 1) then
          if let some w ← evalNatLit? (ty.getArg! 0) then
            if w == 64 && v >= (1 <<< 63) && ((1 <<< 64) - v) <= (1 <<< 32) then
              let negMag := (1 <<< 64) - v
              return ← mkAppM ``Neg.neg #[mkCanonBitVecLit 64 negMag]
            return mkCanonBitVecLit w v
          return mkApp2 (mkConst ``BitVec.ofNat) (ty.getArg! 0) (toExpr v)
  if ty.isConstOf ``Nat then
    if let some n ← getNatValue? e then
      return ← mkNumeral ty n
  match e with
  | .app f a => return mkApp (← cleanReducedExpr f) (← cleanReducedExpr a)
  | _ => return e

/-- Core implementation of `reduceBitVecAddAssoc`: fold `(base + c1) + c2` into `base + (c1 + c2)`
    when `c1` and `c2` are ground `BitVec` literals, so symbolic `base + offset` PCs and addresses
    normalize cleanly across steps and backward branches before generic `ofNat` rules can fire. -/
def reduceBitVecAddAssocCore (e : Expr) : SimpM Simp.Step := do
  if e.getAppNumArgs != 6 then return .continue
  let lhs := e.getArg! 4
  let c2 := e.getArg! 5
  if !lhs.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let baseExpr := lhs.getArg! 4
  let c1 := lhs.getArg! 5
  if c1.isAppOfArity ``Neg.neg 3 || c2.isAppOfArity ``Neg.neg 3 then return .continue
  if let some (w1, v1) ← evalBitVecLit? c1 then
    if let some (w2, v2) ← evalBitVecLit? c2 then
      if w1 == w2 && !(w1 == 64 && (v1 >= (1 <<< 63) || v2 >= (1 <<< 63))) then
        if (← evalBitVecLit? baseExpr).isNone then
          let sumLit := mkCanonBitVecLit w1 (v1 + v2)
          let newExpr ← mkAppM ``HAdd.hAdd #[baseExpr, sumLit]
          let prf ← mkAppM ``BitVec.add_assoc #[baseExpr, c1, c2]
          return .visit { expr := newExpr, proof? := some prf }
  return .continue

simproc ↓ [arm64_norm, wp_norm] reduceBitVecAddAssoc ((_ + _) + _) := reduceBitVecAddAssocCore
simproc [arm64_norm, wp_norm] reduceBitVecAddAssocPost ((_ + _) + _) := reduceBitVecAddAssocCore

/-- Core implementation of `reduceBitVecAddSub`: fold `(base + c1) - c2` into `base + (c1 - c2)`
    when `c1` and `c2` are ground `BitVec` literals, so backward branches (rewritten by
    `bitvec_add_neg_eq_sub` to `(base + c1) - c2`) fold cleanly. -/
def reduceBitVecAddSubCore (e : Expr) : SimpM Simp.Step := do
  if e.getAppNumArgs != 6 then return .continue
  let lhs := e.getArg! 4
  let c2 := e.getArg! 5
  if !lhs.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let baseExpr := lhs.getArg! 4
  let c1 := lhs.getArg! 5
  if c1.isAppOfArity ``Neg.neg 3 || c2.isAppOfArity ``Neg.neg 3 then return .continue
  if let some (w1, v1) ← evalBitVecLit? c1 then
    if let some (w2, v2) ← evalBitVecLit? c2 then
      if w1 == 64 && w2 == 64 && v1 < (1 <<< 63) then
        if (← evalBitVecLit? baseExpr).isNone then
          let m := 1 <<< w1
          let diffLit := mkCanonBitVecLit w1 ((v1 + m - (v2 % m)) % m)
          let newExpr ← mkAppM ``HAdd.hAdd #[baseExpr, diffLit]
          let prf ← mkAppM ``Arm64.bitvec_add_sub_assoc #[baseExpr, c1, c2]
          return .visit { expr := newExpr, proof? := some prf }
  return .continue

simproc ↓ [arm64_norm, wp_norm] reduceBitVecAddSub ((_ + _) - _) := reduceBitVecAddSubCore
simproc [arm64_norm, wp_norm] reduceBitVecAddSubPost ((_ + _) - _) := reduceBitVecAddSubCore

/-- True if `ty` is an atomic predicate that should not be unfolded further when searching for
    `hasCode`, `Eq`, or `subroutine_ok` hypotheses. -/
def isAtomicCodeOrSpecPred (ty : Expr) : Bool :=
  ty.isAppOfArity ``Program.hasCode 3 ||
  ty.isAppOfArity ``Program.hasWords 3 ||
  ty.isAppOfArity ``Program.hasWordsOff 3 ||
  ty.isAppOfArity ``Program.codeAt 3 ||
  ty.isAppOfArity ``Eq 3 ||
  ty.isAppOf ``Arm64.subroutine_ok ||
  ty.isAppOf ``Arm64.exit_ok ||
  ty.isAppOf ``Arm64.code_ok ||
  ty.isAppOf ``Obj.Loads ||
  ty.isAppOf ``SepProp.Satisfies ||
  ty.isAppOf ``Arm64.DisjointRegions ||
  ty.isAppOf ``Arm64.InRegion ||
  ty.isAppOf ``Arm64.Memory.Disjoint64 ||
  ty.isAppOf ``Arm64.Memory.Disjoint128 ||
  ty.isAppOf ``Arm64.CalleeSavedPreserved ||
  ty.isAppOf ``Arm64.CallingConventionPreserved ||
  ty.isAppOf ``Arm64.StackPreserved ||
  ty.isAppOf ``Obj.AdrpInRange ||
  ty.isAppOf ``Obj.BranchInRange ||
  ty.isAppOf ``Obj.Lo12Aligned ||
  ty.isAppOf ``Obj.Imm19InRange ||
  ty.isAppOf ``Obj.TstBr14InRange ||
  ty.isAppOf ``Obj.AdrInRange ||
  ty.isAppOf ``Obj.Prel32InRange ||
  ty.isAppOf ``Obj.CodeRelocInRange ||
  ty.isAppOf ``LE.le ||
  ty.isAppOf ``LT.lt ||
  ty.isAppOf ``Ne ||
  ty.isAppOf ``Not

/-- Single definitional unfolding step for code and callee bundle predicates (`FnCode.holds`,
    `Program.hasCodeBundle`, `Program.codeAtOff`, `Program.codeAtAddr`, `Program.calleesOk`,
    `allHold`, and user-defined `CodeAt` wrappers) that preserves `prog.fnAddr name` and
    `Program.codeAt` intact. -/
def stepUnfoldCodePred? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  if isAtomicCodeOrSpecPred ty || ty.isAppOfArity ``And 2 then
    return none
  if ty.isAppOfArity ``Program.codeAtOff 4 then
    let prog := ty.getArg! 0
    let name := ty.getArg! 1
    let off := ty.getArg! 2
    let hex := ty.getArg! 3
    let fnOffExpr := mkApp2 (mkConst ``Program.fnOff) prog name
    let eqExpr ← mkEq fnOffExpr off
    let codeAtExpr := mkApp3 (mkConst ``Program.codeAt) prog name hex
    return some (mkApp2 (mkConst ``And) eqExpr codeAtExpr)
  if ty.isAppOfArity ``Program.codeAtAddr 4 then
    let prog := ty.getArg! 0
    let name := ty.getArg! 1
    let addr := ty.getArg! 2
    let hex := ty.getArg! 3
    let fnAddrExpr := mkApp2 (mkConst ``Program.fnAddr) prog name
    let eqExpr ← mkEq fnAddrExpr addr
    let codeAtExpr := mkApp3 (mkConst ``Program.codeAt) prog name hex
    return some (mkApp2 (mkConst ``And) eqExpr codeAtExpr)
  if ty.isAppOfArity ``FnCode.holds 2 then
    let spec ← whnf (ty.getArg! 0)
    let prog := ty.getArg! 1
    if spec.isAppOfArity ``FnCode.mk 3 then
      let fnName := spec.getArg! 0
      let hex := spec.getArg! 1
      let pin ← whnf (spec.getArg! 2)
      if pin.isConstOf ``FnPin.none then
        return some (mkApp3 (mkConst ``Program.codeAt) prog fnName hex)
      else if pin.isAppOfArity ``FnPin.off 1 then
        let off := pin.getArg! 0
        return some (mkApp4 (mkConst ``Program.codeAtOff) prog fnName off hex)
      else if pin.isAppOfArity ``FnPin.addr 1 then
        let addr := pin.getArg! 0
        return some (mkApp4 (mkConst ``Program.codeAtAddr) prog fnName addr hex)
  if ty.isAppOfArity ``Program.hasCodeBundle 2 then
    let prog := ty.getArg! 0
    let specs ← whnf (ty.getArg! 1)
    if specs.isAppOfArity ``List.nil 1 then
      return some (mkConst ``True)
    else if specs.isAppOfArity ``List.cons 3 then
      let s := specs.getArg! 1
      let rest ← whnf (specs.getArg! 2)
      let holdsExpr := mkApp2 (mkConst ``FnCode.holds) s prog
      if rest.isAppOfArity ``List.nil 1 then
        return some holdsExpr
      else if rest.isAppOfArity ``List.cons 3 then
        let restBundle := mkApp2 (mkConst ``Program.hasCodeBundle) prog rest
        return some (mkApp2 (mkConst ``And) holdsExpr restBundle)
  if ty.isAppOfArity ``Program.calleesOk 2 || ty.isAppOfArity ``allHold 1 then
    let tyWhnf ← whnf ty
    if tyWhnf != ty then
      return some tyWhnf
  if ← ty.getAppArgs.anyM (fun a => do pure ((← inferType a).isConstOf ``Program)) then
    return ← unfoldDefinition? ty
  return none

/-- Recursively collect `(proofExpr, typeExpr)` projections from `(hExpr, hTy)` by unfolding
    definitions (`hasCodeBundle`, `FnCode.holds`, `codeAtAddr`, `codeAt`, `calleesOk`, `allHold`,
    user `CodeAt` definitions) and traversing `And.left` / `And.right`. -/
partial def collectCodeProjections (hExpr : Expr) (hTy : Expr) (depth : Nat := 32) :
    MetaM (Array (Expr × Expr)) := do
  if depth == 0 then return #[]
  let hTy ← instantiateMVars hTy
  let mut acc : Array (Expr × Expr) := #[(hExpr, hTy)]
  if hTy.isAppOfArity ``And 2 then
    let p1 := hTy.getArg! 0
    let p2 := hTy.getArg! 1
    let e1 ← mkAppM ``And.left #[hExpr]
    let e2 ← mkAppM ``And.right #[hExpr]
    acc := acc ++ (← collectCodeProjections e1 p1 (depth - 1))
               ++ (← collectCodeProjections e2 p2 (depth - 1))
  else if hTy.isAppOfArity ``Program.codeAt 3 then
    let prog := hTy.getArg! 0
    let name := hTy.getArg! 1
    let hex := hTy.getArg! 2
    let fnAddrExpr := mkApp2 (mkConst ``Program.fnAddr) prog name
    let hcTy := mkApp3 (mkConst ``Program.hasCode) prog fnAddrExpr hex
    let hcPrf := mkApp4 (mkConst ``Program.hasCode_fnAddr_of_codeAt) prog name hex hExpr
    acc := acc.push (hcPrf, hcTy)
  else if let some hTy' ← stepUnfoldCodePred? hTy then
    acc := acc ++ (← collectCodeProjections hExpr hTy' (depth - 1))
  return acc

/-- Evaluate a ground `String` expression (supporting `.lit (.strVal _)`, `++` / `String.append`, and unfolding `def`s). -/
partial def evalStringLit? (e : Expr) : MetaM (Option String) := do
  let e ← instantiateMVars e
  if let .lit (.strVal s) := e then return some s
  if e.isAppOfArity ``HAppend.hAppend 6 then
    if let some s1 ← evalStringLit? (e.getArg! 4) then
      if let some s2 ← evalStringLit? (e.getArg! 5) then
        return some (s1 ++ s2)
  if e.isAppOfArity ``String.append 2 then
    if let some s1 ← evalStringLit? (e.getArg! 0) then
      if let some s2 ← evalStringLit? (e.getArg! 1) then
        return some (s1 ++ s2)
  if let some e' ← unfoldDefinition? e then
    return ← evalStringLit? e'
  let eWhnf ← whnf e
  if let .lit (.strVal s) := eWhnf then return some s
  if eWhnf != e then return ← evalStringLit? eWhnf
  return none

/-- Symbolic PC bases: `prog.fnAddr name`, `img.fnAddr name`, `s.sym obj name`, `img.base`,
    `prog.base`, a placement base `pl.base`, a free variable, or an application of a free variable
    `resolve name`. -/
def isPCBaseAtom (e : Expr) : Bool :=
  e.isAppOfArity ``Program.fnAddr 2 ||
  e.isAppOfArity `Arm64.Obj.Placement.base 1 ||
  e.isAppOfArity `Arm64.Obj.Image.fnAddr 2 ||
  e.isAppOfArity ``State.sym 3 ||
  e.isAppOfArity ``Obj.Image.base 1 ||
  e.isAppOfArity ``Program.base 1 ||
  e.isFVar ||
  (e.isApp && e.getAppFn.isFVar)

/-- Extract `(baseExpr, offsetNat)` from a PC expression `baseExpr + offset#64` or `baseExpr` (offset `0`). -/
partial def evalPCBaseOff? (e : Expr) : MetaM (Option (Expr × Nat)) := do
  let e ← instantiateMVars e
  if (← evalBitVecLit? e).isSome then
    return none
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let lhs := e.getArg! 4
    let rhs := e.getArg! 5
    if let some (64, off2) ← evalBitVecLit? rhs then
      if let some (base, off1) ← evalPCBaseOff? lhs then
        return some (base, (off1 + off2) % (1 <<< 64))
      if (← evalBitVecLit? lhs).isNone then
        return some (lhs, off2 % (1 <<< 64))
  if e.isAppOfArity ``HSub.hSub 6 then
    let lhs := e.getArg! 4
    let rhs := e.getArg! 5
    if let some (64, off2) ← evalBitVecLit? rhs then
      if let some (base, off1) ← evalPCBaseOff? lhs then
        return some (base, (off1 + (1 <<< 64) - (off2 % (1 <<< 64))) % (1 <<< 64))
  if isPCBaseAtom e then
    return some (e, 0)
  -- General path: any linear shape (`8#64 + base`, `base + x - x + 8#64`, ...) whose certified
  -- linear normal form is `1 * base + c` with `base` a PC base atom.
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 then
    if let some lf ← (ProofLib.BV.Lin.linearize e).run' then
      if let #[(base, 1)] := lf.terms then
        if isPCBaseAtom base then
          if let some 64 ← evalNatLit? lf.width then
            return some (base, lf.const.toNat)
  return none

/-- Cross-declaration cache of decoded 32-bit instruction words for constant code definitions.
    Keys are imported `.olean` `Name`s (`m_rc = 0`) and values are arrays of unboxed scalar
    `BitVec 32` words (`lean_is_scalar`), so storing entries never marks any `Expr` multi-threaded. -/
initialize hexConstWordsCacheRef : IO.Ref (Std.HashMap Name (Array (BitVec 32))) ← IO.mkRef {}

/-- Cross-declaration cache mapping an instruction word to its decoded `(instExpr, some instExpr)`
    pair. Entries are small ground terms shared across declarations; `lean_mark_mt` on insertion
    only visits the newly inserted subgraph. -/
initialize decodedWordExprCacheRef : IO.Ref (Std.HashMap (BitVec 32) (Expr × Expr)) ← IO.mkRef {}

/-- Extract an `Array (BitVec 32)` from a `List (BitVec 32)` expression `e` in `MetaM`. -/
partial def evalWordListExpr? (e : Expr) : MetaM (Option (Array (BitVec 32))) := do
  let mut cur := e
  let mut acc : Array (BitVec 32) := #[]
  while true do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then
      return some acc
    else if c.isAppOfArity ``List.cons 3 then
      let hd := c.getArg! 1
      let tl := c.getArg! 2
      let some (32, v) ← evalBitVecLit? hd | return none
      acc := acc.push (BitVec.ofNat 32 v)
      cur := tl
    else if c.isAppOfArity ``Arm64.Program.parseHexWords 1 then
      if let some s ← evalStringLit? (c.getArg! 0) then
        return some (acc ++ (Arm64.Program.parseHexWords s).toArray)
      return none
    else
      let c' ← whnf c
      if c' == c then
        return none
      cur := c'
  return none

structure HasCodeFetchCache where
  declName : Name
  codeFVarIds : Array FVarId
  hasCodeFacts : Array (Expr × Expr)
  rawProjs : Array (Expr × Expr) := #[]

structure VCGenDeclCache where
  hasCodeFetch? : Option HasCodeFetchCache := none
  hexExprWords : Std.HashMap Expr (Array (BitVec 32)) := {}

/-- Per-declaration `IO.Ref VCGenDeclCache` (`m_rc > 0`) stored in a `.local` environment
    extension so `lean_st_ref_set` takes the single-threaded fast path without calling
    `lean_mark_mt` on cached proof terms while mutations inside backtracking `saveState`/`restore`
    scopes survive rollback. -/
initialize vcgenDeclCacheRefExt : EnvExtension (Option (IO.Ref VCGenDeclCache)) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Obtain (or lazily allocate once for the current declaration) the per-declaration `IO.Ref`
    backing `HasCodeFetchCache` and local `hexExprWords`. -/
def getOrCreateVCGenDeclCacheRef : CoreM (IO.Ref VCGenDeclCache) := do
  if let some ref := vcgenDeclCacheRefExt.getState (← getEnv) then
    return ref
  let ref ← IO.mkRef {}
  modify fun s => { s with env := vcgenDeclCacheRefExt.setState s.env (some ref) }
  return ref

private def evalWordsCached? (hexExpr : Expr) (declCacheRef : IO.Ref VCGenDeclCache) :
    MetaM (Option (Array (BitVec 32))) := do
  if hexExpr.isConst then
    let cName := hexExpr.constName!
    if let some cachedWords := (← hexConstWordsCacheRef.get).get? cName then
      return some cachedWords
    if let some wArr ← evalWordListExpr? hexExpr then
      hexConstWordsCacheRef.modify (·.insert cName wArr)
      return some wArr
    return none
  if let some cachedWords := (← declCacheRef.get).hexExprWords.get? hexExpr then
    return some cachedWords
  if let some wArr ← evalWordListExpr? hexExpr then
    declCacheRef.modify fun c => { c with hexExprWords := c.hexExprWords.insert hexExpr wArr }
    return some wArr
  return none

private def decodeWordCached? (w : BitVec 32) : MetaM (Option (Expr × Expr)) := do
  if let some pair := (← decodedWordExprCacheRef.get).get? w then
    return some pair
  if let some inst := Arm64.decode w then
    let instExpr ← cleanReducedExpr (toExpr inst)
    let someInstExpr ← mkAppM ``Option.some #[instExpr]
    let pair := (instExpr, someInstExpr)
    decodedWordExprCacheRef.modify (·.insert w pair)
    return some pair
  return none

private def buildPcOffsetProof? (pcExpr baseExpr : Expr) (i : Nat)
    (rebaseBaseOffOpt : Option (Expr × Expr)) : MetaM (Option (Expr × Expr)) := do
  let offExpr := toExpr (BitVec.ofNat 64 (4 * i))
  let basePlusOff ← mkAppM ``HAdd.hAdd #[baseExpr, offExpr]
  let hPcProof? : Option Expr ← do
    if pcExpr == basePlusOff then
      some <$> mkEqRefl pcExpr
    else if i == 0 && (pcExpr == baseExpr || (← withReducible (isDefEq pcExpr baseExpr))) then
      let addZero ← mkAppM ``BitVec.add_zero #[baseExpr]
      some <$> mkEqSymm addZero
    else if let some (bBase, bOffLit) := rebaseBaseOffOpt then
      let assocPrf ← mkAppM ``BitVec.add_assoc #[bBase, bOffLit, offExpr]
      let symmPrf ← mkEqSymm assocPrf
      let eqTy ← mkEq pcExpr basePlusOff
      some <$> mkExpectedTypeHint symmPrf eqTy
    else if pcExpr.isAppOfArity ``HAdd.hAdd 6 && (pcExpr.getArg! 4).isAppOfArity ``HAdd.hAdd 6 then
      let lhs1 := pcExpr.getArg! 4
      let c1 := lhs1.getArg! 5
      let c2 := pcExpr.getArg! 5
      let assocPrf ← mkAppM ``BitVec.add_assoc #[baseExpr, c1, c2]
      let eqTy ← mkEq pcExpr basePlusOff
      some <$> mkExpectedTypeHint assocPrf eqTy
    else if ← isDefEq pcExpr basePlusOff then
      some <$> mkEqRefl pcExpr
    else
      pure none
  return hPcProof?.map (fun prf => (basePlusOff, prf))

private partial def replaceRelocImmInInstr (e : Expr) (newBvExpr : Expr) : Expr :=
  if e.isAppOfArity ``Instr.addSubImm 6 then
    let imm12Expr := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (12 : Nat)) newBvExpr
    mkApp6 (mkConst ``Instr.addSubImm)
      (e.getArg! 0) (e.getArg! 1) (e.getArg! 2) (e.getArg! 3) imm12Expr (e.getArg! 5)
  else if e.isAppOfArity ``AddrMode.Offset 2 then
    mkApp2 (mkConst ``AddrMode.Offset) (e.getArg! 0) newBvExpr
  else
    match e with
    | .app f a =>
      if a.isAppOfArity ``AddrMode.Offset 2 then
        mkApp f (mkApp2 (mkConst ``AddrMode.Offset) (a.getArg! 0) newBvExpr)
      else
        mkApp f newBvExpr
    | _ => e

private partial def evalIntLit? (e : Expr) : MetaM (Option Int) := do
  let e := e.consumeMData
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some k ← evalNatLit? (e.getArg! 1) then
      return some (Int.ofNat k)
  if e.isAppOfArity ``Int.ofNat 1 then
    if let some k ← evalNatLit? (e.getArg! 0) then
      return some (Int.ofNat k)
  if e.isAppOfArity ``Neg.neg 3 then
    if let some v ← evalIntLit? (e.getArg! 2) then
      return some (-v)
  if e.isAppOfArity ``Int.negOfNat 1 then
    if let some k ← evalNatLit? (e.getArg! 0) then
      return some (Int.negOfNat k)
  if e.isAppOfArity ``Int.negSucc 1 then
    if let some k ← evalNatLit? (e.getArg! 0) then
      return some (Int.negSucc k)
  return none

private partial def evalListElemAt? (e : Expr) (idx : Nat) : MetaM (Option Expr) := do
  let mut cur := e
  let mut k := idx
  while true do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then
      return none
    else if c.isAppOfArity ``List.cons 3 then
      if k == 0 then
        return some (c.getArg! 1)
      k := k - 1
      cur := c.getArg! 2
    else if let some c' ← unfoldDefinition? c then
      cur := c'
    else
      let c' ← whnf c
      if c' == c then
        return none
      cur := c'
  return none

private partial def unfoldRelocEntry? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let c := e.consumeMData
  if c.isAppOf ``Obj.RelocEntry.mk && c.getAppNumArgs >= 4 then
    return some (c.getArg! 0, c.getArg! 1, c.getArg! 2, c.getArg! 3)
  if let some c' ← unfoldDefinition? c then
    return ← unfoldRelocEntry? c'
  let c' ← whnf c
  if c'.isAppOf ``Obj.RelocEntry.mk && c'.getAppNumArgs >= 4 then
    return some (c'.getArg! 0, c'.getArg! 1, c'.getArg! 2, c'.getArg! 3)
  return none

private partial def findRelocEntryAtOff? (relocsExpr : Expr) (targetOff : Nat) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let mut cur := relocsExpr
  while true do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then
      return none
    else if c.isAppOfArity ``List.cons 3 then
      let hd := c.getArg! 1
      if let some (offE, kindE, symE, addendE) ← unfoldRelocEntry? hd then
        if (← evalNatLit? offE) == some targetOff then
          return some (hd, kindE, symE, addendE)
      cur := c.getArg! 2
    else if let some c' ← unfoldDefinition? c then
      cur := c'
    else
      let c' ← whnf c
      if c' == c then
        return none
      cur := c'
  return none

private partial def findCallEntryAtOff? (callsExpr : Expr) (targetOff : Nat) :
    MetaM (Option (Expr × Expr)) := do
  let mut cur := callsExpr
  while true do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then
      return none
    else if c.isAppOfArity ``List.cons 3 then
      let hd := c.getArg! 1
      let hdW ← if hd.isAppOfArity ``Prod.mk 4 then pure hd else whnf hd
      if hdW.isAppOfArity ``Prod.mk 4 then
        if (← evalNatLit? (hdW.getArg! 2)) == some targetOff then
          return some (hd, hdW.getArg! 3)
      cur := c.getArg! 2
    else if let some c' ← unfoldDefinition? c then
      cur := c'
    else
      let c' ← whnf c
      if c' == c then
        return none
      cur := c'
  return none

private def evalRelocTargetExpr (resolveExpr symExpr addendExpr : Expr) : MetaM Expr := do
  let symAddrExpr := mkApp resolveExpr symExpr
  match ← evalIntLit? addendExpr with
  | some 0 => return symAddrExpr
  | some (Int.ofNat k) => mkAppM ``HAdd.hAdd #[symAddrExpr, toExpr (BitVec.ofNat 64 k)]
  | _ => return mkApp2 (mkConst ``Obj.addSignedAddr) symAddrExpr addendExpr

private def findRangeOrAlignProof? (goalProp : Expr) (rawProjs : Array (Expr × Expr))
    (patchCtx? : Option (Bool × Expr × Expr × Expr × Expr × Nat))
    (hPOpt : Option (Expr × Expr × Expr)) : MetaM (Option Expr) := do
  if goalProp.isAppOfArity ``Obj.Lo12Aligned 2 then
    if (← evalNatLit? (goalProp.getArg! 0)) == some 0 then
      return some (mkApp (mkConst ``Obj.lo12Aligned_zero) (goalProp.getArg! 1))
  if let some (isPatchCalls, listExpr, aExpr, resolveExpr, rExpr, offNat) := patchCtx? then
    let someRExpr ← mkAppM ``Option.some #[rExpr]
    let hFindRefl ← mkEqRefl someRExpr
    let thmName := if isPatchCalls then ``Obj.BranchInRange.of_find?_eq_some
                   else ``Obj.CodeRelocInRange.of_find?_eq_some
    -- The `hrange` premise of `thmName` instantiated at this site's list, base, and resolver.
    -- `inferType` does not check argument types, so each candidate hypothesis must be checked
    -- against it explicitly: otherwise the first `∀`-hypothesis whose conclusion fits is taken,
    -- and the kernel later rejects the proof term.
    let premise? ← observing? (do
      let .forallE _ dom _ _ ← whnf (← inferType
          (mkAppN (mkConst thmName) #[listExpr, aExpr, resolveExpr])) | throwError "no premise"
      return dom)
    for (prf, pTy) in rawProjs do
      if pTy.consumeMData.isForall && (← isProp pTy) then
        let cand := mkAppN (mkConst thmName)
          #[listExpr, aExpr, resolveExpr, prf, toExpr offNat, rExpr, hFindRefl]
        if let some candPrf ← observing? (do
            let some premise := premise? | throwError "no premise"
            unless ← isDefEq pTy premise do throwError "premise mismatch"
            let candTy ← inferType cand
            if ← isDefEq candTy goalProp then
              mkExpectedTypeHint cand goalProp
            else
              throwError "mismatch") then
          return some candPrf
  let fnHead := goalProp.getAppFn
  for (prf, pTy) in rawProjs do
    if pTy.getAppFn == fnHead then
      if ← isDefEq pTy goalProp then
        return some (← mkExpectedTypeHint prf goalProp)
      if let some (PExpr, pcExpr, hPProof) := hPOpt then
        if PExpr != pcExpr && goalProp.getAppNumArgs == 2 then
          let altProp := mkApp2 fnHead pcExpr (goalProp.getArg! 1)
          if ← isDefEq pTy altProp then
            let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
            let motive ← withLocalDeclD `_p bv64Ty fun p =>
              mkLambdaFVars #[p] (mkApp2 fnHead p (goalProp.getArg! 1))
            let symmP ← mkEqSymm hPProof
            let prf' ← mkEqNDRec motive prf symmP
            return some (← mkExpectedTypeHint prf' goalProp)
  return none

private partial def unfoldToPatchOrCons (e : Expr) : MetaM Expr := do
  let c := e.consumeMData
  if c.isAppOfArity ``List.cons 3 || c.isAppOfArity ``List.nil 1 ||
     c.isAppOfArity ``Obj.patchRelocs 4 || c.isAppOfArity ``Obj.patchCalls 4 then
    return c
  if let some c' ← unfoldDefinition? c then
    return ← unfoldToPatchOrCons c'
  return c

/-- Fetch a concrete (unrelocated) instruction word `w` at index `i` of `words` by decoupling
    `words[i]? = some w` from `decode w = some inst` (avoiding kernel reduction of `decode` over
    open `patchRelocs` / `patchCalls` lists). -/
theorem Program.fetch_of_hasWords_getElem_decode {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) (w : BitVec 32) {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (hget : words[i]? = some w)
    (hdec : decode w = some inst) :
    prog.fetch pc = some inst := by
  have ⟨hi, hwi⟩ := List.getElem?_eq_some_iff.1 hget
  rw [h_pc, Program.fetch_of_hasWords h i hi, hwi, hdec]

private def closeConcreteWordAt? (progExpr baseExpr pcExpr hexExpr rhs hPrf : Expr)
    (i : Nat) (w : BitVec 32) (rebaseBaseOffOpt : Option (Expr × Expr)) : MetaM (Option Expr) := do
  let some (instExpr, someInstExpr) ← decodeWordCached? w | return none
  if !(← isDefEq rhs someInstExpr) then return none
  let some (_, hPcProof) ← buildPcOffsetProof? pcExpr baseExpr i rebaseBaseOffOpt | return none
  let wLitExpr := toExpr w
  let someWExpr ← mkAppM ``Option.some #[wLitExpr]
  let hGetProof ← mkEqRefl someWExpr
  let hDecProof ← mkEqRefl someInstExpr
  let hWordsExpr := mkApp3 (mkConst ``Program.hasWords) progExpr baseExpr hexExpr
  let hHyp ← mkExpectedTypeHint hPrf hWordsExpr
  return some (mkAppN (mkConst ``Program.fetch_of_hasWords_getElem_decode)
    #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, instExpr, hHyp, hPcProof, hGetProof, hDecProof])

private def tryCloseRelocWordFetch (progExpr baseExpr pcExpr hexExpr rhs hPrf : Expr)
    (i : Nat) (rebaseBaseOffOpt : Option (Expr × Expr)) (rawProjs : Array (Expr × Expr))
    (declCacheRef : IO.Ref VCGenDeclCache) : MetaM (Option Expr) := do
  let hexUnf ← unfoldToPatchOrCons hexExpr
  let mut wExprOpt : Option (Expr × Bool × Option (Bool × Expr × Expr × Expr × Expr × Nat)) := none
  if hexUnf.isAppOfArity ``Obj.patchRelocs 4 then
    let relocsExpr := hexUnf.getArg! 0
    let tmplWordsExpr := hexUnf.getArg! 1
    let aExpr := hexUnf.getArg! 2
    let resolveExpr := hexUnf.getArg! 3
    let some tmplWords ← evalWordsCached? tmplWordsExpr declCacheRef | return none
    if h_lt : i < tmplWords.size then
      let w := tmplWords[i]
      match ← findRelocEntryAtOff? relocsExpr (4 * i) with
      | none =>
        return ← closeConcreteWordAt? progExpr baseExpr pcExpr hexExpr rhs hPrf i w rebaseBaseOffOpt
      | some (rExpr, kindExpr, symExpr, addendExpr) =>
        let kindWhnf ← whnf kindExpr
        let PExpr ← mkAppM ``HAdd.hAdd #[aExpr, toExpr (BitVec.ofNat 64 (4 * i))]
        let targetExpr ← evalRelocTargetExpr resolveExpr symExpr addendExpr
        let wLitExpr := toExpr w
        let pCtx := some (false, relocsExpr, aExpr, resolveExpr, rExpr, 4 * i)
        if kindWhnf.isConstOf ``Obj.RelocKind.adrpHi21 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.adrpWord) wLitExpr PExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.adrpHi21Nc then
          wExprOpt := some (mkApp3 (mkConst ``Obj.adrpWord) wLitExpr PExpr targetExpr, true, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.addLo12 || kindWhnf.isConstOf ``Obj.RelocKind.ldst8Lo12 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.lo12Word) (toExpr (0 : Nat)) wLitExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.ldst16Lo12 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.lo12Word) (toExpr (1 : Nat)) wLitExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.ldst32Lo12 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.lo12Word) (toExpr (2 : Nat)) wLitExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.ldst64Lo12 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.lo12Word) (toExpr (3 : Nat)) wLitExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.ldst128Lo12 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.lo12Word) (toExpr (4 : Nat)) wLitExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.call26 || kindWhnf.isConstOf ``Obj.RelocKind.jump26 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.branchWord) wLitExpr PExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.condbr19 || kindWhnf.isConstOf ``Obj.RelocKind.ldPrelLo19 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.imm19Word) wLitExpr PExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.tstbr14 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.tstbr14Word) wLitExpr PExpr targetExpr, false, pCtx)
        else if kindWhnf.isConstOf ``Obj.RelocKind.adrPrelLo21 then
          wExprOpt := some (mkApp3 (mkConst ``Obj.adrWord) wLitExpr PExpr targetExpr, false, pCtx)
  else if hexUnf.isAppOfArity ``Obj.patchCalls 4 then
    let callsExpr := hexUnf.getArg! 0
    let tmplWordsExpr := hexUnf.getArg! 1
    let aExpr := hexUnf.getArg! 2
    let resolveExpr := hexUnf.getArg! 3
    let some tmplWords ← evalWordsCached? tmplWordsExpr declCacheRef | return none
    if h_lt : i < tmplWords.size then
      let w := tmplWords[i]
      match ← findCallEntryAtOff? callsExpr (4 * i) with
      | none =>
        return ← closeConcreteWordAt? progExpr baseExpr pcExpr hexExpr rhs hPrf i w rebaseBaseOffOpt
      | some (rExpr, symExpr) =>
        let PExpr ← mkAppM ``HAdd.hAdd #[aExpr, toExpr (BitVec.ofNat 64 (4 * i))]
        let targetExpr := mkApp resolveExpr symExpr
        let pCtx := some (true, callsExpr, aExpr, resolveExpr, rExpr, 4 * i)
        wExprOpt := some (mkApp3 (mkConst ``Obj.branchWord) (toExpr w) PExpr targetExpr, false, pCtx)
  else
    let some wE ← evalListElemAt? hexUnf i | return none
    if let some (32, v) ← evalBitVecLit? wE then
      return ← closeConcreteWordAt? progExpr baseExpr pcExpr hexExpr rhs hPrf i (BitVec.ofNat 32 v) rebaseBaseOffOpt
    wExprOpt := some (wE.consumeMData, false, none)
  let some (wExpr, isNc, patchCtx?) := wExprOpt | return none
  let some (basePlusOff, hPcProof) ← buildPcOffsetProof? pcExpr baseExpr i rebaseBaseOffOpt | return none
  let hWordsExpr := mkApp3 (mkConst ``Program.hasWords) progExpr baseExpr hexExpr
  let hHyp ← mkExpectedTypeHint hPrf hWordsExpr
  let someWExpr ← mkAppM ``Option.some #[wExpr]
  let hGetProof ← mkEqRefl someWExpr
  let rflTrue ← mkEqRefl (toExpr true)
  let mkHP? (PExpr : Expr) : MetaM (Option Expr) := do
    if PExpr == pcExpr then some <$> mkEqRefl pcExpr
    else if PExpr == basePlusOff then some <$> mkEqSymm hPcProof
    else if ← isDefEq PExpr pcExpr then some <$> mkEqRefl pcExpr
    else if ← isDefEq PExpr basePlusOff then some <$> mkEqSymm hPcProof
    else pure none
  if wExpr.isAppOfArity ``Obj.adrpWord 3 then
    let wLitExpr := wExpr.getArg! 0
    let PExpr := wExpr.getArg! 1
    let targetExpr := wExpr.getArg! 2
    let some (32, wNat) ← evalBitVecLit? wLitExpr | return none
    let w := BitVec.ofNat 32 wNat
    if (w &&& 0x9f000000#32) != 0x90000000#32 then return none
    let some (tmplInstExpr, _) ← decodeWordCached? w | return none
    let some hPProof ← mkHP? PExpr | return none
    let rdExpr := toExpr (Reg.fromZRBits (w.extractLsb' 0 5))
    let pageDiffExpr ← mkAppM ``HSub.hSub #[mkApp (mkConst ``Obj.pageOf) targetExpr, mkApp (mkConst ``Obj.pageOf) pcExpr]
    if !isNc then
      let rangeGoal := mkApp2 (mkConst ``Obj.AdrpInRange) PExpr targetExpr
      if let some hrangePrf ← findRangeOrAlignProof? rangeGoal rawProjs patchCtx? (some (PExpr, pcExpr, hPProof)) then
        let instExpr := replaceRelocImmInInstr tmplInstExpr pageDiffExpr
        let someInstExpr ← mkAppM ``Option.some #[instExpr]
        if ← isDefEq rhs someInstExpr then
          return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_adrpAt)
            #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr, rdExpr,
              hHyp, hPcProof, hPProof, hGetProof, rflTrue, ← mkEqRefl rdExpr, hrangePrf])
    else
      let ext21 ← mkAppM ``BitVec.extractLsb' #[toExpr (12 : Nat), toExpr (21 : Nat), pageDiffExpr]
      let sext64 ← mkAppM ``BitVec.signExtend #[toExpr (64 : Nat), ext21]
      let ncDiffExpr ← mkAppM ``HShiftLeft.hShiftLeft #[sext64, toExpr (12 : Nat)]
      let ncInstExpr := replaceRelocImmInInstr tmplInstExpr ncDiffExpr
      let someNcInstExpr ← mkAppM ``Option.some #[ncInstExpr]
      if ← isDefEq rhs someNcInstExpr then
        return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_adrpNcAt)
          #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr, rdExpr,
            hHyp, hPcProof, hPProof, hGetProof, rflTrue, ← mkEqRefl rdExpr])
    return none
  if wExpr.isAppOfArity ``Obj.lo12Word 3 then
    let scaleExpr := wExpr.getArg! 0
    let wLitExpr := wExpr.getArg! 1
    let targetExpr := wExpr.getArg! 2
    let some scale ← evalNatLit? scaleExpr | return none
    let some (32, wNat) ← evalBitVecLit? wLitExpr | return none
    let w := BitVec.ofNat 32 wNat
    let some (tmplInstExpr, _) ← decodeWordCached? w | return none
    let lo12Expr := mkApp (mkConst ``Obj.lo12Of) targetExpr
    let instExpr := replaceRelocImmInInstr tmplInstExpr lo12Expr
    let someInstExpr ← mkAppM ``Option.some #[instExpr]
    if !(← isDefEq rhs someInstExpr) then return none
    if scale == 0 && (w &&& 0xffc00000#32) == 0x91000000#32 then
      let rdSpExpr := toExpr (Reg.fromSPBits (w.extractLsb' 0 5))
      let rnSpExpr := toExpr (Reg.fromSPBits (w.extractLsb' 5 5))
      return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_addLo12At)
        #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, targetExpr, rdSpExpr, rnSpExpr,
          hHyp, hPcProof, hGetProof, rflTrue, ← mkEqRefl rdSpExpr, ← mkEqRefl rnSpExpr])
    if (w &&& 0x3f000000#32) == 0x39000000#32 && (w &&& 0xffc00000#32) != 0xf9800000#32 &&
       (w.extractLsb' 30 2).toNat == scale then
      let alignGoal := mkApp2 (mkConst ``Obj.Lo12Aligned) scaleExpr targetExpr
      let some halPrf ← findRangeOrAlignProof? alignGoal rawProjs patchCtx? none | return none
      let rflFalse ← mkEqRefl (toExpr false)
      return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_ldstGprLo12At)
        #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, scaleExpr, wLitExpr, targetExpr, instExpr,
          hHyp, hPcProof, hGetProof, ← mkEqRefl scaleExpr, rflTrue, rflFalse, ← mkEqRefl someInstExpr, halPrf])
    if (w &&& 0x3f000000#32) == 0x3d000000#32 then
      let some (isLoad, sz, sc) := decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat | return none
      if sc != scale then return none
      let alignGoal := mkApp2 (mkConst ``Obj.Lo12Aligned) scaleExpr targetExpr
      let some halPrf ← findRangeOrAlignProof? alignGoal rawProjs patchCtx? none | return none
      let isLoadExpr := toExpr isLoad
      let szExpr := toExpr sz
      let tupleExpr ← mkAppM ``Prod.mk #[isLoadExpr, ← mkAppM ``Prod.mk #[szExpr, scaleExpr]]
      let someTupleExpr ← mkAppM ``Option.some #[tupleExpr]
      return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_ldstSimdLo12At)
        #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, scaleExpr, wLitExpr, targetExpr, isLoadExpr, szExpr, instExpr,
          hHyp, hPcProof, hGetProof, ← mkEqRefl someTupleExpr, rflTrue, ← mkEqRefl someInstExpr, halPrf])
    return none
  if wExpr.isAppOfArity ``Obj.branchWord 3 then
    let wLitExpr := wExpr.getArg! 0
    let PExpr := wExpr.getArg! 1
    let targetExpr := wExpr.getArg! 2
    let some (32, wNat) ← evalBitVecLit? wLitExpr | return none
    let w := BitVec.ofNat 32 wNat
    let isBl := (w &&& 0xfc000000#32) == 0x94000000#32
    let isB := (w &&& 0xfc000000#32) == 0x14000000#32
    if !isBl && !isB then return none
    let some (tmplInstExpr, _) ← decodeWordCached? w | return none
    let some hPProof ← mkHP? PExpr | return none
    let rangeGoal := mkApp2 (mkConst ``Obj.BranchInRange) PExpr targetExpr
    let some hrangePrf ← findRangeOrAlignProof? rangeGoal rawProjs patchCtx? (some (PExpr, pcExpr, hPProof)) | return none
    let dispExpr ← mkAppM ``HSub.hSub #[targetExpr, pcExpr]
    let instExpr := replaceRelocImmInInstr tmplInstExpr dispExpr
    let someInstExpr ← mkAppM ``Option.some #[instExpr]
    if !(← isDefEq rhs someInstExpr) then return none
    let thmName := if isBl then ``Obj.fetch_of_hasWords_blAt else ``Obj.fetch_of_hasWords_bAt
    return some (mkAppN (mkConst thmName)
      #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr,
        hHyp, hPcProof, hPProof, hGetProof, rflTrue, hrangePrf])
  if wExpr.isAppOfArity ``Obj.imm19Word 3 then
    let wLitExpr := wExpr.getArg! 0
    let PExpr := wExpr.getArg! 1
    let targetExpr := wExpr.getArg! 2
    let some (32, wNat) ← evalBitVecLit? wLitExpr | return none
    let w := BitVec.ofNat 32 wNat
    let some (tmplInstExpr, _) ← decodeWordCached? w | return none
    let some hPProof ← mkHP? PExpr | return none
    let rangeGoal := mkApp2 (mkConst ``Obj.Imm19InRange) PExpr targetExpr
    let some hrangePrf ← findRangeOrAlignProof? rangeGoal rawProjs patchCtx? (some (PExpr, pcExpr, hPProof)) | return none
    let dispExpr ← mkAppM ``HSub.hSub #[targetExpr, pcExpr]
    let instExpr := replaceRelocImmInInstr tmplInstExpr dispExpr
    let someInstExpr ← mkAppM ``Option.some #[instExpr]
    if !(← isDefEq rhs someInstExpr) then return none
    if (w &&& 0xff000010#32) == 0x54000000#32 then
      let ccExpr := toExpr (CondCode.ofBits (w.extractLsb' 0 4))
      return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_bcondAt)
        #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr, ccExpr,
          hHyp, hPcProof, hPProof, hGetProof, rflTrue, ← mkEqRefl ccExpr, hrangePrf])
    if (w &&& 0x7e000000#32) == 0x34000000#32 then
      return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_cbzAt)
        #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr, instExpr,
          hHyp, hPcProof, hPProof, hGetProof, rflTrue, ← mkEqRefl someInstExpr, hrangePrf])
    if (w &&& 0x3f000000#32) == 0x18000000#32 then
      return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_ldrLitAt)
        #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr, instExpr,
          hHyp, hPcProof, hPProof, hGetProof, rflTrue, ← mkEqRefl someInstExpr, hrangePrf])
    return none
  if wExpr.isAppOfArity ``Obj.tstbr14Word 3 then
    let wLitExpr := wExpr.getArg! 0
    let PExpr := wExpr.getArg! 1
    let targetExpr := wExpr.getArg! 2
    let some (32, wNat) ← evalBitVecLit? wLitExpr | return none
    let w := BitVec.ofNat 32 wNat
    if (w &&& 0x7e000000#32) != 0x36000000#32 then return none
    let some (tmplInstExpr, _) ← decodeWordCached? w | return none
    let some hPProof ← mkHP? PExpr | return none
    let rangeGoal := mkApp2 (mkConst ``Obj.TstBr14InRange) PExpr targetExpr
    let some hrangePrf ← findRangeOrAlignProof? rangeGoal rawProjs patchCtx? (some (PExpr, pcExpr, hPProof)) | return none
    let dispExpr ← mkAppM ``HSub.hSub #[targetExpr, pcExpr]
    let instExpr := replaceRelocImmInInstr tmplInstExpr dispExpr
    let someInstExpr ← mkAppM ``Option.some #[instExpr]
    if !(← isDefEq rhs someInstExpr) then return none
    return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_tstbr14At)
      #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr, instExpr,
        hHyp, hPcProof, hPProof, hGetProof, rflTrue, ← mkEqRefl someInstExpr, hrangePrf])
  if wExpr.isAppOfArity ``Obj.adrWord 3 then
    let wLitExpr := wExpr.getArg! 0
    let PExpr := wExpr.getArg! 1
    let targetExpr := wExpr.getArg! 2
    let some (32, wNat) ← evalBitVecLit? wLitExpr | return none
    let w := BitVec.ofNat 32 wNat
    if (w &&& 0x9f000000#32) != 0x10000000#32 then return none
    let some (tmplInstExpr, _) ← decodeWordCached? w | return none
    let some hPProof ← mkHP? PExpr | return none
    let rangeGoal := mkApp2 (mkConst ``Obj.AdrInRange) PExpr targetExpr
    let some hrangePrf ← findRangeOrAlignProof? rangeGoal rawProjs patchCtx? (some (PExpr, pcExpr, hPProof)) | return none
    let rdExpr := toExpr (Reg.fromZRBits (w.extractLsb' 0 5))
    let dispExpr ← mkAppM ``HSub.hSub #[targetExpr, pcExpr]
    let instExpr := replaceRelocImmInInstr tmplInstExpr dispExpr
    let someInstExpr ← mkAppM ``Option.some #[instExpr]
    if !(← isDefEq rhs someInstExpr) then return none
    return some (mkAppN (mkConst ``Obj.fetch_of_hasWords_adrAt)
      #[progExpr, baseExpr, pcExpr, hexExpr, toExpr i, wLitExpr, PExpr, targetExpr, rdExpr,
        hHyp, hPcProof, hPProof, hGetProof, rflTrue, ← mkEqRefl rdExpr, hrangePrf])
  return none

/-- True if a local declaration could plausibly contribute a `hasCode` or `fnAddr`/`fnOff` equality
    fact to `collectCodeProjections`. Excludes `Memory`/`State`/`BitVec` data variables, spatial
    `Satisfies` hypotheses, and register/flag/branch condition hypotheses so the cache remains
    valid across `STR`/`STP` (`intro m`) and `wp_if` (`intro hcond`). -/
private def mayContributeCodeProjection (decl : LocalDecl) : Bool :=
  if decl.isImplementationDetail || decl.isAuxDecl then false
  else
    let ty := decl.type.consumeMData
    if ty.isConstOf ``Arm64.Memory || ty.isConstOf ``Arm64.State || ty.isConstOf ``Arm64.SepProp ||
       ty.isAppOfArity ``BitVec 1 || ty.isAppOfArity ``SepProp.Satisfies 2 ||
       ty.isAppOf ``Arm64.DisjointRegions || ty.isAppOf ``Arm64.Memory.Disjoint64 ||
       ty.isAppOf ``Arm64.Memory.Disjoint128 || ty.isAppOf ``Arm64.CalleeSavedPreserved ||
       ty.isAppOfArity ``Not 1 || ty.isAppOfArity ``Ne 3 ||
       (ty.isForall && (ty.bindingBody!.isAppOfArity ``BitVec 1 || ty.bindingBody!.isAppOfArity ``Option 1)) then
      false
    else
      match ty.eq? with
      | some (eqTy, lhs, _) =>
        if eqTy.isConstOf ``Bool || eqTy.isConstOf ``ExecStatus ||
           lhs.isAppOf ``State.pc || lhs.isAppOf ``State.sp ||
           lhs.isAppOf ``State.readReg64 || lhs.isAppOf ``State.readReg32 ||
           lhs.isAppOf ``State.readReg || lhs.isAppOf ``State.status then
          false
        else
          true
      | none => true

/-- Close a fetch at `b + pcOff` on `P.rebase (b + bOff) X` from a rebase-fetch lemma at relative
    offset `k` (`bOff + k = pcOff`). -/
theorem Program.rebase_fetch_of_add_base {P : Program} {b bOff pcOff k : BitVec 64}
    {X : String → Option (Arm64.State → Arm64.State)} {inst : Instr}
    (hf : (P.rebase (b + bOff) X).fetch ((b + bOff) + k) = some inst)
    (heq : bOff + k = pcOff) :
    (P.rebase (b + bOff) X).fetch (b + pcOff) = some inst := by
  have h : (b + bOff) + k = b + pcOff := by rw [BitVec.add_assoc, heq]
  rw [← h]
  exact hf

register_option proofLib.fetchLocalHypIndex : Bool := {
  defValue := true
  descr := "let `tryCloseFetchFromHasCode` close `prog.fetch pc = some ?inst` from a local \
    `prog.fetch pc' = some inst` hypothesis whose program and `base + literal` PC shape match \
    structurally, before falling back to unifying against every hypothesis"
}

/-- Structural pre-filter key of a fetch PC: `(b, n)` for `b + n` with `n` a bit-vector literal,
    otherwise `(pc, 0)`. Two PCs with different keys may still be definitionally equal; the key
    is only used to pick candidates, each confirmed by unification. -/
def fetchPcKey (pc : Expr) : Expr × Nat :=
  let pc := pc.consumeMData
  if pc.isAppOfArity ``HAdd.hAdd 6 then
    match evalBitVecLitPure? (pc.getArg! 5) with
    | some (_, n) => (pc.getArg! 4, n)
    | none => (pc, 0)
  else
    (pc, 0)

/-- Close a fetch subgoal `prog.fetch pc = some ?inst` using a generated `<prog>_fetch_0x<off>` /
    `<C>_rebase_fetch_0x<off>` lemma or any `hasCode` / `codeAt` / `FnCode.holds` /
    `hasCodeBundle` hypothesis in the local context. For `prog = (C a₁ ... aₙ).rebase b X` (`C` a
    constant, possibly applied to parameters such as a placement), the rebase lemma is applied as
    `C_rebase_fetch_0x<off> a₁ ... aₙ b X`, so it must hold for all values of the parameters. Also
    supports shifted rebase bases `b = b₀ + bOff#64` with `pc = b₀ + pcOff#64` (`pcOff ≥ bOff`),
    resolving relative offset `pcOff - bOff` via `Program.rebase_fetch_of_add_base`. -/
def tryCloseFetchFromHasCode : TacticM Bool := do
  let gs ← getGoals
  let g :: rest := gs | return true
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq? | return false
    if !lhs.isAppOfArity ``Program.fetch 2 then return false
    let progExpr0 := lhs.getArg! 0
    let pcExpr := lhs.getArg! 1
    let pcLit? ← evalBitVecLit? pcExpr
    if progExpr0.isConst then
      if let some (64, pcVal) := pcLit? then
        let hexStr := String.ofList (Nat.toDigits 16 pcVal)
        let lemmaName := progExpr0.constName!.appendAfter s!"_fetch_0x{hexStr}"
        if let some info := (← getEnv).find? lemmaName then
          if let some (_, _, lemmaRhs) := info.type.eq? then
            if ← isDefEq rhs lemmaRhs then
              let prf ← mkExpectedTypeHint (mkConst lemmaName) ty
              g.assign prf
              setGoals rest
              return true
    let progExpr ← if progExpr0.isAppOfArity ``Program.rebase 4 then pure progExpr0
      else withReducible (whnf progExpr0)
    if progExpr.isAppOfArity ``Program.rebase 4 then
      let cExpr := progExpr.getArg! 0
      let bExpr := progExpr.getArg! 1
      let xExpr := progExpr.getArg! 2
      let oExpr := progExpr.getArg! 3
      -- The code is a constant `C` or a constant applied to parameters `C a₁ ... aₙ` (e.g. a code
      -- block patched under a placement); the lemma `C_rebase_fetch_0x<off>` then takes
      -- `a₁ ... aₙ b X` in that order.
      let cFn := cExpr.getAppFn
      if cFn.isConst && oExpr.isLambda && oExpr.bindingBody!.isAppOfArity ``Option.none 1 then
        if let some (pcBase, offVal) ← evalPCBaseOff? pcExpr then
          if ← withReducible (isDefEq pcBase bExpr) then
            let lemmaName? : Option Name :=
              if offVal == 0 && !(pcExpr.isAppOfArity ``HAdd.hAdd 6) then
                some (cFn.constName!.appendAfter "_rebase_fetch_base")
              else if pcExpr.isAppOfArity ``HAdd.hAdd 6 && pcExpr.getArg! 4 == bExpr then
                let hexStr := String.ofList (Nat.toDigits 16 offVal)
                some (cFn.constName!.appendAfter s!"_rebase_fetch_0x{hexStr}")
              else
                none
            if let some lemmaName := lemmaName? then
              -- Only use the lemma when its explicit binders are exactly `a₁ ... aₙ b X`.
              let arityOk := match (← getEnv).find? lemmaName with
                | some info => info.type.getForallBinderNames.length == cExpr.getAppNumArgs + 2
                | none => false
              if arityOk then
                let prfApp := mkApp2 (mkAppN (mkConst lemmaName) cExpr.getAppArgs) bExpr xExpr
                let prfTy ← inferType prfApp
                if let some (_, _, lemmaRhs) := prfTy.eq? then
                  if ← isDefEq rhs lemmaRhs then
                    let prf ← mkExpectedTypeHint prfApp ty
                    g.assign prf
                    setGoals rest
                    return true
          else if bExpr.isAppOfArity ``HAdd.hAdd 6 && pcExpr.isAppOfArity ``HAdd.hAdd 6 then
            if let some (bBase, bOff) ← evalPCBaseOff? bExpr then
              if bOff > 0 && offVal ≥ bOff && offVal < 2 ^ 64 &&
                  (← withReducible (isDefEq pcBase bBase)) &&
                  bExpr.getArg! 4 == bBase then
                let relOff := offVal - bOff
                if relOff == 0 then
                  let lemmaName := cFn.constName!.appendAfter "_rebase_fetch_base"
                  let arityOk := match (← getEnv).find? lemmaName with
                    | some info => info.type.getForallBinderNames.length == cExpr.getAppNumArgs + 2
                    | none => false
                  if arityOk then
                    let prfApp := mkApp2 (mkAppN (mkConst lemmaName) cExpr.getAppArgs) bExpr xExpr
                    let prfTy ← inferType prfApp
                    if let some (_, prfLhs, lemmaRhs) := prfTy.eq? then
                      if (← withReducible (isDefEq prfLhs lhs)) && (← isDefEq rhs lemmaRhs) then
                        let prf ← mkExpectedTypeHint prfApp ty
                        g.assign prf
                        setGoals rest
                        return true
                else
                  let hexStr := String.ofList (Nat.toDigits 16 relOff)
                  let lemmaName := cFn.constName!.appendAfter s!"_rebase_fetch_0x{hexStr}"
                  let arityOk := match (← getEnv).find? lemmaName with
                    | some info => info.type.getForallBinderNames.length == cExpr.getAppNumArgs + 2
                    | none => false
                  if arityOk then
                    let prf0 := mkApp2 (mkAppN (mkConst lemmaName) cExpr.getAppArgs) bExpr xExpr
                    let prf0Ty ← inferType prf0
                    if let some (_, prf0Lhs, lemmaRhs) := prf0Ty.eq? then
                      if ← isDefEq rhs lemmaRhs then
                        if ← withReducible (isDefEq prf0Lhs lhs) then
                          let prf ← mkExpectedTypeHint prf0 ty
                          g.assign prf
                          setGoals rest
                          return true
                        else if pcExpr.getArg! 4 == pcBase &&
                            lemmaRhs.isAppOfArity ``Option.some 2 &&
                            prf0Lhs.isAppOfArity ``Program.fetch 2 &&
                            (prf0Lhs.getArg! 1).isAppOfArity ``HAdd.hAdd 6 then
                          let bOffE := bExpr.getArg! 5
                          let pcOffE := pcExpr.getArg! 5
                          let kE := (prf0Lhs.getArg! 1).getArg! 5
                          let instE := lemmaRhs.getArg! 1
                          if let (some (64, bOffV), some (64, kV), some (64, pcOffV)) :=
                              (← evalBitVecLit? bOffE, ← evalBitVecLit? kE, ← evalBitVecLit? pcOffE) then
                            if (bOffV + kV) % (1 <<< 64) == pcOffV then
                              let sumE ← mkAppM ``HAdd.hAdd #[bOffE, kE]
                              if ← isDefEq sumE pcOffE then
                                let heq ← mkExpectedTypeHint (← mkEqRefl pcOffE) (← mkEq sumE pcOffE)
                                let prfApp := mkAppN (mkConst ``Program.rebase_fetch_of_add_base)
                                  #[cExpr, bBase, bOffE, pcOffE, kE, xExpr, instE, prf0, heq]
                                if ← withReducible (isDefEq (← inferType prfApp) ty) then
                                  let prf ← mkExpectedTypeHint prfApp ty
                                  g.assign prf
                                  setGoals rest
                                  return true
    -- Local `prog.fetch pc = some inst` hypotheses (e.g. instantiated `_rebase_fetch_0x<off>`
    -- lemmas, whose `have`-introduced types are still metavariables until instantiated): match the
    -- program and the `base + literal` shape of the PC structurally before the (reducible)
    -- unification, instead of unifying against every hypothesis.
    if proofLib.fetchLocalHypIndex.get (← getOptions) then
      let pcKey := fetchPcKey pcExpr
      let progKey := progExpr0.consumeMData
      for decl in ← getLCtx do
        if !decl.isImplementationDetail && !decl.isAuxDecl then
          let dTy := (← instantiateMVars decl.type).consumeMData
          let some (_, hLhs, _) := dTy.eq? | continue
          let hLhs := hLhs.consumeMData
          if !hLhs.isAppOfArity ``Program.fetch 2 then continue
          if fetchPcKey (hLhs.getArg! 1) != pcKey then continue
          if (hLhs.getArg! 0).consumeMData != progKey then continue
          if ← withReducible (isDefEq dTy ty) then
            g.assign decl.toExpr
            setGoals rest
            return true
    let declCacheRef ← getOrCreateVCGenDeclCacheRef
    let declName := (← Term.getDeclName?).getD .anonymous
    let lctx ← getLCtx
    let mut codeFVarIds : Array FVarId := #[]
    for decl in lctx do
      if mayContributeCodeProjection decl then
        codeFVarIds := codeFVarIds.push decl.fvarId
    let (hasCodeFacts, rawProjs) ← do
      let declCache ← declCacheRef.get
      if let some cached := declCache.hasCodeFetch?.filter (fun c => c.declName == declName && c.codeFVarIds == codeFVarIds) then
        pure (cached.hasCodeFacts, cached.rawProjs)
      else
        let mut rawProjs : Array (Expr × Expr) := #[]
        for fid in codeFVarIds do
          if let some decl := lctx.find? fid then
            rawProjs := rawProjs ++ (← collectCodeProjections decl.toExpr decl.type)
        let mut eqFacts : Array (Expr × Expr × Expr) := #[]
        for (prf, pTy) in rawProjs do
          if let some (_, eqLhs, eqRhs) := pTy.eq? then
            eqFacts := eqFacts.push (prf, eqLhs, eqRhs)
        let mut facts : Array (Expr × Expr) := #[]
        for (prf, pTy) in rawProjs do
          if pTy.isAppOfArity ``Program.hasCode 3 || pTy.isAppOfArity ``Program.hasWords 3 then
            let headFn := pTy.getAppFn
            facts := facts.push (prf, pTy)
            let hProg := pTy.getArg! 0
            let baseExpr := pTy.getArg! 1
            let hexExpr := pTy.getArg! 2
            for (eqPrf, eqLhs, eqRhs) in eqFacts do
              if eqLhs == baseExpr then
                let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
                let motive ← withLocalDeclD `_b bv64Ty fun b =>
                  mkLambdaFVars #[b] (mkApp3 headFn hProg b hexExpr)
                let prf' ← mkEqNDRec motive prf eqPrf
                let ty' := mkApp3 headFn hProg eqRhs hexExpr
                facts := facts.push (prf', ty')
        declCacheRef.modify fun c =>
          { c with hasCodeFetch? := some { declName, codeFVarIds, hasCodeFacts := facts, rawProjs } }
        pure (facts, rawProjs)
    for (hPrf, hcTy) in hasCodeFacts do
      let hProg := hcTy.getArg! 0
      let baseExpr := hcTy.getArg! 1
      let hexExpr := hcTy.getArg! 2
      if ← isDefEq hProg progExpr then
        let mut idxOpt : Option Nat := none
        let mut rebaseBaseOffOpt : Option (Expr × Expr) := none
        if let some (64, baseVal) ← evalBitVecLit? baseExpr then
          if let some (64, pcVal) := pcLit? then
            let diff := (pcVal + (1 <<< 64) - baseVal) % (1 <<< 64)
            if diff % 4 == 0 then
              idxOpt := some (diff / 4)
        if idxOpt.isNone then
          if pcExpr == baseExpr || (!(pcExpr.isAppOfArity ``HAdd.hAdd 6) && (← withReducible (isDefEq pcExpr baseExpr))) then
            idxOpt := some 0
          else if pcExpr.isAppOfArity ``HAdd.hAdd 6 then
            let lhs1 := pcExpr.getArg! 4
            let rhs1 := pcExpr.getArg! 5
            if lhs1 == baseExpr || (← withReducible (isDefEq lhs1 baseExpr)) then
              if let some (64, offVal) ← evalBitVecLit? rhs1 then
                if offVal % 4 == 0 then
                  idxOpt := some (offVal / 4)
            else if lhs1.isAppOfArity ``HAdd.hAdd 6 then
              if (lhs1.getArg! 4) == baseExpr || (← withReducible (isDefEq (lhs1.getArg! 4) baseExpr)) then
                if let (some (64, v1), some (64, v2)) := (← evalBitVecLit? (lhs1.getArg! 5), ← evalBitVecLit? rhs1) then
                  let offVal := (v1 + v2) % (1 <<< 64)
                  if offVal % 4 == 0 then
                    idxOpt := some (offVal / 4)
            if idxOpt.isNone then
              if let some (64, pcOff) ← evalBitVecLit? rhs1 then
                let baseWhnf ← if baseExpr.isAppOfArity ``HAdd.hAdd 6 then pure baseExpr else whnf baseExpr
                if baseWhnf.isAppOfArity ``HAdd.hAdd 6 then
                  let bBase := baseWhnf.getArg! 4
                  let bOffExpr := baseWhnf.getArg! 5
                  if lhs1 == bBase || (← withReducible (isDefEq lhs1 bBase)) then
                    if let some (64, baseOff) ← evalBitVecLit? bOffExpr then
                      let diff := (pcOff + (1 <<< 64) - baseOff) % (1 <<< 64)
                      if diff % 4 == 0 then
                        idxOpt := some (diff / 4)
                        rebaseBaseOffOpt := some (lhs1, toExpr (BitVec.ofNat 64 baseOff))
        if let some i := idxOpt then
          let words? : Option (Array (BitVec 32)) ← do
            if hexExpr.isConst then
              let cName := hexExpr.constName!
              if let some cachedWords := (← hexConstWordsCacheRef.get).get? cName then
                pure (some cachedWords)
              else if let some wArr ← evalWordListExpr? hexExpr then
                hexConstWordsCacheRef.modify (·.insert cName wArr)
                pure (some wArr)
              else
                pure none
            else if let some cachedWords := (← declCacheRef.get).hexExprWords.get? hexExpr then
              pure (some cachedWords)
            else if let some wArr ← evalWordListExpr? hexExpr then
              declCacheRef.modify fun c => { c with hexExprWords := c.hexExprWords.insert hexExpr wArr }
              pure (some wArr)
            else
              pure none
          if let some words := words? then
            if h_lt : i < words.size then
              let w := words[i]
              let decoded? : Option (Expr × Expr) ← do
                if let some pair := (← decodedWordExprCacheRef.get).get? w then
                  pure (some pair)
                else if let some inst := Arm64.decode w then
                  let instExpr ← cleanReducedExpr (toExpr inst)
                  let someInstExpr ← mkAppM ``Option.some #[instExpr]
                  let pair := (instExpr, someInstExpr)
                  decodedWordExprCacheRef.modify (·.insert w pair)
                  pure (some pair)
                else
                  pure none
              if let some (instExpr, someInstExpr) := decoded? then
                if ← isDefEq rhs someInstExpr then
                  let iExpr := toExpr i
                  let offExpr := toExpr (BitVec.ofNat 64 (4 * i))
                  let basePlusOff ← mkAppM ``HAdd.hAdd #[baseExpr, offExpr]
                  let hPcProof? : Option Expr ← do
                    if pcExpr == basePlusOff then
                      some <$> mkEqRefl pcExpr
                    else if i == 0 && (pcExpr == baseExpr || (← withReducible (isDefEq pcExpr baseExpr))) then
                      let addZero ← mkAppM ``BitVec.add_zero #[baseExpr]
                      some <$> mkEqSymm addZero
                    else if let some (bBase, bOffLit) := rebaseBaseOffOpt then
                      let assocPrf ← mkAppM ``BitVec.add_assoc #[bBase, bOffLit, offExpr]
                      let symmPrf ← mkEqSymm assocPrf
                      let eqTy ← mkEq pcExpr basePlusOff
                      some <$> mkExpectedTypeHint symmPrf eqTy
                    else if pcExpr.isAppOfArity ``HAdd.hAdd 6 && (pcExpr.getArg! 4).isAppOfArity ``HAdd.hAdd 6 then
                      let lhs1 := pcExpr.getArg! 4
                      let c1 := lhs1.getArg! 5
                      let c2 := pcExpr.getArg! 5
                      let assocPrf ← mkAppM ``BitVec.add_assoc #[baseExpr, c1, c2]
                      let eqTy ← mkEq pcExpr basePlusOff
                      some <$> mkExpectedTypeHint assocPrf eqTy
                    else if ← isDefEq pcExpr basePlusOff then
                      some <$> mkEqRefl pcExpr
                    else
                      pure none
                  if let some hPcProof := hPcProof? then
                    let hDecProof ← mkEqRefl someInstExpr
                    let hCodeExpr : Expr := mkApp3 (mkConst ``Program.hasCode) progExpr baseExpr hexExpr
                    let hHyp ← mkExpectedTypeHint hPrf hCodeExpr
                    let proof := mkAppN (mkConst ``Program.fetch_of_hasCode_decodeAt)
                      #[progExpr, baseExpr, pcExpr, hexExpr, iExpr, instExpr, hHyp, hPcProof, hDecProof]
                    g.assign proof
                    setGoals rest
                    return true
          else if let some proof ← tryCloseRelocWordFetch progExpr baseExpr pcExpr hexExpr rhs hPrf i rebaseBaseOffOpt rawProjs declCacheRef then
            g.assign proof
            setGoals rest
            return true
    return false

/-- Fast `MetaM` check to close `s.status = .Running` directly from a root-state hypothesis
    `hrun : s0.status = .Running` using explicit `State.status_*` spine lemmas instead of `rfl`. -/
def tryCloseRunningStatus (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | return false
  if !lhs.isAppOfArity ``State.status 1 || !rhs.isConstOf ``ExecStatus.Running then
    return false
  let s := lhs.getArg! 0
  let extract? ← extractStateStatusProof s
  let stExpr := (extract?.map (·.1)).getD lhs
  if stExpr.isConstOf ``ExecStatus.Running then
    match extract? with
    | some (_, prf) => g.assign prf
    | none => g.assign (← mkEqRefl rhs)
    return true
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let dty ← instantiateMVars decl.type
      if let some (_, dlhs, drhs) := dty.eq? then
        if dlhs == stExpr && drhs.isConstOf ``ExecStatus.Running then
          match extract? with
          | some (_, prf) => g.assign (← mkEqTrans prf decl.toExpr)
          | none => g.assign decl.toExpr
          return true
  return false

/-- Prove `base.canX addr n = true` (`canRead` if `isRead`, else `canWrite`) for the memory
    `base` below all stores: from a local fact, an owned separation-logic block containing
    `[addr, addr + n)`, an indexed element of an owned word array, or (for a range spanning
    several blocks) by splitting off the first byte (at most `fuel` times). -/
partial def provePermBase? (isRead : Bool) (base addr : Expr) (nVal : Nat) (fuel : Nat := 64) :
    TacticM (Option Expr) := do
  let nLit := mkNatLit nVal
  -- A local fact `base.canX addr n = true`.
  let fn := if isRead then ``Arm64.Memory.canRead else ``Arm64.Memory.canWrite
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.true && lhs.isAppOfArity fn 3 do continue
    unless ← withReducible (isDefEq (lhs.getArg! 0) base) do continue
    unless ← withReducible (isDefEq (lhs.getArg! 1) addr) do continue
    unless (← (Meta.evalNat (lhs.getArg! 2)).run) == some nVal do continue
    return some decl.toExpr
  -- A local region fact `base.RW b len` (or, for loads, `base.Readable b len`) covering
  -- `[addr, addr + n)`.
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let isRW := ty.isAppOfArity ``Arm64.Memory.RW 3
    let isRd := isRead && ty.isAppOfArity ``Arm64.Memory.Readable 3
    unless isRW || isRd do continue
    unless ← withReducible (isDefEq (ty.getArg! 0) base) do continue
    let rb := ty.getArg! 1
    let rlen := ty.getArg! 2
    let hkTy ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat
      #[← mkAppM ``HSub.hSub #[addr, rb]], nLit], rlen]
    let some hk ← proveRegionWriteBound? hkTy | continue
    let hnTy ← mkAppM ``LE.le #[rlen, ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]]
    let some hn ← proveRegionWriteBound? hnTy | continue
    let lem := if isRd then ``Arm64.Memory.Readable.canRead_sub
      else if isRead then ``Arm64.Memory.RW.canRead_sub else ``Arm64.Memory.RW.canWrite_sub
    let some prf ← observing? (mkAppM lem #[decl.toExpr, hk, hn]) | continue
    return some prf
  let some (h, P) ← SepSolver.findSatHyp? base | return none
  let P ← instantiateMVars P
  let as := SepSolver.atoms P
  let lemmaName := if isRead then ``IsBlock.canRead_sub else ``IsBlock.canWrite_sub
  for hi : i in [:as.size] do
    let some blk ← SepSolver.blockOf? as[i] | continue
    let hkTy ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat
      #[← mkAppM ``HSub.hSub #[addr, blk.base]], nLit], blk.len]
    let some hk ← proveRegionWriteBound? hkTy | continue
    let hnTy ← mkAppM ``LE.le #[blk.len, ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]]
    let some hn ← proveRegionWriteBound? hnTy | continue
    let (_, p) ← SepSolver.focus base P h i
    let some prf ← observing? (mkAppM lemmaName #[blk.isBlock, p, hk, hn]) | continue
    return some prf
  -- Indexed element `a + (i <<< 3)` of an owned word array `a ↦₆₄* ws`.
  if nVal == 8 && addr.isAppOfArity ``HAdd.hAdd 6 then
    let a := addr.getArg! 4
    let off := addr.getArg! 5
    if off.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
      let idx := off.getArg! 4
      if (← (Meta.evalNat (off.getArg! 5)).run) == some 3 then
        for hi : i in [:as.size] do
          let atm := as[i]
          unless atm.isAppOfArity ``Arm64.pointsToWords64 2 do continue
          unless ← withReducible (isDefEq (atm.getArg! 0) a) do continue
          let ws := atm.getArg! 1
          let hiTy ← mkAppM ``LT.lt #[← mkAppM ``BitVec.toNat #[idx], ← mkAppM ``List.length #[ws]]
          let some hbound ← proveRegionWriteBound? hiTy | continue
          let (_, p) ← SepSolver.focus base P h i
          let lem := if isRead then ``canRead_shl3_of_words else ``canWrite_shl3_of_words
          let some prf ← observing? (mkAppM lem #[p, idx, hbound]) | continue
          return some prf
  -- A range spanning several blocks: split off the first byte.
  if nVal ≥ 2 && fuel > 0 then
    let some p1 ← provePermBase? isRead base addr 1 0 | return none
    let addr' ← mkAppM ``HAdd.hAdd #[addr, toExpr (1#64 : BitVec 64)]
    let some p2 ← provePermBase? isRead base addr' (nVal - 1) (fuel - 1) | return none
    let lem := if isRead then ``Arm64.Memory.canRead_succ_of else ``Arm64.Memory.canWrite_succ_of
    let prf := mkAppN (mkConst lem) #[base, addr, mkNatLit (nVal - 1), p1, p2]
    return some prf
  return none

/-- Transport `prf : mPrev.canX addr nLit = true` across one write or `mapZero` step. -/
def transportPermStep (isRead : Bool) (addr nLit prf mPrev : Expr)
    (w : Name × Expr × Expr × Expr) : MetaM Expr := do
  let (wName, _, wAddr, wVal) := w
  if wName == ``Arm64.Memory.mapZero then
    let lem := if isRead then ``Arm64.Memory.canRead_mapZero_of_canRead
      else ``Arm64.Memory.canWrite_mapZero_of_canWrite
    mkAppM lem #[wAddr, wVal, prf]
  else if isRead then
    let lem := match wName with
      | ``Arm64.Memory.write8 => ``Arm64.Memory.canRead_write8_of_canRead
      | ``Arm64.Memory.write16 => ``Arm64.Memory.canRead_write16_of_canRead
      | ``Arm64.Memory.write32 => ``Arm64.Memory.canRead_write32_of_canRead
      | ``Arm64.Memory.write64 => ``Arm64.Memory.canRead_write64_of_canRead
      | _ => ``Arm64.Memory.canRead_write128_of_canRead
    mkAppM lem #[wAddr, wVal, prf]
  else
    let lem := match wName with
      | ``Arm64.Memory.write8 => ``Arm64.Memory.perm_write8
      | ``Arm64.Memory.write16 => ``Arm64.Memory.perm_write16
      | ``Arm64.Memory.write32 => ``Arm64.Memory.perm_write32
      | ``Arm64.Memory.write64 => ``Arm64.Memory.perm_write64
      | _ => ``Arm64.Memory.perm_write128
    let hperm ← mkAppM lem #[mPrev, wAddr, wVal]
    let c ← mkAppOptM ``Arm64.Memory.canWrite_congr #[none, none, some hperm, some addr, some nLit]
    mkEqTrans c prf

/-- Prove `mem.canRead a n = true` / `mem.canWrite a n = true` (`e` is the `canRead`/`canWrite`
    application) via `provePermBase?` on the memory below the stores of `mem`, or from a
    `Memory.mapZero` step on the spine of `mem` when `a` lies inside the newly mapped region. -/
def provePermAccess? (e : Expr) : TacticM (Option Expr) := do
  let isRead := e.isAppOfArity ``Arm64.Memory.canRead 3
  let mem := e.getArg! 0
  let addr := e.getArg! 1
  let nExpr := e.getArg! 2
  let nVal? ← match ← (Meta.evalNat nExpr).run with
    | some v => pure (some v)
    | none => do
      let r ← withTransparency .default (whnf nExpr)
      match r.rawNatLit? with
      | some v => pure (some v)
      | none => (Meta.evalNat r).run
  let some nVal := nVal? | return none
  let nLit := mkNatLit nVal
  let (writes, base) := SepSolver.peelWrites mem
  let mut startFound : Option (Nat × Expr × Expr) := none
  if let some prf ← provePermBase? isRead base addr nVal then
    startFound := some (0, base, prf)
  else
    for hk : k in [:writes.size] do
      let (wName, mAfter, wAddr, wVal) := writes[k]
      unless wName == ``Arm64.Memory.mapZero do continue
      let mPrev := if k == 0 then base else writes[k - 1]!.2.1
      let some hmap ← SepSolver.proveCanMap? mPrev wAddr wVal | continue
      let hkTy ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat
        #[← mkAppM ``HSub.hSub #[addr, wAddr]], nLit], wVal]
      let some hkPrf ← proveRegionWriteBound? hkTy | continue
      let hnTy ← mkAppM ``LE.le #[wVal, ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]]
      let some hnPrf ← proveRegionWriteBound? hnTy | continue
      let lem := if isRead then ``Arm64.Memory.canRead_mapZero_sub else ``Arm64.Memory.canWrite_mapZero_sub
      let some prf ← observing? (mkAppM lem #[hmap, hkPrf, hnPrf]) | continue
      startFound := some (k + 1, mAfter, prf)
      break
  let some (startIdx, startMem, initPrf) := startFound | return none
  let mut prf := initPrf
  let mut mPrev := startMem
  for k in [startIdx:writes.size] do
    let w := writes[k]!
    prf ← transportPermStep isRead addr nLit prf mPrev w
    mPrev := w.2.1
  return some (← mkExpectedTypeHint prf (← mkEq e (mkConst ``Bool.true)))

/-- All closed `Memory.canRead` / `Memory.canWrite` applications in `e`. -/
partial def collectPermChecks (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc :=
    if (e.isAppOfArity ``Arm64.Memory.canRead 3 || e.isAppOfArity ``Arm64.Memory.canWrite 3)
        && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => collectPermChecks a (collectPermChecks f acc)
  | .lam _ t b _ | .forallE _ t b _ => collectPermChecks b (collectPermChecks t acc)
  | .letE _ t v b _ => collectPermChecks b (collectPermChecks v (collectPermChecks t acc))
  | .mdata _ b => collectPermChecks b acc
  | .proj _ _ b => collectPermChecks b acc
  | _ => acc

def arm64DischargePermsImpl : TacticM Unit := do
  let g ← getMainGoal
  let names ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let mut prfs : Array Expr := #[]
    for sub in collectPermChecks ty do
      if let some p ← provePermAccess? sub then
        prfs := prfs.push p
    let mut g' := g
    let mut names : Array Name := #[]
    for p in prfs do
      let n := Name.mkSimple s!"_hperm_{names.size}"
      g' ← g'.assert n (← inferType p) p
      let (_, g'') ← g'.intro1P
      g' := g''
      names := names.push n
    replaceMainGoal [g']
    pure names
  if names.isEmpty then return
  let ids : Array Ident := names.map mkIdent
  let mut args : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for id in ids do
    args := args.push (← `(Lean.Parser.Tactic.simpLemma| $id:ident))
  args := args ++ #[
    ← `(Lean.Parser.Tactic.simpLemma| Bool.not_true),
    ← `(Lean.Parser.Tactic.simpLemma| Bool.not_false),
    ← `(Lean.Parser.Tactic.simpLemma| Bool.and_true),
    ← `(Lean.Parser.Tactic.simpLemma| Bool.true_and),
    ← `(Lean.Parser.Tactic.simpLemma| Bool.and_self),
    ← `(Lean.Parser.Tactic.simpLemma| Bool.true_eq_false),
    ← `(Lean.Parser.Tactic.simpLemma| Bool.false_eq_true),
    ← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte),
    ← `(Lean.Parser.Tactic.simpLemma| ite_true),
    ← `(Lean.Parser.Tactic.simpLemma| ite_false),
    ← `(Lean.Parser.Tactic.simpLemma| not_false_eq_true)]
  evalTactic (← `(tactic| try simp only [$args,*]))
  for id in ids do
    evalTactic (← `(tactic| try clear $id:ident))

elab "arm64_discharge_perms_internal" : tactic => arm64DischargePermsImpl

/-- Take a single instruction step along `reaches_pc` or `exits_with` (without checking `refl`). -/
elab "arm64_step_inst" : tactic => do
  introSpAlignedIfPresent
  let okStep ← tryTactic do
    let mvarId0 ← getMainGoal
    let ty0 ← mvarId0.withContext (instantiateMVars (← mvarId0.getType))
    if ty0.isAppOf ``exits_with then
      evalTactic (← `(tactic| apply exits_with_step))
    else if ty0.isAppOf ``reaches_outcome then
      evalTactic (← `(tactic| apply reaches_outcome_step))
    else
      evalTactic (← `(tactic| apply reaches_pc_step))
    let gs ← getGoals
    match gs with
    | g1 :: g2 :: g3 :: rest =>
      if !(← tryCloseRunningStatus g1) then
        setGoals [g1]
        evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
      setGoals [g2]
      evalTactic (← `(tactic| try simp (config := { decide := true }) only [arm64_norm, *]))
      if !(← getGoals).isEmpty then
        let closedByHasCode ← tryCloseFetchFromHasCode
        if !closedByHasCode then
          let g2' ← getMainGoal
          g2'.withContext do
            let ty ← instantiateMVars (← g2'.getType)
            if let some (_, lhs, rhs) := ty.eq? then
              if !lhs.isAppOfArity ``Option.some 2 && !lhs.hasFVar then
                let lhsRed ← Lean.Meta.reduce lhs
                let lhsClean ← cleanReducedExpr lhsRed
                let _ ← isDefEq lhsClean rhs
          evalTactic (← `(tactic| rfl))
      setGoals [g3]
      let isSysOrSvc ← g3.withContext do
        let ty3 ← instantiateMVars (← g3.getType)
        let stArg? :=
          if ty3.isAppOfArity ``reaches_outcome 7 then
            some (ty3.getArg! 6)
          else if ty3.getAppNumArgs >= 3 then
            some (ty3.getArg! 2)
          else
            none
        if let some stArg := stArg? then
          if stArg.isAppOf ``execInst && stArg.getAppNumArgs >= 2 then
            let instExpr := stArg.getArg! 0
            return (instExpr.find? fun e => e.isConstOf ``Instr.sysReg || e.isConstOf ``Instr.system).isSome
          if stArg.isAppOf ``Program.evalInst && stArg.getAppNumArgs >= 3 then
            let instExpr := stArg.getArg! 1
            return (instExpr.find? fun e => e.isConstOf ``Instr.sysReg || e.isConstOf ``Instr.system).isSome
        return false
      if isSysOrSvc then
        -- `MSR tpidr_el0, xt` is the one instruction whose `execInst` body is a raw `State`
        -- structure update. Rewrite it into the opaque `setTpidrEl0` combinator *before*
        -- `dsimp only [execInst]` expands it, otherwise later field rewrites (e.g. of `PC`)
        -- destroy the structure-update pattern and the framing lemmas stop matching.
        evalTactic (← `(tactic| try simp only [Program.evalInst_sysReg, Program.evalInst_system_halt, Program.evalInst_svc0, execInst_msr_tpidr, execInst_svc0, execInst_brk1]))
      evalTactic (← `(tactic| (
        try dsimp only [Program.evalInst, execInst, execInstWithSvc, applySimdResult, applySimdSatResult, evalSimdModImmExt, evalSimdImmShiftNonZeroExt, evalSimdImmShiftNonZeroExtSatFlags, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags, evalSimdTwoRegMiscExt, evalSimdTwoRegMiscExtSatFlags, advSimdExpandImm, narrowSimdLanes, anySimdLane, anyZipSimdLane, anyNarrowSimdLane, simdLaneUInt, simdLaneSInt, intToSimdLane, aslRShr, aslSignedSat, aslSignedSatFlag, aslUnsignedSat, aslUnsignedSatFlag, aslSat, aslSatFlag, simdClz, simdCls, shaChoose32, shaParity32, shaMajority32, shaMajority64, sha256Sigma0, sha256Sigma1, sha256Hash, evalCryptoSha2Reg, evalCryptoSha3Reg, evalCryptoSha512Reg2, evalCryptoSha512Reg3, evalCryptoSha3FourReg, evalCryptoXar, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare, execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp, evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned, checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits, Reg.fromSPBits]
        try simp (config := { decide := true }) only [arm64_norm, *]
        try arm64_discharge_perms_internal
      )))
      setGoals ((← getGoals) ++ rest)
    | _ => throwError "unexpected goals"
  if !okStep then
    throwError "arm64_step_inst: goal is not a steppable reaches_pc or exits_with state"

/-- Fast `MetaM` check whether `s`'s PC could possibly equal `target_pc`.
    When `s`'s PC reduces along the state spine to a concrete `BitVec` numeral `pcVal`
    (e.g. `0x100a4#64`) while `target_pc` is either a different concrete numeral or a symbolic
    return address (e.g. `s0.readReg64 .lr`), `s.pc = target_pc` cannot hold, so `arm64_step`
    can skip `apply reaches_pc_refl` + `simp` completely. -/
partial def evalSpinePCLit? (s : Expr) : MetaM (Option (Nat × Nat)) := do
  if let some lit ← evalBitVecLit? s then
    return some lit
  if s.isAppOfArity ``State.advancePC 1 then
    if let some (w, v) ← evalSpinePCLit? (s.getArg! 0) then
      return some (w, (v + 4) % (1 <<< w))
    return none
  if s.isAppOfArity ``State.setPC 2 then
    return ← evalBitVecLit? (s.getArg! 1)
  if let some s' := stateSpineParent? s then
    return ← evalSpinePCLit? s'
  if s.isFVar then
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOfArity ``State.pc 1 && lhs.getArg! 0 == s then
            if let some lit ← evalBitVecLit? rhs then
              return some lit
  return none

/-- Trace `s`'s PC along the state-update spine when `s.pc` is relative to a symbolic `base`
    (e.g. `prog.fnAddr "foo" + 0x8#64`). -/
partial def evalSpinePCBaseOff? (s : Expr) : MetaM (Option (Expr × Nat)) := do
  if s.isAppOfArity ``State.advancePC 1 then
    if let some (base, off) ← evalSpinePCBaseOff? (s.getArg! 0) then
      return some (base, (off + 4) % (1 <<< 64))
    return none
  if s.isAppOfArity ``State.setPC 2 then
    return ← evalPCBaseOff? (s.getArg! 1)
  if let some s' := stateSpineParent? s then
    return ← evalSpinePCBaseOff? s'
  if s.isFVar then
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOfArity ``State.pc 1 && lhs.getArg! 0 == s then
            if let some bo ← evalPCBaseOff? rhs then
              return some bo
  return none

/-- True if `s` has a `State.setPC` (such as `ret` / `br`) along its state-update spine. -/
partial def hasSetPCAlongSpine (s : Expr) : Bool :=
  if s.isAppOfArity ``State.setPC 2 then true
  else if s.isAppOfArity ``State.advancePC 1 then
    hasSetPCAlongSpine (s.getArg! 0)
  else if let some s' := stateSpineParent? s then
    hasSetPCAlongSpine s'
  else false

/-- Take one symbolic step along `reaches_pc` or `exits_with` (or finish via `refl` if at target). -/
elab "arm64_step" : tactic => do
  introSpAlignedIfPresent
  let mvarId ← getMainGoal
  let ty ← mvarId.withContext (instantiateMVars (← mvarId.getType))
  if ty.isAppOfArity ``reaches_outcome 7 then
    let s0Expr := ty.getArg! 5
    let stateExpr := ty.getArg! 6
    if stateExpr.isAppOfArity ``ite 5 then
      let okIte ← tryTactic do
        evalTactic (← `(tactic| apply reaches_outcome_ite <;> intro _))
      if okIte then return
    if let some stExpr := extractStateStatusExpr stateExpr then
      if stExpr.isConstOf ``ExecStatus.Panicked then
        let okReflPanic ← tryTactic do
          evalTactic (← `(tactic| apply reaches_outcome_refl_panic))
          let gs ← getGoals
          match gs with
          | g1 :: g2 :: rest =>
            setGoals [g1]
            evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
            setGoals [g2]
            evalTactic (← `(tactic| (
              (try simp (config := { decide := true }) only [arm64_norm, *]) <;>
              (try omega) <;>
              (try bv_fallback)
            )))
            setGoals ((← getGoals) ++ rest)
          | _ => throwError "unexpected goals"
        if okReflPanic then return
      if stExpr.isConstOf ``ExecStatus.OutOfMemory then
        let okReflOom ← tryTactic do
          evalTactic (← `(tactic| apply reaches_outcome_refl_oom))
          let gs ← getGoals
          match gs with
          | g1 :: g2 :: rest =>
            setGoals [g1]
            evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
            setGoals [g2]
            evalTactic (← `(tactic| (
              (try simp (config := { decide := true }) only [arm64_norm, *]) <;>
              (try omega) <;>
              (try bv_fallback)
            )))
            setGoals ((← getGoals) ++ rest)
          | _ => throwError "unexpected goals"
        if okReflOom then return
      if stExpr.isAppOfArity ``ExecStatus.Exited 1 then
        let codeStx ← Term.exprToSyntax (stExpr.getArg! 0)
        let okReflExit ← tryTactic do
          evalTactic (← `(tactic| refine reaches_outcome_refl_exit (code := $codeStx) ?_ ?_))
          let gs ← getGoals
          match gs with
          | g1 :: g2 :: rest =>
            setGoals [g1]
            evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
            setGoals [g2]
            evalTactic (← `(tactic| (
              (try simp (config := { decide := true }) only [arm64_norm, *]) <;>
              (try omega) <;>
              (try bv_fallback)
            )))
            setGoals ((← getGoals) ++ rest)
          | _ => throwError "unexpected goals"
        if okReflExit then return
    let targetPC := mkApp2 (mkConst ``State.readReg64) s0Expr (mkConst ``Reg.lr)
    let mut canBeRefl := true
    if let some (w1, v1) ← mvarId.withContext (evalSpinePCLit? stateExpr) then
      if let some (w2, v2) ← mvarId.withContext (evalBitVecLit? targetPC) then
        canBeRefl := (w1 == w2 && v1 == v2)
      else
        canBeRefl := false
    else if let some (base1, off1) ← mvarId.withContext (evalSpinePCBaseOff? stateExpr) then
      if let some (base2, off2) ← mvarId.withContext (evalPCBaseOff? targetPC) then
        if base1 == base2 then
          canBeRefl := (off1 == off2)
      else if targetPC.isAppOfArity ``State.readReg64 2 then
        canBeRefl := false
    else if targetPC.isAppOfArity ``State.readReg64 2 && !hasSetPCAlongSpine stateExpr then
      canBeRefl := false
    if canBeRefl then
      let okReflRet ← tryTactic do
        evalTactic (← `(tactic| apply reaches_outcome_refl_return))
        let gs ← getGoals
        match gs with
        | g1 :: g2 :: g3 :: rest =>
          setGoals [g1]
          evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
          setGoals [g2]
          evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
          setGoals [g3]
          evalTactic (← `(tactic| (
            (try simp (config := { decide := true }) only [arm64_norm, *]) <;>
            (try omega) <;>
            (try bv_fallback)
          )))
          setGoals ((← getGoals) ++ rest)
        | _ => throwError "unexpected goals"
      if okReflRet then return
    evalTactic (← `(tactic| arm64_step_inst))
    return
  if ty.isAppOfArity ``exits_with 5 then
    let stateExpr := ty.getArg! 2
    if stateExpr.isAppOfArity ``ite 5 then
      let okIte ← tryTactic do
        evalTactic (← `(tactic| apply exits_with_ite <;> intro _))
      if okIte then return
    if let some stExpr := extractStateStatusExpr stateExpr then
      if stExpr.isConstOf ``ExecStatus.OutOfMemory then
        let okReflOom ← tryTactic do
          evalTactic (← `(tactic| apply exits_with_oom))
          let gs ← getGoals
          match gs with
          | g1 :: g2 :: rest =>
            setGoals [g1]
            evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
            setGoals [g2]
            evalTactic (← `(tactic| (try simp (config := { decide := true }) only [arm64_norm, *])))
            setGoals ((← getGoals) ++ rest)
          | _ => throwError "unexpected goals"
        if okReflOom then return
    let isExited := match extractStateStatusExpr stateExpr with
      | some stExpr => stExpr.isAppOfArity ``ExecStatus.Exited 1
      | none => false
    if isExited then
      let okRefl ← tryTactic do
        evalTactic (← `(tactic| apply exits_with_refl))
        let gs ← getGoals
        match gs with
        | g1 :: g2 :: rest =>
          setGoals [g1]
          evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
          setGoals [g2]
          evalTactic (← `(tactic| (try simp (config := { decide := true }) only [arm64_norm, *])))
          setGoals ((← getGoals) ++ rest)
        | _ => throwError "unexpected goals"
      if okRefl then return
    evalTactic (← `(tactic| arm64_step_inst))
    return
  let mut isIte := false
  let mut canBeRefl := true
  if ty.isAppOfArity ``reaches_pc 5 then
    let targetPC := ty.getArg! 1
    let stateExpr := ty.getArg! 2
    if stateExpr.isAppOfArity ``ite 5 then
      isIte := true
      canBeRefl := false
    else if let some stExpr := extractStateStatusExpr stateExpr then
      if stExpr.isConstOf ``ExecStatus.OutOfMemory then
        let okReflOom ← tryTactic do
          evalTactic (← `(tactic| apply reaches_pc_oom))
          let gs ← getGoals
          match gs with
          | g1 :: g2 :: rest =>
            setGoals [g1]
            evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
            setGoals [g2]
            evalTactic (← `(tactic| (try simp (config := { decide := true }) only [arm64_norm, *])))
            setGoals ((← getGoals) ++ rest)
          | _ => throwError "unexpected goals"
        if okReflOom then return
    if let some (w1, v1) ← mvarId.withContext (evalSpinePCLit? stateExpr) then
      if let some (w2, v2) ← mvarId.withContext (evalBitVecLit? targetPC) then
        canBeRefl := (w1 == w2 && v1 == v2)
      else
        -- `stateExpr` has a concrete literal PC while `targetPC` is symbolic (e.g. `s0.readReg64 .lr`)
        canBeRefl := false
    else if let some (base1, off1) ← mvarId.withContext (evalSpinePCBaseOff? stateExpr) then
      if let some (base2, off2) ← mvarId.withContext (evalPCBaseOff? targetPC) then
        if base1 == base2 then
          canBeRefl := (off1 == off2)
      else if targetPC.isAppOfArity ``State.readReg64 2 then
        canBeRefl := false
    else if targetPC.isAppOfArity ``State.readReg64 2 && !hasSetPCAlongSpine stateExpr then
      canBeRefl := false
  if isIte then
    let okIte ← tryTactic do
      evalTactic (← `(tactic| apply reaches_pc_ite <;> intro _))
    if okIte then return
  if canBeRefl then
    let okRefl ← tryTactic do
      evalTactic (← `(tactic| apply reaches_pc_refl))
      let gs ← getGoals
      match gs with
      | g1 :: g2 :: g3 :: rest =>
        setGoals [g1]
        evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
        setGoals [g2]
        evalTactic (← `(tactic| (simp (config := { decide := true }) only [arm64_norm, *]; done)))
        setGoals [g3]
        evalTactic (← `(tactic| (try simp (config := { decide := true }) only [arm64_norm, *])))
        setGoals ((← getGoals) ++ rest)
      | _ => throwError "unexpected goals"
    if okRefl then return
  evalTactic (← `(tactic| arm64_step_inst))

/-- True if `ty` mentions any code or callee bundle constant (`hasCode`, `codeAt`, `codeAtAddr`,
    `FnCode.holds`, `hasCodeBundle`, `calleesOk`, `allHold`). -/
def mentionsCodeOrCalleePred (ty : Expr) : Bool :=
  (ty.find? fun e =>
    e.isConstOf ``Program.hasCode ||
    e.isConstOf ``Program.hasWords ||
    e.isConstOf ``Program.hasWordsOff ||
    e.isConstOf ``Program.codeAt ||
    e.isConstOf ``Program.codeAtOff ||
    e.isConstOf ``Program.codeAtAddr ||
    e.isConstOf ``FnCode.holds ||
    e.isConstOf ``Program.hasCodeBundle ||
    e.isConstOf ``Program.calleesOk ||
    e.isConstOf ``allHold).isSome

/-- Unfold code/callee bundle definitions (`hasCodeBundle`, `FnCode.holds`, `codeAtAddr`,
    `calleesOk`, `allHold`, or user `CodeAt` wrappers around them) if unfolding exposes an `And`. -/
partial def unfoldToAndIfPossible? (ty : Expr) (depth : Nat := 16) : MetaM (Option Expr) := do
  if depth == 0 then return none
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``And 2 then
    return if mentionsCodeOrCalleePred ty then some ty else none
  if let some ty' ← stepUnfoldCodePred? ty then
    return ← unfoldToAndIfPossible? ty' (depth - 1)
  return none

/-- True if `e` is a stack-pointer or program-counter observation of a machine state (`s.sp`,
    `s.pc`). General-purpose register observations (`s.readReg64 r`) are deliberately excluded:
    substituting them into goals makes `simp [arm64_norm, *]` in `arm64_step_inst` attempt
    expensive failed unifications (observed as a >2x slowdown on multi-instruction suites). -/
def isStateRegObservation (e : Expr) : Bool :=
  e.isAppOfArity ``State.sp 1 || e.isAppOfArity ``State.pc 1

/-- Substitute ghost variables bound by equations `_h_split_k : obs = g` produced when
    `arm64_norm_hyps` splits a pure precondition (e.g. `⌜s0.sp = sp0 ∧ ...⌝ ∗ P`), where `obs` is a
    stack-pointer/pc observation of a state (`s0.sp`, `s0.pc`) and `g` is a local (ghost)
    variable. Replacing `g` by `obs` everywhere keeps hypotheses and goal phrased over the same
    terms, so that facts such as `s0.sp &&& 15 = 0` apply to goals that mention `sp0`. -/
def substSplitGhostEqs : TacticM Unit := do
  let mut progress := true
  while progress do
    progress := false
    let g ← getMainGoal
    let cands ← g.withContext do
      let mut cands : Array FVarId := #[]
      for decl in (← getLCtx) do
        if decl.isImplementationDetail || decl.isAuxDecl then continue
        unless decl.userName.toString.startsWith "_h_split_" do continue
        let ty ← instantiateMVars decl.type
        let some (_, lhs, rhs) := ty.eq? | continue
        unless rhs.isFVar && isStateRegObservation lhs do continue
        let rDecl ← rhs.fvarId!.getDecl
        if rDecl.isLet || lhs.containsFVar rhs.fvarId! then continue
        cands := cands.push decl.fvarId
      return cands
    for h in cands do
      let ok ← try
          let g' ← Lean.Meta.subst g h
          replaceMainGoal [g']
          pure true
        catch _ => pure false
      if ok then
        progress := true
        break

/-- Split conjunction hypotheses (`P ∧ Q`, including bundled `CodeBundle`, `codeAtAddr`, and
    `calleesOk` hypotheses) in the local context, normalize all local hypotheses once
    (without touching the goal target), split any pure/existential hypotheses exposed by
    separation-logic normalization, and extract `Memory.read*` / `DisjointRegions` facts. -/
elab "arm64_norm_hyps" : tactic => do
  introSpAlignedIfPresent
  let splitIdxRef ← IO.mkRef (0 : Nat)
  let nextSplitIdent : TacticM (TSyntax `ident) := do
    let i := (← splitIdxRef.get) + 1
    splitIdxRef.set i
    return mkIdent (Name.mkSimple s!"_h_split_{i}")
  let splitAndExistsLoop : TacticM Unit := do
    let mut progress := true
    while progress do
      progress := false
      let mvarId ← getMainGoal
      let lctx ← mvarId.withContext getLCtx
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
          let ty ← mvarId.withContext (instantiateMVars decl.type)
          if ty.isAppOfArity ``And 2 then
            let id := mkIdent decl.userName
            let hLhs ← nextSplitIdent
            if (← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$hLhs:ident, $id:ident⟩)))) then
              progress := true
              break
          else if ty.isAppOfArity ``Exists 2 &&
                  (ty.find? (·.isConstOf ``SepProp.Satisfies)).isSome then
            let id := mkIdent decl.userName
            let hW ← nextSplitIdent
            if (← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$hW:ident, $id:ident⟩)))) then
              progress := true
              break
          else if let some andTy ← mvarId.withContext (unfoldToAndIfPossible? ty) then
            let g' ← mvarId.changeLocalDecl decl.fvarId andTy
            replaceMainGoal [g']
            let id := mkIdent decl.userName
            let hLhs ← nextSplitIdent
            if (← tryTactic (evalTactic (← `(tactic| rcases $id:ident with ⟨$hLhs:ident, $id:ident⟩)))) then
              progress := true
              break
  splitAndExistsLoop
  let mvarId ← getMainGoal
  let lctx ← mvarId.withContext getLCtx
  let mut hypIdents : Array (TSyntax `ident) := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
      let ty ← mvarId.withContext (instantiateMVars decl.type)
      if ← mvarId.withContext (Meta.isProp ty) then
        hypIdents := hypIdents.push (mkIdent decl.userName)
  if !hypIdents.isEmpty then
    let _ ← tryTactic (evalTactic (← `(tactic| simp (config := { decide := true }) only [arm64_norm] at $[$hypIdents:ident]*)))
  splitAndExistsLoop
  substSplitGhostEqs
  extractSepHypFacts

/-- Fast structural equality check for code/callee predicates (`Program.hasCode`, `Program.codeAt`,
    `FnCode.holds`, `Program.subroutineOk`, `subroutine_ok`) that compares arguments directly
    without unfolding `Program.hasCode` into `Program.parseHexWords`. -/
def fastCodePredEq (t1 t2 : Expr) : MetaM Bool := do
  if t1 == t2 then return true
  if t1.isAppOfArity ``Program.hasCode 3 && t2.isAppOfArity ``Program.hasCode 3 then
    return (← isDefEq (t1.getArg! 0) (t2.getArg! 0)) &&
           (← isDefEq (t1.getArg! 1) (t2.getArg! 1)) &&
           (← isDefEq (t1.getArg! 2) (t2.getArg! 2))
  if t1.isAppOfArity ``Program.codeAt 3 && t2.isAppOfArity ``Program.codeAt 3 then
    return (← isDefEq (t1.getArg! 0) (t2.getArg! 0)) &&
           (← isDefEq (t1.getArg! 1) (t2.getArg! 1)) &&
           (← isDefEq (t1.getArg! 2) (t2.getArg! 2))
  if t1.isAppOfArity ``FnCode.holds 2 && t2.isAppOfArity ``FnCode.holds 2 then
    return (← isDefEq (t1.getArg! 0) (t2.getArg! 0)) &&
           (← isDefEq (t1.getArg! 1) (t2.getArg! 1))
  if t1.isAppOfArity ``Program.subroutineOk 6 && t2.isAppOfArity ``Program.subroutineOk 6 then
    -- args: `S α inst prog fnName spec`
    return (← isDefEq (t1.getArg! 3) (t2.getArg! 3)) &&
           (← isDefEq (t1.getArg! 4) (t2.getArg! 4)) &&
           (← isDefEq (t1.getArg! 5) (t2.getArg! 5))
  if t1.isAppOfArity ``subroutine_ok 4 && t2.isAppOfArity ``subroutine_ok 4 then
    return (← isDefEq (t1.getArg! 1) (t2.getArg! 1)) &&
           (← isDefEq (t1.getArg! 2) (t2.getArg! 2)) &&
           (← isDefEq (t1.getArg! 3) (t2.getArg! 3))
  withReducibleAndInstances (isDefEq t1 t2)

/-- Construct a proof of `goalTy` from a pool of `(proofExpr, typeExpr)` projections,
    splitting conjunctive goals (`And.intro`) and unfolding bundle/code definitions as needed. -/
partial def solveGoalFromCodeProjs? (goalTy : Expr) (projs : Array (Expr × Expr))
    (depth : Nat := 32) : MetaM (Option Expr) := do
  if depth == 0 then return none
  let goalTy ← instantiateMVars goalTy
  if goalTy.isConstOf ``True then
    return some (mkConst ``True.intro)
  for (prf, pTy) in projs do
    if ← fastCodePredEq goalTy pTy then
      return some prf
  if goalTy.isAppOfArity ``And 2 then
    if let some prf1 ← solveGoalFromCodeProjs? (goalTy.getArg! 0) projs (depth - 1) then
      if let some prf2 ← solveGoalFromCodeProjs? (goalTy.getArg! 1) projs (depth - 1) then
        return some (← mkAppM ``And.intro #[prf1, prf2])
  if let some goalTy' ← stepUnfoldCodePred? goalTy then
    if let some prf ← solveGoalFromCodeProjs? goalTy' projs (depth - 1) then
      return some (← mkExpectedTypeHint prf goalTy)
  return none


/-- Extract the `(symbols, stubs)` list expressions from a concrete `Program` expression (by
    reducing the `Program.symbols` / `Program.stubs` projections to whnf). -/
def extractProgTables? (progExpr : Expr) : MetaM (Option (Expr × Expr)) := do
  let progExpr ← instantiateMVars progExpr
  let syms ← whnf (mkApp (mkConst ``Program.symbols) progExpr)
  let stubs ← whnf (mkApp (mkConst ``Program.stubs) progExpr)
  if (syms.isAppOfArity ``List.cons 3 || syms.isAppOfArity ``List.nil 1) &&
     (stubs.isAppOfArity ``List.cons 3 || stubs.isAppOfArity ``List.nil 1) then
    return some (syms, stubs)
  return none

/-- Walk a concrete `List (String × Nat)` table `tbl` looking up `name`, returning the found
    offset (if any) and a proof of `tbl.find? (·.1 == name) = some (name, off)` (resp. `= none`),
    without kernel `String.decEq` UTF-8 encoding. -/
partial def proveFindName? (tbl nameExpr nameCsExpr hName : Expr) (nameStr : String) :
    MetaM (Option (Option Expr × Expr)) := do
  let tblWhnf ← whnf tbl
  if tblWhnf.isAppOfArity ``List.nil 1 then
    return some (none, mkApp (mkConst ``Program.find?_name_nil) nameExpr)
  if !tblWhnf.isAppOfArity ``List.cons 3 then
    return none
  let head ← whnf (tblWhnf.getArg! 1)
  let tail := tblWhnf.getArg! 2
  if !head.isAppOfArity ``Prod.mk 4 then
    return none
  let sExpr := head.getArg! 2
  let offExpr := head.getArg! 3
  let some sStr ← evalStringLit? sExpr | return none
  if sStr == nameStr then
    let prf := mkApp3 (mkConst ``Program.find?_name_cons_eq) nameExpr offExpr tail
    return some (some offExpr, prf)
  else
    let some (res, tailPrf) ← proveFindName? tail nameExpr nameCsExpr hName nameStr
      | return none
    let sCsExpr := toExpr sStr.toList
    let hS := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``String) (mkApp (mkConst ``String.ofList) sCsExpr)
    let hNe := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false)
    let stepEq := mkAppN (mkConst ``Program.find?_name_cons_ne)
      #[sExpr, nameExpr, sCsExpr, nameCsExpr, offExpr, tail, hS, hName, hNe]
    let prf ← mkEqTrans stepEq tailPrf
    return some (res, prf)

/-- Prove `prog.fnOff name = off` for a concrete `prog` by walking `prog.symbols` (then
    `prog.stubs`) without kernel `String.decEq` UTF-8 encoding. Returns `(off, proof)`. -/
def proveFnOffEq? (progExpr nameExpr : Expr) : MetaM (Option (Expr × Expr)) := do
  let some nameStr ← evalStringLit? nameExpr | return none
  let some (symsExpr, stubsExpr) ← extractProgTables? progExpr | return none
  let nameCsExpr := toExpr nameStr.toList
  let hName := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``String) (mkApp (mkConst ``String.ofList) nameCsExpr)
  let some (res, symPrf) ← proveFindName? symsExpr nameExpr nameCsExpr hName nameStr
    | return none
  let fnOffExpr := mkApp2 (mkConst ``Program.fnOff) progExpr nameExpr
  match res with
  | some offExpr =>
    let prf := mkAppN (mkConst ``Program.fnOff_of_symbols_find?) #[progExpr, nameExpr, offExpr, symPrf]
    return some (offExpr, ← mkExpectedTypeHint prf (← mkEq fnOffExpr offExpr))
  | none =>
    let some (some offExpr, stubPrf) ← proveFindName? stubsExpr nameExpr nameCsExpr hName nameStr
      | return none
    let prf := mkAppN (mkConst ``Program.fnOff_of_stubs_find?)
      #[progExpr, nameExpr, offExpr, symPrf, stubPrf]
    return some (offExpr, ← mkExpectedTypeHint prf (← mkEq fnOffExpr offExpr))

/-- Prove `prog.fnAddr name = prog.base + BitVec.ofNat 64 off` via `proveFnOffEq?`.
    Returns `(off, fnOffProof, fnAddrProof)`. -/
def proveFnAddrEq? (progExpr nameExpr : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some (offExpr, hOff) ← proveFnOffEq? progExpr nameExpr | return none
  let prf := mkAppN (mkConst ``Program.fnAddr_eq_of_fnOff_eq) #[progExpr, nameExpr, offExpr, hOff]
  return some (offExpr, hOff, prf)

/-- Prove `prog.hasWordsOff off hex` in a single kernel pass via `checkBytesWordsBound`. -/
def proveHasWordsOffHex? (progExpr offExpr hexExpr : Expr) : MetaM (Option Expr) := do
  let hCheck := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  return some (mkAppN (mkConst ``Program.hasWordsOff_of_check)
    #[progExpr, offExpr, hexExpr, hCheck])

/-- Prove `prog.hasCode base hex` at a concrete `base` address in a single pass via `checkBytesWordsBound`. -/
def proveHasCodeAtConcreteBase? (progExpr baseExpr hexExpr : Expr) : MetaM (Option Expr) := do
  let hCheck := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  return some (mkAppN (mkConst ``Program.hasCode_of_checkBytesWordsBound)
    #[progExpr, baseExpr, hexExpr, hCheck])

/-- Linear-time decision procedure for `CodeAt`, `FnCode.holds`, `Program.hasCodeBundle`,
    `Program.codeAt`, `Program.codeAtOff`, `Program.codeAtAddr`, and `Program.hasCode` goals. -/
partial def solveDecideCode? (goalTy : Expr) (depth : Nat := 64) : MetaM (Option Expr) := do
  if depth == 0 then return none
  let goalTy ← instantiateMVars goalTy
  if goalTy.isConstOf ``True then
    return some (mkConst ``True.intro)
  if goalTy.isAppOfArity ``And 2 then
    if let some p1 ← solveDecideCode? (goalTy.getArg! 0) (depth - 1) then
      if let some p2 ← solveDecideCode? (goalTy.getArg! 1) (depth - 1) then
        return some (← mkAppM ``And.intro #[p1, p2])
    return none
  if let some (_, lhs, rhs) := goalTy.eq? then
    if lhs.isAppOfArity ``Program.fnOff 2 then
      if let some (offExpr, prf) ← proveFnOffEq? (lhs.getArg! 0) (lhs.getArg! 1) then
        if ← isDefEq offExpr rhs then
          return some (← mkExpectedTypeHint prf goalTy)
    if lhs.isAppOfArity ``Program.fnAddr 2 then
      if let some (offExpr, _, prf) ← proveFnAddrEq? (lhs.getArg! 0) (lhs.getArg! 1) then
        let progExpr := lhs.getArg! 0
        let addrExpr ← mkAppM ``HAdd.hAdd
          #[mkApp (mkConst ``Program.base) progExpr, ← mkAppM ``BitVec.ofNat #[toExpr 64, offExpr]]
        if ← isDefEq addrExpr rhs then
          return some (← mkExpectedTypeHint prf goalTy)
    return none
  if goalTy.isAppOfArity ``Program.codeAt 3 then
    let progExpr := goalTy.getArg! 0
    let nameExpr := goalTy.getArg! 1
    let hexExpr := goalTy.getArg! 2
    if let some (offExpr, hOff) ← proveFnOffEq? progExpr nameExpr then
      if let some hCode ← proveHasWordsOffHex? progExpr offExpr hexExpr then
        return some (mkAppN (mkConst ``Program.codeAt_of_fnOff_eq)
          #[progExpr, nameExpr, offExpr, hexExpr, hOff, hCode])
    return none
  if goalTy.isAppOfArity ``Program.hasCode 3 then
    let progExpr := goalTy.getArg! 0
    let baseExpr := goalTy.getArg! 1
    let hexExpr := goalTy.getArg! 2
    if baseExpr.isAppOfArity ``Program.fnAddr 2 then
      let nameExpr := baseExpr.getArg! 1
      if let some (offExpr, hOff) ← proveFnOffEq? progExpr nameExpr then
        if let some hCode ← proveHasWordsOffHex? progExpr offExpr hexExpr then
          return some (mkAppN (mkConst ``Program.hasCode_fnAddr_of_fnOff_eq)
            #[progExpr, nameExpr, offExpr, hexExpr, hOff, hCode])
    return ← proveHasCodeAtConcreteBase? progExpr baseExpr hexExpr
  if let some goalTy' ← stepUnfoldCodePred? goalTy then
    if let some prf ← solveDecideCode? goalTy' (depth - 1) then
      return some (← mkExpectedTypeHint prf goalTy)
  return none

/-- Prove a concrete `CodeAt`, `FnCode.holds`, or `Program.hasCodeBundle` goal by linear-time
    kernel decision with a fallback to `decide`. -/
elab "arm64_decide_code" : tactic => do
  let mvarId ← getMainGoal
  let solved ← mvarId.withContext do
    let goalTy ← instantiateMVars (← mvarId.getType)
    if let some prf ← solveDecideCode? goalTy then
      mvarId.assign prf
      return true
    return false
  if solved then
    replaceMainGoal []
  else
    withOptions (fun opts => maxRecDepth.set opts 200000) do
      evalTactic (← `(tactic| decide))

/-- Prove a `CodeAt`, `FnCode.holds`, `Program.hasCodeBundle`, `Program.calleesOk`, or
    `prog.fetch pc = some inst` goal by projecting from an optional bundle theorem/hypothesis `h`
    and all local hypotheses, or falling back to `arm64_decide_code` for concrete extracted programs. -/
elab "arm64_code_at" hOpt:(ppSpace colGt term)? : tactic => do
  let mvarId ← getMainGoal
  let solved ← mvarId.withContext do
    let goalTy ← instantiateMVars (← mvarId.getType)
    let mut projs : Array (Expr × Expr) := #[]
    if let some hStx := hOpt then
      let hExpr ← elabTerm hStx none
      let hTy ← inferType hExpr
      projs := projs ++ (← collectCodeProjections hExpr hTy)
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        projs := projs ++ (← collectCodeProjections decl.toExpr decl.type)
    if let some prf ← solveGoalFromCodeProjs? goalTy projs then
      mvarId.assign prf
      return true
    return false
  if !solved then
    let closedFetch ← tryCloseFetchFromHasCode
    if !closedFetch then
      evalTactic (← `(tactic| arm64_decide_code))

/-- Check whether a theorem's proof term is a direct reflexivity / definitional-unfolding proof
    (`Eq.refl`, `rfl`, `Iff.refl`, `Iff.rfl`, or `propext` of `Iff.rfl`).
    When `simp` rewrites using a `rfl`-tagged theorem on `Arm64.State`, it omits the theorem
    application from the proof term and emits `of_eq_true (eq_self _)`, forcing the kernel to
    re-check `State` equality by `O(2^N)` structure eta over the symbolic state spine. -/
partial def isRflProofBody (e : Expr) : Bool :=
  match e with
  | .lam _ _ b _ => isRflProofBody b
  | .mdata _ b => isRflProofBody b
  | .letE _ _ _ b _ => isRflProofBody b
  | _ =>
    if e.isAppOfArity ``id 2 then
      isRflProofBody (e.getArg! 1)
    else if e.isAppOf ``Eq.refl || e.isAppOf ``rfl ||
            e.isAppOf ``Iff.refl || e.isAppOf ``Iff.rfl ||
            e.isAppOf ``HEq.refl || e.isAppOf ``HEq.rfl then
      true
    else if e.isAppOfArity ``propext 3 then
      isRflProofBody (e.getArg! 2)
    else
      false

/-- Inspect the `SimpExtension` named `attrName` (e.g. `` `arm64_norm `` or `` `wp_norm ``) and return
    all registered theorems whose statement mentions `Arm64.State` and whose proof is `rfl` /
    `Iff.rfl` / definitional unfolding. -/
def findRflStateSimpLemmas (attrName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some ext ← getSimpExtension? attrName
    | throwError "findRflStateSimpLemmas: unknown simp extension `{attrName}`"
  let thms ← ext.getTheorems
  let allThms := thms.pre.values ++ thms.post.values
  let mut offenders : Array Name := #[]
  for t in allThms do
    if let .decl declName := t.origin then
      if offenders.contains declName then continue
      let some cinfo := env.find? declName | continue
      if (cinfo.type.find? (·.isConstOf ``Arm64.State)).isSome then
        let isRflVal := match cinfo.value? with
          | some v => isRflProofBody v
          | none => false
        if t.rfl || (← Lean.Meta.isRflTheorem declName) || isRflVal then
          offenders := offenders.push declName
  return offenders.qsort (fun a b => a.toString < b.toString)

/-- Verify that neither `arm64_norm` nor `wp_norm` contains any `rfl`-proved lemma mentioning
    `Arm64.State`. Throws an error listing all offending theorem names if any are found. -/
def checkNoRflStateSimpLemmas : MetaM Unit := do
  let mut msgs : Array String := #[]
  for attrName in #[`arm64_norm, `wp_norm] do
    let bad ← findRflStateSimpLemmas attrName
    for nm in bad do
      msgs := msgs.push s!"  [{attrName}] {nm}"
  if !msgs.isEmpty then
    let listStr := String.intercalate "\n" msgs.toList
    throwError "Found `rfl`-proved `Arm64.State` lemmas in normalization simp sets \
      (these cause O(2^N) kernel structure-eta blowups; prove them with `by cases s; rfl` or \
      field lemmas instead):\n{listStr}"

/-- Command that fails at elaboration time if any theorem in `arm64_norm` or `wp_norm` whose
    type mentions `Arm64.State` is proved by `rfl` / `Iff.rfl`. -/
elab "#arm64_check_no_rfl_state_lemmas" : command =>
  Command.liftTermElabM checkNoRflStateSimpLemmas

end

end ProofLib

