/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.SymWP.InsnSteps
import Arm64.Trusted.Spec.SepLogic

/-!
# `SymM`-Based Symbolic Execution Engine

Hash-consed `SymM` symbolic execution engine and tactic driver (`wp_sym_step`, `wp_sym_steps`,
`wp_sym_steps_to_call`, `wp_sym_steps_to_ret`, `wp_sym_steps_to_insn`, `wp_clear_temps`) for
`SepWP`. Shares `State` update spines via `Sym.shareCommon` and memoizes `Sym.Simp` normalization
across an entire basic block in `WpSymBlockState`; per-instruction step rules live in
`ProofLib/SepLogic/SymWP/InsnSteps.lean`.
-/

public meta section

namespace ProofLib

open Lean Elab Tactic Meta
open Arm64

-- `set_option trace.proofLib.symStep.fallback true` reports every instruction that
-- `wp_sym_step` / `wp_sym_steps` steps with the slower `wpStepCoreWithOutcome` instead of a
-- `SymM` fast path, with the reason.
initialize registerTraceClass `proofLib.symStep.fallback

/-! ## Expression Preprocessing and Cached Instruction Body Templates -/

private def tryUnfoldArm64Head? (e : Expr) : MetaM (Option Expr) := do
  if let .letE _ _ v b _ := e then
    return some (b.instantiate1 v)
  if let .proj typeName i structExpr := e then
    if typeName != ``Arm64.State then
      if let some v ← projectCore? structExpr i then
        return some v
  if let .const fnName _ := e.getAppFn then
    if e.isAppOfArity ``Int64.toBitVec 1 then
      if (e.getArg! 0).isAppOfArity ``Int64.ofBitVec 1 then
        return some ((e.getArg! 0).getArg! 0)
      if !e.hasFVar && !e.hasLooseBVars then
        if let some (64, v) ← evalBitVecLit? e then
          return some (toExpr (BitVec.ofNat 64 v))
    if e.isAppOfArity ``BitVec.ofFin 2 && !e.hasFVar && !e.hasLooseBVars then
      if let some (w, v) ← evalBitVecLit? e then
        return some (toExpr (BitVec.ofNat w v))
    if e.isAppOfArity ``ite 5 then
      let c := e.getArg! 1
      if !c.hasFVar && !c.hasLooseBVars then
        let inst ← whnf (e.getArg! 2)
        if inst.isAppOfArity ``Decidable.isTrue 2 then
          return some (e.getArg! 3)
        if inst.isAppOfArity ``Decidable.isFalse 2 then
          return some (e.getArg! 4)
        let dec ← whnf (mkApp2 (mkConst ``Decidable.decide) c inst)
        if dec.isConstOf ``Bool.true then
          return some (e.getArg! 3)
        if dec.isConstOf ``Bool.false then
          return some (e.getArg! 4)
      return none
    if fnName == ``Reg.gpr || fnName == ``Reg.fromZRBits || fnName == ``Reg.fromSPBits then
      if let some rk := evalRegKindPure? e then
        let target := canonRegExpr rk
        if target != e then return some target
      return none
    if !e.hasFVar && !e.hasLooseBVars then
      if fnName == ``HMod.hMod || fnName == ``HSub.hSub || fnName == ``HAdd.hAdd ||
         fnName == ``HMul.hMul || fnName == ``Nat.shiftLeft || fnName == ``Nat.sub ||
         fnName == ``Nat.add || fnName == ``Nat.mod then
        if (← inferType e).isConstOf ``Nat then
          let e' ← whnf e
          if let .lit (.natVal n) := e' then
            return some (mkNatLit n)
      if e.isAppOfArity ``BitVec.ofNat 2 then
        let wExpr := e.getArg! 0
        let nExpr := e.getArg! 1
        if (evalNatLitPure? nExpr).isNone then
          if let some w := evalNatLitPure? wExpr then
            let nWhnf ← whnf nExpr
            if let .lit (.natVal n) := nWhnf then
              return some (toExpr (BitVec.ofNat w n))
    if (← getMatcherInfo? fnName).isSome then
      if let .reduced e' ← reduceMatcher? e then
        return some e'
      if let some e' ← reduceRecMatcher? e then
        return some e'
      return none
    if isUnfoldableArm64Eval fnName then
      if let some u ← unfoldDefinition? e (ignoreTransparency := true) then
        if let .const uFn _ := u.getAppFn then
          if (← getMatcherInfo? uFn).isSome then
            if let .reduced u' ← reduceMatcher? u then
              return some u'
            if let some u' ← reduceRecMatcher? u then
              return some u'
            return none
        return some u
    let env ← getEnv
    if let some projInfo := env.getProjectionFnInfo? fnName then
      if projInfo.ctorName != ``Arm64.State.mk && e.getAppNumArgs == projInfo.numParams + 1 then
        let major := e.getArg! projInfo.numParams
        if major.isAppOf projInfo.ctorName then
          if let some (.ctorInfo cval) := env.find? projInfo.ctorName then
            if major.getAppNumArgs == cval.numParams + cval.numFields && projInfo.i < cval.numFields then
              return some (major.getArg! (cval.numParams + projInfo.i))
  return none

/-- Reduce raw `.proj` nodes and structure projection functions (`env.getProjectionFnInfo?`)
    applied to constructor applications (excluding `State.mk`) in a single bottom-up pass. -/
def reduceCtorProjs (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Core.transform e (post := fun sub => do
    if let .proj _ i structExpr := sub then
      if let .const ctorName _ := structExpr.getAppFn then
        if ctorName != ``Arm64.State.mk then
          if let some (.ctorInfo cval) := env.find? ctorName then
            if structExpr.getAppNumArgs == cval.numParams + cval.numFields && i < cval.numFields then
              return .done (structExpr.getArg! (cval.numParams + i))
    if let .const fnName _ := sub.getAppFn then
      if let some projInfo := env.getProjectionFnInfo? fnName then
        if projInfo.ctorName != ``Arm64.State.mk && sub.getAppNumArgs == projInfo.numParams + 1 then
          let major := sub.getArg! projInfo.numParams
          if major.isAppOf projInfo.ctorName then
            if let some (.ctorInfo cval) := env.find? projInfo.ctorName then
              if major.getAppNumArgs == cval.numParams + cval.numFields && projInfo.i < cval.numFields then
                return .done (major.getArg! (cval.numParams + projInfo.i))
    return .continue)

/-- Normalize an expression for `SymM` by unfolding `isUnfoldableArm64Eval` and `@[reducible]`
    definitions, reducing matchers, zeta-reducing `let` bindings, reducing constructor projections,
    and folding remaining `.proj` nodes into projection function applications. -/
def preprocessForSym (e : Expr) : MetaM Expr := do
  let e1 ← Meta.transform e
    (pre := fun sub => do
      if let some sub' ← tryUnfoldArm64Head? sub then
        return .visit sub'
      return .continue)
    (post := fun sub => do
      if let some sub' ← tryUnfoldArm64Head? sub then
        return .visit sub'
      return .continue)
  Sym.foldProjs (← reduceCtorProjs (← zetaReduce (← Sym.unfoldReducible e1)))

/-- Cross-declaration cache mapping a decoded `instExpr : Instr` to the preprocessed body of
    `execInst instExpr _s` with `_s : State` abstracted as `.bvar 0`. Entries are small ground
    templates shared by every declaration that steps the same instruction; `lean_mark_mt` on
    insertion only visits the newly inserted (not yet multi-threaded) subgraph. -/
initialize execInstBodyCacheRef : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}

/-- Cross-declaration cache mapping an `amExpr : AddrMode` to the preprocessed body of
    `evalAddrMode _s amExpr` with `_s : State` abstracted as `.bvar 0`. -/
initialize evalAddrModeBodyCacheRef : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}

/-- Get or build the preprocessed `execInst instExpr _s` body abstracted over `_s : State`
    (`_s` is `.bvar 0`). -/
def getOrBuildExecInstBody (instExpr : Expr) : MetaM Expr := do
  if let some bodyAbst := (← execInstBodyCacheRef.get).get? instExpr then
    return bodyAbst
  let bodyAbst ← withLocalDeclD `_s (mkConst ``Arm64.State) fun sFVar => do
    let raw := mkApp2 (mkConst ``Arm64.execInst) instExpr sFVar
    let clean ← preprocessForSym raw
    return clean.abstract #[sFVar]
  execInstBodyCacheRef.modify (·.insert instExpr bodyAbst)
  return bodyAbst

/-- Get or build the preprocessed `evalAddrMode _s amExpr` body abstracted over `_s : State`
    (`_s` is `.bvar 0`). -/
def getOrBuildEvalAddrModeBody (amExpr : Expr) : MetaM Expr := do
  if let some bodyAbst := (← evalAddrModeBodyCacheRef.get).get? amExpr then
    return bodyAbst
  let bodyAbst ← withLocalDeclD `_s (mkConst ``Arm64.State) fun sFVar => do
    let raw := mkApp2 (mkConst ``Arm64.evalAddrMode) sFVar amExpr
    let clean ← preprocessForSym raw
    return clean.abstract #[sFVar]
  evalAddrModeBodyCacheRef.modify (·.insert amExpr bodyAbst)
  return bodyAbst

/-- Compile a declaration into a `Sym.Simp.Theorem`, unfolding `@[reducible]` definitions,
    zeta-reducing `let` bindings, reducing constructor projections, and folding raw `.proj` nodes
    on `thm.rhs` so `Theorem.rewrite` always produces clean `Sym`-compatible expressions. -/
def mkSymTheoremFromDecl? (declName : Name) : MetaM (Option Sym.Simp.Theorem) := do
  try
    let thm ← Sym.Simp.mkTheoremFromDecl declName
    let rhsAbst ← forallTelescopeReducing (← inferType thm.expr) fun xs _ => do
      let rhsOpen := thm.rhs.instantiateRev xs
      let rhsClean ← Sym.foldProjs (← reduceCtorProjs (← zetaReduce (← Sym.unfoldReducible rhsOpen)))
      return rhsClean.abstract xs
    return some { thm with rhs := rhsAbst }
  catch _ =>
    return none

/-- Compile a local hypothesis expression `hExpr` into a `Sym.Simp.Theorem`. -/
def mkSymTheoremFromLocalExpr? (hExpr : Expr) : MetaM (Option Sym.Simp.Theorem) := do
  try
    let thm ← Sym.Simp.mkTheoremFromExpr hExpr
    let rhsAbst ← forallTelescopeReducing (← inferType thm.expr) fun xs _ => do
      let rhsOpen := thm.rhs.instantiateRev xs
      let rhsClean ← Sym.foldProjs (← reduceCtorProjs (← zetaReduce (← Sym.unfoldReducible rhsOpen)))
      return rhsClean.abstract xs
    return some { thm with rhs := rhsAbst }
  catch _ =>
    return none

/-- Build the `Sym.Simp.Theorems` for `symWPRewriteDecls` in `MetaM`. -/
def buildSymWPTheorems : MetaM Sym.Simp.Theorems := do
  let mut thms : Sym.Simp.Theorems := {}
  for r in symWPRewriteDecls do
    if let some thm ← mkSymTheoremFromDecl? r then
      thms := thms.insert thm
  return thms

elab "init_sym_wp_theorems" : command => do
  let thms ← Command.liftTermElabM buildSymWPTheorems
  modifyEnv fun env => symWPTheoremsExt.addEntry env thms

init_sym_wp_theorems

/-- Get or build the pre-compiled `Sym.Simp.Theorems` for ARM64 instruction execution and state normalization. -/
def getOrBuildSymWPTheorems : MetaM Sym.Simp.Theorems := do
  if let some thms := symWPTheoremsExt.getState (← getEnv) then
    return thms
  buildSymWPTheorems

/-! ## `Sym.Simp` State-Spine and Bitvector Simprocs -/

/-- `Simproc` in `Sym.Simp` that zeta-reduces `.letE` expressions via `Sym.instantiateRevS`,
    reduces structure projection functions applied to constructors (excluding `State.mk`), and
    unfolds `@[reducible]` ARM64 helpers once their constructor arguments are exposed. -/
def symZetaAndProj : Sym.Simp.Simproc := fun e => do
  if e.isHeadBetaTarget then
    let e' ← Sym.shareCommon e.headBeta
    if Sym.isSameExpr e e' then return .rfl false
    let ty ← inferType e
    let u ← getLevel ty
    let eqTy ← mkEq e e'
    let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (mkApp2 (mkConst ``Eq.refl [u]) ty e')
    return .step e' prf false
  if let .letE _ _ val body _ := e then
    let e' ← Sym.instantiateRevS body #[val]
    if Sym.isSameExpr e e' then return .rfl false
    let ty ← inferType e
    let u ← getLevel ty
    let eqTy ← mkEq e e'
    let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (mkApp2 (mkConst ``Eq.refl [u]) ty e')
    return .step e' prf false
  if let .const fnName _ := e.getAppFn then
    let env ← getEnv
    if let some projInfo := env.getProjectionFnInfo? fnName then
      if projInfo.ctorName != ``Arm64.State.mk && e.getAppNumArgs == projInfo.numParams + 1 then
        let major := e.getArg! projInfo.numParams
        if major.isAppOf projInfo.ctorName then
          if let some (.ctorInfo cval) := env.find? projInfo.ctorName then
            if major.getAppNumArgs == cval.numParams + cval.numFields && projInfo.i < cval.numFields then
              let fieldVal := major.getArg! (cval.numParams + projInfo.i)
              if Sym.isSameExpr e fieldVal then return .rfl false
              let ty ← inferType fieldVal
              let u ← getLevel ty
              let eqTy ← mkEq e fieldVal
              let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (mkApp2 (mkConst ``Eq.refl [u]) ty fieldVal)
              return .step fieldVal prf false
    if isReducibleArm64Helper fnName then
      if let some u ← tryUnfoldArm64Head? e then
        let e' ← Sym.shareCommon (← Sym.foldProjs u)
        if !Sym.isSameExpr e e' then
          let ty ← inferType e
          let uLvl ← getLevel ty
          let eqTy ← mkEq e e'
          let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (mkApp2 (mkConst ``Eq.refl [uLvl]) ty e')
          return .step e' prf false
  return .rfl false

/-- Pre-`Simproc` in `Sym.Simp` that canonicalizes `Reg` wrapper projections (`toReg`, `Reg.fromZRBits`,
    `Reg.fromSPBits`, `Reg.gpr`) in $O(1)$ without descending into `BitVec 5` subterms. -/
def symReduceRegCanon : Sym.Simp.Simproc := fun e => do
  let fn := e.getAppFn
  let isRegHead :=
    fn.isConstOf ``Reg.gpr ||
    fn.isConstOf ``Reg.fromZRBits ||
    fn.isConstOf ``Reg.fromSPBits
  if !isRegHead then return .rfl false
  let some rk := evalRegKindPure? e | return .rfl false
  let target ← Sym.shareCommon (canonRegExpr rk)
  if Sym.isSameExpr e target then
    return .rfl true
  let eqTy ← mkEq e target
  let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Reg) target)
  return .step target prf true

/-- Pre-`Simproc` in `Sym.Simp` that discards writes to `.xzr` top-down before simplifying the
    written value, canonicalizes the register argument of `State.writeReg64`, and commutes
    `State.writeReg64`, `State.writeVReg128`, `State.setPState`, and `State.orFpsr` past
    `State.setPC`, `State.setMem`, and flag updates. -/
def symReduceStateWritePre : Sym.Simp.Simproc := fun e => do
  if e.isAppOfArity ``State.writeReg 4 then
    let r := e.getArg! 2
    let some rk := evalRegKindPure? r | return .rfl false
    if rk != .xzr then return .rfl false
    let w := e.getArg! 1
    let some _ := evalRegWidthPure? w | return .rfl false
    let s := e.getArg! 0
    let val := e.getArg! 3
    let prf := mkApp5 (mkConst ``State.writeReg_of_isZeroReg) s w r val reflBoolTrueExpr
    return .step s prf false
  if e.isAppOfArity ``State.writeReg32 3 then
    let r := e.getArg! 1
    let some rk := evalRegKindPure? r | return .rfl false
    if rk != .xzr then return .rfl false
    let s := e.getArg! 0
    let val := e.getArg! 2
    let prf := mkApp4 (mkConst ``State.writeReg32_of_isZeroReg) s r val reflBoolTrueExpr
    return .step s prf false
  if e.isAppOfArity ``State.writeReg64 3 then
    let s := e.getArg! 0
    let r := e.getArg! 1
    let val := e.getArg! 2
    if let some rk := evalRegKindPure? r then
      if rk == .xzr then
        let prf := mkApp4 (mkConst ``State.writeReg64_of_isZeroReg) s r val reflBoolTrueExpr
        return .step s prf false
      let rCanon ← Sym.shareCommon (canonRegExpr rk)
      if s.isAppOfArity ``State.setPC 2 then
        let s0 := s.getArg! 0
        let pc := s.getArg! 1
        let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPC) (mkApp3 (mkConst ``State.writeReg64) s0 rCanon val) pc)
        let commPrf := mkApp4 (mkConst ``State.writeReg64_setPC) s0 pc rCanon val
        let prf ← if Sym.isSameExpr r rCanon then pure commPrf else
          let eqTy ← mkEq e e'
          pure (mkApp2 (mkConst ``id [Level.zero]) eqTy commPrf)
        return .step e' prf false
      if s.isAppOfArity ``State.setMem 2 then
        let s0 := s.getArg! 0
        let m := s.getArg! 1
        let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setMem) (mkApp3 (mkConst ``State.writeReg64) s0 rCanon val) m)
        let commPrf := mkApp4 (mkConst ``State.writeReg64_setMem) s0 m rCanon val
        let prf ← if Sym.isSameExpr r rCanon then pure commPrf else
          let eqTy ← mkEq e e'
          pure (mkApp2 (mkConst ``id [Level.zero]) eqTy commPrf)
        return .step e' prf false
      if s.isAppOfArity ``State.setPState 2 then
        let s0 := s.getArg! 0
        let ps := s.getArg! 1
        let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPState) (mkApp3 (mkConst ``State.writeReg64) s0 rCanon val) ps)
        let commPrf := mkApp4 (mkConst ``State.writeReg64_setPState) s0 ps rCanon val
        let prf ← if Sym.isSameExpr r rCanon then pure commPrf else
          let eqTy ← mkEq e e'
          pure (mkApp2 (mkConst ``id [Level.zero]) eqTy commPrf)
        return .step e' prf false
      if s.isAppOfArity ``State.orFpsr 2 then
        let s0 := s.getArg! 0
        let f := s.getArg! 1
        let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.orFpsr) (mkApp3 (mkConst ``State.writeReg64) s0 rCanon val) f)
        let commPrf := mkApp4 (mkConst ``State.writeReg64_orFpsr) s0 f rCanon val
        let prf ← if Sym.isSameExpr r rCanon then pure commPrf else
          let eqTy ← mkEq e e'
          pure (mkApp2 (mkConst ``id [Level.zero]) eqTy commPrf)
        return .step e' prf false
      if s.isAppOfArity ``State.setFpsr 2 then
        let s0 := s.getArg! 0
        let f := s.getArg! 1
        let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setFpsr) (mkApp3 (mkConst ``State.writeReg64) s0 rCanon val) f)
        let commPrf := mkApp4 (mkConst ``State.writeReg64_setFpsr) s0 f rCanon val
        let prf ← if Sym.isSameExpr r rCanon then pure commPrf else
          let eqTy ← mkEq e e'
          pure (mkApp2 (mkConst ``id [Level.zero]) eqTy commPrf)
        return .step e' prf false
      if !Sym.isSameExpr r rCanon then
        let e' ← Sym.shareCommon (mkApp3 (mkConst ``State.writeReg64) s rCanon val)
        let eqTy ← mkEq e e'
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Arm64.State) e')
        return .step e' prf false
    return .rfl false
  if e.isAppOfArity ``State.setPState 2 then
    let s := e.getArg! 0
    let ps := e.getArg! 1
    if s.isAppOfArity ``State.setPC 2 then
      let s0 := s.getArg! 0
      let pc := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPC) (mkApp2 (mkConst ``State.setPState) s0 ps) pc)
      let prf := mkApp3 (mkConst ``State.setPState_setPC) s0 pc ps
      return .step e' prf false
    if s.isAppOfArity ``State.setMem 2 then
      let s0 := s.getArg! 0
      let m := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setMem) (mkApp2 (mkConst ``State.setPState) s0 ps) m)
      let prf := mkApp3 (mkConst ``State.setPState_setMem) s0 m ps
      return .step e' prf false
    if s.isAppOfArity ``State.setPState 2 then
      let s0 := s.getArg! 0
      let ps1 := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPState) s0 ps)
      let prf := mkApp3 (mkConst ``State.setPState_setPState) s0 ps1 ps
      return .step e' prf false
    return .rfl false
  if e.isAppOfArity ``State.orFpsr 2 then
    let s := e.getArg! 0
    let f := e.getArg! 1
    if s.isAppOfArity ``State.setPC 2 then
      let s0 := s.getArg! 0
      let pc := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPC) (mkApp2 (mkConst ``State.orFpsr) s0 f) pc)
      let prf := mkApp3 (mkConst ``State.orFpsr_setPC) s0 pc f
      return .step e' prf false
    if s.isAppOfArity ``State.setMem 2 then
      let s0 := s.getArg! 0
      let m := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setMem) (mkApp2 (mkConst ``State.orFpsr) s0 f) m)
      let prf := mkApp3 (mkConst ``State.orFpsr_setMem) s0 m f
      return .step e' prf false
    if s.isAppOfArity ``State.setPState 2 then
      let s0 := s.getArg! 0
      let ps := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPState) (mkApp2 (mkConst ``State.orFpsr) s0 f) ps)
      let prf := mkApp3 (mkConst ``State.orFpsr_setPState) s0 ps f
      return .step e' prf false
    return .rfl false
  if e.isAppOfArity ``State.writeVReg128 3 then
    let s := e.getArg! 0
    let idx := e.getArg! 1
    let val := e.getArg! 2
    if s.isAppOfArity ``State.setPC 2 then
      let s0 := s.getArg! 0
      let pc := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPC) (mkApp3 (mkConst ``State.writeVReg128) s0 idx val) pc)
      let prf := mkApp4 (mkConst ``State.writeVReg128_setPC) s0 pc idx val
      return .step e' prf false
    if s.isAppOfArity ``State.setMem 2 then
      let s0 := s.getArg! 0
      let m := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setMem) (mkApp3 (mkConst ``State.writeVReg128) s0 idx val) m)
      let prf := mkApp4 (mkConst ``State.writeVReg128_setMem) s0 m idx val
      return .step e' prf false
    if s.isAppOfArity ``State.setPState 2 then
      let s0 := s.getArg! 0
      let ps := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setPState) (mkApp3 (mkConst ``State.writeVReg128) s0 idx val) ps)
      let prf := mkApp4 (mkConst ``State.writeVReg128_setPState) s0 ps idx val
      return .step e' prf false
    if s.isAppOfArity ``State.orFpsr 2 then
      let s0 := s.getArg! 0
      let f := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.orFpsr) (mkApp3 (mkConst ``State.writeVReg128) s0 idx val) f)
      let prf := mkApp4 (mkConst ``State.writeVReg128_orFpsr) s0 f idx val
      return .step e' prf false
    if s.isAppOfArity ``State.setFpsr 2 then
      let s0 := s.getArg! 0
      let f := s.getArg! 1
      let e' ← Sym.shareCommon (mkApp2 (mkConst ``State.setFpsr) (mkApp3 (mkConst ``State.writeVReg128) s0 idx val) f)
      let prf := mkApp4 (mkConst ``State.writeVReg128_setFpsr) s0 f idx val
      return .step e' prf false
    return .rfl false
  return .rfl false

private def findLocalStateReadEq? (lhsTarget : Expr) : MetaM (Option (Expr × Expr)) := do
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let ty := decl.type
      if let some (_, lhs, rhs) := ty.eq? then
        if lhs == lhsTarget then
          return some (rhs, decl.toExpr)
        if lhs.isAppOfArity ``State.readReg64 2 && lhsTarget.isAppOfArity ``State.readReg64 2 &&
           lhs.getArg! 0 == lhsTarget.getArg! 0 &&
           evalRegKindPure? (lhs.getArg! 1) == evalRegKindPure? (lhsTarget.getArg! 1) then
          return some (rhs, decl.toExpr)
        if lhs.isAppOfArity ``State.readVReg128 2 && lhsTarget.isAppOfArity ``State.readVReg128 2 &&
           lhs.getArg! 0 == lhsTarget.getArg! 0 &&
           evalBitVecLitPure? (lhs.getArg! 1) == evalBitVecLitPure? (lhsTarget.getArg! 1) then
          return some (rhs, decl.toExpr)
  return none

private partial def extractStateReadVReg128Expr (s : Expr) (idx : Nat) (idxExpr : Expr) : MetaM (Option Expr) := do
  if s.isAppOfArity ``State.writeVReg128 3 then
    let s' := s.getArg! 0
    let some (5, idx') := evalBitVecLitPure? (s.getArg! 1) | return none
    if idx == idx' then
      return some (s.getArg! 2)
    else
      return some ((← extractStateReadVReg128Expr s' idx idxExpr).getD (mkApp2 (mkConst ``State.readVReg128) s' idxExpr))
  else if s.isAppOfArity ``State.writeVReg64 3 then
    let s' := s.getArg! 0
    let some (5, idx') := evalBitVecLitPure? (s.getArg! 1) | return none
    if idx == idx' then
      return some (mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (64 : Nat)) (toExpr (128 : Nat)) (s.getArg! 2))
    else
      return some ((← extractStateReadVReg128Expr s' idx idxExpr).getD (mkApp2 (mkConst ``State.readVReg128) s' idxExpr))
  else if s.isAppOfArity ``State.writeVReg32 3 then
    let s' := s.getArg! 0
    let some (5, idx') := evalBitVecLitPure? (s.getArg! 1) | return none
    if idx == idx' then
      return some (mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (128 : Nat)) (s.getArg! 2))
    else
      return some ((← extractStateReadVReg128Expr s' idx idxExpr).getD (mkApp2 (mkConst ``State.readVReg128) s' idxExpr))
  else if s.isAppOfArity ``State.writeReg64 3 ||
          s.isAppOfArity ``State.writeReg32 3 ||
          s.isAppOfArity ``State.writeReg 4 ||
          s.isAppOfArity ``State.advancePC 1 ||
          s.isAppOfArity ``State.setPC 2 ||
          s.isAppOfArity ``State.setMem 2 ||
          s.isAppOfArity ``State.setPState 2 ||
          s.isAppOfArity ``State.setBrk 2 ||
          s.isAppOfArity ``State.setPhysMemAvail 2 ||
          s.isAppOfArity ``State.setFs 2 ||
          s.isAppOfArity ``State.nextOracle 1 ||
          s.isAppOfArity ``State.stepExclOracle 1 ||
          s.isAppOfArity ``State.stepExclLoop 1 ||
          s.isAppOfArity ``State.appendTrace 2 ||
          s.isAppOfArity ``State.setStatus 2 ||
          s.isAppOfArity ``State.setFpsr 2 ||
          s.isAppOfArity ``State.orFpsr 2 ||
          s.isAppOfArity ``ProofLib.setTpidrEl0 2 then
    let s' := s.getArg! 0
    return some ((← extractStateReadVReg128Expr s' idx idxExpr).getD (mkApp2 (mkConst ``State.readVReg128) s' idxExpr))
  else
    return none

/-- Post-`Simproc` in `Sym.Simp` that prunes shadowed `State.writeReg64` / `State.writeVReg128`
    updates and resolves `State.readReg64`, `State.readReg32`, `State.readReg`, `State.readVReg128`,
    `State.sp`, `State.pstate`, and `State.pc` in a single spine walk. -/
def symReduceStatePost : Sym.Simp.Simproc := fun e => do
  if e.isAppOfArity ``State.writeReg64 3 then
    let s := e.getArg! 0
    let r := e.getArg! 1
    let val := e.getArg! 2
    if evalRegKindPure? r == some .xzr then
      return .step s (mkApp4 (mkConst ``State.writeReg64_of_isZeroReg) s r val reflBoolTrueExpr) true
    if s.isAppOfArity ``State.writeReg64 3 && s.getArg! 1 == r then
      let s0 := s.getArg! 0
      let v1 := s.getArg! 2
      let s' ← Sym.shareCommon (mkApp3 (mkConst ``State.writeReg64) s0 r val)
      let prf := mkApp4 (mkConst ``State.writeReg64_writeReg64_same) s0 r v1 val
      return .step s' prf true
    if spineHasRegWrite s r then
      if let some (s0', prf0) ← pruneShadowedRegWrite s r val then
        let mut sCurr := s0'
        let mut prfCurr := prf0
        while spineHasRegWrite sCurr r do
          let some (sNext, prfNext) ← pruneShadowedRegWrite sCurr r val | break
          prfCurr ← mkEqTrans prfCurr prfNext
          sCurr := sNext
        let sShared ← Sym.shareCommon (mkApp3 (mkConst ``State.writeReg64) sCurr r val)
        return .step sShared prfCurr true
    return .rfl false
  if e.isAppOfArity ``State.readReg64 2 then
    let s := e.getArg! 0
    let r := e.getArg! 1
    let some rk := evalRegKindPure? r | return .rfl false
    match rk with
    | .xzr =>
      let z ← Sym.shareCommon (toExpr (0#64))
      let prf := mkApp3 (mkConst ``State.readReg64_of_isZeroReg) s r reflBoolTrueExpr
      return .step z prf true
    | .sp =>
      let (target0, hSpine) ← extractStateSPProofOrRefl s
      let hRead := mkApp5 (mkConst ``State.readReg64_of_isSp) s r target0 reflBoolTrueExpr hSpine
      if target0.isAppOfArity ``State.sp 1 && (target0.getArg! 0).isFVar then
        if let some (rhs, hLocal) ← findLocalStateReadEq? target0 then
          let rhsShared ← Sym.shareCommon (← preprocessForSym rhs)
          let hLocalCast := mkApp2 (mkConst ``id [Level.zero]) (← mkEq target0 rhsShared) hLocal
          let prf ← mkEqTrans hRead hLocalCast
          return .step rhsShared prf true
      let target ← Sym.shareCommon target0
      if Sym.isSameExpr target e then
        return .rfl true
      return .step target hRead true
    | .gpr idx =>
      let idxExpr := mkCanonBitVecLit 5 idx.toNat
      let canonReg ← Sym.shareCommon (mkApp (mkConst ``Reg.gpr) idxExpr)
      let (target0, hSpine) ← extractStateReadReg64GprProofOrRefl s idx idxExpr canonReg
      let hRead := mkApp6 (mkConst ``State.readReg64_of_isGprIdx) s r idxExpr target0 reflBoolTrueExpr hSpine
      if target0.isAppOfArity ``State.readReg64 2 && (target0.getArg! 0).isFVar then
        if let some (rhs, hLocal) ← findLocalStateReadEq? target0 then
          let rhsShared ← Sym.shareCommon (← preprocessForSym rhs)
          let hLocalCast := mkApp2 (mkConst ``id [Level.zero]) (← mkEq target0 rhsShared) hLocal
          let prf ← mkEqTrans hRead hLocalCast
          return .step rhsShared prf true
      let target ← Sym.shareCommon target0
      if Sym.isSameExpr target e then
        return .rfl true
      return .step target hRead true
  if e.isAppOfArity ``State.readReg32 2 then
    let s := e.getArg! 0
    let r := e.getArg! 1
    let some rk := evalRegKindPure? r | return .rfl false
    match rk with
    | .xzr =>
      let z ← Sym.shareCommon (toExpr (0#32))
      let prf := mkApp3 (mkConst ``State.readReg32_of_isZeroReg) s r reflBoolTrueExpr
      return .step z prf true
    | .sp =>
      let (sp0, hSpine) ← extractStateSPProofOrRefl s
      let spExpr ← Sym.shareCommon sp0
      let target ← Sym.shareCommon (mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) spExpr)
      if Sym.isSameExpr target e then return .rfl false
      let prf := mkApp5 (mkConst ``State.readReg32_of_isSp) s r spExpr reflBoolTrueExpr hSpine
      return .step target prf false
    | .gpr idx =>
      let idxExpr := mkCanonBitVecLit 5 idx.toNat
      let canonReg ← Sym.shareCommon (mkApp (mkConst ``Reg.gpr) idxExpr)
      let (val64_0, hSpine) ← extractStateReadReg64GprProofOrRefl s idx idxExpr canonReg
      let val64 ← Sym.shareCommon val64_0
      let target ← Sym.shareCommon (mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) val64)
      if Sym.isSameExpr target e then return .rfl false
      let prf := mkApp6 (mkConst ``State.readReg32_of_isGprIdx) s r idxExpr val64 reflBoolTrueExpr hSpine
      return .step target prf false
  if e.isAppOfArity ``State.readReg 3 then
    let s := e.getArg! 0
    let w := e.getArg! 1
    let r := e.getArg! 2
    let some rw := evalRegWidthPure? w | return .rfl false
    let some rk := evalRegKindPure? r | return .rfl false
    match rk with
    | .xzr =>
      let z ← Sym.shareCommon (toExpr (0#64))
      let prf := mkApp4 (mkConst ``State.readReg_of_isZeroReg) s w r reflBoolTrueExpr
      return .step z prf true
    | .sp =>
      let (spExpr, hSpine) ← extractStateSPProofOrRefl s
      let (target0, prf) := match rw with
        | .W64 =>
          (spExpr, mkApp7 (mkConst ``State.readReg_w64_of_isSp) s w r spExpr reflBoolTrueExpr reflBoolTrueExpr hSpine)
        | .W32 =>
          let trunc := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) spExpr
          let zext := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) trunc
          (zext, mkApp7 (mkConst ``State.readReg_w32_of_isSp) s w r spExpr reflBoolFalseExpr reflBoolTrueExpr hSpine)
      let target ← Sym.shareCommon target0
      if Sym.isSameExpr target e then return .rfl false
      return .step target prf false
    | .gpr idx =>
      let idxExpr := mkCanonBitVecLit 5 idx.toNat
      let canonReg ← Sym.shareCommon (mkApp (mkConst ``Reg.gpr) idxExpr)
      let (val64, hSpine) ← extractStateReadReg64GprProofOrRefl s idx idxExpr canonReg
      let (target0, prf) := match rw with
        | .W64 =>
          (val64, mkApp8 (mkConst ``State.readReg_w64_of_isGprIdx) s w r idxExpr val64 reflBoolTrueExpr reflBoolTrueExpr hSpine)
        | .W32 =>
          let trunc := mkApp3 (mkConst ``BitVec.truncate) (toExpr (64 : Nat)) (toExpr (32 : Nat)) val64
          let zext := mkApp3 (mkConst ``BitVec.zeroExtend) (toExpr (32 : Nat)) (toExpr (64 : Nat)) trunc
          (zext, mkApp8 (mkConst ``State.readReg_w32_of_isGprIdx) s w r idxExpr val64 reflBoolFalseExpr reflBoolTrueExpr hSpine)
      let target ← Sym.shareCommon target0
      if Sym.isSameExpr target e then return .rfl false
      return .step target prf false
  if e.isAppOfArity ``State.sp 1 then
    let s := e.getArg! 0
    if s.isFVar then
      if let some (rhs, hLocal) ← findLocalStateReadEq? e then
        let rhsShared ← Sym.shareCommon rhs
        if Sym.isSameExpr rhsShared e then return .rfl true
        return .step rhsShared hLocal true
      return .rfl true
    let some (target0, hSpine) ← extractStateSPProof s | return .rfl false
    if target0.isAppOfArity ``State.sp 1 && (target0.getArg! 0).isFVar then
      if let some (rhs, hLocal) ← findLocalStateReadEq? target0 then
        let rhsShared ← Sym.shareCommon rhs
        let prf ← mkEqTrans hSpine hLocal
        return .step rhsShared prf true
    let target ← Sym.shareCommon target0
    if Sym.isSameExpr target e then return .rfl true
    return .step target hSpine true
  if e.isAppOfArity ``State.pstate 1 then
    let s := e.getArg! 0
    if let some (psExpr, prf) ← extractStatePStateProof s then
      let psShared ← Sym.shareCommon psExpr
      if Sym.isSameExpr psShared e then return .rfl false
      return .step psShared prf false
    return .rfl false
  if e.isAppOfArity ``State.pc 1 then
    let s := e.getArg! 0
    if let some (pcExpr, prf) ← provePcEq? s then
      let pcShared ← Sym.shareCommon pcExpr
      if Sym.isSameExpr pcShared e then return .rfl true
      return .step pcShared prf true
    if s.isFVar then
      if let some (rhs, hLocal) ← findLocalStateReadEq? e then
        let rhsShared ← Sym.shareCommon rhs
        if Sym.isSameExpr rhsShared e then return .rfl true
        return .step rhsShared hLocal true
    return .rfl false
  if e.isAppOfArity ``State.writeVReg128 3 then
    let s := e.getArg! 0
    let idx := e.getArg! 1
    let val := e.getArg! 2
    if s.isAppOfArity ``State.writeVReg128 3 && s.getArg! 1 == idx then
      let s0 := s.getArg! 0
      let v1 := s.getArg! 2
      let s' ← Sym.shareCommon (mkApp3 (mkConst ``State.writeVReg128) s0 idx val)
      let prf := mkApp4 (mkConst ``State.writeVReg128_writeVReg128_same) s0 idx v1 val
      return .step s' prf true
    return .rfl false
  if e.isAppOfArity ``State.readVReg128 2 then
    let s := e.getArg! 0
    let idxExpr := e.getArg! 1
    let some (5, idx) := evalBitVecLitPure? idxExpr | return .rfl false
    let canonIdx := toExpr (BitVec.ofNat 5 idx)
    let valOpt ← extractStateReadVReg128Expr s idx canonIdx
    let target0 := valOpt.getD (mkApp2 (mkConst ``State.readVReg128) s canonIdx)
    if target0.isAppOfArity ``State.readVReg128 2 && (target0.getArg! 0).isFVar then
      if let some (rhs, hLocal) ← findLocalStateReadEq? target0 then
        let rhsShared ← Sym.shareCommon (← preprocessForSym rhs)
        let prf ← if valOpt.isNone then
          pure (mkApp2 (mkConst ``id [Level.zero]) (← mkEq e rhsShared) hLocal)
        else
          let eqTy ← mkEq e target0
          let hDef := mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl target0)
          let hLocalCast := mkApp2 (mkConst ``id [Level.zero]) (← mkEq target0 rhsShared) hLocal
          mkEqTrans hDef hLocalCast
        return .step rhsShared prf true
    let target ← Sym.shareCommon target0
    if Sym.isSameExpr target e then
      return .rfl true
    let eqTy ← mkEq e target
    let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl target)
    return .step target prf true
  return .rfl false

/-- Post-`Simproc` in `Sym.Simp` that folds nested 64-bit pointer/SP constant offsets
    (`(base ± c1) ± c2`) via `SepSolver.foldBV64OffsetTop?`. -/
def symReduceBV64Offsets : Sym.Simp.Simproc := fun e => do
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 then
    if let some (normExpr, prf) ← SepSolver.foldBV64OffsetTop? e then
      let normShared ← Sym.shareCommon normExpr
      if Sym.isSameExpr normShared e then return .rfl true
      return .step normShared prf true
  return .rfl false

/-- Post-`Simproc` in `Sym.Simp` that evaluates ground `BitVec`, `Nat`, `Bool`, `shiftVal`, and
    `checkAddrSPAligned` expressions in $O(1)$. -/
def symEvalGround : Sym.Simp.Simproc := fun e => do
  let fn := e.getAppFn
  let .const declName _ := fn | return .rfl false
  if declName == ``BitVec.ofNat || declName == ``OfNat.ofNat ||
     declName == ``Bool.true || declName == ``Bool.false then
    return .rfl false
  if declName == ``checkAddrSPAligned && e.getAppNumArgs == 2 then
    let bTrue := mkConst ``Bool.true
    let targetEq ← mkEq e bTrue
    if let some prf ← proveCheckAddrSPAligned? targetEq e bTrue then
      let tShared ← Sym.shareCommon bTrue
      return .step tShared prf true
    return .rfl false
  if declName == ``shiftVal && e.getAppNumArgs == 4 then
    let amtExpr := e.getArg! 3
    let vOpt : Option Nat :=
      match evalNatLitPure? amtExpr with
      | some n => some n
      | none => (evalBitVecLitPure? amtExpr).map Prod.snd
    if let some v := vOpt then
      let wExpr := e.getArg! 0
      let valExpr := e.getArg! 1
      let stExpr := e.getArg! 2
      let some rw := evalRegWidthPure? wExpr | return .rfl false
      let maxBits := match rw with | .W32 => 32 | .W64 => 64
      if v == 0 && rw == .W64 then
        let eqTy ← mkEq e valExpr
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl valExpr)
        return .step valExpr prf false
      if v >= maxBits then
        if stExpr.isConstOf ``ShiftType.LSL || stExpr.isConstOf ``ShiftType.LSR then
          let z ← Sym.shareCommon (toExpr (0#64))
          let eqTy ← mkEq e z
          let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl z)
          return .step z prf true
    return .rfl false
  if declName == ``HOr.hOr && e.getAppNumArgs == 6 then
    let a := e.getArg! 4
    let b := e.getArg! 5
    if let some (w, 0) := evalBitVecLitPure? a then
      if w == 64 || w == 32 then
        let eqTy ← mkEq e b
        let rawPrf := mkApp2 (mkConst ``BitVec.zero_or) (toExpr w) b
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy rawPrf
        return .step b prf false
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    return .rfl false
  if declName == ``BitVec.toNat && e.getAppNumArgs == 2 then
    if let some (_, v) := evalBitVecLitPure? (e.getArg! 1) then
      let lit ← Sym.shareCommon (toExpr v)
      let eqTy ← mkEq e lit
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) lit)
      return .step lit prf true
    return .rfl false
  if declName == ``HAdd.hAdd || declName == ``HSub.hSub ||
     declName == ``HMul.hMul || declName == ``HDiv.hDiv || declName == ``HMod.hMod ||
     declName == ``HAnd.hAnd || declName == ``HOr.hOr || declName == ``HXor.hXor ||
     declName == ``HShiftLeft.hShiftLeft || declName == ``HShiftRight.hShiftRight then
    if e.getAppNumArgs == 6 then
      let a := e.getArg! 4
      let b := e.getArg! 5
      if let some (w1, v1) := evalBitVecLitPure? a then
        if let some (w2, v2) := evalBitVecLitPure? b then
          if w1 == w2 then
            let m := 1 <<< w1
            let resVal : Option Nat :=
              if declName == ``HAdd.hAdd then some ((v1 + v2) % m)
              else if declName == ``HSub.hSub then some ((v1 + m - (v2 % m)) % m)
              else if declName == ``HMul.hMul then some ((v1 * v2) % m)
              else if declName == ``HDiv.hDiv then some (if v2 == 0 then 0 else v1 / v2)
              else if declName == ``HMod.hMod then some (if v2 == 0 then v1 else v1 % v2)
              else if declName == ``HAnd.hAnd then some (v1 &&& v2)
              else if declName == ``HOr.hOr then some (v1 ||| v2)
              else if declName == ``HXor.hXor then some (v1 ^^^ v2)
              else if declName == ``HShiftLeft.hShiftLeft then some ((v1 <<< v2) % m)
              else if declName == ``HShiftRight.hShiftRight then some (v1 >>> v2)
              else none
            if let some rv := resVal then
              let lit ← Sym.shareCommon (toExpr (BitVec.ofNat w1 rv))
              let eqTy ← mkEq e lit
              let bvTy := mkApp (mkConst ``BitVec) (toExpr w1)
              let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
                (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
              return .step lit prf true
      if (declName == ``HShiftLeft.hShiftLeft || declName == ``HShiftRight.hShiftRight) then
        if let some (w1, v1) := evalBitVecLitPure? a then
          if let some amt := evalNatLitPure? b then
            let m := 1 <<< w1
            let rv := if declName == ``HShiftLeft.hShiftLeft then (v1 <<< amt) % m else v1 >>> amt
            let lit ← Sym.shareCommon (toExpr (BitVec.ofNat w1 rv))
            let eqTy ← mkEq e lit
            let bvTy := mkApp (mkConst ``BitVec) (toExpr w1)
            let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
              (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
            return .step lit prf true
      if let some n1 := evalNatLitPure? a then
        if let some n2 := evalNatLitPure? b then
          let resNat : Option Nat :=
            if declName == ``HAdd.hAdd then some (n1 + n2)
            else if declName == ``HSub.hSub then some (n1 - n2)
            else if declName == ``HMul.hMul then some (n1 * n2)
            else if declName == ``HDiv.hDiv then some (n1 / n2)
            else if declName == ``HMod.hMod then some (n1 % n2)
            else if declName == ``HShiftLeft.hShiftLeft then some (n1 <<< n2)
            else if declName == ``HShiftRight.hShiftRight then some (n1 >>> n2)
            else none
          if let some rn := resNat then
            let lit ← Sym.shareCommon (toExpr rn)
            let eqTy ← mkEq e lit
            let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
              (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) lit)
            return .step lit prf true
    return .rfl false
  if declName == ``Complement.complement && e.getAppNumArgs == 3 then
    if let some (w, v) := evalBitVecLitPure? (e.getArg! 2) then
      let m := 1 <<< w
      let lit ← Sym.shareCommon (toExpr (BitVec.ofNat w ((m - 1) - (v % m))))
      let eqTy ← mkEq e lit
      let bvTy := mkApp (mkConst ``BitVec) (toExpr w)
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
      return .step lit prf true
    return .rfl false
  if declName == ``Neg.neg && e.getAppNumArgs == 3 then
    if let some (w, v) := evalBitVecLitPure? (e.getArg! 2) then
      if w == 64 && 0 < v && v <= (1 <<< 32) then
        return .rfl false
      let m := 1 <<< w
      let lit ← Sym.shareCommon (toExpr (BitVec.ofNat w ((m - (v % m)) % m)))
      let eqTy ← mkEq e lit
      let bvTy := mkApp (mkConst ``BitVec) (toExpr w)
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
      return .step lit prf true
    return .rfl false
  if (declName == ``BitVec.zeroExtend || declName == ``BitVec.truncate ||
      declName == ``BitVec.setWidth || declName == ``BitVec.signExtend) && e.getAppNumArgs == 3 then
    if let some wOut := evalNatLitPure? (e.getArg! 1) then
      if let some (wIn, v) := evalBitVecLitPure? (e.getArg! 2) then
        let rv :=
          if declName == ``BitVec.signExtend then
            (BitVec.ofNat wIn v).signExtend wOut |>.toNat
          else
            v % (1 <<< wOut)
        let lit ← Sym.shareCommon (toExpr (BitVec.ofNat wOut rv))
        let eqTy ← mkEq e lit
        let bvTy := mkApp (mkConst ``BitVec) (toExpr wOut)
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
        return .step lit prf true
    return .rfl false
  if declName == ``BitVec.extractLsb' && e.getAppNumArgs == 4 then
    if let some start := evalNatLitPure? (e.getArg! 1) then
      if let some len := evalNatLitPure? (e.getArg! 2) then
        if let some (_, v) := evalBitVecLitPure? (e.getArg! 3) then
          let rv := (v >>> start) % (1 <<< len)
          let lit ← Sym.shareCommon (toExpr (BitVec.ofNat len rv))
          let eqTy ← mkEq e lit
          let bvTy := mkApp (mkConst ``BitVec) (toExpr len)
          let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
            (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
          return .step lit prf true
    return .rfl false
  if (declName == ``BEq.beq || declName == ``bne) && e.getAppNumArgs == 4 then
    let a := e.getArg! 2
    let b := e.getArg! 3
    if let some (w1, v1) := evalBitVecLitPure? a then
      if let some (w2, v2) := evalBitVecLitPure? b then
        if w1 == w2 then
          let isEq := if declName == ``BEq.beq then (v1 == v2) else (v1 != v2)
          let bExpr ← Sym.shareCommon (toExpr isEq)
          let eqTy ← mkEq e bExpr
          let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
            (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) bExpr)
          return .step bExpr prf true
    return .rfl false
  if (declName == ``BitVec.ult || declName == ``BitVec.ule ||
      declName == ``BitVec.slt || declName == ``BitVec.sle) && e.getAppNumArgs == 3 then
    let a := e.getArg! 1
    let b := e.getArg! 2
    if let some (w1, v1) := evalBitVecLitPure? a then
      if let some (w2, v2) := evalBitVecLitPure? b then
        if w1 == w2 then
          let bv1 := BitVec.ofNat w1 v1
          let bv2 := BitVec.ofNat w1 v2
          let resBool :=
            if declName == ``BitVec.ult then bv1.ult bv2
            else if declName == ``BitVec.ule then bv1.ule bv2
            else if declName == ``BitVec.slt then bv1.slt bv2
            else bv1.sle bv2
          let bExpr ← Sym.shareCommon (toExpr resBool)
          let eqTy ← mkEq e bExpr
          let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
            (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) bExpr)
          return .step bExpr prf true
    return .rfl false
  if (declName == ``BitVec.sshiftRight || declName == ``BitVec.rotateRight) && e.getAppNumArgs == 3 then
    if let some (w, v) := evalBitVecLitPure? (e.getArg! 1) then
      if let some amt := evalNatLitPure? (e.getArg! 2) then
        let bvIn := BitVec.ofNat w v
        let bvOut :=
          if declName == ``BitVec.sshiftRight then bvIn.sshiftRight amt
          else bvIn.rotateRight amt
        let lit ← Sym.shareCommon (toExpr bvOut)
        let eqTy ← mkEq e lit
        let bvTy := mkApp (mkConst ``BitVec) (toExpr w)
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
        return .step lit prf true
    return .rfl false
  if declName == ``BitVec.sdiv && e.getAppNumArgs == 3 then
    if let some (w1, v1) := evalBitVecLitPure? (e.getArg! 1) then
      if let some (w2, v2) := evalBitVecLitPure? (e.getArg! 2) then
        if w1 == w2 then
          let bvOut := BitVec.sdiv (BitVec.ofNat w1 v1) (BitVec.ofNat w1 v2)
          let lit ← Sym.shareCommon (toExpr bvOut)
          let eqTy ← mkEq e lit
          let bvTy := mkApp (mkConst ``BitVec) (toExpr w1)
          let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
            (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
          return .step lit prf true
    return .rfl false
  if declName == ``HAppend.hAppend && e.getAppNumArgs == 6 then
    if let some (w1, v1) := evalBitVecLitPure? (e.getArg! 4) then
      if let some (w2, v2) := evalBitVecLitPure? (e.getArg! 5) then
        let wOut := w1 + w2
        let rv := ((v1 <<< w2) ||| v2) % (1 <<< wOut)
        let lit ← Sym.shareCommon (toExpr (BitVec.ofNat wOut rv))
        let eqTy ← mkEq e lit
        let bvTy := mkApp (mkConst ``BitVec) (toExpr wOut)
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
        return .step lit prf true
    return .rfl false
  if declName == ``reverseBits && e.getAppNumArgs == 2 then
    if let some (w, v) := evalBitVecLitPure? (e.getArg! 1) then
      let bvOut := reverseBits (BitVec.ofNat w v)
      let lit ← Sym.shareCommon (toExpr bvOut)
      let eqTy ← mkEq e lit
      let bvTy := mkApp (mkConst ``BitVec) (toExpr w)
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
      return .step lit prf true
    return .rfl false
  if (declName == ``rev16_64 || declName == ``rev32_64 || declName == ``rev64) && e.getAppNumArgs == 1 then
    if let some (64, v) := evalBitVecLitPure? (e.getArg! 0) then
      let bvIn := BitVec.ofNat 64 v
      let bvOut :=
        if declName == ``rev16_64 then rev16_64 bvIn
        else if declName == ``rev32_64 then rev32_64 bvIn
        else rev64 bvIn
      let lit ← Sym.shareCommon (toExpr bvOut)
      let eqTy ← mkEq e lit
      let bvTy := mkApp (mkConst ``BitVec) (toExpr 64)
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) bvTy lit)
      return .step lit prf true
    return .rfl false
  if (declName == ``countLeadingZeros || declName == ``countLeadingSigns) && e.getAppNumArgs == 2 then
    if let some (w, v) := evalBitVecLitPure? (e.getArg! 1) then
      let bvIn := BitVec.ofNat w v
      let rn :=
        if declName == ``countLeadingZeros then countLeadingZeros bvIn
        else countLeadingSigns bvIn
      let lit ← Sym.shareCommon (toExpr rn)
      let eqTy ← mkEq e lit
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) lit)
      return .step lit prf true
    return .rfl false
  if (declName == ``addsPState64 || declName == ``subsPState64) && e.getAppNumArgs == 2 then
    if let some (64, v1) := evalBitVecLitPure? (e.getArg! 0) then
      if let some (64, v2) := evalBitVecLitPure? (e.getArg! 1) then
        let bv1 := BitVec.ofNat 64 v1
        let bv2 := BitVec.ofNat 64 v2
        let ps := if declName == ``addsPState64 then (AddWithCarry64 bv1 bv2 false).2 else (AddWithCarry64 bv1 (~~~bv2) true).2
        let psExpr ← Sym.shareCommon (mkApp4 (mkConst ``PState.mk) (toExpr ps.n) (toExpr ps.z) (toExpr ps.c) (toExpr ps.v))
        let eqTy ← mkEq e psExpr
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``PState) psExpr)
        return .step psExpr prf true
    return .rfl false
  if (declName == ``addsPState32 || declName == ``subsPState32) && e.getAppNumArgs == 2 then
    if let some (32, v1) := evalBitVecLitPure? (e.getArg! 0) then
      if let some (32, v2) := evalBitVecLitPure? (e.getArg! 1) then
        let bv1 := BitVec.ofNat 32 v1
        let bv2 := BitVec.ofNat 32 v2
        let ps := if declName == ``addsPState32 then (AddWithCarry32 bv1 bv2 false).2 else (AddWithCarry32 bv1 (~~~bv2) true).2
        let psExpr ← Sym.shareCommon (mkApp4 (mkConst ``PState.mk) (toExpr ps.n) (toExpr ps.z) (toExpr ps.c) (toExpr ps.v))
        let eqTy ← mkEq e psExpr
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``PState) psExpr)
        return .step psExpr prf true
    return .rfl false
  if (declName == ``AddWithCarry64 || declName == ``AddWithCarry32) && e.getAppNumArgs == 3 then
    let cExpr := e.getArg! 2
    if cExpr.isConstOf ``Bool.true || cExpr.isConstOf ``Bool.false then
      let cBool := cExpr.isConstOf ``Bool.true
      if declName == ``AddWithCarry64 then
        if let some (64, v1) := evalBitVecLitPure? (e.getArg! 0) then
          if let some (64, v2) := evalBitVecLitPure? (e.getArg! 1) then
            let (res, ps) := AddWithCarry64 (BitVec.ofNat 64 v1) (BitVec.ofNat 64 v2) cBool
            let psExpr := mkApp4 (mkConst ``PState.mk) (toExpr ps.n) (toExpr ps.z) (toExpr ps.c) (toExpr ps.v)
            let bvTy := mkApp (mkConst ``BitVec) (toExpr 64)
            let pairExpr ← Sym.shareCommon (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) bvTy (mkConst ``PState) (toExpr res) psExpr)
            let eqTy ← mkEq e pairExpr
            let prodTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) bvTy (mkConst ``PState)
            let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
              (mkApp2 (mkConst ``Eq.refl [Level.one]) prodTy pairExpr)
            return .step pairExpr prf true
      else
        if let some (32, v1) := evalBitVecLitPure? (e.getArg! 0) then
          if let some (32, v2) := evalBitVecLitPure? (e.getArg! 1) then
            let (res, ps) := AddWithCarry32 (BitVec.ofNat 32 v1) (BitVec.ofNat 32 v2) cBool
            let psExpr := mkApp4 (mkConst ``PState.mk) (toExpr ps.n) (toExpr ps.z) (toExpr ps.c) (toExpr ps.v)
            let bvTy := mkApp (mkConst ``BitVec) (toExpr 32)
            let pairExpr ← Sym.shareCommon (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) bvTy (mkConst ``PState) (toExpr res) psExpr)
            let eqTy ← mkEq e pairExpr
            let prodTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) bvTy (mkConst ``PState)
            let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
              (mkApp2 (mkConst ``Eq.refl [Level.one]) prodTy pairExpr)
            return .step pairExpr prf true
    return .rfl false
  if (declName == ``PState.n || declName == ``PState.z ||
      declName == ``PState.c || declName == ``PState.v) && e.getAppNumArgs == 1 then
    let ps := e.getArg! 0
    if ps.isAppOfArity ``PState.mk 4 then
      let bExpr :=
        if declName == ``PState.n then ps.getArg! 0
        else if declName == ``PState.z then ps.getArg! 1
        else if declName == ``PState.c then ps.getArg! 2
        else ps.getArg! 3
      if bExpr.isConstOf ``Bool.true || bExpr.isConstOf ``Bool.false then
        let bShared ← Sym.shareCommon bExpr
        let eqTy ← mkEq e bShared
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) bShared)
        return .step bShared prf true
    return .rfl false
  if declName == ``BitVec.msb && e.getAppNumArgs == 2 then
    if let some (w, v) := evalBitVecLitPure? (e.getArg! 1) then
      let resBool := w > 0 && (((v >>> (w - 1)) &&& 1) == 1)
      let bExpr ← Sym.shareCommon (toExpr resBool)
      let eqTy ← mkEq e bExpr
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
        (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) bExpr)
      return .step bExpr prf true
    return .rfl false
  if declName == ``BitVec.getLsbD && e.getAppNumArgs == 3 then
    if let some (w, v) := evalBitVecLitPure? (e.getArg! 1) then
      if let some idx := evalNatLitPure? (e.getArg! 2) then
        let resBool := idx < w && (((v >>> idx) &&& 1) == 1)
        let bExpr ← Sym.shareCommon (toExpr resBool)
        let eqTy ← mkEq e bExpr
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) bExpr)
        return .step bExpr prf true
    return .rfl false
  if declName == ``ConditionHolds && e.getAppNumArgs == 2 then
    let ps := e.getArg! 1
    if ps.isAppOfArity ``PState.mk 4 then
      let nE := ps.getArg! 0
      let zE := ps.getArg! 1
      let cE := ps.getArg! 2
      let vE := ps.getArg! 3
      let isBoolConst (b : Expr) : Bool := b.isConstOf ``Bool.true || b.isConstOf ``Bool.false
      if isBoolConst nE && isBoolConst zE && isBoolConst cE && isBoolConst vE then
        let eWhnf ← whnfD e
        if isBoolConst eWhnf then
          let bExpr ← Sym.shareCommon eWhnf
          let eqTy ← mkEq e bExpr
          let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
            (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) bExpr)
          return .step bExpr prf true
    return .rfl false
  return .rfl false

/-! ## `SymM` Basic-Block Cache and Expression Simplifier -/

/-- Seed normalized `State` spine prefixes and register values into `Sym.Simp.Cache`
    (`persistentCache`) so subsequent `Sym.Simp` calls hit `persistentCache` in $O(1)$
    via pointer identity (`ExprPtr`). -/
partial def seedNormalizedInSymCache (e : Expr) (cache : Sym.Simp.Cache) : Sym.Simp.Cache :=
  if e.hasMVar || cache.contains { expr := e } then
    cache
  else
    let cache := cache.insert { expr := e } (Sym.Simp.Result.rfl true)
    if e.isAppOfArity ``State.setMem 2 then
      seedNormalizedInSymCache (e.getArg! 0) cache
    else if e.isAppOfArity ``State.setPC 2 then
      let cache := seedNormalizedInSymCache (e.getArg! 1) cache
      seedNormalizedInSymCache (e.getArg! 0) cache
    else if e.isAppOfArity ``State.setPState 2 then
      let cache := seedNormalizedInSymCache (e.getArg! 1) cache
      seedNormalizedInSymCache (e.getArg! 0) cache
    else if e.isAppOfArity ``State.writeReg64 3 || e.isAppOfArity ``State.writeVReg128 3 then
      let cache := seedNormalizedInSymCache (e.getArg! 2) cache
      seedNormalizedInSymCache (e.getArg! 0) cache
    else if e.isAppOfArity ``Prod.mk 4 then
      let cache := seedNormalizedInSymCache (e.getArg! 2) cache
      seedNormalizedInSymCache (e.getArg! 3) cache
    else
      cache

/-- Like `Sym.Simp.simpControl`, except when an `ite` or `cond` condition does not resolve
    to a boolean constant, also simplifies the `then` and `else` branches non-contextually
    (via `Sym.Simp.simpFixedPrefix`) so register reads inside `CSEL`/`CSINC`/`CSINV`/`CSNEG`
    branches are reduced. -/
def symSimpControl : Sym.Simp.Simproc := fun e => do
  if !e.isApp then return .rfl
  let .const declName _ := e.getAppFn | return .rfl
  if declName == ``ite && e.getAppNumArgs == 5 then
    match ← Sym.Simp.simpControl e with
    | .rfl _ cd =>
      let r₂ ← Sym.Simp.simpFixedPrefix e 3 2
      return (if cd && !r₂.isContextDependent then r₂.withContextDependent else r₂).markAsDone
    | .step e' h done cd =>
      if !done then
        return .step e' h false cd
      else
        return (← Sym.Simp.mkEqTransResult e e' h (← Sym.Simp.simpFixedPrefix e' 3 2) cd).markAsDone
  else if declName == ``cond && e.getAppNumArgs == 4 then
    match ← Sym.Simp.simpControl e with
    | .rfl _ cd =>
      let r₂ ← Sym.Simp.simpFixedPrefix e 2 2
      return (if cd && !r₂.isContextDependent then r₂.withContextDependent else r₂).markAsDone
    | .step e' h done cd =>
      if !done then
        return .step e' h false cd
      else
        return (← Sym.Simp.mkEqTransResult e e' h (← Sym.Simp.simpFixedPrefix e' 2 2) cd).markAsDone
  else
    Sym.Simp.simpControl e

/-- Build the `Sym.Simp.Methods` combining pre-compiled `Sym.Simp.Theorems`, local hypothesis
    rewrite rules, `symSimpControl` (`simpIte`, `simpCond`, `simpMatch`), `Sym.Simp.evalGround`,
    and custom ARM64 `Sym.Simp.Simproc`s. -/
def mkSymWPMethods (baseThms : Sym.Simp.Theorems) (localThms : Sym.Simp.Theorems) : Sym.Simp.Methods :=
  let pre : Sym.Simp.Simproc :=
    symZetaAndProj >> symReduceRegCanon >> symReduceStateWritePre >> symSimpControl
  let post : Sym.Simp.Simproc :=
    symZetaAndProj >> symSimpControl >> symReduceStatePost >>
    baseThms.rewrite >> localThms.rewrite >>
    symReduceBV64Offsets >> symEvalGround >> Sym.Simp.evalGround
  { pre, post }

/-- Collect lightweight local equality hypotheses (`lhs = rhs`, excluding `s0.pc = _`, `s0.status = _`,
    and heavy spatial/code hypotheses) as `Sym.Simp.Theorems`. -/
def buildLocalSymTheorems : MetaM Sym.Simp.Theorems := do
  let mut thms : Sym.Simp.Theorems := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let ty ← instantiateMVars decl.type
      if !isHeavyNonSimpHyp ty then
        if let some (_, lhs, _) := ty.eq? then
          if !lhs.isAppOf ``State.pc && !lhs.isAppOf ``State.status &&
             !lhs.isAppOf ``State.spAligned then
            if let some thm ← mkSymTheoremFromLocalExpr? decl.toExpr then
              thms := thms.insert thm
  return thms

/-- Persistent `SymM` and `Sym.Simp` state threaded across all instructions in a basic block,
    retaining the `Sym.Context` shared expressions, `Sym.State` hash-consing and type/congruence
    caches, and `Sym.Simp.State.persistentCache`. -/
structure WpSymBlockState where
  symCtx           : Sym.Context
  symInternalState : Sym.State
  simpState        : Sym.Simp.State := {}

/-- Initialize a fresh `WpSymBlockState` at the start of a basic block. -/
def mkInitialWpSymBlockState : MetaM WpSymBlockState :=
  Sym.SymM.run do
    return {
      symCtx := ← readThe Sym.Context
      symInternalState := ← getThe Sym.State
      simpState := {}
    }

private partial def unfoldTopStateWrapper (e : Expr) : Expr :=
  if e.isAppOfArity ``State.setPC 2 then
    mkApp2 e.getAppFn (unfoldTopStateWrapper (e.getArg! 0)) (e.getArg! 1)
  else if e.isAppOfArity ``State.writeReg64 3 then
    let r := e.getArg! 1
    let rCanon := match evalRegKindPure? r with | some rk => canonRegExpr rk | none => r
    mkApp3 e.getAppFn (unfoldTopStateWrapper (e.getArg! 0)) rCanon (e.getArg! 2)
  else if e.isAppOfArity ``State.writeVReg128 3 then
    mkApp3 e.getAppFn (unfoldTopStateWrapper (e.getArg! 0)) (e.getArg! 1) (e.getArg! 2)
  else if e.isAppOfArity ``applyWriteback 2 then
    let s := e.getArg! 0
    let wb := e.getArg! 1
    if wb.isAppOfArity ``Option.none 1 then
      s
    else if wb.isAppOfArity ``Option.some 2 && (wb.getArg! 1).isAppOfArity ``Prod.mk 4 then
      let pair := wb.getArg! 1
      let r := pair.getArg! 2
      let rCanon := match evalRegKindPure? r with | some rk => canonRegExpr rk | none => r
      mkApp3 (mkConst ``State.writeReg64) s rCanon (pair.getArg! 3)
    else
      e
  else
    e

/-- Simplify `lhs` in `SymM` using `methods` and persistent `WpSymBlockState`, preserving the
    `AlphaShareCommon.State` hash-consing table and `Sym.Simp.State.persistentCache` across calls. -/
def symSimpExpr (lhs : Expr) (methods : Sym.Simp.Methods) (config : Sym.Simp.Config)
    (bs : WpSymBlockState) : MetaM ((Expr × Expr) × WpSymBlockState) := do
  if let some (rhsDirect, prfDirect) ← proveApplyWritebackNoneSetPCDirect? lhs then
    let (rhsShared, symInternalState') ← (Sym.withoutShareCommonChecks (Sym.shareCommon rhsDirect)) bs.symCtx |>.run bs.symInternalState
    let seeded := seedNormalizedInSymCache rhsShared bs.simpState.persistentCache
    return ((rhsShared, prfDirect), { bs with symInternalState := symInternalState', simpState := { bs.simpState with persistentCache := seeded } })
  let template? ←
    if lhs.isAppOfArity ``Arm64.execInst 2 then
      pure (some (← getOrBuildExecInstBody (lhs.getArg! 0), lhs.getArg! 1))
    else if lhs.isAppOfArity ``Arm64.evalAddrMode 2 then
      pure (some (← getOrBuildEvalAddrModeBody (lhs.getArg! 1), lhs.getArg! 0))
    else
      pure none
  let act : Sym.SymM ((Expr × Expr) × Sym.Simp.State) :=
    Sym.withoutShareCommonChecks do
      let lhsShared ←
        if let some (bodyAbst, sArg) := template? then
          let bodyShared ← Sym.shareCommon bodyAbst
          let sShared ← Sym.shareCommon sArg
          Sym.instantiateRevS bodyShared #[sShared]
        else if lhs.isAppOfArity ``State.readReg64 2 then
          let r := lhs.getArg! 1
          let rCanon := match evalRegKindPure? r with | some rk => canonRegExpr rk | none => r
          Sym.shareCommon (mkApp2 lhs.getAppFn (lhs.getArg! 0) rCanon)
        else if lhs.isAppOfArity ``State.setPC 2 then
          Sym.shareCommon (unfoldTopStateWrapper lhs)
        else
          let lhsPre ← preprocessForSym lhs
          Sym.shareCommon lhsPre
      let sInit : Sym.Simp.State := { bs.simpState with numSteps := 0 }
      let (res, sOut) ← Sym.Simp.SimpM.run (Sym.Simp.simp lhsShared)
        (methods := methods) (config := config) (s := sInit)
      match res with
      | Sym.Simp.Result.rfl .. =>
        let seeded := seedNormalizedInSymCache lhsShared sOut.persistentCache
        let ty ← inferType lhs
        let u ← getLevel ty
        let eqTy ← mkEq lhs lhsShared
        let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy
          (mkApp2 (mkConst ``Eq.refl [u]) ty lhsShared)
        return ((lhsShared, prf), { sOut with persistentCache := seeded })
      | Sym.Simp.Result.step rhs prf .. =>
        let seeded := seedNormalizedInSymCache rhs sOut.persistentCache
        let prf' ← if Sym.isSameExpr lhs lhsShared then pure prf else
          let eqTy ← mkEq lhs rhs
          pure (mkApp2 (mkConst ``id [Level.zero]) eqTy prf)
        return ((rhs, prf'), { sOut with persistentCache := seeded })
  let ((resPair, simpState'), symInternalState') ← act bs.symCtx |>.run bs.symInternalState
  return (resPair, { bs with symInternalState := symInternalState', simpState := simpState' })

/-! ## Basic-Block Step Driver and Tactic Syntax -/

/-- Take a single instruction step in `SymM`, dispatching via `classifyInsnStepRule` (defined in
    `ProofLib.SepLogic.SymWP.InsnSteps`) to `symStepPureInsn?`, `symStepLdr64Insn?`,
    `symStepStr64Insn?`, or `wpStepCoreWithOutcome`. -/
def wpSymStepInBlock (methods : Sym.Simp.Methods) (config : Sym.Simp.Config)
    (bs : WpSymBlockState) (inStepLoop : Bool := false)
    (resolvedItePcRef : Option (IO.Ref (Option Expr)) := none) :
    TacticM (WpStepOutcome × WpSymBlockState) := do
  let _ ← getOrCreateWpNormSimpCacheRef
  let (_, _, pcExpr0) ← getSepWPStateAndPC
  if (iteApp? pcExpr0).isSome then
    trace[proofLib.symStep.fallback]
      m!"conditional PC (`ite`): stepping with wpStepCoreWithOutcome at PC {pcExpr0}"
    let out ← wpStepCoreWithOutcome (tacticName := "wp_sym_step") (isSingleStep := !inStepLoop)
      (resolvedItePcRef := resolvedItePcRef)
    return (out, bs)
  let (progExpr, _targetPcExpr, pcExpr) ← getSepWPStateAndPC
  if (iteApp? pcExpr).isSome then
    throwUnresolvedBranchStepError "wp_sym_step" pcExpr
  let g0 ← getMainGoal
  let savedFetch ← saveState
  let fetchResOpt : Option (Expr × Expr) ← g0.withContext do
    let savedGoals ← getGoals
    let instMVar ← mkFreshExprMVar (mkConst ``Instr)
    let someInst ← mkAppM ``Option.some #[instMVar]
    let fetchLhs := mkApp2 (mkConst ``Program.fetch) progExpr pcExpr
    let fetchGoalTy ← mkEq fetchLhs someInst
    let fetchGoal ← mkFreshExprMVar fetchGoalTy
    setGoals [fetchGoal.mvarId!]
    -- Each fallback sits in its own `else do` block so it only runs when the previous ones failed
    -- (`else if ← c` would hoist `c` before the whole `if` chain and run it unconditionally).
    let ok ←
      if ← tryCloseFetchFromHasCode then
        Pure.pure true
      else do
      if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_assumption))) then
        Pure.pure true
      else do
      if ← skipNormFetchAt progExpr pcExpr then
        Pure.pure false
      else do
      if (← evalBitVecLit? pcExpr).isSome || (← evalPCBaseOff? pcExpr).isSome then
        tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (
          (conv => lhs; simp (config := { decide := true }) only [arm64_norm]);
          rfl))))
      else
        Pure.pure false
    setGoals savedGoals
    if ok then
      return some (← instantiateMVars instMVar, ← instantiateMVars fetchGoal)
    else
      return none
  let some (instExpr, fetchPrf) := fetchResOpt
    | do
      restoreState savedFetch
      if ← tryPairStepHook "wp_sym_step" progExpr pcExpr then
        return (.steppedPair, bs)
      if ← tryPairStepHook "wp_sym_step" progExpr pcExpr "callStep" then
        return (.steppedCall, bs)
      throwCouldNotFetchDecodeError "wp_sym_step" pcExpr
  let (stepRule, outcome) := classifyInsnStepRule instExpr
  let simpFn := fun e s => symSimpExpr e methods config s
  match stepRule with
  | .pureStep =>
    if let some (nextGoal, bs') ← symStepPureInsn? simpFn pcExpr instExpr fetchPrf bs then
      replaceMainGoal [nextGoal]
      return (outcome, bs')
  | .ldr64 rt addr =>
    if let some (nextGoal, bs') ← symStepLdr64Insn? simpFn pcExpr rt addr fetchPrf bs then
      replaceMainGoal [nextGoal]
      return (outcome, bs')
  | .str64 rt addr =>
    if let some (nextGoal, bs') ← symStepStr64Insn? simpFn pcExpr rt addr fetchPrf bs then
      replaceMainGoal [nextGoal]
      return (outcome, bs')
  | _ => pure ()
  if ← isTracingEnabledFor `proofLib.symStep.fallback then
    let reason : MessageData := match stepRule with
      | .pureStep => "pure-instruction fast path (symStepPureInsn?) failed"
      | .ldr64 .. => "LDR (64-bit) fast path (symStepLdr64Insn?) failed"
      | .str64 .. => "STR (64-bit) fast path (symStepStr64Insn?) failed"
      | _ => "no SymM fast path for this instruction class"
    let goalHead := (← instantiateMVars (← getMainTarget)).getAppFn
    trace[proofLib.symStep.fallback]
      m!"{reason}: stepping with wpStepCoreWithOutcome at PC {pcExpr}\n\
        instruction: {instExpr}\ngoal head: {goalHead}"
  let out ← wpStepCoreWithOutcome (isSingleStep := !inStepLoop)
  return (out, bs)

/-- Step forward through up to `maxSteps` instructions using the `SymM` / `Sym.Simp` engine,
    sharing a single `WpSymBlockState` (`AlphaShareCommon.State` + `persistentCache`) across the basic block. -/
def wpSymStepsCore (maxSteps : Nat) (quiet : Bool := false)
    (warnOnBoundReached : Bool := false) : TacticM Unit := do
  let _ ← getOrCreateWpNormSimpCacheRef
  let baseThms ← (← getMainGoal).withContext getOrBuildSymWPTheorems
  let mut localThms ← (← getMainGoal).withContext buildLocalSymTheorems
  let mut methods := mkSymWPMethods baseThms localThms
  let config : Sym.Simp.Config := { maxSteps := 100000 }
  let mut bs ← (← getMainGoal).withContext mkInitialWpSymBlockState
  let stopAtTarget := CondClassify.proofLib.wpStopAtBranchTarget.get (← getOptions)
  let verbose := !quiet && CondClassify.proofLib.wpVerbose.get (← getOptions)
  let mut boundaryCacheOpt : Option WpStepsBoundaryCache := none
  -- Set after a pair step (two instructions): the next iteration only consumes budget.
  let mut skipNext := false
  for i in [0:maxSteps] do
    if skipNext then
      skipNext := false
      continue
    let gs ← getGoals
    if gs.isEmpty then return
    let stateAndPc? ← withoutModifyingState do
      tryTacticCatchRuntime getSepWPStateAndPC
    let some (progExpr, targetPcExpr, pcExpr) := stateAndPc? | do
      if i == 0 && !quiet then
        let g ← getMainGoal
        let wpp? ← g.withContext do
          let tgt := (← instantiateMVars (← g.getType)).consumeMData
          if tgt.isAppOfArity ``SepWPp 7 then
            pure (some (tgt.getArg! 1, tgt.getArg! 2))
          else
            pure none
        if let some (targetPc, sExpr) := wpp? then
          let pcE := mkApp (mkConst ``State.pc) sExpr
          logWpStopBeforeTarget "wp_sym_steps" pcE targetPc
            m!"goal is `SepWPp`, which `wp_sym_steps` does not step directly"
            m!"use `wpp_call <callee_spec>`, `wp_cut_call`, or `apply SepWPp.of_sepWP_ret` / `apply SepWPp.of_sepWP`"
            (quiet := quiet)
      return
    let bc ← match boundaryCacheOpt with
      | some c => Pure.pure c
      | none =>
        let c ← buildWpStepsBoundaryCache progExpr
        boundaryCacheOpt := some c
        Pure.pure c
    -- Also at `i = 0`: a goal left at an `ite` PC by an earlier stepping call whose decided arm is
    -- the target must stop there instead of resolving the branch and stepping the target instruction.
    if stopAtTarget then
      match ← wpStopAtResolvedIteTarget pcExpr targetPcExpr with
      | .stopped =>
        if verbose then
          (← getMainGoal).withContext do
            logInfo <| MessageData.ofLazyM (es := #[targetPcExpr]) do
              return m!"wp_sym_steps: stopped at target after a conditional branch (pc = {targetPcExpr})"
        return
      | .unresolved =>
        if i > 0 then
          let cond := if pcExpr.isAppOfArity ``ite 5 then pcExpr.getArg! 1 else pcExpr
          logWpStopBeforeTarget "wp_sym_steps" pcExpr targetPcExpr
            m!"branch condition unresolved at pc (condition: {cond})"
            m!"use `wp_if hcond` (or prove `have hcond : ... := by bv_arith` before `wp_sym_steps`)"
            (quiet := quiet)
          return
      | _ => Pure.pure ()
    if i > 0 then
      let atTarget ← withoutModifyingState do
        tryTacticCatchRuntimeBool do
          if ← pcReachedTarget pcExpr targetPcExpr then Pure.pure ()
          else throwError "not at target"
      if atTarget then
        if verbose then
          (← getMainGoal).withContext do
            logInfo <| MessageData.ofLazyM (es := #[pcExpr]) do
              return m!"wp_sym_steps: stopped at return/target boundary (pc = {pcExpr})"
        return
      if ← isOtherFunctionEntryCached bc targetPcExpr pcExpr (afterUncondB := false) then
        logWpStopBeforeTarget "wp_sym_steps" pcExpr targetPcExpr
          m!"stopped at function entry / tail-call boundary"
          m!"use `wp_tailcall <callee_spec>` (or `wp_sym_step` to inline)"
          (quiet := quiet)
        return
    let wasIte := pcExpr.isAppOfArity ``ite 5
    let resolvedItePcRef ← IO.mkRef (none : Option Expr)
    let stepped? ← tryTacticCatchRuntimeMsg
      (wpSymStepInBlock methods config bs (inStepLoop := true) (resolvedItePcRef := some resolvedItePcRef))
    match stepped? with
    | .error detail =>
      let (_, targetNow, pcNow) ← getSepWPStateAndPC
      if let some resolvedPc ← resolvedItePcRef.get then
        reportStepStuck "wp_sym_steps" resolvedPc detail (some targetNow) (quiet := quiet)
      else if pcNow.isAppOfArity ``ite 5 then
        let cond := pcNow.getArg! 1
        logWpStopBeforeTarget "wp_sym_steps" pcNow targetNow
          m!"branch condition unresolved at pc (condition: {cond})"
          m!"use `wp_if hcond` (or prove `have hcond : ... := by bv_arith` before `wp_sym_steps`)"
          (quiet := quiet)
      else
        reportStepStuck "wp_sym_steps" pcNow detail (some targetNow) (quiet := quiet)
      return
    | .ok (out, bs') =>
      bs := bs'
      if wasIte then
        localThms ← (← getMainGoal).withContext buildLocalSymTheorems
        methods := mkSymWPMethods baseThms localThms
      match out with
      | .steppedCall =>
        if !quiet then
          let (_, targetAfter, pcAfter) ← getSepWPStateAndPC
          let atTarget ← withoutModifyingState do
            tryTacticCatchRuntimeBool do
              if ← pcReachedTarget pcAfter targetAfter then Pure.pure ()
              else throwError "not at target"
          if atTarget then
            if verbose then
              (← getMainGoal).withContext do
                logInfo <| MessageData.ofLazyM (es := #[pcAfter]) do
                  return m!"wp_sym_steps: stopped at subroutine call boundary (pc = {pcAfter})"
          else
            let callSitePc := (← resolvedItePcRef.get).getD pcExpr
            logWpStopBeforeTarget "wp_sym_steps" pcAfter targetAfter
              m!"stopped at subroutine call boundary (`bl` at {callSitePc})"
              m!"use `wpp_call <callee_spec>` or `wp_call <callee_spec>` (or `wp_sym_step` to inline)"
              (quiet := quiet)
        return
      | .steppedRet =>
        if !quiet then
          let (_, targetAfter, pcAfter) ← getSepWPStateAndPC
          let atTarget ← withoutModifyingState do
            tryTacticCatchRuntimeBool do
              if ← pcReachedTarget pcAfter targetAfter then Pure.pure ()
              else throwError "not at target"
          if atTarget then
            if verbose then
              (← getMainGoal).withContext do
                logInfo <| MessageData.ofLazyM (es := #[pcAfter]) do
                  return m!"wp_sym_steps: stopped at return/target boundary (pc = {pcAfter})"
          else
            logWpStopBeforeTarget "wp_sym_steps" pcAfter targetAfter
              m!"stopped at return (`ret`), which does not match target pc"
              m!"check `target_pc` or `lr` (`x30`) preservation before `wp_done`"
              (quiet := quiet)
        return
      | .steppedBranch =>
        let (_progAfter, targetAfter, pcAfter) ← getSepWPStateAndPC
        let atTarget ← withoutModifyingState do
          tryTacticCatchRuntimeBool do
            if ← pcReachedTarget pcAfter targetAfter then Pure.pure ()
            else throwError "not at target"
        if atTarget then
          if verbose then
            (← getMainGoal).withContext do
              logInfo <| MessageData.ofLazyM (es := #[pcAfter]) do
                return m!"wp_sym_steps: stopped at return/target boundary (pc = {pcAfter})"
          return
        if ← isOtherFunctionEntryCached bc targetAfter pcAfter (afterUncondB := true) then
          logWpStopBeforeTarget "wp_sym_steps" pcAfter targetAfter
            m!"stopped at function entry / tail-call boundary"
            m!"use `wp_tailcall <callee_spec>` (or `wp_sym_step` to inline)"
            (quiet := quiet)
          return
      | .steppedNormal =>
        continue
      | .steppedPair =>
        skipNext := true
        continue
  if warnOnBoundReached && maxSteps > 0 then
    let gsEnd ← getGoals
    if !gsEnd.isEmpty then
      let stateAndPcEnd? ← withoutModifyingState do
        tryTacticCatchRuntime getSepWPStateAndPC
      if let some (_, targetEnd, pcEnd) := stateAndPcEnd? then
        let atTargetEnd ← withoutModifyingState do
          tryTacticCatchRuntimeBool do
            if ← pcReachedTarget pcEnd targetEnd then Pure.pure ()
            else throwError "not at target"
        if !atTargetEnd then
          logWpStopBeforeTarget "wp_sym_steps" pcEnd targetEnd
            m!"reached default step bound ({maxSteps})"
            m!"pass an explicit bound (e.g. `wp_sym_steps {maxSteps * 2}`) or another `wp_sym_steps` to continue"
            (quiet := quiet)

/-- Take a single forward symbolic execution step using the `SymM` / `Sym.Simp` engine. -/
elab "wp_sym_step" : tactic => do
  let baseThms ← (← getMainGoal).withContext getOrBuildSymWPTheorems
  let localThms ← (← getMainGoal).withContext buildLocalSymTheorems
  let methods := mkSymWPMethods baseThms localThms
  let config : Sym.Simp.Config := { maxSteps := 100000 }
  let bs ← (← getMainGoal).withContext mkInitialWpSymBlockState
  let _ ← wpSymStepInBlock methods config bs

/-- Step forward through straight-line instructions (default bound 128, or `wp_sym_steps n`)
    using the `SymM` (`Lean.Meta.Sym.Simp`) engine. Under
    `set_option proofLib.wpVerbose true`, an `info` diagnostic is emitted with the stop reason
    and suggested next tactic. -/
syntax "wp_sym_steps" (ppSpace colGt num)? : tactic
elab_rules : tactic
  | `(tactic| wp_sym_steps $[$n?:num]?) => do
    let bound := match n? with
      | some n => n.getNat
      | none => 128
    let verbose := CondClassify.proofLib.wpVerbose.get (← getOptions)
    wpSymStepsCore bound (quiet := !verbose) (warnOnBoundReached := n?.isNone)

private def isSymTempName (n : Name) : Bool :=
  match n with
  | .str _ s =>
    let hasDigitOrUnderscoreAfter (pfx : String) : Bool :=
      s.startsWith pfx && s.length > pfx.length &&
      (let c := s.toList[pfx.length]!; c.isDigit || c == '_')
    s.startsWith "v_" || s.startsWith "t_" ||
    s == "tmp" || hasDigitOrUnderscoreAfter "tmp" ||
    s == "htmp" || hasDigitOrUnderscoreAfter "htmp" ||
    hasDigitOrUnderscoreAfter "h_tmp" ||
    hasDigitOrUnderscoreAfter "hv" ||
    hasDigitOrUnderscoreAfter "h_v" ||
    (s.startsWith "v" && s.length > 1 && (s.toList[1]?.map Char.isDigit).getD false) ||
    (s.startsWith "t" && s.length > 1 && (s.toList[1]?.map Char.isDigit).getD false)
  | _ => false

/-- Topologically inspect local `let`/`have` symbolic temporaries (`v*`, `hv*`, etc., or an
    explicit list of identifiers if provided) from newest to oldest and clear only those with
    zero forward dependencies in the goal or remaining context (never failing with
    `clear_dependent_var`). -/
def wpClearTempsCore (explicitIds : Array Ident := #[]) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let mut explicitFVars : Std.HashSet FVarId := {}
    for id in explicitIds do
      if let some decl := lctx.findFromUserName? id.getId then
        explicitFVars := explicitFVars.insert decl.fvarId
    let isCandidate (decl : LocalDecl) : Bool :=
      if !explicitIds.isEmpty then
        explicitFVars.contains decl.fvarId
      else
        isSymTempName decl.userName
    let goalTy ← instantiateMVars (← g.getType)
    let mut live := collectFVars {} goalTy
    let mut toClear : Array FVarId := #[]
    for declOpt in lctx.decls.toList.reverse do
      let some decl := declOpt | continue
      if decl.isImplementationDetail || decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      if isCandidate decl && !live.fvarSet.contains decl.fvarId then
        toClear := toClear.push decl.fvarId
      else
        live := collectFVars live ty
        if let some val := decl.value? then
          live := collectFVars live (← instantiateMVars val)
    if !toClear.isEmpty then
      let g' ← g.tryClearMany toClear
      replaceMainGoal [g']

/-- Clear dead local `let`/`have` symbolic temporaries (`v*`, `hv*`, etc., or an explicit list
    of identifiers) in reverse topological order, skipping any temporary that still has a forward
    dependency in the goal or remaining context (never failing with `clear_dependent_var`). -/
syntax "wp_clear_temps" (ppSpace colGt "[" ident,* "]")? (ppSpace colGt ident)* : tactic
elab_rules : tactic
  | `(tactic| wp_clear_temps $[ [ $[$brIds:ident],* ] ]? $[$ids:ident]*) => do
    let a1 := brIds.getD #[]
    wpClearTempsCore (a1 ++ ids)

/-- Step a `SepWP` goal using `wpSymStepsCore` from the current PC up to byte offset `targetOff`
    (relative to function entry where current PC is at `curOff`), executing `(targetOff - curOff) / 4`
    instructions. -/
def stepSymWpToOffset (tag : String) (targetOff curOff : Nat) : TacticM Unit := do
  unless curOff ≤ targetOff do
    throwError "{tag}: target byte offset {targetOff} precedes current PC byte offset {curOff}"
  unless (targetOff - curOff) % 4 == 0 do
    throwError "{tag}: byte distance {targetOff - curOff} (from +{curOff} to +{targetOff}) is not 4-byte aligned"
  let nSteps := (targetOff - curOff) / 4
  if nSteps > 0 then
    let verbose := CondClassify.proofLib.wpVerbose.get (← getOptions)
    wpSymStepsCore nSteps (quiet := !verbose) (warnOnBoundReached := false)

/-- Step a `SepWP` goal via `SymM` (`wpSymStepsCore`) up to the `k`-th (0-indexed, default `0`)
    call site (`wp_sym_steps_to_call <relocs> "<sym>" [k]`,
    `wp_sym_steps_to_call <entry> <relocs> "<sym>" [k]`, or
    `wp_sym_steps_to_call <code> <entry> <target> [k]`). -/
syntax "wp_sym_steps_to_call" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| wp_sym_steps_to_call $args:term*) => do
    let (_, callOff, curOff) ← resolveCallTargetOffArgs "wp_sym_steps_to_call" args
    stepSymWpToOffset "wp_sym_steps_to_call" callOff curOff

/-- Step a `SepWP` goal via `SymM` (`wpSymStepsCore`) up to the `k`-th `RET` instruction in `<words>`:
    `wp_sym_steps_to_ret <words> [k]`. -/
syntax "wp_sym_steps_to_ret" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| wp_sym_steps_to_ret $args:term*) => do
    unless args.size == 1 || args.size == 2 do
      throwError "wp_sym_steps_to_ret: expected `<words> [k]`, got {args.size} arguments"
    let w := args[0]!
    let k ← if args.size == 2 then
        let some n := args[1]!.raw.isNatLit?
          | throwError "wp_sym_steps_to_ret: expected occurrence index numeral, got `{args[1]!}`"
        pure n
      else pure 0
    let g ← getMainGoal
    let retOff ← g.withContext do
      let wE ← instantiateMVars (← Term.elabTermAndSynthesize w none)
      CodeLookup.lookupWordsRetOff wE k
    let (_, curOff) ← getGoalEntryAndCurOff none
    stepSymWpToOffset "wp_sym_steps_to_ret" retOff curOff

/-- Step a `SepWP` goal via `SymM` (`wpSymStepsCore`) up to the `k`-th instruction in `<words>`
    matching `<target>`: `wp_sym_steps_to_insn <words> <target> [k]`. -/
syntax "wp_sym_steps_to_insn" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| wp_sym_steps_to_insn $args:term*) => do
    unless args.size == 2 || args.size == 3 do
      throwError "wp_sym_steps_to_insn: expected `<words> <target> [k]`, got {args.size} arguments"
    let w := args[0]!
    let t := args[1]!
    let k ← if args.size == 3 then
        let some n := args[2]!.raw.isNatLit?
          | throwError "wp_sym_steps_to_insn: expected occurrence index numeral, got `{args[2]!}`"
        pure n
      else pure 0
    let g ← getMainGoal
    let insnOff ← g.withContext do
      let wE ← instantiateMVars (← Term.elabTermAndSynthesize w none)
      let tE ← instantiateMVars (← Term.elabTermAndSynthesize t none)
      CodeLookup.lookupWordsInsnOff wE tE k
    let (_, curOff) ← getGoalEntryAndCurOff none
    stepSymWpToOffset "wp_sym_steps_to_insn" insnOff curOff

end ProofLib
