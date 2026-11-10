/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Arm64
public import ProofLib.VCGen
public import ProofLib.SepLogic.WP.TacticCore

/-!
# Pair-Step and Call-Step Hook for Placed Code

Step-tactic hook (`tryPairStepHook`) for linker-placed programs `(C a_1 ... a_n).rebase b X` at
offsets without a fixed single-word instruction encoding:
- `C_pairStep_0x<off>` steps across a two-word sequence such as a relaxable `ADRP` + `ADD` pair;
- `C_callStep_0x<off>` steps across a linker-retargetable `BL` to a branch-forwarding entry,
  stopping `wp_steps` at the final callee entry with `X30` set.

Both follow the signature convention
`C_<kind>_0x<off> a_1 ... a_n b X (h_1 : H_1) ... (h_k : H_k) (hnext : SepWP _ tgt s' P post oom) : SepWP _ tgt s P post oom`
with `tgt s P post oom` implicit. Side conditions `H_i` are discharged from `s.status = .Running`,
`s.pc = e` (including base-offset reassociation), reducible `assumption` (up to 3 levels of `∧`
projections), and `rfl`. `skipNormFetchAt` skips the `simp only [arm64_norm]` fetch fallback at
registered pair-step and call-step offsets (configurable via `proofLib.skipNormAtCallStep`).
-/

public section

namespace ProofLib

/-- Reassociate `x = b + pcOff` into `x = (b + bOff) + k` when `bOff + k = pcOff`. -/
theorem eq_add_of_eq_add_assoc {x b bOff k pcOff : BitVec 64}
    (hp : x = b + pcOff) (heq : bOff + k = pcOff) : x = (b + bOff) + k := by
  rw [hp, BitVec.add_assoc, heq]

end ProofLib

end

public meta section

namespace ProofLib

open Arm64
open Lean Elab Tactic Meta

private def tryAssocPcEq? (p pcFound rhs ty : Expr) : MetaM (Option Expr) := do
  let some (_, xE, _) := ty.eq? | return none
  if !pcFound.isAppOfArity ``HAdd.hAdd 6 || !rhs.isAppOfArity ``HAdd.hAdd 6 then
    return none
  let bAdd := rhs.getArg! 4
  if !bAdd.isAppOfArity ``HAdd.hAdd 6 then return none
  if !(← withReducible (isDefEq (pcFound.getArg! 4) (bAdd.getArg! 4))) then return none
  let bOffE := bAdd.getArg! 5
  let kE := rhs.getArg! 5
  let pcOffE := pcFound.getArg! 5
  let some (64, bOffV) ← evalBitVecLit? bOffE | return none
  let some (64, kV) ← evalBitVecLit? kE | return none
  let some (64, pcOffV) ← evalBitVecLit? pcOffE | return none
  if (bOffV + kV) % (1 <<< 64) != pcOffV then return none
  let sumE ← mkAppM ``HAdd.hAdd #[bOffE, kE]
  if !(← isDefEq sumE pcOffE) then return none
  let heq ← mkExpectedTypeHint (← mkEqRefl pcOffE) (← mkEq sumE pcOffE)
  let prf := mkAppN (mkConst ``eq_add_of_eq_add_assoc)
    #[xE, bAdd.getArg! 4, bOffE, kE, pcOffE, p, heq]
  if ← withReducible (isDefEq (← inferType prf) ty) then return some prf
  return none

/-- Look up `C_<kind>_0x<off> a_1 ... a_n b X` when `progExpr = (C a_1 ... a_n).rebase b X _`
    and `pcExpr = b + off#64` (or `b = b_0 + bOff#64` and `pcExpr = b_0 + pcOff#64` with
    `off = pcOff - bOff`). -/
def findPairStepLemma? (progExpr pcExpr : Expr) (kind : String := "pairStep") :
    MetaM (Option (Name × Expr)) := do
  let progExpr ← instantiateMVars progExpr
  let progExpr ← if progExpr.isAppOfArity ``Program.rebase 4 then pure progExpr
    else withReducible (whnf progExpr)
  if !progExpr.isAppOfArity ``Program.rebase 4 then return none
  let cExpr := progExpr.getArg! 0
  let bExpr := progExpr.getArg! 1
  let xExpr := progExpr.getArg! 2
  let cFn := cExpr.getAppFn
  if !cFn.isConst then return none
  let some (pcBase, offVal) ← evalPCBaseOff? pcExpr | return none
  let relOff? : Option Nat ← do
    if ← withReducible (isDefEq pcBase bExpr) then
      pure (some offVal)
    else if let some (bBase, bOff) ← evalPCBaseOff? bExpr then
      if bOff > 0 && offVal ≥ bOff && offVal < 2 ^ 64 &&
          (← withReducible (isDefEq pcBase bBase)) then
        pure (some (offVal - bOff))
      else
        pure none
    else
      pure none
  let some relOff := relOff? | return none
  let hexStr := String.ofList (Nat.toDigits 16 relOff)
  let lemmaName := cFn.constName!.appendAfter s!"_{kind}_0x{hexStr}"
  let some info := (← getEnv).find? lemmaName | return none
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  return some (lemmaName, mkApp2 (mkAppN (mkConst lemmaName lvls) cExpr.getAppArgs) bExpr xExpr)

register_option proofLib.skipNormAtCallStep : Bool := {
  defValue := true
  descr := "Skip the `simp only [arm64_norm]` fetch fallback in `wp_steps` / `wp_sym_steps` at a pc \
    that has a `C_callStep_0x<off>` lemma (as at `C_pairStep_0x<off>` sites), and step with the \
    call-step lemma directly. Set to `false` to try the `arm64_norm` fetch first."
}

/-- Whether the step tactics should skip their `simp only [arm64_norm]` fetch fallback at
    `pcExpr`: true at a `C_pairStep_0x<off>` site, and (unless `proofLib.skipNormAtCallStep` is
    `false`) at a `C_callStep_0x<off>` site. Such sites have no fixed fetch result, so the
    simp fallback would fail anyway, and the hooks of `tryPairStepHook` handle them. -/
def skipNormFetchAt (progExpr pcExpr : Expr) : MetaM Bool := do
  if (← findPairStepLemma? progExpr pcExpr).isSome then return true
  if !proofLib.skipNormAtCallStep.get (← getOptions) then return false
  return (← findPairStepLemma? progExpr pcExpr "callStep").isSome

private partial def conjProj? (ty prf pty : Expr) (depth : Nat) : MetaM (Option Expr) := do
  if ← withReducible (isDefEq pty ty) then return some prf
  if depth == 0 then return none
  let pty' ← withReducible (whnf pty)
  let_expr And a b := pty' | return none
  if let some p ← conjProj? ty (mkApp3 (mkConst ``And.left) a b prf) a (depth - 1) then
    return some p
  conjProj? ty (mkApp3 (mkConst ``And.right) a b prf) b (depth - 1)

private def dischargePairSide? (s pcExpr ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  if let some (_, lhs, rhs) := ty.eq? then
    if lhs.isAppOfArity ``State.status 1 && rhs.isConstOf ``ExecStatus.Running then
      if ← isDefEq (lhs.getArg! 0) s then
        if let some p ← proveStatusRunningExpr? s then return some p
    if lhs.isAppOfArity ``State.pc 1 then
      if ← isDefEq (lhs.getArg! 0) s then
        if let some (pcFound, p) ← provePcEq? s then
          if ← withReducible (isDefEq pcFound rhs) then return some p
          if let some prf ← tryAssocPcEq? p pcFound rhs ty then return some prf
          if !pcFound.isAppOfArity ``HAdd.hAdd 6 && !rhs.isAppOfArity ``HAdd.hAdd 6 then
            if ← isDefEq pcFound rhs then return some p
        if ← withReducible (isDefEq pcExpr rhs) then
          if let some (pcFound, p) ← provePcEq? s then
            if ← withReducible (isDefEq pcFound pcExpr) then return some p
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      if let some p ← conjProj? ty decl.toExpr decl.type 3 then
        return some p
      if let some (_, lhs, rhs) := ty.eq? then
        if lhs.isAppOfArity ``State.pc 1 then
          if let some (_, dlhs, drhs) := decl.type.eq? then
            if ← withReducible (isDefEq dlhs lhs) then
              if let some prf ← tryAssocPcEq? decl.toExpr drhs rhs ty then return some prf
  if let some (_, lhs, rhs) := ty.eq? then
    if ← withReducible (isDefEq lhs rhs) then
      return some (← mkEqRefl lhs)
  return none

/-- Apply `C_<kind>_0x<off>` to a `SepWP ((C a_1 ... a_n).rebase b X) tgt s P post oom` goal at
    `pcExpr`, discharge its side conditions, normalize the resulting state, and return `true`
    (or `false` if no such lemma exists). -/
def tryPairStepHook (tacticName : String) (progExpr pcExpr : Expr) (kind : String := "pairStep") :
    TacticM Bool := do
  let g ← getMainGoal
  let found? ← g.withContext (findPairStepLemma? progExpr pcExpr kind)
  let some (lemmaName, lemmaApp) := found? | return false
  let newGoals ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then
      throwError "{tacticName}: pair-step lemma `{lemmaName}` found at PC `{pcExpr}`, but the goal \
        is not a `SepWP` goal"
    let s := ty.getArg! 2
    let gs ← try g.apply lemmaApp
      catch e => throwError "{tacticName}: pair-step lemma `{lemmaName}` does not apply at PC \
        `{pcExpr}`:{indentD e.toMessageData}"
    let mut rest : List MVarId := []
    for sg in gs do
      if ← sg.isAssigned then continue
      let sty := (← instantiateMVars (← sg.getType)).consumeMData
      if sty.isAppOfArity ``SepWP 6 then
        rest := rest ++ [sg]
        continue
      let some prf ← sg.withContext (dischargePairSide? s pcExpr sty)
        | throwError "{tacticName}: pair-step lemma `{lemmaName}` at PC `{pcExpr}`: could not \
            discharge hypothesis{indentExpr sty}\nhint: add it to the local context (tried the \
            state spine, `assumption`, and `rfl`)"
      sg.assign prf
    pure rest
  let [gNext] := newGoals
    | throwError "{tacticName}: pair-step lemma `{lemmaName}` at PC `{pcExpr}` left \
        {newGoals.length} `SepWP` goals (expected 1)"
  replaceMainGoal [gNext]
  -- When the program base is a shifted `b₀ + bOff`, fold `(b₀ + bOff) + k` in the new state
  -- into `b₀ + (bOff + k)` before `wp_norm_state`.
  let progUnw ← gNext.withContext do
    let p ← instantiateMVars progExpr
    if p.isAppOfArity ``Program.rebase 4 then pure p else withReducible (whnf p)
  if progUnw.isAppOfArity ``Program.rebase 4 && (progUnw.getArg! 1).isAppOfArity ``HAdd.hAdd 6 then
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      conv => arg 3; simp only [ProofLib.reduceBitVecAddAssoc])))
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_norm_state)))
  return true

end ProofLib
