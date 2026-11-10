/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.ISA.Semantics
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
public meta import Lean.Elab.Tactic -- shake: keep

/-!
# `generalize_entry h : e = x`: Equation-Preserving Entry Generalization

Extends `generalize_entry` (`GeneralizeEntry.lean`) to introduce the equation `h : e = x` via
`bind_entry e (fun x => e = x → goal x) _ rfl`, keeping `e` as an argument to the opaque theorem
`bind_entry` so the kernel never substitutes or unfolds `prog.fnAddr name` inside the proof body.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry

public meta section

open Lean Meta Elab Tactic

/-- Implementation of `generalize_entry h : e = x`: as `run`, and also introduce `h : e = x`. -/
def runEq (h : Ident) (e : Term) (x : Ident) (consts : Array Name) : TacticM Unit :=
  withMainContext do
  let eExpr ← elabTerm e none
  let lctx ← getLCtx
  let mut toRevert : Array FVarId := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let ty ← instantiateMVars decl.type
      if (ty.find? fun sub => consts.any sub.isConstOf).isSome then
        toRevert := toRevert.push decl.fvarId
  let (reverted, mvarId) ← (← getMainGoal).revert toRevert true
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    let targetAbst ← kabstract target eExpr
    let eType ← inferType eExpr
    let u ← getLevel eType
    -- `fun x => e = x → target[x]`; under the `h` binder, `x` is `#1`.
    let eqTy := mkApp3 (mkConst ``Eq [u]) eType eExpr (mkBVar 0)
    let body := mkForall h.getId BinderInfo.default eqTy (targetAbst.liftLooseBVars 0 1)
    let pLam := Lean.mkLambda x.getId BinderInfo.default eType body
    let newGoalType := mkForall x.getId BinderInfo.default eType body
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoalType (← mvarId.getTag)
    let proof := mkApp
      (mkApp4 (mkConst ``CryptoVerification.LibsignalTripleRatchet.bind_entry [u]) eType pLam eExpr
        newMVar)
      (mkApp2 (mkConst ``Eq.refl [u]) eType eExpr)
    mvarId.assign proof
    let (_, m1) ← newMVar.mvarId!.intro1P
    let (_, m2) ← m1.intro1P
    let (_, m3) ← m2.introNP reverted.size
    replaceMainGoal [m3]

end

end CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry

/-- `generalize_entry h : e = x`: `generalize_entry e = x` (see `TripleRatchet/GeneralizeEntry.lean`)
that also introduces the equation `h : e = x`. A fast replacement for
`generalize h : e = x at *` when the proof uses `h`. -/
syntax "generalize_entry " ident " : " term:51 " = " ident (" reverting " "[" ident,* "]")? :
  tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| generalize_entry $h:ident : $e = $x) =>
    CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry.runEq h e x #[``Arm64.Program.fnAddr]
  | `(tactic| generalize_entry $h:ident : $e = $x reverting [$cs,*]) => do
    let mut consts : Array Name := #[``Arm64.Program.fnAddr]
    for c in cs.getElems do
      consts := consts.push (← realizeGlobalConstNoOverloadWithInfo c)
    CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry.runEq h e x consts

section Test
open Arm64

example (prog : Program) (h0 : prog.fnAddr "f" = 0#64) : prog.fnAddr "f" + 0#64 = 0#64 := by
  generalize_entry h : prog.fnAddr "f" = entry
  have _ : prog.fnAddr "f" = entry := h
  simpa using h0

-- The unnamed form still parses as before.
example (prog : Program) (h : prog.fnAddr "f" = 0#64) : prog.fnAddr "f" + 0#64 = 0#64 := by
  generalize_entry prog.fnAddr "f" = entry
  simpa using h

end Test
