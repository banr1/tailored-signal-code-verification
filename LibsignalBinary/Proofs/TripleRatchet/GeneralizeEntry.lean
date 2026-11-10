/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean.Elab.Tactic -- shake: keep
import Arm64.Trusted.ISA.Semantics

/-!
# `generalize_entry`: Abstract Function Entry Addresses Without Kernel Re-Unfolding

`generalize (prog.fnAddr name) = entry at *` constructs a beta-redex that `instantiateMVars`
beta-reduces, re-inserting `prog.fnAddr name` into the proof term and forcing the kernel to unfold
`fnOff name` (linear symbol-table `String` lookup) during definitional equality checks.

`generalize_entry e = x` instead reverts hypotheses mentioning `Program.fnAddr`, abstracts `e` in
the goal, and closes the goal via the opaque theorem `bind_entry`, keeping `e` strictly as a
top-level argument to `bind_entry` so the kernel never unfolds it.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

universe u

/-- `P e` from `∀ x, P x`. A theorem (not a `fun` application), so the kernel does not
beta-reduce it and substitute `e` into the body. -/
theorem bind_entry {α : Sort u} {P : α → Prop} (e : α) (h : ∀ x : α, P x) : P e := h e

end CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry

public meta section

open Lean Meta Elab Tactic

/-- Implementation of `generalize_entry`: generalize `e` to a fresh `x` in the goal and in every
hypothesis that mentions one of `consts`, closing the old goal with `bind_entry`. -/
def run (e : Term) (x : Ident) (consts : Array Name) : TacticM Unit := withMainContext do
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
    let pLam := Lean.mkLambda x.getId BinderInfo.default eType targetAbst
    let newGoalType := mkForall x.getId BinderInfo.default eType targetAbst
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoalType (← mvarId.getTag)
    let proof := mkApp4 (mkConst ``CryptoVerification.LibsignalTripleRatchet.bind_entry [u]) eType pLam
      eExpr newMVar
    mvarId.assign proof
    let (_, mvarId') ← newMVar.mvarId!.intro1P
    let (_, mvarId'') ← mvarId'.introNP reverted.size
    replaceMainGoal [mvarId'']

end

end CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry

/-- `generalize_entry e = x`: replace `e` (typically `prog.fnAddr name`, or the program `prog`
itself) by a fresh variable `x` in the goal and in every hypothesis that mentions
`Program.fnAddr`, through `CryptoVerification.LibsignalTripleRatchet.bind_entry`.
`generalize_entry e = x reverting [c₁, …]` also generalizes the hypotheses that mention one of
the constants `cᵢ` (e.g. the program constant, when `e` is the program). See the module
docstring for why this is faster to kernel-check than `generalize e = x at *`. -/
syntax "generalize_entry " term:51 " = " ident (" reverting " "[" ident,* "]")? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| generalize_entry $e = $x) =>
    CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry.run e x #[``Arm64.Program.fnAddr]
  | `(tactic| generalize_entry $e = $x reverting [$cs,*]) => do
    let mut consts : Array Name := #[``Arm64.Program.fnAddr]
    for c in cs.getElems do
      consts := consts.push (← realizeGlobalConstNoOverloadWithInfo c)
    CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry.run e x consts

section Test
open Arm64

example (prog : Program) (h : prog.fnAddr "f" = 0#64) : prog.fnAddr "f" + 0#64 = 0#64 := by
  generalize_entry prog.fnAddr "f" = entry
  simpa using h

example (prog : Program) (h : prog.base = 0#64) : prog.base = 0#64 := by
  generalize_entry prog = p reverting [Program.base]
  exact h

end Test
