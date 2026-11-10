/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import GeneratedLean.LibsignalSessionObj
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.E2E.Record.Support.ImageWitness
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Loaded session image at base `0` (`sessionImg0`)

Defines `sessionImg0` (`libsignalSessionImage` loaded at base `0`) and proves well-formedness and
`Obj.Loads libsignalSessionImage sessionImg0`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record

open Arm64

/-- `libsignalSessionImage` loaded at base 0. -/
noncomputable def sessionImg0 : Obj.Image :=
  match libsignalSessionImage.load 0#64 with
  | .ok img => img
  | .error _ => default

/-- `libsignalSessionImage` is well formed. -/
theorem libsignalSessionImage_wellFormed : libsignalSessionImage.wellFormed = true := by
  exact ImageWitness.libsignalSessionImage_wellFormed'

/-- Loading `libsignalSessionImage` at base `0` succeeds. -/
theorem libsignalSessionImage_load_ok : ∃ img, libsignalSessionImage.load 0#64 = .ok img := by
  exact ImageWitness.libsignalSessionImage_load_ok'

open Lean Meta Elab Tactic in
run_meta do
  let info ← getConstInfo ``sessionImg0
  let val := info.value!
  let fnHead := val.getAppFn
  let args := val.getAppArgs
  let excTy := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkConst ``Obj.Image)
  let imgTy := mkConst ``Obj.Image
  let fnVal := Expr.lam `x excTy (mkApp4 fnHead args[0]! (.bvar 0) args[2]! args[3]!) .default
  withExporting <| addDecl (.defnDecl {
    name := `CryptoVerification.E2E.Record.sessionImg0_fn
    levelParams := []
    type := Expr.forallE `x excTy imgTy .default
    value := fnVal
    hints := info.hints
    safety := .safe
  })

private theorem load_eq_ok_of_fn {e : Except String Obj.Image} {img0 : Obj.Image}
    (h : ∃ img, e = .ok img)
    (heq : sessionImg0_fn e = img0) :
    e = .ok img0 := by
  obtain ⟨img, rfl⟩ := h
  delta sessionImg0_fn at heq
  change img = img0 at heq
  exact congrArg Except.ok heq

open Lean Meta Elab Tactic in
elab "assign_load_sessionImg0" : tactic => withMainContext do
  let info ← getConstInfo ``sessionImg0
  let args := info.value!.getAppArgs
  let e := args[1]!
  let img0 := mkConst ``sessionImg0
  let h := mkConst ``libsignalSessionImage_load_ok
  let heq := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Obj.Image) img0
  let pf := mkApp4 (mkConst ``load_eq_ok_of_fn) e img0 h heq
  (← getMainGoal).assign pf
  replaceMainGoal []

private theorem libsignalSessionImage_load_sessionImg0 :
    libsignalSessionImage.load 0#64 = .ok sessionImg0 := by
  assign_load_sessionImg0

private theorem loads_of_load_zero {li : Obj.LinkedImage} {img : Obj.Image}
    (h : li.load 0#64 = .ok img) :
    Obj.Loads li img := by
  change li.load img.base = .ok img
  rw [(ProofLib.ObjectLoad.load_ok h).1]
  exact h

/-- `sessionImg0` is a valid load of `libsignalSessionImage`. -/
theorem loads_sessionImg0 : Obj.Loads libsignalSessionImage sessionImg0 := by
  exact loads_of_load_zero libsignalSessionImage_load_sessionImg0

namespace EntryAux

theorem sessionImg0_base : sessionImg0.base = 0#64 :=
  (ProofLib.ObjectLoad.load_ok libsignalSessionImage_load_sessionImg0).1

end EntryAux

end CryptoVerification.E2E.Record
