/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.ObjectLoad

/-!
# Rebased Parametric Code Fetch Tests

Positive and negative tests for the `Program.rebase` lookup in `ProofLib.tryCloseFetchFromHasCode`
when the program constant is parameterized (`(C a).rebase b X`).
-/

@[expose] public section

namespace Examples.Testing.ParamCodeFetch

open Arm64 ProofLib ProofLib.ProgramReflection

set_option linter.literalFetch false

/-- A three-word program at base 0 whose third word `w` is a parameter: `NOP; RET; w`. -/
def widgetP (w : BitVec 32) : Program :=
  Program.ofWords 0#64 [0xd503201f#32, 0xd65f03c0#32, w]

/-- Fetch at offset 0 of `widgetP w` rebased to any `b`, with any extern hooks `X`. -/
theorem widgetP_rebase_fetch_base (w : BitVec 32) (b : BitVec 64)
    (X : String → Option (State → State)) :
    ((widgetP w).rebase b X).fetch b = some .nop := by
  have h := Program.fetch_rebase_eq_of_hookAtOff? (P := widgetP w) (b := b) (X := X)
    (O := fun _ => none) (off := 0) rfl (fun _ => rfl) (fun _ => rfl) (by decide) rfl
  rw [show b + BitVec.ofNat 64 0 = b from BitVec.add_zero b] at h
  exact h.trans (by rfl_kernel)

/-- Fetch at offset 4 of `widgetP w` (`RET`), for every parameter value `w`. -/
theorem widgetP_rebase_fetch_0x4 (w : BitVec 32) (b : BitVec 64)
    (X : String → Option (State → State)) :
    ((widgetP w).rebase b X).fetch (b + 0x4#64) = some (.ret (.gpr 30#5)) :=
  Program.fetch_rebase_eq_of_hookAtOff? (P := widgetP w) (b := b) (X := X)
    (O := fun _ => none) (off := 4) rfl (fun _ => rfl) (fun _ => rfl) (by decide) rfl
    |>.trans (by rfl_kernel)

/-- Fetch at offset 8 of `widgetP 0xd503201f` (`NOP`): stated for one fixed parameter value, so
    its binders are `b X` only and it does not match the `a₁ ... aₙ b X` shape the lookup needs. -/
theorem widgetP_rebase_fetch_0x8 (b : BitVec 64) (X : String → Option (State → State)) :
    ((widgetP 0xd503201f#32).rebase b X).fetch (b + 0x8#64) = some .nop :=
  Program.fetch_rebase_eq_of_hookAtOff? (P := widgetP 0xd503201f#32) (b := b)
    (X := X) (O := fun _ => none) (off := 8) rfl (fun _ => rfl) (fun _ => rfl) (by decide) rfl
    |>.trans (by rfl)

/-! ## Positive tests -/

example (w : BitVec 32) (b : BitVec 64) (X : String → Option (State → State)) :
    ((widgetP w).rebase b X).fetch b = some .nop := by
  arm64_code_at

example (w : BitVec 32) (b : BitVec 64) (X : String → Option (State → State)) :
    ((widgetP w).rebase b X).fetch (b + 0x4#64) = some (.ret (.gpr 30#5)) := by
  arm64_code_at

/-! ## Negative tests -/

/-- The only offset-8 lemma fixes the parameter (wrong binder shape): the lookup does not apply. -/
example (b : BitVec 64) (X : String → Option (State → State)) :
    ((widgetP 0xd503201f#32).rebase b X).fetch (b + 0x8#64) = some .nop := by
  fail_if_success (run_tac do
    unless ← ProofLib.tryCloseFetchFromHasCode do throwError "not closed")
  exact widgetP_rebase_fetch_0x8 b X

/-- The lemma's instruction (`RET`) does not match the goal's (`NOP`): the lookup does not apply. -/
example (w : BitVec 32) (b : BitVec 64) (X : String → Option (State → State)) :
    ((widgetP w).rebase b X).fetch (b + 0x4#64) ≠ some .nop := by
  intro h
  fail_if_success
    have : ((widgetP w).rebase b X).fetch (b + 0x4#64) = some .nop := by
      clear h
      run_tac do unless ← ProofLib.tryCloseFetchFromHasCode do throwError "not closed"
  rw [widgetP_rebase_fetch_0x4] at h
  cases h

end Examples.Testing.ParamCodeFetch
