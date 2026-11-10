/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

/-!
# Deliberately Unsound Fixtures for Kernel Axiom Audit

Isolated fixture declarations using `sorry`, custom axioms, `native_decide`, and `bv_decide` to
serve as negative test inputs that `#axiom_audit` must flag.
-/

@[expose] public section

namespace Testing.AxiomAudit.Tests

theorem clean_thm (a b : Nat) : a + b = b + a := Nat.add_comm a b

set_option warn.sorry false in
theorem sorry_thm : (1 : Nat) = 2 := by sorry

axiom custom_ax : (1 : Nat) = 1

theorem uses_custom : (1 : Nat) = 1 := custom_ax

theorem uses_native : (10 : Nat) < 11 := by native_decide

theorem uses_bv_decide (x y : BitVec 8) : (x ^^^ y) + 2 * (x &&& y) = x + y := by bv_decide

/-- Downstream theorem: blame must point at `uses_bv_decide`, not at the downstream theorem. -/
theorem downstream (x y : BitVec 8) : (x ^^^ y) + 2 * (x &&& y) + 0 = x + y :=
  (BitVec.add_zero _).trans (uses_bv_decide x y)

set_option warn.sorry false in
private theorem priv_sorry : (2 : Nat) = 3 := by sorry

end Testing.AxiomAudit.Tests
