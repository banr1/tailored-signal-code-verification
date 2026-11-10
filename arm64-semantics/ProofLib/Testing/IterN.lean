/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.IterN

/-!
# Regression Tests for `ProofLib.IterN`

Tests `iterN`, `iterDown`, and `iterUp` (`ProofLib/IterN.lean`): `rfl` zero/successor equations,
step-last equations, `Nat.repeat` equivalence, non-unfolding on large literal counts under tight
`maxRecDepth`/`maxHeartbeats` budgets, and `#guard_msgs` checks on abstract counts.
-/

@[expose] public section

namespace ProofLib.Testing.IterN

open ProofLib

/-! ## Small Concrete Counts -/

example : iterN (· + 2) 5 1 = 11 := rfl
example : iterDown (fun i acc => acc * 10 + i) 3 0 = 210 := rfl
example : iterUp (fun i acc => acc * 10 + i) 1 3 0 = 123 := rfl
example : iterN (· * 2) 10 1 = 2 ^ 10 := by decide

/-! ## Equations Over Abstract Steps -/

example {α : Type} (f : α → α) (n : Nat) (x : α) : iterN f (n + 2) x = iterN f n (f (f x)) := by
  simp only [iterN_succ]

example {α : Type} (f : α → α) (n : Nat) (x : α) : iterN f (n + 1) x = f (iterN f n x) :=
  iterN_succ' f n x

example {α : Type} (f : Nat → α → α) (n : Nat) (x : α) :
    iterDown f (n + 1) x = f 0 (iterDown (fun k => f (k + 1)) n x) :=
  iterDown_succ' f n x

example {α : Type} (f : Nat → α → α) (i n : Nat) (x : α) :
    iterUp f i (n + 1) x = f (i + n) (iterUp f i n x) :=
  iterUp_succ' f i n x

example {α : Type} (f : α → α) (n : Nat) (x : α) : iterN f n x = Nat.repeat f n x :=
  iterN_eq_repeat f n x

example {α : Type} (f : α → α) (m n : Nat) (x : α) :
    iterN f (m + n) x = iterN f n (iterN f m x) := iterN_add f m n x

example {α : Type} (f : α → α) (i n : Nat) (x : α) :
    iterUp (fun _ => f) i n x = iterDown (fun _ => f) n x := by
  rw [iterUp_const, iterDown_const]

/-! ## Large Literal Counts

Each step below is one `Nat` literal comparison (`999999 + 1 =?= 1000000`) for the kernel; the
remaining 999999 iterations of an opaque step stay folded. The tight `maxRecDepth` and
`maxHeartbeats` budgets make any accidental unfolding fail loudly. -/

set_option maxRecDepth 128 in
set_option maxHeartbeats 2000 in
example {α : Type} (f : α → α) (x : α) : iterN f 1000000 x = iterN f 999999 (f x) :=
  iterN_succ f 999999 x

set_option maxRecDepth 128 in
set_option maxHeartbeats 2000 in
example {α : Type} (f : α → α) (x : α) : iterN f 1000000 x = iterN f 999998 (f (f x)) := by
  rw [iterN_succ, iterN_succ]

set_option maxRecDepth 128 in
set_option maxHeartbeats 2000 in
example {α : Type} (f : Nat → α → α) (x : α) :
    iterDown f 1000000 x = iterDown f 999999 (f 999999 x) :=
  iterDown_succ f 999999 x

set_option maxRecDepth 128 in
set_option maxHeartbeats 2000 in
example {α : Type} (f : Nat → α → α) (x : α) :
    iterUp f 7 1000000 x = iterUp f 8 999999 (f 7 x) :=
  iterUp_succ f 7 999999 x

-- A large count of an expensive concrete step: the successor equation still costs one literal
-- comparison, independent of the cost of the step.
set_option maxRecDepth 128 in
set_option maxHeartbeats 2000 in
example (x : Nat) :
    iterN (fun y => y * y % (2 ^ 255 - 19)) 254 x
      = iterN (fun y => y * y % (2 ^ 255 - 19)) 253 (x * x % (2 ^ 255 - 19)) :=
  iterN_succ _ 253 x

/-! ## Negative Tests on Abstract Counts -/

/-- error: `simp` made no progress -/
#guard_msgs in
example {α : Type} (f : α → α) (n : Nat) (x : α) : iterN f n x = Nat.repeat f n x := by
  simp only [iterN_succ, iterN_zero]

/-- error: `simp` made no progress -/
#guard_msgs in
example {α : Type} (f : Nat → α → α) (i n : Nat) (x : α) : iterUp f i n x = x := by
  simp only [iterUp_succ, iterUp_zero]

end ProofLib.Testing.IterN

end
