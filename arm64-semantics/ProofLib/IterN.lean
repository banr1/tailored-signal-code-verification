/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Structural Loop Iterators

Pure loop iterators `iterN`, `iterDown`, and `iterUp` defined directly via `Nat.rec` instead of
`Nat.brecOn` recursion. Because their zero and step-first successor equations hold by `rfl` over an
abstract count, rewriting with `iterN_succ`, `iterDown_succ`, or `iterUp_succ` at a concrete bound
avoids unfolding the remaining iterations in the kernel. Import `ProofLib.IterN` explicitly when
defining pure loop models.
-/

@[expose] public section

namespace ProofLib

universe u

/-- `iterN f n x` applies `f` to `x` `n` times (`f` is applied first to `x`). Defined directly by
    `Nat.rec`, so `iterN_zero` / `iterN_succ` are `rfl` over an abstract count. -/
def iterN {α : Sort u} (f : α → α) (n : Nat) : α → α :=
  Nat.rec (motive := fun _ => α → α) (fun x => x) (fun _ ih x => ih (f x)) n

/-- `iterDown f n x` applies `f (n - 1)` first, then `f (n - 2)`, ..., and `f 0` last. Defined
    directly by `Nat.rec`, so `iterDown_zero` / `iterDown_succ` are `rfl` over an abstract count. -/
def iterDown {α : Sort u} (f : Nat → α → α) (n : Nat) : α → α :=
  Nat.rec (motive := fun _ => α → α) (fun x => x) (fun k ih x => ih (f k x)) n

/-- `iterUp f i n x` applies `f i` first, then `f (i + 1)`, ..., and `f (i + n - 1)` last. Defined
    directly by `Nat.rec` (the start index is threaded through the motive), so `iterUp_zero` /
    `iterUp_succ` are `rfl` over an abstract count. -/
def iterUp {α : Sort u} (f : Nat → α → α) (i n : Nat) : α → α :=
  Nat.rec (motive := fun _ => Nat → α → α) (fun _ x => x) (fun _ ih j x => ih (j + 1) (f j x)) n i

@[simp] theorem iterN_zero {α : Sort u} (f : α → α) (x : α) : iterN f 0 x = x := rfl

@[simp] theorem iterN_succ {α : Sort u} (f : α → α) (n : Nat) (x : α) :
    iterN f (n + 1) x = iterN f n (f x) := rfl

@[simp] theorem iterDown_zero {α : Sort u} (f : Nat → α → α) (x : α) : iterDown f 0 x = x := rfl

@[simp] theorem iterDown_succ {α : Sort u} (f : Nat → α → α) (n : Nat) (x : α) :
    iterDown f (n + 1) x = iterDown f n (f n x) := rfl

@[simp] theorem iterUp_zero {α : Sort u} (f : Nat → α → α) (i : Nat) (x : α) :
    iterUp f i 0 x = x := rfl

@[simp] theorem iterUp_succ {α : Sort u} (f : Nat → α → α) (i n : Nat) (x : α) :
    iterUp f i (n + 1) x = iterUp f (i + 1) n (f i x) := rfl

theorem iterN_succ' {α : Sort u} (f : α → α) (n : Nat) (x : α) :
    iterN f (n + 1) x = f (iterN f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- The last step of `iterDown f (n + 1)` is `f 0`; the earlier steps are `iterDown` of the
    shifted step `fun k => f (k + 1)`. -/
theorem iterDown_succ' {α : Sort u} (f : Nat → α → α) (n : Nat) (x : α) :
    iterDown f (n + 1) x = f 0 (iterDown (fun k => f (k + 1)) n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f (n + 1) x)

theorem iterUp_succ' {α : Sort u} (f : Nat → α → α) (i n : Nat) (x : α) :
    iterUp f i (n + 1) x = f (i + n) (iterUp f i n x) := by
  induction n generalizing i x with
  | zero => rfl
  | succ n ih =>
    rw [iterUp_succ, ih (i + 1) (f i x), iterUp_succ, show i + 1 + n = i + (n + 1) by omega]

theorem iterN_add {α : Sort u} (f : α → α) (m n : Nat) (x : α) :
    iterN f (m + n) x = iterN f n (iterN f m x) := by
  induction m generalizing x with
  | zero => show iterN f (0 + n) x = iterN f n x; rw [Nat.zero_add]
  | succ m ih => rw [Nat.add_right_comm]; exact ih (f x)

/-- `iterN` agrees with core `Nat.repeat` (which applies the step last); use it to reuse
    `Nat.repeat` lemmas. -/
theorem iterN_eq_repeat {α : Type u} (f : α → α) (n : Nat) (x : α) :
    iterN f n x = Nat.repeat f n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterN_succ', ih]; rfl

theorem iterDown_const {α : Sort u} (f : α → α) (n : Nat) (x : α) :
    iterDown (fun _ => f) n x = iterN f n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

theorem iterUp_const {α : Sort u} (f : α → α) (i n : Nat) (x : α) :
    iterUp (fun _ => f) i n x = iterN f n x := by
  induction n generalizing i x with
  | zero => rfl
  | succ n ih => exact ih (i + 1) (f x)

end ProofLib

end
