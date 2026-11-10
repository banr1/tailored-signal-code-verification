/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
import Mathlib.Data.Nat.Log

/-!
# Logarithmic Cost-to-Size Budget Bridge

Bit-length inequalities for `ReductionDsl.bits` and arithmetic bridges bounding parameterized
reduction AST sizes `sz ≤ C₀ + C₁ * bits costBudget` by
`reductionSizeBudget + 2 ^ 12 * bits costBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.ReductionDsl.SizeBudgetBridge

open _root_.ReductionDsl (bits reductionSizeBudget)

theorem bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem bits_pos (n : ℕ) : 1 ≤ bits n := by
  unfold bits
  omega

theorem bits_add_le_two_mul_bits_add (a b : ℕ) :
    bits a + bits b ≤ 2 * bits (a + b) := by
  have ha : bits a ≤ bits (a + b) := bits_mono (Nat.le_add_right a b)
  have hb : bits b ≤ bits (a + b) := bits_mono (Nat.le_add_left b a)
  omega

theorem bits_succ_le (n : ℕ) : bits (n + 1) ≤ bits n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · unfold bits
    have h2n : n + 1 ≤ 2 * n := by omega
    have hlog : Nat.log 2 (n + 1) ≤ Nat.log 2 (2 * n) := Nat.log_mono_right h2n
    rw [Nat.mul_comm, Nat.log_mul_base (by decide) (by omega)] at hlog
    omega

/-- Bounds `sz` by `reductionSizeBudget + 2 ^ 12 * bits costBudget` from
`sz ≤ C₀ + C₁ * bits costBudget` with `C₀ ≤ 2 ^ 22` and `C₁ ≤ 2 ^ 11`. -/
theorem size_le_budget_of_log_cost {sz C₀ C₁ costBudget : ℕ}
    (h₀ : C₀ ≤ 2 ^ 22) (h₁ : C₁ ≤ 2 ^ 11)
    (hR : sz ≤ C₀ + C₁ * bits costBudget) :
    sz ≤ reductionSizeBudget + 2 ^ 12 * bits costBudget := by
  have h₀' : C₀ ≤ reductionSizeBudget := Nat.le_trans h₀ (by decide)
  have h₁' : C₁ * bits costBudget ≤ 2 ^ 12 * bits costBudget :=
    Nat.mul_le_mul_right (bits costBudget) (Nat.le_trans h₁ (by decide))
  omega

theorem size_le_budget_of_log_cost_mono {sz C₀ C₁ param costBudget : ℕ}
    (h₀ : C₀ ≤ 2 ^ 22) (h₁ : C₁ ≤ 2 ^ 11) (hM : param ≤ costBudget)
    (hR : sz ≤ C₀ + C₁ * bits param) :
    sz ≤ reductionSizeBudget + 2 ^ 12 * bits costBudget := by
  have hbit : C₁ * bits param ≤ C₁ * bits costBudget :=
    Nat.mul_le_mul_left C₁ (bits_mono hM)
  exact size_le_budget_of_log_cost h₀ h₁ (Nat.le_trans hR (by omega))

theorem bits_mul_le (a b : ℕ) : bits (a * b) ≤ bits a + bits b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.zero_mul]
    have hb : 1 ≤ bits b := bits_pos b
    have h0 : bits 0 = 1 := by decide
    omega
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp only [Nat.mul_zero]
      have ha' : 1 ≤ bits a := bits_pos a
      have h0 : bits 0 = 1 := by decide
      omega
    · unfold bits
      have ha_lt : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by decide) a
      have hb_lt : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by decide) b
      have hab_lt : a * b < 2 ^ ((Nat.log 2 a + 1) + (Nat.log 2 b + 1)) := by
        rw [Nat.pow_add]
        exact Nat.mul_lt_mul'' ha_lt hb_lt
      have hlog : Nat.log 2 (a * b) < (Nat.log 2 a + 1) + (Nat.log 2 b + 1) :=
        Nat.log_lt_of_lt_pow (Nat.mul_ne_zero (by omega) (by omega)) hab_lt
      omega

end Computational.Proofs.ReductionDsl.SizeBudgetBridge
