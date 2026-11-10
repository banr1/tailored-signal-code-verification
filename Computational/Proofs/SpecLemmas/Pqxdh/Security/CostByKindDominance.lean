/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.Assumptions
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Game.StatementBinaryHarnessCore

/-!
# Comparison of Per-Kind and Total-Count Cost Budgets

Proves dominance and equality relations comparing the per-kind query and step-cost budgets
(`gdhQueryBudget`, `authGdhQueryBudget`, `gdhPrimQueryBudget`, `stepCostBudgetSplit`,
`bhAdapterCostBudgetByKind`, and `bhE2ECostBudgetByKind`) against their total-count counterparts.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

/-- `gdhQueryBudget` is bounded above by the total-count form clamping sessions at
`min q_total N_sess_tot`. -/
theorem gdhQueryBudget_le_v2 (S : Setup) (b : QueryBudget) :
    gdhQueryBudget S b ≤
      min (4 * b.q_total ^ 2)
          (4 * min b.q_ro b.q_total * min b.q_total S.N_sess_tot +
            2 * min b.q_total S.N_sess_tot * (min b.q_total S.N_sess_tot - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot := by
  have hs : min (min b.q_on b.q_total) S.N_sess_tot ≤ min b.q_total S.N_sess_tot := by omega
  unfold gdhQueryBudget
  dsimp only
  gcongr

/-- `authGdhQueryBudget` is bounded above by the total-count form clamping sessions at
`min q_total N_sess_tot`. -/
theorem authGdhQueryBudget_le_v2 (S : Setup) (b : QueryBudget) :
    authGdhQueryBudget S b ≤
      min (5 * b.q_total ^ 2)
          ((4 * min b.q_ro b.q_total + min b.q_roRoot b.q_total) * min b.q_total S.N_sess_tot +
            3 * min b.q_total S.N_sess_tot * (min b.q_total S.N_sess_tot - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot := by
  have hs : min (min b.q_on b.q_total) S.N_sess_tot ≤ min b.q_total S.N_sess_tot := by omega
  unfold authGdhQueryBudget
  dsimp only
  gcongr

private theorem prim_aux (q s' s C : ℕ) (hs' : s' ≤ s) (hs : s ≤ q) (hC : 2 ≤ C) :
    32 * (q - s') + 16 * (s' + 1) * C ≤ 32 * (q - s) + 16 * (s + 1) * C := by
  obtain ⟨k, rfl⟩ : ∃ k, s = s' + k := ⟨s - s', by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, q = s' + k + r := ⟨q - (s' + k), by omega⟩
  have e1 : s' + k + r - s' = k + r := by omega
  have e2 : s' + k + r - (s' + k) = r := by omega
  rw [e1, e2]
  have hk : k * 2 ≤ k * C := Nat.mul_le_mul_left _ hC
  nlinarith [hk]

/-- `gdhPrimQueryBudget` is bounded above by the total-count form clamping sessions at
`min q_total N_sess_tot`. -/
theorem gdhPrimQueryBudget_le_v2 (S : Setup) (b : QueryBudget) :
    gdhPrimQueryBudget S b ≤
      32 * (b.q_total - min b.q_total S.N_sess_tot) +
        16 * (min b.q_total S.N_sess_tot + 1) * (5 * S.N_dh + S.N_sess_tot + 12) := by
  unfold gdhPrimQueryBudget
  dsimp only
  exact prim_aux _ _ _ _ (by omega) (by omega) (by omega)

private theorem split_aux (a m q β Ad As Qd Qs L : ℕ) (hq : a + m ≤ q) (hβ : β + 4 ≤ 7 * m)
    (hd : Ad ≤ Qd) (hs : As ≤ Qs) :
    2 ^ 16 * (a + 1) * (a + 1) + 2 ^ 15 * (a + 1) * (Ad + As) + 2 ^ 10 * (a + m + 1) * L +
        2 ^ 13 * (m + a) * (β + 4) + 2 ^ 13 * m * a + 2 ^ 11 * Ad ^ 2 + 2 ^ 8 * Ad * As ≤
      2 ^ 16 * (q + 1) * (q + 1) + 2 ^ 15 * (q + 1) * (Qd + Qs) + 2 ^ 10 * (q + 1) * L +
        2 ^ 11 * Qd ^ 2 + 2 ^ 8 * Qd * Qs := by
  have h1 : (a + m + 1) * (a + m + 1) ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (a + 1) * (Ad + As) ≤ (q + 1) * (Qd + Qs) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (a + m + 1) * L ≤ (q + 1) * L := Nat.mul_le_mul_right _ (by omega)
  have h4 : Ad ^ 2 ≤ Qd ^ 2 := Nat.pow_le_pow_left hd 2
  have h5 : Ad * As ≤ Qd * Qs := Nat.mul_le_mul hd hs
  have h6 : (m + a) * (β + 4) ≤ (m + a) * (7 * m) := Nat.mul_le_mul_left _ hβ
  have h7 : 0 ≤ m * m := Nat.zero_le _
  have h8 : 0 ≤ a * m := Nat.zero_le _
  nlinarith

/-- With no offline queries and `q_total ≤ q_on`, `stepCostBudgetSplit` equals `stepCostBudget`
plus the random-oracle table term `2 ^ 13 * q_total * (bits (2 * q_total + 1) + 4)`. -/
theorem stepCostBudgetSplit_eq_of_noOff (S : Setup) (b : QueryBudget) (hon : b.q_total ≤ b.q_on) :
    stepCostBudgetSplit S b 0 =
      stepCostBudget S b +
        2 ^ 13 * b.q_total * (ReductionDsl.bits (2 * b.q_total + 1) + 4) := by
  have h1 : min b.q_on b.q_total = b.q_total := by omega
  unfold stepCostBudgetSplit stepCostBudget
  simp only [h1, Nat.zero_min, zero_add, Nat.zero_mul, Nat.mul_zero, add_zero]
  ring

/-- `stepCostBudgetSplit` is at most `stepCostBudget` when `q_on + q_off ≤ q_total` and
`bits (q_off + 2 * q_on + 1) + 4 ≤ 7 * q_off`. -/
theorem stepCostBudgetSplit_le (S : Setup) (b : QueryBudget) (q_off : ℕ)
    (hsum : b.q_on + q_off ≤ b.q_total)
    (hβ : ReductionDsl.bits (q_off + 2 * b.q_on + 1) + 4 ≤ 7 * q_off) :
    stepCostBudgetSplit S b q_off ≤ stepCostBudget S b := by
  have h1 : min b.q_on b.q_total = b.q_on := by omega
  have h2 : min q_off b.q_total = q_off := by omega
  unfold stepCostBudgetSplit stepCostBudget
  simp only [h1, h2]
  exact split_aux _ _ _ _ _ _ _ _ _ hsum hβ (by omega) (by omega)

end SignalPqxdh.Security

namespace CryptoVerification.E2E

private theorem adapter_aux (a r q s d Gon Gq : ℕ) (hq : a + r ≤ q) (hG : Gon ≤ Gq)
    (hG' : 2 ^ 12 ≤ Gq) :
    2 ^ 6 * (a + s + d + 1) * Gon + 2 ^ 12 * r ≤ 2 ^ 6 * (q + s + d + 1) * Gq := by
  have h1 : (a + s + d + 1) * Gon ≤ (a + s + d + 1) * Gq := Nat.mul_le_mul_left _ hG
  have h2 : 2 ^ 12 * r ≤ Gq * r := Nat.mul_le_mul_right _ hG'
  have h3 : (a + s + d + 1) * Gq + r * Gq ≤ (q + s + d + 1) * Gq := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- With no random-oracle queries and `q_total ≤ q_on`, `bhAdapterCostBudgetByKind` equals
`bhAdapterCostBudget`. -/
theorem bhAdapterCostBudgetByKind_eq_of_noRo (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) (hon : b.q_total ≤ b.q_on) (hro : b.q_ro = 0) :
    bhAdapterCostBudgetByKind S b qStart qDR ℓ = bhAdapterCostBudget S b qStart qDR ℓ := by
  have h1 : min b.q_on b.q_total = b.q_total := by omega
  unfold bhAdapterCostBudgetByKind bhAdapterCostBudget
  simp only [h1, hro, Nat.zero_min, Nat.mul_zero, add_zero]

/-- `bhAdapterCostBudgetByKind` is at most `bhAdapterCostBudget` whenever `q_on + q_ro ≤ q_total`. -/
theorem bhAdapterCostBudgetByKind_le (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) (hsum : b.q_on + b.q_ro ≤ b.q_total) :
    bhAdapterCostBudgetByKind S b qStart qDR ℓ ≤ bhAdapterCostBudget S b qStart qDR ℓ := by
  have h1 : min b.q_on b.q_total = b.q_on := by omega
  have h2 : min b.q_ro b.q_total = b.q_ro := by omega
  unfold bhAdapterCostBudgetByKind bhAdapterCostBudget
  simp only [h1, h2]
  exact adapter_aux _ _ _ _ _ _ _ hsum (by omega) (by omega)

private theorem e2e_aux (a m q s d Fa Fq na nb Ta Tq β : ℕ) (hq : a + m ≤ q) (hsd : s + d ≤ q)
    (hF : Fa ≤ Fq) (hFq : q + 1 ≤ Fq) (hn : na ≤ nb) (hT : Ta ≤ Tq)
    (hβ : 16 * (β + 4) ≤ m) :
    2 ^ 10 * (a + s + d + 1) * Fa + 2 ^ 13 * (m + (a + s + d)) * (β + 4) + 2 ^ 13 * na * Ta ≤
      2 ^ 10 * (q + s + d + 1) * Fq + 2 ^ 13 * nb * Tq := by
  have h1 : (a + s + d + 1) * Fa ≤ (a + s + d + 1) * Fq := Nat.mul_le_mul_left _ hF
  have h2 : 16 * ((m + (a + s + d)) * (β + 4)) ≤ (m + (a + s + d)) * m := by
    rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ hβ
  have h3 : (m + (a + s + d)) * m ≤ 2 * (q + 1) * m := Nat.mul_le_mul_right _ (by omega)
  have h4 : (q + 1) * m ≤ Fq * m := Nat.mul_le_mul_right _ hFq
  have h5 : (a + s + d + 1) * Fq + m * Fq ≤ (q + s + d + 1) * Fq := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have h6 : na * Ta ≤ nb * Tq := Nat.mul_le_mul hn hT
  nlinarith

/-- With no random-oracle queries and `q_total ≤ q_on`, `bhE2ECostBudgetByKind` equals
`bhE2ECostBudget` plus `2 ^ 13 * Q * (bits (2 * Q + 1) + 4)` for `Q = q_total + qStart + qDR`. -/
theorem bhE2ECostBudgetByKind_eq_of_noRo (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) (hon : b.q_total ≤ b.q_on) (hro : b.q_ro = 0) :
    bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ =
      bhE2ECostBudget S b qStart qDR qInst qep ℓ +
        2 ^ 13 * (b.q_total + qStart + qDR) *
          (ReductionDsl.bits (2 * (b.q_total + qStart + qDR) + 1) + 4) := by
  have h1 : min b.q_on b.q_total = b.q_total := by omega
  unfold bhE2ECostBudgetByKind bhE2ECostBudget
  simp only [h1, hro, Nat.zero_min, zero_add]
  ring

/-- `bhE2ECostBudgetByKind` is at most `bhE2ECostBudget` when `q_on + q_ro ≤ q_total`,
`qStart + qDR ≤ q_total`, and `16 * (bits (q_ro + 2 * (q_on + qStart + qDR) + 1) + 4) ≤ q_ro`. -/
theorem bhE2ECostBudgetByKind_le (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) (hsum : b.q_on + b.q_ro ≤ b.q_total)
    (hsd : qStart + qDR ≤ b.q_total)
    (hβ : 16 * (ReductionDsl.bits (b.q_ro + 2 * (b.q_on + qStart + qDR) + 1) + 4) ≤ b.q_ro) :
    bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ ≤
      bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
  have h1 : min b.q_on b.q_total = b.q_on := by omega
  have h2 : min b.q_ro b.q_total = b.q_ro := by omega
  unfold bhE2ECostBudgetByKind bhE2ECostBudget
  simp only [h1, h2]
  refine e2e_aux _ _ _ _ _ _ _ _ _ _ _ _ hsum hsd ?_ ?_ ?_ ?_ hβ
  · gcongr <;> omega
  · omega
  · omega
  · omega

end CryptoVerification.E2E
