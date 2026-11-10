/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.InternalTop
public import ProofLib.SepLogic.WPFrozen
public import ProofLib.SepLogic.WPp
public import ProofLib.SepLogic.Entry
public import ProofLib.SepLogic.SymWP
public import ProofLib.BV
public import ProofLib.BV.WidthNorm

/-!
# Verification of `hashbrown_with_capacity`

Proves `capacity_to_buckets` and table-layout arithmetic, post-allocation heap-table assembly
(`U64MapRep_of_alloc_memset`), cold panic helper contracts, and `hashbrown_with_capacity`
(`Infallible` and general).
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown

/-! ## `capacity_to_buckets` and Table-Layout Arithmetic -/

@[simp] theorem capToBucketMask_zero : capToBucketMask 0 = 0#64 := rfl

theorem capToBucketMask_valid {cap : Nat} (hpos : 0 < cap) (hle : cap ≤ MaxHashbrownCapacity) :
    ValidBucketMask (capToBucketMask cap) := by
  have hz : cap ≠ 0 := by omega
  by_cases h4 : cap < 4
  · simp only [capToBucketMask, hz, h4, ↓reduceIte]; exact ⟨2, by decide, by decide, rfl⟩
  · by_cases h8 : cap < 8
    · simp only [capToBucketMask, hz, h4, h8, ↓reduceIte]; exact ⟨3, by decide, by decide, rfl⟩
    · by_cases h15 : cap < 15
      · simp only [capToBucketMask, hz, h4, h8, h15, ↓reduceIte]; exact ⟨4, by decide, by decide, rfl⟩
      · simp only [capToBucketMask, hz, h4, h8, h15, ↓reduceIte]
        have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
        have hadj_ne : (cap * 8) / 7 - 1 ≠ 0 := by omega
        have := (Nat.le_log2 hadj_ne).mpr (by omega : 2 ^ 4 ≤ (cap * 8) / 7 - 1)
        have := (Nat.log2_lt hadj_ne).mpr (by omega : (cap * 8) / 7 - 1 < 2 ^ 58)
        exact ⟨Nat.log2 ((cap * 8) / 7 - 1) + 1, by omega, by omega, rfl⟩

theorem capToBucketMask_ne_zero {cap : Nat} (hpos : 0 < cap) (hle : cap ≤ MaxHashbrownCapacity) :
    capToBucketMask cap ≠ 0#64 := (capToBucketMask_valid hpos hle).ne_zero

theorem capToBucketMask_small_buckets {cap : BitVec 64} (hne : cap ≠ 0#64) (hlt15 : cap < 15#64) :
    (if cap < 4#64 then 4#64 else (cap &&& 8#64) + 8#64) =
      BitVec.ofNat 64 ((capToBucketMask cap.toNat).toNat + 1) := by
  have hpos := (Nat.eq_zero_or_pos cap.toNat).resolve_left fun hz => hne (BitVec.eq_of_toNat_eq hz)
  have hlt15_nat : cap.toNat < 15 := BitVec.lt_def.mp hlt15; have hz : cap.toNat ≠ 0 := by omega
  by_cases h4 : cap < 4#64
  · have h4t : cap.toNat < 4 := BitVec.lt_def.mp h4
    simp only [h4, capToBucketMask, hz, h4t, ↓reduceIte]; decide
  · have h4n : ¬ (cap.toNat < 4) := fun h => h4 (BitVec.lt_def.mpr h)
    by_cases h8n : cap.toNat < 8
    · have hand : cap &&& 8#64 = 0#64 := by bv_bits
      simp only [h4, hand, capToBucketMask, hz, h4n, h8n, ↓reduceIte]; decide
    · have hand : cap &&& 8#64 = 8#64 := by bv_bits
      simp only [h4, hand, capToBucketMask, hz, h4n, h8n, hlt15_nat, ↓reduceIte]; decide

theorem umulh_div7_nat {n : Nat} (hn : n < 2 ^ 64) :
    let q := (n * 0x2492492492492493) / 2 ^ 64
    ((q + (n - q) / 2) / 4) = n / 7 := by
  dsimp only; let M := 0x2492492492492493
  have hM : 7 * M = 2 ^ 64 + 5 := by decide
  have hq_le : (n * M) / 2 ^ 64 ≤ n := Nat.div_le_of_le_mul <| by
    calc n * M ≤ n * 2 ^ 64 := Nat.mul_le_mul_left n (by decide)
      _ = 2 ^ 64 * n := Nat.mul_comm _ _
  have hstep1 : (n * M) / 2 ^ 64 + (n - (n * M) / 2 ^ 64) / 2 = (n + (n * M) / 2 ^ 64) / 2 := by omega
  have hstep2 : n + (n * M) / 2 ^ 64 = (n * (2 ^ 64 + M)) / 2 ^ 64 := by
    have hd := Nat.add_mul_div_left (n * M) n (by decide : 0 < 2 ^ 64)
    rw [Nat.left_distrib, Nat.mul_comm n (2 ^ 64)]; omega
  rw [hstep1, hstep2, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      show 2 ^ 64 * 2 * 4 = 8 * 2 ^ 64 by decide]
  let k := n / 7; let r := n % 7
  have hnr : n = 7 * k + r := (Nat.div_add_mod n 7).symm; have hr : r < 7 := Nat.mod_lt n (by decide)
  have h7M : 7 * (2 ^ 64 + M) = 8 * 2 ^ 64 + 5 := by omega
  have hexpand : n * (2 ^ 64 + M) = (5 * k + r * (2 ^ 64 + M)) + (8 * 2 ^ 64) * k := by
    calc n * (2 ^ 64 + M) = (7 * k + r) * (2 ^ 64 + M) := by rw [← hnr]
      _ = k * (7 * (2 ^ 64 + M)) + r * (2 ^ 64 + M) := by
          rw [Nat.right_distrib, Nat.mul_assoc, ← Nat.mul_assoc 7 k, Nat.mul_comm 7 k, Nat.mul_assoc]
      _ = k * (8 * 2 ^ 64 + 5) + r * (2 ^ 64 + M) := by rw [h7M]
      _ = (5 * k + r * (2 ^ 64 + M)) + (8 * 2 ^ 64) * k := by rw [Nat.left_distrib]; omega
  have hrem_lt : 5 * k + r * (2 ^ 64 + M) < 8 * 2 ^ 64 := by
    have h7rem : 7 * (5 * k + r * (2 ^ 64 + M)) = 5 * n + r * (8 * 2 ^ 64) := by
      calc 7 * (5 * k + r * (2 ^ 64 + M))
        _ = 5 * (7 * k) + r * (7 * (2 ^ 64 + M)) := by
            rw [Nat.left_distrib, show 7 * (5 * k) = 5 * (7 * k) by omega,
                show 7 * (r * (2 ^ 64 + M)) = r * (7 * (2 ^ 64 + M)) by
                  rw [← Nat.mul_assoc, Nat.mul_comm 7 r, Nat.mul_assoc]]
        _ = 5 * (7 * k + r) + r * (8 * 2 ^ 64) := by rw [h7M, Nat.left_distrib, Nat.left_distrib]; omega
        _ = 5 * n + r * (8 * 2 ^ 64) := by rw [← hnr]
    omega
  rw [hexpand, Nat.add_mul_div_left _ _ (by decide : 0 < 8 * 2 ^ 64),
      Nat.div_eq_of_lt hrem_lt, Nat.zero_add]

theorem umulh_div7_bv {cap : BitVec 64} (hhi : cap >>> 61 = 0#64) :
    let n := cap <<< 3
    let q := BitVec.setWidth 64 ((BitVec.setWidth 128 n * BitVec.setWidth 128 0x2492492492492493#64) >>> 64)
    (q + ((n - q) >>> 1)) >>> 2 = BitVec.ofNat 64 ((cap.toNat * 8) / 7) := by
  dsimp only
  have hcap_lt : cap.toNat < 2 ^ 61 := by
    have := congrArg BitVec.toNat hhi
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at this; omega
  have hn_lt : cap.toNat * 8 < 2 ^ 64 := by omega
  have hn_nat : (cap <<< 3).toNat = cap.toNat * 8 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn_lt]
  rw [BitVec.setWidth_umulh, hn_nat, show (0x2492492492492493#64).toNat = 0x2492492492492493 from rfl,
      Nat.shiftRight_eq_div_pow]
  let n := cap.toNat * 8; let q := (n * 0x2492492492492493) / 2 ^ 64
  have hq_le : q ≤ n := Nat.div_le_of_le_mul <| by
    calc n * 0x2492492492492493 ≤ n * 2 ^ 64 := Nat.mul_le_mul_left n (by decide)
      _ = 2 ^ 64 * n := Nat.mul_comm _ _
  have hq_bv : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub_nat : (cap <<< 3 - BitVec.ofNat 64 q).toNat = n - q := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn_nat, hq_bv]; exact hq_le), hn_nat, hq_bv]
  have hsh1_nat : ((cap <<< 3 - BitVec.ofNat 64 q) >>> 1).toNat = (n - q) / 2 := by
    rw [BitVec.toNat_ushiftRight, hsub_nat, Nat.shiftRight_eq_div_pow]
  have hadd_nat : (BitVec.ofNat 64 q + ((cap <<< 3 - BitVec.ofNat 64 q) >>> 1)).toNat = q + (n - q) / 2 := by
    rw [BitVec.toNat_add, hq_bv, hsh1_nat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, hadd_nat, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact umulh_div7_nat hn_lt

theorem allOnes_lsr_clz_eq {x : BitVec 64} (hx : x ≠ 0#64) :
    0xffffffffffffffff#64 >>> (x.clz.toNat % 64) = BitVec.ofNat 64 (2 ^ (Nat.log2 x.toNat + 1) - 1) := by
  have hx_pos : x.toNat ≠ 0 := fun hz => hx (BitVec.eq_of_toNat_eq hz)
  have hclz_nat : x.clz.toNat < 64 := BitVec.lt_def.mp (BitVec.clz_lt_iff_ne_zero.mpr hx)
  have hlo : 2 ^ (63 - x.clz.toNat) ≤ x.toNat := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide) hx
  have hhi : x.toNat < 2 ^ (63 - x.clz.toNat + 1) := by
    rw [← show 64 - x.clz.toNat = 63 - x.clz.toNat + 1 by omega]; exact BitVec.toNat_lt_two_pow_sub_clz
  have hlog : Nat.log2 x.toNat = 63 - x.clz.toNat := (Nat.log2_eq_iff hx_pos).mpr ⟨hlo, hhi⟩
  apply BitVec.eq_of_toNat_eq
  rw [show x.clz.toNat % 64 = 63 - Nat.log2 x.toNat by omega, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, show (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 from rfl]
  let k := Nat.log2 x.toNat
  have hpow64 : 2 ^ 64 = 2 ^ (k + 1) * 2 ^ (63 - k) := by
    conv => lhs; rw [show 64 = (k + 1) + (63 - k) by omega]
    exact Nat.pow_add 2 (k + 1) (63 - k)
  have h2pos := Nat.two_pow_pos (63 - k); have h2kpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
  have hp : 2 ^ (k + 1) * 2 ^ (63 - k) = 2 ^ (63 - k) + 2 ^ (63 - k) * (2 ^ (k + 1) - 1) := by
    calc 2 ^ (k + 1) * 2 ^ (63 - k) = (1 + (2 ^ (k + 1) - 1)) * 2 ^ (63 - k) := by congr 1; omega
      _ = 2 ^ (63 - k) + 2 ^ (63 - k) * (2 ^ (k + 1) - 1) := by rw [Nat.right_distrib, Nat.one_mul, Nat.mul_comm]
  rw [show 2 ^ 64 - 1 = (2 ^ (63 - k) - 1) + 2 ^ (63 - k) * (2 ^ (k + 1) - 1) by omega,
      Nat.add_mul_div_left _ _ h2pos, Nat.div_eq_of_lt (by omega : 2 ^ (63 - k) - 1 < 2 ^ (63 - k)),
      Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : Nat.log2 x.toNat + 1 ≤ 64); omega

theorem capToBucketMask_large_ok {cap : BitVec 64}
    (hge15 : ¬ (cap < 15#64)) (hle : cap.toNat ≤ MaxHashbrownCapacity) :
    let adj := (cap.toNat * 8) / 7
    cap >>> 61 = 0#64 ∧ BitVec.ofNat 64 adj - 1#64 ≠ 0#64 ∧
    capToBucketMask cap.toNat = 0xffffffffffffffff#64 >>> ((BitVec.ofNat 64 adj - 1#64).clz.toNat % 64) ∧
    ¬ (0xffffffffffffffff#64 < capToBucketMask cap.toNat) ∧ (capToBucketMask cap.toNat ≤ 0x0ffffffffffffffe#64) ∧
    capToBucketMask cap.toNat + 1#64 = BitVec.ofNat 64 ((capToBucketMask cap.toNat).toNat + 1) := by
  dsimp only
  have hge15_nat := (Nat.lt_or_ge cap.toNat 15).resolve_left fun hlt => hge15 (BitVec.lt_def.mpr hlt)
  have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  have hsh61 : cap >>> 61 = 0#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  let adj := (cap.toNat * 8) / 7
  have hadj_lo : 17 ≤ adj := by omega
  have hadj_hi : adj ≤ 2 ^ 58 := by omega
  have hsub_eq : BitVec.ofNat 64 adj - 1#64 = BitVec.ofNat 64 (adj - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)]; simp only [BitVec.toNat_ofNat]; omega
  have hsub_ne : BitVec.ofNat 64 adj - 1#64 ≠ 0#64 := by
    rw [hsub_eq]; intro hz; have := congrArg BitVec.toNat hz; simp only [BitVec.toNat_ofNat] at this; omega
  have hmask_eq : capToBucketMask cap.toNat = 0xffffffffffffffff#64 >>> ((BitVec.ofNat 64 adj - 1#64).clz.toNat % 64) := by
    rw [allOnes_lsr_clz_eq hsub_ne, show (BitVec.ofNat 64 adj - 1#64).toNat = adj - 1 by
      rw [hsub_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
    simp only [capToBucketMask, show cap.toNat ≠ 0 by omega, show ¬ (cap.toNat < 4) by omega,
      show ¬ (cap.toNat < 8) by omega, show ¬ (cap.toNat < 15) by omega, ↓reduceIte]; rfl
  obtain ⟨exp, hlo_e, hhi_e, hbm_e⟩ := capToBucketMask_valid (by omega) hle
  have hbm_nat : (capToBucketMask cap.toNat).toNat = 2 ^ exp - 1 := by
    have := ValidBucketMask.buckets_eq hlo_e hhi_e hbm_e; omega
  have h258 : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi_e
  have hle_lim : capToBucketMask cap.toNat ≤ 0x0ffffffffffffffe#64 := by
    rw [BitVec.le_def, hbm_nat, show (0x0ffffffffffffffe#64).toNat = 0x0ffffffffffffffe from rfl]; omega
  have hadd1 : capToBucketMask cap.toNat + 1#64 = BitVec.ofNat 64 ((capToBucketMask cap.toNat).toNat + 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hbm_nat]
    change (2 ^ exp - 1 + 1) % 2 ^ 64 = (BitVec.ofNat 64 (2 ^ exp - 1 + 1)).toNat; simp only [BitVec.toNat_ofNat]
  exact ⟨hsh61, hsub_ne, hmask_eq, fun h => absurd h (BitVec.not_lt.mpr (by bv_arith)), hle_lim, hadd1⟩

theorem ValidBucketMask.tableAlloc_machine_ok {bm : BitVec 64} (hbm : ValidBucketMask bm) :
    let buckets := bm.toNat + 1; let bBV := BitVec.ofNat 64 buckets
    (bBV <<< 4 = BitVec.ofNat 64 (16 * buckets)) ∧ (bBV + 8#64 = BitVec.ofNat 64 (buckets + 8)) ∧
    ((buckets + 8) + 16 * buckets = tableAllocBytes bm) ∧ (tableAllocBytes bm ≤ 0x7ffffffffffffff8) ∧
    (bBV - 1#64 = bm) ∧
    ((if bBV < 9#64 then bBV - 1#64 else ((bBV >>> 3) <<< 3) - (bBV >>> 3)) = bucketMaskToCapacityBV bm) := by
  dsimp only; have hne := hbm.ne_zero; obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hbm
  have hbuckets := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hpow_lo : 4 ≤ 2 ^ exp := show 2 ^ 2 ≤ 2 ^ exp from Nat.pow_le_pow_right (by decide) hlo
  have hpow_hi : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi
  let buckets := bm.toNat + 1
  have hsh4 : BitVec.ofNat 64 buckets <<< 4 = BitVec.ofNat 64 (16 * buckets) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hadd8 : BitVec.ofNat 64 buckets + 8#64 = BitVec.ofNat 64 (buckets + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsub1 : BitVec.ofNat 64 buckets - 1#64 = bm := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : buckets < 2 ^ 64)]; omega)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : buckets < 2 ^ 64)]; omega
  refine ⟨hsh4, hadd8, by simp only [tableAllocBytes, hne, ↓reduceIte]; omega,
    by simp only [tableAllocBytes, hne, ↓reduceIte]; omega, hsub1, ?_⟩
  rw [hsub1, show BitVec.ofNat 64 buckets = bm + 1#64 by rw [← hsub1]; bv_lin,
      show (((bm + 1#64) >>> 3) <<< 3) - ((bm + 1#64) >>> 3) = ((bm + 1#64) >>> 3) * 7#64 by bv_lin]
  unfold bucketMaskToCapacityBV
  have hcond : (bm + 1#64 < 9#64) ↔ (bm < 8#64) := by
    have : bm.toNat < 2 ^ 58 := by omega
    constructor <;> intro h <;> bv_arith
  by_cases hc : bm < 8#64
  · simp only [hcond.mpr hc, hc, ↓reduceIte]
  · simp only [show ¬ (bm + 1#64 < 9#64) from fun h => hc (hcond.mp h), hc, ↓reduceIte]

theorem capToBucketMask_overflow_cases {cap : BitVec 64} (hov : MaxHashbrownCapacity < cap.toNat) :
    ¬ (cap < 15#64) ∧ (cap >>> 61 ≠ 0#64 ∨ (cap >>> 61 = 0#64 ∧
      let adj := (cap.toNat * 8) / 7
      BitVec.ofNat 64 adj - 1#64 ≠ 0#64 ∧
      let mask := 0xffffffffffffffff#64 >>> ((BitVec.ofNat 64 adj - 1#64).clz.toNat % 64)
      (0x0ffffffffffffffe#64 < mask ∨ (mask = BitVec.ofNat 64 (2 ^ 59 - 1) ∧ mask ≤ 0x0ffffffffffffffe#64)))) := by
  have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  refine ⟨fun hlt => by have : cap.toNat < 15 := BitVec.lt_def.mp hlt; omega, ?_⟩
  by_cases hsh : cap >>> 61 = 0#64
  · right; refine ⟨hsh, ?_⟩
    have hcap_lt61 : cap.toNat < 2 ^ 61 := by
      have := congrArg BitVec.toNat hsh
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at this; omega
    let adj := (cap.toNat * 8) / 7
    have hadj_lo : 2 ^ 58 + 1 ≤ adj := by omega
    have hadj_hi : adj < 2 ^ 62 := by omega
    have hsub_eq : BitVec.ofNat 64 adj - 1#64 = BitVec.ofNat 64 (adj - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_ofNat]; omega
    have hsub_ne : BitVec.ofNat 64 adj - 1#64 ≠ 0#64 := by
      rw [hsub_eq]; intro hz; have := congrArg BitVec.toNat hz; simp only [BitVec.toNat_ofNat] at this; omega
    refine ⟨hsub_ne, ?_⟩
    rw [allOnes_lsr_clz_eq hsub_ne, show (BitVec.ofNat 64 adj - 1#64).toNat = adj - 1 by
      rw [hsub_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
    have hadj1_ne : adj - 1 ≠ 0 := by omega
    have hlog_lo : 58 ≤ Nat.log2 (adj - 1) := (Nat.le_log2 hadj1_ne).mpr (by omega)
    have hlog_hi : Nat.log2 (adj - 1) < 62 := (Nat.log2_lt hadj1_ne).mpr (by omega)
    let exp := Nat.log2 (adj - 1) + 1
    by_cases he59 : exp = 59
    · right; change BitVec.ofNat 64 (2 ^ exp - 1) = _ ∧ BitVec.ofNat 64 (2 ^ exp - 1) ≤ _
      rw [he59]; exact ⟨rfl, by decide⟩
    · left
      have hpow_lo : 2 ^ 60 ≤ 2 ^ exp := Nat.pow_le_pow_right (by decide) (by omega)
      have hpow_hi : 2 ^ exp ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega)
      change 0x0ffffffffffffffe#64 < BitVec.ofNat 64 (2 ^ exp - 1)
      rw [BitVec.lt_def]; change 0x0ffffffffffffffe < (BitVec.ofNat 64 (2 ^ exp - 1)).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · exact Or.inl hsh

theorem capToBucketMask_succ_capacity_eq_nextResizeMask {bm : BitVec 64}
    (hbm : bm = 0#64 ∨ ValidBucketMask bm) (hlt : bucketMaskToCapacity bm < MaxHashbrownCapacity) :
    bucketMaskToCapacity bm + 1 ≤ MaxHashbrownCapacity ∧
    capToBucketMask (bucketMaskToCapacity bm + 1) = nextResizeMask bm := by
  refine ⟨by omega, ?_⟩; rcases hbm with rfl | hv
  · decide
  · have hne := hv.ne_zero; obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hv
    have hexp_lt58 : exp < 58 := by
      by_cases h58 : exp = 58
      · subst h58; rw [hbm_eq, show bucketMaskToCapacity (BitVec.ofNat 64 (2 ^ 58 - 1)) = MaxHashbrownCapacity by decide] at hlt; omega
      · omega
    have hcap := ValidBucketMask.capacity_eq hlo hhi hbm_eq
    have hbkt := ValidBucketMask.buckets_eq hlo hhi hbm_eq
    by_cases he2 : exp = 2
    · subst he2; subst hbm_eq; decide
    · by_cases he3 : exp = 3
      · subst he3; subst hbm_eq; decide
      · simp only [he2, ↓reduceIte] at hcap
        have hpow_lo : 2 ≤ 2 ^ (exp - 3) := show 2 ^ 1 ≤ 2 ^ (exp - 3) from Nat.pow_le_pow_right (by decide) (by omega)
        simp only [capToBucketMask, show bucketMaskToCapacity bm + 1 ≠ 0 by omega,
          show ¬ (bucketMaskToCapacity bm + 1 < 4) by omega, show ¬ (bucketMaskToCapacity bm + 1 < 8) by omega,
          show ¬ (bucketMaskToCapacity bm + 1 < 15) by omega, nextResizeMask, hne, ↓reduceIte]
        have hpow8 : 2 ^ (exp - 3) * 8 = 2 ^ exp := by
          calc 2 ^ (exp - 3) * 8 = 2 ^ ((exp - 3) + 3) := (Nat.pow_add 2 (exp - 3) 3).symm
            _ = 2 ^ exp := by rw [show (exp - 3) + 3 = exp by omega]
        have hadj : ((bucketMaskToCapacity bm + 1) * 8) / 7 - 1 = 2 ^ exp := by
          rw [hcap, show (7 * 2 ^ (exp - 3) + 1) * 8 = 8 + 7 * 2 ^ exp by
            calc (7 * 2 ^ (exp - 3) + 1) * 8 = 7 * (2 ^ (exp - 3) * 8) + 8 := by omega
              _ = 8 + 7 * 2 ^ exp := by rw [hpow8]; omega,
            Nat.add_mul_div_left 8 (2 ^ exp) (by decide : 0 < 7)]; omega
        rw [hadj, Nat.log2_two_pow, hbkt, Nat.pow_succ, Nat.mul_comm]

/-! ## Post-Allocation Heap-Table Assembly -/

theorem memRegion_tableAllocBytes_split {bm : BitVec 64} (allocPtr : BitVec 64) (hbm : ValidBucketMask bm) :
    memRegion allocPtr (tableAllocBytes bm) =
      (memRegion allocPtr (16 * (bm.toNat + 1)) ∗
       memRegion (allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (bm.toNat + 1 + 8)) := by
  have hne := hbm.ne_zero; obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hbm
  have hbkt := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hpow_hi : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi
  rw [show tableAllocBytes bm = 16 * (bm.toNat + 1) + (bm.toNat + 1 + 8) by
    simp only [tableAllocBytes, hne, ↓reduceIte]; omega]
  exact memRegion_split allocPtr (16 * (bm.toNat + 1)) (bm.toNat + 1 + 8) (by omega)

theorem U64MapRep_of_alloc_memset (pl : Obj.Placement) (A : HbAlloc)
    (mapPtr allocPtr ctrlPtr bm : BitVec 64) (hbm : ValidBucketMask bm)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hctrl : ctrlPtr = allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) :
    hbRodata pl ∗ U64MapStruct mapPtr ctrlPtr bm (bucketMaskToCapacityBV bm) 0#64 ∗
    A.Block allocPtr (tableAllocBytes bm) 8 ∗ memRegion allocPtr (16 * (bm.toNat + 1)) ∗
    (ctrlPtr ↦ₛ List.replicate (bm.toNat + 1 + 8) 0xff#8) ⊢
      U64MapRep pl A mapPtr [] bm 0 ∗ hbRodata pl := by
  have hne := hbm.ne_zero; obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hbm
  have hbkt := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hpow_hi : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi
  rw [show tableAllocBytes bm = 17 * (bm.toNat + 1) + 8 by simp only [tableAllocBytes, hne, ↓reduceIte]]
  refine Entails.trans (sepConj_mono (hbRodata_dup pl)
    (sepConj_mono_right (sepConj_mono (A.block_valid allocPtr (17 * (bm.toNat + 1) + 8) 8)
      (sepConj_mono_left (memRegion_to_slotsDownFrom (bm.toNat + 1) allocPtr (by omega)))))) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (⌜allocPtr ≠ 0#64 ∧ allocPtr.toNat % 8 = 0 ∧ allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64⌝ ∗
     ((∃∗ slots : List (BitVec 64 × BitVec 64),
        ⌜slots.length = bm.toNat + 1⌝ ∗ slotsDownFrom (allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) slots) ∗
      (hbRodata pl ∗ U64MapStruct mapPtr ctrlPtr bm (bucketMaskToCapacityBV bm) 0#64 ∗
       A.Block allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ (ctrlPtr ↦ₛ List.replicate (bm.toNat + 1 + 8) 0xff#8)))) ∗
    hbRodata pl by ac_rfl)) (sepConj_mono_left (Entails.pure_left fun ⟨halloc_ne, halloc_al, halloc_nw⟩ => ?_))
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun slots => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hslots_len => ?_
  unfold U64MapRep
  simp only [hne, ↓reduceIte]; refine Entails.pure_right ⟨hal, hnw, Map64Wf.nil⟩ ?_
  refine Entails.trans (Entails.of_eq (show _ =
    hbRodata pl ∗ (U64MapStruct mapPtr ctrlPtr bm (bucketMaskToCapacityBV bm) 0#64 ∗
     A.Block allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
     slotsDownFrom (allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) slots ∗
     (ctrlPtr ↦ₛ List.replicate (bm.toNat + 1 + 8) 0xff#8)) by ac_rfl)) (sepConj_mono_right ?_)
  rw [← hctrl]
  exact Entails.sepExists_right
    { allocPtr := allocPtr, ctrlPtr := ctrlPtr, growthLeft := bucketMaskToCapacityBV bm,
      items := 0#64, ctrl := List.replicate (bm.toNat + 1 + 8) tagEmpty, slots := slots }
    (Entails.pure_right ⟨SwissTableInv_init_of_mask ⟨exp, hlo, hhi, hbm_eq⟩ hslots_len,
      by simp [bucketMaskToCapacity], halloc_ne, halloc_al, halloc_nw, hctrl⟩ (Entails.refl _))

/-! ## Cold Panic Helper Subroutines (`capacity_overflow` and `alloc_err`) -/

def hbColdPanicSpec (φ : Prop) : Spec Unit where
  pre := fun _ s0 => ⌜s0.readReg32 .x0 = 1#32 ∧ φ⌝ ∗ stackAt s0.sp 16
  post := fun _ _ _ => ⌜False⌝
  onPanic := fun _ _ _ => ⌜φ⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem satisfies_pure_frame_of_sepConj {φ : Prop} {P R : SepProp} {m : Memory}
    (hφ : φ) (hm : m ⊨ P ∗ R) : m ⊨ ⌜φ⌝ ∗ R :=
  (satisfies_pure_sepConj φ R m).mpr ⟨hφ, ((satisfies_pure_sepConj True R m).mp (satisfies_true_sepConj hm)).2⟩

theorem hbCapOverflow_infallible_ok (P : HbPlaced) (X : String → Option (State → State)) {φ : Prop}
    (hpan : ((hbProg11 P).rebase P.pl11.base X).externAt? (P.pl.ρ hbPanicFmtSym) = some Rust.panicked) :
    let prog := (hbProg11 P).rebase P.pl11.base X
    subroutine_ok prog (prog.fnAddr hbCapOverflowSym) (hbColdPanicSpec φ) := by
  have hP := P.placeable11; have hb : (hbProg11 P).base = P.pl11.base := rfl
  dsimp only; wpp_entry; apply SepWPp.of_sepWP_at (mid := P.pl.ρ hbPanicFmtSym)
  rw [stackAt_eq_cells s0.sp 2]; cells_unfold; dsimp only [Nat.reduceMul, Nat.reduceSub]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_; wp_steps
  refine SepWP.done (by dsimp only [hbPanicFmtSym]; simp; bv_lin)
    (by simp [hrun]) fun hpcm hrunm =>
      SepWPp.panic hrunm (by rwa [hpcm]) fun hmf => satisfies_pure_frame_of_sepConj ‹φ› hmf

theorem hbFallibilityAllocErr_infallible_ok (P : HbPlaced) (X : String → Option (State → State)) {φ : Prop}
    (hpan : ((hbProg12 P).rebase P.pl12.base X).externAt? (P.pl.ρ hbAllocErrSym) = some Rust.panicked) :
    let prog := (hbProg12 P).rebase P.pl12.base X
    subroutine_ok prog (prog.fnAddr hbFallibilityAllocErrSym) (hbColdPanicSpec φ) := by
  have hP := P.placeable12; have hb : (hbProg12 P).base = P.pl12.base := rfl
  dsimp only; wpp_entry; apply SepWPp.of_sepWP_at (mid := P.pl.ρ hbAllocErrSym)
  rw [stackAt_eq_cells s0.sp 2]; cells_unfold; dsimp only [Nat.reduceMul, Nat.reduceSub]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_; wp_steps
  refine SepWP.done (by dsimp only [hbAllocErrSym]; simp; bv_lin)
    (by simp [hrun]) fun hpcm hrunm =>
      SepWPp.panic hrunm (by rwa [hpcm]) fun hmf => satisfies_pure_frame_of_sepConj ‹φ› hmf

theorem hbCapOverflow_crossBlock_ok (P : HbPlaced) {i : Nat} {prog_i : Program}
    (X : String → Option (State → State)) (hi : i < 13)
    (hreb_i : prog_i = hashbrownLib.blockProgram P.mpl i X) {φ : Prop}
    (hpan : prog_i.externAt? (P.pl.ρ hbPanicFmtSym) = some Rust.panicked) :
    subroutine_ok prog_i P.pl11.base (hashbrownLib.withCodeLoaded P.mpl (hbColdPanicSpec φ)) := by
  have hP := P.placeable11; have hb : (hbProg11 P).base = P.pl11.base := rfl
  have hpan11 : ((hbProg11 P).rebase P.pl11.base X).externAt? (P.pl.ρ hbPanicFmtSym) =
      some Rust.panicked := by
    rw [hbExternAt?_transfer P hi (by decide) hreb_i (hbProg11_rebase P X)]; exact hpan
  have hfn := hbCapOverflow_infallible_ok P X (φ := φ) hpan11
  dsimp only at hfn; simp only [hbCapOverflowSym, arm64_norm] at hfn
  exact hbSubroutineOk_crossBlock P hi (by decide) hreb_i (hbProg11_rebase P X)
    (hbWithCodeLoaded_of_plain P.mpl hfn)

theorem hbFallibilityAllocErr_crossBlock_ok (P : HbPlaced) {i : Nat} {prog_i : Program}
    (X : String → Option (State → State)) (hi : i < 13)
    (hreb_i : prog_i = hashbrownLib.blockProgram P.mpl i X) {φ : Prop}
    (hpan : prog_i.externAt? (P.pl.ρ hbAllocErrSym) = some Rust.panicked) :
    subroutine_ok prog_i P.pl12.base (hashbrownLib.withCodeLoaded P.mpl (hbColdPanicSpec φ)) := by
  have hP := P.placeable12; have hb : (hbProg12 P).base = P.pl12.base := rfl
  have hpan12 : ((hbProg12 P).rebase P.pl12.base X).externAt? (P.pl.ρ hbAllocErrSym) =
      some Rust.panicked := by
    rw [hbExternAt?_transfer P hi (by decide) hreb_i (hbProg12_rebase P X)]; exact hpan
  have hfn := hbFallibilityAllocErr_infallible_ok P X (φ := φ) hpan12
  dsimp only at hfn; simp only [hbFallibilityAllocErrSym, arm64_norm] at hfn
  exact hbSubroutineOk_crossBlock P hi (by decide) hreb_i (hbProg12_rebase P X)
    (hbWithCodeLoaded_of_plain P.mpl hfn)

/-! ## `hashbrown_with_capacity` Proofs (`Infallible` and General) -/

private theorem step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; let m' := s.mem.write64 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

private def hbWithCapFrame (s0 : State) (vPad : BitVec 64) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ vPad) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private def HbUpperSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧ s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧ s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧ calleeSavedVRegs s = calleeSavedVRegs s0

private theorem HbUpperSaved.trans_cs {s0 s1 s2 : State}
    (h01 : HbUpperSaved s0 s1) (h12 : CalleeSavedPreserved s1 s2) : HbUpperSaved s0 s2 :=
  ⟨h12.readReg64_x24.trans h01.1, h12.readReg64_x25.trans h01.2.1, h12.readReg64_x26.trans h01.2.2.1,
   h12.readReg64_x27.trans h01.2.2.2.1, h12.readReg64_x28.trans h01.2.2.2.2.1, h12.vregs.trans h01.2.2.2.2.2⟩

local macro "hb_up " h:ident : tactic => `(tactic|
  exact ⟨by simpa using ($h).1, by simpa using ($h).2.1, by simpa using ($h).2.2.1,
         by simpa using ($h).2.2.2.1, by simpa using ($h).2.2.2.2.1, by simpa [calleeSavedVRegs] using ($h).2.2.2.2.2⟩)

private theorem hbWithCap_prologue (P : HbPlaced) (X : String → Option (State → State))
    {target : BitVec 64} {s0 : State} {mapPtr : BitVec 64} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = P.pl10.base) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hx8 : s0.readReg64 .x8 = mapPtr)
    (hcont : ∀ (s1 : State) (vPad : BitVec 64),
      s1.pc = P.pl10.base + 24#64 → s1.status = .Running → s1.sp = s0.sp - 64#64 →
      s1.spAligned = true → s1.readReg64 .x0 = s0.readReg64 .x0 → s1.readReg64 .x19 = mapPtr →
      s1.readReg64 .x29 = s0.sp - 64#64 → s1.readReg64 Reg.lr = s0.readReg64 Reg.lr →
      HbUpperSaved s0 s1 → StdStatePreserved s0 s1 →
      SepWP ((hbProg10 P).rebase P.pl10.base X) target s1 (hbWithCapFrame s0 vPad ∗ F) post oom) :
    SepWP ((hbProg10 P).rebase P.pl10.base X) target s0 (memRegion (s0.sp - 64#64) 64 ∗ F) post oom := by
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  have hsp64 : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true := State.spAligned_sub s0 64 hsp
  open_cells (s0.sp - 64#64) 64 8; rename_i c0 c1 c2 c3 c4 c5 c6 c7
  rw [show s0.sp - 64#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = s0.sp - 8#64 by bv_omega]
  refine step_stp64_perm (rt1 := .x29) (rt2 := .x30) (addr := .PreIndex .sp (-64#64))
    (ea := s0.sp - 64#64) (ea2 := s0.sp - 56#64) (wb := some (.sp, s0.sp - 64#64))
    hpc hrun (by simp) hsp
    (by show (s0.sp + -64#64, some (Reg.sp, s0.sp + -64#64)) = _; rw [show s0.sp + -64#64 = s0.sp - 64#64 by bv_omega])
    (by bv_omega) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  refine step_str64_perm (pc := P.pl10.base + 4#64) (rt := .x23) (addr := .Offset .sp 16#64)
    (ea := s0.sp - 48#64) (wb := none) (val := s0.readReg64 .x23) (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp64)
    (by show (s0.sp - 64#64 + 16#64, none) = _; rw [show s0.sp - 64#64 + 16#64 = s0.sp - 48#64 by bv_omega])
    (by simp) (by wp_sep_access) fun m2 hm2 => ?_
  refine step_stp64_perm (pc := P.pl10.base + 8#64) (rt1 := .x22) (rt2 := .x21) (addr := .Offset .sp 32#64)
    (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := none) (v1 := s0.readReg64 .x22) (v2 := s0.readReg64 .x21)
    (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp64)
    (by show (s0.sp - 64#64 + 32#64, none) = _; rw [show s0.sp - 64#64 + 32#64 = s0.sp - 32#64 by bv_omega])
    (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m3 hm3 => ?_
  refine step_stp64_perm (pc := P.pl10.base + 12#64) (rt1 := .x20) (rt2 := .x19) (addr := .Offset .sp 48#64)
    (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none) (v1 := s0.readReg64 .x20) (v2 := s0.readReg64 .x19)
    (by simp) (by simp [hrun]) (by simp)
    (by dsimp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, applyWriteback]; simpa [State.writeReg64_sp] using hsp64)
    (by show (s0.sp - 64#64 + 48#64, none) = _; rw [show s0.sp - 64#64 + 48#64 = s0.sp - 16#64 by bv_omega])
    (by bv_omega) (by simp) (by simp) (by wp_sep_access) (by wp_sep_access) fun m4 hm4 => ?_
  dsimp only [applyWriteback]
  refine SepWP.weaken_pre (P' := hbWithCapFrame s0 c3 ∗ F)
    (Entails.of_eq (by unfold hbWithCapFrame; ac_rfl)) ?_
  rw [show P.pl10.base + 12#64 + 4#64 = P.pl10.base + 16#64 by simp]; wp_step; wp_step
  exact hcont _ c3 (by simp) (by simp [hrun]) (by simp) (by simpa [State.spAligned] using hsp64)
    (by simp) (by simp) (by simp) (by simp)
    ⟨by simp, by simp, by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
     fun a => by simpa using congrFun (hm4.trans (hm3.trans (hm2.trans hm1))) a⟩

private theorem hbWithCap_epilogue (P : HbPlaced) (X : String → Option (State → State))
    {s0 s : State} {mapPtr ctrlPtr bm gl vPad : BitVec 64} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = P.pl10.base + 292#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 64#64) (hsp0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = mapPtr) (hx23 : s.readReg64 .x23 = ctrlPtr)
    (hx20 : s.readReg64 .x20 = bm) (hx21 : s.readReg64 .x21 = gl) (hup : HbUpperSaved s0 s)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 Reg.lr → sf.status = .Running → sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf → StdStatePreserved s sf →
      post sf (U64MapStruct mapPtr ctrlPtr bm gl 0#64 ∗ memRegion (s0.sp - 64#64) 64 ∗ F)) :
    SepWP ((hbProg10 P).rebase P.pl10.base X) (s0.readReg64 Reg.lr) s
      (memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗ F) post oom := by
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  open_cells mapPtr 32 4; rename_i m0 m1 m2 m3
  rw [show mapPtr + 8#64 + 8#64 + 8#64 = mapPtr + 24#64 by bv_omega]; unfold hbWithCapFrame
  refine step_stp64_perm (rt1 := .x23) (rt2 := .x20) (addr := .Offset .x19 0#64)
    (ea := mapPtr) (ea2 := mapPtr + 8#64) (wb := none) (v1 := ctrlPtr) (v2 := bm)
    hpc hrun (by simp) rfl (by show (s.readReg64 .x19 + 0#64, none) = _; rw [hx19, BitVec.add_zero])
    rfl hx23 hx20 (by wp_sep_access) (by wp_sep_access) fun ma hma => ?_
  refine step_stp64_perm (pc := P.pl10.base + 296#64) (rt1 := .x21) (rt2 := .xzr) (addr := .Offset .x19 16#64)
    (ea := mapPtr + 16#64) (ea2 := mapPtr + 24#64)
    (wb := none) (v1 := gl) (v2 := 0#64) (by simp) (by simp [hrun]) (by simp) rfl
    (by dsimp [evalAddrMode, applyWriteback]
        rw [show ((s.setPC (P.pl10.base + 292#64 + 4#64)).setMem ma).readReg64 (.gpr 19#5) = mapPtr by simpa [Reg.x19] using hx19])
    (by bv_omega) (by simpa [Reg.x21] using hx21) rfl (by wp_sep_access) (by wp_sep_access) fun mb hmb => ?_
  dsimp only [applyWriteback]; rw [show P.pl10.base + 296#64 + 4#64 = P.pl10.base + 300#64 by simp]
  wp_sym_steps
  refine SepWP.weaken_pre (P' := U64MapStruct mapPtr ctrlPtr bm gl 0#64 ∗ memRegion (s0.sp - 64#64) 64 ∗ F) ?_ ?_
  · have hstk64 : hbWithCapFrame s0 vPad ⊢ memRegion (s0.sp - 64#64) 64 := by
      unfold hbWithCapFrame
      rw [show memRegion (s0.sp - 64#64) 64 = cells (s0.sp - 64#64) 8 from memRegion_cells (s0.sp - 64#64) 8 (by decide)]
      refine cells_sub_succ_entails 64 8 (cells_sub_succ_entails 56 7 (cells_sub_succ_entails 48 6
        (cells_sub_succ_entails 40 5 (cells_sub_succ_entails 32 4 (cells_sub_succ_entails 24 3 (cells_sub_succ_entails 16 2 ?_))))))
      rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), Nat.sub_self, cells_zero]
      exact Entails.sepExists_right _ (by rw [sepConj_emp]; exact Entails.refl _)
    unfold hbWithCapFrame at hstk64
    exact Entails.trans (Entails.of_eq (by unfold U64MapStruct; ac_rfl)) (sepConj_mono_right (sepConj_mono_left hstk64))
  · refine SepWP.done (by simp [Reg.lr]) (by simp [hrun]) (hcont _ (by simp [Reg.lr]) (by simp [hrun]) (by simp) ?_ ?_)
    · exact ⟨by simp, by simp, by simp, by simp, by simp, by simpa using hup.1, by simpa using hup.2.1,
        by simpa using hup.2.2.1, by simpa using hup.2.2.2.1, by simpa using hup.2.2.2.2.1,
        by simp [Reg.fp], by simpa [calleeSavedVRegs] using hup.2.2.2.2.2⟩
    · exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun a => by simpa using congrFun (hmb.trans hma) a⟩

private theorem hbWithCap_toAlloc (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg10 P).rebase P.pl10.base X) P.pl10 A)
    {target : BitVec 64} {s0 s1 : State} {cap mapPtr : BitVec 64} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hCode0 : A.CodeInv s0.mem) (hkf1 : s0.mem.KeepsFrozen s1.mem)
    (hpc : s1.pc = P.pl10.base + 24#64) (hrun : s1.status = .Running)
    (hsp : s1.sp = s0.sp - 64#64) (hsp1 : s1.spAligned = true)
    (hx0 : s1.readReg64 .x0 = cap) (hx19 : s1.readReg64 .x19 = mapPtr)
    (hup1 : HbUpperSaved s0 s1) (hstd1 : StdStatePreserved s0 s1)
    (hcap0 : cap ≠ 0#64) (hle : cap.toNat ≤ MaxHashbrownCapacity)
    (hcont : ∀ sc : State,
      let bm := capToBucketMask cap.toNat; let buckets := bm.toNat + 1
      sc.pc = P.pl10.ρ hbAllocSym → sc.status = .Running → sc.sp = s0.sp - 64#64 →
      sc.spAligned = true → sc.readReg64 Reg.lr = P.pl10.base + 200#64 →
      sc.readReg64 .x0 = BitVec.ofNat 64 (tableAllocBytes bm) → sc.readReg64 .x1 = 8#64 →
      sc.readReg64 .x19 = mapPtr → sc.readReg64 .x20 = BitVec.ofNat 64 (tableAllocBytes bm) →
      sc.readReg64 .x21 = BitVec.ofNat 64 buckets → sc.readReg64 .x22 = BitVec.ofNat 64 (buckets + 8) →
      sc.readReg64 .x23 = BitVec.ofNat 64 (16 * buckets) → ValidBucketMask bm → HbUpperSaved s0 sc →
      StdStatePreserved s0 sc → s0.mem.KeepsFrozen sc.mem →
      SepWP ((hbProg10 P).rebase P.pl10.base X) target sc F post oom) :
    SepWP ((hbProg10 P).rebase P.pl10.base X) target s1 F post oom := by
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  let bm := capToBucketMask cap.toNat; let buckets := bm.toNat + 1
  have hpos := (Nat.eq_zero_or_pos cap.toNat).resolve_left fun hz => hcap0 (BitVec.eq_of_toNat_eq hz)
  have hbm : ValidBucketMask bm := capToBucketMask_valid hpos hle
  refine SepWP.seq (mid := P.pl10.base + 156#64)
    (Mid := fun s2 P2 => P2 = F ∧ s2.sp = s0.sp - 64#64 ∧ s2.spAligned = true ∧
      s2.readReg64 .x19 = mapPtr ∧ s2.readReg64 .x21 = BitVec.ofNat 64 buckets ∧
      HbUpperSaved s0 s2 ∧ StdStatePreserved s0 s2 ∧ s0.mem.KeepsFrozen s2.mem) ?_ ?_
  · wp_step; apply SepWP.ite_false rfl (by simpa [hx0] using hcap0); wp_steps
    by_cases hlt15 : cap < 15#64
    · apply SepWP.ite_false rfl (by rw [BitVec.ule_iff_le]; bv_omega); wp_steps
      refine SepWP.done (by simp) (by simp [hrun]) ⟨rfl, by simp [hsp], by simpa [State.spAligned, hsp] using hsp1,
        by simpa [Reg.x19] using hx19, ?_, by hb_up hup1,
        hstd1.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, by simpa using hkf1⟩
      simpa [Reg.x21, BitVec.ult_iff_lt, buckets, bm] using capToBucketMask_small_buckets hcap0 hlt15
    · apply SepWP.ite_true rfl (by rw [BitVec.ule_iff_le]; bv_omega)
      obtain ⟨hsh61, hsub_ne, hmask_eq, _, hle_lim, hadd1⟩ := capToBucketMask_large_ok hlt15 hle
      have humulh : (BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64) +
          (cap <<< 3 - BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64)) >>> 1) >>> 2 =
          BitVec.ofNat 64 ((cap.toNat * 8) / 7) := umulh_div7_bv hsh61
      wp_steps; apply SepWP.ite_false rfl (by rw [BitVec.ult_iff_lt, ← hmask_eq]; bv_omega); wp_steps
      refine SepWP.done (by simp) (by simp [hrun]) ⟨rfl, by simp [hsp], by simpa [State.spAligned, hsp] using hsp1,
        by simpa [Reg.x19] using hx19, ?_, by hb_up hup1,
        hstd1.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, by simpa using hkf1⟩
      simpa [Reg.x21, ← hmask_eq, buckets, bm] using hadd1
  · rintro s2 P2 hpc2 hrun2 ⟨rfl, hsp2, hsp2_al, hx19_2, hx21_2, hup2, hstd2, hkf2⟩
    obtain ⟨hsh4, hadd8, htab, htab_le, _, _⟩ := (ValidBucketMask.tableAlloc_machine_ok hbm); wp_steps
    apply SepWP.ite_false rfl (by
      dsimp only [buckets]; rw [hsh4, hadd8, ← BitVec.ofNat_add, htab, BitVec.ult_iff_lt, BitVec.lt_def]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tableAllocBytes bm < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : bm.toNat + 1 + 8 < 2 ^ 64)]; omega)
    wp_steps
    apply SepWP.ite_false rfl (by
      dsimp only [buckets]; rw [hsh4, hadd8, ← BitVec.ofNat_add, htab, BitVec.ult_iff_lt, BitVec.lt_def]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tableAllocBytes bm < 2 ^ 64), Nat.reducePow, Nat.reduceMod]; omega)
    wp_steps
    refine SepWP.call_subroutine hext.allocShim_ok (x := ()) (ret_pc := P.pl10.base + 188#64)
      (by dsimp only [hbAllocShimSym]; simp; bv_lin)
      (by simp [hrun2]) (by simpa [State.spAligned, hsp2] using hsp2_al) (by simp [Reg.lr])
      (fun _ hm => by
        dsimp only [withCodeInv, hbAllocShimSpec]; rw [sepConj_emp]
        exact (satisfies_pure_sepConj _ _ _).mpr ⟨A.codeInv_keepsFrozen hkf2 hCode0, hm⟩)
      (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (fun sa hpca hruna ⟨hpost_a, hspa, hcsa⟩ => ?_) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
    dsimp only [withCodeInv, hbAllocShimSpec] at hpost_a
    obtain ⟨hstd_a, hkf_a⟩ := ((satisfies_pure_sepConj _ emp _).mp (by rwa [sepConj_emp])).1
    have hstd_c : StdStatePreserved s2 sa :=
      StdStatePreserved.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩ hstd_a
    have hup_c : HbUpperSaved s0 sa := HbUpperSaved.trans_cs (by hb_up hup2) hcsa
    have hx19_a : sa.readReg64 .x19 = mapPtr := hcsa.readReg64_x19.trans (by simpa [Reg.x19] using hx19_2)
    have hx21_a : sa.readReg64 .x21 = BitVec.ofNat 64 buckets := hcsa.readReg64_x21.trans (by simpa [Reg.x21] using hx21_2)
    have hx22_a : sa.readReg64 .x22 = BitVec.ofNat 64 (buckets + 8) := hcsa.readReg64_x22.trans (by dsimp only [buckets]; simp [hadd8])
    have hx23_a : sa.readReg64 .x23 = BitVec.ofNat 64 (16 * buckets) := hcsa.readReg64_x23.trans (by dsimp only [buckets]; simp [hsh4])
    have hx20_a : sa.readReg64 .x20 = BitVec.ofNat 64 (tableAllocBytes bm) :=
      hcsa.readReg64_x20.trans (by dsimp only [buckets]; simp [hsh4, hadd8, ← BitVec.ofNat_add, htab])
    wp_steps
    exact hcont _
      (by dsimp only [hbAllocSym]; simp; bv_lin)
      (by simp [hruna]) (by simp [hspa, hsp2]) (by simpa [State.spAligned, hspa, hsp2] using hsp2_al)
      (by simp [Reg.lr]) (by simp [Reg.x0, bm]) (by simp [Reg.x1])
      (by simpa [Reg.x19] using hx19_a) (by simpa [Reg.x20] using hx20_a)
      (by simpa [Reg.x21] using hx21_a) (by simpa [Reg.x22] using hx22_a)
      (by simpa [Reg.x23] using hx23_a) hbm (by hb_up hup_c)
      ((hstd2.trans hstd_c).trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩)
      (hkf2.trans (by simpa using hkf_a))

private theorem sepWP_pure_elim {prog : Program} {target : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWP prog target s P post oom) : SepWP prog target s (⌜φ⌝ ∗ P) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact SepWP.to_reaches_pc (h hm.1) hm.2

private theorem stdStatePreserved_congr_left {s1 s1' s2 : State}
    (h1 : s1'.fs = s1.fs) (h2 : s1'.trace = s1.trace) (h3 : s1'.tpidrEl0 = s1.tpidrEl0)
    (h4 : s1'.sigActions = s1.sigActions) (h5 : s1'.brk = s1.brk) (h6 : s1'.brkStart = s1.brkStart)
    (h7 : s1'.physMemAvail = s1.physMemAvail) (h8 : s1'.mem = s1.mem)
    (h : StdStatePreserved s1' s2) : StdStatePreserved s1 s2 :=
  ⟨h.1.trans h1, h.2.1.trans h2, h.2.2.1.trans h3, h.2.2.2.1.trans h4, h.2.2.2.2.1.trans h5,
   h.2.2.2.2.2.1.trans h6, h.2.2.2.2.2.2.1.trans h7, fun a => (h.2.2.2.2.2.2.2 a).trans (congrArg (fun m => m.perm a) h8)⟩

private theorem sepWP_seq_frozen {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {Φ : Memory → Prop}
    (hst : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m') (hΦ : Φ s.mem)
    (h : SepWP prog mid s P (fun sm Pm => Φ sm.mem → SepWP prog target sm Pm post oom) oom) :
    SepWP prog target s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm hL
  rcases SepWP.to_reaches_pc h hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ := SepWP.to_reaches_pc (hcont (hst _ _ hΦ hst1.keepsFrozen)) hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

private theorem hbWithCap_postAlloc (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg10 P).rebase P.pl10.base X) P.pl10 A)
    {s0 sa : State} {mapPtr bm vPad : BitVec 64} {lc blk : Nat} {oom : State → SepProp}
    (hCode0 : A.CodeInv s0.mem) (hasp : AllocStatePreserved s0 sa)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hstk_nw : A.stackBytes + 80 ≤ 2 ^ 64) (hsp0_al : s0.spAligned = true)
    (hpc : sa.pc = P.pl10.base + 200#64) (hrun : sa.status = .Running)
    (hsp : sa.sp = s0.sp - 64#64) (hsp_al : sa.spAligned = true)
    (hne0 : sa.readReg64 .x0 ≠ 0#64) (hx19 : sa.readReg64 .x19 = mapPtr)
    (hx21 : sa.readReg64 .x21 = BitVec.ofNat 64 (bm.toNat + 1))
    (hx22 : sa.readReg64 .x22 = BitVec.ofNat 64 (bm.toNat + 1 + 8))
    (hx23 : sa.readReg64 .x23 = BitVec.ofNat 64 (16 * (bm.toNat + 1)))
    (hbm : ValidBucketMask bm) (hup : HbUpperSaved s0 sa) :
    SepWP ((hbProg10 P).rebase P.pl10.base X) (s0.readReg64 Reg.lr) sa
      (stackAt (s0.sp - 64#64) A.stackBytes ∗
       (⌜(sa.readReg64 .x0).toNat % (8#64).toNat = 0 ∧
          (sa.readReg64 .x0).toNat + (BitVec.ofNat 64 (tableAllocBytes bm)).toNat < 2 ^ 64⌝ ∗
        A.Heap (lc + A.cost (BitVec.ofNat 64 (tableAllocBytes bm)).toNat (8#64).toNat) (blk + 1) sa ∗
        A.Block (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm)).toNat (8#64).toNat ∗
        memRegion (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm)).toNat) ∗
       (hbRodata P.pl ∗ memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
        memRegion ((s0.sp - 64#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)))
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ ⌜AllocStatePreserved s0 sf⌝ ∗ hbRodata P.pl ∗ U64MapRep P.pl A mapPtr [] bm 0 ∗
          A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sf ∗
          stackAt s0.sp (80 + A.stackBytes))) oom := by
  generalize hx0 : sa.readReg64 .x0 = allocPtr at hne0 ⊢
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  obtain ⟨_, _, _, htab_le, hsub1, hcap_mach⟩ := (ValidBucketMask.tableAlloc_machine_ok hbm)
  have hstk_sh := stackAt_shrink (s0.sp - 64#64) (16 + A.stackBytes) A.stackBytes (by omega) (by omega)
  have hsz_nat : (BitVec.ofNat 64 (tableAllocBytes bm)).toNat = tableAllocBytes bm := by
    simp only [BitVec.toNat_ofNat]; omega
  have hcost_eq : A.cost (tableAllocBytes bm) 8 = hbMapCost A bm := by simp only [hbMapCost, hbm.ne_zero, ↓reduceIte]
  have hblk_eq : 1 = tableAllocBlocks bm := by simp only [tableAllocBlocks, hbm.ne_zero, ↓reduceIte]
  refine SepWP.weaken_pre (P' := ⌜allocPtr.toNat % (8#64).toNat = 0 ∧
      allocPtr.toNat + (BitVec.ofNat 64 (tableAllocBytes bm)).toNat < 2 ^ 64⌝ ∗
    (hbRodata P.pl ∗ memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
     A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sa ∗
     A.Block allocPtr (tableAllocBytes bm) 8 ∗ memRegion allocPtr (tableAllocBytes bm) ∗
     stackAt (s0.sp - 64#64) (16 + A.stackBytes)))
    (by rw [hsz_nat, show (8#64).toNat = 8 from rfl, hcost_eq, ← hblk_eq, hstk_sh]; exact Entails.of_eq (by ac_rfl))
    (sepWP_pure_elim fun _ => ?_)
  clear hstk_sh hsz_nat hcost_eq hblk_eq
  have hlen_lt : bm.toNat + 1 + 8 < 2 ^ 64 := by
    obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hbm; have := ValidBucketMask.buckets_eq hlo hhi hbm_eq
    have : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi; omega
  refine SepWP.mono_frozen (Φ := fun m => s0.mem.KeepsFrozen m)
    (post := fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ StdStatePreserved sa sf ∧
      (Pf ⊢ hbRodata P.pl ∗ U64MapRep P.pl A mapPtr [] bm 0 ∗
        A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sf ∗ stackAt s0.sp (80 + A.stackBytes)))
    (fun _ _ => Memory.KeepsFrozen.trans) hasp.2.2.2.2 ?_
    fun sf Pf _ _ hkf_sf ⟨hsp_f, hcs_f, hstd_af, hPf⟩ => ⟨hsp_f, hcs_f, Entails.pure_right
      ⟨hstd_af.1.trans hasp.1, hstd_af.2.1.trans hasp.2.1, hstd_af.2.2.2.1.trans hasp.2.2.1,
       hstd_af.2.2.1.trans hasp.2.2.2.1, hkf_sf⟩ hPf⟩
  rw [memRegion_tableAllocBytes_split allocPtr hbm]
  wp_step; apply SepWP.ite_false rfl (by simpa [hx0] using hne0); wp_steps
  let ctrlPtr := allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))
  refine SepWP.call_subroutine_frame hext.memset_ok (x := (ctrlPtr, 0xff#8, bm.toNat + 1 + 8))
    (F := hbRodata P.pl ∗ memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
      A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sa ∗
      A.Block allocPtr (tableAllocBytes bm) 8 ∗ memRegion allocPtr (16 * (bm.toNat + 1)) ∗
      stackAt (s0.sp - 64#64) (16 + A.stackBytes))
    (ret_pc := P.pl10.base + 248#64)
    (by dsimp only [hbMemsetSym]; simp; bv_lin)
    (by simp [hrun]) (by simpa [State.spAligned, hsp] using hsp_al) (by simp [Reg.lr])
    (fun R hm => by
      dsimp only [withCodeInv, stdMemsetSpec]; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨by simpa using A.codeInv_keepsFrozen hasp.2.2.2.2 hCode0, ?_⟩
      rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨by simp [Reg.x0, ctrlPtr],
        by simp [Reg.x1, State.readReg32], by simp [Reg.x2], hlen_lt⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by dsimp only [ctrlPtr]; ac_rfl)) hm)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sm hpcm hrunm hspm hcsm => ?_) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  dsimp only [withCodeInv, stdMemsetSpec]; rw [sepConj_assoc]; refine sepWP_pure_elim fun ⟨_, hstd_m⟩ => ?_
  have hstd_am : StdStatePreserved sa sm :=
    stdStatePreserved_congr_left (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hstd_m
  have hup_m : HbUpperSaved s0 sm := HbUpperSaved.trans_cs (by hb_up hup) hcsm
  have hb_add : bm + 1#64 = BitVec.ofNat 64 (bm.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [← hb_add, show bm + 1#64 - 1#64 = bm by bv_lin] at hcap_mach
  have hx19_m : sm.readReg64 .x19 = mapPtr := hcsm.readReg64_x19.trans (by simpa [Reg.x19] using hx19)
  have hx20_m : sm.readReg64 .x20 = bm := hcsm.readReg64_x20.trans (by simp)
  have hx21_m : sm.readReg64 .x21 = bucketMaskToCapacityBV bm :=
    hcsm.readReg64_x21.trans (by simpa [BitVec.ult_iff_lt] using hcap_mach)
  have hx23_m : sm.readReg64 .x23 = ctrlPtr := hcsm.readReg64_x23.trans (by simp [ctrlPtr])
  wp_steps
  refine SepWP.weaken_pre (P' := memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
    (hbRodata P.pl ∗ A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sa ∗
     A.Block allocPtr (tableAllocBytes bm) 8 ∗ memRegion allocPtr (16 * (bm.toNat + 1)) ∗
     (ctrlPtr ↦ₛ List.replicate (bm.toNat + 1 + 8) 0xff#8) ∗ stackAt (s0.sp - 64#64) (16 + A.stackBytes)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine hbWithCap_epilogue P X (by simp) (by simp [hrunm]) (by simp [hspm, hsp]) hsp0_al
    (by simpa [Reg.x19] using hx19_m) (by simpa [Reg.x23] using hx23_m)
    (by simpa [Reg.x20] using hx20_m) (by simpa [Reg.x21] using hx21_m) (by hb_up hup_m)
    fun sf _ _ hspf hcsf hstd_mf => ?_
  have hstd_af : StdStatePreserved sa sf := StdStatePreserved.trans hstd_am
    (stdStatePreserved_congr_left (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hstd_mf)
  refine ⟨hspf, hcsf, hstd_af, ?_⟩
  rw [show 80 + A.stackBytes = (16 + A.stackBytes) + 64 by omega, stackAt_region s0.sp (16 + A.stackBytes) 64 (by omega)]
  exact Entails.trans (Entails.of_eq (show _ =
      (hbRodata P.pl ∗ U64MapStruct mapPtr ctrlPtr bm (bucketMaskToCapacityBV bm) 0#64 ∗
       A.Block allocPtr (tableAllocBytes bm) 8 ∗ memRegion allocPtr (16 * (bm.toNat + 1)) ∗
       (ctrlPtr ↦ₛ List.replicate (bm.toNat + 1 + 8) 0xff#8)) ∗
      A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sa ∗
      (stackAt (s0.sp - 64#64) (16 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64) by ac_rfl))
    (Entails.trans (sepConj_mono
      (U64MapRep_of_alloc_memset P.pl A mapPtr allocPtr ctrlPtr bm hbm hal hnw rfl)
      (sepConj_mono_left (A.heap_transport (StdStatePreserved.toHbVmPreserved hstd_af))))
      (Entails.of_eq (by ac_rfl)))

private theorem hbWithCap_runToPostAlloc (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg10 P).rebase P.pl10.base X) P.pl10 A)
    {target : BitVec 64} {s0 s1 : State} {mapPtr cap vPad : BitVec 64} {lc blk : Nat}
    {post : State → SepProp → Prop} (hCode0 : A.CodeInv s0.mem) (hkf1 : s0.mem.KeepsFrozen s1.mem)
    (hstk_nw : A.stackBytes + 80 ≤ 2 ^ 64) (hpc1 : s1.pc = P.pl10.base + 24#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 64#64) (hsp1_al : s1.spAligned = true)
    (hx0' : s1.readReg64 .x0 = cap) (hx19_1 : s1.readReg64 .x19 = mapPtr)
    (hup1 : HbUpperSaved s0 s1) (hstd1 : StdStatePreserved s0 s1)
    (hcap0 : cap ≠ 0#64) (hle_max : cap.toNat ≤ MaxHashbrownCapacity)
    (himp_can : ¬ A.allowOom → A.CanAlloc lc blk (tableAllocBytes (capToBucketMask cap.toNat)) 8)
    (hcont : ∀ sa : State,
      let bm := capToBucketMask cap.toNat
      sa.pc = P.pl10.base + 200#64 → sa.status = .Running → sa.sp = s0.sp - 64#64 →
      sa.spAligned = true → sa.readReg64 .x19 = mapPtr →
      sa.readReg64 .x21 = BitVec.ofNat 64 (bm.toNat + 1) →
      sa.readReg64 .x22 = BitVec.ofNat 64 (bm.toNat + 1 + 8) →
      sa.readReg64 .x23 = BitVec.ofNat 64 (16 * (bm.toNat + 1)) →
      ValidBucketMask bm → HbUpperSaved s0 sa → AllocStatePreserved s0 sa →
      SepWP ((hbProg10 P).rebase P.pl10.base X) target sa
        (stackAt (s0.sp - 64#64) A.stackBytes ∗
         (if sa.readReg64 .x0 = 0#64 then
            ⌜A.allowOom ∧ ¬ A.CanAlloc lc blk (BitVec.ofNat 64 (tableAllocBytes bm)).toNat (8#64).toNat⌝ ∗ A.Heap lc blk sa
          else
            ⌜(sa.readReg64 .x0).toNat % (8#64).toNat = 0 ∧
              (sa.readReg64 .x0).toNat + (BitVec.ofNat 64 (tableAllocBytes bm)).toNat < 2 ^ 64⌝ ∗
            A.Heap (lc + A.cost (BitVec.ofNat 64 (tableAllocBytes bm)).toNat (8#64).toNat) (blk + 1) sa ∗
            A.Block (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm)).toNat (8#64).toNat ∗
            memRegion (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm)).toNat) ∗
         (hbRodata P.pl ∗ memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
          memRegion ((s0.sp - 64#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)))
        post (fun _ => ⌜A.allowOom⌝)) :
    SepWP ((hbProg10 P).rebase P.pl10.base X) target s1
      (hbWithCapFrame s0 vPad ∗ (hbRodata P.pl ∗ memRegion mapPtr 32 ∗ A.Heap lc blk s0 ∗
        stackAt (s0.sp - 64#64) (16 + A.stackBytes))) post (fun _ => ⌜A.allowOom⌝) := by
  refine hbWithCap_toAlloc P A X hext hCode0 hkf1 hpc1 hrun1 hsp1 hsp1_al hx0' hx19_1
    hup1 hstd1 hcap0 hle_max
    fun sc hpc_c hrun_c hsp_c hsp_c_al hlr_c hx0_c hx1_c hx19_c _ hx21_c hx22_c hx23_c
        hbm hup_c hstd_c hkf_c => ?_
  let bm := capToBucketMask cap.toNat; change ValidBucketMask bm at hbm
  have hstk_sh := stackAt_shrink (s0.sp - 64#64) (16 + A.stackBytes) A.stackBytes (by omega) (by omega)
  have htab_eq : tableAllocBytes bm = 17 * (bm.toNat + 1) + 8 := by
    simp only [tableAllocBytes, hbm.ne_zero, ↓reduceIte]
  have hlay : LayoutOk (BitVec.ofNat 64 (tableAllocBytes bm)) 8#64 := htab_eq ▸ (ValidBucketMask.tableLayoutOk hbm)
  have hsz_nat : (BitVec.ofNat 64 (tableAllocBytes bm)).toNat = tableAllocBytes bm := by
    have := (ValidBucketMask.tableAlloc_machine_ok hbm).2.2.2.1; simp only [BitVec.toNat_ofNat]; omega
  refine SepWP.weaken_pre (P' := A.Heap lc blk sc ∗ stackAt sc.sp A.stackBytes ∗ (hbRodata P.pl ∗
    memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
    memRegion ((s0.sp - 64#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)))
    (by rw [hsp_c, hstk_sh]
        exact Entails.trans (Entails.of_eq (show _ =
          A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) A.stackBytes ∗ (hbRodata P.pl ∗ memRegion mapPtr 32 ∗
            hbWithCapFrame s0 vPad ∗ memRegion ((s0.sp - 64#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)) by ac_rfl))
          (sepConj_mono_left (A.heap_transport (StdStatePreserved.toHbVmPreserved hstd_c)))) ?_
  refine SepWP.call_subroutine_frame hext.alloc_ok (x := (BitVec.ofNat 64 (tableAllocBytes bm), 8#64, lc, blk))
    (F := hbRodata P.pl ∗ memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
      memRegion ((s0.sp - 64#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes))
    (ret_pc := P.pl10.base + 200#64) hpc_c hrun_c hsp_c_al hlr_c
    (fun R' hm => by
      dsimp only [withCodeInv, hbAllocSpec]; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨A.codeInv_keepsFrozen hkf_c hCode0, ?_⟩; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0_c, hx1_c, hlay, fun hna => by simpa [hsz_nat] using himp_can hna⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sa hpca hruna hspa hcsa => ?_)
    (fun R' sf _ h => by
      dsimp only [withCodeInv, hbAllocSpec] at h
      have h' := (satisfies_pure_sepConj _ _ _).mp h; exact satisfies_pure_frame_of_sepConj h'.1 h'.2)
  dsimp only [withCodeInv, hbAllocSpec]; rw [sepConj_assoc]; refine sepWP_pure_elim fun hasp_ca => ?_
  have hasp_0c : AllocStatePreserved s0 sc := StdStatePreserved.toAllocStatePreserved hstd_c hkf_c
  have hasp_0a : AllocStatePreserved s0 sa :=
    ⟨hasp_ca.1.trans hasp_0c.1, hasp_ca.2.1.trans hasp_0c.2.1, hasp_ca.2.2.1.trans hasp_0c.2.2.1,
     hasp_ca.2.2.2.1.trans hasp_0c.2.2.2.1, hasp_0c.2.2.2.2.trans hasp_ca.2.2.2.2⟩
  rw [hsp_c, sepConj_assoc]
  exact hcont sa hpca hruna (hspa.trans hsp_c) (by simpa [State.spAligned, hspa] using hsp_c_al)
    (hcsa.readReg64_x19.trans hx19_c) (hcsa.readReg64_x21.trans hx21_c)
    (hcsa.readReg64_x22.trans hx22_c) (hcsa.readReg64_x23.trans hx23_c)
    hbm (hup_c.trans_cs hcsa) hasp_0a

private theorem hbWithCap_infallible_wp (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg10 P).rebase P.pl10.base X) P.pl10 A)
    {s0 : State} {mapPtr cap : BitVec 64} {lc blk : Nat} {R : SepProp}
    (hpc : s0.pc = P.pl10.base) (hrun : s0.status = .Running)
    (hsp0_al : s0.spAligned = true) (hCode0 : A.CodeInv s0.mem)
    (hx0 : s0.readReg64 .x0 = cap) (hx8 : s0.readReg64 .x8 = mapPtr)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hstk_nw : A.stackBytes + 80 ≤ 2 ^ 64) (hcan0 : HbCanWithCapacity A cap lc blk) :
    SepWP ((hbProg10 P).rebase P.pl10.base X) (s0.readReg64 Reg.lr) s0
      (hbRodata P.pl ∗ memRegion mapPtr 32 ∗ A.Heap lc blk s0 ∗ stackAt s0.sp (80 + A.stackBytes))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜AllocStatePreserved s0 sf⌝ ∗ hbRodata P.pl ∗
        U64MapRep P.pl A mapPtr [] (capToBucketMask cap.toNat) 0 ∗
        A.Heap (lc + hbMapCost A (capToBucketMask cap.toNat))
          (blk + tableAllocBlocks (capToBucketMask cap.toNat)) sf ∗
        stackAt s0.sp (80 + A.stackBytes)) ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜A.allowOom⌝) := by
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  obtain ⟨hle_max, hcan_or⟩ := hcan0
  refine SepWP.mono (post := fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (Pf ⊢ ⌜AllocStatePreserved s0 sf⌝ ∗ hbRodata P.pl ∗
        U64MapRep P.pl A mapPtr [] (capToBucketMask cap.toNat) 0 ∗
        A.Heap (lc + hbMapCost A (capToBucketMask cap.toNat))
          (blk + tableAllocBlocks (capToBucketMask cap.toNat)) sf ∗
        stackAt s0.sp (80 + A.stackBytes))) ?_ fun sf Pf _ _ ⟨hspf, hcsf, hPf⟩ =>
    ⟨Satisfies.mono (sepConj_mono_left hPf), hspf, hcsf⟩
  have hstk_eq : stackAt s0.sp (80 + A.stackBytes) =
      stackAt (s0.sp - 64#64) (16 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64 := by
    rw [show 80 + A.stackBytes = (16 + A.stackBytes) + 64 by omega]
    exact stackAt_region s0.sp (16 + A.stackBytes) 64 (by omega)
  refine SepWP.weaken_pre (P' := memRegion (s0.sp - 64#64) 64 ∗ (hbRodata P.pl ∗
    memRegion mapPtr 32 ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (16 + A.stackBytes)))
    (Entails.of_eq (by rw [hstk_eq]; ac_rfl)) ?_
  refine sepWP_seq_frozen (mid := P.pl10.base + 24#64) (Φ := fun m => s0.mem.KeepsFrozen m)
    (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl s0.mem) ?_
  refine hbWithCap_prologue P X hpc hrun hsp0_al hx8
    fun s1 vPad hpc1 hrun1 hsp1 hsp1_al hx0_1 hx19_1 _ _ hup1 hstd1 => SepWP.done hpc1 hrun1 fun hkf1 => ?_
  have hx0' : s1.readReg64 .x0 = cap := hx0_1.trans hx0
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    rw [show capToBucketMask (0#64).toNat = 0#64 from rfl, show hbMapCost A 0#64 = 0 from rfl,
        show tableAllocBlocks 0#64 = 0 from rfl, Nat.add_zero, Nat.add_zero]
    refine SepWP.mono_frozen (Φ := fun m => s0.mem.KeepsFrozen m)
      (post := fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ StdStatePreserved s0 sf ∧
        (Pf ⊢ hbRodata P.pl ∗ U64MapRep P.pl A mapPtr [] 0#64 0 ∗
          A.Heap lc blk sf ∗ stackAt s0.sp (80 + A.stackBytes)))
      (fun _ _ => Memory.KeepsFrozen.trans) hkf1 ?_ fun sf Pf _ _ hkf_sf ⟨hsp_f, hcs_f, hstd_f, hPf⟩ =>
        ⟨hsp_f, hcs_f, Entails.pure_right (StdStatePreserved.toAllocStatePreserved hstd_f hkf_sf) hPf⟩
    wp_steps
    refine SepWP.weaken_pre (P' := memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad ∗
      (hbRodata P.pl ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (16 + A.stackBytes)))
      (Entails.of_eq (by ac_rfl)) ?_
    refine hbWithCap_epilogue P X (ctrlPtr := P.pl.ρ hbEmptyCtrlSym) (bm := 0#64) (gl := 0#64)
      (by simp) (by simp [hrun1]) (by simp [hsp1]) hsp0_al (by simpa [Reg.x19] using hx19_1)
      (by simp [Reg.x23]) (by simp [Reg.x20]) (by simp [Reg.x21]) (by hb_up hup1)
      fun sf _ _ hspf hcsf hstd_ef => ?_
    have hstd0f : StdStatePreserved s0 sf := StdStatePreserved.trans hstd1
      (stdStatePreserved_congr_left (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hstd_ef)
    refine ⟨hspf, hcsf, hstd0f, ?_⟩; rw [hstk_eq]
    exact Entails.trans (Entails.of_eq (show _ =
        (hbRodata P.pl ∗ U64MapStruct mapPtr (P.pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64) ∗
        A.Heap lc blk s0 ∗ (stackAt (s0.sp - 64#64) (16 + A.stackBytes) ∗ memRegion (s0.sp - 64#64) 64) by ac_rfl))
      (Entails.trans (sepConj_mono (U64MapRep_init P.pl A mapPtr hal hnw)
        (sepConj_mono_left (A.heap_transport (StdStatePreserved.toHbVmPreserved hstd0f))))
        (Entails.of_eq (by ac_rfl)))
  · have hcan := hcan_or.resolve_left hcap0
    refine hbWithCap_runToPostAlloc P A X hext hCode0 hkf1 hstk_nw hpc1 hrun1 hsp1 hsp1_al
      hx0' hx19_1 hup1 hstd1 hcap0 hle_max (fun _ => hcan)
      fun sa hpca hruna hspa hspa_al hx19_a hx21_a hx22_a hx23_a hbm hup_a hasp_0a => ?_
    let bm := capToBucketMask cap.toNat; change ValidBucketMask bm at hbm
    have hsz_nat : (BitVec.ofNat 64 (tableAllocBytes bm)).toNat = tableAllocBytes bm := by
      have := (ValidBucketMask.tableAlloc_machine_ok hbm).2.2.2.1; simp only [BitVec.toNat_ofNat]; omega
    by_cases hret0 : sa.readReg64 .x0 = 0#64
    · simp only [hret0, ↓reduceIte]
      refine SepWP.weaken_pre (P' := ⌜A.allowOom ∧ ¬ A.CanAlloc lc blk
          (BitVec.ofNat 64 (tableAllocBytes bm)).toNat (8#64).toNat⌝ ∗
        (stackAt (s0.sp - 64#64) A.stackBytes ∗ A.Heap lc blk sa ∗ (hbRodata P.pl ∗ memRegion mapPtr 32 ∗
          hbWithCapFrame s0 vPad ∗ memRegion ((s0.sp - 64#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes))))
        (Entails.of_eq (by ac_rfl)) ?_
      exact sepWP_pure_elim fun ⟨_, hncan⟩ => False.elim (hncan (by simpa [hsz_nat] using hcan))
    · simp only [hret0, ↓reduceIte]
      exact hbWithCap_postAlloc P A X hext hCode0 hasp_0a hal hnw hstk_nw hsp0_al
        hpca hruna hspa hspa_al hret0 hx19_a hx21_a hx22_a hx23_a hbm hup_a

theorem hashbrown_with_capacity_infallible_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg10 P).rebase P.pl10.base X) P.pl10 A) :
    let prog := (hbProg10 P).rebase P.pl10.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_with_capacity")
      (withCodeInv A (hashbrownWithCapacityInfallibleSpec P.pl A)) := by
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  dsimp only; apply subroutine_ok_of_sepWP_init
  rintro ⟨mapPtr, cap, lc, blk⟩ R s0 hpc hrun hpre hsp0_al; simp only [arm64_norm] at hpc
  dsimp only [withCodeInv, hashbrownWithCapacityInfallibleSpec] at hpre ⊢
  rw [sepConj_assoc] at hpre; obtain ⟨hCode0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  rw [sepConj_assoc] at hpre
  obtain ⟨⟨hx0, hx8, hal, hnw, hstk_nw, hcan0⟩, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  exact ⟨_, hpre, hbWithCap_infallible_wp P A X hext hpc hrun hsp0_al hCode0 hx0 hx8 hal hnw hstk_nw hcan0⟩

private theorem hbWithCap_overflow_toPanic (P : HbPlaced) (X : String → Option (State → State))
    {s0 s1 : State} {cap : BitVec 64} {F : SepProp} {oom : State → SepProp}
    (hpc1 : s1.pc = P.pl10.base + 24#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 64#64) (hsp1_al : s1.spAligned = true)
    (hx0 : s1.readReg64 .x0 = cap) (hov : MaxHashbrownCapacity < cap.toNat) :
    SepWP ((hbProg10 P).rebase P.pl10.base X) P.pl11.base s1 F
      (fun sm Pm => Pm = F ∧ sm.sp = s0.sp - 64#64 ∧ sm.spAligned = true ∧ sm.readReg32 .x0 = 1#32) oom := by
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  have hcap0 : cap ≠ 0#64 := by rintro rfl; exact absurd hov (by decide)
  obtain ⟨hnlt15, hor⟩ := capToBucketMask_overflow_cases hov
  refine SepWP.seq (mid := P.pl10.base + 252#64)
    (Mid := fun s2 P2 => P2 = F ∧ s2.sp = s0.sp - 64#64 ∧ s2.spAligned = true) ?_ ?_
  · wp_step; apply SepWP.ite_false rfl (by simpa [hx0] using hcap0)
    wp_steps; apply SepWP.ite_true rfl (by rw [BitVec.ule_iff_le]; bv_omega)
    rcases hor with hsh_ne | ⟨hsh_eq, _, hmask_or⟩
    · wp_step; wp_step; apply SepWP.ite_true rfl (by simpa [hx0] using hsh_ne)
      exact SepWP.done (by simp) (by simp [hrun1]) ⟨rfl, by simp [hsp1], by simpa [State.spAligned, hsp1] using hsp1_al⟩
    · have humulh : (BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64) +
          (cap <<< 3 - BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64)) >>> 1) >>> 2 =
          BitVec.ofNat 64 ((cap.toNat * 8) / 7) := umulh_div7_bv hsh_eq
      wp_steps; rcases hmask_or with hgt_lim | ⟨hmask_59, hle_lim⟩
      · apply SepWP.ite_true rfl (by rw [BitVec.ult_iff_lt]; simpa [hx0, humulh] using hgt_lim)
        exact SepWP.done (by simp) (by simp [hrun1]) ⟨rfl, by simp [hsp1], by simpa [State.spAligned, hsp1] using hsp1_al⟩
      · apply SepWP.ite_false rfl (by rw [BitVec.ult_iff_lt, BitVec.not_lt]; simpa only [arm64_norm, hx0, humulh] using hle_lim)
        wp_steps
        exact SepWP.done (by simp) (by simp [hrun1]) ⟨rfl, by simp [hsp1], by simpa [State.spAligned, hsp1] using hsp1_al⟩
  · rintro s2 P2 hpc2 hrun2 ⟨rfl, hsp2, hsp2_al⟩; wp_steps
    exact SepWP.done (by simp; bv_lin) (by simp [hrun2])
      ⟨rfl, by simp [hsp2], by simpa [State.spAligned, hsp2] using hsp2_al, by simp [Reg.x0, State.readReg32]⟩

private theorem sepWPp_call_coldPanic {mpl : Obj.MultiPlacement} {prog : Program}
    {ret entry ret_pc spBase : BitVec 64}
    {s : State} {F R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    {φ : Prop} {stkTotal : Nat}
    (hcall : subroutine_ok prog entry (hashbrownLib.withCodeLoaded mpl (hbColdPanicSpec φ)))
    (hcl : hashbrownLib.CodeLoaded mpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hsp : s.sp = spBase) (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg32 .x0 = 1#32)
    (hφ : φ) (hge16 : 16 ≤ stkTotal) (hnw_stk : spBase.toNat < 2 ^ 64 ∧ stkTotal ≤ 2 ^ 64) :
    SepWPp prog ret s (stackAt spBase stkTotal ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜φ⌝ ∗ R)) oom := by
  have hsh := stackAt_shrink spBase stkTotal 16 hge16 hnw_stk.2
  refine SepWPp.call (x := ()) hcall hpc hrun hsp_al hlr
    (F := memRegion (spBase - BitVec.ofNat 64 stkTotal) (stkTotal - 16) ∗ F)
    (fun R' hm => by
      dsimp only [MultiPlacedLib.withCodeLoaded]
      rw [sepConj_comm ((hbColdPanicSpec φ).pre () s), sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨hcl, ?_⟩
      dsimp only [hbColdPanicSpec]; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0, hφ⟩, ?_⟩
      rw [hsh] at hm; rw [hsp]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ hmf => satisfies_pure_frame_of_sepConj hφ hmf)
    (fun _ _ _ _ _ => SepWPp.pure_left False.elim) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)

theorem hashbrown_with_capacity_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg10 P).rebase P.pl10.base X) P.pl10 A) :
    let prog := (hbProg10 P).rebase P.pl10.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_with_capacity")
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownWithCapacitySpec P.pl A))) := by
  have hP := P.placeable10; have hb : (hbProg10 P).base = P.pl10.base := rfl
  dsimp only; apply subroutine_ok_of_sepWPp_init
  rintro ⟨mapPtr, cap, lc, blk⟩ R s0 hpc hrun hpre hsp0_al; simp only [arm64_norm] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre ⊢
  rw [sepConj_comm ((withCodeInv A (hashbrownWithCapacitySpec P.pl A)).pre _ s0), sepConj_assoc] at hpre
  obtain ⟨hcl0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  dsimp only [withCodeInv, hashbrownWithCapacitySpec] at hpre ⊢
  rw [sepConj_assoc] at hpre; obtain ⟨hCode0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  rw [sepConj_assoc] at hpre
  obtain ⟨⟨hx0, hx8, hal, hnw, hstk_nw, himp_can⟩, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  refine ⟨_, hpre, ?_⟩
  by_cases hcan : HbCanWithCapacity A cap lc blk
  · exact SepWPp.of_sepWP_ret (hbWithCap_infallible_wp P A X hext hpc hrun hsp0_al hCode0 hx0 hx8 hal hnw hstk_nw hcan)
  · have hao : A.allowOom := Classical.byContradiction fun hna => hcan (himp_can hna)
    refine SepWPp.congr_pre (P' := memRegion (s0.sp - 64#64) 64 ∗ (hbRodata P.pl ∗
      memRegion mapPtr 32 ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (16 + A.stackBytes)))
      (by rw [show 80 + A.stackBytes = (16 + A.stackBytes) + 64 by omega,
              stackAt_region s0.sp (16 + A.stackBytes) 64 (by omega)]; ac_rfl) ?_
    by_cases hle_max : cap.toNat ≤ MaxHashbrownCapacity
    · have hcap0 : cap ≠ 0#64 := fun h0 => hcan ⟨hle_max, Or.inl h0⟩
      apply SepWPp.of_sepWP (mid := P.pl10.base + 200#64)
      refine sepWP_seq_frozen (mid := P.pl10.base + 24#64) (Φ := fun m => s0.mem.KeepsFrozen m)
        (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl s0.mem) ?_
      refine hbWithCap_prologue P X hpc hrun hsp0_al hx8
        fun s1 vPad hpc1 hrun1 hsp1 hsp1_al hx0_1 hx19_1 _ _ hup1 hstd1 => SepWP.done hpc1 hrun1 fun hkf1 => ?_
      refine hbWithCap_runToPostAlloc P A X hext hCode0 hkf1 hstk_nw hpc1 hrun1 hsp1 hsp1_al
        (hx0_1.trans hx0) hx19_1 hup1 hstd1 hcap0 hle_max (fun hna => (hna hao).elim)
        fun sa hpca hruna hspa hspa_al hx19_a hx21_a hx22_a hx23_a hbm hup_a hasp_0a => SepWP.done hpca hruna ?_
      by_cases hret0 : sa.readReg64 .x0 = 0#64
      · simp only [hret0, ↓reduceIte]
        have hstk_sh := stackAt_shrink (s0.sp - 64#64) (16 + A.stackBytes) A.stackBytes (by omega) (by omega)
        refine SepWPp.congr_pre (P' := ⌜A.allowOom ∧ ¬ A.CanAlloc lc blk
            (BitVec.ofNat 64 (tableAllocBytes (capToBucketMask cap.toNat))).toNat (8#64).toNat⌝ ∗
          (stackAt (s0.sp - 64#64) (16 + A.stackBytes) ∗
           (A.Heap lc blk sa ∗ hbRodata P.pl ∗ memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad)))
          (by rw [hstk_sh]; ac_rfl) (SepWPp.pure_left fun _ => ?_)
        apply SepWPp.of_sepWP_at (mid := P.pl12.base)
        refine SepWP.mono_frozen (Φ := fun m => sa.mem.KeepsFrozen m)
          (post := fun sm Pm => Pm = stackAt (s0.sp - 64#64) (16 + A.stackBytes) ∗
              (A.Heap lc blk sa ∗ hbRodata P.pl ∗ memRegion mapPtr 32 ∗ hbWithCapFrame s0 vPad) ∧
            sm.sp = s0.sp - 64#64 ∧ sm.spAligned = true ∧ sm.readReg32 .x0 = 1#32)
          (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl sa.mem) ?_ ?_
        · wp_steps
          exact SepWP.done (by simp; bv_lin) (by simp [hruna])
            ⟨rfl, by simp [hspa], by simpa [State.spAligned, hspa] using hspa_al, by simp [Reg.x0, State.readReg32]⟩
        · rintro sm Pm _ _ hkf_am ⟨rfl, hspm, hspm_al, hx0_m⟩ hpcm hrunm
          have hpan_fn := hbFallibilityAllocErr_crossBlock_ok P X (i := 10) (by decide)
            (hbProg10_rebase P X) (φ := A.allowOom ∧ ¬ HbCanWithCapacity A cap lc blk)
            (by simpa using (hext.panic_hooks hao).2)
          exact sepWPp_call_coldPanic (stkTotal := 16 + A.stackBytes) hpan_fn
            (hcl0.of_keepsFrozen (hasp_0a.2.2.2.2.trans hkf_am))
            hpcm hrunm hspm_al hspm rfl hx0_m ⟨hao, hcan⟩ (by omega) ⟨(s0.sp - 64#64).isLt, by omega⟩
      · simp only [hret0, ↓reduceIte]
        exact SepWPp.of_sepWP_ret (SepWP.mono
          (hbWithCap_postAlloc P A X hext hCode0 hasp_0a hal hnw hstk_nw hsp0_al
            hpca hruna hspa hspa_al hret0 hx19_a hx21_a hx22_a hx23_a hbm hup_a)
          fun sf Pf _ _ ⟨hspf, hcsf, hPf⟩ => ⟨Satisfies.mono (sepConj_mono_left hPf), hspf, hcsf⟩)
    · apply SepWPp.of_sepWP_at (mid := P.pl11.base)
      refine SepWP.mono_frozen (Φ := fun m => s0.mem.KeepsFrozen m)
        (post := fun sm Pm => ∃ vPad, Pm = hbWithCapFrame s0 vPad ∗
          (hbRodata P.pl ∗ memRegion mapPtr 32 ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 64#64) (16 + A.stackBytes)) ∧
          sm.sp = s0.sp - 64#64 ∧ sm.spAligned = true ∧ sm.readReg32 .x0 = 1#32)
        (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl s0.mem) ?_ ?_
      · refine hbWithCap_prologue P X hpc hrun hsp0_al hx8 fun s1 vPad hpc1 hrun1 hsp1 hsp1_al hx0_1 _ _ _ _ _ => ?_
        refine SepWP.mono (hbWithCap_overflow_toPanic P X hpc1 hrun1 hsp1 hsp1_al (hx0_1.trans hx0) (Nat.lt_of_not_ge hle_max)) ?_
        rintro sm Pm _ _ ⟨rfl, hspm, hspm_al, hx0_m⟩
        exact ⟨vPad, rfl, hspm, hspm_al, hx0_m⟩
      · rintro sm Pm _ _ hkf_0m ⟨vPad, rfl, hspm, hspm_al, hx0_m⟩ hpcm hrunm
        refine SepWPp.congr_pre (P' := stackAt (s0.sp - 64#64) (16 + A.stackBytes) ∗
          (hbWithCapFrame s0 vPad ∗ hbRodata P.pl ∗ memRegion mapPtr 32 ∗ A.Heap lc blk s0)) (by ac_rfl) ?_
        have hpan_fn := hbCapOverflow_crossBlock_ok P X (i := 10) (by decide)
          (hbProg10_rebase P X) (φ := A.allowOom ∧ ¬ HbCanWithCapacity A cap lc blk)
          (by simpa using (hext.panic_hooks hao).1)
        exact sepWPp_call_coldPanic (stkTotal := 16 + A.stackBytes) hpan_fn (hcl0.of_keepsFrozen hkf_0m)
          hpcm hrunm hspm_al hspm rfl hx0_m ⟨hao, hcan⟩ (by omega) ⟨(s0.sp - 64#64).isLt, by omega⟩

/-! ## `MultiPlacedLib.subroutineOk` Wrappers -/

set_option maxRecDepth 200000 in
theorem hashbrown_with_capacity_infallible_subroutineOk (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X (A mpl)) :
    hashbrownLib.subroutineOk "hashbrown_with_capacity"
      (fun mpl => withCodeInv (A mpl) (hashbrownWithCapacityInfallibleSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_with_capacity" 10 (off := 0) (fun P X' => hbProg10_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownWithCapacityInfallibleSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_with_capacity_infallible_ok P (A P.mpl) X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg10_rebase P X) (hbPl10_eq P)))

set_option maxRecDepth 200000 in
theorem hashbrown_with_capacity_subroutineOk (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X (A mpl)) :
    hashbrownLib.subroutineOk "hashbrown_with_capacity"
      (fun mpl => withCodeInv (A mpl) (hashbrownWithCapacitySpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_withCL "hashbrown_with_capacity" 10 (off := 0) (fun P X' => hbProg10_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownWithCapacitySpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_with_capacity_ok P (A P.mpl) X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg10_rebase P X) (hbPl10_eq P)))

end CaseStudies.Hashbrown.Proofs
