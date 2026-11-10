/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.SwissTable.Proofs.Group

/-!
# SwissTable Triangular Probe Sequence and Reachability

Defines the triangular probe position `probePos` and slot-reachability predicate `ProbeReachable`
over a 64-bit hash value, and proves that `triGroupIdx` is surjective modulo any power of two, so
every probe chain visits every group (`exists_empty_probe_group_of_empty_slot`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.SwissTable

open Arm64 ProofLib

/-! ## Probe Positions -/

/-- Starting index `((h + triByteOff step) & bm).toNat < buckets` of the `step`-th probe group
    for hash `h`. -/
def probePos (bm h : BitVec 64) (step : Nat) : Nat :=
  ((h + BitVec.ofNat 64 (triByteOff step)) &&& bm).toNat

/-- Full slot `i < buckets` is reachable along the triangular probe chain of hash `h`:
    at some `step < numGroups bm` and `lane < 8`, lane `lane` of `ctrlGroupAt ctrl (probePos bm h step)`
    holds `tagOfHash h` with `(probePos bm h step + lane) % buckets = i`, and no strictly earlier
    group `s' < step` contains `tagEmpty` (`0xff#8`). -/
def ProbeReachable (bm : BitVec 64) (ctrl : List (BitVec 8)) (h : BitVec 64) (i : Nat) : Prop :=
  let buckets := bm.toNat + 1
  ∃ step lane : Nat,
    step < numGroups bm ∧
    lane < 8 ∧
    (ctrlGroupAt ctrl (probePos bm h step))[lane]? = some (tagOfHash h) ∧
    (probePos bm h step + lane) % buckets = i ∧
    ∀ s' < step, tagEmpty ∉ ctrlGroupAt ctrl (probePos bm h s')

@[simp]
theorem probePos_zero (bm h : BitVec 64) : probePos bm h 0 = (h &&& bm).toNat := by
  simp [probePos]

theorem probePos_lt_buckets {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (h : BitVec 64) (step : Nat) : probePos bm h step < bm.toNat + 1 :=
  hbm.and_lt_buckets _

theorem probePos_bv_eq (bm h : BitVec 64) (step : Nat) :
    ((h + BitVec.ofNat 64 (triByteOff step)) &&& bm) =
      BitVec.ofNat 64 (probePos bm h step) := by
  unfold probePos
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem probePos_step_bv {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (h : BitVec 64) (step : Nat) :
    ((BitVec.ofNat 64 (probePos bm h step) + (BitVec.ofNat 64 (8 * step) + 8#64)) &&& bm) =
      BitVec.ofNat 64 (probePos bm h (step + 1)) := by
  have hstr : BitVec.ofNat 64 (8 * step) + 8#64 = BitVec.ofNat 64 (8 * (step + 1)) := by
    rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add]
  rw [← probePos_bv_eq, hstr, hbm.add_and_eq, BitVec.add_assoc, ← BitVec.ofNat_add,
    ← triByteOff_succ, probePos_bv_eq]

theorem probePos_eq_add_mod {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (h : BitVec 64) (step : Nat) :
    probePos bm h step = (probePos bm h 0 + 8 * triGroupIdx step) % (bm.toNat + 1) := by
  rcases hbm.buckets_bounds_dvd with ⟨_, _, hdvd⟩
  unfold probePos
  rw [triByteOff_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero,
    hbm.and_toNat_eq_mod, hbm.and_toNat_eq_mod, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ hdvd, ← triByteOff_eq_eight_mul_triGroupIdx, Nat.add_mod,
    Nat.mod_mod_of_dvd _ hdvd, ← Nat.add_mod, ← Nat.mod_add_mod]

/-! ## Triangular Probe Sequence Completeness -/

private theorem pow2_dvd_mul_of_odd :
    ∀ (k a b : Nat), b % 2 = 1 → 2 ^ k ∣ a * b → 2 ^ k ∣ a
  | 0, _, _, _, _ => Nat.one_dvd _
  | k + 1, a, b, hodd, ⟨c, hc⟩ => by
    have h2c : 2 ^ (k + 1) * c = 2 * (2 ^ k * c) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    have ha2 : a % 2 = 0 := by
      have hm : (a * b) % 2 = (2 ^ (k + 1) * c) % 2 := congrArg (· % 2) hc
      rw [h2c, Nat.mul_mod, hodd] at hm; omega
    have hk : 2 ^ k ∣ (a / 2) * b := ⟨c, by
      have ha : a = 2 * (a / 2) := by omega
      have hmul : (2 * (a / 2)) * b = 2 * ((a / 2) * b) := Nat.mul_assoc 2 (a / 2) b
      rw [ha, hmul, h2c] at hc; omega⟩
    rcases pow2_dvd_mul_of_odd k (a / 2) b hodd hk with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    omega

theorem triGroupIdx_inj_mod_pow2 (m : Nat) {a b : Nat} (hab : a < b) (hb : b < 2 ^ m) :
    triGroupIdx a % 2 ^ m ≠ triGroupIdx b % 2 ^ m := by
  intro heq
  have h2a : 2 * triGroupIdx a = a * (a + 1) := by
    have h := triByteOff_eq_eight_mul_triGroupIdx a; unfold triByteOff at h
    rw [Nat.mul_assoc] at h; omega
  have h2b : 2 * triGroupIdx b = b * (b + 1) := by
    have h := triByteOff_eq_eight_mul_triGroupIdx b; unfold triByteOff at h
    rw [Nat.mul_assoc] at h; omega
  have hprod : (b - a) * (b + a + 1) = 2 * (triGroupIdx b - triGroupIdx a) := by
    have hd : b = a + (b - a) := by omega
    have hexp : (a + (b - a)) * (a + (b - a) + 1) =
        a * (a + 1) + (b - a) * (a + (b - a) + a + 1) := by
      calc (a + (b - a)) * (a + (b - a) + 1)
          = a * (a + (b - a) + 1) + (b - a) * (a + (b - a) + 1) := Nat.add_mul ..
        _ = a * ((a + 1) + (b - a)) + (b - a) * (a + (b - a) + 1) := by congr 2; omega
        _ = a * (a + 1) + a * (b - a) + (b - a) * (a + (b - a) + 1) := by rw [Nat.mul_add]
        _ = a * (a + 1) + ((b - a) * a + (b - a) * (a + (b - a) + 1)) := by
              rw [Nat.mul_comm a (b - a), Nat.add_assoc]
        _ = a * (a + 1) + (b - a) * (a + (b - a) + a + 1) := by
              rw [← Nat.mul_add]; congr 2; omega
    rw [← hd] at hexp; omega
  have hdvd : 2 ^ m ∣ triGroupIdx b - triGroupIdx a := by
    refine ⟨triGroupIdx b / 2 ^ m - triGroupIdx a / 2 ^ m, ?_⟩
    have h1 := Nat.div_add_mod (triGroupIdx a) (2 ^ m)
    have h2 := Nat.div_add_mod (triGroupIdx b) (2 ^ m)
    have h3 : 2 ^ m * (triGroupIdx b / 2 ^ m - triGroupIdx a / 2 ^ m) =
        2 ^ m * (triGroupIdx b / 2 ^ m) - 2 ^ m * (triGroupIdx a / 2 ^ m) := Nat.mul_sub ..
    omega
  rcases hdvd with ⟨q, hq⟩
  have hdvd2 : 2 ^ (m + 1) ∣ (b - a) * (b + a + 1) :=
    ⟨q, by rw [hprod, hq, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc]⟩
  have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
  by_cases hs : (b + a + 1) % 2 = 1
  · have hle := Nat.le_of_dvd (by omega) (pow2_dvd_mul_of_odd (m + 1) (b - a) (b + a + 1) hs hdvd2)
    omega
  · have hd_odd : (b - a) % 2 = 1 := by omega
    rw [Nat.mul_comm] at hdvd2
    have hle := Nat.le_of_dvd (by omega) (pow2_dvd_mul_of_odd (m + 1) (b + a + 1) (b - a) hd_odd hdvd2)
    omega

private def inPfx (f : Nat → Nat) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, y => inPfx f k y || (f k == y)

private theorem inPfx_iff (f : Nat → Nat) : ∀ k y, inPfx f k y = true ↔ ∃ i < k, f i = y
  | 0, _ => by simp [inPfx]
  | k + 1, y => by
    simp only [inPfx, Bool.or_eq_true, inPfx_iff f k y, beq_iff_eq]
    exact ⟨fun h => h.elim (fun ⟨i, hi, e⟩ => ⟨i, by omega, e⟩) (fun e => ⟨k, by omega, e⟩),
      fun ⟨i, hi, e⟩ => if h : i < k then Or.inl ⟨i, h, e⟩ else
        Or.inr ((by omega : i = k) ▸ e)⟩

def cntTrue (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cntTrue p n + if p n then 1 else 0

theorem cntTrue_congr {p q : Nat → Bool} :
    ∀ n, (∀ y < n, p y = q y) → cntTrue p n = cntTrue q n
  | 0, _ => rfl
  | n + 1, h => by simp [cntTrue, cntTrue_congr n (fun y hy => h y (by omega)), h n (by omega)]

theorem cntTrue_set (p : Nat → Bool) (x : Nat) :
    ∀ n, x < n → p x = false → cntTrue (fun y => p y || (x == y)) n = cntTrue p n + 1
  | 0, hx, _ => by omega
  | n + 1, hx, hpx => by
    simp only [cntTrue]
    by_cases hxn : x = n
    · subst hxn
      rw [cntTrue_congr (p := fun y => p y || (x == y)) (q := p) x
        (fun y hy => by simp [beq_eq_false_iff_ne.2 (by omega : x ≠ y)])]
      simp [hpx]
    · rw [cntTrue_set p x n (by omega) hpx]
      simp [beq_eq_false_iff_ne.2 (by omega : x ≠ n)]; omega

theorem cntTrue_lt_of_false (p : Nat → Bool) (y : Nat) :
    ∀ n, y < n → p y = false → cntTrue p n < n
  | 0, hy, _ => by omega
  | n + 1, hy, hpy => by
    have hle : ∀ m, cntTrue p m ≤ m := fun m => by
      induction m with | zero => simp [cntTrue] | succ m ih => simp only [cntTrue]; split <;> omega
    simp only [cntTrue]
    by_cases hyn : y = n
    · subst hyn; simp [hpy]; have := hle y; omega
    · have := cntTrue_lt_of_false p y n (by omega) hpy; split <;> omega

theorem exists_triGroupIdx_mod_pow2 (m g0 target : Nat) (ht : target < 2 ^ m) :
    ∃ step < 2 ^ m, (g0 + triGroupIdx step) % 2 ^ m = target := by
  let M := 2 ^ m
  have hM : 0 < M := Nat.one_le_pow m 2 (by decide)
  let f := fun s => (g0 + triGroupIdx s) % M
  have hinj : ∀ a b, a < b → b < M → f a ≠ f b := by
    intro a b hab hb heq
    let c := M * (g0 / M + 1) - g0
    have hc : c + g0 = M * (g0 / M + 1) := by
      have h1 := Nat.div_add_mod g0 M
      have h2 := Nat.mod_lt g0 hM
      have h3 : M * (g0 / M + 1) = M * (g0 / M) + M := Nat.mul_succ M (g0 / M)
      omega
    have hcancel : ∀ z, (c + (g0 + z) % M) % M = z % M := fun z => by
      rw [Nat.add_mod_mod, ← Nat.add_assoc, hc, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
        Nat.mod_mod]
    have htri : triGroupIdx a % M = triGroupIdx b % M := by
      dsimp only [f] at heq
      rw [← hcancel (triGroupIdx a), ← hcancel (triGroupIdx b), heq]
    exact triGroupIdx_inj_mod_pow2 m hab hb htri
  have hcnt : ∀ k ≤ M, cntTrue (inPfx f k) M = k := by
    intro k hk
    induction k with
    | zero =>
      clear hk ht; dsimp only [inPfx]
      induction M with | zero => rfl | succ n ih => simp [cntTrue, ih]
    | succ k ih =>
      have hfk : inPfx f k (f k) = false :=
        Classical.byContradiction fun hne => by
          have htrue : inPfx f k (f k) = true := by cases h : inPfx f k (f k) <;> simp_all
          rcases (inPfx_iff f k (f k)).1 htrue with ⟨i, hik, hfi⟩
          exact hinj i k hik (by omega) hfi
      change cntTrue (fun y => inPfx f k y || (f k == y)) M = k + 1
      rw [cntTrue_set (inPfx f k) (f k) M (Nat.mod_lt _ hM) hfk, ih (by omega)]
  apply (inPfx_iff f M target).1
  cases h : inPfx f M target with
  | true => rfl
  | false =>
    have hlt := cntTrue_lt_of_false (inPfx f M) target M ht h
    have heq := hcnt M (Nat.le_refl M)
    omega

/-- If some slot `e < buckets` is `tagEmpty`, then the probe chain of every hash `h` reaches a
    group containing `tagEmpty` within `numGroups bm` steps. -/
theorem exists_empty_probe_group_of_empty_slot {bm : BitVec 64} {ctrl : List (BitVec 8)}
    (hbm : ValidBucketMask bm) (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    (hemp : ∃ (e : Nat) (_ : e < bm.toNat + 1),
      ctrl[e]'(by have hlen := hm.1; omega) = tagEmpty)
    (h : BitVec 64) :
    ∃ step < numGroups bm, tagEmpty ∈ ctrlGroupAt ctrl (probePos bm h step) := by
  rcases hbm.buckets_cases with h4 | ⟨h8, _⟩
  · rcases hbm.numGroups_pow2 with ⟨gExp, hng, _, _⟩
    have hpos : 0 < numGroups bm := by rw [hng]; exact Nat.one_le_pow gExp 2 (by decide)
    exact ⟨0, hpos, CtrlMirrorInv.empty_in_group_of_eq4 (h4 ▸ hm)
      (by have := probePos_lt_buckets hbm h 0; omega)⟩
  · rcases hbm.numGroups_pow2 with ⟨gExp, hng, _, hbuck8⟩
    have hb8 := hbuck8 h8
    let G := 2 ^ gExp
    have hG : 0 < G := Nat.one_le_pow gExp 2 (by decide)
    rcases hemp with ⟨e, he_lt, he_emp⟩
    let pos0 := probePos bm h 0
    have hpos0 : pos0 < 8 * G := by have := probePos_lt_buckets hbm h 0; omega
    let delta := (e + 8 * G - pos0) % (8 * G)
    have hdelta : delta < 8 * G := Nat.mod_lt _ (by omega)
    rcases exists_triGroupIdx_mod_pow2 gExp (pos0 / 8) ((pos0 / 8 + delta / 8) % G)
        (Nat.mod_lt _ hG) with ⟨step, hstep, hmodG⟩
    refine ⟨step, by omega, ?_⟩
    have hlen : ctrl.length = (bm.toNat + 1) + 8 := hm.1
    have hpos_s : probePos bm h step < bm.toNat + 1 := probePos_lt_buckets hbm h step
    rw [mem_ctrlGroupAt_iff (by omega)]
    refine ⟨delta % 8, by omega, ?_⟩
    rw [CtrlMirrorInv.lane_eq_mod_of_ge8 hm h8 hpos_s (by omega)]
    have hidx : (probePos bm h step + delta % 8) % (bm.toNat + 1) = e := by
      rw [probePos_eq_add_mod hbm h step, hb8, Nat.mod_add_mod]
      have hp0 : pos0 = 8 * (pos0 / 8) + pos0 % 8 := (Nat.div_add_mod pos0 8).symm
      have hdl : delta = 8 * (delta / 8) + delta % 8 := (Nat.div_add_mod delta 8).symm
      have h1 : pos0 + 8 * triGroupIdx step + delta % 8 =
          8 * (pos0 / 8 + triGroupIdx step) + (pos0 % 8 + delta % 8) := by omega
      have h2 : pos0 + delta = 8 * (pos0 / 8 + delta / 8) + (pos0 % 8 + delta % 8) := by omega
      have hm8 : ∀ x, (8 * x) % (8 * G) = 8 * (x % G) := fun x => Nat.mul_mod_mul_left 8 x G
      rw [h1, Nat.add_mod, hm8, hmodG, ← hm8, ← Nat.add_mod, ← h2]
      dsimp only [delta]
      rw [Nat.add_mod_mod, show pos0 + (e + 8 * G - pos0) = e + 8 * G by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [hidx, he_emp]

end VerifiedLibraries.SwissTable
