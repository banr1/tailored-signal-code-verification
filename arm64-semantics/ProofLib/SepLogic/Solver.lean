/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import ProofLib.SepLogic
public import ProofLib.Lemmas
public import ProofLib.BV.Arith
public import ProofLib.SepLogic.OmegaBounded
import ProofLib.SepLogic.Model

/-!
# Reflective AC Separation-Logic Solver

Reflective AC normalization, frame cancellation, container splitting, and store-update engine
over `SepBlock` instances. Reifies `∗`-trees over a balanced `SepAtomTree` table to prove AC
rearrangements in $O(N \log N)$ via `SepTree.eq_of_sortIdx`, and provides the `sep_entail`,
`sep_focus`, `sep_eq`, and `sep_facts` tactics.
-/

namespace ProofLib

open Arm64

@[expose] public section

/-! ## Kernel lemmas used by the solver -/


/-- Reflective AC transport of a `Satisfies` proof over a balanced atom table, with the
    `O(N log N)` sorted-index certificate (`SepTree.eq_of_sortIdx`). -/
theorem SepTree.sat_of_sortIdx {m : Memory} (tbl : SepAtomTree) (t₁ t₂ : SepTree)
    (hp : SepTree.idxBEq t₁.sortIdx t₂.sortIdx = true) (h : m ⊨ t₁.denoteT tbl) :
    m ⊨ t₂.denoteT tbl :=
  cast (congrArg (fun P => m ⊨ P) (SepTree.eq_of_sortIdx tbl.get t₁ t₂ hp)) h

theorem Satisfies.head_congr {m : Memory} {A B R : SepProp} (e : A = B) (h : m ⊨ A ∗ R) :
    m ⊨ B ∗ R :=
  e ▸ h

theorem Satisfies.congr_prop {m : Memory} {P Q : SepProp} (e : P = Q) (h : m ⊨ P) :
    m ⊨ Q :=
  e ▸ h

theorem Satisfies.pure_intro {m : Memory} {φ : Prop} {R : SepProp} (hφ : φ) (h : m ⊨ R) :
    m ⊨ ⌜φ⌝ ∗ R :=
  (satisfies_pure_sepConj φ R m).mpr ⟨hφ, h⟩

namespace IsBlock

/-- Two blocks over the same region with equivalent content descriptions are the same assertion. -/
theorem eq_of_iff {P Q : SepProp} {b : BitVec 64} {n : Nat} {Φ : Memory → Prop} {Ψ : Memory → Prop}
    (hP : IsBlock P b n Φ) (hQ : IsBlock Q b n Ψ) (h : ∀ m, Φ m ↔ Ψ m) : P = Q := by
  ext hp
  rw [hP.iff, hQ.iff]
  exact exists_congr fun m => and_congr_left fun _ => h m

/-- Any owned block entails the untyped writable `memRegion` over the same byte range. -/
theorem entails_memRegion {P : SepProp} {b : BitVec 64} {n : Nat} {Φ : Memory → Prop}
    (hP : IsBlock P b n Φ) : P ⊢ Arm64.memRegion b n :=
  hP.entails (IsBlock.memRegion b n) (fun _ _ => trivial)

end IsBlock

/-- A region splits into two adjacent regions. -/
theorem memRegion_split (b : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion b (n + k) = memRegion b n ∗ memRegion (b + BitVec.ofNat 64 n) k :=
  IsBlock.eq_of_iff (IsBlock.memRegion b (n + k))
    ((IsBlock.memRegion b n).sepConj (IsBlock.memRegion _ k) rfl h)
    (fun _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩)

/-- `memRegion_split` at an explicit split address `b'`. -/
theorem memRegion_split' {b b' : BitVec 64} {n k N : Nat} (hN : N = n + k)
    (hb : b' = b + BitVec.ofNat 64 n) (h : N ≤ 2 ^ 64) :
    memRegion b N = memRegion b n ∗ memRegion b' k := by
  subst hN hb; exact memRegion_split b n k h

/-- A 1-byte region is an existential 8-bit cell. -/
theorem memRegion_one (a : BitVec 64) : memRegion a 1 = (∃∗ v : BitVec 8, a ↦₈ v) :=
  IsBlock.eq_of_iff (IsBlock.memRegion a 1) (IsBlock.sepExists fun v => IsBlock.pointsTo8 a v)
    (fun m => ⟨fun _ => ⟨m.read8 a, rfl⟩, fun _ => trivial⟩)

/-- An 8-bit cell is a 1-byte region (forgetting its value). -/
theorem pointsTo8_entails_memRegion (a : BitVec 64) (v : BitVec 8) : (a ↦₈ v) ⊢ memRegion a 1 := by
  rw [memRegion_one]; exact Entails.sepExists_intro v

/-- A 2-byte region is an existential 16-bit cell. -/
theorem memRegion_two (a : BitVec 64) : memRegion a 2 = (∃∗ v : BitVec 16, a ↦₁₆ v) :=
  IsBlock.eq_of_iff (IsBlock.memRegion a 2) (IsBlock.sepExists fun v => IsBlock.pointsTo16 a v)
    (fun m => ⟨fun _ => ⟨m.read16 a, rfl⟩, fun _ => trivial⟩)

/-- A 16-bit cell is a 2-byte region (forgetting its value). -/
theorem pointsTo16_entails_memRegion (a : BitVec 64) (v : BitVec 16) : (a ↦₁₆ v) ⊢ memRegion a 2 := by
  rw [memRegion_two]; exact Entails.sepExists_intro v

/-- A 4-byte region is an existential 32-bit cell. -/
theorem memRegion_four (a : BitVec 64) : memRegion a 4 = (∃∗ v : BitVec 32, a ↦₃₂ v) :=
  IsBlock.eq_of_iff (IsBlock.memRegion a 4) (IsBlock.sepExists fun v => IsBlock.pointsTo32 a v)
    (fun m => ⟨fun _ => ⟨m.read32 a, rfl⟩, fun _ => trivial⟩)

/-- A 32-bit cell is a 4-byte region (forgetting its value). -/
theorem pointsTo32_entails_memRegion (a : BitVec 64) (v : BitVec 32) : (a ↦₃₂ v) ⊢ memRegion a 4 := by
  rw [memRegion_four]; exact Entails.sepExists_intro v

/-- An 8-byte region is an existential 64-bit cell. -/
theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = (∃∗ v : BitVec 64, a ↦₆₄ v) :=
  IsBlock.eq_of_iff (IsBlock.memRegion a 8) (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    (fun m => ⟨fun _ => ⟨m.read64 a, rfl⟩, fun _ => trivial⟩)

/-- A 64-bit cell is an 8-byte region (forgetting its value). -/
theorem pointsTo64_entails_memRegion (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [memRegion_eight]; exact Entails.sepExists_intro v

/-- A 16-byte region is an existential 128-bit cell. -/
theorem memRegion_sixteen (a : BitVec 64) : memRegion a 16 = (∃∗ v : BitVec 128, a ↦₁₂₈ v) :=
  IsBlock.eq_of_iff (IsBlock.memRegion a 16) (IsBlock.sepExists fun v => IsBlock.pointsTo128 a v)
    (fun m => ⟨fun _ => ⟨m.read128 a, rfl⟩, fun _ => trivial⟩)


/-- Split an `m`-byte slice at offset `k` out of `memRegion b N` (`k + m ≤ N`). -/
theorem memRegion_split3 (b : BitVec 64) (N k m : Nat) (hk : k + m ≤ N) (hN : N ≤ 2 ^ 64) :
    memRegion b N =
      memRegion (b + BitVec.ofNat 64 k) m ∗
        (memRegion b k ∗ memRegion (b + BitVec.ofNat 64 (k + m)) (N - k - m)) := by
  rw [memRegion_split' (n := k) (k := N - k) (by omega) rfl hN,
      memRegion_split' (b := b + BitVec.ofNat 64 k) (n := m) (k := N - k - m) (by omega)
        (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by omega)]
  ac_rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] regionHeap Heap.empty in
private theorem emp_isBlock (b : BitVec 64) : IsBlock SepProp.emp b 0 (fun _ => True) := by
  refine ⟨fun h => ?_, fun _ _ _ _ => trivial⟩
  have hr : regionHeap b 0 (default : Memory) = Heap.empty := by
    refine Heap.ext_phys fun x => ?_
    simp [regionHeap, InRegion, Heap.empty]
  simp only [SepProp.holds_emp_iff]
  constructor
  · intro hh
    exact ⟨default, trivial, by rw [hr]; exact hh⟩
  · rintro ⟨m, -, rfl⟩
    refine Heap.ext_phys fun x => ?_
    simp [regionHeap, InRegion, Heap.empty]

/-- An empty region is `emp`. -/
theorem memRegion_zero (b : BitVec 64) : memRegion b 0 = SepProp.emp :=
  IsBlock.eq_of_iff (IsBlock.memRegion b 0) (emp_isBlock b) (fun _ => Iff.rfl)

theorem memRegion_add_ofNat_sub_toNat (p q : BitVec 64) :
    p + BitVec.ofNat 64 (q - p).toNat = q := by
  have h : BitVec.ofNat 64 (q - p).toNat = q - p := BitVec.ofNat_toNat 64 (q - p)
  rw [h, BitVec.sub_eq_add_neg, BitVec.add_comm q (-p), ← BitVec.add_assoc,
      BitVec.add_neg_eq_sub, BitVec.sub_self, BitVec.zero_add]

theorem memRegion_subblock_exact {p q : BitVec 64} {n w : Nat}
    (hq : p = q) (hw : n = w) :
    memRegion p n = memRegion q w := by
  subst hq hw; rfl

theorem memRegion_subblock_prefix {p q r : BitVec 64} {n w rem : Nat}
    (hq : p = q) (hr : q + BitVec.ofNat 64 w = r) (hrem : n - w = rem)
    (hw : w ≤ n) (hn : n ≤ 2 ^ 64) :
    memRegion p n = memRegion q w ∗ memRegion r rem := by
  subst hq hr hrem
  exact memRegion_split' (by omega) rfl hn

theorem memRegion_subblock_suffix {p q : BitVec 64} {n k w : Nat}
    (hq : p + BitVec.ofNat 64 k = q) (hkw : k + w = n) (hn : n ≤ 2 ^ 64) :
    memRegion p n = memRegion q w ∗ memRegion p k := by
  subst hq hkw
  rw [memRegion_split p k w hn, sepConj_comm]

theorem memRegion_subblock_mid {p q r : BitVec 64} {n k w rem : Nat}
    (hq : p + BitVec.ofNat 64 k = q) (hr : q + BitVec.ofNat 64 w = r)
    (hrem : n - k - w = rem) (hkw : k + w ≤ n) (hn : n ≤ 2 ^ 64) :
    memRegion p n = memRegion q w ∗ (memRegion p k ∗ memRegion r rem) := by
  subst hq hr hrem
  rw [memRegion_split3 p n k w hkw hn]
  congr 3
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bitvec64_sub_sub_fold (x a b c : BitVec 64) (h : a + b = c) :
    (x - a) - b = x - c := by
  subst h; bv_omega

theorem bitvec64_sub_sub_zero (x a b : BitVec 64) (h : a + b = 0#64) :
    (x - a) - b = x := by
  have : (x - a) - b = x - (a + b) := by bv_omega
  rw [this, h, BitVec.sub_zero]

theorem bitvec64_sub_add_fold_sub (x a b c : BitVec 64) (h : a - b = c) :
    (x - a) + b = x - c := by
  subst h; bv_omega

theorem bitvec64_sub_add_fold_add (x a b c : BitVec 64) (h : b - a = c) :
    (x - a) + b = x + c := by
  subst h; bv_omega

theorem bitvec64_sub_add_zero (x a b : BitVec 64) (h : a = b) :
    (x - a) + b = x := by
  subst h; bv_omega

theorem bitvec64_add_sub_fold_sub (x a b c : BitVec 64) (h : b - a = c) :
    (x + a) - b = x - c := by
  subst h; bv_omega

theorem bitvec64_add_sub_fold_add (x a b c : BitVec 64) (h : a - b = c) :
    (x + a) - b = x + c := by
  subst h; bv_omega

theorem bitvec64_add_sub_zero (x a b : BitVec 64) (h : a = b) :
    (x + a) - b = x := by
  subst h; bv_omega

theorem bitvec64_add_add_fold (x a b c : BitVec 64) (h : a + b = c) :
    (x + a) + b = x + c := by
  subst h; bv_omega

theorem bitvec64_add_add_zero (x a b : BitVec 64) (h : a + b = 0#64) :
    (x + a) + b = x := by
  have : (x + a) + b = x + (a + b) := by bv_omega
  rw [this, h, BitVec.add_zero]


theorem bitvec64_add_neg_lit_eq_sub (x a c : BitVec 64) (h : a + c = 0#64) :
    x + a = x - c := by
  have : x + a = (x + (a + c)) - c := by bv_omega
  rw [this, h, BitVec.add_zero]

theorem read64_lo_hi_of_read128 {m : Memory} {a : BitVec 64} {v : BitVec 128}
    (h : m.read128 a = v) :
    m.read64 a = v.extractLsb' 0 64 ∧ m.read64 (a + 8#64) = v.extractLsb' 64 64 := by
  subst h
  simp only [Memory.read128]
  generalize m.read64 a = lo
  generalize m.read64 (a + 8#64) = hi
  constructor <;> bv_decide

namespace IsBlock

variable {P R : SepProp} {a : BitVec 64} {Φ : Memory → Prop} {m : Memory}

/-- A byte store at the base of a 1-byte block. -/
theorem write8 (hb : IsBlock P a 1 Φ) (h : m ⊨ P ∗ R) (v : BitVec 8) :
    m.write8 a v ⊨ (a ↦₈ v) ∗ R :=
  hb.update (pointsTo8 a v) (Nat.le_refl _) h
    ((AgreesOutside.rfl' m a 1).write8 (by simp [InRegion])) (Memory.read8_write8_same ..)

/-- A 16-bit store at the base of a 2-byte block. -/
theorem write16 (hb : IsBlock P a 2 Φ) (h : m ⊨ P ∗ R) (v : BitVec 16) :
    m.write16 a v ⊨ (a ↦₁₆ v) ∗ R :=
  hb.update (pointsTo16 a v) (Nat.le_refl _) h
    ((AgreesOutside.rfl' m a 2).write16 (by simp) (by decide)) (Memory.read16_write16_same ..)

/-- A 32-bit store at the base of a 4-byte block. -/
theorem write32 (hb : IsBlock P a 4 Φ) (h : m ⊨ P ∗ R) (v : BitVec 32) :
    m.write32 a v ⊨ (a ↦₃₂ v) ∗ R :=
  hb.update (pointsTo32 a v) (Nat.le_refl _) h
    ((AgreesOutside.rfl' m a 4).write32 (by simp) (by decide)) (Memory.read32_write32_same ..)

/-- A 64-bit store at the base of an 8-byte block. -/
theorem write64 (hb : IsBlock P a 8 Φ) (h : m ⊨ P ∗ R) (v : BitVec 64) :
    m.write64 a v ⊨ (a ↦₆₄ v) ∗ R :=
  hb.update (pointsTo64 a v) (Nat.le_refl _) h
    ((AgreesOutside.rfl' m a 8).write64 (by simp) (by decide)) (Memory.read64_write64_same ..)

/-- A 128-bit store at the base of a 16-byte block. -/
theorem write128 (hb : IsBlock P a 16 Φ) (h : m ⊨ P ∗ R) (v : BitVec 128) :
    m.write128 a v ⊨ (a ↦₁₂₈ v) ∗ R :=
  hb.update (pointsTo128 a v) (Nat.le_refl _) h
    ((AgreesOutside.rfl' m a 16).write128 (by simp) (by decide)) (read128_write128_same ..)

end IsBlock

/-! ### Word-array element access

Read/write lemmas for the contiguous 64-bit word-array points-to assertion `a ↦₆₄* ws`,
relating raw `Memory.read64` / `Memory.write64` accesses at `a + 8 * i` (or `a + (i <<< 3)`) to
the owned ghost list `ws`. -/

/-- Reading the `i`-th element of an owned word array `a ↦₆₄* ws`. -/
theorem read64_of_words {m : Memory} :
    ∀ (ws : List (BitVec 64)) (a : BitVec 64) (i : Nat) {R : SepProp},
      (m ⊨ (a ↦₆₄* ws) ∗ R) → i < ws.length →
      m.read64 (a + BitVec.ofNat 64 (8 * i)) = ws.getD i 0#64
  | [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | w :: ws, a, 0, R, h, _ => by
      rw [pointsToWords64_cons, sepConj_assoc] at h
      simpa using (IsBlock.pointsTo64 a w).read h
  | w :: ws, a, i + 1, R, h, hi => by
      rw [pointsToWords64_cons, sepConj_assoc, sepConj_left_comm] at h
      have haddr : a + BitVec.ofNat 64 (8 * (i + 1)) = (a + 8#64) + BitVec.ofNat 64 (8 * i) := by
        rw [Nat.mul_succ, Nat.add_comm _ 8, BitVec.ofNat_add, ← BitVec.add_assoc]
      rw [haddr, read64_of_words ws (a + 8#64) i h (by simpa using hi)]
      simp

/-- Writing the `i`-th element of an owned word array `a ↦₆₄* ws` yields `a ↦₆₄* ws.set i v`. -/
theorem write64_words {m : Memory} (v : BitVec 64) :
    ∀ (ws : List (BitVec 64)) (a : BitVec 64) (i : Nat) {R : SepProp},
      (m ⊨ (a ↦₆₄* ws) ∗ R) → i < ws.length →
      (m.write64 (a + BitVec.ofNat 64 (8 * i)) v ⊨ (a ↦₆₄* ws.set i v) ∗ R)
  | [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | w :: ws, a, 0, R, h, _ => by
      rw [pointsToWords64_cons, sepConj_assoc] at h
      have h' := (IsBlock.pointsTo64 a w).write64 h v
      simpa [sepConj_assoc] using h'
  | w :: ws, a, i + 1, R, h, hi => by
      rw [pointsToWords64_cons, sepConj_assoc, sepConj_left_comm] at h
      have h' := write64_words v ws (a + 8#64) i h (by simpa using hi)
      have haddr : a + BitVec.ofNat 64 (8 * (i + 1)) = (a + 8#64) + BitVec.ofNat 64 (8 * i) := by
        rw [Nat.mul_succ, Nat.add_comm _ 8, BitVec.ofNat_add, ← BitVec.add_assoc]
      rw [haddr]
      rw [List.set_cons_succ, pointsToWords64_cons, sepConj_assoc, sepConj_left_comm]
      exact h'

/-- `i <<< 3` as a byte offset `8 * i` for word-array indexing. -/
theorem shl3_eq_ofNat (i : BitVec 64) : (i <<< 3) = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- Reading element `i` (a `BitVec 64` index scaled by `lsl #3`) of an owned word array. -/
theorem read64_shl3_of_words {m : Memory} {ws : List (BitVec 64)} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ (a ↦₆₄* ws) ∗ R) (i : BitVec 64) (hi : i.toNat < ws.length) :
    m.read64 (a + (i <<< 3)) = ws.getD i.toNat 0#64 := by
  rw [shl3_eq_ofNat]; exact read64_of_words ws a i.toNat h hi

/-- Writing element `i` (a `BitVec 64` index scaled by `lsl #3`) of an owned word array. -/
theorem write64_shl3_of_words {m : Memory} {ws : List (BitVec 64)} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ (a ↦₆₄* ws) ∗ R) (i : BitVec 64) (hi : i.toNat < ws.length) (v : BitVec 64) :
    m.write64 (a + (i <<< 3)) v ⊨ (a ↦₆₄* ws.set i.toNat v) ∗ R := by
  rw [shl3_eq_ofNat]; exact write64_words v ws a i.toNat h hi

/-- The `i`-th element of an owned word array is readable and writable (`p` is `canRead` or
    `canWrite`, both of which hold on an owned 8-byte block). -/
theorem canAccess_of_words {m : Memory} (p : Memory → BitVec 64 → Nat → Bool)
    (hp : ∀ (a : BitVec 64) (v : BitVec 64) (R : SepProp) (m : Memory), m ⊨ (a ↦₆₄ v) ∗ R → p m a 8 = true) :
    ∀ (ws : List (BitVec 64)) (a : BitVec 64) (i : Nat) {R : SepProp},
      (m ⊨ (a ↦₆₄* ws) ∗ R) → i < ws.length → p m (a + BitVec.ofNat 64 (8 * i)) 8 = true
  | [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | w :: ws, a, 0, R, h, _ => by
      rw [pointsToWords64_cons, sepConj_assoc] at h
      simpa using hp a w _ m h
  | w :: ws, a, i + 1, R, h, hi => by
      rw [pointsToWords64_cons, sepConj_assoc, sepConj_left_comm] at h
      have haddr : a + BitVec.ofNat 64 (8 * (i + 1)) = (a + 8#64) + BitVec.ofNat 64 (8 * i) := by
        rw [Nat.mul_succ, Nat.add_comm _ 8, BitVec.ofNat_add, ← BitVec.add_assoc]
      rw [haddr]
      exact canAccess_of_words p hp ws (a + 8#64) i h (by simpa using hi)

/-- The `i`-th element of an owned word array `a ↦₆₄* ws` is readable (`8` bytes at `a + 8 * i`). -/
theorem canRead_of_words {m : Memory} (ws : List (BitVec 64)) (a : BitVec 64) (i : Nat)
    {R : SepProp} (h : m ⊨ (a ↦₆₄* ws) ∗ R) (hi : i < ws.length) :
    m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true :=
  canAccess_of_words Memory.canRead
    (fun a v _ _ h => (IsBlock.pointsTo64 a v).canRead (by decide) h) ws a i h hi

/-- The `i`-th element of an owned word array `a ↦₆₄* ws` is writable (`8` bytes at `a + 8 * i`). -/
theorem canWrite_of_words {m : Memory} (ws : List (BitVec 64)) (a : BitVec 64) (i : Nat)
    {R : SepProp} (h : m ⊨ (a ↦₆₄* ws) ∗ R) (hi : i < ws.length) :
    m.canWrite (a + BitVec.ofNat 64 (8 * i)) 8 = true :=
  canAccess_of_words Memory.canWrite
    (fun a v _ _ h => (IsBlock.pointsTo64 a v).canWrite (by decide) h) ws a i h hi

theorem canRead_shl3_of_words {m : Memory} {ws : List (BitVec 64)} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ (a ↦₆₄* ws) ∗ R) (i : BitVec 64) (hi : i.toNat < ws.length) :
    m.canRead (a + (i <<< 3)) 8 = true := by
  rw [shl3_eq_ofNat]
  exact canRead_of_words ws a i.toNat h hi

theorem canWrite_shl3_of_words {m : Memory} {ws : List (BitVec 64)} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ (a ↦₆₄* ws) ∗ R) (i : BitVec 64) (hi : i.toNat < ws.length) :
    m.canWrite (a + (i <<< 3)) 8 = true := by
  rw [shl3_eq_ofNat]
  exact canWrite_of_words ws a i.toNat h hi

private theorem solver_stackFrameSlotsCont_region (sp : BitVec 64) (k : Nat) :
    ∀ (n : Nat) (X : SepProp), n * 8 ≤ 2 ^ 64 →
      stackFrameSlotsCont sp k n (fun rest => X ∗ rest) =
        X ∗ memRegion (sp - BitVec.ofNat 64 ((k + n) * 8)) (n * 8) := by
  intro n
  induction n with
  | zero => intro X _; simp [stackFrameSlotsCont, memRegion_zero, sepConj_emp]
  | succ n ih =>
    intro X hb
    cases n with
    | zero =>
      simp only [stackFrameSlotsCont, Nat.zero_add, Nat.one_mul, memRegion_eight,
        sepExists_sepConj_right]
    | succ m =>
      simp only [stackFrameSlotsCont]
      have hfun : ∀ v : BitVec 64,
          (fun rest => X ∗ (((sp - BitVec.ofNat 64 ((k + m + 2) * 8)) ↦₆₄ v) ∗ rest)) =
          (fun rest => (X ∗ ((sp - BitVec.ofNat 64 ((k + m + 2) * 8)) ↦₆₄ v)) ∗ rest) :=
        fun v => funext fun rest => (sepConj_assoc _ _ _).symm
      simp only [hfun]
      rw [funext fun v => ih (X ∗ _) (by omega)]
      simp only [sepConj_assoc, ← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← memRegion_eight]
      congr 1
      rw [memRegion_split' (b := sp - BitVec.ofNat 64 ((k + (m + 1 + 1)) * 8)) (n := 8)
        (k := (m + 1) * 8) (by omega) ?_ (by omega)]
      · congr 2 <;> omega
      · have h1 : (k + (m + 1 + 1)) * 8 = (k + (m + 1)) * 8 + 8 := by omega
        rw [h1, BitVec.ofNat_add]
        generalize BitVec.ofNat 64 ((k + (m + 1)) * 8) = x
        bv_arith

/-- Equivalence between `stackFrameAt sp n` and `memRegion (sp - BitVec.ofNat 64 n) n`
    used by the separation-logic solver for container splitting. -/
theorem solver_stackFrameAt_eq_memRegion (sp : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64) :
    stackFrameAt sp n = memRegion (sp - BitVec.ofNat 64 n) n := by
  unfold stackFrameAt
  by_cases h0 : n = 0
  · subst h0; simp [memRegion_zero]
  by_cases h8 : n % 8 = 0
  · simp only [h0, h8, beq_iff_eq, ite_false, ite_true, stackFrameSlotsFrom]
    have hid : (fun P : SepProp => P) = (fun rest => SepProp.emp ∗ rest) :=
      funext fun _ => (emp_sepConj _).symm
    rw [hid, solver_stackFrameSlotsCont_region sp 0 (n / 8) SepProp.emp (by omega), emp_sepConj,
      Nat.zero_add, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h8)]
  · simp [h0, h8]

end

public meta section

namespace SepSolver

open Lean Meta Elab Tactic

register_option proofLib.frameSplitNearMiss : Bool := {
  defValue := true
  descr := "when `frame_split` / `sep_entail` / `sep_focus` finds a goal atom and context atom at the \
    same address and width with different values, match them and discharge the value equality side condition"
}

register_option proofLib.frameSplitLeaveSideGoals : Bool := {
  defValue := false
  descr := "when a same-address near-miss value equality `v_ctx = v_goal` cannot be discharged automatically \
    by `sep_entail` or `sep_frame`, leave it as an open subgoal instead of failing"
}

register_option proofLib.frameSplitContainers : Bool := {
  defValue := true
  descr := "automatically split `stackFrameAt`, `memRegion`, and `pointsToBytes` (`↦ₛ`) container atoms \
    at the requested offset when a goal atom falls inside one"
}

register_option proofLib.frameSplitUnfold : Bool := {
  defValue := true
  descr := "automatically unfold composite `SepProp` definitions tagged with `@[sep_unfold]` when folded \
    atom matching fails"
}

register_option proofLib.sepShapeDispatch : Bool := {
  defValue := true
  descr := "dispatch `sep_focus` and `sep_entail` across entailment, universally quantified implication, \
    and concrete `SepProp` equality goal shapes"
}

/-- Attribute marking a user-defined composite `SepProp` definition so `sep_entail`, `sep_focus`,
    `sep_eq`, `wp_frame_split`, and `sep_frame` automatically unfold it when folded matching fails. -/
initialize sepUnfoldAttr : TagAttribute ←
  registerTagAttribute `sep_unfold
    "mark a composite `SepProp` definition to be unfolded by separation-logic tactics when folded matching fails"

/-- True if `name` is tagged with `@[sep_unfold]`. -/
def isSepUnfoldConst (name : Name) : MetaM Bool := do
  try
    return sepUnfoldAttr.hasTag (← getEnv) name
  catch _ =>
    return false

/-! ## Metadata stripping and 64-bit address offset normalization -/

/-- Recursively strip `.mdata` annotations from an expression. -/
partial def stripMData (e : Expr) : Expr :=
  match e with
  | .mdata _ b => stripMData b
  | .app f a => e.updateApp! (stripMData f) (stripMData a)
  | .lam _ t b _ => e.updateLambdaE! (stripMData t) (stripMData b)
  | .forallE _ t b _ => e.updateForallE! (stripMData t) (stripMData b)
  | .letE _ t v b _ => e.updateLetE! (stripMData t) (stripMData v) (stripMData b)
  | .proj _ _ b => e.updateProj! (stripMData b)
  | e => e

/-- Evaluate a ground `Nat` literal in the solver normalizer. -/
def evalNatLitSolver? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n := e.rawNatLit? then return some n
  if let some n ← getNatValue? e then return some n
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .default (whnf e)
  if let some n := e'.rawNatLit? then return some n
  getNatValue? e'

/-- Extract the unsigned value `< 2^64` of a ground `BitVec 64` literal. -/
partial def evalBV64Lit? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if e.hasFVar || e.hasMVar then return none
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some 64 ← evalNatLitSolver? (e.getArg! 0) then
      if let some v ← evalNatLitSolver? (e.getArg! 1) then
        return some (v % (1 <<< 64))
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty := e.getArg! 0
    if ty.isAppOfArity ``BitVec 1 then
      if let some 64 ← evalNatLitSolver? (ty.getArg! 0) then
        if let some v ← evalNatLitSolver? (e.getArg! 1) then
          return some (v % (1 <<< 64))
  if e.isAppOfArity ``Neg.neg 3 then
    if let some v ← evalBV64Lit? (e.getArg! 2) then
      let m := 1 <<< 64
      return some ((m - (v % m)) % m)
  if e.isAppOfArity ``HMul.hMul 6 then
    if let some a ← evalBV64Lit? (e.getArg! 4) then
      if let some b ← evalBV64Lit? (e.getArg! 5) then
        return some ((a * b) % (1 <<< 64))
  let e' ← if e.isConst then withTransparency .default (whnf e) else pure e
  if e'.isAppOfArity ``BitVec.ofFin 2 then
    if let some 64 ← evalNatLitSolver? (e'.getArg! 0) then
      let finExpr ← whnf (e'.getArg! 1)
      if finExpr.isAppOfArity ``Fin.mk 3 then
        if let some v ← evalNatLitSolver? (finExpr.getArg! 1) then
          return some (v % (1 <<< 64))
  return none

/-- Construct a canonical `BitVec.ofNat 64 v` expression using `OfNat.ofNat` numerals (`toExpr : Nat → Expr`)
    instead of raw `.lit (.natVal v)` so it matches surface syntax `v#64` and `DiscrTree` keys. -/
@[inline] def mkCanonBV64Lit (v : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) (toExpr (v % (1 <<< 64)))

/-- Fold `(x - a) - b` into `x - (a + b)` (or `x` when `a + b = 0`) for 64-bit literals `a, b`. -/
simproc [wp_norm] reduceBV64SubSub ((_ - _) - _) := fun e => do
  if !e.isAppOfArity ``HSub.hSub 6 then return .continue
  let lhs := e.getArg! 4
  let bExpr := e.getArg! 5
  if !lhs.isAppOfArity ``HSub.hSub 6 then return .continue
  let some b ← evalBV64Lit? bExpr | return .continue
  let aExpr := lhs.getArg! 5
  let some a ← evalBV64Lit? aExpr | return .continue
  let x := lhs.getArg! 4
  if (← evalBV64Lit? x).isSome then return .continue
  let c := (a + b) % (1 <<< 64)
  if c == 0 then
    let prf ← mkAppM ``bitvec64_sub_sub_zero #[x, aExpr, bExpr, ← mkEqRefl (mkCanonBV64Lit 0)]
    return .visit { expr := x, proof? := some prf }
  else
    let cExpr := mkCanonBV64Lit c
    let newExpr ← mkAppM ``HSub.hSub #[x, cExpr]
    let prf ← mkAppM ``bitvec64_sub_sub_fold #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
    return .visit { expr := newExpr, proof? := some prf }

/-- Fold `(x - a) + b` into `x - (a - b)`, `x + (b - a)`, or `x` for 64-bit literals `a, b`. -/
simproc [wp_norm] reduceBV64SubAdd ((_ - _) + _) := fun e => do
  if !e.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let lhs := e.getArg! 4
  let bExpr := e.getArg! 5
  if !lhs.isAppOfArity ``HSub.hSub 6 then return .continue
  let some b ← evalBV64Lit? bExpr | return .continue
  let aExpr := lhs.getArg! 5
  let some a ← evalBV64Lit? aExpr | return .continue
  let x := lhs.getArg! 4
  if (← evalBV64Lit? x).isSome then return .continue
  let diff := (b + (1 <<< 64) - a) % (1 <<< 64)
  if diff == 0 then
    let prf ← mkAppM ``bitvec64_sub_add_zero #[x, aExpr, bExpr, ← mkEqRefl aExpr]
    return .visit { expr := x, proof? := some prf }
  else if diff >= (1 <<< 63) then
    let cExpr := mkCanonBV64Lit ((1 <<< 64) - diff)
    let newExpr ← mkAppM ``HSub.hSub #[x, cExpr]
    let prf ← mkAppM ``bitvec64_sub_add_fold_sub #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
    return .visit { expr := newExpr, proof? := some prf }
  else
    let cExpr := mkCanonBV64Lit diff
    let newExpr ← mkAppM ``HAdd.hAdd #[x, cExpr]
    let prf ← mkAppM ``bitvec64_sub_add_fold_add #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
    return .visit { expr := newExpr, proof? := some prf }

/-- Fold `(x + a) - b` into `x - (b - a)`, `x + (a - b)`, or `x` for 64-bit literals `a, b`.
    Not registered in global `[wp_norm]` so it does not shadow `reduceBitVecAddSub` in `[arm64_norm]`
    on backward-branch PC expressions `(entry + k) - d`; `SepSolver.normAddrMeta` folds `(x + a) - b`
    in spatial addresses directly. -/
simproc reduceBV64AddSub ((_ + _) - _) := fun e => do
  if !e.isAppOfArity ``HSub.hSub 6 then return .continue
  let lhs := e.getArg! 4
  let bExpr := e.getArg! 5
  if !lhs.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let some b ← evalBV64Lit? bExpr | return .continue
  let aExpr := lhs.getArg! 5
  let some a ← evalBV64Lit? aExpr | return .continue
  let x := lhs.getArg! 4
  if (← evalBV64Lit? x).isSome then return .continue
  let diff := (a + (1 <<< 64) - b) % (1 <<< 64)
  if diff == 0 then
    let prf ← mkAppM ``bitvec64_add_sub_zero #[x, aExpr, bExpr, ← mkEqRefl aExpr]
    return .visit { expr := x, proof? := some prf }
  else if diff >= (1 <<< 63) then
    let cExpr := mkCanonBV64Lit ((1 <<< 64) - diff)
    let newExpr ← mkAppM ``HSub.hSub #[x, cExpr]
    let prf ← mkAppM ``bitvec64_add_sub_fold_sub #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
    return .visit { expr := newExpr, proof? := some prf }
  else
    let cExpr := mkCanonBV64Lit diff
    let newExpr ← mkAppM ``HAdd.hAdd #[x, cExpr]
    let prf ← mkAppM ``bitvec64_add_sub_fold_add #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
    return .visit { expr := newExpr, proof? := some prf }

/-- Fold `(x + a) + b` into `x + (a + b)` (or `x` when `a + b = 0`) for 64-bit literals `a, b`.
    Coordinated with `reduceBitVecAddAssoc` in `[arm64_norm]`. -/
simproc reduceBV64AddAdd ((_ + _) + _) := fun e => do
  if !e.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let lhs := e.getArg! 4
  let bExpr := e.getArg! 5
  if !lhs.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let some b ← evalBV64Lit? bExpr | return .continue
  let aExpr := lhs.getArg! 5
  let some a ← evalBV64Lit? aExpr | return .continue
  let x := lhs.getArg! 4
  if (← evalBV64Lit? x).isSome then return .continue
  let c := (a + b) % (1 <<< 64)
  if c == 0 then
    let prf ← mkAppM ``bitvec64_add_add_zero #[x, aExpr, bExpr, ← mkEqRefl (mkCanonBV64Lit 0)]
    return .visit { expr := x, proof? := some prf }
  else
    let cExpr := mkCanonBV64Lit c
    let newExpr ← mkAppM ``HAdd.hAdd #[x, cExpr]
    let prf ← mkAppM ``bitvec64_add_add_fold #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
    return .visit { expr := newExpr, proof? := some prf }

/-- Compose two optional equality proofs via `mkEqTrans`. -/
def mkEqTransOpt (p1? p2? : Option Expr) : MetaM (Option Expr) := do
  match p1?, p2? with
  | none, none => return none
  | some p1, none => return some p1
  | none, some p2 => return some p2
  | some p1, some p2 => return some (← mkEqTrans p1 p2)

/-- Single top-level 64-bit offset folding step on `e` (assuming its operands are normalized). -/
partial def foldBV64OffsetTop? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if e.isAppOfArity ``HSub.hSub 6 then
    let lhs := e.getArg! 4
    let bExpr := e.getArg! 5
    let some b ← evalBV64Lit? bExpr | return none
    if (← evalBV64Lit? lhs).isSome then return none
    if b == 0 then
      return some (lhs, mkApp2 (mkConst ``BitVec.sub_zero) (toExpr 64) lhs)
    if lhs.isAppOfArity ``HSub.hSub 6 then
      let x := lhs.getArg! 4
      let aExpr := lhs.getArg! 5
      if let some a ← evalBV64Lit? aExpr then
        if (← evalBV64Lit? x).isNone then
          let c := (a + b) % (1 <<< 64)
          if c == 0 then
            let prf ← mkAppM ``bitvec64_sub_sub_zero #[x, aExpr, bExpr, ← mkEqRefl (mkCanonBV64Lit 0)]
            return some (x, prf)
          else
            let cExpr := mkCanonBV64Lit c
            let newExpr ← mkAppM ``HSub.hSub #[x, cExpr]
            let prf ← mkAppM ``bitvec64_sub_sub_fold #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
            return some (newExpr, prf)
    if lhs.isAppOfArity ``HAdd.hAdd 6 then
      let x := lhs.getArg! 4
      let aExpr := lhs.getArg! 5
      if let some a ← evalBV64Lit? aExpr then
        if (← evalBV64Lit? x).isNone then
          if a == b then
            let prf ← mkAppM ``bitvec64_add_sub_zero #[x, aExpr, bExpr, ← mkEqRefl aExpr]
            return some (x, prf)
          else if a > b then
            let cExpr := mkCanonBV64Lit (a - b)
            let newExpr ← mkAppM ``HAdd.hAdd #[x, cExpr]
            let prf ← mkAppM ``bitvec64_add_sub_fold_add #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
            return some (newExpr, prf)
          else
            let cExpr := mkCanonBV64Lit (b - a)
            let newExpr ← mkAppM ``HSub.hSub #[x, cExpr]
            let prf ← mkAppM ``bitvec64_add_sub_fold_sub #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
            return some (newExpr, prf)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let lhs := e.getArg! 4
    let bExpr := e.getArg! 5
    let some b ← evalBV64Lit? bExpr | return none
    if (← evalBV64Lit? lhs).isSome then return none
    if b == 0 then
      return some (lhs, mkApp2 (mkConst ``BitVec.add_zero) (toExpr 64) lhs)
    if b >= (1 <<< 63) && ((1 <<< 64) - b) <= (1 <<< 32) then
      let c := (1 <<< 64) - b
      let cExpr := mkCanonBV64Lit c
      let subExpr ← mkAppM ``HSub.hSub #[lhs, cExpr]
      let prf1 ← mkAppM ``bitvec64_add_neg_lit_eq_sub #[lhs, bExpr, cExpr, ← mkEqRefl (mkCanonBV64Lit 0)]
      if let some (finalExpr, prf2) ← foldBV64OffsetTop? subExpr then
        return some (finalExpr, ← mkEqTrans prf1 prf2)
      return some (subExpr, prf1)
    if lhs.isAppOfArity ``HSub.hSub 6 then
      let x := lhs.getArg! 4
      let aExpr := lhs.getArg! 5
      if let some a ← evalBV64Lit? aExpr then
        if (← evalBV64Lit? x).isNone then
          if a == b then
            let prf ← mkAppM ``bitvec64_sub_add_zero #[x, aExpr, bExpr, ← mkEqRefl aExpr]
            return some (x, prf)
          else if a > b then
            let cExpr := mkCanonBV64Lit (a - b)
            let newExpr ← mkAppM ``HSub.hSub #[x, cExpr]
            let prf ← mkAppM ``bitvec64_sub_add_fold_sub #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
            return some (newExpr, prf)
          else
            let cExpr := mkCanonBV64Lit (b - a)
            let newExpr ← mkAppM ``HAdd.hAdd #[x, cExpr]
            let prf ← mkAppM ``bitvec64_sub_add_fold_add #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
            return some (newExpr, prf)
    if lhs.isAppOfArity ``HAdd.hAdd 6 then
      let x := lhs.getArg! 4
      let aExpr := lhs.getArg! 5
      if let some a ← evalBV64Lit? aExpr then
        if (← evalBV64Lit? x).isNone then
          let c := (a + b) % (1 <<< 64)
          if c == 0 then
            let prf ← mkAppM ``bitvec64_add_add_zero #[x, aExpr, bExpr, ← mkEqRefl (mkCanonBV64Lit 0)]
            return some (x, prf)
          else
            let cExpr := mkCanonBV64Lit c
            let newExpr ← mkAppM ``HAdd.hAdd #[x, cExpr]
            let prf ← mkAppM ``bitvec64_add_add_fold #[x, aExpr, bExpr, cExpr, ← mkEqRefl cExpr]
            return some (newExpr, prf)
  return none

/-- Normalize a 64-bit address expression `e` in `MetaM` (stripping `mdata`, substituting local
    `sf.sp = ...` equalities, and folding literal offset chains), returning `(e', proof?)`. -/
partial def normAddrMeta (e : Expr) (fuel : Nat := 16) : MetaM (Expr × Option Expr) := do
  if fuel == 0 then return (e, none)
  let e := stripMData (← instantiateMVars e)
  if e.isAppOfArity ``HMul.hMul 6 then
    if let some v ← evalBV64Lit? e then
      let cExpr := mkCanonBV64Lit v
      let prf ← mkExpectedTypeHint (← mkEqRefl cExpr) (← mkEq e cExpr)
      return (cExpr, some prf)
  if e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HAdd.hAdd 6 then
    let lhs := e.getArg! 4
    let rhs := e.getArg! 5
    let (lhs', pLhs?) ← normAddrMeta lhs (fuel - 1)
    let (rhs', pRhs?) ← normAddrMeta rhs (fuel - 1)
    let fn4 := mkAppN e.getAppFn (e.getAppArgs.extract 0 4)
    let eMid := mkApp2 fn4 lhs' rhs'
    let pCongr? : Option Expr ←
      if pLhs?.isSome || pRhs?.isSome then
        let p1 ← match pLhs? with
          | some p => mkCongrArg fn4 p
          | none => mkEqRefl (mkApp fn4 lhs')
        let p2 ← match pRhs? with
          | some p => mkCongr p1 p
          | none => mkCongrFun p1 rhs'
        pure (some p2)
      else
        pure none
    if let some (eFinal, pFold) ← foldBV64OffsetTop? eMid then
      return (eFinal, ← mkEqTransOpt pCongr? (some pFold))
    return (eMid, pCongr?)
  if e.isAppOfArity ``State.sp 1 then
    let s := e.getArg! 0
    if s.isFVar then
      for decl in (← getLCtx) do
        if decl.isImplementationDetail || decl.isAuxDecl then continue
        let ty := stripMData (← instantiateMVars decl.type)
        let some (_, lhs, rhs) := ty.eq? | continue
        if lhs == e && !rhs.containsFVar s.fvarId! then
          let (rhs', pRhs?) ← normAddrMeta rhs (fuel - 1)
          return (rhs', ← mkEqTransOpt (some decl.toExpr) pRhs?)
  return (e, none)

/-- True if `e` is a primitive points-to or `memRegion` atom that must not be unfolded to `Heap → Prop`. -/
def isPrimSepAtom (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n =>
    n == ``pointsTo8 || n == ``pointsTo16 || n == ``pointsTo32 ||
    n == ``pointsTo64 || n == ``pointsTo128 || n == ``pointsToBytes ||
    n == ``pointsToWords64 || n == ``regionBlock || n == ``memRegion ||
    n == ``pointsTo8RO || n == ``pointsTo16RO || n == ``pointsTo32RO ||
    n == ``pointsTo64RO || n == ``pointsTo128RO || n == ``pointsToBytesRO ||
    n == ``pointsToWords64RO || n == ``regionBlockRO ||
    n == ``stackFrame16At || n == ``stackFrame32At
  | none => false

/-- Normalize a `SepProp` expression `e` in `MetaM` (stripping `mdata`, unfolding `stackFrame`,
    and normalizing addresses of all spatial
    atoms), returning `(e', proof?)`. Uses `consumeMData` on the `SepProp.sepConj` spine so
    traversal is strictly linear $O(N)$ in the number of atoms. -/
partial def normSepPropMeta (e : Expr) : MetaM (Expr × Option Expr) := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if e.isAppOfArity ``SepProp.sepConj 2 then
    let l := e.getArg! 0
    let r := e.getArg! 1
    let (l', pL?) ← normSepPropMeta l
    let (r', pR?) ← normSepPropMeta r
    let e' := mkApp2 (mkConst ``SepProp.sepConj) l' r'
    if pL?.isSome || pR?.isSome then
      let fn := mkConst ``SepProp.sepConj
      let p1 ← match pL? with
        | some p => mkCongrArg fn p
        | none => mkEqRefl (mkApp fn l')
      let p2 ← match pR? with
        | some p => mkCongr p1 p
        | none => mkCongrFun p1 r'
      return (e', some p2)
    return (e', none)
  let e := stripMData e
  if e.isAppOfArity ``Arm64.stackFrame 2 then
    let s := e.getArg! 0
    let len := e.getArg! 1
    let spExpr := mkApp (mkConst ``State.sp) s
    let offExpr ← match ← evalNatLitSolver? len with
      | some n => pure (toExpr (BitVec.ofNat 64 n))
      | none => mkAppM ``BitVec.ofNat #[toExpr 64, len]
    let baseExpr ← mkAppM ``HSub.hSub #[spExpr, offExpr]
    let (base', pBase?) ← normAddrMeta baseExpr
    let e' := mkApp2 (mkConst ``Arm64.memRegion) base' len
    let prf ← match pBase? with
      | some pBase =>
        let pCongr ← mkCongrFun (← mkCongrArg (mkConst ``Arm64.memRegion) pBase) len
        mkExpectedTypeHint pCongr (← mkEq e e')
      | none =>
        mkExpectedTypeHint (← mkEqRefl e') (← mkEq e e')
    return (e', some prf)
  if e.isAppOfArity ``Arm64.stackFrame16 1 || e.isAppOfArity ``Arm64.stackFrame32 1 then
    let s := e.getArg! 0
    let atConst := if e.isAppOfArity ``Arm64.stackFrame16 1 then ``Arm64.stackFrame16At else ``Arm64.stackFrame32At
    let spExpr := mkApp (mkConst ``State.sp) s
    let (sp', pSp?) ← normAddrMeta spExpr
    let e' := mkApp (mkConst atConst) sp'
    let prf ← match pSp? with
      | some pSp =>
        let pCongr ← mkCongrArg (mkConst atConst) pSp
        mkExpectedTypeHint pCongr (← mkEq e e')
      | none =>
        mkExpectedTypeHint (← mkEqRefl e') (← mkEq e e')
    return (e', some prf)
  if isPrimSepAtom e then
    let args := e.getAppArgs
    if args.size >= 1 then
      let addr := args[0]!
      let (addr', pAddr?) ← normAddrMeta addr
      if let some pAddr := pAddr? then
        let mut prf ← mkCongrArg e.getAppFn pAddr
        for idx in [1:args.size] do
          prf ← mkCongrFun prf args[idx]!
        let e' := mkAppN e.getAppFn (args.set! 0 addr')
        return (e', some prf)
    return (e, none)
  return (e, none)

/-! ## Separating-conjunction trees -/

/-- The atoms of a separating-conjunction tree, left to right, without `emp`.
    Uses `.consumeMData` along the `SepProp.sepConj` spine and `stripMData` only at leaf atoms
    so traversal scales linearly $O(N)$ on large separation-logic frames. -/
partial def atoms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``SepProp.sepConj 2 then atoms (e.getArg! 1) (atoms (e.getArg! 0) acc)
  else
    let e := (stripMData e).headBeta
    if e.isConstOf ``SepProp.emp then acc
    else acc.push e

def mkSep (a b : Expr) : Expr := mkApp2 (mkConst ``SepProp.sepConj) a b

/-- Right-nested separating conjunction of `xs` (`emp` if empty, no trailing `emp`). -/
def mkSepList (xs : Array Expr) : Expr :=
  if xs.isEmpty then mkConst ``SepProp.emp else xs.pop.foldr mkSep xs.back!

def mkSat (P m : Expr) : Expr := mkApp2 (mkConst ``SepProp.Satisfies) P m


/-! ## Reflective AC normalization -/

/-- Index of `a` in the shared atom table (syntactic, then reducible-defeq), appending it if new. -/
def atomIdx (a : Expr) : StateRefT (Array Expr) MetaM Nat := do
  let tbl ← get
  if let some i := tbl.findIdx? (· == a) then return i
  for h : i in [:tbl.size] do
    let b := tbl[i]
    if b.getAppFn == a.getAppFn && b.getAppNumArgs == a.getAppNumArgs then
      if ← withReducibleAndInstances (isDefEq b a) then return i
  modify (·.push a)
  return tbl.size

/-- Reify a separating-conjunction tree into a `SepTree` over the shared atom table. -/
partial def reify (e : Expr) : StateRefT (Array Expr) MetaM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``SepProp.sepConj 2 then
    return mkApp2 (mkConst ``SepTree.sep) (← reify (e.getArg! 0)) (← reify (e.getArg! 1))
  else
    let e := (stripMData e).headBeta
    if e.isConstOf ``SepProp.emp then
      return mkConst ``SepTree.nil
    else
      return mkApp (mkConst ``SepTree.atom) (mkRawNatLit (← atomIdx e))

def mkAtomList (tbl : Array Expr) : Expr :=
  let ty := mkConst ``SepProp
  tbl.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty a acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

/-- Syntactic atom table: the atoms in insertion order, indexed by structural equality. -/
abbrev SynTable := Array Expr × Std.HashMap Expr Nat

/-- Index of `a` in a syntactic atom table, appending it if new. -/
def synAtomIdx (a : Expr) : StateM SynTable Nat := do
  let (tbl, idx) ← get
  if let some i := idx[a]? then return i
  set (tbl.push a, idx.insert a tbl.size)
  return tbl.size

/-- `reify` over a syntactic atom table (no `isDefEq`). -/
partial def synReify (e : Expr) : StateM SynTable Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``SepProp.sepConj 2 then
    return mkApp2 (mkConst ``SepTree.sep) (← synReify (e.getArg! 0)) (← synReify (e.getArg! 1))
  else
    let e := (stripMData e).headBeta
    if e.isConstOf ``SepProp.emp then
      return mkConst ``SepTree.nil
    else
      return mkApp (mkConst ``SepTree.atom) (mkRawNatLit (← synAtomIdx e))

/-- Fast path of `reifyPermTbl?`: succeeds when the atoms of `A` and `B` agree as multisets up to
    syntactic equality, using a hash map instead of quadratically many `isDefEq` calls. -/
def synReifyPermTbl? (A B : Expr) : Option (Array Expr × Expr × Expr) :=
  let go : StateM SynTable (Expr × Expr × Nat × Array Nat × Array Nat) := do
    let tA ← synReify A
    let nA := (← get).1.size
    let tB ← synReify B
    return (tA, tB, nA, ← (atoms A).mapM synAtomIdx, ← (atoms B).mapM synAtomIdx)
  let ((tA, tB, nA, iA, iB), (tbl, _)) := go.run (#[], {})
  -- every atom of `B` must already occur in `A`, with the same multiplicities
  if tbl.size == nA && iA.size == iB.size && iA.qsort (· < ·) == iB.qsort (· < ·) then
    some (tbl, tA, tB)
  else none


/-- Reify `A` and `B` over one atom table. Returns `(atom table, tree of A, tree of B)` if their
    atom multisets agree. -/
def reifyPermTbl? (A B : Expr) : MetaM (Option (Array Expr × Expr × Expr)) := do
  if let some r := synReifyPermTbl? A B then return some r
  let go : StateRefT (Array Expr) MetaM (Expr × Expr × Array Nat × Array Nat) := do
    let tA ← reify A
    let tB ← reify B
    return (tA, tB, ← (atoms A).mapM atomIdx, ← (atoms B).mapM atomIdx)
  let ((tA, tB, iA, iB), tbl) ← go.run #[]
  unless iA.size == iB.size && iA.qsort (· < ·) == iB.qsort (· < ·) do return none
  return some (tbl, tA, tB)

/-- The balanced `SepAtomTree` holding `tbl[i]` at index `i` (see `SepAtomTree.get`). The subtree
    rooted at table position `idx` holds positions `idx + k * stride`; its left subtree takes the
    odd `k`, its right subtree the even `k > 0`. -/
partial def mkSepAtomTree (tbl : Array Expr) (idx : Nat := 0) (stride : Nat := 1) : Expr :=
  if h : idx < tbl.size then
    mkApp3 (mkConst ``SepAtomTree.node) tbl[idx]
      (mkSepAtomTree tbl (idx + stride) (2 * stride))
      (mkSepAtomTree tbl (idx + 2 * stride) (2 * stride))
  else mkConst ``SepAtomTree.leaf

/-- `Eq.refl true`, the kernel-evaluated permutation certificate. -/
def rflTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- Given `h : m ⊨ A`, a proof of `m ⊨ B` when `A` and `B` have the same atom multiset
    (`none` otherwise). One kernel-checked sorted-index comparison (`SepTree.sat_of_sortIdx`). -/
def satAC? (m A B h : Expr) : MetaM (Option Expr) := do
  let A ← instantiateMVars A
  let B ← instantiateMVars B
  if A == B then return some h
  let some (tbl, tA, tB) ← reifyPermTbl? A B | return none
  let prf := mkAppN (mkConst ``SepTree.sat_of_sortIdx) #[m, mkSepAtomTree tbl, tA, tB, rflTrue, h]
  return some (← mkExpectedTypeHint prf (mkSat B m))

/-- Like `satAC?`, failing with an error. -/
def satAC (m A B h : Expr) : MetaM Expr := do
  let some p ← satAC? m A B h | throwError "sep solver: {A} and {B} are not AC-equal"
  return p

/-- Given `h : m ⊨ P`, a proof of `m ⊨ Pᵢ ∗ rest` focusing the `i`-th atom; returns `(rest, proof)`. -/
def focus (m P h : Expr) (i : Nat) : MetaM (Expr × Expr) := do
  let as := atoms (← instantiateMVars P)
  let rest := mkSepList (as.eraseIdx! i)
  return (rest, ← satAC m P (mkSep as[i]! rest) h)

/-- The certificate `A = B` for reified trees `tA`, `tB` over atom table `tbl`
    (`SepTree.eq_of_sortIdx`). -/
def eqACOfTbl (A B : Expr) (tbl : Array Expr) (tA tB : Expr) : MetaM Expr := do
  let f := mkApp (mkConst ``SepAtomTree.get) (mkSepAtomTree tbl)
  mkExpectedTypeHint (mkAppN (mkConst ``SepTree.eq_of_sortIdx) #[f, tA, tB, rflTrue]) (← mkEq A B)

/-- A proof of `A = B` where `A` and `B` have the same atom multiset. -/
def eqAC (A B : Expr) : MetaM Expr := do
  let A ← instantiateMVars A
  let B ← instantiateMVars B
  if A == B then return ← mkEqRefl A
  let some (tbl, tA, tB) ← reifyPermTbl? A B | throwError "sep solver: {A} and {B} are not AC-equal"
  eqACOfTbl A B tbl tA tB

/-! ## Blocks -/

/-- The `SepBlock` description of an atom: `IsBlock atom base len Φ`. -/
structure Block where
  isBlock : Expr
  base : Expr
  len : Expr
  Φ : Expr

/-- Look up the `SepBlock` instance of an atom. -/
def blockOf? (atom : Expr) : MetaM (Option Block) := do
  let atom := stripMData (← instantiateMVars atom)
  if atom.getAppFn.isMVar || atom.getAppFn.isFVar || atom.isFVar then return none
  let b ← mkFreshExprMVar (mkApp (mkConst ``BitVec) (mkRawNatLit 64))
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let Φ ← mkFreshExprMVar (← mkArrow (mkConst ``Memory) (mkSort Level.zero))
  let ty := mkApp4 (mkConst ``SepBlock) atom b n Φ
  let some inst ← observing? (synthInstance ty) | return none
  unless ← withReducibleAndInstances (isDefEq ty (← inferType inst)) do return none
  let b ← instantiateMVars b
  let n ← instantiateMVars n
  let Φ ← instantiateMVars Φ
  return some ⟨mkApp5 (mkConst ``SepBlock.isBlock) atom b n Φ inst, b, n, Φ⟩

def Block.at (blk : Block) (m : Expr) : Expr := (blk.Φ.beta #[m]).headBeta

/-- A proof of `n' ≤ n` for defeq or literal lengths. -/
def proveLenLe? (n' n : Expr) : MetaM (Option Expr) := do
  if ← withReducibleAndInstances (isDefEq n' n) then return some (mkApp (mkConst ``Nat.le_refl) n)
  let (some a, some b) := ((← instantiateMVars n').nat?, (← instantiateMVars n).nat?) | return none
  if a ≤ b then return some (← mkDecideProof (← mkAppM ``LE.le #[n', n])) else return none

def mkUpdate (hb hb' hle h hag hΦ : Expr) : MetaM Expr :=
  mkAppM ``IsBlock.update #[hb, hb', hle, h, hag, hΦ]

/-! ## Side conditions -/

/-- Discharger for value side goals (`φ ↦ proof of φ`). -/
abbrev Disch := Expr → TacticM (Option Expr)

/-- Prove a (beta-reduced) content predicate: `True`, conjunctions, and otherwise `disch`. -/
partial def proveConj (disch : Disch) (φ : Expr) : TacticM (Option Expr) := do
  let φ := (stripMData (← instantiateMVars φ)).headBeta
  if φ.isConstOf ``True then return some (mkConst ``True.intro)
  if φ.isAppOfArity ``And 2 then
    let some p ← proveConj disch (φ.getArg! 0) | return none
    let some q ← proveConj disch (φ.getArg! 1) | return none
    return some (mkApp4 (mkConst ``And.intro) (φ.getArg! 0) (φ.getArg! 1) p q)
  disch φ

/-- Proof of `h = g` for atoms with the same head, from equality side goals on differing arguments. -/
def congrAtoms? (disch : Disch) (h g : Expr) : TacticM (Option Expr) := do
  let h := stripMData (← instantiateMVars h)
  let g := stripMData (← instantiateMVars g)
  unless h.getAppFn == g.getAppFn && h.getAppNumArgs == g.getAppNumArgs do return none
  let mut prf ← mkEqRefl h.getAppFn
  for a in h.getAppArgs, b in g.getAppArgs do
    if a == b then
      prf ← mkCongrFun prf a
    else if ← withReducibleAndInstances (isDefEq a b) then
      prf ← mkCongrFun prf a
    else if !a.hasMVar && !b.hasMVar then
      let some e ← disch (← mkEq a b) | return none
      prf ← mkCongr prf e
    else
      return none
  return some prf

/-! ## Entailment -/

/-- How a goal atom is obtained from a hypothesis atom. -/
inductive Step where
  /-- Syntactically equal (possibly after unification). -/
  | same
  /-- Same head: `hyp = goal` by congruence. -/
  | congr (e : Expr)
  /-- Same base: `IsBlock.update` at the same memory (`hb`, `hb'`, `hle`, `hΦ`). -/
  | update (hb hb' hle hΦ : Expr) (base len : Expr)

/-- Goal preprocessing: open `∃∗` atoms with metavariables and turn `⌜φ⌝` atoms into pending side
    goals. Returns the spatial goal and a function turning its proof into a proof of `G`. -/
partial def expandGoal (m G : Expr) (pures : IO.Ref (Array (Expr × Expr))) :
    MetaM (Expr × (Expr → MetaM Expr)) := do
  let G := (← instantiateMVars G).consumeMData
  let as := atoms G
  let some i := as.findIdx? fun a =>
      a.isAppOfArity ``SepProp.pure 1 || a.isAppOfArity ``SepProp.sepExists 2
    | return (G, pure)
  let a := as[i]!
  let rest := mkSepList (as.eraseIdx! i)
  if a.isAppOfArity ``SepProp.pure 1 then
    let φ := a.getArg! 0
    let hφ ← mkFreshExprMVar φ
    pures.modify (·.push (hφ, φ))
    let (G', k) ← expandGoal m rest pures
    return (G', fun p => do
      let p ← k p
      satAC m (mkSep a rest) G (mkAppN (mkConst ``Satisfies.pure_intro) #[m, φ, rest, hφ, p]))
  else
    let α := a.getArg! 0
    let f := a.getArg! 1
    let w ← mkFreshExprMVar α
    let (G', k) ← expandGoal m (mkSep (f.beta #[w]).headBeta rest) pures
    let u ← getLevel α
    return (G', fun p => do
      let p ← k p
      let p' := mkAppN (mkConst ``Satisfies.sepExists_intro [u]) #[α, f, rest, m, w, p]
      satAC m (mkSep a rest) G (← mkExpectedTypeHint p' (mkSat (mkSep a rest) m)))

/-- Given `e : SepProp`, atom index `idx` (0-indexed in `atoms e` order), and `hEq : atom = newExpr`,
    return `(e', hEqTree)` where `hEqTree : e = e'` replaces atom `idx` by `newExpr`. -/
partial def rewriteAtomAtEq? (e : Expr) (idx : Nat) (newExpr hEq : Expr) : MetaM (Option (Expr × Expr)) := do
  let rec go (cur : Expr) (k : Nat) : MetaM (Expr × Nat × Option Expr) := do
    let curBeta := cur.consumeMData.headBeta
    if curBeta.isAppOfArity ``SepProp.sepConj 2 then
      let l := curBeta.getArg! 0
      let r := curBeta.getArg! 1
      let (l', k1, hL?) ← go l k
      if let some hL := hL? then
        let step ← mkCongrFun (← mkCongrArg (mkConst ``SepProp.sepConj) hL) r
        return (mkSep l' r, k1, some step)
      let (r', k2, hR?) ← go r k1
      if let some hR := hR? then
        let step ← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) l) hR
        return (mkSep l r', k2, some step)
      return (cur, k2, none)
    else
      let leaf := (stripMData curBeta).headBeta
      if leaf.isConstOf ``SepProp.emp then
        return (cur, k, none)
      else if k == idx then
        return (newExpr, k + 1, some hEq)
      else
        return (cur, k + 1, none)
  let (e', _, h?) ← go e 0
  return h?.map fun h => (e', h)

/-- Decompose a normalized 64-bit address expression into `(base, signedConstOffset)`. -/
def splitBaseOff (e : Expr) : MetaM (Expr × Int) := do
  let e := (stripMData e).headBeta
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let b := stripMData (e.getArg! 4)
    if let some kv ← evalBV64Lit? (e.getArg! 5) then
      let sk : Int := if kv ≥ 2 ^ 63 then (kv : Int) - (2 ^ 64 : Int) else (kv : Int)
      return (b, sk)
    else return (e, 0)
  else if e.isAppOfArity ``HSub.hSub 6 then
    let b := stripMData (e.getArg! 4)
    if let some kv ← evalBV64Lit? (e.getArg! 5) then
      let sk : Int := if kv ≥ 2 ^ 63 then (kv : Int) - (2 ^ 64 : Int) else (kv : Int)
      return (b, -sk)
    else return (e, 0)
  else if let some kv ← evalBV64Lit? e then
    return (mkConst ``Unit.unit, (kv : Int))
  else return (e, 0)

/-- Non-negative constant byte offset `q - p` when `p` and `q` share a base expression. -/
def constAddrOffset? (p q : Expr) : MetaM (Option Nat) := do
  let (bp, op) ← splitBaseOff p
  let (bq, oq) ← splitBaseOff q
  if bp == bq && oq ≥ op && (oq - op) < (2 ^ 64 : Int) then
    return some (oq - op).toNat
  else return none

/-- Normalized 64-bit address expression representing `q + BitVec.ofNat 64 wExpr`,
    together with a kernel equality proof `h : q + BitVec.ofNat 64 wExpr = r`
    canonicalized by `normAddrMeta` so `r` matches `normSepPropMeta` atoms bit-for-bit. -/
def normAddConstOffsetAddr (q wExpr : Expr) : MetaM (Expr × Expr) := do
  let raw ← mkAppM ``HAdd.hAdd #[q, ← mkAppM ``BitVec.ofNat #[toExpr (64 : Nat), wExpr]]
  let wBV ← match ← evalNatLitSolver? wExpr with
    | some n => pure (mkCanonBV64Lit n)
    | none => mkAppM ``BitVec.ofNat #[toExpr (64 : Nat), wExpr]
  let rawCanon ← mkAppM ``HAdd.hAdd #[q, wBV]
  let pMid ← mkExpectedTypeHint (← mkEqRefl rawCanon) (← mkEq raw rawCanon)
  let (r, prf?) ← normAddrMeta rawCanon
  let prf ← match prf? with
    | some p => mkEqTrans pMid p
    | none => pure pMid
  return (r, prf)

/-- Meta-level side-condition discharger (`isDefEq` / `normAddrMeta` / local hypothesis / ground `decide`)
    for pure `MetaM` callers (`frameSplit?` / `closeEntails?`). -/
def metaDisch (φ : Expr) : MetaM (Option Expr) := do
  let φ ← instantiateMVars φ
  if let some (_, lhs, rhs) := φ.eq? then
    if ← isDefEq lhs rhs then
      return some (← mkExpectedTypeHint (← mkEqRefl rhs) φ)
    let (nl, pL?) ← normAddrMeta lhs
    let (nr, pR?) ← normAddrMeta rhs
    if nl == nr || (← isDefEq nl nr) then
      let pMid ← mkExpectedTypeHint (← mkEqRefl nr) (← mkEq nl nr)
      let p1 ← mkEqTransOpt pL? (some pMid)
      let pSymR ← pR?.mapM mkEqSymm
      if let some pFull ← mkEqTransOpt p1 pSymR then
        return some (← mkExpectedTypeHint pFull φ)
    if proofLib.frameSplitNearMiss.get (← getOptions) then
      for decl in (← getLCtx) do
        if decl.isImplementationDetail then continue
        let dty ← instantiateMVars decl.type
        if let some (_, dlhs, drhs) := dty.eq? then
          if (← withReducible (isDefEq dlhs lhs)) && (← withReducible (isDefEq drhs rhs)) then
            return some (← mkExpectedTypeHint decl.toExpr φ)
          if (← withReducible (isDefEq dlhs rhs)) && (← withReducible (isDefEq drhs lhs)) then
            return some (← mkExpectedTypeHint (← mkEqSymm decl.toExpr) φ)
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let dty ← instantiateMVars decl.type
    if ← withReducible (isDefEq dty φ) then
      return some (← mkExpectedTypeHint decl.toExpr φ)
  if (φ.isAppOfArity ``LE.le 4 || φ.isAppOfArity ``LT.lt 4) && !φ.hasMVar then
    let bArg := φ.getArg! 3
    let aArg := φ.getArg! 2
    if !aArg.hasFVar then
      for decl in (← getLCtx) do
        if decl.isImplementationDetail then continue
        let dty ← instantiateMVars decl.type
        if let some (_, dlhs, drhs) := dty.eq? then
          -- `<&&>` and the nested `else do` keep the `isDefEq` checks lazy (a `(← c)` operand of
          -- `&&` / `else if` is hoisted and run before the `if`).
          let (nLit?, hEqToRhs?) ←
            if ← pure (!drhs.hasFVar && !drhs.hasMVar) <&&> withReducible (isDefEq dlhs bArg) then
              pure (some drhs, some (← mkEqSymm decl.toExpr))
            else do
            if ← pure (!dlhs.hasFVar && !dlhs.hasMVar) <&&> withReducible (isDefEq drhs bArg) then
              pure (some dlhs, some decl.toExpr)
            else pure (none, none)
          if let (some nLit, some hEqToRhs) := (nLit?, hEqToRhs?) then
            try
              let φSubst := mkApp φ.appFn! nLit
              let dec ← mkDecide φSubst
              if ← isDefEq dec (mkConst ``true) then
                let hDec ← mkDecideProof φSubst
                let hCongr ← mkCongrArg φ.appFn! hEqToRhs
                return some (← mkExpectedTypeHint (← mkEqMP hCongr hDec) φ)
            catch _ => pure ()
  if !φ.hasFVar && !φ.hasMVar then
    try
      let dec ← mkDecide φ
      if ← isDefEq dec (mkConst ``true) then
        return some (← mkDecideProof φ)
    catch _ =>
      pure ()
  return none

/-- Lift a `TacticM` side-condition discharger (`disch`), trying fast kernel `metaDisch` first and
    preserving `Environment` auxiliary theorems when invoking `disch` (`bv_omega`). -/
def liftTacDisch (disch : Disch) (φ : Expr) : TacticM (Option Expr) := do
  if let some prf ← metaDisch φ then
    return some prf
  let savedMCtx ← getMCtx
  let savedGoals ← getGoals
  try
    if let some prf ← disch φ then
      setGoals savedGoals
      return some (← mkExpectedTypeHint (← instantiateMVars prf) φ)
    setMCtx savedMCtx
    setGoals savedGoals
    return none
  catch _ =>
    setMCtx savedMCtx
    setGoals savedGoals
    return none

private def proveEqOrLeFast? {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (ty : Expr) : M (Option Expr) := do
  let ty ← (instantiateMVars ty : MetaM Expr)
  if let some (_, lhs, rhs) := ty.eq? then
    if ← (isDefEq lhs rhs : MetaM Bool) then
      return some (← (mkExpectedTypeHint (← mkEqRefl rhs) ty : MetaM Expr))
  disch ty

/-- Recursively inline any local `let`-bound free variables (`ldecl` with `decl.value? = some v`) inside `e`. -/
partial def unfoldLetFVars (e : Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let e' ← instantiateMVars e
  if !e'.hasFVar then return e'
  let rec go (t : Expr) : Expr :=
    t.replace fun sub =>
      if sub.isFVar then
        match lctx.find? sub.fvarId! >>= (·.value?) with
        | some val => some (go val)
        | none => none
      else none
  return go e'

/-- If `[q, q + wExpr)` provably lies inside `memRegion p nExpr` (via constant-offset `normAddr`
    or `disch`/`bv_omega`), return `(rhs, eqPrf)` with `eqPrf : memRegion p nExpr = rhs`, where
    `rhs` starts with `memRegion q wExpr` followed by non-empty remainder `memRegion` slices. -/
def splitMemRegionSubblock? {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (p nExpr q wExpr : Expr) :
    M (Option (Expr × Expr)) := do
  if p.hasMVar || q.hasMVar || nExpr.hasMVar || wExpr.hasMVar then return none
  let pLet ← (unfoldLetFVars p : MetaM Expr)
  let qLet ← (unfoldLetFVars q : MetaM Expr)
  let pow64 ← (mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)] : MetaM Expr)
  -- Fast path: constant offset `q - p = k` and concrete lengths `n`, `w`
  if let some k ← (constAddrOffset? pLet qLet : MetaM (Option Nat)) then
    if let (some n, some w) := (← (evalNatLitSolver? nExpr : MetaM (Option Nat)), ← (evalNatLitSolver? wExpr : MetaM (Option Nat))) then
      if k + w > n || n > 2 ^ 64 then return none
      let rem := n - k - w
      let memRegQ := mkApp2 (mkConst ``memRegion) q wExpr
      if k == 0 && rem == 0 then
        let some hq ← proveEqOrLeFast? disch (← (mkEq p q : MetaM Expr)) | return none
        let some hw ← proveEqOrLeFast? disch (← (mkEq nExpr wExpr : MetaM Expr)) | return none
        let prf := mkAppN (mkConst ``memRegion_subblock_exact) #[p, q, nExpr, wExpr, hq, hw]
        return some (memRegQ, prf)
      else if k == 0 then
        let (r, hr) ← (normAddConstOffsetAddr q wExpr : MetaM (Expr × Expr))
        let remExpr := mkNatLit rem
        let some hq ← proveEqOrLeFast? disch (← (mkEq p q : MetaM Expr)) | return none
        let subExpr ← (mkAppM ``HSub.hSub #[nExpr, wExpr] : MetaM Expr)
        let some hrem ← proveEqOrLeFast? disch (← (mkEq subExpr remExpr : MetaM Expr)) | return none
        let some hw ← proveEqOrLeFast? disch (← (mkAppM ``LE.le #[wExpr, nExpr] : MetaM Expr)) | return none
        let some hn ← proveEqOrLeFast? disch (← (mkAppM ``LE.le #[nExpr, pow64] : MetaM Expr)) | return none
        let rhs := mkSep memRegQ (mkApp2 (mkConst ``memRegion) r remExpr)
        let prf := mkAppN (mkConst ``memRegion_subblock_prefix)
          #[p, q, r, nExpr, wExpr, remExpr, hq, hr, hrem, hw, hn]
        return some (rhs, prf)
      else if rem == 0 then
        let kExpr := mkNatLit k
        let (qNorm, hq0) ← (normAddConstOffsetAddr p kExpr : MetaM (Expr × Expr))
        let some hq1 ← proveEqOrLeFast? disch (← (mkEq qNorm q : MetaM Expr)) | return none
        let hq ← (mkEqTrans hq0 hq1 : MetaM Expr)
        let addExpr ← (mkAppM ``HAdd.hAdd #[kExpr, wExpr] : MetaM Expr)
        let some hkw ← proveEqOrLeFast? disch (← (mkEq addExpr nExpr : MetaM Expr)) | return none
        let some hn ← proveEqOrLeFast? disch (← (mkAppM ``LE.le #[nExpr, pow64] : MetaM Expr)) | return none
        let rhs := mkSep memRegQ (mkApp2 (mkConst ``memRegion) p kExpr)
        let prf := mkAppN (mkConst ``memRegion_subblock_suffix)
          #[p, q, nExpr, kExpr, wExpr, hq, hkw, hn]
        return some (rhs, prf)
      else
        let kExpr := mkNatLit k
        let remExpr := mkNatLit rem
        let (qNorm, hq0) ← (normAddConstOffsetAddr p kExpr : MetaM (Expr × Expr))
        let some hq1 ← proveEqOrLeFast? disch (← (mkEq qNorm q : MetaM Expr)) | return none
        let hq ← (mkEqTrans hq0 hq1 : MetaM Expr)
        let (r, hr) ← (normAddConstOffsetAddr q wExpr : MetaM (Expr × Expr))
        let remLhs ← (mkAppM ``HSub.hSub #[← mkAppM ``HSub.hSub #[nExpr, kExpr], wExpr] : MetaM Expr)
        let some hrem ← proveEqOrLeFast? disch (← (mkEq remLhs remExpr : MetaM Expr)) | return none
        let kwLhs ← (mkAppM ``HAdd.hAdd #[kExpr, wExpr] : MetaM Expr)
        let some hkw ← proveEqOrLeFast? disch (← (mkAppM ``LE.le #[kwLhs, nExpr] : MetaM Expr)) | return none
        let some hn ← proveEqOrLeFast? disch (← (mkAppM ``LE.le #[nExpr, pow64] : MetaM Expr)) | return none
        let rhs := mkSep memRegQ (mkSep (mkApp2 (mkConst ``memRegion) p kExpr) (mkApp2 (mkConst ``memRegion) r remExpr))
        let prf := mkAppN (mkConst ``memRegion_subblock_mid)
          #[p, q, r, nExpr, kExpr, wExpr, remExpr, hq, hr, hrem, hkw, hn]
        return some (rhs, prf)
  -- Fast static rejection before invoking `disch` (`bv_omega`):
  -- 1. Unfold local `let`-bindings so `let q := p + 8` exposes shared bases before comparison.
  -- 2. If `p` and `q` share a base (`bp == bq`), any negative offset `oq < op` wraps modulo `2 ^ 64`.
  -- 3. If `bp` and `bq` are distinct free variables with no pure local declaration mentioning both,
  --    `(q - p).toNat + wExpr ≤ nExpr` cannot hold across independent pointers.
  let (bp, op) ← (splitBaseOff pLet : MetaM (Expr × Int))
  let (bq, oq) ← (splitBaseOff qLet : MetaM (Expr × Int))
  if bp == bq && oq < op then return none
  if bp.isFVar && bq.isFVar && bp != bq then
    let pId := bp.fvarId!
    let qId := bq.fvarId!
    let mut linked := false
    for decl in (← (getLCtx : MetaM LocalContext)) do
      if !decl.isImplementationDetail then
        let ty ← (instantiateMVars decl.type : MetaM Expr)
        let inTy := !ty.isAppOfArity ``SepProp.Satisfies 2 && ty.containsFVar pId && ty.containsFVar qId
        let inVal ← match decl.value? with
          | some val => do
            let v ← (instantiateMVars val : MetaM Expr)
            pure ((v.containsFVar pId && v.containsFVar qId) ||
                  (decl.fvarId == pId && v.containsFVar qId) ||
                  (decl.fvarId == qId && v.containsFVar pId))
          | none => pure false
        if inTy || inVal then
          linked := true
          break
    unless linked do return none
  -- Symbolic fallback: `k := (q - p).toNat`, side condition `(q - p).toNat + wExpr ≤ nExpr ∧ nExpr ≤ 2^64` via `disch`
  let qSubP ← (mkAppM ``HSub.hSub #[q, p] : MetaM Expr)
  let kExpr := mkApp2 (mkConst ``BitVec.toNat) (toExpr (64 : Nat)) qSubP
  let wBV ← (mkAppM ``BitVec.ofNat #[toExpr (64 : Nat), wExpr] : MetaM Expr)
  let rExpr ← (mkAppM ``HAdd.hAdd #[q, wBV] : MetaM Expr)
  let remExpr ← (mkAppM ``HSub.hSub #[← mkAppM ``HSub.hSub #[nExpr, kExpr], wExpr] : MetaM Expr)
  let kwGoal ← (mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[kExpr, wExpr], nExpr] : MetaM Expr)
  let nGoal ← (mkAppM ``LE.le #[nExpr, pow64] : MetaM Expr)
  let some hkw ← disch kwGoal | return none
  let some hn ← disch nGoal | return none
  let hq := mkApp2 (mkConst ``memRegion_add_ofNat_sub_toNat) p q
  let hr ← (mkEqRefl rExpr : MetaM Expr)
  let hrem ← (mkEqRefl remExpr : MetaM Expr)
  let memRegQ := mkApp2 (mkConst ``memRegion) q wExpr
  let rhs := mkSep memRegQ (mkSep (mkApp2 (mkConst ``memRegion) p kExpr) (mkApp2 (mkConst ``memRegion) rExpr remExpr))
  let prf := mkAppN (mkConst ``memRegion_subblock_mid)
    #[p, q, rExpr, nExpr, kExpr, wExpr, remExpr, hq, hr, hrem, hkw, hn]
  return some (rhs, prf)

/-- Prove `h = g` for atoms with the same constant head, discharging differing closed arguments
    via `disch`. -/
def congrAtomsWithDisch? {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (h g : Expr) : M (Option Expr) := do
  let h := stripMData (← (instantiateMVars h : MetaM Expr))
  let g := stripMData (← (instantiateMVars g : MetaM Expr))
  unless h.getAppFn == g.getAppFn && h.getAppNumArgs == g.getAppNumArgs do return none
  unless h.getAppFn.isConst do return none
  let mut prf ← (mkEqRefl h.getAppFn : MetaM Expr)
  for a in h.getAppArgs, b in g.getAppArgs do
    if a == b then
      prf ← (mkCongrFun prf a : MetaM Expr)
    else if ← (withReducibleAndInstances (isDefEq a b) : MetaM Bool) then
      prf ← (mkCongrFun prf a : MetaM Expr)
    else if !a.hasMVar && !b.hasMVar then
      let eqTy ← (mkEq a b : MetaM Expr)
      let some e ← disch eqTy | return none
      prf ← (mkCongr prf e : MetaM Expr)
    else
      return none
  return some prf

/-- Unfold any atom in `cur` whose head constant is tagged `@[sep_unfold]` and does not have a
    same-head match in `other`, normalizing the unfolded result with `normSepPropMeta`. -/
def unfoldUnmatchedSepUnfoldAtoms (cur : Expr) (hCur? : Option Expr) (other : Expr) :
    MetaM (Expr × Option Expr) := do
  unless proofLib.frameSplitUnfold.get (← getOptions) do return (cur, hCur?)
  let otherAtoms := atoms other
  let mut curE := cur
  let mut curH? := hCur?
  for _ in [0:16] do
    let as := atoms curE
    let mut changed := false
    for hi : i in [:as.size] do
      let a := stripMData (← instantiateMVars as[i])
      let some fn := a.getAppFn.constName? | continue
      unless ← isSepUnfoldConst fn do continue
      if otherAtoms.any fun b =>
          let b := stripMData b
          b == a || (b.getAppFn.constName? == some fn &&
            (a.getAppNumArgs == 0 || (b.getAppNumArgs > 0 && b.getArg! 0 == a.getArg! 0))) then
        continue
      let some aUnf ← unfoldDefinition? a | continue
      let (aNorm, pNorm?) ← normSepPropMeta aUnf
      let eqPrf ← match pNorm? with
        | some pNorm => mkExpectedTypeHint pNorm (← mkEq a aNorm)
        | none => mkExpectedTypeHint (← mkEqRefl aNorm) (← mkEq a aNorm)
      if let some (nextE, hTree) ← rewriteAtomAtEq? curE i aNorm eqPrf then
        curE := nextE
        curH? ← mkEqTransOpt curH? (some hTree)
        changed := true
        break
    if !changed then break
  return (curE, curH?)

/-- Unfold `@[sep_unfold]` atoms in `e` that do not have a same-head match in `other`
    (definitional tree transformation for `sep_frame`). -/
partial def expandSepUnfoldTree (e : Expr) (other : Expr) (fuel : Nat := 8) : MetaM Expr := do
  unless proofLib.frameSplitUnfold.get (← getOptions) do return e
  let otherAtoms := atoms other
  let rec go (t : Expr) (f : Nat) : MetaM Expr := do
    let t := (← instantiateMVars t).consumeMData.headBeta
    if t.isAppOfArity ``SepProp.sepConj 2 then
      return mkSep (← go (t.getArg! 0) f) (← go (t.getArg! 1) f)
    if f == 0 then return t
    let a := stripMData t
    let some fn := a.getAppFn.constName? | return t
    unless ← isSepUnfoldConst fn do return t
    if otherAtoms.any fun b =>
        let b := stripMData b
        b == a || (b.getAppFn.constName? == some fn &&
          (a.getAppNumArgs == 0 || (b.getAppNumArgs > 0 && b.getArg! 0 == a.getArg! 0))) then
      return t
    let some aUnf ← unfoldDefinition? a | return t
    go aUnf (f - 1)
  go e fuel

/-- Extract the first address argument of a spatial atom or existential spatial atom. -/
def atomFirstAddr? (e : Expr) : Option Expr :=
  let e := (stripMData e).headBeta
  if e.isAppOfArity ``SepProp.sepExists 2 then
    match (e.getArg! 1).consumeMData with
    | .lam _ _ body _ =>
      let body := (stripMData body).headBeta
      if body.getAppNumArgs >= 1 && !(body.getArg! 0).hasLooseBVars then
        some (body.getArg! 0)
      else none
    | _ => none
  else if e.getAppNumArgs >= 1 then
    some (e.getArg! 0)
  else none

/-- If `a` is `stackFrameAt sp nExpr` (or `stackFrame16At sp` / `stackFrame32At sp`), rewrite it
    to normalized `memRegion (sp - n) n` via `solver_stackFrameAt_eq_memRegion`. -/
def expandStackFrameAtAtom? {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (a : Expr) : M (Option (Expr × Expr)) := do
  let a ← (instantiateMVars a : MetaM Expr)
  let (sp, nExpr) ←
    if a.isAppOfArity ``Arm64.stackFrameAt 2 then
      pure (a.getArg! 0, a.getArg! 1)
    else if a.isAppOfArity ``Arm64.stackFrame16At 1 then
      pure (a.getArg! 0, toExpr (16 : Nat))
    else if a.isAppOfArity ``Arm64.stackFrame32At 1 then
      pure (a.getArg! 0, toExpr (32 : Nat))
    else
      return none
  let pow64 ← (mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)] : MetaM Expr)
  let some hn ← proveEqOrLeFast? disch (← (mkAppM ``LE.le #[nExpr, pow64] : MetaM Expr)) | return none
  let rawEq := mkApp3 (mkConst ``solver_stackFrameAt_eq_memRegion) sp nExpr hn
  let rawRhs := (← (instantiateMVars (← inferType rawEq) : MetaM Expr)).getArg! 2
  let (rhsNorm, pNorm?) ← (normSepPropMeta rawRhs : MetaM (Expr × Option Expr))
  let eqPrf ← match pNorm? with
    | some pNorm => (mkEqTrans rawEq pNorm : MetaM Expr)
    | none => pure rawEq
  let eqPrf ← (mkExpectedTypeHint eqPrf (← mkEq a rhsNorm) : MetaM Expr)
  return some (rhsNorm, eqPrf)

/-- Expand any `stackFrameAt` atoms in `cur` that do not appear identically in `other` and share a
    base pointer with an atom of `other` into normalized `memRegion` atoms. -/
def expandUnmatchedStackFrameAtoms {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (cur : Expr) (hCur? : Option Expr) (other : Expr) :
    M (Expr × Option Expr) := do
  unless proofLib.frameSplitContainers.get (← (getOptions : MetaM Options)) do return (cur, hCur?)
  let otherAtoms := atoms other
  let mut otherBases : Array Expr := #[]
  for oa in otherAtoms do
    if let some addr := atomFirstAddr? oa then
      let (ob, _) ← (splitBaseOff (← unfoldLetFVars addr) : MetaM (Expr × Int))
      otherBases := otherBases.push ob
  let mut curE := cur
  let mut curH? := hCur?
  for _ in [0:16] do
    let as := atoms curE
    let mut changed := false
    for hi : i in [:as.size] do
      let a ← (instantiateMVars as[i] : MetaM Expr)
      if otherAtoms.any (· == a) then continue
      let some spAddr := atomFirstAddr? a | continue
      let (ab, _) ← (splitBaseOff (← unfoldLetFVars spAddr) : MetaM (Expr × Int))
      unless otherBases.any (· == ab) do continue
      if let some (rhs, eqPrf) ← expandStackFrameAtAtom? disch a then
        if let some (nextE, hTree) ← (rewriteAtomAtEq? curE i rhs eqPrf : MetaM _) then
          curE := nextE
          curH? ← (mkEqTransOpt curH? (some hTree) : MetaM _)
          changed := true
          break
    if !changed then break
  return (curE, curH?)

/-- If `s` is `q ↦_w v` or `∃∗ v, q ↦_w v` for `w ∈ {1, 2, 4, 8}`, return `(q, w, focusName)`. -/
def pointsToFocusTargetInfo? (s : Expr) : Option (Expr × Nat × Name) :=
  let s := (stripMData s).headBeta
  let cellExpr :=
    if s.isAppOfArity ``SepProp.sepExists 2 then
      match (s.getArg! 1).consumeMData with
      | .lam _ _ body _ =>
        let body := (stripMData body).headBeta
        if body.getAppNumArgs >= 1 && !(body.getArg! 0).hasLooseBVars then body else s
      | _ => s
    else s
  let fn := cellExpr.getAppFn.constName?.getD .anonymous
  if cellExpr.getAppNumArgs >= 2 then
    if fn == ``Arm64.pointsTo8 then some (cellExpr.getArg! 0, 1, `ProofLib.pointsToBytes_focus8)
    else if fn == ``Arm64.pointsTo16 then some (cellExpr.getArg! 0, 2, `ProofLib.pointsToBytes_focus16)
    else if fn == ``Arm64.pointsTo32 then some (cellExpr.getArg! 0, 4, `ProofLib.pointsToBytes_focus32)
    else if fn == ``Arm64.pointsTo64 then some (cellExpr.getArg! 0, 8, `ProofLib.pointsToBytes_focus64)
    else none
  else none

/-- Pre-split at most once per `p ↦ₛ bs` (`pointsToBytes`) atom in `curFull` when `sub'` requests
    a fixed-width cell `q ↦_w v` (`w ∈ {1, 2, 4, 8}`) at a constant offset `off` inside `bs`. -/
def preSplitPointsToBytes {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (curFull : Expr) (curHFull? : Option Expr) (sub' : Expr) :
    M (Expr × Option Expr) := do
  unless proofLib.frameSplitContainers.get (← (getOptions : MetaM Options)) do
    return (curFull, curHFull?)
  let initAtoms := atoms curFull
  let origSlices := initAtoms.filter (·.isAppOfArity ``Arm64.pointsToBytes 2)
  if origSlices.isEmpty then return (curFull, curHFull?)
  let mut fullE := curFull
  let mut hFull? := curHFull?
  let mut usedSlices : Array Expr := #[]
  for s0 in atoms sub' do
    let s ← (instantiateMVars s0 : MetaM Expr)
    let fs := atoms fullE
    if fs.any (· == s) then continue
    let some (q, w, focusName) := pointsToFocusTargetInfo? s | continue
    unless (← (getEnv : MetaM Environment)).contains focusName do continue
    if fs.any (fun a => !(a.isAppOfArity ``Arm64.pointsToBytes 2) && atomFirstAddr? a == some q) then
      continue
    let qLet ← (unfoldLetFVars q : MetaM Expr)
    for hi : i in [:fs.size] do
      let a := fs[i]
      if a.isAppOfArity ``Arm64.pointsToBytes 2 && origSlices.contains a && !usedSlices.contains a then
        let p := a.getArg! 0
        let bs := a.getArg! 1
        let pLet ← (unfoldLetFVars p : MetaM Expr)
        let some off ← (constAddrOffset? pLet qLet : MetaM (Option Nat)) | continue
        let lenExpr ← (mkAppM ``List.length #[bs] : MetaM Expr)
        let boundGoal ←
          if w == 1 then (mkAppM ``LT.lt #[mkNatLit off, lenExpr] : MetaM Expr)
          else (mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit off, mkNatLit w], lenExpr] : MetaM Expr)
        let some hBound ← proveEqOrLeFast? disch boundGoal | continue
        let rawEq ← (mkAppM focusName #[p, bs, mkNatLit off, hBound] : MetaM Expr)
        let rawRhs := (← (instantiateMVars (← inferType rawEq) : MetaM Expr)).getArg! 2
        let (rhsNorm, pNorm?) ← (normSepPropMeta rawRhs : MetaM (Expr × Option Expr))
        let eqPrf ← match pNorm? with
          | some pNorm => (mkEqTrans rawEq pNorm : MetaM Expr)
          | none => pure rawEq
        let eqPrf ← (mkExpectedTypeHint eqPrf (← mkEq a rhsNorm) : MetaM Expr)
        if let some (nextFull, hTree) ← (rewriteAtomAtEq? fullE i rhsNorm eqPrf : MetaM _) then
          fullE := nextFull
          hFull? ← (mkEqTransOpt hFull? (some hTree) : MetaM _)
          usedSlices := usedSlices.push a
          break
  return (fullE, hFull?)

private def isPureNearMissHypDecl (decl : LocalDecl) : MetaM Bool := do
  if decl.isImplementationDetail || decl.hasValue then return false
  let ty := (← instantiateMVars decl.type).consumeMData
  unless ← isProp ty do return false
  if let some n := ty.getAppFn.constName? then
    if n == ``SepProp.Satisfies || n == ``SepProp.Entails ||
       n == `ProofLib.SepFrame ||
       n == `ProofLib.SepLoad8 || n == `ProofLib.SepLoad16 ||
       n == `ProofLib.SepLoad32 || n == `ProofLib.SepLoad64 ||
       n == `ProofLib.SepStore8 || n == `ProofLib.SepStore16 ||
       n == `ProofLib.SepStore32 || n == `ProofLib.SepStore64 ||
       n == `ProofLib.SepStoreDcZva ||
       n == ``Arm64.Program.hasCode || n == `ProofLib.FnCode.holds ||
       n.toString.endsWith "SepWP" || n.toString.endsWith "SepWPp" then
      return false
  return true

private partial def pruneNearMissGoal?
    (g : MVarId) (eqTy lhsLet rhsLet : Expr) : MetaM (Option MVarId) := g.withContext do
  let lctx ← getLCtx
  let addExprFVars (e : Expr) (s0 : Std.HashSet FVarId) : Std.HashSet FVarId :=
    let rec collect (t : Expr) (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
      if !t.hasFVar then acc
      else match t with
        | .fvar id =>
          if acc.contains id then acc
          else
            let acc := acc.insert id
            match lctx.find? id >>= (·.value?) with
            | some v => collect v acc
            | none => acc
        | .app f a => collect a (collect f acc)
        | .lam _ d b _ | .forallE _ d b _ => collect b (collect d acc)
        | .letE _ d v b _ => collect b (collect v (collect d acc))
        | .mdata _ b | .proj _ _ b => collect b acc
        | _ => acc
    collect e s0
  let mut pureDecls : Array (LocalDecl × Expr × Std.HashSet FVarId) := #[]
  for decl in lctx do
    if ← isPureNearMissHypDecl decl then
      let ty ← instantiateMVars decl.type
      pureDecls := pureDecls.push (decl, ty, addExprFVars ty {})
  let anyClosedFalse := pureDecls.any fun (_, ty, _) =>
    !ty.hasFVar && (ty.find? (·.isConstOf ``False)).isSome
  let nonSubsingletonCarrier : Bool :=
    match eqTy.eq? with
    | some (argTy, _, _) =>
      let argTy := argTy.consumeMData
      argTy.isConstOf ``Nat ||
        (argTy.isAppOfArity ``BitVec 1 && (argTy.getArg! 0).consumeMData != mkNatLit 0)
    | none => false
  if !anyClosedFalse && nonSubsingletonCarrier then
    let lhsFVs := addExprFVars lhsLet {}
    let rhsFVs := addExprFVars rhsLet {}
    if lhsLet.isFVar then
      let fv := lhsLet.fvarId!
      if ((lctx.find? fv) >>= (·.value?)).isNone && !rhsFVs.contains fv &&
          !(pureDecls.any fun (_, _, fvs) => fvs.contains fv) then
        return none
    if rhsLet.isFVar then
      let fv := rhsLet.fvarId!
      if ((lctx.find? fv) >>= (·.value?)).isNone && !lhsFVs.contains fv &&
          !(pureDecls.any fun (_, _, fvs) => fvs.contains fv) then
        return none
  let tgt ← instantiateMVars (← g.getType)
  let mut relFVars := addExprFVars tgt {}
  let mut keptHyps : Std.HashSet FVarId := {}
  for _ in [:pureDecls.size] do
    let mut grew := false
    for (decl, ty, tyFVars) in pureDecls do
      if !keptHyps.contains decl.fvarId then
        let sharesFVar := tyFVars.toList.any relFVars.contains
        let closedFalse := !ty.hasFVar && (ty.find? (·.isConstOf ``False)).isSome
        if sharesFVar || closedFalse then
          keptHyps := keptHyps.insert decl.fvarId
          for fv in tyFVars.toList do
            relFVars := relFVars.insert fv
          grew := true
    if !grew then break
  let mut toClear : Array FVarId := #[]
  for decl in lctx.decls.toList.reverse do
    if let some d := decl then
      if !d.isImplementationDetail && !d.hasValue then
        if ← isProp d.type then
          if !keptHyps.contains d.fvarId then
            toClear := toClear.push d.fvarId
  return some (← g.tryClearMany toClear)

/-- Prove a near-miss address or length equality `lhs = rhs` using fast `MetaM` normalization and
    `ProofLib.BV.Lin` first, falling back to a bounded normalizer chain (`dsimp (zetaDelta := true)`,
    `subst_vars`, `arm64_norm`, `bv_lin`, `bv_arith`, `proveOmegaBounded?`) on a relevance-pruned
    goal. -/
partial def proveNearMissEq? (eqTy : Expr) : MetaM (Option Expr) := do
  let eqTy ← instantiateMVars eqTy
  let some (_, lhs, rhs) := eqTy.eq? | return none
  if lhs.hasMVar || rhs.hasMVar then return none
  if let some prf ← metaDisch eqTy then return some prf
  let lhsLet ← unfoldLetFVars lhs
  let rhsLet ← unfoldLetFVars rhs
  if lhsLet == rhsLet || (← isDefEq lhsLet rhsLet) then
    return some (← mkExpectedTypeHint (← mkEqRefl rhsLet) eqTy)
  if lhsLet != lhs || rhsLet != rhs then
    let (nl, _) ← normAddrMeta lhsLet
    let (nr, _) ← normAddrMeta rhsLet
    if nl == nr || (← isDefEq nl nr) then
      if ← isDefEq lhs rhs then
        return some (← mkExpectedTypeHint (← mkEqRefl rhs) eqTy)
  if (← ProofLib.BV.Lin.proveNe? lhsLet rhsLet).isSome then return none
  if let (some n1, some n2) := (← evalNatLitSolver? lhsLet, ← evalNatLitSolver? rhsLet) then
    if n1 == n2 then return some (← mkExpectedTypeHint (← mkEqRefl rhs) eqTy)
    else return none
  if let some pf ← ProofLib.BV.Lin.proveEq? lhsLet rhsLet then
    return some (← mkExpectedTypeHint pf eqTy)
  let outerMaxHb := (← readThe Core.Context).maxHeartbeats
  let outerCap := if outerMaxHb == 0 then 8000 else Nat.min 8000 (outerMaxHb / 2000)
  if outerCap == 0 then return none
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  let fail : MetaM (Option Expr) := do
    saved.restore
    Core.setMessageLog savedMsgs
    return none
  try
    let mvar ← mkFreshExprSyntheticOpaqueMVar eqTy
    let some gPruned ← pruneNearMissGoal? mvar.mvarId! eqTy lhsLet rhsLet
      | return ← fail
    let ok ← MonadRuntimeException.tryCatchRuntimeEx
      (withOptions (fun o => o.set `linter.unusedSimpArgs false |>.set `warningAsError false) <|
       withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := outerCap * 1000 }) <|
       withCurrHeartbeats do
        let gs ← Term.TermElabM.run' <| Tactic.run gPruned do
          let stepOrKeep (g : MVarId) (tac : Syntax) (cap : Nat) : TacticM (Option MVarId) := do
            let res? ← ProofLib.tryTacticCatchRuntime <| ProofLib.withHeartbeatCap cap do
              let subGs ← Tactic.run g (withoutRecover (evalTactic tac))
              if subGs.isEmpty && (← instantiateMVars (mkMVar g)).hasSorry then
                throwError "contains sorry"
              if subGs.length > 1 then
                throwError "multiple goals"
              return subGs
            match res? with
            | some [] => return none
            | some [g'] => return some g'
            | _ => return some g
          let trySolvers (g : MVarId) (full : Bool) : TacticM Bool := do
            if ← ProofLib.runTacCapped g (← `(tactic| with_reducible rfl)) 1000 then return true
            if ← ProofLib.runTacCapped g (← `(tactic| decide)) 1000 then return true
            if ← ProofLib.runTacCapped g (← `(tactic| (bv_lin; done))) 2500 then return true
            if !full then return false
            if ← ProofLib.runTacCapped g (← `(tactic| (bv_arith; done))) 2500 then return true
            if ← ProofLib.proveOmegaBounded? g (← ProofLib.omegaDefaultTacs) (cap := 2500) then
              return true
            return false
          let some g1 ← stepOrKeep gPruned (← `(tactic| (
            try dsimp (config := { zetaDelta := true }) only at *
            try subst_vars))) 1500
            | Tactic.setGoals []; return
          if ← trySolvers g1 false then
            Tactic.setGoals []; return
          let some g2 ← stepOrKeep g1 (← `(tactic|
            simp (config := { decide := true, zetaDelta := true, maxSteps := 2000 }) only
              [ite_true, ite_false, dite_true, dite_false, Bool.false_eq_true, Bool.true_eq_false,
               wp_norm, arm64_norm, BitVec.ofNat_toNat, BitVec.setWidth_eq, *])) 2500
            | Tactic.setGoals []; return
          if ← trySolvers g2 true then
            Tactic.setGoals []; return
          let some g3 ← stepOrKeep g2 (← `(tactic| (
            apply BitVec.eq_of_toNat_eq
            try simp (config := { decide := true, zetaDelta := true, maxSteps := 2000 }) only
              [ite_true, ite_false, dite_true, dite_false, Bool.false_eq_true, Bool.true_eq_false,
               wp_norm, arm64_norm, BitVec.toNat_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, *])))
            2500
            | Tactic.setGoals []; return
          if g3 != g2 then
            if ← ProofLib.proveOmegaBounded? g3 (← ProofLib.omegaDefaultTacs) (cap := 2500) then
              Tactic.setGoals []; return
        return gs.isEmpty)
      (fun _ => return false)
    unless ok do return ← fail
    let prf ← instantiateMVars mvar
    if prf.hasSorry || prf.hasExprMVar then return ← fail
    Core.setMessageLog savedMsgs
    return some (← mkExpectedTypeHint prf eqTy)
  catch _ =>
    return ← fail

private partial def congrTermNearMiss? (a b : Expr) (fuel : Nat := 4) : MetaM (Option Expr) := do
  let a := stripMData (← instantiateMVars a)
  let b := stripMData (← instantiateMVars b)
  if a == b then
    return some (← mkEqRefl a)
  if ← withReducibleAndInstances (isDefEq a b) then
    let aInst ← instantiateMVars a
    return some (← mkEqRefl aInst)
  if fuel > 0 && a.getAppFn == b.getAppFn && a.getAppFn.isConst && a.getAppNumArgs == b.getAppNumArgs then
    let savedMCtx ← getMCtx
    let mut prf ← mkEqRefl a.getAppFn
    let mut allOk := true
    for ai in a.getAppArgs, bi in b.getAppArgs do
      if let some ei ← congrTermNearMiss? ai bi (fuel - 1) then
        prf ← mkCongr prf ei
      else
        allOk := false
        break
    if allOk then
      return some prf
    setMCtx savedMCtx
  if !a.hasMVar && !b.hasMVar then
    return ← proveNearMissEq? (← mkEq a b)
  return none

/-- Prove `a = s` for spatial near-miss atoms with the same constant head and arity, rolling back
    any tentative metavariable assignments if any argument equality fails. -/
def congrAtomsNearMiss? (a s : Expr) : MetaM (Option Expr) := do
  let a := stripMData (← instantiateMVars a)
  let s := stripMData (← instantiateMVars s)
  unless a.getAppFn == s.getAppFn && a.getAppNumArgs == s.getAppNumArgs do return none
  unless a.getAppFn.isConst do return none
  if s.getAppNumArgs >= 1 && (s.getArg! 0).hasMVar then return none
  let savedMCtx ← getMCtx
  let mut prf ← mkEqRefl a.getAppFn
  for ai in a.getAppArgs, si in s.getAppArgs do
    match ← congrTermNearMiss? ai si 4 with
    | some ei => prf ← mkCongr prf ei
    | none =>
      setMCtx savedMCtx
      return none
  return some prf

/-- On the fallback pass (`splitRegions = true`), when `proofLib.frameSplitNearMiss` is enabled,
    rewrite any context atom `a` in `curFull` to a target atom `s` in `sub'` at the same predicate
    head when either (Pass 1) `a` and `s` already share a definitionally equal address and `disch`
    proves their value equality, or (Pass 2) `congrAtomsNearMiss?` proves their address/length/value
    equality with bounded normalizers. -/
def preCongrNearMissAtoms {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (curFull : Expr) (curHFull? : Option Expr) (sub' : Expr) :
    M (Expr × Option Expr) := do
  unless proofLib.frameSplitNearMiss.get (← (getOptions : MetaM Options)) do
    return (curFull, curHFull?)
  let mut fullE := curFull
  let mut hFull? := curHFull?
  let subAtoms := atoms sub'
  for s0 in subAtoms do
    let s ← (instantiateMVars s0 : MetaM Expr)
    if s.isMVar then continue
    let fs := atoms fullE
    let mut alreadyMatched := false
    for a in fs do
      if a == s then alreadyMatched := true; break
      if a.getAppFn == s.getAppFn then
        if ← (withReducibleAndInstances (isDefEq a s) : MetaM Bool) then
          alreadyMatched := true; break
    if alreadyMatched then continue
    let mut matchedPass1 := false
    for hi : i in [:fs.size] do
      let a := fs[i]
      if subAtoms.any (· == a) then continue
      if a.getAppFn == s.getAppFn && a.getAppNumArgs == s.getAppNumArgs then
        let addrOk ←
          if isPrimSepAtom s && a.getAppNumArgs >= 1 then
            (withReducibleAndInstances (isDefEq (a.getArg! 0) (s.getArg! 0)) : MetaM Bool)
          else
            pure true
        if addrOk then
          if let some eqPrf ← congrAtomsWithDisch? disch a s then
            if let some (nextFull, hTree) ← (rewriteAtomAtEq? fullE i s eqPrf : MetaM _) then
              fullE := nextFull
              hFull? ← (mkEqTransOpt hFull? (some hTree) : MetaM _)
              matchedPass1 := true
              break
    if matchedPass1 then continue
    if s.getAppNumArgs >= 1 && (s.getArg! 0).hasMVar then continue
    let mut tried := 0
    for hi : i in [:fs.size] do
      if tried >= 6 then break
      let a := fs[i]
      if subAtoms.any (· == a) then continue
      if a.getAppFn == s.getAppFn && a.getAppNumArgs == s.getAppNumArgs then
        if a.getAppNumArgs >= 1 then
          let aAddr ← (unfoldLetFVars (a.getArg! 0) : MetaM Expr)
          let sAddr ← (unfoldLetFVars (s.getArg! 0) : MetaM Expr)
          if (← (ProofLib.BV.Lin.proveNe? aAddr sAddr : MetaM _)).isSome then continue
        tried := tried + 1
        if let some eqPrf ← (congrAtomsNearMiss? a s : MetaM (Option Expr)) then
          let sInst ← (instantiateMVars s : MetaM Expr)
          if let some (nextFull, hTree) ← (rewriteAtomAtEq? fullE i sInst eqPrf : MetaM _) then
            fullE := nextFull
            hFull? ← (mkEqTransOpt hFull? (some hTree) : MetaM _)
            break
  return (fullE, hFull?)

/-- Pre-split any `memRegion p n` atoms in `P` when an unmatched goal block `g` (`q ↦_w v` or
    `memRegion q w`) provably lies inside `[p, p + n)`. -/
def preSplitHypMemRegions (disch : Disch) (m P h Gs : Expr) :
    TacticM (Expr × Expr) := do
  let initAtoms := atoms P
  unless initAtoms.any (·.isAppOfArity ``memRegion 2) do return (P, h)
  let mut curP := P
  let mut cur := h
  let mut reserved : Array (Expr × Expr) := #[]
  let gs := atoms Gs
  -- Reserve existing exact-base block matches so we never split a region for an already-present cell
  for g0 in gs do
    let g ← instantiateMVars g0
    if g.isMVar then continue
    if let some gb ← blockOf? g then
      for ha in initAtoms do
        if let some hb ← blockOf? ha then
          if hb.base == gb.base && hb.len == gb.len then
            reserved := reserved.push (hb.base, hb.len)
            break
  for g0 in gs do
    let g ← instantiateMVars g0
    if g.isMVar then continue
    let some gb ← blockOf? g | continue
    let curAtoms := atoms curP
    let mut alreadyPresent := false
    for ha in curAtoms do
      if let some hb ← blockOf? ha then
        if hb.base == gb.base && hb.len == gb.len then
          alreadyPresent := true
          reserved := reserved.push (hb.base, hb.len)
          break
    if alreadyPresent then continue
    for hi : i in [:curAtoms.size] do
      let a := curAtoms[i]
      if a.isAppOfArity ``memRegion 2 then
        let p := a.getArg! 0
        let nExpr := a.getArg! 1
        if reserved.any (fun (rb, rl) => rb == p && rl == nExpr) then continue
        if let some (rhs, eqPrf) ← splitMemRegionSubblock? (liftTacDisch disch) p nExpr gb.base gb.len then
          if let some (curP', hEqTree) ← rewriteAtomAtEq? curP i rhs eqPrf then
            cur := mkAppN (mkConst ``Satisfies.congr_prop) #[m, curP, curP', hEqTree, cur]
            curP := curP'
            reserved := reserved.push (gb.base, gb.len)
            break
  return (curP, cur)

/-- Pre-split any `memRegion p n` atoms in `Gs` when hypothesis atoms in `P` start at `p` with
    smaller width `w < n` (so a goal `memRegion p n` absorbs contiguous `↦₈` / `↦₆₄` / `memRegion` slices). -/
def preSplitGoalMemRegions {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (P Gs : Expr) (hGs? : Option Expr) :
    M (Expr × Option Expr) := do
  unless (atoms Gs).any (·.isAppOfArity ``memRegion 2) do return (Gs, hGs?)
  let hypAtoms := atoms P
  let mut curGs := Gs
  let mut curHGs? := hGs?
  for _ in [0:32] do
    let gs := atoms curGs
    let mut splitDone := false
    for hi : i in [:gs.size] do
      let g := gs[i]
      if g.isAppOfArity ``memRegion 2 && !(hypAtoms.any (· == g)) then
        let p := g.getArg! 0
        let nExpr := g.getArg! 1
        for ha in hypAtoms do
          if let some hb ← (blockOf? ha : MetaM (Option Block)) then
            if (← (constAddrOffset? p hb.base : MetaM (Option Nat))) == some 0 && hb.len != nExpr then
              if let some (rhs, eqPrf) ← splitMemRegionSubblock? disch p nExpr p hb.len then
                if let some (gs', hTree) ← (rewriteAtomAtEq? curGs i rhs eqPrf : MetaM (Option (Expr × Expr))) then
                  curGs := gs'
                  curHGs? ← match curHGs? with
                    | some prev => pure (some (← (mkEqTrans prev hTree : MetaM Expr)))
                    | none => pure (some hTree)
                  splitDone := true
                  break
      if splitDone then break
    if !splitDone then break
  return (curGs, curHGs?)

/-- Core engine for `entail?`, optionally splitting unmatched `memRegion` blocks when `splitRegions` is `true`. -/
def entailCore? (disch : Disch) (m P h G : Expr) (splitRegions : Bool) : TacticM (Option Expr) := do
  let P0 := (← instantiateMVars P).consumeMData
  let G0 := (← instantiateMVars G).consumeMData
  let (P', hP?) ← normSepPropMeta P0
  let h0 ← match hP? with
    | some hP => pure (mkAppN (mkConst ``Satisfies.congr_prop) #[m, P0, P', ← instantiateMVars hP, h])
    | none => pure h
  let pures ← IO.mkRef #[]
  let (Gs0, k) ← expandGoal m G0 pures
  let (Gs1, hGs1?) ← normSepPropMeta Gs0
  let (P, h, Gs, hGs?) ←
    if splitRegions then
      let d := liftTacDisch disch
      let (P1, hP1?) ← unfoldUnmatchedSepUnfoldAtoms P' none Gs1
      let (Gs2, hGs2?) ← unfoldUnmatchedSepUnfoldAtoms Gs1 hGs1? P1
      let (P2, hP2?) ← expandUnmatchedStackFrameAtoms d P1 hP1? Gs2
      let (Gs3, hGs3?) ← expandUnmatchedStackFrameAtoms d Gs2 hGs2? P2
      let h2 ← match hP2? with
        | some hP2 => pure (mkAppN (mkConst ``Satisfies.congr_prop) #[m, P', P2, ← instantiateMVars hP2, h0])
        | none => pure h0
      let (P3, h3) ← preSplitHypMemRegions disch m P2 h2 Gs3
      let (P4, hP4?) ← preSplitPointsToBytes d P3 none Gs3
      let (P5, hP5?) ← preCongrNearMissAtoms d P4 hP4? Gs3
      let h5 ← match hP5? with
        | some hP5 => pure (mkAppN (mkConst ``Satisfies.congr_prop) #[m, P3, P5, ← instantiateMVars hP5, h3])
        | none => pure h3
      let (Gs4, hGs4?) ← preSplitGoalMemRegions d P5 Gs3 hGs3?
      pure (P5, h5, Gs4, hGs4?)
    else
      pure (P', h0, Gs1, hGs1?)
  if splitRegions && P == P' && Gs == Gs1 then return none
  let hyp := atoms (← instantiateMVars P)
  let goal := atoms (← instantiateMVars Gs)
  let mut nonMVarCount := 0
  for g0 in goal do
    let g ← instantiateMVars g0
    if !g.isMVar then nonMVarCount := nonMVarCount + 1
  if nonMVarCount > hyp.size then return none
  let mut used := Array.replicate hyp.size false
  let mut matched : Array (Option (Nat × Step)) := Array.replicate goal.size none
  let mut frame? : Option Expr := none
  let mut hypBlocks : Array (Option (Option Block)) := Array.replicate hyp.size none
  for hg : kIdx in [:goal.size] do
    let g ← instantiateMVars goal[kIdx]
    if g.isMVar then
      if frame?.isSome then return none
      frame? := some g
      continue
    let mut found : Option (Nat × Step) := none
    for hi : i in [:hyp.size] do
      if found.isNone && !used[i]! && hyp[i] == g then found := some (i, .same)
    if found.isNone then
      for hi : i in [:hyp.size] do
        if found.isNone && !used[i]! && hyp[i].getAppFn == g.getAppFn then
          if ← withReducibleAndInstances (isDefEq hyp[i] g) then found := some (i, .same)
    if found.isNone then
      for hi : i in [:hyp.size] do
        if found.isNone && !used[i]! && hyp[i].getAppFn != g.getAppFn &&
           !hyp[i].getAppFn.isFVar && !g.getAppFn.isFVar &&
           !hyp[i].getAppFn.isMVar && !g.getAppFn.isMVar &&
           !(isPrimSepAtom hyp[i] && isPrimSepAtom g) then
          if ← withReducibleAndInstances (isDefEq hyp[i] g) then found := some (i, .same)
    if let some (i, step) := found then
      used := used.set! i true
      matched := matched.set! kIdx (some (i, step))
  let mut plan : Array (Nat × Expr × Step) := #[]
  for hg : kIdx in [:goal.size] do
    let g ← instantiateMVars goal[kIdx]
    if g.isMVar then continue
    if let some (i, step) := matched[kIdx]! then
      plan := plan.push (i, g, step)
      continue
    let mut found : Option (Nat × Step) := none
    if let some gb ← blockOf? g then
      for hi : i in [:hyp.size] do
        if found.isNone && !used[i]! then
          if hypBlocks[i]!.isNone then
            hypBlocks := hypBlocks.set! i (some (← blockOf? hyp[i]))
          if let some (some hb) := hypBlocks[i]! then
            if ← withReducibleAndInstances (isDefEq hb.base gb.base) then
              if let some e ← congrAtoms? disch hyp[i] g then
                found := some (i, .congr e)
              else if let some hle ← proveLenLe? gb.len hb.len then
                if let some hΦ ← proveConj disch (gb.at m) then
                  let hbIsBlock ← instantiateMVars hb.isBlock
                  let gbIsBlock ← instantiateMVars gb.isBlock
                  found := some (i, .update hbIsBlock gbIsBlock hle hΦ hb.base hb.len)
      if found.isNone && !gb.base.hasMVar then
        for hi : i in [:hyp.size] do
          if found.isNone && !used[i]! && hyp[i].getAppFn == g.getAppFn then
            if let some (some hb) := hypBlocks[i]! then
              if !hb.base.hasMVar then
                let eqBase ← mkEq hb.base gb.base
                if (← withoutModifyingState (disch eqBase)).isSome then
                  if let some e ← congrAtoms? disch hyp[i] g then
                    found := some (i, .congr e)
    if found.isNone then
      for hi : i in [:hyp.size] do
        if found.isNone && !used[i]! && hyp[i].getAppFn == g.getAppFn then
          if let some e ← congrAtoms? disch hyp[i] g then
            found := some (i, .congr e)
    let some (i, step) := found | return none
    used := used.set! i true
    plan := plan.push (i, ← instantiateMVars g, step)
  let mut cur := h
  let mut curP ← instantiateMVars P
  for (i, g, step) in plan do
    match step with
    | .same => pure ()
    | .congr e =>
      let some j := (atoms curP).findIdx? (· == hyp[i]!) | return none
      let (rest, p) ← focus m curP cur j
      cur := mkAppN (mkConst ``Satisfies.head_congr) #[m, hyp[i]!, g, rest, e, p]
      curP := mkSep g rest
    | .update hb hb' hle hΦ base len =>
      let some j := (atoms curP).findIdx? (· == hyp[i]!) | return none
      let (rest, p) ← focus m curP cur j
      let hag := mkAppN (mkConst ``AgreesOutside.rfl') #[m, base, len]
      cur ← mkUpdate hb hb' hle p hag hΦ
      curP := mkSep g rest
  let leftovers := (hyp.zip used).filterMap fun (a, u) => if u then none else some a
  curP ← instantiateMVars curP
  let Gs ← instantiateMVars Gs
  let spatial ← match frame? with
    | some f =>
      unless ← isDefEq f (mkSepList leftovers) do return none
      satAC? m (← instantiateMVars curP) (← instantiateMVars Gs) cur
    | none =>
      if leftovers.isEmpty then satAC? m curP Gs cur
      else
        let some p ← satAC? m curP (mkSep Gs (mkSepList leftovers)) cur | return none
        pure (some (mkAppN (mkConst ``Satisfies.of_sep_left) #[m, Gs, mkSepList leftovers, p]))
  let some spatial := spatial | return none
  let spatial ← match hGs? with
    | some hGs =>
      let hGsSymm ← mkEqSymm (← instantiateMVars hGs)
      let Gs0Inst ← instantiateMVars Gs0
      let GsInst ← instantiateMVars Gs
      pure (mkAppN (mkConst ``Satisfies.congr_prop) #[m, GsInst, Gs0Inst, hGsSymm, spatial])
    | none => pure spatial
  for (hφ, φ) in ← pures.get do
    let some p ← proveConj disch φ | return none
    hφ.mvarId!.assign p
  instantiateMVars (← k spatial)

/-- Given `h : m ⊨ P`, prove `m ⊨ G`, or return `none`. -/
def entail? (disch : Disch) (m P h G : Expr) : TacticM (Option Expr) := do
  let savedMCtx ← getMCtx
  if let some prf ← entailCore? disch m P h G false then
    return some prf
  setMCtx savedMCtx
  entailCore? disch m P h G true

/-- Split a proof of a content predicate into proofs of its equational conjuncts; a 128-bit read
    `m.read128 a = v` also yields its two 64-bit halves. -/
partial def splitFacts (φ prf : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  if φ.isAppOfArity ``And 2 then
    let acc ← splitFacts (φ.getArg! 0) (mkApp3 (mkConst ``And.left) (φ.getArg! 0) (φ.getArg! 1) prf) acc
    splitFacts (φ.getArg! 1) (mkApp3 (mkConst ``And.right) (φ.getArg! 0) (φ.getArg! 1) prf) acc
  else if φ.isAppOfArity ``Eq 3 then
    let acc := acc.push prf
    if (φ.getArg! 1).isAppOfArity ``Memory.read128 2 then
      let lohi ← mkAppM ``read64_lo_hi_of_read128 #[prf]
      return (acc.push (← mkAppM ``And.left #[lohi])).push (← mkAppM ``And.right #[lohi])
    return acc
  else
    return acc

/-- If `atom` is a read-only points-to atom `a ↦_wᵣ v`, return `(IsBlockRO.pointsTo*RO a v, Φ m)`
    so `sep_facts` extracts its read equality too. -/
def roBlockReadAt? (atom m : Expr) : MetaM (Option (Expr × Expr)) := do
  let atom := stripMData (← instantiateMVars atom)
  if atom.isAppOfArity ``pointsTo8RO 2 then
    let a := atom.getArg! 0; let v := atom.getArg! 1
    return some (mkApp2 (mkConst ``IsBlockRO.pointsTo8RO) a v, ← mkEq (mkApp2 (mkConst ``Memory.read8) m a) v)
  if atom.isAppOfArity ``pointsTo16RO 2 then
    let a := atom.getArg! 0; let v := atom.getArg! 1
    return some (mkApp2 (mkConst ``IsBlockRO.pointsTo16RO) a v, ← mkEq (mkApp2 (mkConst ``Memory.read16) m a) v)
  if atom.isAppOfArity ``pointsTo32RO 2 then
    let a := atom.getArg! 0; let v := atom.getArg! 1
    return some (mkApp2 (mkConst ``IsBlockRO.pointsTo32RO) a v, ← mkEq (mkApp2 (mkConst ``Memory.read32) m a) v)
  if atom.isAppOfArity ``pointsTo64RO 2 then
    let a := atom.getArg! 0; let v := atom.getArg! 1
    return some (mkApp2 (mkConst ``IsBlockRO.pointsTo64RO) a v, ← mkEq (mkApp2 (mkConst ``Memory.read64) m a) v)
  if atom.isAppOfArity ``pointsTo128RO 2 then
    let a := atom.getArg! 0; let v := atom.getArg! 1
    return some (mkApp2 (mkConst ``IsBlockRO.pointsTo128RO) a v, ← mkEq (mkApp2 (mkConst ``Memory.read128) m a) v)
  return none

/-- Given `h : m ⊨ P`, the content predicates `Φ m` of all block atoms of `P` (split into
    equational conjuncts), and (if `disj`) the pairwise disjointness of positive-length literal
    blocks. -/
def blockFacts (m P h : Expr) (disj : Bool := true) : MetaM (Array Expr × Array Expr) := do
  let P ← instantiateMVars P
  let as := atoms P
  let mut reads : Array Expr := #[]
  let mut blocks : Array (Nat × Block) := #[]
  for hi : i in [:as.size] do
    if let some blk ← blockOf? as[i] then
      blocks := blocks.push (i, blk)
      let φ := blk.at m
      if φ.isConstOf ``True then continue
      let (_, p) ← focus m P h i
      let fact ← mkExpectedTypeHint (← mkAppM ``IsBlock.read #[blk.isBlock, p]) φ
      reads ← splitFacts φ fact reads
    else if let some (ibRO, φ) ← roBlockReadAt? as[i] m then
      let (_, p) ← focus m P h i
      let fact ← mkExpectedTypeHint (← mkAppM ``IsBlockRO.read #[ibRO, p]) φ
      reads ← splitFacts φ fact reads
  let mut disjs : Array Expr := #[]
  unless disj do return (reads, disjs)
  for h₁ : x in [:blocks.size] do
    for h₂ : y in [x + 1:blocks.size] do
      let (i, b₁) := blocks[x]
      let (j, b₂) := blocks[y]
      let (some n₁, some n₂) := (b₁.len.nat?, b₂.len.nat?) | continue
      if n₁ == 0 || n₂ == 0 then continue
      let others := (as.mapIdx fun k a => (k, a)).filterMap fun (k, a) =>
        if k == i || k == j then none else some a
      let target := mkSep as[i]! (mkSep as[j]! (mkSepList others))
      let some p ← satAC? m P target h | continue
      let pos₁ ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, b₁.len])
      let pos₂ ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, b₂.len])
      disjs := disjs.push (← mkAppM ``IsBlock.disjoint #[b₁.isBlock, b₂.isBlock, pos₁, pos₂, p])
  return (reads, disjs)

/-! ## Stores -/

/-- Width in bytes and exact-width store lemma for a `Memory.write*` function. -/
def writeInfo? (wName : Name) : Option (Nat × Name) :=
  if wName == ``Memory.write8 then some (1, ``IsBlock.write8)
  else if wName == ``Memory.write16 then some (2, ``IsBlock.write16)
  else if wName == ``Memory.write32 then some (4, ``IsBlock.write32)
  else if wName == ``Memory.write64 then some (8, ``IsBlock.write64)
  else if wName == ``Memory.write128 then some (16, ``IsBlock.write128)
  else none

/-- Peel `Memory.write*` and `Memory.mapZero` applications off `m`: `(writes, base)` with the
    oldest write first; each write is `(function, memory after the write, address, value)` (for
    `mapZero`, the "value" is the length). -/
partial def peelWrites (m : Expr) : Array (Name × Expr × Expr × Expr) × Expr :=
  let m := m.consumeMData
  match m.getAppFn.constName? with
  | some fn =>
    if ((writeInfo? fn).isSome || fn == ``Memory.mapZero) && m.getAppNumArgs == 3 then
      let (rest, base) := peelWrites (m.getArg! 0)
      (rest.push (fn, m, m.getArg! 1, m.getArg! 2), base)
    else (#[], m)
  | none => (#[], m)

/-- Prove `m.canMap base len = true` from a local hypothesis `m₀.canMap base' len' = true`
    where `m` is obtained from `m₀` by `Memory.write*` stores (which leave `canMap` unchanged). -/
partial def proveCanMap? (m base len : Expr) : MetaM (Option Expr) := do
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.true && lhs.isAppOfArity ``Memory.canMap 3 do continue
    unless ← withReducible (isDefEq (lhs.getArg! 0) m) do continue
    unless ← withReducible (isDefEq (lhs.getArg! 1) base) do continue
    unless ← withReducible (isDefEq (lhs.getArg! 2) len) do continue
    return some decl.toExpr
  let m := m.consumeMData
  let some fn := m.getAppFn.constName? | return none
  unless (writeInfo? fn).isSome && m.getAppNumArgs == 3 do return none
  let mPrev := m.getArg! 0
  let some pPrev ← proveCanMap? mPrev base len | return none
  let lem := match fn with
    | ``Memory.write8 => ``Memory.canMap_write8
    | ``Memory.write16 => ``Memory.canMap_write16
    | ``Memory.write32 => ``Memory.canMap_write32
    | ``Memory.write64 => ``Memory.canMap_write64
    | _ => ``Memory.canMap_write128
  let eqStep ← mkAppM lem #[mPrev, m.getArg! 1, m.getArg! 2, base, len]
  return some (← mkEqTrans eqStep pPrev)

/-- Extends `hag : AgreesOutside mStart mPrev base len` across one store (proving its bounds). -/
abbrev StepAgrees :=
  (mStart mPrev base len hag : Expr) → (wName : Name) → (wAddr wVal : Expr) → TacticM (Option Expr)

/-- Given `h : m ⊨ P` and the stores `writes` (oldest first) leading from `m` to some memory,
    step through the first store (batching subsequent stores into the same block); returns the
    number of stores consumed and the new `(memory, assertion, proof)`. A `mapZero a n` with
    `m.canMap a n = true` adds a new `memRegion a n` atom (`Satisfies.mapZero`). -/
def stepWrite? (stepAg : StepAgrees) (m P h : Expr) (writes : Array (Name × Expr × Expr × Expr))
    (start : Nat) : TacticM (Option (Nat × Expr × Expr × Expr)) := do
  let (wName, mNext, wAddr, wVal) := writes[start]!
  let P ← instantiateMVars P
  let as := atoms P
  if wName == ``Memory.mapZero then
    let some hmap ← proveCanMap? m wAddr wVal | return none
    let prf ← mkAppM ``Satisfies.mapZero #[h, hmap]
    let P' := mkSep (mkApp2 (mkConst ``memRegion) wAddr wVal) P
    return some (1, mNext, P', ← mkExpectedTypeHint prf (mkSat P' mNext))
  let some (wBytes, writeLemma) := writeInfo? wName | return none
  for hi : i in [:as.size] do
    if let some blk ← blockOf? as[i] then
      if blk.len.nat? == some wBytes then
        if ← withReducibleAndInstances (isDefEq blk.base wAddr) then
          let (_, p) ← focus m P h i
          let prf ← mkAppM writeLemma #[blk.isBlock, p, wVal]
          let P' := (← instantiateMVars (← inferType prf)).getArg! 0
          return some (1, mNext, P', ← mkExpectedTypeHint prf (mkSat P' mNext))
  for hi : i in [:as.size] do
    let some blk ← blockOf? as[i] | continue
    let hag0 := mkAppN (mkConst ``AgreesOutside.rfl') #[m, blk.base, blk.len]
    let some hag1 ← stepAg m m blk.base blk.len hag0 wName wAddr wVal | continue
    let mut hag := hag1
    let mut batchMem := mNext
    let mut j := start + 1
    while j < writes.size do
      let (wNameJ, mNextJ, wAddrJ, wValJ) := writes[j]!
      if wNameJ == ``Memory.mapZero then break
      let some hagNext ← stepAg m batchMem blk.base blk.len hag wNameJ wAddrJ wValJ | break
      hag := hagNext
      batchMem := mNextJ
      j := j + 1
    let (rest, p) ← focus m P h i
    -- Keep the atom if its contents are unconstrained, else weaken it to `memRegion`.
    let (tgt, tgtBlk) :=
      if (blk.at batchMem).isConstOf ``True then (as[i], blk.isBlock)
      else (mkApp2 (mkConst ``memRegion) blk.base blk.len,
        mkApp2 (mkConst ``IsBlock.memRegion) blk.base blk.len)
    let prf ← mkUpdate blk.isBlock tgtBlk (mkApp (mkConst ``Nat.le_refl) blk.len) p hag
      (mkConst ``True.intro)
    return some (j - start, batchMem, mkSep tgt rest, prf)
  return none

/-! ## Frame splitting and error diagnostics -/

/-- True if `n` is a fixed-width points-to cell constructor (`↦₈`..`↦₁₂₈` or read-only). -/
def isPointsToCellConst (n : Name) : Bool :=
  n == ``pointsTo8 || n == ``pointsTo16 || n == ``pointsTo32 ||
  n == ``pointsTo64 || n == ``pointsTo128 ||
  n == ``pointsTo8RO || n == ``pointsTo16RO || n == ``pointsTo32RO ||
  n == ``pointsTo64RO || n == ``pointsTo128RO

/-- If `e` is a points-to atom (`addr ↦_w v`, `∃∗ v, addr ↦_w v`, `addr ↦ₛ bs`, `addr ↦ᵣ bs`,
    `addr ↦₆₄* ws`, `pointsToArray`), return `(isFixedWidthCell, headName, addr)`. -/
def pointsToAtomInfo? (e : Expr) : Option (Bool × Name × Expr) :=
  let e := (stripMData e).headBeta
  if e.isAppOfArity ``SepProp.sepExists 2 then
    match (e.getArg! 1).consumeMData with
    | .lam _ _ body _ =>
      let body := (stripMData body).headBeta
      let fn := body.getAppFn.constName?.getD .anonymous
      if isPointsToCellConst fn && body.getAppNumArgs >= 2 && !(body.getArg! 0).hasLooseBVars then
        some (true, fn, body.getArg! 0)
      else none
    | _ => none
  else
    let fn := e.getAppFn.constName?.getD .anonymous
    if isPointsToCellConst fn && e.getAppNumArgs >= 2 then
      some (true, fn, e.getArg! 0)
    else if (fn == ``pointsToBytes || fn == ``pointsToBytesRO ||
             fn == ``pointsToWords64 || fn == ``pointsToWords64RO) && e.getAppNumArgs >= 2 then
      some (false, fn, e.getArg! 0)
    else if fn == `ProofLib.pointsToArray && e.getAppNumArgs >= 4 then
      some (false, fn, e.getArg! 3)
    else none

/-- If `e` is a region or slice container atom (`b ↦ₛ bs`, `b ↦ᵣ bs`, `b ↦₆₄* ws`, `memRegion b len`,
    `stackFrameAt b len`, etc.), return its base address expression. -/
def containerAtomAddr? (e : Expr) : Option Expr :=
  let e := (stripMData e).headBeta
  let fn := e.getAppFn.constName?.getD .anonymous
  if (fn == ``pointsToBytes || fn == ``pointsToBytesRO ||
      fn == ``pointsToWords64 || fn == ``pointsToWords64RO ||
      fn == ``memRegion || fn == ``regionBlock || fn == ``regionBlockRO ||
      fn == ``stackFrameAt || fn == ``stackFrame16At || fn == ``stackFrame32At ||
      fn == ``stackFrameSlotsFrom || fn == ``stackFrameSlotsCont ||
      fn == `ProofLib.memRegionPartition) && e.getAppNumArgs >= 1 then
    some (e.getArg! 0)
  else if (fn == ``stackFrame || fn == ``stackFrame16 || fn == ``stackFrame32) && e.getAppNumArgs >= 1 then
    some (mkApp (mkConst ``State.sp) (e.getArg! 0))
  else if fn == `ProofLib.pointsToArray && e.getAppNumArgs >= 4 then
    some (e.getArg! 3)
  else none

/-- Extract the address or base expression of any primitive spatial atom (`pointsTo*`, `memRegion`,
    `stackFrame*`, `regionBlock*`, `pointsToArray`). -/
def spatialAtomAddr? (e : Expr) : Option Expr :=
  match pointsToAtomInfo? e with
  | some (_, _, addr) => some addr
  | none => containerAtomAddr? e

/-- True if `n` is a built-in primitive or connective `SepProp` head. -/
def isBuiltinSepHead (n : Name) : Bool :=
  isPointsToCellConst n ||
  n == ``pointsToBytes || n == ``pointsToBytesRO ||
  n == ``pointsToWords64 || n == ``pointsToWords64RO ||
  n == ``regionBlock || n == ``regionBlockRO || n == ``memRegion ||
  n == ``stackFrame || n == ``stackFrame16 || n == ``stackFrame32 ||
  n == ``stackFrame16At || n == ``stackFrame32At || n == ``stackFrameAt ||
  n == ``stackFrameSlotsCont || n == ``stackFrameSlotsFrom || n == ``stackFrameFor ||
  n == `ProofLib.pointsToArray ||
  n == `ProofLib.memRegionPartition || n == `ProofLib.memRegionPartitionAt ||
  n == `ProofLib.stackAt ||
  n == ``SepProp.emp || n == ``SepProp.pure || n == ``SepProp.sepExists ||
  n == ``SepProp.sepConj || n == ``SepProp.sepImp

/-- Return `some headName` when `e` has a non-primitive constant `SepProp` head. -/
def compositeSepHead? (e : Expr) : Option Name :=
  let e := (stripMData e).headBeta
  match e.getAppFn.constName? with
  | some n => if isBuiltinSepHead n then none else some n
  | none => none

/-- Normalize an address expression `addr` and decompose into `(normAddr, normBase, signedOffset)`
    for diagnostic near-miss classification (never throws). -/
def normAddrAndBaseDiag (addr : Expr) : MetaM (Expr × Expr × Int) := do
  try
    let a1 ← unfoldLetFVars addr
    let (a2, _) ← normAddrMeta a1 8
    let (base, off) ← splitBaseOff a2
    let b1 ← unfoldLetFVars base
    let (b2, _) ← normAddrMeta b1 8
    return (a2, b2, off)
  catch _ =>
    return (addr, addr, 0)

private partial def collectUnprovedLeafEqs (t c : Expr) (fuel : Nat := 4) :
    MetaM (Array (Expr × Expr)) := do
  let t := stripMData (← instantiateMVars t)
  let c := stripMData (← instantiateMVars c)
  if t == c then return #[]
  if ← withReducibleAndInstances (isDefEq t c) then return #[]
  if !t.hasMVar && !c.hasMVar then
    if (← proveNearMissEq? (← mkEq t c)).isSome then return #[]
  if fuel > 0 && t.getAppFn == c.getAppFn && t.getAppFn.isConst && t.getAppNumArgs == c.getAppNumArgs then
    let mut acc : Array (Expr × Expr) := #[]
    for ti in t.getAppArgs, ci in c.getAppArgs do
      acc := acc ++ (← collectUnprovedLeafEqs ti ci (fuel - 1))
    return acc
  if t.hasMVar || c.hasMVar then return #[]
  return #[(t, c)]

private def sharesNonAddrStructure (t c : Expr) : Bool :=
  if t.getAppNumArgs < 2 || c.getAppNumArgs < 2 then true
  else
    let ta := stripMData (t.getArg! 1)
    let ca := stripMData (c.getArg! 1)
    ta == ca || (ta.getAppFn.isConst && ta.getAppFn == ca.getAppFn)

/-- Diagnose near-misses, region/slice containers at the same base, and composite-vs-raw
    abstraction mismatches between an unmatched target atom `t` and candidate context atoms.
    Wrapped in `try ... catch` so diagnostic formatting never fails. -/
def explainAtomMismatchHints (t : Expr) (candidates : Array Expr)
    (allCtxAtoms : Array Expr := candidates) : MetaM (Array MessageData) := withoutModifyingState do
  try
    let t := (stripMData (← instantiateMVars t)).headBeta
    let pool := if candidates.isEmpty then allCtxAtoms else candidates
    let mut lines : Array MessageData := #[]
    let mut nearMissAtoms : Array Expr := #[]
    if let some (tIsCell, _, addrT) := pointsToAtomInfo? t then
      let (normAddrT, normBaseT, offT) ← normAddrAndBaseDiag addrT
      for c0 in pool do
        let c := (stripMData c0).headBeta
        if let some (cIsCell, _, addrC) := pointsToAtomInfo? c then
          if tIsCell && cIsCell then
            let (normAddrC, normBaseC, offC) ← normAddrAndBaseDiag addrC
            if normAddrT == normAddrC || (normBaseT == normBaseC && offT == offC) then
              if !nearMissAtoms.contains c && nearMissAtoms.size < 3 then
                nearMissAtoms := nearMissAtoms.push c
      if !nearMissAtoms.isEmpty then
        let nearMsg := MessageData.joinSep (nearMissAtoms.toList.map (fun a => m!"`{a}`")) m!", "
        lines := lines.push
          m!"  near-miss at same address: target expects `{t}`, but context has {nearMsg} (prove the values equal with `rw`/`simp` before matching, or split/coalesce cell widths)"
    if nearMissAtoms.isEmpty && t.getAppFn.isConst && isPrimSepAtom t && t.getAppNumArgs >= 1 then
      let addrT := t.getArg! 0
      let addrTLet ← unfoldLetFVars addrT
      let (_, normBaseT, _) ← normAddrAndBaseDiag addrT
      let sameHeadPool := pool.map (fun x => (stripMData x).headBeta) |>.filter fun c =>
        c.getAppFn == t.getAppFn && c.getAppNumArgs == t.getAppNumArgs
      let mut bestCand? : Option Expr := none
      for preferValMatch in [true, false] do
        if bestCand?.isSome then break
        for c in sameHeadPool do
          let addrC := c.getArg! 0
          let addrCLet ← unfoldLetFVars addrC
          if (← ProofLib.BV.Lin.proveNe? addrTLet addrCLet).isSome then continue
          let (_, normBaseC, _) ← normAddrAndBaseDiag addrC
          if normBaseT == normBaseC || !addrTLet.isFVar || !addrCLet.isFVar then
            if !preferValMatch || sharesNonAddrStructure t c then
              bestCand? := some c
              break
      if let some c := bestCand? then
        let remEqs ← collectUnprovedLeafEqs t c
        if !remEqs.isEmpty then
          nearMissAtoms := nearMissAtoms.push c
          let remMsg := MessageData.joinSep
            (remEqs.toList.map fun (l, r) => m!"`{l} = {r}`") m!", "
          let (firstL, firstR) := remEqs[0]!
          lines := lines.push
            m!"  near-miss: target expects `{t}`, context has `{c}`; remaining equality: {remMsg}\n  hint: `have h : {firstL} = {firstR} := by bv_arith`"
    let mut containerAtoms : Array Expr := #[]
    if let some addrT := spatialAtomAddr? t then
      let (normAddrT, normBaseT, _) ← normAddrAndBaseDiag addrT
      for c0 in pool do
        let c := (stripMData c0).headBeta
        if !nearMissAtoms.contains c then
          if let some addrC := containerAtomAddr? c then
            let (normAddrC, normBaseC, _) ← normAddrAndBaseDiag addrC
            if normBaseT == normBaseC || normAddrT == normAddrC then
              if !containerAtoms.contains c && containerAtoms.size < 2 then
                containerAtoms := containerAtoms.push c
      if !containerAtoms.isEmpty then
        let contMsg := MessageData.joinSep (containerAtoms.toList.map (fun a => m!"`{a}`")) m!", "
        lines := lines.push
          m!"hint: context contains region/slice atom {contMsg} at the same base; carve or split the window with `pointsToBytes_focus` / `memRegion_split_le` / `stackFrameAt_split_close`"
    if let some headName := compositeSepHead? t then
      if allCtxAtoms.any (fun c => (spatialAtomAddr? c).isSome) ||
         !pool.any (fun c => c.getAppFn.constName? == some headName) then
        lines := lines.push
          m!"hint: target atom `{t}` uses composite definition `{headName}`; unfold or fold `{headName}` so both sides are at the same abstraction level"
    else if (spatialAtomAddr? t).isSome && nearMissAtoms.isEmpty && containerAtoms.isEmpty then
      for c0 in pool do
        let c := (stripMData c0).headBeta
        if let some headName := compositeSepHead? c then
          lines := lines.push
            m!"hint: context atom `{c}` uses composite definition `{headName}` while target atom `{t}` is a raw spatial atom; unfold or fold `{headName}` so both sides are at the same abstraction level"
          break
    return lines
  catch _ =>
    return #[]

/-- Format an actionable error message naming the unmatched atom(s) in `sub` and the remaining
    candidate atoms in `full` when `frameSplit?` or `closeSat` fails. -/
def explainFrameSplitFailure (sub full : Expr) : MetaM MessageData := withoutModifyingState do
  let (full', _) ← try normSepPropMeta full catch _ => pure (full, none)
  let (sub', _) ← try normSepPropMeta sub catch _ => pure (sub, none)
  let fs := atoms (← instantiateMVars full')
  let mut used := Array.replicate fs.size false
  let mut unmatched : Array Expr := #[]
  let mut subMVarAtoms : Array Expr := #[]
  for s0 in atoms (← instantiateMVars sub') do
    let s ← instantiateMVars s0
    if s.getAppFn.isMVar then
      subMVarAtoms := subMVarAtoms.push s
      continue
    let mut found : Option Nat := none
    for hi : i in [:fs.size] do
      if found.isNone && !used[i]! && fs[i] == s then found := some i
    for hi : i in [:fs.size] do
      if found.isNone && !used[i]! && fs[i].getAppFn == s.getAppFn then
        if ← withReducibleAndInstances (isDefEq fs[i] s) then found := some i
    for hi : i in [:fs.size] do
      if found.isNone && !used[i]! && fs[i].getAppFn != s.getAppFn &&
         !fs[i].getAppFn.isFVar && !s.getAppFn.isFVar &&
         !fs[i].getAppFn.isMVar && !s.getAppFn.isMVar &&
         !(isPrimSepAtom fs[i] && isPrimSepAtom s) then
        if ← withReducibleAndInstances (isDefEq fs[i] s) then found := some i
    if let some i := found then
      used := used.set! i true
    else
      unmatched := unmatched.push s
  let candidates := (fs.zip used).filterMap fun (a, u) => if u then none else some a
  let maxShown := 8
  let fmtList (xs : Array Expr) : MessageData :=
    let shown := MessageData.joinSep ((xs.extract 0 maxShown).toList.map toMessageData) m!", "
    if xs.size > maxShown then m!"{shown}, … (+{xs.size - maxShown} more)" else shown
  let candMsg := if candidates.isEmpty then m!"(none)" else fmtList candidates
  -- Unassigned metavariable atoms (`?m`, `?f x`) are never matched by `frameSplit?`.
  let fullMVarAtoms := candidates.filter (·.getAppFn.isMVar)
  let mvarHint : MessageData :=
    if subMVarAtoms.isEmpty && fullMVarAtoms.isEmpty then m!""
    else
      let subPart :=
        if subMVarAtoms.isEmpty then m!""
        else m!"\nhint: target contains unassigned metavariable atom(s) {fmtList subMVarAtoms}, which `frame_split` never matches against concrete atoms; instantiate them first (e.g. `refine`/`show` with an explicit frame, or `sep_focus` on a `P = Q ∗ ?F` equation, which assigns `?F` to the leftover atoms: {candMsg})"
      let fullPart :=
        if fullMVarAtoms.isEmpty then m!""
        else m!"\nhint: precondition contains unassigned metavariable atom(s) {fmtList fullMVarAtoms}; instantiate them (e.g. `refine`/`show` or by elaborating the hypothesis with explicit arguments) before framing"
      subPart ++ fullPart
  if let some first := unmatched[0]? then
    let typoHint :=
      if first.getAppFn.isFVar then
        m!" (note: `{first.getAppFn}` is a local variable — possible typo or auto-bound implicit)"
      else m!""
    let extraMsg :=
      if unmatched.size > 1 then
        m!" (also unmatched: {fmtList (unmatched.extract 1 unmatched.size)})"
      else m!""
    let diagLines ← explainAtomMismatchHints first candidates fs
    if diagLines.isEmpty then
      return m!"frame_split: no match for {first}{typoHint} in precondition{extraMsg}; candidates: {candMsg}{mvarHint}"
    else
      let diagMsg := MessageData.joinSep diagLines.toList m!"\n"
      return m!"frame_split: no match for {first}{typoHint} in precondition{extraMsg}\n{diagMsg}\ncandidates: {candMsg}{mvarHint}"
  else if !subMVarAtoms.isEmpty then
    return m!"frame_split: all concrete atoms matched, but the target still contains unassigned metavariable atom(s) {fmtList subMVarAtoms}; remaining precondition atoms: {candMsg}{mvarHint}"
  else
    return m!"frame_split: no match for {sub'} in precondition; candidates: {candMsg}{mvarHint}"

/-- If `s` is `memRegion q w` or `∃∗ v, q ↦_w v`, return `(q, wExpr, Option (memRegion q w = s))`. -/
def memRegionOrExistsCellInfo? (s : Expr) : MetaM (Option (Expr × Expr × Option Expr)) := do
  if s.isAppOfArity ``memRegion 2 then
    return some (s.getArg! 0, s.getArg! 1, none)
  if s.isAppOfArity ``SepProp.sepExists 2 then
    let lam := (s.getArg! 1).consumeMData
    if let .lam _ _ body _ := lam then
      if body.hasLooseBVars && !(body.getArg! 0).hasLooseBVars then
        let q := body.getArg! 0
        let fn := body.getAppFn.constName?.getD .anonymous
        let info? : Option (Nat × Name) :=
          if fn == ``Arm64.pointsTo8 then some (1, ``memRegion_one)
          else if fn == ``Arm64.pointsTo16 then some (2, ``memRegion_two)
          else if fn == ``Arm64.pointsTo32 then some (4, ``memRegion_four)
          else if fn == ``Arm64.pointsTo64 then some (8, ``memRegion_eight)
          else if fn == ``Arm64.pointsTo128 then some (16, ``memRegion_sixteen)
          else none
        if let some (w, lem) := info? then
          return some (q, toExpr w, some (mkApp (mkConst lem) q))
  return none

/-- Pre-split any `memRegion p n` atoms in `full'` when `sub'` requests `memRegion q w` or
    `∃∗ v, q ↦_w v` inside `[p, p + n)`. -/
def preSplitFullMemRegions {M : Type → Type} [Monad M] [MonadLiftT MetaM M]
    (disch : Expr → M (Option Expr)) (full' : Expr) (hFull? : Option Expr) (sub' : Expr) :
    M (Expr × Option Expr) := do
  unless (atoms full').any (·.isAppOfArity ``memRegion 2) do return (full', hFull?)
  let mut curFull := full'
  let mut curHFull? := hFull?
  for s0 in atoms sub' do
    let s ← (instantiateMVars s0 : MetaM Expr)
    let fs := atoms curFull
    if fs.any (· == s) then continue
    let some (q, wExpr, toCellEq?) ← (memRegionOrExistsCellInfo? s : MetaM _) | continue
    for hi : i in [:fs.size] do
      let a := fs[i]
      if a.isAppOfArity ``memRegion 2 then
        let p := a.getArg! 0
        let nExpr := a.getArg! 1
        if let some (rhs0, eqPrf0) ← splitMemRegionSubblock? disch p nExpr q wExpr then
          let (rhs, eqPrf) ← match toCellEq? with
            | none => pure (rhs0, eqPrf0)
            | some hCell =>
              if let some (rhs1, hStep) ← (rewriteAtomAtEq? rhs0 0 s hCell : MetaM _) then
                pure (rhs1, ← (mkEqTrans eqPrf0 hStep : MetaM Expr))
              else
                pure (rhs0, eqPrf0)
          if let some (fullNext, hTree) ← (rewriteAtomAtEq? curFull i rhs eqPrf : MetaM _) then
            curFull := fullNext
            curHFull? ← match curHFull? with
              | some prev => pure (some (← (mkEqTrans prev hTree : MetaM Expr)))
              | none => pure (some hTree)
            break
  return (curFull, curHFull?)

/-- Core engine for `frameSplit?`, splitting `memRegion` atoms when `splitRegions` is `true`. -/
def frameSplitCore? (sub full : Expr) (splitRegions : Bool) : MetaM (Option (Expr × Expr)) := do
  let full0 ← instantiateMVars full
  let sub0 ← instantiateMVars sub
  let (full1, hFull1?) ← normSepPropMeta full0
  let (sub1, hSub1?) ← normSepPropMeta sub0
  let (full', hFull?, sub', hSub?) ←
    if splitRegions then
      let (full2, hFull2?) ← unfoldUnmatchedSepUnfoldAtoms full1 hFull1? sub1
      let (sub2, hSub2?) ← unfoldUnmatchedSepUnfoldAtoms sub1 hSub1? full2
      let (full3, hFull3?) ← expandUnmatchedStackFrameAtoms metaDisch full2 hFull2? sub2
      let (sub3, hSub3?) ← expandUnmatchedStackFrameAtoms metaDisch sub2 hSub2? full3
      let (full4, hFull4?) ← preSplitFullMemRegions metaDisch full3 hFull3? sub3
      let (full5, hFull5?) ← preSplitPointsToBytes metaDisch full4 hFull4? sub3
      let (full6, hFull6?) ← preCongrNearMissAtoms metaDisch full5 hFull5? sub3
      let (sub4, hSub4?) ← preSplitGoalMemRegions metaDisch full6 sub3 hSub3?
      pure (full6, hFull6?, sub4, hSub4?)
    else
      pure (full1, hFull1?, sub1, hSub1?)
  if splitRegions && full' == full1 && sub' == sub1 then return none
  let fs := atoms full'
  let mut used := Array.replicate fs.size false
  for s0 in atoms sub' do
    let s ← instantiateMVars s0
    let mut found : Option Nat := none
    for hi : i in [:fs.size] do
      if found.isNone && !used[i]! && fs[i] == s then found := some i
    for hi : i in [:fs.size] do
      if found.isNone && !used[i]! && fs[i].getAppFn == s.getAppFn then
        if ← withReducibleAndInstances (isDefEq fs[i] s) then found := some i
    for hi : i in [:fs.size] do
      if found.isNone && !used[i]! && fs[i].getAppFn != s.getAppFn &&
         !fs[i].getAppFn.isFVar && !s.getAppFn.isFVar &&
         !fs[i].getAppFn.isMVar && !s.getAppFn.isMVar &&
         !(isPrimSepAtom fs[i] && isPrimSepAtom s) then
        if ← withReducibleAndInstances (isDefEq fs[i] s) then found := some i
    let some i := found | return none
    used := used.set! i true
  let frame := mkSepList ((fs.zip used).filterMap fun (a, u) => if u then none else some a)
  let sub'Inst ← instantiateMVars sub'
  let target' := mkSep sub'Inst frame
  let some (tbl, tA, tB) ← reifyPermTbl? full' target' | return none
  let mut prf ← eqACOfTbl full' target' tbl tA tB
  if let some hFull := hFull? then
    prf ← mkEqTrans (← instantiateMVars hFull) prf
  if let some hSub := hSub? then
    let hSubSymm ← mkEqSymm (← instantiateMVars hSub)
    let hTargetEq ← mkCongrFun (← mkCongrArg (mkConst ``SepProp.sepConj) hSubSymm) frame
    prf ← mkEqTrans prf hTargetEq
  let finalTarget := mkSep (← instantiateMVars sub0) frame
  return some (frame, ← mkExpectedTypeHint prf (← mkEq (← instantiateMVars full0) finalTarget))

/-- Split `full = sub ∗ frame`: direct syntactic/reducible matching runs first with zero overhead;
    if unmatched atoms remain, any enclosing `memRegion p n` containing `[q, q + w)` is split out. -/
def frameSplit? (sub full : Expr) : MetaM (Option (Expr × Expr)) := do
  let savedMCtx ← getMCtx
  if let some res ← frameSplitCore? sub full false then
    return some res
  setMCtx savedMCtx
  frameSplitCore? sub full true

/-- True if `n` names a `SepWP` or `SepWPp` weakest-precondition predicate. -/
def isSepWPHeadName (n : Name) : Bool :=
  n == `ProofLib.SepWP || n == `ProofLib.SepWPp ||
  n.toString.endsWith "SepWP" || n.toString.endsWith "SepWPp"

/-- Concise human-readable description of the head constructor/binder of a goal `ty`. -/
def goalHeadDesc (ty : Expr) : String :=
  let ty := ty.consumeMData
  if ty.isForall then
    if ty.isArrow then "→" else "∀"
  else
    match ty.getAppFn.constName? with
    | some n => toString n
    | none =>
      if ty.getAppFn.isFVar then "local variable"
      else if ty.getAppFn.isMVar then "metavariable"
      else "expression"

/-- True if `ty` is a `∀`/implication telescope wrapping `Satisfies` (`m ⊨ P`) or `Entails` (`P ⊢ Q`). -/
def isForallSatOrEntails (ty : Expr) : Bool :=
  let rec go (e : Expr) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      let e := e.consumeMData
      if e.isAppOfArity ``SepProp.Satisfies 2 || e.isAppOfArity ``SepProp.Entails 2 then true
      else if let .forallE _ d b _ := e then
        d.consumeMData.isAppOfArity ``SepProp.Satisfies 2 || go b fuel
      else false
  ty.consumeMData.isForall && go ty 6

/-- Routing hint for `sep_focus` when the goal is not an equation. -/
def sepFocusGoalShapeHint (ty : Expr) : MessageData :=
  let ty := ty.consumeMData
  if ty.getAppFn.constName?.any isSepWPHeadName then
    m!"hint: `sep_focus` operates on `P = Q ∗ R` equations; to rewrite the `SepWP` precondition, use `wp_conv_pre => ...` or `rw [pointsToBytes_focus ...]`"
  else if ty.isAppOfArity ``SepProp.Entails 2 || ty.isAppOfArity ``SepProp.Satisfies 2 || isForallSatOrEntails ty then
    m!"hint: use `sep_entail` or `sep_frame` to discharge entailment/satisfaction goals"
  else
    m!"hint: `sep_focus` operates on `P = Q ∗ R` equations"

/-- Routing hint for `sep_entail` (`sep solver`) when the goal is not `m ⊨ P` or `P ⊢ Q`. -/
def sepSolverGoalShapeHint (ty : Expr) : MessageData :=
  let ty := ty.consumeMData
  if isForallSatOrEntails ty then
    m!"hint: run `intro m hm; sep_entail`"
  else if ty.getAppFn.constName?.any isSepWPHeadName then
    m!"hint: goal is a `SepWP` weakest precondition; use `wp_done` (at target PC) or `wp_steps`"
  else if ty.eq?.isSome then
    m!"hint: goal is an equation; use `sep_eq` or `sep_frame` for `SepProp` equalities (or `sep_focus` for `Full = Sub ∗ ?F`)"
  else if ty.getAppFn.constName? == some `ProofLib.SepFrame then
    m!"hint: use `wp_frame_split` or `sep_frame` to discharge `SepFrame` goals"
  else
    m!"hint: `sep_entail` expects a goal of the form `m ⊨ P` or `P ⊢ Q`"

/-! ## Tactic front end -/

/-- A discharger running tactic `tac` on the side goal (which must be closed completely). -/
def tacDisch (tac : TSyntax `tactic) : Disch := fun φ => do
  let mvar ← mkFreshExprMVar φ
  let saved ← getGoals
  setGoals [mvar.mvarId!]
  let ok ← tryTactic do
    evalTactic tac
    unless (← getGoals).isEmpty do throwError "unsolved side goal"
  setGoals saved
  if ok then return some (← instantiateMVars mvar) else return none

/-- The most recent hypothesis `h : m' ⊨ P` with `m'` reducibly defeq to `m`: `(h, P)`. Looks
    through `Memory.mapFresh` (`brk` / `mmap`), which preserves every assertion. -/
partial def findSatHyp? (m : Expr) : MetaM (Option (Expr × Expr)) := do
  let m := stripMData m
  for decl in (← getLCtx).decls.toList.reverse do
    let some decl := decl | continue
    if decl.isImplementationDetail then continue
    let ty := stripMData (← instantiateMVars decl.type)
    if ty.isAppOfArity ``SepProp.Satisfies 2 then
      if ← withReducibleAndInstances (isDefEq (ty.getArg! 1) m) then
        return some (decl.toExpr, ty.getArg! 0)
  if m.isAppOfArity ``Memory.mapFresh 4 then
    if let some (h, P) ← findSatHyp? (m.getArg! 0) then
      let prf := mkAppN (mkConst ``satisfies_mapFresh)
        #[P, m.getArg! 0, h, m.getArg! 1, m.getArg! 2, m.getArg! 3]
      return some (prf, P)
  return none

/-- Core engine for `closeEntails?`, splitting `memRegion` atoms when `splitRegions` is `true`. -/
partial def closeEntailsCore? (disch : Disch) (P Q : Expr) (splitRegions : Bool) : TacticM (Option Expr) := do
  let (P1, hP1?) ← normSepPropMeta P
  let (Q1, hQ1?) ← normSepPropMeta Q
  let (P2, hP?, Q2, hQ?) ←
    if splitRegions then
      let d := liftTacDisch disch
      let (Pa, hPa?) ← unfoldUnmatchedSepUnfoldAtoms P1 hP1? Q1
      let (Qa, hQa?) ← unfoldUnmatchedSepUnfoldAtoms Q1 hQ1? Pa
      let (Pb, hPb?) ← expandUnmatchedStackFrameAtoms d Pa hPa? Qa
      let (Qb, hQb?) ← expandUnmatchedStackFrameAtoms d Qa hQa? Pb
      let (Pc, hPc?) ← preSplitFullMemRegions d Pb hPb? Qb
      let (Pd, hPd?) ← preSplitPointsToBytes d Pc hPc? Qb
      let (Pe, hPe?) ← preCongrNearMissAtoms d Pd hPd? Qb
      let (Qc, hQc?) ← preSplitGoalMemRegions d Pe Qb hQb?
      pure (Pe, hPe?, Qc, hQc?)
    else
      pure (P1, hP1?, Q1, hQ1?)
  -- Weaken any points-to blocks in `P2` to `memRegion` when `Q2` has `memRegion` at that base/len
  let rec weakenToRegions (cur : Expr) : MetaM (Expr × Expr) := do
    let cb := cur.consumeMData.headBeta
    if cb.isAppOfArity ``SepProp.sepConj 2 then
      let (l', hl) ← weakenToRegions (cb.getArg! 0)
      let (r', hr) ← weakenToRegions (cb.getArg! 1)
      return (mkSep l' r', mkAppN (mkConst ``sepConj_mono) #[cb.getArg! 0, l', cb.getArg! 1, r', hl, hr])
    else
      let leaf := (stripMData cb).headBeta
      if !leaf.isAppOfArity ``memRegion 2 then
        if let some hb ← blockOf? leaf then
          let qAtoms := atoms Q2
          if qAtoms.any (fun ga => ga.isAppOfArity ``memRegion 2 && ga.getArg! 0 == hb.base && ga.getArg! 1 == hb.len) then
            let reg := mkApp2 (mkConst ``memRegion) hb.base hb.len
            let ent ← mkAppM ``IsBlock.entails_memRegion #[hb.isBlock]
            return (reg, ent)
      return (cur, mkApp (mkConst ``Entails.refl) cur)
  let (P3, hWeaken) ← if splitRegions then weakenToRegions P2 else pure (P2, mkApp (mkConst ``Entails.refl) P2)
  if splitRegions && P2 == P1 && Q2 == Q1 && P3 == P2 then return none
  let some (tbl, tA, tB) ← reifyPermTbl? P3 Q2 | return none
  let hAC ← eqACOfTbl P3 Q2 tbl tA tB
  let mut prf := mkAppN (mkConst ``Entails.trans)
    #[P2, P3, Q2, hWeaken, mkAppN (mkConst ``Entails.of_eq) #[P3, Q2, hAC]]
  if let some hP := hP? then
    prf := mkAppN (mkConst ``Entails.trans) #[P, P2, Q2, mkAppN (mkConst ``Entails.of_eq) #[P, P2, hP], prf]
  if let some hQ := hQ? then
    let hQSymm ← mkEqSymm hQ
    prf := mkAppN (mkConst ``Entails.trans) #[P, Q2, Q, prf, mkAppN (mkConst ``Entails.of_eq) #[Q2, Q, hQSymm]]
  return some prf

/-- Prove a heap-level entailment `P ⊢ Q`: tries zero-overhead AC normalization first, falling
    back to contiguous `memRegion` splitting and block weakening when needed. -/
partial def closeEntails? (disch : Disch) (P Q : Expr) : TacticM (Option Expr) := do
  let savedMCtx ← getMCtx
  if let some prf ← closeEntailsCore? disch P Q false then
    return some prf
  setMCtx savedMCtx
  closeEntailsCore? disch P Q true

/-- Format a residual multiset diff message when `sep_eq` fails to prove `lhs = rhs`. -/
def explainSepEqFailure (lhs rhs : Expr) : MetaM MessageData := withoutModifyingState do
  try
    let lhs0 ← instantiateMVars lhs
    let rhs0 ← instantiateMVars rhs
    let (lhs', _) ← try normSepPropMeta lhs0 catch _ => pure (lhs0, none)
    let (rhs', _) ← try normSepPropMeta rhs0 catch _ => pure (rhs0, none)
    let lhsAtoms := atoms (← instantiateMVars lhs')
    let rhsAtoms := atoms (← instantiateMVars rhs')
    let mut usedL := Array.replicate lhsAtoms.size false
    let mut usedR := Array.replicate rhsAtoms.size false
    for hi : i in [:lhsAtoms.size] do
      let a := lhsAtoms[i]
      for hj : j in [:rhsAtoms.size] do
        if !usedL[i]! && !usedR[j]! && a == rhsAtoms[j] then
          usedL := usedL.set! i true
          usedR := usedR.set! j true
    for hi : i in [:lhsAtoms.size] do
      if !usedL[i]! then
        let a := lhsAtoms[i]
        for hj : j in [:rhsAtoms.size] do
          if !usedL[i]! && !usedR[j]! && a.getAppFn == rhsAtoms[j].getAppFn then
            if ← withReducibleAndInstances (isDefEq a rhsAtoms[j]) then
              usedL := usedL.set! i true
              usedR := usedR.set! j true
    let lhsOnly := (lhsAtoms.zip usedL).filterMap fun (a, u) => if u then none else some a
    let rhsOnly := (rhsAtoms.zip usedR).filterMap fun (a, u) => if u then none else some a
    let fmtList (xs : Array Expr) : MessageData :=
      if xs.isEmpty then m!"(none)"
      else MessageData.joinSep (xs.toList.map (fun e => m!"`{e}`")) m!", "
    let hints ← match lhsOnly[0]? with
      | some firstL => explainAtomMismatchHints firstL rhsOnly rhsAtoms
      | none =>
        match rhsOnly[0]? with
        | some firstR => explainAtomMismatchHints firstR lhsOnly lhsAtoms
        | none => pure #[]
    let hintSuffix :=
      if hints.isEmpty then m!""
      else m!"\n" ++ MessageData.joinSep hints.toList m!"\n"
    return m!"sep_eq: atom multisets differ:\n  only in LHS: {fmtList lhsOnly}\n  only in RHS: {fmtList rhsOnly}\n  LHS: {fmtList lhsAtoms}\n  RHS: {fmtList rhsAtoms}{hintSuffix}"
  catch _ =>
    return m!"sep_eq: atom multisets differ:\n  LHS: {lhs}\n  RHS: {rhs}"

/-- Close the main goal `m ⊨ G` (or `P ⊢ Q`) from a hypothesis over the same memory using `entail?`. -/
partial def closeSat (disch : Disch) : TacticM Unit := do
  let g ← getMainGoal
  let ty0 ← g.withContext do pure (stripMData (← instantiateMVars (← g.getType)))
  if proofLib.sepShapeDispatch.get (← getOptions) && isForallSatOrEntails ty0 then
    let (_, g') ← g.intros
    replaceMainGoal [g']
    closeSat disch
    return
  g.withContext do
    let ty := stripMData (← instantiateMVars (← g.getType))
    let leaveOpen := proofLib.frameSplitLeaveSideGoals.get (← getOptions)
    if ty.isAppOfArity ``SepProp.Entails 2 then
      if let some prf ← closeEntails? disch (ty.getArg! 0) (ty.getArg! 1) then
        g.assign prf
        replaceMainGoal []
        return
      if leaveOpen then
        let openGoalsRef ← IO.mkRef (#[] : Array MVarId)
        let dischOpen : Disch := fun φ => do
          if let some prf ← disch φ then return some prf
          let φ ← instantiateMVars φ
          if φ.eq?.isSome && !φ.hasMVar then
            let mv ← mkFreshExprMVar φ
            openGoalsRef.modify (·.push mv.mvarId!)
            return some mv
          return none
        if let some prf ← closeEntails? dischOpen (ty.getArg! 0) (ty.getArg! 1) then
          g.assign prf
          let prfMVars ← getMVars prf
          replaceMainGoal ((← openGoalsRef.get).filter (prfMVars.contains ·)).toList
          return
      throwError (← explainFrameSplitFailure (ty.getArg! 1) (ty.getArg! 0))
    unless ty.isAppOfArity ``SepProp.Satisfies 2 do
      throwError m!"sep solver: goal is not of the form `m ⊨ P` (goal head: `{goalHeadDesc ty}`)\n  actual goal: {ty}\n{sepSolverGoalShapeHint ty}"
    let G := ty.getArg! 0
    let m := ty.getArg! 1
    if (stripMData (← instantiateMVars G)).isConstOf ``SepProp.emp then
      g.assign (mkApp (mkConst ``satisfies_emp) m)
      replaceMainGoal []
      return
    let some (h, P) ← findSatHyp? m | throwError "sep solver: no hypothesis `{m} ⊨ _`"
    if let some prf ← entail? disch m P h G then
      g.assign prf
      replaceMainGoal []
    else if leaveOpen then
      let openGoalsRef ← IO.mkRef (#[] : Array MVarId)
      let dischOpen : Disch := fun φ => do
        if let some prf ← disch φ then return some prf
        let φ ← instantiateMVars φ
        if φ.eq?.isSome && !φ.hasMVar then
          let mv ← mkFreshExprMVar φ
          openGoalsRef.modify (·.push mv.mvarId!)
          return some mv
        return none
      if let some prf ← entail? dischOpen m P h G then
        g.assign prf
        let prfMVars ← getMVars prf
        replaceMainGoal ((← openGoalsRef.get).filter (prfMVars.contains ·)).toList
      else
        let pures ← IO.mkRef #[]
        let (Gs, _) ← expandGoal m G pures
        throwError (← explainFrameSplitFailure Gs P)
    else
      let pures ← IO.mkRef #[]
      let (Gs, _) ← expandGoal m G pures
      throwError (← explainFrameSplitFailure Gs P)

/-- `sep_entail`: close `m ⊨ Q` from a hypothesis `m ⊨ P` (or `P ⊢ Q`) by AC normalization,
    cancellation (value side goals by `rfl`, `assumption`, `simp_all`, or the kernel-only
    `bv_fallback`), frame inference, and dropping unmatched hypothesis atoms. -/
elab "sep_entail" : tactic => do
  closeSat (tacDisch (← `(tactic| first | rfl | assumption | (simp_all; done) | (bv_fallback; done))))

/-- `sep_eq`: close a `SepProp` equality goal `P = Q` (such as AC reassociations
    `A ∗ B ∗ C = C ∗ A ∗ B`, `emp` units, or block equivalences inside `have`, `rw`, or `conv`)
    via `sepProp_eq_of_entails` and `sep_entail`, reporting the one-for-one multiset difference
    (`only in LHS` / `only in RHS`) on failure. -/
elab (priority := default - 1) "sep_eq" : tactic => do
  let saved ← saveState
  try
    evalTactic (← `(tactic| (apply sepProp_eq_of_entails <;> sep_entail)))
  catch _ =>
    saved.restore
    let g ← getMainGoal
    g.withContext do
      let ty := stripMData (← instantiateMVars (← g.getType))
      let some (α, lhs, rhs) := ty.eq?
        | throwError m!"sep_eq: goal is not an equation `P = Q` (goal head: `{goalHeadDesc ty}`)\n  actual goal: {ty}\nhint: `sep_eq` operates on `P = Q` equations; for entailment/satisfaction goals, use `sep_entail` or `sep_frame`"
      unless α.isConstOf ``Arm64.SepProp do
        throwError m!"sep_eq: expected a `SepProp` equality `P = Q`, got equality of type `{α}`\n  actual goal: {ty}"
      throwError (← explainSepEqFailure lhs rhs)

/-- `sep_focus`: prove `Full = T ∗ ?F` by finding the atoms of `T` in `Full` (instantiating
    metavariables of `T`) and assigning `?F` to the remaining atoms; when `proofLib.sepShapeDispatch`
    is enabled, also dispatches entailment/satisfaction goals to `sep_entail` and concrete `SepProp`
    equalities to `sep_eq`. -/
elab "sep_focus" : tactic => do
  let dispatch := proofLib.sepShapeDispatch.get (← getOptions)
  let g ← getMainGoal
  let ty ← g.withContext do pure (stripMData (← instantiateMVars (← g.getType)))
  if dispatch && (ty.isAppOfArity ``SepProp.Entails 2 || ty.isAppOfArity ``SepProp.Satisfies 2 || isForallSatOrEntails ty) then
    evalTactic (← `(tactic| sep_entail))
    return
  g.withContext do
    let some (α, full, rhs) := ty.eq?
      | throwError m!"sep_focus: goal is not an equation (goal head: `{goalHeadDesc ty}`)\n  actual goal: {ty}\n{sepFocusGoalShapeHint ty}"
    unless rhs.isAppOfArity ``SepProp.sepConj 2 do
      if dispatch && α.isConstOf ``Arm64.SepProp && !rhs.hasMVar then
        if ← tryTactic (evalTactic (← `(tactic| sep_eq))) then return
      throwError m!"sep_focus: goal is not `_ = _ ∗ _`\n  actual goal: {ty}\nhint: `sep_focus` operates on `P = Q ∗ R` equations; to prove a general `SepProp` equality `P = Q`, use `sep_eq` or `sep_frame`"
    let some (frame, prf) ← frameSplit? (rhs.getArg! 0) full
      | do
        if dispatch && α.isConstOf ``Arm64.SepProp && !rhs.hasMVar then
          if ← tryTactic (evalTactic (← `(tactic| sep_eq))) then return
        throwError (← explainFrameSplitFailure (rhs.getArg! 0) full)
    unless ← isDefEq (rhs.getArg! 1) frame do
      if dispatch && α.isConstOf ``Arm64.SepProp && !(rhs.getArg! 1).hasMVar then
        if ← tryTactic (evalTactic (← `(tactic| sep_eq))) then return
      throwError m!"sep_focus: cannot assign frame `{frame}` to RHS frame `{rhs.getArg! 1}`\n  actual goal: {ty}\nhint: `sep_focus` assigns a metavariable frame `?F` in `Full = Sub ∗ ?F`; when the RHS frame is already concrete, use `sep_eq` or `sep_frame`"
    g.assign prf
    replaceMainGoal []

/-- `sep_facts h`: add the content facts (`Memory.read*` equalities) and pairwise disjointness of
    the blocks of `h : m ⊨ P` to the local context. -/
elab "sep_facts " h:term : tactic => do
  let g ← getMainGoal
  let facts ← g.withContext do
    let h ← elabTerm h none
    let ty := stripMData (← instantiateMVars (← inferType h))
    unless ty.isAppOfArity ``SepProp.Satisfies 2 do throwError "sep_facts: not `m ⊨ P`"
    let (reads, disj) ← blockFacts (ty.getArg! 1) (ty.getArg! 0) h
    (reads ++ disj).mapM fun p => return (p, ← instantiateMVars (← inferType p))
  let mut g := g
  for (p, ty) in facts do
    let (_, g') ← (← g.assert (← g.withContext do return (← getLCtx).getUnusedName `h_sep) ty p).intro1P
    g := g'
  replaceMainGoal [g]

end SepSolver

end

@[expose] public section

/-! ## Framed reads and pure extraction -/

/-- Extract a pure conjunct `⌜φ⌝` from `m ⊨ Full` via `sep_focus` (or an explicit decomposition
    `hf : Full = ⌜φ⌝ ∗ F`), returning both `φ` and `m ⊨ F`. -/
theorem extract_pure {φ : Prop} {m : Memory} {Full F : SepProp}
    (h : m ⊨ Full) (hf : Full = ⌜φ⌝ ∗ F := by sep_focus) : φ ∧ m ⊨ F :=
  (satisfies_pure_sepConj φ F m).mp (hf ▸ h)

/-- Read an 8-bit value owned by some atom `a ↦₈ v` of `Full`. -/
theorem read8_sep_at (a : BitVec 64) {m : Memory} {v : BitVec 8} {Full F : SepProp}
    (h : m ⊨ Full) (hf : Full = (a ↦₈ v) ∗ F := by sep_focus) : m.read8 a = v :=
  (IsBlock.pointsTo8 a v).read (hf ▸ h)


/-- Read a 32-bit value owned by some atom `a ↦₃₂ v` of `Full`. -/
theorem read32_sep_at (a : BitVec 64) {m : Memory} {v : BitVec 32} {Full F : SepProp}
    (h : m ⊨ Full) (hf : Full = (a ↦₃₂ v) ∗ F := by sep_focus) : m.read32 a = v :=
  (IsBlock.pointsTo32 a v).read (hf ▸ h)

/-- Read a 64-bit value owned by some atom `a ↦₆₄ v` of `Full`. -/
theorem read64_sep_at (a : BitVec 64) {m : Memory} {v : BitVec 64} {Full F : SepProp}
    (h : m ⊨ Full) (hf : Full = (a ↦₆₄ v) ∗ F := by sep_focus) : m.read64 a = v :=
  (IsBlock.pointsTo64 a v).read (hf ▸ h)

/-- Read element `i` of a word array `a ↦₆₄* ws` owned by `Full`, at byte offset `i <<< 3`. -/
theorem read64_shl3_of_words_at (a : BitVec 64) {m : Memory} {ws : List (BitVec 64)}
    {Full F : SepProp} (h : m ⊨ Full) (i : BitVec 64) (hi : i.toNat < ws.length)
    (hf : Full = (a ↦₆₄* ws) ∗ F := by sep_focus) :
    m.read64 (a + (i <<< 3)) = ws.getD i.toNat 0#64 :=
  read64_shl3_of_words (hf ▸ h) i hi



end

end ProofLib
