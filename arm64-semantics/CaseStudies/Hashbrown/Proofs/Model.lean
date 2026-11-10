/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Spec.Top
public import VerifiedLibraries.SwissTable.Proofs.Control
public import ProofLib.BV.Bits

/-!
# Finite-Map and `FxHasher64` Model

Defines the unique-key association-list model (`Map64`, `Map64Wf`), `FxHasher64` (`fxHash`,
`h1Hash`, `h2Tag`), and the `U64Map` table allocation size, and re-exports the generic SwissTable
control-tag and triangular-probe definitions from `VerifiedLibraries.SwissTable.Proofs.Control`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 ProofLib CaseStudies.Hashbrown

export VerifiedLibraries.SwissTable (
  tagEmpty tagDeleted isSpecialTag isFullTag tagOfHash tagOfHash_lt_0x80 tagOfHash_and_0x80
  tagOfHash_ne_empty tagOfHash_ne_deleted ValidTag ValidTag.empty ValidTag.deleted
  ValidTag.of_tagOfHash isFullTag_iff_lt_0x80 isSpecialTag_iff_ge_0x80 isFullTag_tagOfHash
  isFullTag_tagEmpty isFullTag_tagDeleted ValidTag.special_cases ValidBucketMask
  bucketMaskToCapacityBV bucketMaskToCapacity bucketMaskToCapacityBV_zero
  bucketMaskToCapacity_zero bucketMaskToCapacityBV_three bucketMaskToCapacity_three
  ValidBucketMask.ne_zero ValidBucketMask.buckets_eq ValidBucketMask.capacity_eq
  ValidBucketMask.capacity_bounds triGroupIdx triByteOff triByteOff_zero triByteOff_succ
  triByteOff_eq_eight_mul_triGroupIdx setCtrlMirrorIdx CtrlMirrorInv CtrlMirrorInv_init numGroups
  ctrlGroupAt)

/-! ## Finite-Map Reference Model -/

/-- Internal finite-map reference type, matching `CliMap` in `Spec/Top.lean`. -/
abbrev Map64 : Type := CliMap

/-- Well-formedness of a `Map64` association list: keys are pairwise distinct (`Nodup`), so
    `m.length` equals the exact number of live key-value entries (`items`). -/
def Map64Wf (m : Map64) : Prop :=
  (m.map Prod.fst).Nodup

@[simp]
theorem cliMapLookup_nil (k : BitVec 64) : cliMapLookup k [] = none := rfl

@[simp]
theorem cliMapErase_nil (k : BitVec 64) : cliMapErase k [] = [] := rfl

theorem cliMapLookup_cons (k k' : BitVec 64) (v' : BitVec 64) (rest : Map64) :
    cliMapLookup k ((k', v') :: rest) = if k' == k then some v' else cliMapLookup k rest := rfl

theorem cliMapErase_cons (k k' : BitVec 64) (v' : BitVec 64) (rest : Map64) :
    cliMapErase k ((k', v') :: rest) =
      if k' == k then cliMapErase k rest else (k', v') :: cliMapErase k rest := rfl

theorem mem_keys_iff_lookup_isSome {k : BitVec 64} {m : Map64} :
    k ∈ m.map Prod.fst ↔ (cliMapLookup k m).isSome := by
  induction m with
  | nil => simp [cliMapLookup]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [List.map_cons, List.mem_cons, cliMapLookup]
    by_cases h : k' = k
    · subst h; simp
    · have hne : (k' == k) = false := beq_eq_false_iff_ne.mpr h
      simp [hne, Ne.symm h, ih]

theorem lookup_eq_none_iff_not_mem_keys {k : BitVec 64} {m : Map64} :
    cliMapLookup k m = none ↔ k ∉ m.map Prod.fst := by
  rw [mem_keys_iff_lookup_isSome]
  cases cliMapLookup k m <;> simp

@[simp]
theorem cliMapLookup_erase_self (k : BitVec 64) (m : Map64) :
    cliMapLookup k (cliMapErase k m) = none := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [cliMapErase]
    by_cases h : k' == k
    · simp [h, ih]
    · simp [h, cliMapLookup, ih]

theorem cliMapLookup_erase_ne {k' k : BitVec 64} (hne : k' ≠ k) (m : Map64) :
    cliMapLookup k' (cliMapErase k m) = cliMapLookup k' m := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k0, v0⟩
    simp only [cliMapErase, cliMapLookup]
    by_cases h0 : k0 == k
    · have hk0 : k0 = k := beq_iff_eq.mp h0
      subst hk0
      have hne' : (k0 == k') = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp [hne', ih]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, cliMapLookup]
      cases h1 : k0 == k'
      · exact ih
      · rfl

@[simp]
theorem cliMapLookup_insert_self (k v : BitVec 64) (m : Map64) :
    cliMapLookup k (cliMapInsert k v m) = some v := by
  simp [cliMapInsert, cliMapLookup]

theorem cliMapLookup_insert_ne {k' k : BitVec 64} (hne : k' ≠ k) (v : BitVec 64) (m : Map64) :
    cliMapLookup k' (cliMapInsert k v m) = cliMapLookup k' m := by
  have hbeq : (k == k') = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
  simp [cliMapInsert, cliMapLookup, hbeq, cliMapLookup_erase_ne hne]

theorem not_mem_keys_erase (k : BitVec 64) (m : Map64) :
    k ∉ (cliMapErase k m).map Prod.fst :=
  lookup_eq_none_iff_not_mem_keys.mp (cliMapLookup_erase_self k m)

theorem mem_keys_erase_of_mem {x k : BitVec 64} {m : Map64}
    (h : x ∈ (cliMapErase k m).map Prod.fst) : x ∈ m.map Prod.fst := by
  induction m with
  | nil => simp [cliMapErase] at h
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [cliMapErase] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hrest)

theorem Map64Wf.nil : Map64Wf [] := List.Pairwise.nil

theorem Map64Wf.erase {m : Map64} (hwf : Map64Wf m) (k : BitVec 64) :
    Map64Wf (cliMapErase k m) := by
  unfold Map64Wf at hwf ⊢
  induction m with
  | nil => exact List.Pairwise.nil
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    rw [List.map_cons, List.nodup_cons] at hwf
    simp only [cliMapErase]
    split
    · exact ih hwf.2
    · rw [List.map_cons, List.nodup_cons]
      exact ⟨fun hm => hwf.1 (mem_keys_erase_of_mem hm), ih hwf.2⟩

theorem Map64Wf.insert {m : Map64} (hwf : Map64Wf m) (k v : BitVec 64) :
    Map64Wf (cliMapInsert k v m) := by
  unfold Map64Wf cliMapInsert
  rw [List.map_cons, List.nodup_cons]
  exact ⟨not_mem_keys_erase k m, hwf.erase k⟩

theorem cliMapErase_eq_self_of_lookup_none {k : BitVec 64} {m : Map64}
    (h : cliMapLookup k m = none) : cliMapErase k m = m := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [cliMapLookup] at h
    by_cases hk : k' == k
    · simp [hk] at h
    · simp [hk] at h
      simp [cliMapErase, hk, ih h]

theorem cliMapErase_length_of_lookup_none {k : BitVec 64} {m : Map64}
    (h : cliMapLookup k m = none) : (cliMapErase k m).length = m.length := by
  rw [cliMapErase_eq_self_of_lookup_none h]

theorem cliMapErase_length_of_lookup_some {k v : BitVec 64} {m : Map64}
    (hwf : Map64Wf m) (h : cliMapLookup k m = some v) :
    (cliMapErase k m).length + 1 = m.length := by
  induction m with
  | nil => simp [cliMapLookup] at h
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    unfold Map64Wf at hwf
    rw [List.map_cons, List.nodup_cons] at hwf
    simp only [cliMapLookup, cliMapErase] at h ⊢
    by_cases hk : k' == k
    · have heq : k' = k := beq_iff_eq.mp hk
      subst heq
      have hnone : cliMapLookup k' rest = none := lookup_eq_none_iff_not_mem_keys.mpr hwf.1
      simp only [beq_self_eq_true, ↓reduceIte, cliMapErase_eq_self_of_lookup_none hnone,
        List.length_cons]
    · simp [hk] at h ⊢
      have := ih hwf.2 h
      omega

theorem cliMapInsert_length_of_lookup_none {k v : BitVec 64} {m : Map64}
    (h : cliMapLookup k m = none) :
    (cliMapInsert k v m).length = m.length + 1 := by
  simp [cliMapInsert, cliMapErase_length_of_lookup_none h]

theorem cliMapInsert_length_of_lookup_some {k v oldV : BitVec 64} {m : Map64}
    (hwf : Map64Wf m) (h : cliMapLookup k m = some oldV) :
    (cliMapInsert k v m).length = m.length := by
  have he := cliMapErase_length_of_lookup_some hwf h
  simp only [cliMapInsert, List.length_cons]
  omega

theorem Map64Wf.length_eq_of_lookup_eq {m1 m2 : Map64}
    (hwf1 : Map64Wf m1) (hwf2 : Map64Wf m2)
    (heq : ∀ q : BitVec 64, cliMapLookup q m1 = cliMapLookup q m2) :
    m1.length = m2.length := by
  induction m1 generalizing m2 with
  | nil =>
    cases m2 with
    | nil => rfl
    | cons kv rest =>
      have h := heq kv.1
      simp [cliMapLookup] at h
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    have hwf1' := hwf1
    unfold Map64Wf at hwf1'
    rw [List.map_cons, List.nodup_cons] at hwf1'
    have hnone1 : cliMapLookup k rest = none := lookup_eq_none_iff_not_mem_keys.mpr hwf1'.1
    have hsome2 : cliMapLookup k m2 = some v := by
      have h := (heq k).symm
      simpa [cliMapLookup] using h
    have hlen2 := cliMapErase_length_of_lookup_some hwf2 hsome2
    have hih := ih hwf1'.2 (hwf2.erase k) fun q => by
      by_cases hqk : q = k
      · subst hqk; rw [hnone1, cliMapLookup_erase_self]
      · rw [cliMapLookup_erase_ne hqk, ← heq q]
        have hbeq : (k == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hqk)
        simp [cliMapLookup, hbeq]
    simp only [List.length_cons]
    omega

/-! ## `FxHasher64` -/

/-- `FX_SEED = 0x517cc1b727220a95` from `CaseStudies/Hashbrown/Implementation/src/lib.rs`. -/
def fxSeed : BitVec 64 := 0x517cc1b727220a95#64

/-- Unfolded product `k * FX_SEED` before the final 32-bit xorshift. -/
def fxProd (k : BitVec 64) : BitVec 64 := k * fxSeed

/-- 64-bit `FxHasher64` output `(k * FX_SEED) ^ ((k * FX_SEED) >> 32)`. -/
def fxHash (k : BitVec 64) : BitVec 64 :=
  let p := fxProd k
  p ^^^ (p >>> 32)

/-- Primary SwissTable probe hash `h1(hash) = hash`. -/
abbrev h1Hash (k : BitVec 64) : BitVec 64 := fxHash k

/-- Secondary 7-bit SwissTable control tag `h2(hash) = Tag::full(hash) = (hash >> 57) as u8`,
    written in terms of `fxProd k >>> 57` to match the compiled shift sequence. -/
def h2Tag (k : BitVec 64) : BitVec 8 :=
  (fxProd k >>> 57).truncate 8

/-- XORing `fxProd k` with `fxProd k >>> 32` leaves bits `63..32` unchanged, so
    `(fxProd k >>> 57).truncate 8 = (fxHash k >>> 57).truncate 8`. -/
theorem h2Tag_eq_fxHash (k : BitVec 64) :
    h2Tag k = (fxHash k >>> 57).truncate 8 := by
  unfold h2Tag fxHash
  congr 1
  ext i hi
  simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge (fxProd k) (32 + (57 + i)) (by omega), Bool.xor_false]

theorem h2Tag_lt_0x80 (k : BitVec 64) : (h2Tag k).toNat < 0x80 := by
  have h : h2Tag k < 0x80#8 := by unfold h2Tag; bv_bits
  simpa [BitVec.lt_def] using h

theorem h2Tag_and_0x80 (k : BitVec 64) : h2Tag k &&& 0x80#8 = 0#8 := by
  unfold h2Tag; bv_bits

@[simp]
theorem h2Tag_ne_empty (k : BitVec 64) : h2Tag k ≠ 0xff#8 := by
  have := h2Tag_lt_0x80 k; intro h; rw [h] at this; contradiction

@[simp]
theorem h2Tag_ne_deleted (k : BitVec 64) : h2Tag k ≠ 0x80#8 := by
  have := h2Tag_lt_0x80 k; intro h; rw [h] at this; contradiction

theorem h2Tag_eq_tagOfHash (k : BitVec 64) : h2Tag k = tagOfHash (fxHash k) := by
  rw [h2Tag_eq_fxHash]; rfl

/-! ## `U64Map` Table Allocation Size -/

/-- Total heap allocation size (`17 * buckets + 8` bytes, `0` when `bm = 0`). -/
def tableAllocBytes (bm : BitVec 64) : Nat :=
  if bm = 0#64 then 0 else 17 * (bm.toNat + 1) + 8

/-- Number of live heap blocks owned by `U64Map` (`0` when `bm = 0`, `1` when `bm ≠ 0`). -/
def tableAllocBlocks (bm : BitVec 64) : Nat :=
  if bm = 0#64 then 0 else 1

/-- Maximum `capacity` accepted by `with_capacity` / `reserve_rehash` without capacity overflow:
    `7 * 2 ^ 55 = 0x0380_0000_0000_0000` (yielding `buckets = 2 ^ 58`). -/
def MaxHashbrownCapacity : Nat := 7 * 2 ^ 55

end CaseStudies.Hashbrown.Proofs
