/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Model
public import VerifiedLibraries.SwissTable.Proofs.Inv
public import CaseStudies.Hashbrown.Proofs.PlacedCode
public import CaseStudies.Hashbrown.Proofs.Externs
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Region

/-!
# SwissTable Representation Invariants

Defines the `Map64` SwissTable invariant (`SwissTableInv`), its equivalence with
`VerifiedLibraries.SwissTable.SwissTableInv`, downward `(k, v)` slot separation logic
(`slotsDownFrom`), and the top-level `U64MapRep` predicate.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib CaseStudies.Hashbrown

/-! ## `h2Tag` Control Tags -/

theorem ValidTag.of_h2Tag (k : BitVec 64) : ValidTag (h2Tag k) :=
  Or.inr (Or.inr (h2Tag_lt_0x80 k))

@[simp]
theorem isFullTag_h2Tag (k : BitVec 64) : isFullTag (h2Tag k) = true :=
  (isFullTag_iff_lt_0x80 _).mpr (h2Tag_lt_0x80 k)

/-! ## Key Probe Reachability and `SwissTableInv` -/

/-- Starting index of step `step`'s group on the probe chain of key `k`: the generic SwissTable
    probe position of `fxHash k`. -/
def probePos (bm k : BitVec 64) (step : Nat) : Nat :=
  VerifiedLibraries.SwissTable.probePos bm (fxHash k) step

/-- Key `k` stored at full slot `i < buckets` is reachable along its triangular probe chain:
    at some `step < numGroups bm` and `lane < 8`, lane `lane` of `ctrlGroupAt ctrl (probePos bm k step)`
    holds `h2Tag k` with `(probePos bm k step + lane) % buckets = i`, and no strictly earlier group
    `s' < step` contains `tagEmpty` (`0xff#8`). -/
def ProbeReachable (bm : BitVec 64) (ctrl : List (BitVec 8)) (k : BitVec 64) (i : Nat) : Prop :=
  let buckets := bm.toNat + 1
  ∃ step lane : Nat,
    step < numGroups bm ∧
    lane < 8 ∧
    (ctrlGroupAt ctrl (probePos bm k step))[lane]? = some (h2Tag k) ∧
    (probePos bm k step + lane) % buckets = i ∧
    ∀ s' < step, tagEmpty ∉ ctrlGroupAt ctrl (probePos bm k s')

theorem ProbeReachable_iff_swissTable {bm : BitVec 64} {ctrl : List (BitVec 8)} {k : BitVec 64}
    {i : Nat} :
    ProbeReachable bm ctrl k i ↔ VerifiedLibraries.SwissTable.ProbeReachable bm ctrl (fxHash k) i := by
  unfold ProbeReachable VerifiedLibraries.SwissTable.ProbeReachable
  rw [h2Tag_eq_tagOfHash]
  rfl

theorem mem_of_cliMapLookup_eq_some {k v : BitVec 64} {m : Map64}
    (h : cliMapLookup k m = some v) : (k, v) ∈ m := by
  induction m with
  | nil => simp [cliMapLookup] at h
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [cliMapLookup] at h
    by_cases hk : k' = k
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem cliMapLookup_eq_some_of_mem {k v : BitVec 64} {m : Map64} (hwf : Map64Wf m)
    (h : (k, v) ∈ m) : cliMapLookup k m = some v := by
  unfold Map64Wf at hwf
  induction m with
  | nil => simp at h
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    rw [List.map_cons, List.nodup_cons] at hwf
    simp only [cliMapLookup]
    rcases List.mem_cons.mp h with he | hrest
    · rcases Prod.mk.injEq _ _ _ _ ▸ he with ⟨rfl, rfl⟩
      simp
    · have hne : k' ≠ k := by
        rintro rfl
        exact hwf.1 (List.mem_map.mpr ⟨(k', v), hrest, rfl⟩)
      have hb : (k' == k) = false := beq_eq_false_iff_ne.mpr hne
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact ih hwf.2 hrest

/-- Pure SwissTable invariant relating `(bm, growthLeft, items, ctrl, slots)` to abstract `m : Map64`. -/
structure SwissTableInv (bm growthLeft items : BitVec 64)
    (ctrl : List (BitVec 8)) (slots : List (BitVec 64 × BitVec 64)) (m : Map64) : Prop where
  validMask : ValidBucketMask bm
  wf : Map64Wf m
  slots_len : slots.length = bm.toNat + 1
  mirror : CtrlMirrorInv (bm.toNat + 1) ctrl
  items_eq : items = BitVec.ofNat 64 m.length
  growth_le : growthLeft.toNat ≤ bucketMaskToCapacity bm
  conservation :
    m.length + ((ctrl.take (bm.toNat + 1)).countP (· == tagDeleted)) + growthLeft.toNat =
      bucketMaskToCapacity bm
  countFull_eq :
    ((ctrl.take (bm.toNat + 1)).countP isFullTag) = m.length
  full_sound :
    ∀ (i : Nat) (hi : i < bm.toNat + 1),
      isFullTag (ctrl[i]'(by have := mirror.1; omega)) = true →
        ctrl[i]'(by have := mirror.1; omega) = h2Tag (slots[i]'(by omega)).1 ∧
        cliMapLookup (slots[i]'(by omega)).1 m = some (slots[i]'(by omega)).2 ∧
        ProbeReachable bm ctrl (slots[i]'(by omega)).1 i
  full_inj :
    ∀ (i j : Nat) (hi : i < bm.toNat + 1) (hj : j < bm.toNat + 1),
      isFullTag (ctrl[i]'(by have := mirror.1; omega)) = true →
      isFullTag (ctrl[j]'(by have := mirror.1; omega)) = true →
      (slots[i]'(by omega)).1 = (slots[j]'(by omega)).1 →
      i = j
  complete :
    ∀ (k v : BitVec 64),
      cliMapLookup k m = some v →
        ∃ (i : Nat) (hi : i < bm.toNat + 1),
          isFullTag (ctrl[i]'(by have := mirror.1; omega)) = true ∧
          slots[i]'(by omega) = (k, v)

namespace SwissTableInv

theorem toGeneric {bm growthLeft items : BitVec 64} {ctrl : List (BitVec 8)}
    {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm growthLeft items ctrl slots m) :
    VerifiedLibraries.SwissTable.SwissTableInv (fun p : BitVec 64 × BitVec 64 => fxHash p.1) Prod.fst
      bm growthLeft items ctrl slots m := by
  refine ⟨h.validMask, h.wf, h.slots_len, h.mirror, h.items_eq, h.growth_le, h.conservation,
    h.countFull_eq, ?_, h.full_inj, ?_⟩
  · intro i hi hf
    obtain ⟨htag, hlook, hreach⟩ := h.full_sound i hi hf
    exact ⟨htag.trans (h2Tag_eq_tagOfHash _), mem_of_cliMapLookup_eq_some hlook,
      ProbeReachable_iff_swissTable.mp hreach⟩
  · intro x hx
    exact h.complete x.1 x.2 (cliMapLookup_eq_some_of_mem h.wf hx)

theorem ofGeneric {bm growthLeft items : BitVec 64} {ctrl : List (BitVec 8)}
    {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : VerifiedLibraries.SwissTable.SwissTableInv (fun p : BitVec 64 × BitVec 64 => fxHash p.1)
      Prod.fst bm growthLeft items ctrl slots m) :
    SwissTableInv bm growthLeft items ctrl slots m := by
  refine ⟨h.validMask, h.wf, h.slots_len, h.mirror, h.items_eq, h.growth_le, h.conservation,
    h.countFull_eq, ?_, h.full_inj, ?_⟩
  · intro i hi hf
    obtain ⟨htag, hmem, hreach⟩ := h.full_sound i hi hf
    exact ⟨htag.trans (h2Tag_eq_tagOfHash _).symm, cliMapLookup_eq_some_of_mem h.wf hmem,
      ProbeReachable_iff_swissTable.mpr hreach⟩
  · intro k v hlook
    exact h.complete (k, v) (mem_of_cliMapLookup_eq_some hlook)

end SwissTableInv

/-- Every freshly zero-item allocated table with `ctrl = replicate (buckets + 8) 0xff` satisfies
    `SwissTableInv` (also serves as the non-vacuity witness for `lean-sig inv-audit`). -/
theorem SwissTableInv_init_of_mask {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {slots : List (BitVec 64 × BitVec 64)} (hsl : slots.length = bm.toNat + 1) :
    SwissTableInv bm (bucketMaskToCapacityBV bm) 0#64
      (List.replicate (bm.toNat + 1 + 8) tagEmpty) slots [] :=
  SwissTableInv.ofGeneric (VerifiedLibraries.SwissTable.SwissTableInv.init_of_mask hbm hsl)

theorem SwissTableInv_init :
    SwissTableInv 3#64 3#64 0#64
      (List.replicate 12 tagEmpty) (List.replicate 4 (0#64, 0#64)) [] :=
  SwissTableInv_init_of_mask ⟨2, by decide, by decide, rfl⟩ (by decide)

theorem SwissTableInv.exists_empty_slot {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm growthLeft items ctrl slots m) :
    ∃ (i : Nat) (_ : i < bm.toNat + 1),
      ctrl[i]'(by have := h.mirror.1; omega) = tagEmpty :=
  h.toGeneric.exists_empty_slot

theorem ValidBucketMask.tableLayoutOk {bm : BitVec 64} (h : ValidBucketMask bm) :
    LayoutOk (BitVec.ofNat 64 (17 * (bm.toNat + 1) + 8)) 8#64 := by
  obtain ⟨exp, hlo, hhi, hbm⟩ := h
  rw [ValidBucketMask.buckets_eq hlo hhi hbm]
  have hpow_le : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide : 0 < 2) hhi
  have hpow_ge : 4 ≤ 2 ^ exp :=
    show 2 ^ 2 ≤ 2 ^ exp from Nat.pow_le_pow_right (by decide : 0 < 2) hlo
  have hbound : 17 * 2 ^ 58 + 16 ≤ 2 ^ 63 := by decide
  have hbound64 : 2 ^ 63 < 2 ^ 64 := by decide
  refine ⟨?_, by decide, ?_⟩
  · intro hz
    have h0 := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0
    simp at h0
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change 17 * 2 ^ exp + 8 + 8 ≤ 2 ^ 63
    omega

/-! ## Downward Bucket Array Separation Logic -/

/-- One 16-byte `(k, v)` bucket at `p`: `k` at `p + 0`, `v` at `p + 8`. -/
def slotPairAt (p : BitVec 64) (kv : BitVec 64 × BitVec 64) : SepProp :=
  (p ↦₆₄ kv.1) ∗ ((p + 8#64) ↦₆₄ kv.2)

/-- Address `ctrlPtr - 16 * (i + 1)` of bucket `i` below `ctrlPtr`. -/
def slotAddr (ctrlPtr : BitVec 64) (i : Nat) : BitVec 64 :=
  ctrlPtr - BitVec.ofNat 64 (16 * (i + 1))

/-- Downward array of `(k, v)` pairs starting immediately below `top` (`slots[i]` at
    `top - 16 * (i + 1)`). -/
def slotsDownFrom (top : BitVec 64) : List (BitVec 64 × BitVec 64) → SepProp
  | [] => emp
  | kv :: rest => slotPairAt (top - 16#64) kv ∗ slotsDownFrom (top - 16#64) rest

@[simp]
theorem slotsDownFrom_nil (top : BitVec 64) : slotsDownFrom top [] = emp := rfl

@[simp]
theorem slotsDownFrom_cons (top : BitVec 64) (kv : BitVec 64 × BitVec 64)
    (rest : List (BitVec 64 × BitVec 64)) :
    slotsDownFrom top (kv :: rest) =
      slotPairAt (top - 16#64) kv ∗ slotsDownFrom (top - 16#64) rest := rfl

theorem slotsDownFrom_append (top : BitVec 64)
    (xs ys : List (BitVec 64 × BitVec 64)) :
    slotsDownFrom top (xs ++ ys) =
      slotsDownFrom top xs ∗
        slotsDownFrom (top - BitVec.ofNat 64 (16 * xs.length)) ys := by
  induction xs generalizing top with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.cons_append, slotsDownFrom_cons, List.length_cons, ih, sepConj_assoc]
    have htop : top - 16#64 - BitVec.ofNat 64 (16 * xs.length) =
        top - BitVec.ofNat 64 (16 * (xs.length + 1)) := by
      have : 16 * (xs.length + 1) = 16 + 16 * xs.length := by omega
      rw [this, BitVec.ofNat_add]
      bv_lin
    rw [htop]

theorem slotsDownFrom_focus (top : BitVec 64) (slots : List (BitVec 64 × BitVec 64))
    {i : Nat} (hi : i < slots.length) :
    slotsDownFrom top slots =
      slotPairAt (slotAddr top i) slots[i] ∗
        (slotsDownFrom top (slots.take i) ∗
         slotsDownFrom (slotAddr top i) (slots.drop (i + 1))) := by
  conv => lhs; rw [← List.take_append_drop i slots, List.drop_eq_getElem_cons hi]
  rw [slotsDownFrom_append, slotsDownFrom_cons]
  have hlen : (slots.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
  rw [hlen]
  have haddr : top - BitVec.ofNat 64 (16 * i) - 16#64 = slotAddr top i := by
    unfold slotAddr
    have : 16 * (i + 1) = 16 * i + 16 := by omega
    rw [this, BitVec.ofNat_add]
    bv_lin
  rw [haddr]
  ac_rfl

theorem slotsDownFrom_update (top : BitVec 64) (slots : List (BitVec 64 × BitVec 64))
    {i : Nat} (hi : i < slots.length) (kv' : BitVec 64 × BitVec 64) :
    slotPairAt (slotAddr top i) kv' ∗
      (slotsDownFrom top (slots.take i) ∗
       slotsDownFrom (slotAddr top i) (slots.drop (i + 1))) =
      slotsDownFrom top (slots.set i kv') := by
  have hi' : i < (slots.set i kv').length := by simp [hi]
  rw [slotsDownFrom_focus top (slots.set i kv') hi']
  have htake : (slots.set i kv').take i = slots.take i :=
    List.take_set_of_le (by omega)
  have hdrop : (slots.set i kv').drop (i + 1) = slots.drop (i + 1) :=
    List.drop_set_of_lt (by omega)
  simp [htake, hdrop]

theorem slotPairAt_entails_memRegion (p : BitVec 64) (kv : BitVec 64 × BitVec 64) :
    slotPairAt p kv ⊢ memRegion p 16 := by
  unfold slotPairAt
  rw [memRegion_split p 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p kv.1)
    (pointsTo64_entails_memRegion (p + 8#64) kv.2)

theorem memRegion16_entails_slotPairAt (p : BitVec 64) :
    memRegion p 16 ⊢ ∃∗ kv : BitVec 64 × BitVec 64, slotPairAt p kv := by
  rw [memRegion_split p 8 8 (by decide), memRegion_eight p, memRegion_eight (p + 8#64)]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro k
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro v
  exact Entails.sepExists_right (k, v) (Entails.refl _)

theorem slotsDownFrom_to_memRegion :
    ∀ (slots : List (BitVec 64 × BitVec 64)) (allocPtr : BitVec 64),
      16 * slots.length ≤ 2 ^ 64 →
      slotsDownFrom (allocPtr + BitVec.ofNat 64 (16 * slots.length)) slots ⊢
        memRegion allocPtr (16 * slots.length)
  | [], allocPtr, _ => by
    simp [memRegion_zero]
    exact Entails.refl _
  | kv :: rest, allocPtr, hle => by
    simp only [List.length_cons, slotsDownFrom_cons] at hle ⊢
    have hstep :
        allocPtr + BitVec.ofNat 64 (16 * (rest.length + 1)) - 16#64 =
          allocPtr + BitVec.ofNat 64 (16 * rest.length) := by
      have : 16 * (rest.length + 1) = 16 * rest.length + 16 := by omega
      rw [this, BitVec.ofNat_add]
      bv_lin
    rw [hstep]
    have hsplit : 16 * (rest.length + 1) = 16 * rest.length + 16 := by omega
    rw [hsplit, memRegion_split allocPtr (16 * rest.length) 16 hle, sepConj_comm]
    exact sepConj_mono (slotsDownFrom_to_memRegion rest allocPtr (by omega))
      (slotPairAt_entails_memRegion _ kv)

theorem memRegion_to_slotsDownFrom :
    ∀ (n : Nat) (allocPtr : BitVec 64),
      16 * n ≤ 2 ^ 64 →
      memRegion allocPtr (16 * n) ⊢
        ∃∗ slots : List (BitVec 64 × BitVec 64),
          ⌜slots.length = n⌝ ∗ slotsDownFrom (allocPtr + BitVec.ofNat 64 (16 * n)) slots
  | 0, allocPtr, _ => by
    simp only [Nat.mul_zero, memRegion_zero]
    exact Entails.sepExists_right [] (Entails.pure_right rfl (by simp; exact Entails.refl _))
  | n + 1, allocPtr, hle => by
    have hsplit : 16 * (n + 1) = 16 * n + 16 := by omega
    rw [hsplit, memRegion_split allocPtr (16 * n) 16 hle]
    refine Entails.trans
      (sepConj_mono (memRegion_to_slotsDownFrom n allocPtr (by omega))
        (memRegion16_entails_slotPairAt (allocPtr + BitVec.ofNat 64 (16 * n)))) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim
    intro rest
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro kv
    rw [sepConj_assoc]
    apply Entails.pure_left
    intro hlen
    refine Entails.sepExists_right (kv :: rest) ?_
    refine Entails.pure_right (by simp [hlen]) ?_
    have hstep :
        allocPtr + BitVec.ofNat 64 (16 * n + 16) - 16#64 =
          allocPtr + BitVec.ofNat 64 (16 * n) := by
      rw [BitVec.ofNat_add]
      bv_lin
    simp only [slotsDownFrom_cons, hstep]
    exact Entails.of_eq (sepConj_comm _ _)

/-! ## Top-Level `U64MapStruct` and `U64MapRep` -/

/-- 32-byte `U64Map` (`RawTableInner`) struct fields at `mapPtr`:
    `[+0x00] ctrl`, `[+0x08] bucket_mask`, `[+0x10] growth_left`, `[+0x18] items`. -/
def U64MapStruct (mapPtr ctrlPtr bm growthLeft items : BitVec 64) : SepProp :=
  (mapPtr ↦₆₄ ctrlPtr) ∗
  ((mapPtr + 8#64) ↦₆₄ bm) ∗
  ((mapPtr + 16#64) ↦₆₄ growthLeft) ∗
  ((mapPtr + 24#64) ↦₆₄ items)

theorem U64MapStruct_entails_memRegion (mapPtr ctrlPtr bm growthLeft items : BitVec 64) :
    U64MapStruct mapPtr ctrlPtr bm growthLeft items ⊢ memRegion mapPtr 32 := by
  unfold U64MapStruct
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl,
      memRegion_split mapPtr 8 24 (by decide),
      memRegion_split (mapPtr + 8#64) 8 16 (by decide),
      memRegion_split (mapPtr + 8#64 + 8#64) 8 8 (by decide)]
  have h16 : mapPtr + 8#64 + 8#64 = mapPtr + 16#64 := by bv_lin
  have h24 : mapPtr + 16#64 + 8#64 = mapPtr + 24#64 := by bv_lin
  rw [h16, h24]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))

/-- Allocator cost of a `U64Map` with `bucket_mask = bm` (`0` when `bm = 0#64`). -/
def hbMapCost (A : HbAlloc) (bm : BitVec 64) : Nat :=
  if bm = 0#64 then 0 else A.cost (tableAllocBytes bm) 8

@[simp] theorem hbMapCost_zero (A : HbAlloc) : hbMapCost A 0#64 = 0 := rfl

/-- Witness record for a heap-allocated `U64Map` (`bm ≠ 0#64`). -/
structure HbHeapMapWitness where
  allocPtr   : BitVec 64
  ctrlPtr    : BitVec 64
  growthLeft : BitVec 64
  items      : BitVec 64
  ctrl       : List (BitVec 8)
  slots      : List (BitVec 64 × BitVec 64)

/-- Placement-generic SwissTable representation predicate for `hashbrown` v0.17.1 `U64Map` with
    occupied-plus-tombstone budget `u` (`bucketMaskToCapacity bm - growthLeft.toNat ≤ u`):
    - `bm = 0#64`: unallocated static empty singleton (`ctrl = pl.ρ hbEmptyCtrlSym`, `m = []`).
    - `bm ≠ 0#64`: heap-allocated SwissTable satisfying `SwissTableInv` with `A.Block allocPtr (17 * buckets + 8) 8`,
      downward `(k, v)` array `slotsDownFrom ctrlPtr slots`, and control/mirror bytes `ctrlPtr ↦ₛ ctrl`.
    Includes duplicable `hbRodata pl` (`pointsToBytesRO`) so read/modify operations (`get`, `remove`,
    `insert`, `clear`, `len`, `is_empty`) never need a separate `.rodata` parameter. -/
def U64MapRep (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64)
    (m : Map64) (bm : BitVec 64) (u : Nat) : SepProp :=
  ⌜mapPtr.toNat % 8 = 0 ∧ mapPtr.toNat + 32 ≤ 2 ^ 64 ∧ Map64Wf m⌝ ∗
  hbRodata pl ∗
  if bm = 0#64 then
    ⌜m = []⌝ ∗
    U64MapStruct mapPtr (pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64
  else
    ∃∗ w : HbHeapMapWitness,
      ⌜SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m ∧
       bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u ∧
       w.allocPtr ≠ 0#64 ∧
       w.allocPtr.toNat % 8 = 0 ∧
       w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
       w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))⌝ ∗
      U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
      A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      slotsDownFrom w.ctrlPtr w.slots ∗
      (w.ctrlPtr ↦ₛ w.ctrl)

theorem SwissTableInv.length_le_used {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm growthLeft items ctrl slots m) :
    m.length ≤ bucketMaskToCapacity bm - growthLeft.toNat := by
  have := h.conservation; omega

theorem SwissTableInv.used_eq_length_of_sub {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm growthLeft items ctrl slots m)
    (hgl : growthLeft = bucketMaskToCapacityBV bm - items) :
    bucketMaskToCapacity bm - growthLeft.toNat = m.length := by
  have hcap_lt : bucketMaskToCapacity bm < 2 ^ 64 := (bucketMaskToCapacityBV bm).isLt
  have hmlen_le : m.length ≤ bucketMaskToCapacity bm := by have := h.conservation; omega
  have hcap_bv : bucketMaskToCapacityBV bm = BitVec.ofNat 64 (bucketMaskToCapacity bm) := by
    unfold bucketMaskToCapacity; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hgl_nat : growthLeft.toNat = bucketMaskToCapacity bm - m.length := by
    rw [hgl, h.items_eq, hcap_bv, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : m.length < 2 ^ 64), Nat.mod_eq_of_lt hcap_lt,
      show 2 ^ 64 - m.length + bucketMaskToCapacity bm = 2 ^ 64 + (bucketMaskToCapacity bm - m.length) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  omega

theorem U64MapRep_mono_u (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64)
    (m : Map64) (bm : BitVec 64) {u₁ u₂ : Nat} (hle : u₁ ≤ u₂) :
    U64MapRep pl A mapPtr m bm u₁ ⊢ U64MapRep pl A mapPtr m bm u₂ := by
  unfold U64MapRep
  by_cases hbm : bm = 0#64
  · simp only [hbm, ↓reduceIte]; exact Entails.refl _
  · simp only [hbm, ↓reduceIte]
    refine sepConj_mono_right (sepConj_mono_right (Entails.sepExists_elim fun w => ?_))
    refine Entails.sepExists_right w (Entails.pure_left ?_)
    rintro ⟨hinv, hu, h1, h2, h3, h4⟩
    exact Entails.pure_right ⟨hinv, Nat.le_trans hu hle, h1, h2, h3, h4⟩ (Entails.refl _)

theorem U64MapRep_init (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (u : Nat := 0) :
    hbRodata pl ∗ U64MapStruct mapPtr (pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64 ⊢
      U64MapRep pl A mapPtr [] 0#64 u ∗ hbRodata pl := by
  unfold U64MapRep
  simp only [↓reduceIte]
  refine Entails.trans (sepConj_mono_left (hbRodata_dup pl)) ?_
  have h1 :
      (hbRodata pl ∗ hbRodata pl) ∗ U64MapStruct mapPtr (pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64 =
        (hbRodata pl ∗ U64MapStruct mapPtr (pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64) ∗ hbRodata pl := by
    ac_rfl
  rw [h1]
  refine sepConj_mono_left ?_
  have hpure : mapPtr.toNat % 8 = 0 ∧ mapPtr.toNat + 32 ≤ 2 ^ 64 ∧ Map64Wf ([] : Map64) :=
    ⟨hal, hnw, Map64Wf.nil⟩
  refine Entails.pure_right hpure ?_
  apply sepConj_mono_right
  exact Entails.pure_right trivial (Entails.refl _)

end CaseStudies.Hashbrown.Proofs
