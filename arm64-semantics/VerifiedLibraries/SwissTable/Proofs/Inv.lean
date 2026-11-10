/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.SwissTable.Proofs.Probe

/-!
# Generic SwissTable Representation Invariant

Defines `SwissTableInv hashOf keyOf bm growthLeft items ctrl slots S` over slot type `α`, relating
raw table fields `(bucket_mask, growth_left, items)`, control bytes `ctrl[0 .. buckets + 8)`, and
bucket slots `slots[0 .. buckets)` to the abstract contents `S : List α` with pairwise-distinct keys
`keyOf` probed at `hashOf`. Proves initialization (`init_of_mask`), probe-loop termination
(`exists_empty_slot`, `exists_empty_probe_group`), full-lane membership (`mem_of_lane_full`,
`mem_of_lane_match`), and miss soundness upon reaching an empty group (`not_mem_of_probe_empty`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.SwissTable

open Arm64 ProofLib

/-- Pure SwissTable invariant over slot type `α`, relating `(bm, growthLeft, items, ctrl, slots)`
    to the abstract contents `S`. `hashOf x` is the 64-bit hash used to probe slot value `x`, and
    `keyOf x` is its identity for uniqueness (keys of `S` are pairwise distinct). -/
structure SwissTableInv {α κ : Type} (hashOf : α → BitVec 64) (keyOf : α → κ)
    (bm growthLeft items : BitVec 64)
    (ctrl : List (BitVec 8)) (slots : List α) (S : List α) : Prop where
  validMask : ValidBucketMask bm
  wf : (S.map keyOf).Nodup
  slots_len : slots.length = bm.toNat + 1
  mirror : CtrlMirrorInv (bm.toNat + 1) ctrl
  items_eq : items = BitVec.ofNat 64 S.length
  growth_le : growthLeft.toNat ≤ bucketMaskToCapacity bm
  conservation :
    S.length + ((ctrl.take (bm.toNat + 1)).countP (· == tagDeleted)) + growthLeft.toNat =
      bucketMaskToCapacity bm
  countFull_eq :
    ((ctrl.take (bm.toNat + 1)).countP isFullTag) = S.length
  full_sound :
    ∀ (i : Nat) (hi : i < bm.toNat + 1),
      isFullTag (ctrl[i]'(by have := mirror.1; omega)) = true →
        ctrl[i]'(by have := mirror.1; omega) = tagOfHash (hashOf (slots[i]'(by omega))) ∧
        slots[i]'(by omega) ∈ S ∧
        ProbeReachable bm ctrl (hashOf (slots[i]'(by omega))) i
  full_inj :
    ∀ (i j : Nat) (hi : i < bm.toNat + 1) (hj : j < bm.toNat + 1),
      isFullTag (ctrl[i]'(by have := mirror.1; omega)) = true →
      isFullTag (ctrl[j]'(by have := mirror.1; omega)) = true →
      keyOf (slots[i]'(by omega)) = keyOf (slots[j]'(by omega)) →
      i = j
  complete :
    ∀ x ∈ S,
      ∃ (i : Nat) (hi : i < bm.toNat + 1),
        isFullTag (ctrl[i]'(by have := mirror.1; omega)) = true ∧
        slots[i]'(by omega) = x

namespace SwissTableInv

variable {α κ : Type} {hashOf : α → BitVec 64} {keyOf : α → κ}

theorem buckets_cases_of_mask {bm : BitVec 64} (hbm : ValidBucketMask bm) :
    bm.toNat + 1 = 4 ∨ 8 ≤ bm.toNat + 1 := by
  obtain ⟨exp, hlo, hhi, heq⟩ := hbm
  rw [ValidBucketMask.buckets_eq hlo hhi heq]
  by_cases he : exp = 2
  · subst he; left; decide
  · right
    have hge3 : 3 ≤ exp := by omega
    exact Nat.le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by decide) hge3)

/-- Every freshly allocated zero-item table with `ctrl = replicate (buckets + 8) 0xff` satisfies
    `SwissTableInv` with empty contents. -/
theorem init_of_mask {bm : BitVec 64} (hbm : ValidBucketMask bm)
    {slots : List α} (hsl : slots.length = bm.toNat + 1) :
    SwissTableInv hashOf keyOf bm (bucketMaskToCapacityBV bm) 0#64
      (List.replicate (bm.toNat + 1 + 8) tagEmpty) slots [] := by
  have hmir := CtrlMirrorInv_init (bm.toNat + 1) (buckets_cases_of_mask hbm)
  have htake : (List.replicate (bm.toNat + 1 + 8) tagEmpty).take (bm.toNat + 1) =
      List.replicate (bm.toNat + 1) tagEmpty := by
    rw [List.take_replicate, Nat.min_eq_left (by omega)]
  refine
    { validMask := hbm
      wf := List.nodup_nil
      slots_len := hsl
      mirror := hmir
      items_eq := rfl
      growth_le := Nat.le_refl _
      conservation := by
        rw [htake]
        have hc : (List.replicate (bm.toNat + 1) tagEmpty).countP (· == tagDeleted) = 0 := by
          rw [List.countP_eq_zero]
          intro b hb
          rw [List.mem_replicate] at hb
          rw [hb.2]
          decide
        rw [hc]
        simp [bucketMaskToCapacity]
      countFull_eq := by
        rw [htake]
        change (List.replicate (bm.toNat + 1) tagEmpty).countP isFullTag = 0
        rw [List.countP_eq_zero]
        intro b hb
        rw [List.mem_replicate] at hb
        rw [hb.2]
        decide
      full_sound := by
        intro i _ hf
        simp [List.getElem_replicate] at hf
      full_inj := by
        intro i _ _ _ hf _ _
        simp [List.getElem_replicate] at hf
      complete := by
        intro x hx
        simp at hx }

private theorem length_le_countP_or {xs : List (BitVec 8)} {p q : BitVec 8 → Bool}
    (hall : ∀ x ∈ xs, (p x || q x) = true) :
    xs.length ≤ xs.countP p + xs.countP q := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hx := hall x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => hall y (List.mem_cons_of_mem _ hy))
    simp only [List.length_cons, List.countP_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- Every valid SwissTable has at least one `tagEmpty` (`0xff#8`) in `ctrl[0 .. buckets)`. -/
theorem exists_empty_slot {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots S : List α}
    (h : SwissTableInv hashOf keyOf bm growthLeft items ctrl slots S) :
    ∃ (i : Nat) (_ : i < bm.toNat + 1),
      ctrl[i]'(by have := h.mirror.1; omega) = tagEmpty := by
  let buckets := bm.toNat + 1
  let pfx := ctrl.take buckets
  have hcap_lt : bucketMaskToCapacity bm < buckets := (h.validMask.capacity_bounds).2
  apply Classical.byContradiction
  intro hno
  have hall : ∀ x ∈ pfx, (isFullTag x || (x == tagDeleted)) = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hpfx_len : pfx.length = buckets := by
      simp [pfx, buckets, h.mirror.1]
    have hi_b : i < buckets := by omega
    have hget_eq : pfx[i] = ctrl[i]'(by have := h.mirror.1; omega) := by
      simp [pfx, List.getElem_take]
    have hvt : ValidTag (ctrl[i]'(by have := h.mirror.1; omega)) :=
      h.mirror.2.1 _ (List.getElem_mem _)
    have hne : ctrl[i]'(by have := h.mirror.1; omega) ≠ tagEmpty := fun he => hno ⟨i, hi_b, he⟩
    rw [hget_eq]
    rcases hvt with heq | hdel | hlt
    · exact False.elim (hne heq)
    · rw [hdel]; simp
    · rw [(isFullTag_iff_lt_0x80 _).mpr hlt]; rfl
  have hpfx_len : pfx.length = buckets := by
    simp [pfx, buckets, h.mirror.1]
  have hsum : pfx.length ≤ pfx.countP isFullTag + pfx.countP (· == tagDeleted) :=
    length_le_countP_or hall
  have hcons := h.conservation
  have hfull := h.countFull_eq
  change S.length + pfx.countP (· == tagDeleted) + growthLeft.toNat =
    bucketMaskToCapacity bm at hcons
  change pfx.countP isFullTag = S.length at hfull
  omega

/-- The probe chain of every hash reaches a group containing `tagEmpty` within
    `numGroups bm` steps (probe-loop termination). -/
theorem exists_empty_probe_group {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots S : List α}
    (h : SwissTableInv hashOf keyOf bm gl items ctrl slots S) (hv : BitVec 64) :
    ∃ step < numGroups bm, tagEmpty ∈ ctrlGroupAt ctrl (probePos bm hv step) :=
  exists_empty_probe_group_of_empty_slot h.validMask h.mirror h.exists_empty_slot hv

theorem items_eq_zero_iff_nil {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots S : List α}
    (h : SwissTableInv hashOf keyOf bm gl items ctrl slots S) :
    items = 0#64 ↔ S = [] := by
  rcases h.validMask.buckets_bounds_dvd with ⟨_, hb58, _⟩
  have h58 : 2 ^ 58 < 2 ^ 64 := by decide
  have hcap := (h.validMask.capacity_bounds).2
  have hcons := h.conservation
  have hlt : S.length < 2 ^ 64 := by omega
  rw [h.items_eq]
  constructor
  · intro hz
    have h0 := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h0
    exact List.eq_nil_iff_length_eq_zero.2 h0
  · rintro rfl; rfl

/-- A full lane `j` of the group at `pos < buckets` holds a member of `S`. -/
theorem mem_of_lane_full {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots S : List α}
    (h : SwissTableInv hashOf keyOf bm gl items ctrl slots S) {pos j : Nat}
    (hpos : pos < bm.toNat + 1) (hj : j < 8)
    (hfull_lane : isFullTag (getLane8 (ctrlGroupWord ctrl pos) j) = true) :
    slots[(pos + j) % (bm.toNat + 1)]'(by
      have hsl := h.slots_len; have := Nat.mod_lt (pos + j) (by omega : 0 < bm.toNat + 1); omega)
      ∈ S := by
  have hidx_lt : (pos + j) % (bm.toNat + 1) < bm.toNat + 1 := Nat.mod_lt _ (by omega)
  have hctrl := CtrlMirrorInv.lane_full_eq_mod h.validMask h.mirror hpos hj hfull_lane
  have hfull_ctrl : isFullTag (ctrl[(pos + j) % (bm.toNat + 1)]'(by
      have := h.mirror.1; omega)) = true := by
    rw [← hctrl]; exact hfull_lane
  exact (h.full_sound _ hidx_lt hfull_ctrl).2.1

/-- If lane `j` of the group at `pos < buckets` holds the full tag of hash `hv`, then that slot
    holds a member of `S`. -/
theorem mem_of_lane_match {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots S : List α}
    (h : SwissTableInv hashOf keyOf bm gl items ctrl slots S) {hv : BitVec 64} {pos j : Nat}
    (hpos : pos < bm.toNat + 1) (hj : j < 8)
    (htag : getLane8 (ctrlGroupWord ctrl pos) j = tagOfHash hv) :
    slots[(pos + j) % (bm.toNat + 1)]'(by
      have hsl := h.slots_len; have := Nat.mod_lt (pos + j) (by omega : 0 < bm.toNat + 1); omega)
      ∈ S :=
  h.mem_of_lane_full hpos hj (by rw [htag]; exact isFullTag_tagOfHash hv)

/-- If the probe chain of `hashOf x` reaches a group containing `tagEmpty` at `step`, and no
    lane matching `tagOfHash (hashOf x)` on steps `≤ step` holds a slot with key `keyOf x`, then
    `x ∉ S`. -/
theorem not_mem_of_probe_empty {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots S : List α}
    (h : SwissTableInv hashOf keyOf bm gl items ctrl slots S) {x : α} {step : Nat}
    (hemp : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm (hashOf x) step))
    (hmiss : ∀ s ≤ step, ∀ j < 8,
      getLane8 (ctrlGroupWord ctrl (probePos bm (hashOf x) s)) j = tagOfHash (hashOf x) →
      keyOf (slots[(probePos bm (hashOf x) s + j) % (bm.toNat + 1)]'(by
        have hsl := h.slots_len
        have := Nat.mod_lt (probePos bm (hashOf x) s + j) (by omega : 0 < bm.toNat + 1)
        omega)) ≠ keyOf x) :
    x ∉ S := by
  intro hx
  rcases h.complete x hx with ⟨i, hi, hfull_i, hslot_i⟩
  have hreach := (h.full_sound i hi hfull_i).2.2
  rw [hslot_i] at hreach
  rcases hreach with ⟨s_k, j_k, _, hj_k, hgrp, hidx, hno_emp⟩
  have hs_le : s_k ≤ step :=
    Classical.byContradiction fun hgt => hno_emp step (by omega) hemp
  have hpos_lt := probePos_lt_buckets h.validMask (hashOf x) s_k
  have hlen := h.mirror.1
  rw [ctrlGroupAt_getElem? (by omega) hj_k] at hgrp
  injection hgrp with htag
  have hne := hmiss s_k hs_le j_k hj_k htag
  simp [hidx, hslot_i] at hne

end SwissTableInv

end VerifiedLibraries.SwissTable
