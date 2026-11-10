/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Defs

/-!
# Relocatable Hashbrown Library Specifications

Placement-generic Hoare `Spec` contracts for the `hashbrown` v0.17.1 exports and internal
`reserve_rehash` routine over arbitrary `Obj.Placement` and `HbAlloc`, together with capacity-mask
progression (`capToBucketMask`, `nextResizeMask`, `ValidNextMask`) and the ready-to-insert state
predicate `U64MapRepReady`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

/-! ## Capacity-mask progression and growth bounds -/

/-- `bucket_mask` selected by `capacity_to_buckets` for `0 ≤ cap ≤ MaxHashbrownCapacity`:
`0#64` when `cap = 0`, `3#64` for `1 ≤ cap < 4`, `7#64` for `4 ≤ cap < 8`, `15#64` for
`8 ≤ cap < 15`, and `2 ^ (Nat.log2 ((cap * 8) / 7 - 1) + 1) - 1` for `cap ≥ 15`. -/
def capToBucketMask (cap : Nat) : BitVec 64 :=
  if cap = 0 then 0#64
  else if cap < 4 then 3#64
  else if cap < 8 then 7#64
  else if cap < 15 then 15#64
  else
    let adj := (cap * 8) / 7
    BitVec.ofNat 64 (2 ^ (Nat.log2 (adj - 1) + 1) - 1)

/-- Next `bucket_mask` chosen when `reserve_rehash` grows the table: `3#64` from `0#64`, or
`2 * (bm + 1) - 1` when `bm ≠ 0#64`. -/
def nextResizeMask (bm : BitVec 64) : BitVec 64 :=
  if bm = 0#64 then 3#64
  else BitVec.ofNat 64 (2 * (bm.toNat + 1) - 1)

@[simp] theorem nextResizeMask_zero : nextResizeMask 0#64 = 3#64 := rfl

theorem ValidBucketMask.nextResizeMask_valid {bm : BitVec 64}
    (hv : ValidBucketMask bm) (hcap : bucketMaskToCapacity bm < MaxHashbrownCapacity) :
    ValidBucketMask (nextResizeMask bm) ∧
    (nextResizeMask bm).toNat + 1 = 2 * (bm.toNat + 1) := by
  have hbm_ne : bm ≠ 0#64 := ValidBucketMask.ne_zero hv
  rcases hv with ⟨exp, hge2, hle58, hbm_eq⟩
  have hexp_lt58 : exp < 58 := by
    by_cases h58 : exp = 58
    · subst h58
      have hcap58 : bucketMaskToCapacity (BitVec.ofNat 64 (2 ^ 58 - 1)) = MaxHashbrownCapacity := by
        decide
      rw [hbm_eq, hcap58] at hcap
      omega
    · omega
  have hpow58 : 2 ^ 58 < 2 ^ 64 := by decide
  have hbm_nat : bm.toNat + 1 = 2 ^ exp := ValidBucketMask.buckets_eq hge2 hle58 hbm_eq
  have hnext_eq : nextResizeMask bm = BitVec.ofNat 64 (2 ^ (exp + 1) - 1) := by
    simp only [nextResizeMask, hbm_ne, ↓reduceIte, hbm_nat]
    congr 1
    have : 2 * 2 ^ exp = 2 ^ (exp + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  refine ⟨⟨exp + 1, by omega, by omega, hnext_eq⟩, ?_⟩
  exact ValidBucketMask.buckets_eq (by omega) (by omega) hnext_eq |>.trans
    (by rw [Nat.pow_succ, Nat.mul_comm, hbm_nat])

/-- Allowed `bucket_mask` transition across `reserve_rehash` and `hashbrown_insert`: either
`bm' = bm`, or `m.length + 1 > bucketMaskToCapacity bm / 2` grows the mask to `nextResizeMask bm`. -/
def ValidNextMask (m : Map64) (bm bm' : BitVec 64) : Prop :=
  bm' = bm ∨
  (m.length + 1 > bucketMaskToCapacity bm / 2 ∧
   bucketMaskToCapacity bm < MaxHashbrownCapacity ∧
   bm' = nextResizeMask bm)

theorem ValidNextMask.buckets_le_five_mul {m : Map64} {bm bm' : BitVec 64} {k_ins : Nat}
    (hv : ValidNextMask m bm bm')
    (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm)
    (hlen : m.length ≤ k_ins)
    (hprev : bm ≠ 0#64 → bm.toNat + 1 ≤ 5 * k_ins) :
    (bm' = 0#64 ∨ ValidBucketMask bm') ∧
    (bm' ≠ 0#64 → bm'.toNat + 1 ≤ 5 * (k_ins + 1)) := by
  rcases hv with rfl | ⟨hgt, hlt_max, rfl⟩
  · exact ⟨hbm_wf, fun hne => Nat.le_trans (hprev hne) (by omega)⟩
  · rcases hbm_wf with rfl | hv_bm
    · have hv3 : ValidBucketMask 3#64 := ⟨2, by decide, by decide, rfl⟩
      refine ⟨Or.inr hv3, fun _ => ?_⟩
      change (3#64).toNat + 1 ≤ 5 * (k_ins + 1)
      have : (3#64).toNat = 3 := rfl
      omega
    · obtain ⟨hv_next, hmul2⟩ := ValidBucketMask.nextResizeMask_valid hv_bm hlt_max
      refine ⟨Or.inr hv_next, fun _ => ?_⟩
      rcases hv_bm with ⟨exp, hge2, hle58, hbm_eq⟩
      have hcap := ValidBucketMask.capacity_eq hge2 hle58 hbm_eq
      have hbkt := ValidBucketMask.buckets_eq hge2 hle58 hbm_eq
      by_cases hexp2 : exp = 2
      · subst hexp2
        simp only [↓reduceIte] at hcap
        omega
      · have hexp_ge3 : 3 ≤ exp := by omega
        simp only [hexp2, ↓reduceIte] at hcap
        have hpow_split : 2 ^ exp = 8 * 2 ^ (exp - 3) := by
          have : exp = (exp - 3) + 3 := by omega
          conv => lhs; rw [this]
          rw [Nat.pow_add]
          omega
        omega

theorem ValidNextMask.buckets_le_max_five_mul {B : Nat} {m : Map64} {bm bm' : BitVec 64}
    {k_ins : Nat}
    (hv : ValidNextMask m bm bm')
    (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm)
    (hlen : m.length ≤ k_ins)
    (hprev : bm ≠ 0#64 → bm.toNat + 1 ≤ max B (5 * k_ins)) :
    (bm' = 0#64 ∨ ValidBucketMask bm') ∧
    (bm' ≠ 0#64 → bm'.toNat + 1 ≤ max B (5 * (k_ins + 1))) := by
  rcases hv with rfl | hgrow
  · exact ⟨hbm_wf, fun hne => Nat.le_trans (hprev hne) (by omega)⟩
  · obtain ⟨hwf', hle5⟩ :=
      ValidNextMask.buckets_le_five_mul (k_ins := k_ins) (Or.inr hgrow) hbm_wf hlen
        (by
          intro _
          rcases hbm_wf with rfl | hv_bm
          · contradiction
          · rcases hv_bm with ⟨exp, hge2, hle58, hbm_eq⟩
            have hcap := ValidBucketMask.capacity_eq hge2 hle58 hbm_eq
            have hbkt := ValidBucketMask.buckets_eq hge2 hle58 hbm_eq
            have hgt := hgrow.1
            by_cases hexp2 : exp = 2
            · subst hexp2; simp only [↓reduceIte] at hcap; omega
            · simp only [hexp2, ↓reduceIte] at hcap
              have : 2 ^ exp = 8 * 2 ^ (exp - 3) := by
                conv => lhs; rw [show exp = (exp - 3) + 3 by omega, Nat.pow_add]
                omega
              omega)
    exact ⟨hwf', fun hne => Nat.le_trans (hle5 hne) (Nat.le_max_right _ _)⟩

theorem ValidNextMask.buckets_le_max_three_mul {B : Nat} {m : Map64} {bm bm' : BitVec 64}
    {k_ins : Nat} (hB : 4 ≤ B)
    (hv : ValidNextMask m bm bm' ∧ (bm' ≠ bm → bucketMaskToCapacity bm ≤ k_ins))
    (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm)
    (hprev : bm ≠ 0#64 → bm.toNat + 1 ≤ max B (3 * k_ins)) :
    (bm' = 0#64 ∨ ValidBucketMask bm') ∧
    (bm' ≠ 0#64 → bm'.toNat + 1 ≤ max B (3 * (k_ins + 1))) := by
  rcases hv with ⟨rfl | ⟨_, hlt_max, rfl⟩, hres⟩
  · exact ⟨hbm_wf, fun hne => Nat.le_trans (hprev hne) (by omega)⟩
  · rcases hbm_wf with rfl | hv_bm
    · have hv3 : ValidBucketMask 3#64 := ⟨2, by decide, by decide, rfl⟩
      refine ⟨Or.inr hv3, fun _ => ?_⟩
      change (3#64).toNat + 1 ≤ max B (3 * (k_ins + 1))
      have : (3#64).toNat = 3 := rfl
      omega
    · obtain ⟨hv_next, hmul2⟩ := ValidBucketMask.nextResizeMask_valid hv_bm hlt_max
      have hne_bm : nextResizeMask bm ≠ bm := by
        intro heq; rw [heq] at hmul2
        have := (ValidBucketMask.capacity_bounds hv_bm).2; omega
      have hcap_le := hres hne_bm
      refine ⟨Or.inr hv_next, fun _ => ?_⟩
      rcases hv_bm with ⟨exp, hge2, hle58, hbm_eq⟩
      have hcap := ValidBucketMask.capacity_eq hge2 hle58 hbm_eq
      have hbkt := ValidBucketMask.buckets_eq hge2 hle58 hbm_eq
      by_cases hexp2 : exp = 2
      · subst hexp2; simp only [↓reduceIte] at hcap; omega
      · simp only [hexp2, ↓reduceIte] at hcap
        have : 2 ^ exp = 8 * 2 ^ (exp - 3) := by
          conv => lhs; rw [show exp = (exp - 3) + 3 by omega, Nat.pow_add]
          omega
        omega

/-- Budget condition for `reserve_rehash(map, 1, _, Infallible)` to succeed without capacity
overflow or allocator failure. -/
def HbCanReserveOne (A : HbAlloc) (m : Map64) (bm : BitVec 64) (lc blk : Nat) : Prop :=
  m.length + 1 ≤ bucketMaskToCapacity bm / 2 ∨
  (bucketMaskToCapacity bm < MaxHashbrownCapacity ∧
   A.CanAlloc lc blk (tableAllocBytes (nextResizeMask bm)) 8)

/-- Budget condition for `hashbrown_insert(map, k, v)` to succeed without capacity overflow or
allocator failure. -/
def HbCanInsertOne (A : HbAlloc) (m : Map64) (bm : BitVec 64) (u lc blk : Nat) : Prop :=
  u < bucketMaskToCapacity bm ∨ HbCanReserveOne A m bm lc blk

/-- Budget condition for `hashbrown_with_capacity(cap)` to succeed without capacity overflow or
allocator failure. -/
def HbCanWithCapacity (A : HbAlloc) (cap : BitVec 64) (lc blk : Nat) : Prop :=
  cap.toNat ≤ MaxHashbrownCapacity ∧
  (cap = 0#64 ∨ A.CanAlloc lc blk (tableAllocBytes (capToBucketMask cap.toNat)) 8)

/-! ## Ready-to-insert representation -/

theorem StdStatePreserved.toAllocStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) (hfz : s0.mem.KeepsFrozen sf.mem) :
    AllocStatePreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1, hfz⟩

/-- Heap-allocated `U64Map` representation with `bm ≠ 0#64`, `0 < growthLeft.toNat`, and zero
tombstones (`growthLeft = bucketMaskToCapacityBV bm - items`), established by `reserve_rehash` on
the slow path of `hashbrown_insert`. -/
def U64MapRepReady (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64)
    (m : Map64) (bm : BitVec 64) : SepProp :=
  ⌜mapPtr.toNat % 8 = 0 ∧ mapPtr.toNat + 32 ≤ 2 ^ 64 ∧ Map64Wf m ∧ bm ≠ 0#64⌝ ∗
  hbRodata pl ∗
  ∃∗ w : HbHeapMapWitness,
    ⌜SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m ∧
     0 < w.growthLeft.toNat ∧
     w.growthLeft = bucketMaskToCapacityBV bm - w.items ∧
     w.allocPtr ≠ 0#64 ∧
     w.allocPtr.toNat % 8 = 0 ∧
     w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
     w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))⌝ ∗
    U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
    A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
    slotsDownFrom w.ctrlPtr w.slots ∗
    (w.ctrlPtr ↦ₛ w.ctrl)

theorem U64MapRepReady_entails_U64MapRep (pl : Obj.Placement) (A : HbAlloc) (mapPtr : BitVec 64)
    (m : Map64) (bm : BitVec 64) {u : Nat} (hu : m.length ≤ u) :
    U64MapRepReady pl A mapPtr m bm ⊢ U64MapRep pl A mapPtr m bm u := by
  unfold U64MapRepReady U64MapRep
  apply Entails.pure_left
  rintro ⟨hal, hnw, hwf, hbm_ne⟩
  simp only [hbm_ne, ↓reduceIte]
  refine Entails.pure_right ⟨hal, hnw, hwf⟩ ?_
  apply sepConj_mono_right
  apply Entails.sepExists_elim
  intro w
  refine Entails.sepExists_right w ?_
  apply Entails.pure_left
  rintro ⟨hinv, _, hgl_eq, hne, hal_a, hnw_a, hctrl⟩
  have hused : bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u := by
    rw [hinv.used_eq_length_of_sub hgl_eq]; exact hu
  exact Entails.pure_right ⟨hinv, hused, hne, hal_a, hnw_a, hctrl⟩ (Entails.refl _)

theorem U64MapRepReady_init {pl : Obj.Placement} {A : HbAlloc} {mapPtr allocPtr : BitVec 64}
    {bm : BitVec 64} {slots : List (BitVec 64 × BitVec 64)}
    (hbm : ValidBucketMask bm)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (ha_ne : allocPtr ≠ 0#64) (ha_al : allocPtr.toNat % 8 = 0)
    (ha_nw : allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hsl : slots.length = bm.toNat + 1) :
    let ctrlPtr := allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))
    let gl := bucketMaskToCapacityBV bm
    hbRodata pl ∗
      U64MapStruct mapPtr ctrlPtr bm gl 0#64 ∗
      A.Block allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      slotsDownFrom ctrlPtr slots ∗
      (ctrlPtr ↦ₛ List.replicate (bm.toNat + 9) tagEmpty) ⊢
      U64MapRepReady pl A mapPtr [] bm := by
  intro ctrlPtr gl
  have hbm_ne : bm ≠ 0#64 := ValidBucketMask.ne_zero hbm
  have hinv : SwissTableInv bm gl 0#64 (List.replicate (bm.toNat + 9) tagEmpty) slots [] :=
    SwissTableInv_init_of_mask hbm hsl
  have hgl_pos : 0 < gl.toNat := by
    change 0 < bucketMaskToCapacity bm
    have := (ValidBucketMask.capacity_bounds hbm).1
    omega
  unfold U64MapRepReady
  refine Entails.pure_right ⟨hal, hnw, Map64Wf.nil, hbm_ne⟩ ?_
  apply sepConj_mono_right
  let w : HbHeapMapWitness :=
    { allocPtr := allocPtr
      ctrlPtr := ctrlPtr
      growthLeft := gl
      items := 0#64
      ctrl := List.replicate (bm.toNat + 9) tagEmpty
      slots := slots }
  refine Entails.sepExists_right w ?_
  exact Entails.pure_right ⟨hinv, hgl_pos, by dsimp [w, gl]; rw [BitVec.sub_zero], ha_ne, ha_al, ha_nw, rfl⟩
    (Entails.refl _)

/-! ## Subroutine specifications -/

/-- `hashbrown_new() -> U64Map` (indirect return via `x8 = mapPtr`, `0` stack bytes). -/
def hashbrownNewSpec (pl : Obj.Placement) (A : HbAlloc) : Spec (BitVec 64) where
  pre := fun mapPtr s0 =>
    ⌜s0.readReg64 .x8 = mapPtr ∧ mapPtr.toNat % 8 = 0 ∧ mapPtr.toNat + 32 ≤ 2 ^ 64⌝ ∗
    hbRodata pl ∗
    memRegion mapPtr 32
  post := fun mapPtr s0 sf =>
    ⌜sf.readReg64 .x8 = mapPtr ∧ StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
    U64MapRep pl A mapPtr [] 0#64 0 ∗
    hbRodata pl
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `hashbrown_len(map: &U64Map) -> usize` (`0` stack bytes). -/
def hashbrownLenSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat) where
  pre := fun (mapPtr, m, bm, u) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr⌝ ∗
    U64MapRep pl A mapPtr m bm u
  post := fun (mapPtr, m, bm, u) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 m.length ∧
      StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
    U64MapRep pl A mapPtr m bm u
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `hashbrown_is_empty(map: &U64Map) -> bool` (`0` stack bytes). -/
def hashbrownIsEmptySpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat) where
  pre := fun (mapPtr, m, bm, u) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr⌝ ∗
    U64MapRep pl A mapPtr m bm u
  post := fun (mapPtr, m, bm, u) s0 sf =>
    ⌜sf.readReg64 .x0 = (if m.isEmpty then 1#64 else 0#64) ∧
      StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
    U64MapRep pl A mapPtr m bm u
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `hashbrown_get(map: &U64Map, k: u64) -> Option<u64>` (`0` stack bytes). -/
def hashbrownGetSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × BitVec 64) where
  pre := fun (mapPtr, m, bm, u, k) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr ∧ s0.readReg64 .x1 = k⌝ ∗
    U64MapRep pl A mapPtr m bm u
  post := fun (mapPtr, m, bm, u, k) s0 sf =>
    ⌜(match cliMapLookup k m with
      | none   => sf.readReg64 .x0 = 0#64
      | some v => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = v) ∧
      StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
    U64MapRep pl A mapPtr m bm u
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `hashbrown_contains_key(map: &U64Map, k: u64) -> bool` (`0` stack bytes). -/
def hashbrownContainsKeySpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × BitVec 64) where
  pre := fun (mapPtr, m, bm, u, k) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr ∧ s0.readReg64 .x1 = k⌝ ∗
    U64MapRep pl A mapPtr m bm u
  post := fun (mapPtr, m, bm, u, k) s0 sf =>
    ⌜sf.readReg64 .x0 = (if (cliMapLookup k m).isSome then 1#64 else 0#64) ∧
      StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
    U64MapRep pl A mapPtr m bm u
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `hashbrown_remove(map: &mut U64Map, k: u64) -> Option<u64>` (`0` stack bytes). -/
def hashbrownRemoveSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × BitVec 64) where
  pre := fun (mapPtr, m, bm, u, k) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr ∧ s0.readReg64 .x1 = k⌝ ∗
    U64MapRep pl A mapPtr m bm u
  post := fun (mapPtr, m, bm, u, k) s0 sf =>
    ⌜(match cliMapLookup k m with
      | none   => sf.readReg64 .x0 = 0#64
      | some v => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = v) ∧
      StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
    U64MapRep pl A mapPtr (cliMapErase k m) bm u
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `hashbrown_clear(map: &mut U64Map)` (`32` stack bytes; calls `memset` when `items > 0`). -/
def hashbrownClearSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat) where
  pre := fun (mapPtr, m, bm, u) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr⌝ ∗
    U64MapRep pl A mapPtr m bm u ∗
    stackAt s0.sp 32
  post := fun (mapPtr, _, bm, u) s0 sf =>
    ⌜StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗
    U64MapRep pl A mapPtr [] bm u ∗
    stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `hashbrown_drop(map: U64Map)` (indirect by-value pointer in `x0`, tail-calls `___rust_dealloc`
    using `A.stackBytes` stack bytes when `bm ≠ 0#64`). -/
def hashbrownDropSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × Nat × Nat) where
  pre := fun (mapPtr, m, bm, u, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr⌝ ∗
    U64MapRep pl A mapPtr m bm u ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp A.stackBytes
  post := fun (mapPtr, _, bm, _, lc, blk) s0 sf =>
    ⌜AllocStatePreserved s0 sf⌝ ∗
    memRegion mapPtr 32 ∗
    hbRodata pl ∗
    A.Heap (lc - hbMapCost A bm) (blk - tableAllocBlocks bm) sf ∗
    stackAt s0.sp A.stackBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Strong in-budget `hashbrown_with_capacity(cap) -> U64Map` (`onPanic = ⌜False⌝` under
    `HbCanWithCapacity A cap lc blk`; `80 + A.stackBytes` stack bytes). -/
def hashbrownWithCapacityInfallibleSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (mapPtr, cap, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = cap ∧
      s0.readReg64 .x8 = mapPtr ∧
      mapPtr.toNat % 8 = 0 ∧
      mapPtr.toNat + 32 ≤ 2 ^ 64 ∧
      A.stackBytes + 80 ≤ 2 ^ 64 ∧
      HbCanWithCapacity A cap lc blk⌝ ∗
    hbRodata pl ∗
    memRegion mapPtr 32 ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp (80 + A.stackBytes)
  post := fun (mapPtr, cap, lc, blk) s0 sf =>
    let bm := capToBucketMask cap.toNat
    ⌜AllocStatePreserved s0 sf⌝ ∗
    hbRodata pl ∗
    U64MapRep pl A mapPtr [] bm 0 ∗
    A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sf ∗
    stackAt s0.sp (80 + A.stackBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜A.allowOom⌝

/-- General `hashbrown_with_capacity(cap) -> U64Map` allowing `capacity_overflow` / `alloc_err`
    panics when `A.allowOom` holds and `¬ HbCanWithCapacity A cap lc blk`. -/
def hashbrownWithCapacitySpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (mapPtr, cap, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = cap ∧
      s0.readReg64 .x8 = mapPtr ∧
      mapPtr.toNat % 8 = 0 ∧
      mapPtr.toNat + 32 ≤ 2 ^ 64 ∧
      A.stackBytes + 80 ≤ 2 ^ 64 ∧
      (¬ A.allowOom → HbCanWithCapacity A cap lc blk)⌝ ∗
    hbRodata pl ∗
    memRegion mapPtr 32 ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp (80 + A.stackBytes)
  post := fun (mapPtr, cap, lc, blk) s0 sf =>
    let bm := capToBucketMask cap.toNat
    ⌜AllocStatePreserved s0 sf⌝ ∗
    hbRodata pl ∗
    U64MapRep pl A mapPtr [] bm 0 ∗
    A.Heap (lc + hbMapCost A bm) (blk + tableAllocBlocks bm) sf ∗
    stackAt s0.sp (80 + A.stackBytes)
  onPanic := fun (_, cap, lc, blk) _ _ => ⌜A.allowOom ∧ ¬ HbCanWithCapacity A cap lc blk⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜A.allowOom⌝

/-- Strong in-budget contract for `reserve_rehash(map, additional = 1, _, fallibility = 1)`
    (`onPanic = ⌜False⌝` under `HbCanReserveOne A m bm lc blk`; `112 + A.stackBytes` stack bytes),
    establishing `U64MapRepReady` (`bm' ≠ 0#64` and `0 < growthLeft.toNat`). -/
def hashbrownReserveRehashOneInfallibleSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × Nat × Nat) where
  pre := fun (mapPtr, m, bm, u, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr ∧
      s0.readReg64 .x1 = 1#64 ∧
      s0.readReg32 .x3 = 1#32 ∧
      A.stackBytes + 112 ≤ 2 ^ 64 ∧
      HbCanReserveOne A m bm lc blk⌝ ∗
    U64MapRep pl A mapPtr m bm u ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp (112 + A.stackBytes)
  post := fun (mapPtr, m, bm, _, lc, blk) s0 sf =>
    ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
    stackAt s0.sp (112 + A.stackBytes) ∗
    (∃∗ bm' : BitVec 64,
      ⌜ValidNextMask m bm bm'⌝ ∗
      U64MapRepReady pl A mapPtr m bm' ∗
      A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
             ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sf)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜A.allowOom⌝

/-- General contract for `reserve_rehash(map, additional = 1, _, fallibility = 1)` allowing
    `capacity_overflow` / `alloc_err` panics when `A.allowOom` holds and `¬ HbCanReserveOne`. -/
def hashbrownReserveRehashOneSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × Nat × Nat) where
  pre := fun (mapPtr, m, bm, u, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr ∧
      s0.readReg64 .x1 = 1#64 ∧
      s0.readReg32 .x3 = 1#32 ∧
      A.stackBytes + 112 ≤ 2 ^ 64 ∧
      (¬ A.allowOom → HbCanReserveOne A m bm lc blk)⌝ ∗
    U64MapRep pl A mapPtr m bm u ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp (112 + A.stackBytes)
  post := fun (mapPtr, m, bm, _, lc, blk) s0 sf =>
    ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
    stackAt s0.sp (112 + A.stackBytes) ∗
    (∃∗ bm' : BitVec 64,
      ⌜ValidNextMask m bm bm'⌝ ∗
      U64MapRepReady pl A mapPtr m bm' ∗
      A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
             ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sf)
  onPanic := fun (_, m, bm, _, lc, blk) _ _ => ⌜A.allowOom ∧ ¬ HbCanReserveOne A m bm lc blk⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜A.allowOom⌝

/-- Strong in-budget `hashbrown_insert(map, k, v) -> Option<u64>` (`onPanic = ⌜False⌝` under
    `HbCanInsertOne A m bm u lc blk`; `176 + A.stackBytes` stack bytes). -/
def hashbrownInsertInfallibleSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (mapPtr, m, bm, u, k, v, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr ∧
      s0.readReg64 .x1 = k ∧
      s0.readReg64 .x2 = v ∧
      A.stackBytes + 176 ≤ 2 ^ 64 ∧
      HbCanInsertOne A m bm u lc blk⌝ ∗
    U64MapRep pl A mapPtr m bm u ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp (176 + A.stackBytes)
  post := fun (mapPtr, m, bm, u, k, v, lc, blk) s0 sf =>
    ⌜(match cliMapLookup k m with
      | none      => sf.readReg64 .x0 = 0#64
      | some oldV => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = oldV) ∧
      AllocStatePreserved s0 sf⌝ ∗
    stackAt s0.sp (176 + A.stackBytes) ∗
    (∃∗ bm' : BitVec 64,
      ⌜ValidNextMask m bm bm' ∧ (bm' ≠ bm → bucketMaskToCapacity bm ≤ u)⌝ ∗
      U64MapRep pl A mapPtr (cliMapInsert k v m) bm' (u + 1) ∗
      A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
             ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sf)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜A.allowOom⌝

/-- General `hashbrown_insert(map, k, v) -> Option<u64>` allowing `capacity_overflow` / `alloc_err`
    panics when `A.allowOom` holds and `¬ HbCanInsertOne A m bm u lc blk`. -/
def hashbrownInsertSpec (pl : Obj.Placement) (A : HbAlloc) :
    Spec (BitVec 64 × Map64 × BitVec 64 × Nat × BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (mapPtr, m, bm, u, k, v, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = mapPtr ∧
      s0.readReg64 .x1 = k ∧
      s0.readReg64 .x2 = v ∧
      A.stackBytes + 176 ≤ 2 ^ 64 ∧
      (¬ A.allowOom → HbCanInsertOne A m bm u lc blk)⌝ ∗
    U64MapRep pl A mapPtr m bm u ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp (176 + A.stackBytes)
  post := fun (mapPtr, m, bm, u, k, v, lc, blk) s0 sf =>
    ⌜(match cliMapLookup k m with
      | none      => sf.readReg64 .x0 = 0#64
      | some oldV => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = oldV) ∧
      AllocStatePreserved s0 sf⌝ ∗
    stackAt s0.sp (176 + A.stackBytes) ∗
    (∃∗ bm' : BitVec 64,
      ⌜ValidNextMask m bm bm' ∧ (bm' ≠ bm → bucketMaskToCapacity bm ≤ u)⌝ ∗
      U64MapRep pl A mapPtr (cliMapInsert k v m) bm' (u + 1) ∗
      A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
             ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sf)
  onPanic := fun (_, m, bm, u, _, _, lc, blk) _ _ => ⌜A.allowOom ∧ ¬ HbCanInsertOne A m bm u lc blk⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜A.allowOom⌝

end CaseStudies.Hashbrown.Proofs
