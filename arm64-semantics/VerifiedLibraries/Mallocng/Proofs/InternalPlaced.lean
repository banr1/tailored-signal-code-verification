/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedCode
public import VerifiedLibraries.Mallocng.Proofs.Internal
public import VerifiedLibraries.Mallocng.Proofs.Accounting
public import VerifiedLibraries.Mallocng.Proofs.AllocMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.Cost.Reserve

/-!
# Multi-Block Placed Core Subroutine Contracts

Defines per-call `peakCount` byte-delta budgets (`allocMetaPlacedByteBound`,
`allocSlotPlacedByteBound`, `MallocngTightStepBound`, `MallocngTightTotalBound`), composable placed
out-of-memory conditions (`MallocngPlacedOomCond`, `MallocngTightOomCond`), placed core subroutine
contract statements (`AllocMetaPlacedStmt`, `AllocSlotPlacedStmt`, `LibcMallocImplPlacedStmt`,
`DefaultMallocPlacedStmt`, `LibcFreePlacedStmt`, `LibcReallocPlacedStmt`), cross-block caller lifts,
and tight C specifications (`mallocng*TightSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.CType Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `peakCount` Step-Delta Byte Bounds and Placed OOM Conditions -/

/-- Tight per-call newly-mapped byte budget for `__malloc_alloc_meta()` indexed by `peakCount`
    (`180224 + 325 * peakCount = Cost.mallocngMetaStep peakCount`). -/
def allocMetaPlacedByteBound (peakCount : Nat) : Nat :=
  180224 + 325 * peakCount

theorem allocMetaPlacedByteBound_eq_metaStep (peakCount : Nat) :
    allocMetaPlacedByteBound peakCount = Cost.mallocngMetaStep peakCount := rfl

/-- Tight inductive newly-mapped byte budget for `alloc_slot(sc, req)` across recursion depth
    `allocSlotDepthBound sc ≤ 3`: one `__malloc_alloc_meta()` per level plus one root-group `mmap`
    of `≤ Cost.mallocngRootGroupBoundAt peakCount` bytes (`≤ Cost.mallocngSlotReserve`). -/
def allocSlotPlacedByteBound (sc peakCount : Nat) : Nat :=
  (allocSlotDepthBound sc + 1) * allocMetaPlacedByteBound peakCount +
    Cost.mallocngRootGroupBoundAt peakCount

theorem allocMetaPlacedByteBound_le_allocSlot (sc peakCount : Nat) :
    allocMetaPlacedByteBound peakCount ≤ allocSlotPlacedByteBound sc peakCount := by
  unfold allocSlotPlacedByteBound
  have hmul : 1 * allocMetaPlacedByteBound peakCount ≤
      (allocSlotDepthBound sc + 1) * allocMetaPlacedByteBound peakCount :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem allocSlotPlacedByteBound_root_add {sc peakCount len : Nat}
    (hlen : len ≤ Cost.mallocngRootGroupBoundAt peakCount) :
    allocMetaPlacedByteBound peakCount + len ≤ allocSlotPlacedByteBound sc peakCount := by
  have h := allocMetaPlacedByteBound_le_allocSlot sc peakCount
  unfold allocSlotPlacedByteBound at *
  have hmul : 1 * allocMetaPlacedByteBound peakCount ≤
      (allocSlotDepthBound sc + 1) * allocMetaPlacedByteBound peakCount :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem allocSlotPlacedByteBound_ge_len {sc peakCount len : Nat}
    (hlen : len ≤ Cost.mallocngRootGroupBoundAt peakCount) :
    len ≤ allocSlotPlacedByteBound sc peakCount :=
  Nat.le_trans (Nat.le_add_left _ _) (allocSlotPlacedByteBound_root_add (sc := sc) hlen)

theorem allocSlotPlacedByteBound_nested_add {sc pSc peakCount : Nat}
    (hdepth : allocSlotDepthBound pSc + 1 ≤ allocSlotDepthBound sc) :
    allocMetaPlacedByteBound peakCount + allocSlotPlacedByteBound pSc peakCount ≤
      allocSlotPlacedByteBound sc peakCount := by
  unfold allocSlotPlacedByteBound
  have hmul := Nat.mul_le_mul_right (allocMetaPlacedByteBound peakCount)
    (by omega : allocSlotDepthBound pSc + 2 ≤ allocSlotDepthBound sc + 1)
  have hexp : (allocSlotDepthBound pSc + 2) * allocMetaPlacedByteBound peakCount =
      (allocSlotDepthBound pSc + 1) * allocMetaPlacedByteBound peakCount +
        allocMetaPlacedByteBound peakCount :=
    Nat.succ_mul (allocSlotDepthBound pSc + 1) _
  omega

theorem allocSlotPlacedByteBound_le_slotReserve (sc peakCount : Nat) :
    allocSlotPlacedByteBound sc peakCount ≤
      Cost.mallocngSlotReserve (Cost.mallocngRootGroupBoundAt peakCount) peakCount := by
  have hd := allocSlotDepthBound_le_three sc
  unfold allocSlotPlacedByteBound Cost.mallocngSlotReserve
  rw [← allocMetaPlacedByteBound_eq_metaStep]
  have hmul : (allocSlotDepthBound sc + 1) * allocMetaPlacedByteBound peakCount ≤
      4 * allocMetaPlacedByteBound peakCount :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem allocSlotPlacedByteBound_le_overhead (sc peakCount : Nat) :
    allocSlotPlacedByteBound sc peakCount ≤ MallocngBaseOverhead + 4096 * peakCount := by
  have h := allocSlotPlacedByteBound_le_slotReserve sc peakCount
  have hG := Cost.mallocngRootGroupBoundAt_le peakCount
  unfold Cost.mallocngSlotReserve Cost.mallocngMetaStep at h
  unfold MallocngBaseOverhead
  omega

/-- Composable placed internal OOM postcondition tracking `sigActions` alongside `fs` and `trace`,
    so `MallocngPlacedOomCond` lifts directly to `MallocngOomCond` in `Spec/Top.lean`. The refused
    request `sz` is counted together with the newly mapped intervals: `ivs.sum + sz ≤ maxBytes`. -/
def MallocngPlacedOomCond (svc : State → State) (maxIvs maxBytes : Nat) (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  ∃ ivs : List (BitVec 64 × Nat),
    ivs.length ≤ maxIvs ∧
    (ivs.map Prod.snd).sum ≤ maxBytes ∧
    (∀ a : BitVec 64, (sf.mem.perm a).mapped = true →
      (s0.mem.perm a).mapped = true ∨ MallocngInIntervals ivs a) ∧
    (MallocngSanitizedSvc svc →
      ∃ sz : Nat,
        PAGE_SIZE ≤ sz ∧
        sz % PAGE_SIZE = 0 ∧
        (ivs.map Prod.snd).sum + sz ≤ maxBytes ∧
        MallocngNoGapOrPhys sf sz)

namespace MallocngPlacedOomCond

theorem delta {svc : State → State} {k B : Nat} {s0 sf : State}
    (h : MallocngPlacedOomCond svc k B s0 sf) : MallocngMappedDelta k B s0.mem sf.mem := by
  obtain ⟨_, _, _, ivs, hl, hs, hc, _⟩ := h
  exact ⟨ivs, hl, hs, hc⟩

theorem of_delta {svc : State → State} {k k' B1 B : Nat} {s0 sf : State}
    (hfs : sf.fs = s0.fs) (htr : sf.trace = s0.trace) (hsig : sf.sigActions = s0.sigActions)
    (hd : MallocngMappedDelta k B1 s0.mem sf.mem) (hk : k ≤ k') (hB : B1 ≤ B)
    (hgap : MallocngSanitizedSvc svc → ∃ sz : Nat, PAGE_SIZE ≤ sz ∧ sz % PAGE_SIZE = 0 ∧
      B1 + sz ≤ B ∧ MallocngNoGapOrPhys sf sz) :
    MallocngPlacedOomCond svc k' B s0 sf := by
  obtain ⟨ivs, hl, hs, hc⟩ := hd
  refine ⟨hfs, htr, hsig, ivs, Nat.le_trans hl hk, Nat.le_trans hs hB, hc, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, by omega, hng⟩

theorem mono {svc : State → State} {k k' B B' : Nat} {s0 sf : State}
    (hk : k ≤ k') (hB : B ≤ B') (h : MallocngPlacedOomCond svc k B s0 sf) :
    MallocngPlacedOomCond svc k' B' s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hl, hs, hc, hgap⟩ := h
  refine ⟨hfs, htr, hsig, ivs, Nat.le_trans hl hk, Nat.le_trans hs hB, hc, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, by omega, hng⟩

theorem append_delta {svc : State → State} {k1 k2 B1 B2 : Nat} {s0 s1 sf : State}
    (hfs : s1.fs = s0.fs) (htr : s1.trace = s0.trace) (hsig : s1.sigActions = s0.sigActions)
    (hd : MallocngMappedDelta k1 B1 s0.mem s1.mem) (h : MallocngPlacedOomCond svc k2 B2 s1 sf) :
    MallocngPlacedOomCond svc (k1 + k2) (B1 + B2) s0 sf := by
  obtain ⟨ivs1, hl1, hs1, hc1⟩ := hd
  obtain ⟨hfs2, htr2, hsig2, ivs2, hl2, hs2, hc2, hgap⟩ := h
  have hsum : ((ivs1 ++ ivs2).map Prod.snd).sum =
      (ivs1.map Prod.snd).sum + (ivs2.map Prod.snd).sum := by
    rw [List.map_append, List.sum_append]
  refine ⟨hfs2.trans hfs, htr2.trans htr, hsig2.trans hsig, ivs1 ++ ivs2,
    by rw [List.length_append]; omega, by omega, fun a ha => ?_, fun hsan => ?_⟩
  · rcases hc2 a ha with hm1 | ⟨iv, hiv2, hin⟩
    · rcases hc1 a hm1 with hm0 | ⟨iv, hiv1, hin⟩
      · exact Or.inl hm0
      · exact Or.inr ⟨iv, List.mem_append_left ivs2 hiv1, hin⟩
    · exact Or.inr ⟨iv, List.mem_append_right ivs1 hiv2, hin⟩
  · obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
    exact ⟨sz, hlo, hmod, by omega, hng⟩

end MallocngPlacedOomCond

theorem MallocngPlacedOomCond.to_oomCond {svc : State → State}
    {maxIvs maxBytes reqBytes peakCount : Nat} {s0 sf : State}
    (hi : maxIvs ≤ 16) (hb : maxBytes ≤ MallocngStepBound reqBytes peakCount)
    (h : MallocngPlacedOomCond svc maxIvs maxBytes s0 sf) :
    MallocngOomCond svc reqBytes peakCount s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hl, hs, hc, hgap⟩ := h
  refine ⟨hfs, htr, hsig, ⟨ivs, Nat.le_trans hl hi, Nat.le_trans hs hb, hc⟩, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, by omega, hng⟩

/-- Tight newly-mapped step-delta bound (`Cost.mallocngTight2StepBound`:
    `max (4 * metaStep + G) (reqBytes + 4115 + metaStep)`, `metaStep = 180224 + 325 * peakCount`,
    `G = Cost.mallocngRootGroupBoundAt peakCount`). -/
def MallocngTightStepBound (reqBytes peakCount : Nat) : Nat :=
  Cost.mallocngTight2StepBound reqBytes peakCount

/-- Tight combined newly-mapped + failing-request sum bound (`Cost.mallocngTight2TotalBound`,
    equal to the step bound: the refused request is counted inside the same reserve). -/
def MallocngTightTotalBound (reqBytes peakCount : Nat) : Nat :=
  Cost.mallocngTight2TotalBound reqBytes peakCount

theorem MallocngTightStepBound_eq (reqBytes peakCount : Nat) :
    MallocngTightStepBound reqBytes peakCount =
      max (4 * (180224 + 325 * peakCount) + Cost.mallocngRootGroupBoundAt peakCount)
        (reqBytes + 4115 + (180224 + 325 * peakCount)) :=
  Cost.mallocngTight2StepBound_eq reqBytes peakCount

theorem MallocngTightTotalBound_eq (reqBytes peakCount : Nat) :
    MallocngTightTotalBound reqBytes peakCount =
      max (4 * (180224 + 325 * peakCount) + Cost.mallocngRootGroupBoundAt peakCount)
        (reqBytes + 4115 + (180224 + 325 * peakCount)) :=
  Cost.mallocngTight2TotalBound_eq reqBytes peakCount

theorem MallocngTightStepBound_mono {r1 r2 pc : Nat} (h : r1 ≤ r2) :
    MallocngTightStepBound r1 pc ≤ MallocngTightStepBound r2 pc := by
  rw [MallocngTightStepBound_eq, MallocngTightStepBound_eq]; omega

theorem MallocngTightTotalBound_mono {r1 r2 pc : Nat} (h : r1 ≤ r2) :
    MallocngTightTotalBound r1 pc ≤ MallocngTightTotalBound r2 pc := by
  rw [MallocngTightTotalBound_eq, MallocngTightTotalBound_eq]; omega

theorem MallocngTightStepBound_le_stepBound (reqBytes peakCount : Nat) :
    MallocngTightStepBound reqBytes peakCount ≤ MallocngStepBound reqBytes peakCount := by
  have hG := Cost.mallocngRootGroupBoundAt_le peakCount
  rw [MallocngTightStepBound_eq]
  unfold MallocngStepBound MallocngBaseOverhead pageAlignUp PAGE_SIZE
  omega

theorem MallocngMappedDelta.tight_to_step {k reqBytes peakCount : Nat} {m0 mf : Memory}
    (h : MallocngMappedDelta k (MallocngTightStepBound reqBytes peakCount) m0 mf) :
    MallocngMappedDelta k (MallocngStepBound reqBytes peakCount) m0 mf :=
  MallocngMappedDelta.mono (Nat.le_refl _) (MallocngTightStepBound_le_stepBound _ _) h

theorem MallocngCallAccounting.tight_to_step {k reqBytes peakCount : Nat} {s0 sf : State}
    (h : MallocngCallAccounting k (MallocngTightStepBound reqBytes peakCount) s0 sf) :
    MallocngCallAccounting k (MallocngStepBound reqBytes peakCount) s0 sf :=
  ⟨h.1, MallocngMappedDelta.tight_to_step h.2⟩

/-- Tight `realloc` success reserve for a block whose ghost overhead is `≤ a - 16`:
    `n + min (a - 16) (2^31 - 16)` (equals `mallocngAlignedEffSize a n` for `a ≤ 2^31`). -/
def mallocngReallocRes (a n : Nat) : Nat :=
  n + min (a - 16) (MaxAlignedAllocAlign - 16)

theorem mallocngReallocRes_eq_effSize {a n : Nat} (h : a ≤ MaxAlignedAllocAlign) :
    mallocngReallocRes a n = mallocngAlignedEffSize a n := by
  unfold mallocngReallocRes mallocngAlignedEffSize
  split <;> omega

theorem mallocngReallocRes_le (a n : Nat) : mallocngReallocRes a n ≤ n + MaxAlignedAllocAlign := by
  unfold mallocngReallocRes; omega

theorem le_mallocngReallocRes (a n : Nat) : n ≤ mallocngReallocRes a n := by
  unfold mallocngReallocRes; omega

theorem MallocngTightStepBound_reallocRes_le (a n pc : Nat) :
    MallocngTightStepBound (mallocngReallocRes a n) pc ≤
      MallocngStepBound (n + MaxAlignedAllocAlign) pc :=
  Nat.le_trans (MallocngTightStepBound_mono (mallocngReallocRes_le a n))
    (MallocngTightStepBound_le_stepBound _ _)

/-- Tight placed out-of-memory postcondition tracking explicit `ivs` intervals so that both
    `(ivs.map Prod.snd).sum` and `(ivs.map Prod.snd).sum + sz` stay linear in `1 × reqBytes`. -/
def MallocngTightOomCond (svc : State → State) (reqBytes peakCount : Nat) (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  ∃ ivs : List (BitVec 64 × Nat),
    ivs.length ≤ 16 ∧
    (ivs.map Prod.snd).sum ≤ MallocngTightStepBound reqBytes peakCount ∧
    (∀ a : BitVec 64, (sf.mem.perm a).mapped = true →
      (s0.mem.perm a).mapped = true ∨ MallocngInIntervals ivs a) ∧
    (MallocngSanitizedSvc svc →
      ∃ sz : Nat,
        PAGE_SIZE ≤ sz ∧
        sz % PAGE_SIZE = 0 ∧
        sz ≤ MallocngTightStepBound reqBytes peakCount ∧
        (ivs.map Prod.snd).sum + sz ≤ MallocngTightTotalBound reqBytes peakCount ∧
        MallocngNoGapOrPhys sf sz)

theorem MallocngTightOomCond.to_oomCond {svc : State → State}
    {reqBytes reqBytes' peakCount : Nat} {s0 sf : State}
    (hle : reqBytes ≤ reqBytes')
    (h : MallocngTightOomCond svc reqBytes peakCount s0 sf) :
    MallocngOomCond svc reqBytes' peakCount s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hlen, hsum, hcov, hgap⟩ := h
  have hsb1 := MallocngTightStepBound_le_stepBound reqBytes peakCount
  have hsb2 : MallocngStepBound reqBytes peakCount ≤ MallocngStepBound reqBytes' peakCount := by
    unfold MallocngStepBound pageAlignUp PAGE_SIZE; omega
  have hsb := Nat.le_trans hsb1 hsb2
  refine ⟨hfs, htr, hsig, ⟨ivs, hlen, Nat.le_trans hsum hsb, hcov⟩, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, _, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, Nat.le_trans hhi hsb, hng⟩

theorem MallocngTightOomCond.of_pre_perm {svc : State → State} {req peakCount : Nat}
    {s0 s1 sf : State}
    (hfs : s1.fs = s0.fs) (htr : s1.trace = s0.trace) (hsig : s1.sigActions = s0.sigActions)
    (hperm : s1.mem.perm = s0.mem.perm) (hoom : MallocngTightOomCond svc req peakCount s1 sf) :
    MallocngTightOomCond svc req peakCount s0 sf := by
  obtain ⟨h1, h2, h3, ivs, hlen, hsum, hcov, hgap⟩ := hoom
  exact ⟨h1.trans hfs, h2.trans htr, h3.trans hsig, ivs, hlen, hsum,
    fun a ha => (hcov a ha).imp (fun hm => hperm ▸ hm) id, hgap⟩

/-! ## `totalLiveCount` Group and `meta_area` Bounds for `__malloc_alloc_meta` -/

private theorem le_sum_of_mem_nat {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => nomatch h
  | cons y rest ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | hrest
    · omega
    · have := ih hrest; omega

private theorem sum_map_le_nat {α : Type} {f g : α → Nat} {xs : List α}
    (hle : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle x List.mem_cons_self
    have h2 := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

private theorem sum_map_add_nat {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem filter_partition_sum {α : Type} (p : α → Bool) (f : α → Nat) (xs : List α) :
    (xs.map f).sum = ((xs.filter p).map f).sum + ((xs.filter (fun x => !p x)).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    by_cases hp : p x = true
    · simp [hp, ih]; omega
    · have hpf : p x = false := Bool.eq_false_iff.mpr hp
      simp [hpf, ih]; omega

private theorem filter_partition_len {α : Type} (p : α → Bool) (xs : List α) :
    xs.length = (xs.filter p).length + (xs.filter (fun x => !p x)).length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    by_cases hp : p x = true
    · simp [hp, ih]; omega
    · have hpf : p x = false := Bool.eq_false_iff.mpr hp
      simp [hpf, ih]; omega

private theorem nodup_len_le_subset {α : Type} [DecidableEq α] {xs ys : List α}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
    simp only [List.nodup_cons] at hnd
    have hx := hsub x List.mem_cons_self
    have hrest : ∀ y ∈ rest, y ∈ ys.erase x := fun y hy =>
      (List.mem_erase_of_ne (fun (heq : y = x) => hnd.1 (heq ▸ hy))).mpr
        (hsub y (List.mem_cons_of_mem x hy))
    have hlen := ih hnd.2 hrest
    have herase : (ys.erase x).length = ys.length - 1 := List.length_erase_of_mem hx
    have hpos : 1 ≤ ys.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- Count-based counterpart of `groups_length_le`: total active groups in `st.groups` is bounded by
    `32 + 8 * (totalLiveCount st + totalClaimedSlots st)`. -/
theorem groups_length_le_of_liveCount {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    st.groups.length ≤ 32 + 8 * (totalLiveCount st + totalClaimedSlots st) := by
  let empGs := st.groups.filter (·.isEmpty)
  let nonEmpGs := st.groups.filter (fun g => !g.isEmpty)
  have hPartLen : st.groups.length = empGs.length + nonEmpGs.length :=
    filter_partition_len (·.isEmpty) st.groups
  have hEmpLe : empGs.length ≤ 32 := emptyGroups_length_le hwf
  let directLeaves := st.groups.filter (·.hasDirectLeaf)
  let w : GroupDesc → Nat := fun g =>
    (g.slots.map slotLiveCount).sum + (g.slots.filter SlotState.isClaimed).length
  have hGe1 : ∀ g ∈ directLeaves, 1 ≤ w g := by
    intro g hg
    have hDir := (List.mem_filter.mp hg).2
    unfold GroupDesc.hasDirectLeaf at hDir
    obtain ⟨s, hsMem, hsDir⟩ := List.any_eq_true.mp hDir
    cases hS : s with
    | freeAvail | freeInactive | liveNested _ => simp [hS] at hsDir
    | claimed =>
      have hMemF : s ∈ g.slots.filter SlotState.isClaimed :=
        List.mem_filter.mpr ⟨hsMem, by simp [hS, SlotState.isClaimed]⟩
      have := List.length_pos_of_mem hMemF
      dsimp only [w]; omega
    | liveUser u r e =>
      have hMemC : 1 ∈ g.slots.map slotLiveCount := by
        rw [hS] at hsMem
        exact List.mem_map.mpr ⟨.liveUser u r e, hsMem, rfl⟩
      have := le_sum_of_mem_nat hMemC
      dsimp only [w]; omega
  have hDirLeSum : directLeaves.length ≤ (directLeaves.map w).sum := by
    have h1 := sum_map_le_nat (f := fun _ => 1) hGe1
    have h2 : (directLeaves.map fun _ => 1).sum = directLeaves.length := by
      clear h1 hGe1
      induction directLeaves with
      | nil => rfl
      | cons _ tl ih => simp [ih]; omega
    omega
  have hSubSum : (directLeaves.map w).sum ≤ (st.groups.map w).sum := by
    have hp := filter_partition_sum (·.hasDirectLeaf) w st.groups
    dsimp only [directLeaves]; omega
  have hTotalW : (st.groups.map w).sum = totalLiveCount st + totalClaimedSlots st := by
    dsimp only [w]
    rw [sum_map_add_nat]
    rfl
  let ancestors := directLeaves.flatMap fun leaf =>
    (List.range 8).map fun d => iterParentMeta st d leaf.metaPtr
  have hAncLen : ancestors.length = 8 * directLeaves.length := by
    dsimp only [ancestors]
    clear hDirLeSum hSubSum hGe1
    induction directLeaves with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
        List.length_cons]
      omega
  have hNonEmpMetaNd : (nonEmpGs.map (·.metaPtr)).Nodup :=
    ((List.filter_sublist).map _).nodup hwf.groups_nodup.1
  have hNonEmpSub : ∀ m ∈ nonEmpGs.map (·.metaPtr), m ∈ ancestors := by
    intro m hm
    obtain ⟨g, hgMem, rfl⟩ := List.mem_map.mp hm
    have ⟨hgIn, hgNotE⟩ := List.mem_filter.mp hgMem
    have hEFalse : g.isEmpty = false := by simpa using hgNotE
    obtain ⟨leaf, hleaf, d, hdLt8, hLeafDir, hIter, _⟩ := descend_nonempty_group hwf hgIn hEFalse
    refine List.mem_flatMap.mpr ⟨leaf, List.mem_filter.mpr ⟨hleaf, hLeafDir⟩, ?_⟩
    exact List.mem_map.mpr ⟨d, List.mem_range.mpr hdLt8, hIter⟩
  have hNonEmpLe : nonEmpGs.length ≤ ancestors.length := by
    simpa using nodup_len_le_subset hNonEmpMetaNd hNonEmpSub
  omega

/-- Count-based counterpart of `slowPathC_prep_bounds`: when `freeMetas = []`, `bumpMetas = []`,
    `availMetaPages = []`, `inflight ≤ 7`, and `totalLiveCount st ≤ peakCount`, the `PROT_NONE`
    batch `len = 4096 * 2 ^ (m + 1)` requested by `__malloc_alloc_meta` satisfies
    `len + 4096 ≤ allocMetaPlacedByteBound peakCount` (one page of slack for the follow-up
    `mprotect` page, which may be refused). -/
theorem metaAreas_mmap_bytes_le_allocMetaPlacedByteBound
    {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost peakCount : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7) (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = []) (hNoAvail : st.availMetaPages = [])
    (hCount : totalLiveCount st ≤ peakCount) :
    let m := st.ctx.metaAllocShift.toNat
    let len := 4096 * 2 ^ (m + 1)
    m ≤ 35 ∧ 8192 ≤ len ∧ len ≤ 2 ^ 48 ∧ 4096 ∣ len ∧ len + 4096 ≤ allocMetaPlacedByteBound peakCount := by
  intro m len
  obtain ⟨hmLe35, hGe8192, hLe48, hDvd, _⟩ :=
    slowPathC_prep_bounds hwf hInflight hNoFree hNoBump hNoAvail
  refine ⟨hmLe35, hGe8192, hLe48, hDvd, ?_⟩
  let usedAndFree :=
    st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas
  have ⟨_, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hAllSlotsLen : (allMetaSlots st).length = 101 * st.metaAreas.length := by
    unfold allMetaSlots
    induction st.metaAreas with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
        List.length_cons]
      omega
  have hSlotNd : (allMetaSlots st).Nodup := by
    have hAux : ∀ mas : List MetaAreaDesc,
        (mas.map (·.base)).Nodup →
        (∀ ma ∈ mas, 4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧ ma.base.toNat + 4096 ≤ 2 ^ 48) →
        (mas.flatMap fun ma => (List.range 101).map ma.slotAddr).Nodup := by
      intro mas hNd hB
      induction mas with
      | nil => exact List.nodup_nil
      | cons ma rest ih =>
        simp only [List.map_cons, List.nodup_cons] at hNd
        simp only [List.flatMap_cons]
        have hMaB := hB ma List.mem_cons_self
        have hRestB : ∀ m' ∈ rest, 4096 ≤ m'.base.toNat ∧ m'.base.toNat % 4096 = 0 ∧
            m'.base.toNat + 4096 ≤ 2 ^ 48 :=
          fun m' hm' => hB m' (List.mem_cons_of_mem ma hm')
        have hSlotEq : ∀ (x : MetaAreaDesc) (k : Nat), x.base.toNat + 4096 ≤ 2 ^ 48 → k < 101 →
            (x.slotAddr k).toNat = x.base.toNat + (24 + 40 * k) := by
          intro x k hxb hk
          simp only [MetaAreaDesc.slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : 24 + 40 * k < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : x.base.toNat + (24 + 40 * k) < 2 ^ 64)]
        have hHeadNd : ((List.range 101).map ma.slotAddr).Nodup := by
          have hMapInj : ∀ {xs : List Nat}, xs.Nodup →
              (∀ a ∈ xs, ∀ b ∈ xs, ma.slotAddr a = ma.slotAddr b → a = b) →
              (xs.map ma.slotAddr).Nodup := by
            intro xs hndX hinjX
            induction xs with
            | nil => exact List.nodup_nil
            | cons x tl ihX =>
              simp only [List.map_cons, List.nodup_cons] at hndX ⊢
              refine ⟨fun hm => ?_, ihX hndX.2 (fun a ha b hb h =>
                hinjX a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) h)⟩
              obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
              have hxy := hinjX x List.mem_cons_self y (List.mem_cons_of_mem x hy) hfy.symm
              exact hndX.1 (hxy ▸ hy)
          refine hMapInj List.nodup_range (fun k1 hk1 k2 hk2 hEq => ?_)
          have hk1' := List.mem_range.mp hk1
          have hk2' := List.mem_range.mp hk2
          have ht := congrArg BitVec.toNat hEq
          rw [hSlotEq ma k1 hMaB.2.2 hk1', hSlotEq ma k2 hMaB.2.2 hk2'] at ht
          omega
        refine List.nodup_append.mpr ⟨hHeadNd, ih hNd.2 hRestB, fun a ha b hb hAb => ?_⟩
        subst hAb
        obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp ha
        obtain ⟨ma2, hma2, hb'⟩ := List.mem_flatMap.mp hb
        obtain ⟨k2, hk2, hEq⟩ := List.mem_map.mp hb'
        have hk1' := List.mem_range.mp hk1
        have hk2' := List.mem_range.mp hk2
        have hMa2B := hRestB ma2 hma2
        have ht := congrArg BitVec.toNat hEq
        rw [hSlotEq ma k1 hMaB.2.2 hk1', hSlotEq ma2 k2 hMa2B.2.2 hk2'] at ht
        exact hNd.1 ((BitVec.eq_of_toNat_eq (by omega : ma.base.toNat = ma2.base.toNat)) ▸
          List.mem_map_of_mem hma2)
    exact hAux st.metaAreas hwf.metaAreas_wf.1
      (fun ma hma => ⟨(hwf.metaAreas_wf.2.1 ma hma).1, (hwf.metaAreas_wf.2.1 ma hma).2.1,
        (hwf.metaAreas_wf.2.1 ma hma).2.2.1⟩)
  have hSlotsLeUf : (allMetaSlots st).length ≤ usedAndFree.length :=
    nodup_len_le_subset hSlotNd (fun x hx => (hUfIff x).mpr hx)
  have hGsLe := groups_length_le_of_liveCount hwf
  have hInf := hwf.inflight_wf
  have hUfLen : usedAndFree.length = st.groups.length + st.reservedMetas.length := by
    simp [usedAndFree, hNoFree, hNoBump]
  have hMa101 : 101 * st.metaAreas.length ≤ 88 + 8 * peakCount := by omega
  unfold allocMetaPlacedByteBound
  by_cases hm0 : m = 0
  · dsimp only [len]; rw [hm0]; omega
  · obtain ⟨hm40, _, hSum, _, _⟩ := hwf.meta_pages_bound.2.2 m (by omega) rfl
    have hAv0 : st.availMetaPages.length = 0 := by simp [hNoAvail]
    have hPow : 2 ^ (m + 1) ≤ st.metaAreas.length + 42 := by omega
    dsimp only [len]
    omega

/-! ## Placed Core Allocator Subroutine Contracts -/

/-- Placed `__malloc_alloc_meta()` (`blk07`, `224` B stack, `inflight ≤ 7`). -/
def AllocMetaPlacedStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (inflight : Nat) (_hInflight : inflight ≤ 7)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount),
    subroutine_ok (mallocngBlockProg mmpl 7 msvc) (mbase 7) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        stackFrame s0 224 ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ m : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧
           sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
           4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
           m ∉ st.reservedMetas ∧
           st'.reservedMetas = m :: st.reservedMetas ∧
           st'.groups = st.groups ∧
           st'.activeLists = st.activeLists ∧
           st'.liveMap = st.liveMap ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.ctx.active = st.ctx.active ∧
           st'.ctx.usageByClass = st.ctx.usageByClass ∧
           st'.ctx.unmapSeq = st.ctx.unmapSeq ∧
           st'.ctx.bounces = st.ctx.bounces ∧
           st'.ctx.seq = st.ctx.seq ∧
           (∀ g ∈ st.groups, ∀ a : BitVec 64,
             (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) →
               st'.byteVal a = st.byteVal a) ∧
           MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem sf.mem⌝ ∗
          stackFrame s0 224 ∗
          MallocngRuntime maddrs tp ∗
          (m ↦ₛ List.replicate 40 0#8) ∗
          MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝
    })

/-- Placed `alloc_slot(sc, req)` (`blk08`, `(allocSlotDepthBound sc + 1) * 96 + 224` B stack). -/
def AllocSlotPlacedStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (sc req inflight : Nat)
    (_hSc : sc < 48)
    (_hReq : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount),
    subroutine_ok (mallocngBlockProg mmpl 8 msvc) (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧
         (s0.readReg32 .x0).toNat = sc ∧
         (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ idx : Nat,
          ⌜MallocngProcPreserved s0 sf ∧
           st'.reservedMetas = st.reservedMetas ∧
           st'.liveMap = st.liveMap ∧
           totalLiveEffCost st' = totalLiveEffCost st ∧
           totalLiveCount st' = totalLiveCount st ∧
           sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
           (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
             g.sc = sc ∧
             g.metaPtr = st'.ctx.active[sc]'hAct ∧
             g.slots[idx]'hIdx = .claimed ∧
             (g.isMmapped = true →
               ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
           MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1))
             (allocSlotPlacedByteBound sc peakCount) s0.mem sf.mem⌝ ∗
          stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
          MallocngRoTablesA maddrs ∗
          MallocngRuntime maddrs tp ∗
          MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
           (allocSlotPlacedByteBound sc peakCount) s0 sf⌝
    })

/-- Shared `Spec Unit` body for placed `__libc_malloc_impl(req)` (`blk09`) and
    `default_malloc(req)` / `malloc(req)` (`blk04`, `704` B stack). -/
def libcMallocImplPlacedSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bf := mallocngAllocBudget ok req b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 (MallocngStepBound (if ok then req else 0) b.peakCount) s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st' : MallocngSt,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          mallocngIface.Block γ p req
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜MallocngOomCond msvc (if ok then req else 0) b.peakCount s0 sf⌝
  }

/-- Tight `Spec Unit` body for placed `__libc_malloc_impl(req)` (`blk09`) and
    `default_malloc(req)` / `malloc(req)` (`blk04`, `704` B stack) with `MallocngTightOomCond`. -/
def libcMallocImplPlacedTightSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bf := mallocngAllocBudget ok req b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 (MallocngTightStepBound (if ok then req else 0) b.peakCount) s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st' : MallocngSt,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          mallocngIface.Block γ p req
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜MallocngTightOomCond msvc (if ok then req else 0) b.peakCount s0 sf⌝
  }

/-- `libcMallocImplPlacedTightSpec` returning the exact-overhead token `MallocngBlockTokenK γ p req 0`
    (consumed by tight `realloc`, whose result block keeps an alignment-indexed overhead bound). -/
def libcMallocImplPlacedTightKSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bf := mallocngAllocBudget ok req b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 (MallocngTightStepBound (if ok then req else 0) b.peakCount) s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st' : MallocngSt,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          MallocngBlockTokenK γ p req 0
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜MallocngTightOomCond msvc (if ok then req else 0) b.peakCount s0 sf⌝
  }

def LibcMallocImplPlacedStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplPlacedSpec γ tp brkStart b ivs0 req)

def LibcMallocImplPlacedTightStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplPlacedTightSpec γ tp brkStart b ivs0 req)

def LibcMallocImplPlacedTightKStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplPlacedTightKSpec γ tp brkStart b ivs0 req)

def DefaultMallocPlacedStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (libcMallocImplPlacedSpec γ tp brkStart b ivs0 req)

def DefaultMallocPlacedTightStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (libcMallocImplPlacedTightSpec γ tp brkStart b ivs0 req)

/-- Placed `__libc_free(p)` (`blk06`, `272` B stack). -/
def libcFreePlacedSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (n : Nat)
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat)) : Spec Unit :=
  let bf := mallocngFreeBudget (p == 0#64) n b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = p⌝ ∗
      stackFrame s0 272 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0 ∗
      if p = 0#64 then emp
      else memRegion p n ∗ mallocngIface.Block γ p n
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
      stackFrame s0 272 ∗
      MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf
  }

def LibcFreePlacedStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (n : Nat)
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat)),
    subroutine_ok (mallocngBlockProg mmpl 6 msvc) (mbase 6)
      (libcFreePlacedSpec γ tp brkStart p n b ivs0)

/-- Placed `__libc_realloc(p, newSize)` (`blk14`, `800` B stack) on an alignment-indexed old
    block (`MallocngTightInitBlock γ a`, ghost overhead `≤ a - 16`), charging the tight reserve
    `MallocngTightStepBound (mallocngReallocRes a newSize)` on success. -/
def libcReallocPlacedSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p newSize : BitVec 64) (a : Nat)
    (oldBlk : Option (Nat × List (BitVec 8)))
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat)) : Spec Unit :=
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map Prod.snd).getD []).take newSize.toNat
  let bf := mallocngReallocBudget ok oldBlk newSize.toNat b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (MallocngTightInitBlock γ a)).pureWf p oldBlk⌝ ∗
      stackFrame s0 800 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0 ∗
      (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk
    post := fun _ s0 sf =>
      ⌜MallocngCallAccounting 16
         (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) b.peakCount)
         s0 sf⌝ ∗
      stackFrame s0 800 ∗
      MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
      if ok then
        ∃∗ q : BitVec 64,
          ⌜sf.readReg64 .x0 = q ∧
           (MallocngTightInitBlock γ a).pureWf q (newSize.toNat, keptBs)⌝ ∗
          (MallocngTightInitBlock γ a).interp q (newSize.toNat, keptBs)
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        (OptOwn (MallocngTightInitBlock γ a)).interp p oldBlk
    onOom := fun _ s0 sf =>
      ⌜MallocngTightOomCond msvc (if ok then newSize.toNat else 0) b.peakCount s0 sf⌝
  }

def LibcReallocPlacedStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p newSize : BitVec 64) (a : Nat)
    (oldBlk : Option (Nat × List (BitVec 8)))
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat)),
    subroutine_ok (mallocngBlockProg mmpl 14 msvc) (mbase 14)
      (libcReallocPlacedSpec γ tp brkStart p newSize a oldBlk b ivs0)

/-! ## Cross-Block Caller Lifts and Tight Public Entry Specs -/

theorem call_placed_libcMallocImpl [MallocngMultiPlacement] (h : LibcMallocImplPlacedStmt)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplPlacedSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem call_placed_libcMallocImpl_tight [MallocngMultiPlacement]
    (h : LibcMallocImplPlacedTightStmt)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplPlacedTightSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem call_placed_libcMallocImpl_tightK [MallocngMultiPlacement]
    (h : LibcMallocImplPlacedTightKStmt)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplPlacedTightKSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem call_placed_defaultMalloc [MallocngMultiPlacement] (h : DefaultMallocPlacedStmt)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 4) (libcMallocImplPlacedSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 4) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem call_placed_defaultMalloc_tight [MallocngMultiPlacement] (h : DefaultMallocPlacedTightStmt)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 4) (libcMallocImplPlacedTightSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 4) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem call_placed_libcFree [MallocngMultiPlacement] (h : LibcFreePlacedStmt)
    {P : Program} (γ : GhostName) (tp brkStart p : BitVec 64) (n : Nat)
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 6) (libcFreePlacedSpec γ tp brkStart p n b ivs0) :=
  subroutine_ok_block_to_block (j := 6) (by decide) (h γ tp brkStart p n b ivs0) hext hsvc

theorem call_placed_libcRealloc [MallocngMultiPlacement] (h : LibcReallocPlacedStmt)
    {P : Program} (γ : GhostName) (tp brkStart p newSize : BitVec 64) (a : Nat)
    (oldBlk : Option (Nat × List (BitVec 8)))
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 14) (libcReallocPlacedSpec γ tp brkStart p newSize a oldBlk b ivs0) :=
  subroutine_ok_block_to_block (j := 14) (by decide) (h γ tp brkStart p newSize a oldBlk b ivs0)
    hext hsvc

/-- Tight `malloc` C spec refining `mallocngMallocSpec` with `MallocngTightOomCond`. -/
c_type_spec mallocngMallocTightSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (req : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
  let b' := mallocngAllocBudget ok req.toNat b
  c_arg req : Val SizeT
  c_ret : Own (OptOwn (MallocngBlock J γ))
    (if ok then some (req.toNat, 16) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then req.toNat else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then req.toNat else 0) b.peakCount s0 sf

/-- Tight `calloc` C spec refining `mallocngCallocSpec` with `MallocngTightStepBound` /
    `MallocngTightOomCond` at `total = nmemb * size`. -/
c_type_spec mallocngCallocTightSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (nmemb : u64) (size : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let total := nmemb.toNat * size.toNat
  let ok := decide (total ≤ MallocngMaxAllocSize)
  let b' := mallocngAllocBudget ok total b
  c_arg nmemb : Val SizeT
  c_arg size : Val SizeT
  c_ret : Own (OptOwn (MallocngZeroedBlock J γ))
    (if ok then some (total, 16) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then total else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then total else 0) b.peakCount s0 sf

/-- Tight `aligned_alloc` C spec refining `mallocngAlignedAllocSpec` with
    `MallocngTightStepBound` / `MallocngTightOomCond` at `eff = mallocngAlignedEffSize`. -/
c_type_spec mallocngAlignedAllocTightSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := mallocngAlignedAllocOk align len
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let b' := mallocngAlignedBudget ok align.toNat len.toNat b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_ret : Own (OptOwn (MallocngBlock J γ))
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then eff else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then eff else 0) b.peakCount s0 sf

/-- Tight `posix_memalign` C spec refining `mallocngPosixMemalignSpec` with
    `MallocngTightStepBound` / `MallocngTightOomCond` at `eff = mallocngAlignedEffSize`. -/
c_type_spec mallocngPosixMemalignTightSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (res : ptr) (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : u32) where
  let ok := mallocngPosixMemalignOk align len
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let b' := mallocngAlignedBudget ok align.toNat len.toNat b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg res : MutRef (OptOutPtr (MallocngBlock J γ)) none ⇝
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  returns mallocngPosixMemalignRet align len
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then eff else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then eff else 0) b.peakCount s0 sf

/-- Tight `realloc` C spec refining `mallocngReallocSpec` with `MallocngTightOomCond` at
    `newSize.toNat` (eliminating the `+ MaxAlignedAllocAlign` OOM slack). -/
c_type_spec mallocngReallocTightSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (newSize : u64) (sp : sp)
    (ghost oldBlk : Option (Nat × List (BitVec 8)))
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map Prod.snd).getD []).take newSize.toNat
  let b' := mallocngReallocBudget ok oldBlk newSize.toNat b
  c_arg p : MutRef (CondOwn (OptOwn (MallocngInitBlock J γ))) (some oldBlk) ⇝
    (if ok then none else some oldBlk)
  c_arg newSize : Val SizeT
  c_ret : Own (OptOwn (MallocngInitBlock J γ))
    (if ok then some (newSize.toNat, keptBs) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngStepBound (if ok then newSize.toNat + MaxAlignedAllocAlign else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then newSize.toNat else 0) b.peakCount s0 sf

/-- Alignment-indexed tight `realloc` C spec: the old block carries ghost overhead `≤ a - 16`
    (`MallocngTightInitBlock γ a`), the result keeps the same bound, and success charges
    `MallocngTightStepBound (mallocngReallocRes a newSize)` (`= mallocngAlignedEffSize a newSize`
    for `a ≤ 2^31`) instead of `newSize + 2^31`. This is the spec consumed by the tight2 cost
    interface (`tight2_realloc_ok`); `mallocngReallocTightSpec` is derived from it. -/
c_type_spec mallocngReallocTightBlockSpec (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (newSize : u64) (sp : sp)
    (ghost a : Nat)
    (ghost oldBlk : Option (Nat × List (BitVec 8)))
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map Prod.snd).getD []).take newSize.toNat
  let b' := mallocngReallocBudget ok oldBlk newSize.toNat b
  c_arg p : MutRef (CondOwn (OptOwn (MallocngTightInitBlock γ a))) (some oldBlk) ⇝
    (if ok then none else some oldBlk)
  c_arg newSize : Val SizeT
  c_ret : Own (OptOwn (MallocngTightInitBlock γ a))
    (if ok then some (newSize.toNat, keptBs) else none)
  c_env (MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv mallocngIface γ A tp brkStart b' ivs0 s0 sf ∗
          stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then newSize.toNat else 0) b.peakCount s0 sf

end VerifiedLibraries.Mallocng.Proofs
