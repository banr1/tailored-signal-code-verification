/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Region

/-!
# Multi-Offset `memRegion` Partitioning Unit Tests

Tests `memRegion_partition`, `memRegion_partition_at`, `memRegion_split_sub`, and
`memRegion_split_three` across single-cut splits, multi-field struct partitioning and rejoining,
15-field layouts, symbolic tail extents, and negative `MemRegionPartitionValid` checks.
-/

@[expose] public section

namespace Testing.RegionPartition

open Arm64 ProofLib

theorem test_split_at_stepwise (base : BitVec 64) :
    memRegion base 24 =
      memRegion base 8 ∗
        (memRegion (base + 8#64) 2 ∗
          (memRegion (base + 10#64) 2 ∗
            (memRegion (base + 12#64) 4 ∗
              memRegion (base + 16#64) 8))) := by
  rw [memRegion_partition base 24 [8],
      memRegion_partition_at base 8 24 [10],
      memRegion_partition_at base 10 24 [12],
      memRegion_partition_at base 12 24 [16]]

theorem test_partition_struct24 (base : BitVec 64) :
    memRegion base 24 =
      memRegion base 8 ∗
        (memRegion (base + 8#64) 2 ∗
          (memRegion (base + 10#64) 2 ∗
            (memRegion (base + 12#64) 4 ∗
              memRegion (base + 16#64) 8))) := by
  rw [memRegion_partition base 24 [8, 10, 12, 16]]

theorem test_partition_struct24_rejoin (base : BitVec 64) :
    memRegion base 8 ∗
      (memRegion (base + 8#64) 2 ∗
        (memRegion (base + 10#64) 2 ∗
          (memRegion (base + 12#64) 4 ∗
            memRegion (base + 16#64) 8))) =
      memRegion base 24 := by
  rw [memRegion_partition base 24 [8, 10, 12, 16]]

theorem test_typed_struct24_entails_memRegion (base : BitVec 64)
    (f0 : BitVec 64) (f1 f2 : BitVec 16) (f3 : BitVec 32) (f4 : BitVec 64) :
    (base ↦₆₄ f0) ∗ ((base + 8#64) ↦₁₆ f1) ∗ ((base + 10#64) ↦₁₆ f2) ∗
      ((base + 12#64) ↦₃₂ f3) ∗ ((base + 16#64) ↦₆₄ f4) ⊢
      memRegion base 24 := by
  rw [memRegion_partition base 24 [8, 10, 12, 16]]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo16_entails_memRegion _ _)
      (sepConj_mono (pointsTo16_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _))))

theorem test_partition_at_suffix (base : BitVec 64) :
    memRegion (base + 8#64) 16 =
      memRegion (base + 8#64) 2 ∗
        (memRegion (base + 10#64) 2 ∗
          (memRegion (base + 12#64) 4 ∗
            memRegion (base + 16#64) 8)) := by
  rw [memRegion_partition_at base 8 24 [10, 12, 16]]

set_option maxHeartbeats 50000 in
theorem test_partition_large_15_fields (base : BitVec 64) :
    memRegion base 0x13450 =
      memRegion base 0x8 ∗
      (memRegion (base + 0x8#64) 0x4 ∗
      (memRegion (base + 0xc#64) 0x4 ∗
      (memRegion (base + 0x10#64) 0x8 ∗
      (memRegion (base + 0x18#64) 0x58 ∗
      (memRegion (base + 0x70#64) 0x8 ∗
      (memRegion (base + 0x78#64) 0x8 ∗
      (memRegion (base + 0x80#64) 0x8 ∗
      (memRegion (base + 0x88#64) 0x8 ∗
      (memRegion (base + 0x90#64) 0x8 ∗
      (memRegion (base + 0x98#64) 0x3c0 ∗
      (memRegion (base + 0x458#64) 0x8 ∗
      (memRegion (base + 0x460#64) 0x8 ∗
      (memRegion (base + 0x468#64) 0x4548 ∗
      (memRegion (base + 0x49b0#64) 0x8 ∗
       memRegion (base + 0x49b8#64) 0xea98)))))))))))))) := by
  rw [memRegion_partition base 0x13450
    [0x8, 0xc, 0x10, 0x18, 0x70, 0x78, 0x80, 0x88, 0x90, 0x98,
     0x458, 0x460, 0x468, 0x49b0, 0x49b8]]

theorem test_partition_symbolic_tail (base : BitVec 64) (k : Nat) (hk : k ≤ 4096) :
    memRegion base (24 + k) =
      memRegion base 8 ∗
        (memRegion (base + 8#64) 4 ∗
          (memRegion (base + 12#64) 12 ∗
            memRegion (base + 24#64) (24 + k - 24))) := by
  rw [memRegion_partition base (24 + k) [8, 12, 24]]

-- Non-monotonic offset list `[12, 8]` is rejected by `MemRegionPartitionValid`.
/--
error: could not synthesize default value for parameter 'hvalid' using tactics
---
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
-/
#guard_msgs in
example (base : BitVec 64) :
    memRegion base 24 =
      memRegion base 12 ∗ (memRegion (base + 12#64) 0 ∗ memRegion (base + 8#64) 16) := by
  rw [memRegion_partition base 24 [12, 8]]

-- Out-of-bounds offset `[8, 32]` on a 24-byte region is rejected by `MemRegionPartitionValid`.
/--
error: could not synthesize default value for parameter 'hvalid' using tactics
---
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
-/
#guard_msgs in
example (base : BitVec 64) :
    memRegion base 24 =
      memRegion base 8 ∗ (memRegion (base + 8#64) 24 ∗ memRegion (base + 32#64) 0) := by
  rw [memRegion_partition base 24 [8, 32]]

example (sp : BitVec 64) :
    memRegion (sp - 256#64) 256 =
      memRegion (sp - 256#64) 64 ∗ memRegion (sp - 192#64) 192 :=
  memRegion_split_sub sp 256 64 192

example (a : BitVec 64) :
    memRegion a (8 + 8 + 8) =
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 8#64 + 8#64) 8 :=
  memRegion_split_three a 8 8 8 (by decide)

/--
error: could not synthesize default value for parameter 'hmk' using tactics
---
error: Tactic `decide` proved that the proposition
  64 + 128 = 256
is false
-/
#guard_msgs in
example (sp : BitVec 64) :
    memRegion (sp - 256#64) 256 =
      memRegion (sp - 256#64) 64 ∗ memRegion (sp - 128#64) 128 :=
  memRegion_split_sub sp 256 64 128

end Testing.RegionPartition
