/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Cost.GroupTable

/-!
# Per-Call Step Reserve

Bounds the bytes newly mapped by a single placed `malloc` or `realloc` call (and, on
`OutOfMemory`, the refused page-aligned request `sz`) as parameterized by peak block count `pc`
and root-group `mmap` bound `G`:
- `__malloc_alloc_meta()` (`mallocngMetaStep pc = 180224 + 325 * pc`): at most one `brk` extension
  (`≤ 2` pages) or one `PROT_NONE` batch plus one page of slack for a refused `mprotect`.
- `alloc_slot(sc, req)` (`mallocngSlotReserve G pc = 4 * mallocngMetaStep pc + G`): at most 4
  nested `alloc_group` metadata allocations plus one root group of `≤ G` bytes, instantiated at
  `G = mallocngRootGroupBoundAt pc = min (grpMaxAll (pc + 6)) 1 MiB`.
- Large `malloc(req)` (`mallocngLargeReserve req pc = req + 4115 + mallocngMetaStep pc`): one
  `mmap` of `pageAlignUp (req + 20) ≤ req + 4115` bytes plus one `__malloc_alloc_meta()` call.
- On `OutOfMemory`, the refused request `sz` is itself one of the per-call mappings above, so
  `mallocngTight2TotalBoundG = mallocngTight2StepBoundG`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

/-- Newly mapped bytes of one `__malloc_alloc_meta()` call at peak block count `pc`. -/
def mallocngMetaStep (pc : Nat) : Nat := 180224 + 325 * pc

/-- Root-group `mmap` length bound of `alloc_group` (`RootMmapParamsOk`: `len ≤ 1 MiB`). -/
def mallocngRootGroupBound : Nat := 1048576

/-- Per-`peakCount` root-group `mmap` length bound: `alloc_group` maps `len ≤ rootBytesAt sc usage`
    with `usage ≤ peakCount + 6` (`Cost.usage_le_peak_add_six_of_active_zero`), capped by the
    `RootMmapParamsOk` bound `1 MiB`. -/
def mallocngRootGroupBoundAt (pc : Nat) : Nat := min (grpMaxAll (pc + 6)) mallocngRootGroupBound

theorem mallocngRootGroupBoundAt_le (pc : Nat) : mallocngRootGroupBoundAt pc ≤ 1048576 :=
  Nat.min_le_right _ _

theorem le_mallocngRootGroupBoundAt {sc pc u len : Nat} (hsc : sc < 48) (hu : u ≤ pc + 6)
    (hlen : len ≤ rootBytesAt sc u) (hlen1M : len ≤ 1048576) : len ≤ mallocngRootGroupBoundAt pc :=
  Nat.le_min.mpr ⟨Nat.le_trans hlen (Nat.le_trans (rootBytesAt_le_grpMax sc hu)
    (grpMax_le_grpMaxAll hsc _)), hlen1M⟩

theorem mallocngRootGroupBoundAt_five : mallocngRootGroupBoundAt 5 = 315392 := by decide +kernel

private theorem mallocngRootGroupBoundAt_lt_six :
    ∀ pc < 6, mallocngRootGroupBoundAt pc ≤ 315392 := by decide +kernel

theorem mallocngRootGroupBoundAt_le_of_le_five {pc : Nat} (h : pc ≤ 5) :
    mallocngRootGroupBoundAt pc ≤ 315392 :=
  mallocngRootGroupBoundAt_lt_six pc (Nat.lt_succ_of_le h)

/-- Newly mapped bytes of one `alloc_slot` call (`≤ 4` meta allocations plus one root group of
    `≤ G` bytes). -/
def mallocngSlotReserve (G pc : Nat) : Nat := 4 * mallocngMetaStep pc + G

/-- Newly mapped bytes of one large `malloc(req)` (`pageAlignUp (req + 20) ≤ req + 4115` plus one
    meta allocation). -/
def mallocngLargeReserve (req pc : Nat) : Nat := req + 4115 + mallocngMetaStep pc

/-- Per-call newly mapped byte bound (`ivs.sum`, and the refused request `sz`) with root-group
    bound `G`. -/
def mallocngTight2StepBoundG (G req pc : Nat) : Nat :=
  max (mallocngSlotReserve G pc) (mallocngLargeReserve req pc)

/-- Per-call bound on newly mapped bytes plus the refused request (`ivs.sum + sz`) with root-group
    bound `G`: equal to `mallocngTight2StepBoundG` since the refused `mmap` is one of the per-call
    mappings counted by the step reserve. -/
def mallocngTight2TotalBoundG (G req pc : Nat) : Nat :=
  mallocngTight2StepBoundG G req pc

def mallocngTight2StepBound (req pc : Nat) : Nat :=
  mallocngTight2StepBoundG (mallocngRootGroupBoundAt pc) req pc

def mallocngTight2TotalBound (req pc : Nat) : Nat :=
  mallocngTight2TotalBoundG (mallocngRootGroupBoundAt pc) req pc

theorem mallocngTight2StepBound_eq (req pc : Nat) :
    mallocngTight2StepBound req pc =
      max (4 * (180224 + 325 * pc) + mallocngRootGroupBoundAt pc)
        (req + 4115 + (180224 + 325 * pc)) := rfl

theorem mallocngTight2TotalBound_eq (req pc : Nat) :
    mallocngTight2TotalBound req pc =
      max (4 * (180224 + 325 * pc) + mallocngRootGroupBoundAt pc)
        (req + 4115 + (180224 + 325 * pc)) := rfl

theorem mallocngTight2StepBoundG_mono {G G' req req' pc pc' : Nat}
    (hG : G ≤ G') (hr : req ≤ req') (hp : pc ≤ pc') :
    mallocngTight2StepBoundG G req pc ≤ mallocngTight2StepBoundG G' req' pc' := by
  unfold mallocngTight2StepBoundG mallocngSlotReserve mallocngLargeReserve mallocngMetaStep
  omega

theorem mallocngTight2TotalBoundG_mono {G G' req req' pc pc' : Nat}
    (hG : G ≤ G') (hr : req ≤ req') (hp : pc ≤ pc') :
    mallocngTight2TotalBoundG G req pc ≤ mallocngTight2TotalBoundG G' req' pc' := by
  unfold mallocngTight2TotalBoundG
  exact mallocngTight2StepBoundG_mono hG hr hp

theorem mallocngTight2StepBoundG_le_total (G req pc : Nat) :
    mallocngTight2StepBoundG G req pc ≤ mallocngTight2TotalBoundG G req pc :=
  Nat.le_refl _

theorem mallocngReserve_five :
    mallocngMetaStep 5 = 181849 ∧ mallocngSlotReserve (mallocngRootGroupBoundAt 5) 5 = 1042788 := by
  unfold mallocngSlotReserve mallocngMetaStep
  rw [mallocngRootGroupBoundAt_five]
  decide

end VerifiedLibraries.Mallocng.Proofs.Cost
