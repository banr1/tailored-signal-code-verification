/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers6f

/-!
# Group-List Monotonicity for `free`

Establishes `Cost.GroupsGrpMono` across `free` and `nontrivial_free` group-list updates so that
per-group root-length bounds `Cost.GroupsGrpBound` carry over.
-/

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine.VendorFree.Cost
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.Cost LibsignalBinary.Heap.Fine.VendorFree

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

@[expose] public section

theorem groupsGrpMono_map_witness {gs : List GroupDesc} (f : GroupDesc → GroupDesc)
    (hf : ∀ h ∈ gs, ∃ h0 ∈ gs, h0.sc = (f h).sc ∧ (f h).maplen ≤ h0.maplen) :
    GroupsGrpMono gs (gs.map f) :=
  GroupsGrpMono.of_subset fun g hg _ _ => by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact hf h hh

theorem groupsGrpMono_replaceGroupByMeta {gs : List GroupDesc} {g g1 : GroupDesc} (hg : g ∈ gs)
    (m : BitVec 64) (hSc : g1.sc = g.sc) (hMl : g1.maplen = g.maplen) :
    GroupsGrpMono gs (replaceGroupByMeta gs m g1) := by
  unfold replaceGroupByMeta
  refine groupsGrpMono_map_witness _ fun h hh => ?_
  by_cases hc : (h.metaPtr == m) = true
  · simp only [hc, ↓reduceIte]; exact ⟨g, hg, hSc.symm, hMl ▸ Nat.le_refl _⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact ⟨h, hh, rfl, Nat.le_refl _⟩

theorem groupsGrpMono_updateQueuedGroups {gs : List GroupDesc} {g g1 : GroupDesc} (hg : g ∈ gs)
    (head tailPtr : BitVec 64) (hSc : g1.sc = g.sc) (hMl : g1.maplen = g.maplen) :
    GroupsGrpMono gs (updateQueuedGroups gs head tailPtr g1) := by
  unfold updateQueuedGroups
  refine groupsGrpMono_map_witness _ fun h hh => ?_
  by_cases hc : (h.metaPtr == g1.metaPtr) = true
  · simp only [hc, ↓reduceIte]; exact ⟨g, hg, hSc.symm, hMl ▸ Nat.le_refl _⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact ⟨h, hh, rfl, Nat.le_refl _⟩

theorem DequeueOutcome.groupsGrpMono {st : MallocngSt} {g : GroupDesc}
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq) :
    GroupsGrpMono st.groups gsDeq :=
  GroupsGrpMono.of_subset fun h hh _ _ => by
    obtain ⟨_, h0, hh0, _, _, hMl, hSc, _⟩ := hDeq.each_preserved h hh
    exact ⟨h0, hh0, hSc.symm, hMl ▸ Nat.le_refl _⟩

end

end LibsignalBinary.Heap.Fine.VendorFree.Cost
