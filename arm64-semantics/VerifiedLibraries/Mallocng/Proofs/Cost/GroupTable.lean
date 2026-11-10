/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.SizeClasses
public import VerifiedLibraries.Mallocng.Proofs.Defs

/-!
# Usage-Indexed Root-Group Size Tables

Kernel-evaluable tables bounding the `mmap` byte length of a root group created by `alloc_group`
for size class `sc` as a function of an upper bound `U` on `ctx.usage_by_class[sc]` at creation
time. Defines `cntSel`, `rootBytesAt`, `grpMax`, `keptMax`, `keptSum`, and the per-group invariant
`GroupsGrpBound`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-- `small_cnt_tab[sc][i]` (`sc < 9`, `i < 3`), read from the frozen `.rodata` byte literal. -/
def smallCnt (sc i : Nat) : Nat :=
  (smallCntTabBytes.getD (3 * sc + i) 0#8).toNat

/-- `med_cnt_tab[sc & 3]`, read from the frozen `.rodata` byte literal. -/
def medCnt (sc : Nat) : Nat :=
  (medCntTabBytes.getD (sc % 4) 0#8).toNat

/-- `while (!(cnt & 1) && 4 * cnt > usage) cnt >>= 1` (fuel-bounded; `med_cnt_tab ≤ 32`). -/
def halveUsage : Nat → Nat → Nat → Nat
  | 0, _, c => c
  | f + 1, u, c => if c % 2 = 0 ∧ 4 * c > u ∧ 0 < c then halveUsage f u (c / 2) else c

/-- `while (size * cnt >= 65536 * UNIT) cnt >>= 1` (fuel-bounded). -/
def halveSize : Nat → Nat → Nat → Nat
  | 0, _, c => c
  | f + 1, size, c => if size * c ≥ 1048576 ∧ 0 < c then halveSize f size (c / 2) else c

/-- Slot count at the end of `alloc_group`'s table/halving selection (before the `cnt = 1` bump). -/
def cntRaw (sc u : Nat) : Nat :=
  if sc < 9 then
    if 4 * smallCnt sc 0 ≤ u then smallCnt sc 0
    else if 4 * smallCnt sc 1 ≤ u then smallCnt sc 1
    else smallCnt sc 2
  else halveSize 8 (slotStride sc) (halveUsage 8 u (medCnt sc))

/-- `if (cnt == 1 && size * cnt + UNIT <= pagesize / 2) cnt = 2`. -/
def cntBump (sc c : Nat) : Nat :=
  if c = 1 ∧ slotStride sc + 16 ≤ 2048 then 2 else c

/-- Slot count chosen by `alloc_group` before the root-path (`mmap`) reductions, at usage `u`. -/
def cntSel (sc u : Nat) : Nat := cntBump sc (cntRaw sc u)

/-- Root-path `sc & 3` reduction (`4 * cnt > usage`, not bouncing). -/
def reduceCnt (sc c : Nat) : Nat :=
  let size := slotStride sc
  if sc % 4 = 1 ∧ size * c > 8 * 4096 then 2
  else if sc % 4 = 2 ∧ size * c > 4 * 4096 then 3
  else if sc % 4 = 0 ∧ size * c > 8 * 4096 then 3
  else if sc % 4 = 0 ∧ size * c > 2 * 4096 then 5
  else c

/-- Worst-case root `mmap` length (bytes) of a group of class `sc` created at usage `u`
    (`0` when the group is nested). -/
def rootBytesAt (sc u : Nat) : Nat :=
  let size := slotStride sc
  let c := cntSel sc u
  if size * c + 16 ≤ 2048 then 0
  else
    let keep := (7 ≤ sc ∧ sc ≤ 38) ∨ (sc % 2 = 0 ∧ sc < 32)
    let c2 := if keep ∨ 4 * c ≤ u then c else reduceCnt sc c
    if ¬keep ∧ c2 ≤ 7 ∧ 2 * c2 > u ∧ 4 * 4096 ≤ size + 16 then pageAlignUp (size + 16)
    else pageAlignUp (size * c2 + 16)

/-- Cumulative maximum `max_{u ≤ U} rootBytesAt sc u` (monotone in `U`). -/
def grpMax (sc : Nat) : Nat → Nat
  | 0 => rootBytesAt sc 0
  | U + 1 => max (grpMax sc U) (rootBytesAt sc (U + 1))

/-- Worst-case length of the (unique) kept-empty root group of class `sc` (`7 ≤ sc ≤ 38`). -/
def keptMax (sc U : Nat) : Nat :=
  if 7 ≤ sc ∧ sc ≤ 38 then grpMax sc U else 0

/-- Sum of `keptMax sc U` over `sc < 48`: total bytes of kept-empty root groups at usage bound `U`. -/
def keptSum (U : Nat) : Nat :=
  ((List.range 48).map fun sc => keptMax sc U).sum

theorem grpMax_succ_le (sc U : Nat) : grpMax sc U ≤ grpMax sc (U + 1) := by
  simp only [grpMax]; omega

theorem grpMax_mono (sc : Nat) {U V : Nat} (h : U ≤ V) : grpMax sc U ≤ grpMax sc V := by
  induction V with
  | zero => cases Nat.le_zero.mp h; exact Nat.le_refl _
  | succ V ih =>
    rcases Nat.lt_or_ge U (V + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) (grpMax_succ_le sc V)
    · cases Nat.le_antisymm h hge; exact Nat.le_refl _

theorem rootBytesAt_le_grpMax (sc : Nat) {u U : Nat} (h : u ≤ U) :
    rootBytesAt sc u ≤ grpMax sc U := by
  refine Nat.le_trans ?_ (grpMax_mono sc h)
  cases u with
  | zero => exact Nat.le_refl _
  | succ u => simp only [grpMax]; omega

theorem keptMax_mono (sc : Nat) {U V : Nat} (h : U ≤ V) : keptMax sc U ≤ keptMax sc V := by
  unfold keptMax; split
  · exact grpMax_mono sc h
  · exact Nat.le_refl _

/-- `grpMaxAll U = max_{sc < 48} grpMax sc U`: worst-case root-group length over all classes. -/
def grpMaxAll (U : Nat) : Nat :=
  ((List.range 48).map fun sc => grpMax sc U).foldr max 0

private theorem le_foldr_max {xs : List Nat} {x : Nat} (h : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem grpMax_le_grpMaxAll {sc : Nat} (hsc : sc < 48) (U : Nat) : grpMax sc U ≤ grpMaxAll U :=
  le_foldr_max (List.mem_map.mpr ⟨sc, List.mem_range.mpr hsc, rfl⟩)

private theorem grpMax_47_zero : 8195 ≤ grpMax 47 0 := by decide +kernel

theorem grpMaxAll_ge (U : Nat) : 8195 ≤ grpMaxAll U :=
  Nat.le_trans grpMax_47_zero
    (Nat.le_trans (grpMax_mono 47 (Nat.zero_le U)) (grpMax_le_grpMaxAll (by decide) U))

/-- Per-group root-length bound at usage bound `U`: every mapped root group of a small class
    (`sc < 48`) maps at most `grpMax sc U` bytes. -/
def GroupsGrpBound (U : Nat) (groups : List GroupDesc) : Prop :=
  ∀ g ∈ groups, 0 < g.maplen → g.sc < 48 → g.maplen * 4096 ≤ grpMax g.sc U

theorem GroupsGrpBound.mono {U V : Nat} {gs : List GroupDesc} (h : GroupsGrpBound U gs)
    (hUV : U ≤ V) : GroupsGrpBound V gs :=
  fun g hg hm hs => Nat.le_trans (h g hg hm hs) (grpMax_mono _ hUV)

theorem GroupsGrpBound.of_subset {U : Nat} {gs gs' : List GroupDesc} (h : GroupsGrpBound U gs)
    (hsub : ∀ g ∈ gs', 0 < g.maplen → g.sc < 48 → ∃ g0 ∈ gs, g0.sc = g.sc ∧ g.maplen ≤ g0.maplen) :
    GroupsGrpBound U gs' := fun g hg hm hs => by
  obtain ⟨g0, hg0, hsc, hle⟩ := hsub g hg hm hs
  have := h g0 hg0 (Nat.lt_of_lt_of_le hm hle) (hsc ▸ hs)
  rw [hsc] at this; exact Nat.le_trans (Nat.mul_le_mul_right _ hle) this

theorem GroupsGrpBound.map {U : Nat} {gs : List GroupDesc} (h : GroupsGrpBound U gs)
    (f : GroupDesc → GroupDesc) (hf : ∀ g ∈ gs, (f g).sc = g.sc ∧ (f g).maplen ≤ g.maplen) :
    GroupsGrpBound U (gs.map f) :=
  h.of_subset fun g hg _ _ => by
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨g0, hg0, (hf g0 hg0).1.symm, (hf g0 hg0).2⟩

theorem GroupsGrpBound.map_ite {U : Nat} {gs : List GroupDesc} (h : GroupsGrpBound U gs)
    (m : BitVec 64) {g1 : GroupDesc}
    (hg1 : 0 < g1.maplen → g1.sc < 48 → g1.maplen * 4096 ≤ grpMax g1.sc U) :
    GroupsGrpBound U (gs.map fun h => if h.metaPtr == m then g1 else h) := fun g hg hm hs => by
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  by_cases hc : (g0.metaPtr == m) = true
  · simp only [hc, ↓reduceIte] at hm hs ⊢; exact hg1 hm hs
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hm hs ⊢; exact h g0 hg0 hm hs

theorem GroupsGrpBound.filter {U : Nat} {gs : List GroupDesc} (h : GroupsGrpBound U gs)
    (p : GroupDesc → Bool) : GroupsGrpBound U (gs.filter p) :=
  fun g hg => h g (List.mem_filter.mp hg).1

theorem GroupsGrpBound.cons {U : Nat} {gs : List GroupDesc} (h : GroupsGrpBound U gs)
    {g1 : GroupDesc} (hg1 : 0 < g1.maplen → g1.sc < 48 → g1.maplen * 4096 ≤ grpMax g1.sc U) :
    GroupsGrpBound U (g1 :: gs) := fun g hg => by
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hg1
  · exact h g hg

theorem GroupsGrpBound.append {U : Nat} {gs gs' : List GroupDesc} (h : GroupsGrpBound U gs)
    (h' : GroupsGrpBound U gs') : GroupsGrpBound U (gs ++ gs') := fun g hg => by
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · exact h' g hg

/-- `gs'` inherits every per-group root-length bound of `gs` (groups only shrink or vanish). -/
def GroupsGrpMono (gs gs' : List GroupDesc) : Prop :=
  ∀ U, GroupsGrpBound U gs → GroupsGrpBound U gs'

theorem GroupsGrpMono.refl (gs : List GroupDesc) : GroupsGrpMono gs gs := fun _ h => h

theorem GroupsGrpMono.trans {gs gs' gs'' : List GroupDesc} (h : GroupsGrpMono gs gs')
    (h' : GroupsGrpMono gs' gs'') : GroupsGrpMono gs gs'' := fun U hU => h' U (h U hU)

theorem GroupsGrpMono.of_eq {gs gs' : List GroupDesc} (h : gs' = gs) : GroupsGrpMono gs gs' :=
  fun _ hU => h ▸ hU

theorem GroupsGrpMono.of_subset {gs gs' : List GroupDesc}
    (hsub : ∀ g ∈ gs', 0 < g.maplen → g.sc < 48 → ∃ g0 ∈ gs, g0.sc = g.sc ∧ g.maplen ≤ g0.maplen) :
    GroupsGrpMono gs gs' := fun _ hU => hU.of_subset hsub

theorem GroupsGrpMono.of_mem {gs gs' : List GroupDesc} (hsub : ∀ g ∈ gs', g ∈ gs) :
    GroupsGrpMono gs gs' := fun _ hU g hg => hU g (hsub g hg)

theorem keptSum_five : keptSum 5 = 675840 := by decide +kernel

theorem grpMax_five_le : ∀ sc < 48, grpMax sc 5 ≤ 176128 := by decide +kernel

theorem keptSum_sixteen : keptSum 16 = 770048 := by decide +kernel

theorem grpMax_sixteen_le : ∀ sc < 48, grpMax sc 16 ≤ 524288 := by decide +kernel

end VerifiedLibraries.Mallocng.Proofs.Cost
