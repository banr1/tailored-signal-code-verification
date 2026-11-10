/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Common
public import VerifiedLibraries.Mallocng.Proofs.TryAvailHelpers

/-!
# Per-Size-Class `mallocng` Geometry and Linearized Recurrence Tables

Kernel-checked size-class geometry tables (`cntMin`, `ValidRootCnt`, `maxRootBytes`,
`ceilRootPerSlot`, `minCntEdge`), `Nat` occupancy and root-byte recurrences (`occPreBound`,
`gBound`, `edgeBound`, `rBound`), and `65536`-scaled linear slot/group weights (`slotWt`,
`grpWtS`, `BaseRootFine`, `FineStepBound`).
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Scale, Thresholds, and Per-Step Reserve Formula -/

/-- Fixed-point scale `2 ^ 16 = 65536` for integer linearizations of fractional group bounds. -/
def FineScale : Nat := 65536

/-- Exact `0x1ffeb = 131051` nominal request threshold separating `sc < 48` from guaranteed `sc = 63`
    in `__libc_malloc_impl` and `realloc`. -/
def MmapThresholdReq : Nat := 131051

/-- Per-call virtual-memory OOM reserve bound for `fineCostModel`. -/
def FineStepBound (req align maxMetaAreas : Nat) : Nat :=
  pageAlignUp (req + (max align 16 - 16) + 8192) + 20 * 1024 * 1024 + 131072 * maxMetaAreas

theorem FineStepBound_mono_meta {req align m1 m2 : Nat} (hm : m1 ≤ m2) :
    FineStepBound req align m1 ≤ FineStepBound req align m2 := by
  unfold FineStepBound
  omega

theorem req_le_FineStepBound (req align maxMetaAreas : Nat) :
    req ≤ FineStepBound req align maxMetaAreas := by
  unfold FineStepBound
  have hle := pageAlignUp_le (req + (max align 16 - 16) + 8192)
  omega

/-! ## `meta_area`, Guard, and Available-Meta Page Multiplier -/

private def checkMetaGuardAvailBound : Bool :=
  (List.range 41).all fun m =>
    if 1 ≤ m then (m + 1) + (2 ^ m - 2) ≤ 2 * (2 ^ m - m) + 2 else true

private theorem checkMetaGuardAvailBound_true : checkMetaGuardAvailBound = true := by
  decide +kernel

theorem meta_guard_avail_shift_bound {m : Nat} (hlo : 1 ≤ m) (hhi : m ≤ 40) :
    (m + 1) + (2 ^ m - 2) ≤ 2 * (2 ^ m - m) + 2 := by
  have hCheck := List.all_eq_true.mp checkMetaGuardAvailBound_true m
    (List.mem_range.mpr (by omega))
  simp only [hlo, ↓reduceIte, decide_eq_true_eq] at hCheck
  exact hCheck

/-! ## Minimum Slot Counts, `ValidRootCnt`, and `minCntEdge` -/

/-- Minimum slot count across all groups (nested or root) of size class `sc < 48`:
    - `0..6`: `small_cnt_tab` row minimum `[30, 15, 10, 7, 6, 5, 4]` (never root);
    - `7..23`: `2` (`bounces` cap `c ∈ {2, 3, 5}` on `7..23`, and `cnt_f = 1 → 24 ≤ sc`);
    - `24..47`: `1`. -/
def cntMinTab : Array Nat :=
  #[30, 15, 10, 7, 6, 5, 4, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def cntMin (sc : Nat) : Nat :=
  cntMinTab.getD sc 1

private def checkCntMinPos : Bool :=
  (List.range 48).all fun sc => decide (0 < cntMin sc)

private theorem checkCntMinPos_true : checkCntMinPos = true := by
  decide +kernel

theorem cntMin_pos {sc : Nat} (hsc : sc < 48) : 0 < cntMin sc := by
  have h := List.all_eq_true.mp checkCntMinPos_true sc (List.mem_range.mpr hsc)
  simpa using h

def validNestedCntDec (sc cnt : Nat) : Bool :=
  decide (2 ≤ cnt ∧ cnt ≤ 32 ∧ cnt * slotStride sc + 16 ≤ 2048) &&
  (if sc ≤ 8 then
    decide (cnt = (smallCntTabBytes.getD (3 * sc) 0#8).toNat ∨
      cnt = (smallCntTabBytes.getD (3 * sc + 1) 0#8).toNat ∨
      cnt = (smallCntTabBytes.getD (3 * sc + 2) 0#8).toNat)
   else true)

theorem validNestedCnt_iff_dec {sc cnt : Nat} :
    ValidNestedCnt sc cnt ↔ validNestedCntDec sc cnt = true := by
  unfold ValidNestedCnt validNestedCntDec
  by_cases h8 : sc ≤ 8
  · simp [h8, and_assoc]
  · simp [h8]

def validRootCntDec (sc cnt : Nat) : Bool :=
  decide (7 ≤ sc ∧ sc < 48 ∧ cntMin sc ≤ cnt ∧ cnt ≤ 32 ∧ cnt * slotStride sc ≤ 1048575) &&
  (if sc ≤ 25 then decide (cnt * slotStride sc + 16 ≤ 65536) else true)

/-- Valid root `mmap` group slot count for `sc < 48`. -/
def ValidRootCnt (sc cnt : Nat) : Prop :=
  7 ≤ sc ∧ sc < 48 ∧ cntMin sc ≤ cnt ∧ cnt ≤ 32 ∧ cnt * slotStride sc ≤ 1048575 ∧
  (sc ≤ 25 → cnt * slotStride sc + 16 ≤ 65536)

theorem validRootCnt_iff_dec {sc cnt : Nat} :
    ValidRootCnt sc cnt ↔ validRootCntDec sc cnt = true := by
  unfold ValidRootCnt validRootCntDec
  by_cases h25 : sc ≤ 25
  · simp [h25, and_assoc]
  · simp [h25]

/-- Maximum `pageAlignUp (cnt * slotStride sc + 16)` across all `ValidRootCnt sc cnt`. -/
def maxRootBytesTab : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 8192, 8192, 8192, 8192, 8192, 12288, 12288, 16384, 16384, 20480, 24576, 28672, 32768, 40960, 45056, 53248, 65536, 65536, 65536, 106496, 131072, 151552, 176128, 212992, 262144, 303104, 352256, 421888, 524288, 602112, 700416, 839680, 1048576, 1048576, 1048576, 1048576, 1048576, 1048576, 1048576, 1048576, 1048576]

def maxRootBytes (sc : Nat) : Nat :=
  maxRootBytesTab.getD sc 0

/-- Maximum `⌈pageAlignUp (cnt * slotStride sc + 16) / cnt⌉` across all `ValidRootCnt sc cnt`. -/
def ceilRootPerSlotTab : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2731, 2731, 4096, 4096, 4096, 4096, 8192, 8192, 8192, 8192, 12288, 12288, 16384, 16384, 20480, 24576, 28672, 32768, 40960, 45056, 53248, 65536, 77824, 90112, 106496, 131072]

def ceilRootPerSlot (sc : Nat) : Nat :=
  ceilRootPerSlotTab.getD sc 0

/-- Minimum child slot count `cnt` for a nested group of class `ch` placed in parent class `pSc`
    (`0` when `(ch, pSc)` is not a valid nesting edge; `ch ≥ 20` never nests). -/
def minCntEdgeTab : List (List Nat) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 15, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 12, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 4, 0, 5, 7, 8, 9, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 4, 5, 0, 6, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 4, 0, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

def minCntEdge (ch pSc : Nat) : Nat :=
  (minCntEdgeTab.getD ch []).getD pSc 0

private def checkGeomTables : Bool :=
  (List.range 48).all fun sc =>
    (List.range 33).all fun cnt =>
      (if validRootCntDec sc cnt then
        let b := pageAlignUp (cnt * slotStride sc + 16)
        decide (b ≤ maxRootBytes sc ∧ b ≤ ceilRootPerSlot sc * cnt)
       else true) &&
      (if validNestedCntDec sc cnt then
        let pSc := sizeToClassUnits (cnt * sizeClass sc)
        decide (cntMin sc ≤ cnt ∧ pSc < 48 ∧ sc < pSc ∧
          0 < minCntEdge sc pSc ∧ minCntEdge sc pSc ≤ cnt)
       else true)

private theorem checkGeomTables_true : checkGeomTables = true := by
  decide +kernel

theorem validRootCnt_bounds {sc cnt : Nat} (hv : ValidRootCnt sc cnt) :
    pageAlignUp (cnt * slotStride sc + 16) ≤ maxRootBytes sc ∧
    pageAlignUp (cnt * slotStride sc + 16) ≤ ceilRootPerSlot sc * cnt := by
  have hsc : sc < 48 := hv.2.1
  have hcnt : cnt < 33 := by have := hv.2.2.2.1; omega
  have hDec : validRootCntDec sc cnt = true := validRootCnt_iff_dec.mp hv
  have hRow := List.all_eq_true.mp checkGeomTables_true sc (List.mem_range.mpr hsc)
  have hCell := List.all_eq_true.mp hRow cnt (List.mem_range.mpr hcnt)
  rw [Bool.and_eq_true] at hCell
  have hL := hCell.1
  simp only [hDec, ↓reduceIte, decide_eq_true_eq] at hL
  exact hL

theorem validNestedCnt_bounds {sc cnt : Nat} (hsc : sc < 48) (hv : ValidNestedCnt sc cnt) :
    let pSc := sizeToClassUnits (cnt * sizeClass sc)
    cntMin sc ≤ cnt ∧ pSc < 48 ∧ sc < pSc ∧
    0 < minCntEdge sc pSc ∧ minCntEdge sc pSc ≤ cnt := by
  have hcnt : cnt < 33 := by have := hv.2.1; omega
  have hDec : validNestedCntDec sc cnt = true := validNestedCnt_iff_dec.mp hv
  have hRow := List.all_eq_true.mp checkGeomTables_true sc (List.mem_range.mpr hsc)
  have hCell := List.all_eq_true.mp hRow cnt (List.mem_range.mpr hcnt)
  rw [Bool.and_eq_true] at hCell
  have hR := hCell.2
  simp only [hDec, ↓reduceIte, decide_eq_true_eq] at hR
  exact hR

private def checkRootScGeSeven : Bool :=
  (List.range 7).all fun sc =>
    (List.range 3).all fun j =>
      let cnt := (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat
      decide (cnt * slotStride sc + 16 ≤ 2048)

private theorem checkRootScGeSeven_true : checkRootScGeSeven = true := by
  decide +kernel

/-- Any `sc < 48` entering `alloc_group`'s root path (`2048 < cnt * slotStride sc + 16` with
    `small_cnt_tab` entry on `sc ≤ 8`) satisfies `7 ≤ sc`. -/
theorem root_sc_ge_seven_of_gt2048 {sc cnt : Nat}
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hgt : 2048 < cnt * slotStride sc + 16) :
    7 ≤ sc := by
  apply Classical.byContradiction
  intro hlt
  have hsc7 : sc < 7 := by omega
  obtain ⟨j, hj, rfl⟩ := hsm (by omega)
  have hRow := List.all_eq_true.mp checkRootScGeSeven_true sc (List.mem_range.mpr hsc7)
  have hCell := List.all_eq_true.mp hRow j (List.mem_range.mpr hj)
  simp only [decide_eq_true_eq] at hCell
  omega

/-- `slotStride sc - 4` uniquely identifies `sc < 48` (strict monotonicity of `sizeClass`). -/
theorem slotStride_sub4_inj {sc1 sc2 : Nat} (h1 : sc1 < 48) (h2 : sc2 < 48)
    (heq : slotStride sc1 - 4 = slotStride sc2 - 4) : sc1 = sc2 := by
  have ⟨hb1, _⟩ := sizeClass_bounds h1
  have ⟨hb2, _⟩ := sizeClass_bounds h2
  have hStrEq : slotStride sc1 = slotStride sc2 := by
    unfold slotStride at heq ⊢
    omega
  have hScEq : sizeClass sc1 = sizeClass sc2 := by
    unfold slotStride at hStrEq
    omega
  rcases Nat.lt_trichotomy sc1 sc2 with hlt | rfl | hgt
  · have := sizeClass_strictMono hlt h2; omega
  · rfl
  · have := sizeClass_strictMono hgt h1; omega

/-! ## Occupancy, Group-Count, Edge, and Root-Byte Recurrences -/

def occPreBoundAux (pk : List Nat) : Nat → Nat → Nat
  | 0, sc => pk.getD sc 0 + 4
  | fuel + 1, sc =>
    pk.getD sc 0 + 4 +
    ((List.range sc).map fun ch =>
      let m := minCntEdge ch sc
      if 0 < m then 1 + occPreBoundAux pk fuel ch / m else 0).sum

private theorem occPreBoundAux_fuel_irrel (pk : List Nat) :
    ∀ {fuel1 fuel2 sc : Nat}, sc ≤ fuel1 → sc ≤ fuel2 →
      occPreBoundAux pk fuel1 sc = occPreBoundAux pk fuel2 sc
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, sc, h1, _ => by
    have h0 : sc = 0 := by omega
    subst h0; rfl
  | _ + 1, 0, sc, _, h2 => by
    have h0 : sc = 0 := by omega
    subst h0; rfl
  | f1 + 1, f2 + 1, sc, h1, h2 => by
    simp only [occPreBoundAux]
    congr 1
    congr 1
    refine List.map_congr_left (fun ch hch => ?_)
    have hlt : ch < sc := List.mem_range.mp hch
    rw [occPreBoundAux_fuel_irrel pk (by omega : ch ≤ f1) (by omega : ch ≤ f2)]

/-- Upper bound on total occupied slots in `sc` right before `alloc_group(sc)` creates a new group
    (`active[sc] == 0`), given per-class user peak watermark `pk` (`pk.length = 48`) and at most `4`
    in-flight claimed slots globally. -/
def occPreBound (pk : List Nat) (sc : Nat) : Nat :=
  occPreBoundAux pk sc sc

/-- Upper bound on `(allGroups st sc).length` for `sc < 48`. -/
def gBound (pk : List Nat) (sc : Nat) : Nat :=
  1 + occPreBound pk sc / cntMin sc

/-- Upper bound on `(nestedEdge st ch pSc).length` for `ch, pSc < 48`. -/
def edgeBound (pk : List Nat) (ch pSc : Nat) : Nat :=
  let m := minCntEdge ch pSc
  if 0 < m then 1 + occPreBound pk ch / m else 0

/-- Upper bound on `rootBytes st sc` for `sc < 48`. -/
def rBound (pk : List Nat) (sc : Nat) : Nat :=
  maxRootBytes sc + ceilRootPerSlot sc * occPreBound pk sc

theorem occPreBound_eq (pk : List Nat) (sc : Nat) :
    occPreBound pk sc =
      pk.getD sc 0 + 4 + ((List.range sc).map fun ch => edgeBound pk ch sc).sum := by
  cases sc with
  | zero => rfl
  | succ k =>
    unfold occPreBound edgeBound
    simp only [occPreBoundAux]
    congr 1
    congr 1
    refine List.map_congr_left (fun ch hch => ?_)
    have hlt : ch < k + 1 := List.mem_range.mp hch
    rw [occPreBoundAux_fuel_irrel pk (by omega : ch ≤ k) (Nat.le_refl ch)]
    rfl

private theorem list_sum_le_sum {α : Type} (xs : List α) (f g : α → Nat)
    (hle : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle x List.mem_cons_self
    have h2 := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

private theorem occPreBound_mono_aux {pk1 pk2 : List Nat}
    (hpk : ∀ j < 48, pk1.getD j 0 ≤ pk2.getD j 0) :
    ∀ (fuel sc : Nat), sc ≤ fuel → sc < 48 → occPreBound pk1 sc ≤ occPreBound pk2 sc
  | 0, sc, hle, hsc => by
    have h0 : sc = 0 := by omega
    subst h0
    rw [occPreBound_eq, occPreBound_eq]
    have := hpk 0 hsc
    simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  | fuel + 1, sc, hle, hsc => by
    rw [occPreBound_eq, occPreBound_eq]
    have h0 := hpk sc hsc
    have hSum : ((List.range sc).map fun ch => edgeBound pk1 ch sc).sum ≤
        ((List.range sc).map fun ch => edgeBound pk2 ch sc).sum := by
      refine list_sum_le_sum (List.range sc) _ _ (fun ch hch => ?_)
      have hlt : ch < sc := List.mem_range.mp hch
      have hSub := occPreBound_mono_aux hpk fuel ch (by omega) (Nat.lt_trans hlt hsc)
      unfold edgeBound
      by_cases hm : 0 < minCntEdge ch sc
      · simp only [hm, ↓reduceIte]
        have := Nat.div_le_div_right (c := minCntEdge ch sc) hSub
        omega
      · simp [hm]
    omega

theorem occPreBound_mono {pk1 pk2 : List Nat} {sc : Nat} (hsc : sc < 48)
    (hpk : ∀ j < 48, pk1.getD j 0 ≤ pk2.getD j 0) :
    occPreBound pk1 sc ≤ occPreBound pk2 sc :=
  occPreBound_mono_aux hpk sc sc (Nat.le_refl sc) hsc

theorem gBound_mono {pk1 pk2 : List Nat} {sc : Nat} (hsc : sc < 48)
    (hpk : ∀ j < 48, pk1.getD j 0 ≤ pk2.getD j 0) :
    gBound pk1 sc ≤ gBound pk2 sc := by
  unfold gBound
  have h := Nat.div_le_div_right (c := cntMin sc) (occPreBound_mono hsc hpk)
  omega

theorem edgeBound_mono {pk1 pk2 : List Nat} {ch : Nat} (pSc : Nat) (hch : ch < 48)
    (hpk : ∀ j < 48, pk1.getD j 0 ≤ pk2.getD j 0) :
    edgeBound pk1 ch pSc ≤ edgeBound pk2 ch pSc := by
  unfold edgeBound
  by_cases hm : 0 < minCntEdge ch pSc
  · simp only [hm, ↓reduceIte]
    have h := Nat.div_le_div_right (c := minCntEdge ch pSc) (occPreBound_mono hch hpk)
    omega
  · simp [hm]

theorem rBound_mono {pk1 pk2 : List Nat} {sc : Nat} (hsc : sc < 48)
    (hpk : ∀ j < 48, pk1.getD j 0 ≤ pk2.getD j 0) :
    rBound pk1 sc ≤ rBound pk2 sc := by
  unfold rBound
  have h := Nat.mul_le_mul_left (ceilRootPerSlot sc) (occPreBound_mono hsc hpk)
  omega

/-! ## `65536`-Scaled Linear Upper-Bound Tables -/

/-- Homogeneous `48`-variable linear form `∑_{j=0}^{47} coeff j * pk[j]`. -/
def linForm (coeff : Nat → Nat) (pk : List Nat) : Nat :=
  ((List.range 48).map fun j => coeff j * pk.getD j 0).sum

theorem linForm_add (c1 c2 : Nat → Nat) (pk : List Nat) :
    linForm (fun j => c1 j + c2 j) pk = linForm c1 pk + linForm c2 pk := by
  unfold linForm
  suffices ∀ xs : List Nat,
      (xs.map fun j => (c1 j + c2 j) * pk.getD j 0).sum =
        (xs.map fun j => c1 j * pk.getD j 0).sum + (xs.map fun j => c2 j * pk.getD j 0).sum from
    this (List.range 48)
  intro xs
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mul, ih]
    omega

theorem linForm_const_mul (k : Nat) (c : Nat → Nat) (pk : List Nat) :
    linForm (fun j => k * c j) pk = k * linForm c pk := by
  unfold linForm
  suffices ∀ xs : List Nat,
      (xs.map fun j => k * c j * pk.getD j 0).sum =
        k * (xs.map fun j => c j * pk.getD j 0).sum from
    this (List.range 48)
  intro xs
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.mul_assoc k (c x) (pk.getD x 0), ih, ← Nat.mul_add]

theorem linForm_mono_coeff {c1 c2 : Nat → Nat} (pk : List Nat)
    (hle : ∀ j < 48, c1 j ≤ c2 j) :
    linForm c1 pk ≤ linForm c2 pk := by
  unfold linForm
  refine list_sum_le_sum (List.range 48) _ _ (fun j hj => ?_)
  exact Nat.mul_le_mul_right _ (hle j (List.mem_range.mp hj))

private theorem sum_eq_zero_of_forall {xs : List Nat} {f : Nat → Nat}
    (h0 : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h0 x List.mem_cons_self, ih (fun y hy => h0 y (List.mem_cons_of_mem x hy))]

private theorem sum_indicator_range :
    ∀ (n sc v : Nat), sc < n →
      ((List.range n).map fun j => if j = sc then v else 0).sum = v
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, sc, v, h => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    by_cases heq : n = sc
    · subst heq
      have hZ : ((List.range n).map fun j => if j = n then v else 0).sum = 0 :=
        sum_eq_zero_of_forall (fun j hj => by
          have := List.mem_range.mp hj
          simp [Nat.ne_of_lt this])
      simp [hZ]
    · have hlt : sc < n := by omega
      rw [sum_indicator_range n sc v hlt]
      simp [heq]

theorem linForm_unit {sc : Nat} (hsc : sc < 48) (pk : List Nat) :
    linForm (fun j => if j = sc then FineScale else 0) pk = FineScale * pk.getD sc 0 := by
  unfold linForm
  have hMap : ((List.range 48).map fun j => (if j = sc then FineScale else 0) * pk.getD j 0) =
      ((List.range 48).map fun j => if j = sc then FineScale * pk.getD sc 0 else 0) := by
    refine List.map_congr_left (fun j _ => ?_)
    by_cases h : j = sc
    · subst h; simp
    · simp [h]
  rw [hMap]
  exact sum_indicator_range 48 sc (FineScale * pk.getD sc 0) hsc

private theorem ceil_mul_ge (a m : Nat) (hm : 0 < m) :
    a ≤ m * ((a + m - 1) / m) := by
  have hMod := Nat.div_add_mod (a + m - 1) m
  have hLt := Nat.mod_lt (a + m - 1) hm
  omega

/-- Key `Nat` floor-division linearization step: if `S * X ≤ C + linForm A pk` and `0 < m`,
    then `S * (X / m) ≤ C / m + linForm (fun j => (A j + m - 1) / m) pk`. -/
theorem scaled_div_linear_le {S X C m : Nat} {A : Nat → Nat} {pk : List Nat}
    (hm : 0 < m) (hX : S * X ≤ C + linForm A pk) :
    S * (X / m) ≤ C / m + linForm (fun j => (A j + m - 1) / m) pk := by
  let W := linForm (fun j => (A j + m - 1) / m) pk
  have hCoeff : linForm A pk ≤ m * W := by
    rw [← linForm_const_mul]
    exact linForm_mono_coeff pk (fun j _ => ceil_mul_ge (A j) m hm)
  have hMul : m * (S * (X / m)) ≤ C + m * W := by
    have h1 : m * (X / m) ≤ X := Nat.mul_div_le X m
    have h2 : S * (m * (X / m)) ≤ S * X := Nat.mul_le_mul_left S h1
    have h3 : m * (S * (X / m)) = S * (m * (X / m)) := by rw [Nat.mul_left_comm]
    omega
  have hDiv := Nat.div_le_div_right (c := m) hMul
  rw [Nat.mul_div_right _ hm, Nat.add_mul_div_left C W hm] at hDiv
  exact hDiv

/-- Precomputed `occConstS` and `occCoeffS` flat tables (verified by `checkOccLinRec_true`). -/
def occConstSTab : List Nat :=
  [262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 655360, 1321952, 262144, 939349, 546133, 2779999, 365129, 1330379, 2414320, 3822750, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144, 262144]

def occCoeffSTab : List (List Nat) := [
  [65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 32768, 32768, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2185, 4370, 6554, 9363, 10923, 13108, 16384, 0, 0, 21846, 0, 32768, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 16384, 21846, 0, 32768, 32768, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16384, 21846, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1093, 4300, 6554, 9052, 10924, 13108, 16384, 9363, 10923, 40415, 29492, 32768, 21846, 21846, 32768, 32768, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 9363, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 19115, 21846, 13108, 16384, 16384, 21846, 0, 32768, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [729, 1457, 2185, 3121, 3641, 4370, 5462, 0, 0, 30948, 36670, 32769, 29492, 29492, 16384, 21846, 0, 32768, 32768, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1094, 3243, 4916, 8982, 10815, 12952, 15929, 9052, 10144, 43644, 35864, 33939, 32769, 32769, 29492, 32768, 21846, 21846, 0, 32768, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536]
]

def occConstS (sc : Nat) : Nat :=
  occConstSTab.getD sc 0

def occCoeffS (sc j : Nat) : Nat :=
  (occCoeffSTab.getD sc []).getD j 0

def gConstS (sc : Nat) : Nat :=
  FineScale + occConstS sc / cntMin sc

def gCoeffS (sc j : Nat) : Nat :=
  (occCoeffS sc j + cntMin sc - 1) / cntMin sc

def grpWtSTab : List Nat :=
  [4737, 11056, 16659, 24623, 29076, 34877, 43464, 41976, 43302, 140011, 130203, 116368, 99398, 99398, 83013, 76459, 60075, 60075, 49152, 49152, 32768, 32768, 32768, 32768, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536]

def grpWtS (j : Nat) : Nat :=
  grpWtSTab.getD j 0

def slotRootWtSTab : List Nat :=
  [11691957, 30591860, 46238015, 70767213, 84221992, 100996750, 125527685, 178114164, 184291296, 624425248, 582852210, 522200796, 449656423, 449656423, 371354556, 350477426, 260988018, 283368562, 223707136, 223707136, 134217728, 134217728, 178978816, 178978816, 268435456, 268435456, 268435456, 268435456, 536870912, 536870912, 536870912, 536870912, 805306368, 805306368, 1073741824, 1073741824, 1342177280, 1610612736, 1879048192, 2147483648, 2684354560, 2952790016, 3489660928, 4294967296, 5100273664, 5905580032, 6979321856, 8589934592]

def slotRootWtS (j : Nat) : Nat :=
  slotRootWtSTab.getD j 0

def slotWtTab : List Nat :=
  [179, 467, 706, 1080, 1286, 1542, 1916, 2718, 2813, 9528, 8894, 7969, 6862, 6862, 5667, 5348, 3983, 4324, 3414, 3414, 2048, 2048, 2731, 2731, 4096, 4096, 4096, 4096, 8192, 8192, 8192, 8192, 12288, 12288, 16384, 16384, 20480, 24576, 28672, 32768, 40960, 45056, 53248, 65536, 77824, 90112, 106496, 131072]

def slotWt (j : Nat) : Nat :=
  slotWtTab.getD j 0

/-- Size-class bump eligibility: `__libc_malloc_impl` may bump `sc` to `sc + 1` when
    `4 ≤ sc ≤ 31 ∧ sc ≠ 6 ∧ sc % 2 = 0`. -/
def coarseBumpable (sc : Nat) : Bool :=
  decide (4 ≤ sc ∧ sc ≤ 31 ∧ sc ≠ 6 ∧ sc % 2 = 0)

def coarseAlt (sc : Nat) : Nat :=
  if coarseBumpable sc then sc + 1 else sc

def coarseSlotWt (sc : Nat) : Nat :=
  max (slotWt sc) (slotWt (coarseAlt sc))

def coarseGrpWtS (sc : Nat) : Nat :=
  max (grpWtS sc) (grpWtS (coarseAlt sc))

def gBaseConst : Nat :=
  (((List.range 48).map gConstS).sum + FineScale - 1) / FineScale

def BaseRootFine : Nat :=
  ((List.range 48).map maxRootBytes).sum +
  (((List.range 48).map fun sc => ceilRootPerSlot sc * occConstS sc).sum + FineScale - 1) / FineScale

/-! ## Table Recurrence Identities and Closed Linear Bounds -/

private def checkOccLinRec : Bool :=
  (List.range 48).all fun sc =>
    let expC := 4 * FineScale +
      ((List.range sc).map fun ch =>
        let m := minCntEdge ch sc
        if 0 < m then FineScale + occConstS ch / m else 0).sum
    decide (occConstS sc = expC) &&
    (List.range 48).all fun j =>
      let expA := (if j = sc then FineScale else 0) +
        ((List.range sc).map fun ch =>
          let m := minCntEdge ch sc
          if 0 < m then (occCoeffS ch j + m - 1) / m else 0).sum
      decide (occCoeffS sc j = expA)

private theorem checkOccLinRec_true : checkOccLinRec = true := by
  decide +kernel

private def checkColSums : Bool :=
  (List.range 48).all fun j =>
    decide (grpWtS j = ((List.range 48).map fun sc => gCoeffS sc j).sum) &&
    decide (slotRootWtS j = ((List.range 48).map fun sc => ceilRootPerSlot sc * occCoeffS sc j).sum) &&
    decide (slotWt j = (slotRootWtS j + FineScale - 1) / FineScale)

private theorem checkColSums_true : checkColSums = true := by
  decide +kernel

theorem coarseAlt_bounds {sc sc' : Nat} (hsc : sc < 48)
    (halt : sc' = sc ∨ sc' = coarseAlt sc) :
    sc' < 48 ∧ slotWt sc' ≤ coarseSlotWt sc ∧ grpWtS sc' ≤ coarseGrpWtS sc := by
  unfold coarseSlotWt coarseGrpWtS
  rcases halt with rfl | rfl
  · exact ⟨hsc, Nat.le_max_left _ _, Nat.le_max_left _ _⟩
  · refine ⟨?_, Nat.le_max_right _ _, Nat.le_max_right _ _⟩
    unfold coarseAlt coarseBumpable
    by_cases hb : 4 ≤ sc ∧ sc ≤ 31 ∧ sc ≠ 6 ∧ sc % 2 = 0
    · simp [hb]; omega
    · simp [hb, hsc]

private theorem linForm_sum_rows (xs : List Nat) (f : Nat → Nat → Nat) (pk : List Nat) :
    (xs.map fun r => linForm (f r) pk).sum =
      linForm (fun j => (xs.map fun r => f r j).sum) pk := by
  induction xs with
  | nil =>
    unfold linForm
    exact (sum_eq_zero_of_forall (fun _ _ => by simp)).symm
  | cons r rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← linForm_add]

private theorem occPreBound_scaled_le_aux (pk : List Nat) :
    ∀ (fuel sc : Nat), sc ≤ fuel → sc < 48 →
      FineScale * occPreBound pk sc ≤ occConstS sc + linForm (occCoeffS sc) pk
  | 0, sc, hle, hsc => by
    have h0 : sc = 0 := by omega
    subst h0
    have hRow := List.all_eq_true.mp checkOccLinRec_true 0 (List.mem_range.mpr hsc)
    rw [Bool.and_eq_true] at hRow
    have hConstEq : occConstS 0 = 4 * FineScale := by simpa using hRow.1
    have hCoeffEq : ∀ j < 48, occCoeffS 0 j = if j = 0 then FineScale else 0 := by
      intro j hj
      have hCell := List.all_eq_true.mp hRow.2 j (List.mem_range.mpr hj)
      simpa using hCell
    have h1 := linForm_mono_coeff pk (fun j hj => Nat.le_of_eq (hCoeffEq j hj))
    have h2 := linForm_mono_coeff pk (fun j hj => Nat.le_of_eq (hCoeffEq j hj).symm)
    have hLinEq : linForm (occCoeffS 0) pk = FineScale * pk.getD 0 0 :=
      (Nat.le_antisymm h1 h2).trans (linForm_unit hsc pk)
    rw [occPreBound_eq, hConstEq, hLinEq]
    simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.add_zero, Nat.mul_add]
    omega
  | fuel + 1, sc, hle, hsc => by
    have hRow := List.all_eq_true.mp checkOccLinRec_true sc (List.mem_range.mpr hsc)
    rw [Bool.and_eq_true] at hRow
    have hConstEq : occConstS sc = 4 * FineScale +
        ((List.range sc).map fun ch =>
          let m := minCntEdge ch sc
          if 0 < m then FineScale + occConstS ch / m else 0).sum := by
      simpa using hRow.1
    have hCoeffEq : ∀ j < 48, occCoeffS sc j =
        (if j = sc then FineScale else 0) +
        ((List.range sc).map fun ch =>
          let m := minCntEdge ch sc
          if 0 < m then (occCoeffS ch j + m - 1) / m else 0).sum := by
      intro j hj
      have hCell := List.all_eq_true.mp hRow.2 j (List.mem_range.mpr hj)
      simpa using hCell
    have h1 := linForm_mono_coeff pk (fun j hj => Nat.le_of_eq (hCoeffEq j hj))
    have h2 := linForm_mono_coeff pk (fun j hj => Nat.le_of_eq (hCoeffEq j hj).symm)
    have hLinEq : linForm (occCoeffS sc) pk =
        FineScale * pk.getD sc 0 +
        ((List.range sc).map fun ch =>
          linForm (fun j =>
            let m := minCntEdge ch sc
            if 0 < m then (occCoeffS ch j + m - 1) / m else 0) pk).sum := by
      rw [Nat.le_antisymm h1 h2, linForm_add, linForm_unit hsc, ← linForm_sum_rows]
    rw [occPreBound_eq, Nat.mul_add, Nat.mul_add, hConstEq, hLinEq]
    have hEdgeSum :
        FineScale * ((List.range sc).map fun ch => edgeBound pk ch sc).sum ≤
        ((List.range sc).map fun ch =>
          let m := minCntEdge ch sc
          if 0 < m then FineScale + occConstS ch / m else 0).sum +
        ((List.range sc).map fun ch =>
          linForm (fun j =>
            let m := minCntEdge ch sc
            if 0 < m then (occCoeffS ch j + m - 1) / m else 0) pk).sum := by
      have hTerm : ∀ ch ∈ List.range sc,
          FineScale * edgeBound pk ch sc ≤
            (let m := minCntEdge ch sc; if 0 < m then FineScale + occConstS ch / m else 0) +
            linForm (fun j =>
              let m := minCntEdge ch sc
              if 0 < m then (occCoeffS ch j + m - 1) / m else 0) pk := by
        intro ch hch
        have hlt : ch < sc := List.mem_range.mp hch
        have hSub := occPreBound_scaled_le_aux pk fuel ch (by omega) (Nat.lt_trans hlt hsc)
        unfold edgeBound
        by_cases hm : 0 < minCntEdge ch sc
        · simp only [hm, ↓reduceIte, Nat.mul_add, Nat.mul_one]
          have hDiv := scaled_div_linear_le hm hSub
          omega
        · simp only [hm, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
          exact Nat.zero_le _
      clear hConstEq hCoeffEq hLinEq hRow h1 h2
      suffices ∀ xs : List Nat,
          (∀ ch ∈ xs, FineScale * edgeBound pk ch sc ≤
            (let m := minCntEdge ch sc; if 0 < m then FineScale + occConstS ch / m else 0) +
            linForm (fun j =>
              let m := minCntEdge ch sc
              if 0 < m then (occCoeffS ch j + m - 1) / m else 0) pk) →
          FineScale * (xs.map fun ch => edgeBound pk ch sc).sum ≤
            (xs.map fun ch =>
              let m := minCntEdge ch sc
              if 0 < m then FineScale + occConstS ch / m else 0).sum +
            (xs.map fun ch =>
              linForm (fun j =>
                let m := minCntEdge ch sc
                if 0 < m then (occCoeffS ch j + m - 1) / m else 0) pk).sum from
        this (List.range sc) hTerm
      intro xs hT
      induction xs with
      | nil => simp
      | cons ch rest ihL =>
        simp only [List.map_cons, List.sum_cons, Nat.mul_add]
        have hA := hT ch List.mem_cons_self
        have hB := ihL (fun y hy => hT y (List.mem_cons_of_mem ch hy))
        dsimp only at hA hB ⊢
        omega
    omega

theorem occPreBound_scaled_le (pk : List Nat) {sc : Nat} (hsc : sc < 48) :
    FineScale * occPreBound pk sc ≤ occConstS sc + linForm (occCoeffS sc) pk :=
  occPreBound_scaled_le_aux pk sc sc (Nat.le_refl sc) hsc

theorem gBound_scaled_le (pk : List Nat) {sc : Nat} (hsc : sc < 48) :
    FineScale * gBound pk sc ≤ gConstS sc + linForm (gCoeffS sc) pk := by
  unfold gBound gConstS gCoeffS
  rw [Nat.mul_add, Nat.mul_one]
  have hDiv := scaled_div_linear_le (cntMin_pos hsc) (occPreBound_scaled_le pk hsc)
  omega

private theorem sum_scaled_list (S : Nat) (xs : List Nat) (f : Nat → Nat) :
    S * (xs.map f).sum = (xs.map fun x => S * f x).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]

private theorem sum_pair_le {xs : List Nat} {f c1 c2 : Nat → Nat}
    (h : ∀ x ∈ xs, f x ≤ c1 x + c2 x) :
    (xs.map f).sum ≤ (xs.map c1).sum + (xs.map c2).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

theorem sum_gBound_scaled_le (pk : List Nat) :
    FineScale * ((List.range 48).map (gBound pk)).sum ≤
      ((List.range 48).map gConstS).sum + linForm grpWtS pk := by
  rw [sum_scaled_list]
  have h1 : ((List.range 48).map fun sc => FineScale * gBound pk sc).sum ≤
      ((List.range 48).map gConstS).sum +
      ((List.range 48).map fun sc => linForm (gCoeffS sc) pk).sum :=
    sum_pair_le (fun sc hsc => gBound_scaled_le pk (List.mem_range.mp hsc))
  rw [linForm_sum_rows] at h1
  have hCol : linForm (fun j => ((List.range 48).map fun sc => gCoeffS sc j).sum) pk ≤
      linForm grpWtS pk := by
    refine linForm_mono_coeff pk (fun j hj => ?_)
    have hCell := List.all_eq_true.mp checkColSums_true j (List.mem_range.mpr hj)
    rw [Bool.and_eq_true, Bool.and_eq_true] at hCell
    have hEq : grpWtS j = ((List.range 48).map fun sc => gCoeffS sc j).sum := by
      simpa using hCell.1.1
    omega
  omega

/-- Combined small/medium + straddling group count bound:
    `∑_{sc < 48} gBound pk sc + pkStraddle ≤ gBaseConst + (cumGroupsS + FineScale - 1) / FineScale`
    whenever `linForm grpWtS pk + FineScale * pkStraddle ≤ cumGroupsS`. -/
theorem sum_gBound_le (pk : List Nat) {pkStraddle cumGroupsS : Nat}
    (hCum : linForm grpWtS pk + FineScale * pkStraddle ≤ cumGroupsS) :
    ((List.range 48).map (gBound pk)).sum + pkStraddle ≤
      gBaseConst + (cumGroupsS + FineScale - 1) / FineScale := by
  have hS : 0 < FineScale := by decide
  have hSc := sum_gBound_scaled_le pk
  have hA := ceil_mul_ge (((List.range 48).map gConstS).sum) FineScale hS
  have hB := ceil_mul_ge cumGroupsS FineScale hS
  have h2 : FineScale * (((List.range 48).map (gBound pk)).sum + pkStraddle) ≤
      FineScale * (gBaseConst + (cumGroupsS + FineScale - 1) / FineScale) := by
    unfold gBaseConst
    rw [Nat.mul_add, Nat.mul_add]
    dsimp only [FineScale] at hSc hCum hA hB ⊢
    omega
  exact Nat.le_of_mul_le_mul_left h2 hS

theorem sum_rBound_le (pk : List Nat) :
    ((List.range 48).map (rBound pk)).sum ≤ BaseRootFine + linForm slotWt pk := by
  have hS : 0 < FineScale := by decide
  have hSplit : ((List.range 48).map (rBound pk)).sum =
      ((List.range 48).map maxRootBytes).sum +
      ((List.range 48).map fun sc => ceilRootPerSlot sc * occPreBound pk sc).sum := by
    unfold rBound
    suffices ∀ xs : List Nat,
        (xs.map fun sc => maxRootBytes sc + ceilRootPerSlot sc * occPreBound pk sc).sum =
          (xs.map maxRootBytes).sum + (xs.map fun sc => ceilRootPerSlot sc * occPreBound pk sc).sum from
      this (List.range 48)
    intro xs
    induction xs with
    | nil => simp
    | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [hSplit]
  suffices ((List.range 48).map fun sc => ceilRootPerSlot sc * occPreBound pk sc).sum ≤
      (((List.range 48).map fun sc => ceilRootPerSlot sc * occConstS sc).sum + FineScale - 1) / FineScale +
      linForm slotWt pk by
    unfold BaseRootFine; omega
  have hScSum :
      FineScale * ((List.range 48).map fun sc => ceilRootPerSlot sc * occPreBound pk sc).sum ≤
        ((List.range 48).map fun sc => ceilRootPerSlot sc * occConstS sc).sum +
        linForm slotRootWtS pk := by
    rw [sum_scaled_list]
    have hRowLe :
        ((List.range 48).map fun sc => FineScale * (ceilRootPerSlot sc * occPreBound pk sc)).sum ≤
          ((List.range 48).map fun sc => ceilRootPerSlot sc * occConstS sc).sum +
          ((List.range 48).map fun sc =>
            linForm (fun j => ceilRootPerSlot sc * occCoeffS sc j) pk).sum := by
      refine sum_pair_le (fun sc hsc => ?_)
      have hSub := occPreBound_scaled_le pk (List.mem_range.mp hsc)
      have hMul := Nat.mul_le_mul_left (ceilRootPerSlot sc) hSub
      rw [← Nat.mul_assoc, Nat.mul_comm (ceilRootPerSlot sc) FineScale, Nat.mul_assoc] at hMul
      rw [Nat.mul_add, ← linForm_const_mul] at hMul
      exact hMul
    rw [linForm_sum_rows] at hRowLe
    have hCol :
        linForm (fun j => ((List.range 48).map fun sc => ceilRootPerSlot sc * occCoeffS sc j).sum) pk ≤
          linForm slotRootWtS pk := by
      refine linForm_mono_coeff pk (fun j hj => ?_)
      have hCell := List.all_eq_true.mp checkColSums_true j (List.mem_range.mpr hj)
      rw [Bool.and_eq_true, Bool.and_eq_true] at hCell
      have hEq : slotRootWtS j =
          ((List.range 48).map fun sc => ceilRootPerSlot sc * occCoeffS sc j).sum := by
        simpa using hCell.1.2
      omega
    omega
  have hSlotCeil : linForm slotRootWtS pk ≤ FineScale * linForm slotWt pk := by
    rw [← linForm_const_mul]
    refine linForm_mono_coeff pk (fun j hj => ?_)
    have hCell := List.all_eq_true.mp checkColSums_true j (List.mem_range.mpr hj)
    rw [Bool.and_eq_true, Bool.and_eq_true] at hCell
    have hEq : slotWt j = (slotRootWtS j + FineScale - 1) / FineScale := by
      simpa using hCell.2
    rw [hEq]
    exact ceil_mul_ge (slotRootWtS j) FineScale hS
  have hConstCeil :=
    ceil_mul_ge (((List.range 48).map fun sc => ceilRootPerSlot sc * occConstS sc).sum) FineScale hS
  have hFinal :
      FineScale * ((List.range 48).map fun sc => ceilRootPerSlot sc * occPreBound pk sc).sum ≤
        FineScale * ((((List.range 48).map fun sc => ceilRootPerSlot sc * occConstS sc).sum +
          FineScale - 1) / FineScale + linForm slotWt pk) := by
    rw [Nat.mul_add]
    omega
  exact Nat.le_of_mul_le_mul_left hFinal hS

private def checkCoarseWtCap : Bool :=
  (List.range 48).all fun sc =>
    decide (coarseSlotWt sc ≤ 131072 ∧ coarseGrpWtS sc ≤ 3 * FineScale)

private theorem checkCoarseWtCap_true : checkCoarseWtCap = true := by
  decide +kernel

theorem coarseWt_le_cap (sc : Nat) :
    coarseSlotWt sc ≤ 131072 ∧ coarseGrpWtS sc ≤ 3 * FineScale := by
  by_cases hsc : sc < 48
  · have hCell := List.all_eq_true.mp checkCoarseWtCap_true sc (List.mem_range.mpr hsc)
    exact of_decide_eq_true hCell
  · have hAlt : coarseAlt sc = sc := by
      unfold coarseAlt coarseBumpable
      have hb : ¬ (4 ≤ sc ∧ sc ≤ 31 ∧ sc ≠ 6 ∧ sc % 2 = 0) := by omega
      simp [hb]
    have hSlot0 : slotWt sc = 0 := by
      unfold slotWt
      have hNone : slotWtTab[sc]? = none :=
        List.getElem?_eq_none (by simp [slotWtTab]; omega)
      simp [List.getD, hNone]
    have hGrp0 : grpWtS sc = 0 := by
      unfold grpWtS
      have hNone : grpWtSTab[sc]? = none :=
        List.getElem?_eq_none (by simp [grpWtSTab]; omega)
      simp [List.getD, hNone]
    unfold coarseSlotWt coarseGrpWtS FineScale
    rw [hAlt, hSlot0, hGrp0]
    omega

end LibsignalBinary.Heap.Fine
