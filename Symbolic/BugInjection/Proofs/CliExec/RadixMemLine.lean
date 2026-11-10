/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Process.FastParse
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux

/-!
# Snapshot Region Loader and Stack Zero-Mapping Agreement

Defines `loadRegionsLines` to bulk-load a `List Snapshot.Region` into `BinTree Line64`, and proves
that the loaded tree with `[top - sz, top)` stack fallback agrees pointwise with
`(Memory.mapZero ⟨Snapshot.loadCellAt regions⟩ (BitVec.ofNat 64 (top - sz)) sz).cells`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMemLine

open Arm64
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (
  Cell BinTree Line64 rawCellAt
  rawCellAt_foldSetRawCell_noWrap sub_lt_iff_range
  regionToCells regionToCells_length regionToCells_getElem
  loadRegionFast linesEq_loadRegionFast
)

/-- Load a `List Snapshot.Region` into a depth-58 `BinTree Line64` in reverse order so the first
matching region wins (`Snapshot.loadCellAt` uses `List.findSome?`). -/
def loadRegionsLines : List Snapshot.Region → BinTree Line64
  | [] => .empty
  | r :: rs =>
    match loadRegionsLines rs with
    | .empty => loadRegionFast .empty r.start.toNat r.nonAnonLen r.perm r.bytes
    | .twig j u => loadRegionFast (.twig j u) r.start.toNat r.nonAnonLen r.perm r.bytes
    | .branch x y => loadRegionFast (.branch x y) r.start.toNat r.nonAnonLen r.perm r.bytes

theorem rawCellAt_loadRegionsLines (regions : List Snapshot.Region)
    (hwrap : regions.all (fun r => decide (r.start.toNat + r.bytes.length ≤ 2 ^ 64)) = true)
    (a : BitVec 64) :
    rawCellAt (loadRegionsLines regions) a.toNat = Snapshot.loadCellAt regions a := by
  induction regions with
  | nil => simp [loadRegionsLines, rawCellAt, Snapshot.loadCellAt]
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hwrap
    rcases hwrap with ⟨hr_wrap, hrs_wrap⟩
    have hbt (t : BinTree Line64) :
        (match t with
         | .empty => loadRegionFast .empty r.start.toNat r.nonAnonLen r.perm r.bytes
         | .twig j u => loadRegionFast (.twig j u) r.start.toNat r.nonAnonLen r.perm r.bytes
         | .branch x y => loadRegionFast (.branch x y) r.start.toNat r.nonAnonLen r.perm r.bytes) =
          loadRegionFast t r.start.toNat r.nonAnonLen r.perm r.bytes := by cases t <;> rfl
    simp only [loadRegionsLines, hbt, Snapshot.loadCellAt, List.findSome?_cons]
    set cs := regionToCells r.perm r.nonAnonLen 0 r.bytes
    have hlen : cs.length = r.bytes.length := regionToCells_length r.perm r.nonAnonLen 0 r.bytes
    rw [linesEq_loadRegionFast _ r.start.toNat r.nonAnonLen r.perm r.bytes a.toNat a.isLt,
      rawCellAt_foldSetRawCell_noWrap _ _ cs (by rw [hlen]; exact hr_wrap) a.toNat a.isLt]
    have hrng_iff := sub_lt_iff_range hr_wrap (a := a)
    by_cases hlt : (a - r.start).toNat < r.bytes.length
    · have hrng : r.start.toNat ≤ a.toNat ∧ a.toNat < r.start.toNat + cs.length := by
        rw [hlen]; exact hrng_iff.mp hlt
      rw [dite_eq_left_of_eq_true (eq_true hrng), dite_eq_left_of_eq_true (eq_true hlt)]; dsimp only
      have hidx : a.toNat - r.start.toNat = (a - r.start).toNat := by
        simp only [BitVec.toNat_sub]
        have heq : 2 ^ 64 - r.start.toNat + a.toNat = 2 ^ 64 + (a.toNat - r.start.toNat) := by omega
        rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hget := regionToCells_getElem r.perm r.nonAnonLen 0 r.bytes
        (a.toNat - r.start.toNat) (by omega)
      dsimp only [cs]; rw [hget]; simp only [Nat.zero_add, hidx]
    · have hrng : ¬ (r.start.toNat ≤ a.toNat ∧ a.toNat < r.start.toNat + cs.length) := by
        rw [hlen]; exact fun h1 => hlt (hrng_iff.mpr h1)
      rw [dite_eq_right_of_eq_false (eq_false hrng), dite_eq_right_of_eq_false (eq_false hlt)]
      exact ih hrs_wrap

private theorem loadCellAt_perm_mapped_of_some {regions : List Snapshot.Region} {a : BitVec 64}
    {c : Cell} (h : Snapshot.loadCellAt regions a = some c) : ∃ p b, c = (some p, b) := by
  induction regions with
  | nil => simp [Snapshot.loadCellAt] at h
  | cons r rs ih =>
    simp only [Snapshot.loadCellAt, List.findSome?_cons] at h
    by_cases hlt : (a - r.start).toNat < r.bytes.length
    · rw [dite_eq_left_of_eq_true (eq_true hlt)] at h; injection h with h; exact ⟨_, _, h.symm⟩
    · rw [dite_eq_right_of_eq_false (eq_false hlt)] at h; exact ih h

theorem baseRegions_mapZero_cells_eq (regions : List Snapshot.Region) (top sz : Nat)
    (hsz_le : sz ≤ top) (htop_le : top ≤ 2 ^ 64)
    (hreg_wrap : regions.all (fun r => decide (r.start.toNat + r.bytes.length ≤ 2 ^ 64)) = true)
    (a : BitVec 64) :
    (match rawCellAt (loadRegionsLines regions) a.toNat with
     | some c => some c
     | none =>
       if decide (top - sz ≤ a.toNat) && decide (a.toNat < top) then
         some (some Perm.rw, 0#8)
       else none) =
      (Memory.mapZero ⟨Snapshot.loadCellAt regions⟩ (BitVec.ofNat 64 (top - sz)) sz).cells a := by
  dsimp only [Memory.mapZero]
  rw [rawCellAt_loadRegionsLines regions hreg_wrap a]
  by_cases hsz0 : sz = 0
  · subst hsz0
    simp only [Nat.sub_zero, Nat.not_lt_zero, decide_false, Bool.false_and]
    cases Snapshot.loadCellAt regions a with
    | some _ => rfl
    | none =>
      have hf : (decide (top ≤ a.toNat) && decide (a.toNat < top)) = false := by
        by_cases h1 : top ≤ a.toNat
        · have h2 : ¬ (a.toNat < top) := by omega
          simp [h1, h2]
        · simp [h1]
      simp only [hf]
  · set sbNat := top - sz
    set sbBv := BitVec.ofNat 64 sbNat
    have hsb_toNat : sbBv.toNat = sbNat := Nat.mod_eq_of_lt (by dsimp only [sbNat]; omega)
    have hsb_wrap : sbBv.toNat + sz ≤ 2 ^ 64 := by rw [hsb_toNat]; dsimp only [sbNat]; omega
    have hrng_iff := sub_lt_iff_range hsb_wrap (a := a)
    rw [hsb_toNat] at hrng_iff
    have htop_eq : sbNat + sz = top := by dsimp only [sbNat]; omega
    rw [htop_eq] at hrng_iff
    generalize hcell : Snapshot.loadCellAt regions a = co
    cases co with
    | some c =>
      obtain ⟨p, b, rfl⟩ := loadCellAt_perm_mapped_of_some hcell
      have hm : (!(Memory.perm ⟨Snapshot.loadCellAt regions⟩ a).mapped) = false := by
        dsimp only [Memory.perm]; rw [hcell]; rfl
      rw [hm, Bool.and_false]; rfl
    | none =>
      have hm : (!(Memory.perm ⟨Snapshot.loadCellAt regions⟩ a).mapped) = true := by
        dsimp only [Memory.perm]; rw [hcell]; rfl
      rw [hm, Bool.and_true]
      by_cases hrng : sbNat ≤ a.toNat ∧ a.toNat < top
      · have hlt : (a - sbBv).toNat < sz := hrng_iff.mpr hrng
        have hcond1 : (decide (sbNat ≤ a.toNat) && decide (a.toNat < top)) = true := by
          simp [hrng.1, hrng.2]
        rw [hcond1, decide_eq_true hlt]
      · have hnot_lt : ¬ ((a - sbBv).toNat < sz) := fun hl => hrng (hrng_iff.mp hl)
        have hcond1 : (decide (sbNat ≤ a.toNat) && decide (a.toNat < top)) = false := by
          by_cases h1 : sbNat ≤ a.toNat
          · have h2 : ¬ (a.toNat < top) := fun h2 => hrng ⟨h1, h2⟩; simp [h1, h2]
          · simp [h1]
        rw [hcond1, decide_eq_false hnot_lt]

end Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
