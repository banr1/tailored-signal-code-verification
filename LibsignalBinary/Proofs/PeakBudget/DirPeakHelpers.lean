/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit

/-!
# Auxiliary Bounds for CLI `Dir` Peak Live-Heap Proofs

Arithmetic, `HasFineReallocCredit`, and `PhaseCreditSpec` helpers for CLI `Dir` operations:
- `signal_session_io::read_file` doubling schedule (`cliIoReadCaps 9`, `4096 * 2^j` up to `2 MiB`),
- `Path`, `Decimal`, and `AddressText` small `String` reserve / bounded-event sequences,
- `Dir::get` cache-hit (`allocBytes1Events`) and cache-miss (`Path ++ read_file ++ FreeOnlyEvs`),
- `Dir::put` / `Dir::put_str` `Vec<DirEntry>` (`48`-byte stride) growth and hit `.free` replacement.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers

set_option autoImplicit false

open LibsignalBinary.Heap
  (AllocEvent AllocCostModel SeqEnv FreeOnlyEvs
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rawVecNewCap rawVecGrowEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepReq eventStepAlign)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit
   stepEvents_rustAlloc_small stepEvents_rustAlloc_large
   stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
   stepEvents_rustRealloc_large_large)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ModelHyps PhaseCreditSpec ConcatEnv DeallocCreditSpec)

/-! ## 1. `CliIo` Doubling Schedule (`4096 * 2^j`) -/

/-- The `j`-th `Vec<u8>` buffer capacity (`4096 * 2^j`) in `signal_session_io`'s doubling schedule
(definitionally equal to `ReadLoopCommon.cliIoCap`). -/
def cliIoCap (j : Nat) : Nat := 4096 * 2 ^ j

theorem cliIoCap_zero : cliIoCap 0 = 4096 := rfl

theorem cliIoCap_succ (j : Nat) : cliIoCap (j + 1) = 2 * cliIoCap j := by
  unfold cliIoCap
  rw [Nat.pow_succ]
  omega

theorem cliIoCap_ge_4096 : ∀ j : Nat, 4096 ≤ cliIoCap j
  | 0 => Nat.le_refl 4096
  | j + 1 => by
    have ih := cliIoCap_ge_4096 j
    rw [cliIoCap_succ]
    omega

theorem cliIoCap_pos (j : Nat) : 0 < cliIoCap j := by
  have := cliIoCap_ge_4096 j
  omega

theorem cliIoCap_strictMono : ∀ {i j : Nat}, i < j → cliIoCap i < cliIoCap j
  | i, j + 1, h => by
    have hstep : cliIoCap j < cliIoCap (j + 1) := by
      have := cliIoCap_pos j
      rw [cliIoCap_succ]
      omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · exact Nat.lt_trans (cliIoCap_strictMono hlt) hstep
    · exact hstep

theorem cliIoCap_mono {i j : Nat} (h : i ≤ j) : cliIoCap i ≤ cliIoCap j := by
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · exact Nat.le_of_lt (cliIoCap_strictMono hlt)
  · exact Nat.le_refl _

theorem cliIoCap_le_fileCap {j : Nat} (hj : j ≤ 9) : cliIoCap j ≤ 2097152 :=
  cliIoCap_mono hj

/-- Index `j ∈ [0, K]` of the final doubling capacity `4096 * 2^j` reached on `r > 0` input bytes
under cap `4096 * 2^K` (definitionally equal to `ReadLoopCommon.cliIoCapIdx`). -/
def cliIoCapIdx : Nat → Nat → Nat
  | 0, _ => 0
  | K + 1, r => if r ≤ cliIoCap K then cliIoCapIdx K r else K + 1

theorem cliIoCapIdx_le : ∀ (K r : Nat), cliIoCapIdx K r ≤ K
  | 0, _ => Nat.le_refl 0
  | K + 1, r => by
    unfold cliIoCapIdx
    split
    · exact Nat.le_succ_of_le (cliIoCapIdx_le K r)
    · exact Nat.le_refl _

/-- Ordered list of buffer capacities requested by `read_stdin` (`K = 8`) or `read_file` (`K = 9`)
on an input of `r` bytes (definitionally equal to `ReadLoopCommon.cliIoReadCaps`). -/
def cliIoReadCaps (K r : Nat) : List Nat :=
  if r = 0 then []
  else (List.range (cliIoCapIdx K r + 1)).map cliIoCap

/-- Ordered `AllocEvent` tail emitted by `allocSeqPool.go` (`align = 1`) from previous capacity
`prev` across remaining doubling capacities `cs`. -/
def cliIoCapEventsGo : Nat → List Nat → List AllocEvent
  | _, [] => []
  | prev, c :: cs => rustReallocEvents prev c 1 ++ cliIoCapEventsGo c cs

/-- Ordered `AllocEvent` list emitted by `signal_session_io::{read_stdin, read_file}` along
`caps = cliIoReadCaps K r`: `[]` when `caps = []`, otherwise `rustAllocEvents c0 1` followed by
`rustReallocEvents prev c 1` for each capacity doubling step. -/
def cliIoCapEvents : List Nat → List AllocEvent
  | [] => []
  | c0 :: cs => rustAllocEvents c0 1 ++ cliIoCapEventsGo c0 cs

@[simp] theorem cliIoCapEvents_nil : cliIoCapEvents [] = [] := rfl

theorem cliIoCapEvents_readCaps_zero (K : Nat) :
    cliIoCapEvents (cliIoReadCaps K 0) = [] := rfl

theorem rustAllocEvents_cliIoCap (j : Nat) :
    rustAllocEvents (cliIoCap j) 1 = [.alloc (cliIoCap j)] := by
  have hge : 1 ≤ cliIoCap j := by
    have := cliIoCap_ge_4096 j
    omega
  unfold rustAllocEvents
  simp [hge]

theorem rustReallocEvents_cliIoCap (i j : Nat) :
    rustReallocEvents (cliIoCap i) (cliIoCap j) 1 = [.realloc 1 (cliIoCap i) (cliIoCap j)] := by
  have hge : 1 ≤ cliIoCap j := by
    have := cliIoCap_ge_4096 j
    omega
  unfold rustReallocEvents
  simp [hge]

/-- Sum of `2 * cliIoCap 0 + ... + 2 * cliIoCap j + (j + 1) * 9539`. -/
def cliIoSmallCumBound : Nat → Nat
  | 0 => 2 * cliIoCap 0 + 9539
  | j + 1 => cliIoSmallCumBound j + (2 * cliIoCap (j + 1) + 9539)

theorem cliIoSmallCumBound_mono {i j : Nat} (h : i ≤ j) :
    cliIoSmallCumBound i ≤ cliIoSmallCumBound j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    dsimp only [cliIoSmallCumBound]
    omega

/-- Tight `cumSmall` bound for `read_file` / `read_stdin` when `131072 ≤ smallMaxReq M`:
steps `0..5` (`4096 .. 131072`) use `2 * r + 9539`, and steps `≥ 6` (`≥ 262144`) charge only
`largeMetaCost M ≤ 122`. -/
def cliIoTightCumBound : Nat → Nat
  | 0 => 2 * cliIoCap 0 + 9539
  | j + 1 =>
    cliIoTightCumBound j +
      (if j + 1 ≤ 5 then 2 * cliIoCap (j + 1) + 9539 else 122)

theorem cliIoTightCumBound_mono {i j : Nat} (h : i ≤ j) :
    cliIoTightCumBound i ≤ cliIoTightCumBound j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    dsimp only [cliIoTightCumBound]
    omega

theorem cliIoTightCumBound_nine : cliIoTightCumBound 9 = 573818 := rfl

theorem cliIoTightCumBound_eight : cliIoTightCumBound 8 = 573696 := rfl

theorem cliIoSmallCumBound_nine : cliIoSmallCumBound 9 = 8475806 := rfl

theorem cliIoSmallCumBound_eight : cliIoSmallCumBound 8 = 4271963 := rfl

/-- Forward-indexed doubling event sequence `[cliIoCap 0, ..., cliIoCap j]` matching
`cliIoCapEvents ((List.range (j + 1)).map cliIoCap)`. -/
def cliIoCapSeq : Nat → List AllocEvent
  | 0 => rustAllocEvents (cliIoCap 0) 1
  | j + 1 => cliIoCapSeq j ++ rustReallocEvents (cliIoCap j) (cliIoCap (j + 1)) 1

theorem cliIoCapEventsGo_snoc_cap : ∀ (start count : Nat),
    cliIoCapEventsGo (cliIoCap start)
      (((List.range' (start + 1) count).map cliIoCap) ++ [cliIoCap (start + 1 + count)]) =
      cliIoCapEventsGo (cliIoCap start) ((List.range' (start + 1) count).map cliIoCap) ++
        rustReallocEvents (cliIoCap (start + count)) (cliIoCap (start + 1 + count)) 1
  | start, 0 => by
    simp [cliIoCapEventsGo]
  | start, count + 1 => by
    simp only [List.range'_succ, List.map_cons, List.cons_append, cliIoCapEventsGo,
      List.append_assoc]
    rw [show start + 1 + (count + 1) = (start + 1) + 1 + count by omega,
        show start + (count + 1) = (start + 1) + count by omega,
        cliIoCapEventsGo_snoc_cap (start + 1) count]

theorem cliIoCapEvents_map_range : ∀ (j : Nat),
    cliIoCapEvents ((List.range (j + 1)).map cliIoCap) = cliIoCapSeq j
  | 0 => by
    simp [cliIoCapEvents, cliIoCapEventsGo, cliIoCapSeq]
  | j + 1 => by
    have hr : List.range (j + 1 + 1) = List.range (j + 1) ++ [j + 1] := List.range_succ
    rw [hr, List.map_append, List.map_singleton]
    rw [List.range_eq_range', List.range'_succ, List.map_cons, List.cons_append]
    simp only [cliIoCapEvents, Nat.zero_add]
    have hsnoc := cliIoCapEventsGo_snoc_cap 0 j
    simp only [Nat.zero_add] at hsnoc
    rw [Nat.add_comm 1 j] at hsnoc
    rw [hsnoc, ← List.append_assoc]
    have ih := cliIoCapEvents_map_range j
    rw [List.range_eq_range', List.range'_succ, List.map_cons] at ih
    simp only [cliIoCapEvents, Nat.zero_add] at ih
    rw [ih]
    rfl

theorem cliIoCapEvents_readCaps_pos {K r : Nat} (hr : 0 < r) :
    cliIoCapEvents (cliIoReadCaps K r) = cliIoCapSeq (cliIoCapIdx K r) := by
  have hr0 : r ≠ 0 := by omega
  unfold cliIoReadCaps
  simp only [hr0, ↓reduceIte]
  exact cliIoCapEvents_map_range (cliIoCapIdx K r)

/-- Step-`j` `liveLarge` upper-bound increment along `cliIoCapSeq j`. -/
def cliIoStepLiveBound (M : AllocCostModel) [HasFineReallocCredit M] (j : Nat) : Nat :=
  if cliIoCap j ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M (cliIoCap j)

/-- Step-`j` `peakLarge` overlap bound along `cliIoCapSeq j`. -/
def cliIoStepPeakBound : Nat → Nat
  | 0 => cliIoCap 0 + 8195
  | j + 1 => (cliIoCap j + 8195) + (cliIoCap (j + 1) + 8195)

theorem cliIoStepPeakBound_mono {i j : Nat} (h : i ≤ j) :
    cliIoStepPeakBound i ≤ cliIoStepPeakBound j := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    cases k with
    | zero =>
      dsimp only [cliIoStepPeakBound]
      exact Nat.le_trans ih (Nat.le_add_right _ _)
    | succ m =>
      have hm1 := cliIoCap_mono (show m ≤ m + 1 by omega)
      have hm2 := cliIoCap_mono (show m + 1 ≤ m + 2 by omega)
      dsimp only [cliIoStepPeakBound]
      exact Nat.le_trans ih (Nat.add_le_add (Nat.add_le_add_right hm1 8195)
        (Nat.add_le_add_right hm2 8195))

/-- Unconditional `HasFineReallocCredit` telescoping bound on `cliIoCapSeq j` (requires zero
threshold assumptions on `smallMaxReq M`). -/
theorem stepEvents_cliIoCapSeq_uncond (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (st0 : M.σ) :
    ∀ (j : Nat),
      let st' := M.stepEvents (cliIoCapSeq j) st0
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st0 + cliIoSmallCumBound j ∧
      HasFineReallocCredit.liveLarge st' ≤
        HasFineReallocCredit.liveLarge st0 + cliIoStepLiveBound M j ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + cliIoStepPeakBound j)
  | 0 => by
    dsimp only [cliIoCapSeq, cliIoSmallCumBound, cliIoStepLiveBound, cliIoStepPeakBound]
    have hpos0 : 0 < cliIoCap 0 := cliIoCap_pos 0
    by_cases hsm0 : cliIoCap 0 ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hsm0, ↓reduceIte, Nat.add_zero]
      have h := stepEvents_rustAlloc_small M st0 (req := cliIoCap 0) (al := 1)
        (by decide) hpos0 hsm0
      have haff := (hSmallAff (cliIoCap 0) hsm0).1
      dsimp only at h
      exact ⟨by omega, h.2.1, Nat.le_trans h.2.2 (Nat.le_max_left _ _)⟩
    · simp only [hsm0, ↓reduceIte]
      have hgt0 : HasFineReallocCredit.smallMaxReq M < cliIoCap 0 := by omega
      have h := stepEvents_rustAlloc_large M st0 (req := cliIoCap 0) (al := 1)
        (by decide) hgt0
      have hlc := hLargeAff (cliIoCap 0) hgt0
      dsimp only at h
      exact ⟨by omega, h.2.1,
        Nat.le_trans h.2.2 (max_le_max (Nat.le_refl _) (Nat.add_le_add_left hlc _))⟩
  | j + 1 => by
    have ih := stepEvents_cliIoCapSeq_uncond M hSmallAff hLargeAff hMeta st0 j
    dsimp only at ih
    rcases ih with ⟨hcum_j, hlive_j, hpeak_j⟩
    dsimp only [cliIoCapSeq]
    rw [M.stepEvents_append]
    set st_j := M.stepEvents (cliIoCapSeq j) st0
    have hpos_j : 0 < cliIoCap j := cliIoCap_pos j
    have hpos_j1 : 0 < cliIoCap (j + 1) := cliIoCap_pos (j + 1)
    have hlt_cap : cliIoCap j < cliIoCap (j + 1) :=
      cliIoCap_strictMono (Nat.lt_succ_self j)
    have hal_new : 1 ≤ cliIoCap (j + 1) := by omega
    have hpk_mono : cliIoStepPeakBound j ≤ cliIoStepPeakBound (j + 1) :=
      cliIoStepPeakBound_mono (show j ≤ j + 1 by omega)
    have hpk_def : cliIoStepPeakBound (j + 1) = (cliIoCap j + 8195) + (cliIoCap (j + 1) + 8195) :=
      rfl
    by_cases hsm1 : cliIoCap (j + 1) ≤ HasFineReallocCredit.smallMaxReq M
    · have hsm0 : cliIoCap j ≤ HasFineReallocCredit.smallMaxReq M := by omega
      have hlive0 : HasFineReallocCredit.liveLarge st_j ≤ HasFineReallocCredit.liveLarge st0 := by
        unfold cliIoStepLiveBound at hlive_j
        simp only [hsm0, ↓reduceIte, Nat.add_zero] at hlive_j
        exact hlive_j
      have hstep := stepEvents_rustRealloc_small_small M st_j
        (old := cliIoCap j) (new := cliIoCap (j + 1)) (al := 1)
        (by decide) hal_new hpos_j hsm0 hpos_j1 hsm1
      have haff := (hSmallAff (cliIoCap (j + 1)) hsm1).2
      dsimp only at hstep
      dsimp only [cliIoSmallCumBound, cliIoStepLiveBound]
      simp only [hsm1, ↓reduceIte, Nat.add_zero]
      exact ⟨by omega, Nat.le_trans hstep.2.1 hlive0, by omega⟩
    · have hgt1 : HasFineReallocCredit.smallMaxReq M < cliIoCap (j + 1) := by omega
      have hlc1 := hLargeAff (cliIoCap (j + 1)) hgt1
      by_cases hsm0 : cliIoCap j ≤ HasFineReallocCredit.smallMaxReq M
      · have hlive0 : HasFineReallocCredit.liveLarge st_j ≤ HasFineReallocCredit.liveLarge st0 := by
          unfold cliIoStepLiveBound at hlive_j
          simp only [hsm0, ↓reduceIte, Nat.add_zero] at hlive_j
          exact hlive_j
        have hstep := stepEvents_rustRealloc_small_large M st_j
          (old := cliIoCap j) (new := cliIoCap (j + 1)) (al := 1)
          (by decide) hal_new hpos_j hsm0 hgt1
        dsimp only at hstep
        rcases hstep with ⟨hc_s, hl_s, hp_s⟩
        dsimp only [cliIoSmallCumBound, cliIoStepLiveBound]
        simp only [hsm1, ↓reduceIte]
        exact ⟨by omega, hl_s.trans (Nat.add_le_add_right hlive0 _), by omega⟩
      · have hgt0 : HasFineReallocCredit.smallMaxReq M < cliIoCap j := by omega
        have hlc0 := hLargeAff (cliIoCap j) hgt0
        have hlive0 :
            HasFineReallocCredit.liveLarge st_j ≤
              HasFineReallocCredit.liveLarge st0 + HasFineReallocCredit.largeCost M (cliIoCap j) := by
          unfold cliIoStepLiveBound at hlive_j
          simp only [hsm0, ↓reduceIte] at hlive_j
          exact hlive_j
        have hstep := stepEvents_rustRealloc_large_large M st_j
          (old := cliIoCap j) (new := cliIoCap (j + 1)) (al := 1)
          (by decide) hal_new hgt0 hgt1
        dsimp only at hstep
        rcases hstep with ⟨hc_s, hl_s, hp_s⟩
        dsimp only [cliIoSmallCumBound, cliIoStepLiveBound]
        simp only [hsm1, ↓reduceIte]
        exact ⟨by omega, by omega, by omega⟩

/-- Full `cliIoCapEvents (cliIoReadCaps 9 r)` (`read_file`, `≤ 2 MiB`) `HasFineReallocCredit`
bound (`Δcum ≤ 8,475,806`, `Δlive ≤ 2,105,347`, `Δpeak ≤ 3,162,118`, zero assumptions on
`smallMaxReq M`). -/
theorem stepEvents_cliIoReadFile_uncond (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (r : Nat) (st0 : M.σ) :
    let st' := M.stepEvents (cliIoCapEvents (cliIoReadCaps 9 r)) st0
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st0 + 8475806 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 + 2105347 ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st0) (HasFineReallocCredit.liveLarge st0 + 3162118) := by
  dsimp only
  by_cases hr : r = 0
  · subst hr
    rw [cliIoCapEvents_readCaps_zero, M.stepEvents_nil]
    omega
  · have hr_pos : 0 < r := by omega
    rw [cliIoCapEvents_readCaps_pos hr_pos]
    set j := cliIoCapIdx 9 r
    have hj : j ≤ 9 := cliIoCapIdx_le 9 r
    have hseq := stepEvents_cliIoCapSeq_uncond M hSmallAff hLargeAff hMeta st0 j
    dsimp only at hseq
    have hcum_m : cliIoSmallCumBound j ≤ 8475806 := by
      rw [← cliIoSmallCumBound_nine]
      exact cliIoSmallCumBound_mono hj
    have hcap_le : cliIoCap j ≤ 2097152 := cliIoCap_le_fileCap hj
    have hlive_m : cliIoStepLiveBound M j ≤ 2105347 := by
      unfold cliIoStepLiveBound
      split
      · omega
      · rename_i hnot
        have hlc := hLargeAff (cliIoCap j) (by omega)
        omega
    have hpeak_m : cliIoStepPeakBound j ≤ 3162118 := by
      have hp9 : cliIoStepPeakBound 9 = 3162118 := rfl
      rw [← hp9]
      exact cliIoStepPeakBound_mono hj
    exact ⟨by omega, by omega, by omega⟩

/-- Full `cliIoCapEvents (cliIoReadCaps 8 r)` (`read_stdin`, `≤ 1 MiB`) `HasFineReallocCredit`
bound (`Δcum ≤ 4,271,963`, `Δlive ≤ 1,056,771`, `Δpeak ≤ 1,589,254`, zero assumptions on
`smallMaxReq M`). -/
theorem stepEvents_cliIoReadStdin_uncond (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (r : Nat) (st0 : M.σ) :
    let st' := M.stepEvents (cliIoCapEvents (cliIoReadCaps 8 r)) st0
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st0 + 4271963 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 + 1056771 ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st0) (HasFineReallocCredit.liveLarge st0 + 1589254) := by
  dsimp only
  by_cases hr : r = 0
  · subst hr
    rw [cliIoCapEvents_readCaps_zero, M.stepEvents_nil]
    omega
  · have hr_pos : 0 < r := by omega
    rw [cliIoCapEvents_readCaps_pos hr_pos]
    set j := cliIoCapIdx 8 r
    have hj : j ≤ 8 := cliIoCapIdx_le 8 r
    have hseq := stepEvents_cliIoCapSeq_uncond M hSmallAff hLargeAff hMeta st0 j
    dsimp only at hseq
    have hcum_m : cliIoSmallCumBound j ≤ 4271963 := by
      rw [← cliIoSmallCumBound_eight]
      exact cliIoSmallCumBound_mono hj
    have hcap_le : cliIoCap j ≤ 1048576 := by
      have h8 : cliIoCap 8 = 1048576 := rfl
      rw [← h8]
      exact cliIoCap_mono hj
    have hlive_m : cliIoStepLiveBound M j ≤ 1056771 := by
      unfold cliIoStepLiveBound
      split
      · omega
      · rename_i hnot
        have hlc := hLargeAff (cliIoCap j) (by omega)
        omega
    have hpeak_m : cliIoStepPeakBound j ≤ 1589254 := by
      have hp8 : cliIoStepPeakBound 8 = 1589254 := rfl
      rw [← hp8]
      exact cliIoStepPeakBound_mono hj
    exact ⟨by omega, by omega, by omega⟩

/-- Every `read_file` doubling capacity (`j ≤ 9`) is bounded by `2 MiB` (`2,097,152` bytes). -/
theorem cliIoFile_cap_le_twoMiB {j : Nat} (hj : j ≤ 9) :
    cliIoCap j ≤ 2097152 :=
  cliIoCap_le_fileCap hj

/-- For `Dir.changed` with `cap ≤ 64`, `rawVecNewCap 4 cap ≤ 128`, so `newCap * 48 ≤ 6144`. -/
theorem growOneDir_newBytes_le {cap : Nat} (hcap : cap ≤ 64) :
    rawVecNewCap 4 cap * 48 ≤ 6144 := by
  have hnew : rawVecNewCap 4 cap ≤ 128 := by
    unfold rawVecNewCap
    omega
  omega

/-- Single-step `HasFineReallocCredit` bound for `rustAllocEvents req al` (`al ≤ 16`, `0 < req`)
when `req ≤ smallMaxReq M` and `smallAllocCost M req ≤ 2 * req + 9539`. -/
theorem stepEvents_rustAlloc_small_aff (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hpos : 0 < req) (hle : req ≤ HasFineReallocCredit.smallMaxReq M)
    (haff : HasFineReallocCredit.smallAllocCost M req ≤ 2 * req + 9539) :
    let st' := M.stepEvents (rustAllocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st + (2 * req + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have h := stepEvents_rustAlloc_small M st hal hpos hle
  dsimp only at h ⊢
  exact ⟨Nat.le_trans h.1 (Nat.add_le_add_left haff _), h.2.1, h.2.2⟩

/-- Single-step `HasFineReallocCredit` bound for `allocBytes1Events bs` when
`bs.length ≤ smallMaxReq M` (`Δlive = 0, Δpeak = 0`). -/
theorem stepEvents_allocBytes1_small_aff (M : AllocCostModel) [HasFineReallocCredit M]
    (bs : List (BitVec 8)) (st : M.σ)
    (hle : bs.length ≤ HasFineReallocCredit.smallMaxReq M)
    (haff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539) :
    let evs := if bs.length = 0 then ([] : List AllocEvent) else rustAllocEvents bs.length 1
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (2 * bs.length + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  split
  · rw [M.stepEvents_nil]
    exact ⟨Nat.le_add_right _ _, Nat.le_refl _, Nat.le_refl _⟩
  · rename_i hne
    exact stepEvents_rustAlloc_small_aff M st (al := 1) (by decide) (by omega) hle (haff _ hle)

/-- Single-step `HasFineReallocCredit` bound for `allocBytes1Events bs` for arbitrary
`bs.length ≤ maxBytes` (covering both small `≤ smallMaxReq M` and large `> smallMaxReq M`). -/
theorem stepEvents_allocBytes1_any_aff (M : AllocCostModel) [HasFineReallocCredit M]
    (bs : List (BitVec 8)) {maxBytes : Nat} (st : M.σ)
    (hmax : bs.length ≤ maxBytes)
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539)
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122) :
    let evs := if bs.length = 0 then ([] : List AllocEvent) else rustAllocEvents bs.length 1
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (2 * maxBytes + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + (maxBytes + 8195) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + (maxBytes + 8195)) := by
  dsimp only
  split
  · rw [M.stepEvents_nil]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_max_left _ _⟩
  · rename_i hne
    by_cases hsm : bs.length ≤ HasFineReallocCredit.smallMaxReq M
    · have h := stepEvents_rustAlloc_small_aff M st (al := 1) (by decide) (by omega) hsm
        (hSmallAff _ hsm)
      dsimp only at h
      refine ⟨by omega, by omega, ?_⟩
      exact Nat.le_trans h.2.2 (Nat.le_max_left _ _)
    · have hgt : HasFineReallocCredit.smallMaxReq M < bs.length := by omega
      have h := stepEvents_rustAlloc_large M st (al := 1) (by decide) hgt
      have hlc := hLargeAff bs.length hgt
      dsimp only at h
      refine ⟨by omega, by omega, ?_⟩
      have hpk := h.2.2
      omega

/-- `GrowOneDir` (`rawVecGrowEvents 48 4 8 cap`) `HasFineReallocCredit` bound when `cap.toNat ≤ 64`
and `6144 ≤ smallMaxReq M` (`Δlive = 0, Δpeak = 0`, `Δcum ≤ 21827`). -/
theorem stepEvents_growOneDir_small (M : AllocCostModel) [HasFineReallocCredit M]
    (cap : BitVec 64) (st : M.σ)
    (hcap : cap.toNat ≤ 64)
    (hsm6144 : 6144 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539) :
    let st' := M.stepEvents (rawVecGrowEvents 48 4 8 cap) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st + 21827 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have hnew_le : rawVecNewCap 4 cap.toNat * 48 ≤ 6144 := growOneDir_newBytes_le hcap
  have hnew_ge : 192 ≤ rawVecNewCap 4 cap.toNat * 48 := by
    unfold rawVecNewCap
    omega
  unfold rawVecGrowEvents
  dsimp only
  split
  · have h192_le : 4 * 48 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have h := stepEvents_rustAlloc_small M st (req := 4 * 48) (al := 8)
      (by decide) (by decide) h192_le
    have haff := (hSmallAff (4 * 48) h192_le).1
    dsimp only at h
    exact ⟨by omega, h.2.1, h.2.2⟩
  · rename_i hne0
    have hpos_cap : 0 < cap.toNat := by
      exact Nat.pos_of_ne_zero fun ht => hne0 (BitVec.eq_of_toNat_eq ht)
    have hold_pos : 0 < cap.toNat * 48 := by omega
    have hold_le : cap.toNat * 48 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have hnew_sm : rawVecNewCap 4 cap.toNat * 48 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have h := stepEvents_rustRealloc_small_small M st
      (old := cap.toNat * 48) (new := rawVecNewCap 4 cap.toNat * 48) (al := 8)
      (by decide) (by omega) hold_pos hold_le (by omega) hnew_sm
    have haff := (hSmallAff (rawVecNewCap 4 cap.toNat * 48) hnew_sm).2
    dsimp only at h
    exact ⟨by omega, h.2.1, h.2.2⟩

/-- Tight `HasFineReallocCredit` bound on `cliIoCapSeq j` (`Δcum ≤ cliIoTightCumBound j`) when
`131072 ≤ smallMaxReq M < 262144` (matching `fineCostModel`, where `smallMaxReq = 134128`). -/
theorem stepEvents_cliIoCapSeq_tight (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (st0 : M.σ) :
    ∀ (j : Nat),
      let st' := M.stepEvents (cliIoCapSeq j) st0
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st0 + cliIoTightCumBound j ∧
      HasFineReallocCredit.liveLarge st' ≤
        HasFineReallocCredit.liveLarge st0 + cliIoStepLiveBound M j ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + cliIoStepPeakBound j)
  | 0 => by
    dsimp only [cliIoCapSeq, cliIoTightCumBound, cliIoStepLiveBound, cliIoStepPeakBound]
    have hsm0 : cliIoCap 0 ≤ HasFineReallocCredit.smallMaxReq M := by
      have h0 : cliIoCap 0 = 4096 := rfl
      omega
    simp only [hsm0, ↓reduceIte, Nat.add_zero]
    have h := stepEvents_rustAlloc_small M st0 (req := cliIoCap 0) (al := 1)
      (by decide) (cliIoCap_pos 0) hsm0
    have haff := (hSmallAff (cliIoCap 0) hsm0).1
    dsimp only at h
    exact ⟨by omega, h.2.1, Nat.le_trans h.2.2 (Nat.le_max_left _ _)⟩
  | j + 1 => by
    have ih := stepEvents_cliIoCapSeq_tight M hSmLo hSmHi hSmallAff hLargeAff hMeta st0 j
    dsimp only at ih
    rcases ih with ⟨hcum_j, hlive_j, hpeak_j⟩
    dsimp only [cliIoCapSeq]
    rw [M.stepEvents_append]
    set st_j := M.stepEvents (cliIoCapSeq j) st0
    have hpos_j : 0 < cliIoCap j := cliIoCap_pos j
    have hpos_j1 : 0 < cliIoCap (j + 1) := cliIoCap_pos (j + 1)
    have hal_new : 1 ≤ cliIoCap (j + 1) := by omega
    have hpk_mono : cliIoStepPeakBound j ≤ cliIoStepPeakBound (j + 1) :=
      cliIoStepPeakBound_mono (show j ≤ j + 1 by omega)
    have hpk_def : cliIoStepPeakBound (j + 1) = (cliIoCap j + 8195) + (cliIoCap (j + 1) + 8195) :=
      rfl
    by_cases hj5 : j + 1 ≤ 5
    · have hsm1 : cliIoCap (j + 1) ≤ HasFineReallocCredit.smallMaxReq M := by
        have hc5 : cliIoCap 5 = 131072 := rfl
        have hm := cliIoCap_mono hj5
        omega
      have hsm0 : cliIoCap j ≤ HasFineReallocCredit.smallMaxReq M := by
        have hm := cliIoCap_mono (show j ≤ j + 1 by omega)
        omega
      have hlive0 : HasFineReallocCredit.liveLarge st_j ≤ HasFineReallocCredit.liveLarge st0 := by
        unfold cliIoStepLiveBound at hlive_j
        simp only [hsm0, ↓reduceIte, Nat.add_zero] at hlive_j
        exact hlive_j
      have hstep := stepEvents_rustRealloc_small_small M st_j
        (old := cliIoCap j) (new := cliIoCap (j + 1)) (al := 1)
        (by decide) hal_new hpos_j hsm0 hpos_j1 hsm1
      have haff := (hSmallAff (cliIoCap (j + 1)) hsm1).2
      dsimp only at hstep
      dsimp only [cliIoTightCumBound, cliIoStepLiveBound]
      simp only [hj5, hsm1, ↓reduceIte, Nat.add_zero]
      exact ⟨by omega, Nat.le_trans hstep.2.1 hlive0, by omega⟩
    · have hgt1 : HasFineReallocCredit.smallMaxReq M < cliIoCap (j + 1) := by
        have hc6 : cliIoCap 6 = 262144 := rfl
        have hm := cliIoCap_mono (show 6 ≤ j + 1 by omega)
        omega
      have hnot_sm1 : ¬ cliIoCap (j + 1) ≤ HasFineReallocCredit.smallMaxReq M := by omega
      have hlc1 := hLargeAff (cliIoCap (j + 1)) hgt1
      by_cases hj_eq5 : j = 5
      · have hsm0 : cliIoCap j ≤ HasFineReallocCredit.smallMaxReq M := by
          subst hj_eq5
          have hc5 : cliIoCap 5 = 131072 := rfl
          omega
        have hlive0 : HasFineReallocCredit.liveLarge st_j ≤ HasFineReallocCredit.liveLarge st0 := by
          unfold cliIoStepLiveBound at hlive_j
          simp only [hsm0, ↓reduceIte, Nat.add_zero] at hlive_j
          exact hlive_j
        have hstep := stepEvents_rustRealloc_small_large M st_j
          (old := cliIoCap j) (new := cliIoCap (j + 1)) (al := 1)
          (by decide) hal_new hpos_j hsm0 hgt1
        dsimp only at hstep
        rcases hstep with ⟨hc_s, hl_s, hp_s⟩
        dsimp only [cliIoTightCumBound, cliIoStepLiveBound]
        simp only [hj5, hnot_sm1, ↓reduceIte]
        exact ⟨by omega, hl_s.trans (Nat.add_le_add_right hlive0 _), by omega⟩
      · have hgt0 : HasFineReallocCredit.smallMaxReq M < cliIoCap j := by
          have hc6 : cliIoCap 6 = 262144 := rfl
          have hm := cliIoCap_mono (show 6 ≤ j by omega)
          omega
        have hnot_sm0 : ¬ cliIoCap j ≤ HasFineReallocCredit.smallMaxReq M := by omega
        have hlc0 := hLargeAff (cliIoCap j) hgt0
        have hlive0 :
            HasFineReallocCredit.liveLarge st_j ≤
              HasFineReallocCredit.liveLarge st0 + HasFineReallocCredit.largeCost M (cliIoCap j) := by
          unfold cliIoStepLiveBound at hlive_j
          simp only [hnot_sm0, ↓reduceIte] at hlive_j
          exact hlive_j
        have hstep := stepEvents_rustRealloc_large_large M st_j
          (old := cliIoCap j) (new := cliIoCap (j + 1)) (al := 1)
          (by decide) hal_new hgt0 hgt1
        dsimp only at hstep
        rcases hstep with ⟨hc_s, hl_s, hp_s⟩
        dsimp only [cliIoTightCumBound, cliIoStepLiveBound]
        simp only [hj5, hnot_sm1, ↓reduceIte]
        exact ⟨by omega, by omega, by omega⟩

/-- Tight `read_file` (`cliIoReadCaps 9 r`) `HasFineReallocCredit` bound (`Δcum ≤ 573,818`,
`Δlive ≤ 2,105,347`, `Δpeak ≤ 3,162,118`) when `131072 ≤ smallMaxReq M < 262144`. -/
theorem stepEvents_cliIoReadFile_tight (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (r : Nat) (st0 : M.σ) :
    let st' := M.stepEvents (cliIoCapEvents (cliIoReadCaps 9 r)) st0
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st0 + 573818 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 + 2105347 ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st0) (HasFineReallocCredit.liveLarge st0 + 3162118) := by
  dsimp only
  by_cases hr : r = 0
  · subst hr
    rw [cliIoCapEvents_readCaps_zero, M.stepEvents_nil]
    omega
  · have hr_pos : 0 < r := by omega
    rw [cliIoCapEvents_readCaps_pos hr_pos]
    set j := cliIoCapIdx 9 r
    have hj : j ≤ 9 := cliIoCapIdx_le 9 r
    have hseq := stepEvents_cliIoCapSeq_tight M hSmLo hSmHi hSmallAff hLargeAff hMeta st0 j
    dsimp only at hseq
    have hcum_m : cliIoTightCumBound j ≤ 573818 := by
      rw [← cliIoTightCumBound_nine]
      exact cliIoTightCumBound_mono hj
    have hcap_le : cliIoCap j ≤ 2097152 := cliIoCap_le_fileCap hj
    have hlive_m : cliIoStepLiveBound M j ≤ 2105347 := by
      unfold cliIoStepLiveBound
      split
      · omega
      · rename_i hnot
        have hlc := hLargeAff (cliIoCap j) (by omega)
        omega
    have hpeak_m : cliIoStepPeakBound j ≤ 3162118 := by
      have hp9 : cliIoStepPeakBound 9 = 3162118 := rfl
      rw [← hp9]
      exact cliIoStepPeakBound_mono hj
    exact ⟨by omega, by omega, by omega⟩

/-! ## 2. Direct `PhaseCreditSpec` Combinators for `Dir`, `Path`, `Decimal`, and `read_file` -/

theorem req_align_cliIoCapSeq : ∀ (j : Nat) (ev : AllocEvent),
    ev ∈ cliIoCapSeq j → eventStepReq ev ≤ cliIoCap j ∧ eventStepAlign ev ≤ 16
  | 0, ev, hev => by
    dsimp only [cliIoCapSeq] at hev
    rw [rustAllocEvents_cliIoCap, List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl _, Nat.le_refl 16⟩
  | j + 1, ev, hev => by
    dsimp only [cliIoCapSeq] at hev
    rcases List.mem_append.mp hev with h1 | h2
    · obtain ⟨hr, hal⟩ := req_align_cliIoCapSeq j ev h1
      exact ⟨Nat.le_trans hr (cliIoCap_mono (Nat.le_succ j)), hal⟩
    · rw [rustReallocEvents_cliIoCap, List.mem_singleton] at h2
      subst h2
      simp only [eventStepReq, eventStepAlign]
      exact ⟨Nat.le_refl _, by decide⟩

theorem req_align_cliIoReadCaps (K r : Nat) :
    ∀ ev ∈ cliIoCapEvents (cliIoReadCaps K r),
      eventStepReq ev ≤ cliIoCap K ∧ eventStepAlign ev ≤ 16 := by
  by_cases hr : r = 0
  · subst hr
    rw [cliIoCapEvents_readCaps_zero]
    intro ev hev
    nomatch hev
  · rw [cliIoCapEvents_readCaps_pos (by omega)]
    intro ev hev
    obtain ⟨hreq, hal⟩ := req_align_cliIoCapSeq (cliIoCapIdx K r) ev hev
    exact ⟨Nat.le_trans hreq (cliIoCap_mono (cliIoCapIdx_le K r)), hal⟩

/-- Unconditional `PhaseCreditSpec` for `cliIoCapSeq j`. -/
theorem phaseCreditSpec_cliIoCapSeq_uncond {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (j : Nat) :
    PhaseCreditSpec M (· = cliIoCapSeq j)
      (cliIoSmallCumBound j) (cliIoStepLiveBound M j) (cliIoStepPeakBound j) (cliIoCap j) where
  req_align := by
    rintro _ rfl
    exact req_align_cliIoCapSeq j
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_cliIoCapSeq_uncond M hM.hSmallAff hM.hLargeAff hM.hMeta st0 j

/-- Over-cap error cancellation: `cliIoCapSeq j ++ rustDeallocEvents (cliIoCap j) 1` leaves
`Δlive = 0` unconditionally across all `smallMaxReq M` regimes. -/
theorem phaseCreditSpec_cliIoCapSeq_dealloc_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (j : Nat) :
    PhaseCreditSpec M
      (ConcatEnv (· = cliIoCapSeq j) (· = rustDeallocEvents (cliIoCap j) 1))
      (cliIoSmallCumBound j) 0 (cliIoStepPeakBound j) (cliIoCap j) := by
  by_cases hsm : cliIoCap j ≤ HasFineReallocCredit.smallMaxReq M
  · have hw :
        PhaseCreditSpec M (· = cliIoCapSeq j)
          (cliIoSmallCumBound j) (0 + 0) (cliIoStepPeakBound j) (cliIoCap j) := by
      have h0 := phaseCreditSpec_cliIoCapSeq_uncond hM j
      unfold cliIoStepLiveBound at h0
      simpa [hsm] using h0
    exact hw.concat_dealloc_cancel (DeallocCreditSpec.free_small M (by decide) hsm)
  · have hgt : HasFineReallocCredit.smallMaxReq M < cliIoCap j := by omega
    have hw :
        PhaseCreditSpec M (· = cliIoCapSeq j)
          (cliIoSmallCumBound j)
          (0 + HasFineReallocCredit.largeCost M (cliIoCap j))
          (cliIoStepPeakBound j) (cliIoCap j) := by
      have h0 := phaseCreditSpec_cliIoCapSeq_uncond hM j
      unfold cliIoStepLiveBound at h0
      simpa [hsm] using h0
    exact hw.concat_dealloc_cancel (DeallocCreditSpec.free_large M (by decide) hgt)

/-- Unconditional `PhaseCreditSpec` for `cliIoCapEvents (cliIoReadCaps 9 r)` (`read_file`, `≤ 2 MiB`). -/
theorem phaseCreditSpec_cliIoReadFile_uncond {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (r : Nat) :
    PhaseCreditSpec M (· = cliIoCapEvents (cliIoReadCaps 9 r))
      8475806 2105347 3162118 2097152 where
  req_align := by
    rintro _ rfl
    exact req_align_cliIoReadCaps 9 r
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_cliIoReadFile_uncond M hM.hSmallAff hM.hLargeAff hM.hMeta r st0

/-- Existential-`r` `PhaseCreditSpec` for `∃ r, evs = cliIoCapEvents (cliIoReadCaps 9 r)`. -/
theorem phaseCreditSpec_cliIoReadFile_anyR_uncond {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (fun evs => ∃ r, evs = cliIoCapEvents (cliIoReadCaps 9 r))
      8475806 2105347 3162118 2097152 where
  req_align := by
    rintro _ ⟨r, rfl⟩
    exact req_align_cliIoReadCaps 9 r
  credit_le := by
    rintro st0 _ ⟨r, rfl⟩
    exact stepEvents_cliIoReadFile_uncond M hM.hSmallAff hM.hLargeAff hM.hMeta r st0

/-- Tight `PhaseCreditSpec` (`Δcum = 573,818`) for `cliIoCapEvents (cliIoReadCaps 9 r)` when
`131072 ≤ smallMaxReq M < 262144`. -/
theorem phaseCreditSpec_cliIoReadFile_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (r : Nat) :
    PhaseCreditSpec M (· = cliIoCapEvents (cliIoReadCaps 9 r))
      573818 2105347 3162118 2097152 where
  req_align := by
    rintro _ rfl
    exact req_align_cliIoReadCaps 9 r
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_cliIoReadFile_tight M hSmLo hSmHi hM.hSmallAff hM.hLargeAff hM.hMeta r st0

/-- Unconditional `PhaseCreditSpec` for `cliIoCapEvents (cliIoReadCaps 8 r)` (`read_stdin`, `≤ 1 MiB`). -/
theorem phaseCreditSpec_cliIoReadStdin_uncond {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (r : Nat) :
    PhaseCreditSpec M (· = cliIoCapEvents (cliIoReadCaps 8 r))
      4271963 1056771 1589254 1048576 where
  req_align := by
    rintro _ rfl
    exact req_align_cliIoReadCaps 8 r
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_cliIoReadStdin_uncond M hM.hSmallAff hM.hLargeAff hM.hMeta r st0

private theorem step_small_or_free_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ev : AllocEvent} {maxReq : Nat} (st : M.σ)
    (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    let st' := M.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (2 * maxReq + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free al sz =>
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st
    omega
  | alloc req =>
    simp only [eventStepReq] at hreq
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
    have hsa := hM.smallAlloc_le hle
    omega
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
    have hsa := hM.smallAlloc_le hle
    omega
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
      have hsr := hM.smallRealloc_le hnew_le
      omega
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal hold_gt hnew_le
      have hsr := hM.smallRealloc_le hnew_le
      omega

theorem stepEvents_bounded_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ {evs : List AllocEvent},
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      ∀ (st0 : M.σ),
        let st' := M.stepEvents evs st0
        HasFineReallocCredit.cumSmall st' ≤
          HasFineReallocCredit.cumSmall st0 + evs.length * (2 * maxReq + 9539) ∧
        HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 ∧
        HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st0
  | [], _, st0 => by
    simp [AllocCostModel.stepEvents_nil]
  | ev :: evs, h, st0 => by
    obtain ⟨hreq, hal⟩ := h ev List.mem_cons_self
    have htail : ∀ e ∈ evs, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => h e (List.mem_cons_of_mem _ he)
    obtain ⟨hc₁, hl₁, hp₁⟩ := step_small_or_free_aff hM st0 hsm hreq hal
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_bounded_small hM hsm htail (M.step ev st0)
    dsimp only at hc₁ hl₁ hp₁ hc₂ hl₂ hp₂ ⊢
    rw [AllocCostModel.stepEvents_cons, List.length_cons, Nat.add_one_mul]
    set C := 2 * maxReq + 9539
    exact ⟨by omega, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

theorem stepEvents_bounded_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} :
    ∀ {evs : List AllocEvent},
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      ∀ (st0 : M.σ),
        let st' := M.stepEvents evs st0
        HasFineReallocCredit.cumSmall st' ≤
          HasFineReallocCredit.cumSmall st0 + evs.length * (2 * maxReq + 9539) ∧
        HasFineReallocCredit.liveLarge st' ≤
          HasFineReallocCredit.liveLarge st0 + evs.length * (maxReq + 8195) ∧
        HasFineReallocCredit.peakLarge st' ≤
          max (HasFineReallocCredit.peakLarge st0)
            (HasFineReallocCredit.liveLarge st0 + evs.length * (maxReq + 8195))
  | [], _, st0 => by
    simp [AllocCostModel.stepEvents_nil]
  | ev :: evs, h, st0 => by
    obtain ⟨hreq, hal⟩ := h ev List.mem_cons_self
    have htail : ∀ e ∈ evs, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => h e (List.mem_cons_of_mem _ he)
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st0 hreq hal
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_bounded_any hM htail (M.step ev st0)
    dsimp only at hc₁ hl₁ hp₁ hc₂ hl₂ hp₂ ⊢
    set C := 2 * maxReq + 9539
    set L := maxReq + 8195
    rw [AllocCostModel.stepEvents_cons, List.length_cons]
    have hmul1 : (evs.length + 1) * C = evs.length * C + C := Nat.add_one_mul evs.length C
    have hmul2 : (evs.length + 1) * L = evs.length * L + L := Nat.add_one_mul evs.length L
    rw [hmul1, hmul2]
    set KC := evs.length * C
    set KL := evs.length * L
    exact ⟨by omega, by omega, by omega⟩

/-- Small-regime `PhaseCreditSpec` (`Δlive = 0, Δpeak = 0`) for any bounded-count, bounded-request
envelope (`maxReq ≤ smallMaxReq M`), such as `Decimal`, `Path`, or `AddressText`. -/
theorem phaseCreditSpec_of_bounded_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {Env : List AllocEvent → Prop} {maxCount maxReq : Nat}
    (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hb : ∀ evs, Env evs →
      evs.length ≤ maxCount ∧ ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) :
    PhaseCreditSpec M Env (maxCount * (2 * maxReq + 9539)) 0 0 maxReq where
  req_align evs hE := (hb evs hE).2
  credit_le st0 {evs} hE := by
    obtain ⟨hlen, hra⟩ := hb evs hE
    obtain ⟨hc, hl, hp⟩ := stepEvents_bounded_small hM hsm hra st0
    have hmul : evs.length * (2 * maxReq + 9539) ≤ maxCount * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ hlen
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hmul _),
      by simpa using hl,
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

/-- Regime-uniform `PhaseCreditSpec` (zero threshold assumptions on `smallMaxReq M`) for any
bounded-count, bounded-request envelope (`Decimal`, `Path`, `AddressText`, `BoundedRustEvs`). -/
theorem phaseCreditSpec_of_bounded_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {Env : List AllocEvent → Prop} {maxCount maxReq : Nat}
    (hb : ∀ evs, Env evs →
      evs.length ≤ maxCount ∧ ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) :
    PhaseCreditSpec M Env
      (maxCount * (2 * maxReq + 9539))
      (maxCount * (maxReq + 8195))
      (maxCount * (maxReq + 8195))
      maxReq where
  req_align evs hE := (hb evs hE).2
  credit_le st0 {evs} hE := by
    obtain ⟨hlen, hra⟩ := hb evs hE
    obtain ⟨hc, hl, hp⟩ := stepEvents_bounded_any hM hra st0
    have hmul_c : evs.length * (2 * maxReq + 9539) ≤ maxCount * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ hlen
    have hmul_l : evs.length * (maxReq + 8195) ≤ maxCount * (maxReq + 8195) :=
      Nat.mul_le_mul_right _ hlen
    refine ⟨Nat.le_trans hc (Nat.add_le_add_left hmul_c _),
      Nat.le_trans hl (Nat.add_le_add_left hmul_l _), ?_⟩
    exact Nat.le_trans hp (max_le_max (Nat.le_refl _) (Nat.add_le_add_left hmul_l _))

/-- Mirror of `SpecBudget.allocBytes1Events` (`rfl`-equal). -/
def allocBytes1Evs (bs : List (BitVec 8)) : List AllocEvent :=
  if bs.length = 0 then [] else rustAllocEvents bs.length 1

theorem req_align_allocBytes1Evs (bs : List (BitVec 8)) {maxBytes : Nat}
    (hmax : bs.length ≤ maxBytes) :
    ∀ ev ∈ allocBytes1Evs bs, eventStepReq ev ≤ maxBytes ∧ eventStepAlign ev ≤ 16 := by
  unfold allocBytes1Evs
  split
  · intro ev hev; nomatch hev
  · intro ev hev
    unfold rustAllocEvents at hev
    split at hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
      simp only [eventStepReq, eventStepAlign] <;> omega

/-- Small-regime `PhaseCreditSpec` for `allocBytes1Evs bs` (`bs.length ≤ maxBytes ≤ smallMaxReq M`). -/
theorem phaseCreditSpec_allocBytes1_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8)) {maxBytes : Nat}
    (hmax : bs.length ≤ maxBytes) (hsm : maxBytes ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = allocBytes1Evs bs) (2 * maxBytes + 9539) 0 0 maxBytes where
  req_align := by
    rintro _ rfl
    exact req_align_allocBytes1Evs bs hmax
  credit_le := by
    rintro st0 _ rfl
    unfold allocBytes1Evs
    have hbs_sm : bs.length ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hmax hsm
    have h := stepEvents_allocBytes1_small_aff M bs st0 hbs_sm (fun _ hr => hM.smallAlloc_le hr)
    dsimp only at h
    exact ⟨by omega, by omega, Nat.le_trans h.2.2 (Nat.le_max_left _ _)⟩

/-- Regime-uniform `PhaseCreditSpec` for `allocBytes1Evs bs` (`bs.length ≤ maxBytes`, any `smallMaxReq M`). -/
theorem phaseCreditSpec_allocBytes1_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8)) {maxBytes : Nat}
    (hmax : bs.length ≤ maxBytes) :
    PhaseCreditSpec M (· = allocBytes1Evs bs)
      (2 * maxBytes + 9539) (maxBytes + 8195) (maxBytes + 8195) maxBytes where
  req_align := by
    rintro _ rfl
    exact req_align_allocBytes1Evs bs hmax
  credit_le := by
    rintro st0 _ rfl
    unfold allocBytes1Evs
    exact stepEvents_allocBytes1_any_aff M bs st0 hmax
      (fun _ hr => hM.smallAlloc_le hr) hM.hLargeAff hM.hMeta

theorem req_align_growOneDir (cap : BitVec 64) (hcap : cap.toNat ≤ 64) :
    ∀ ev ∈ rawVecGrowEvents 48 4 8 cap, eventStepReq ev ≤ 6144 ∧ eventStepAlign ev ≤ 16 := by
  have hnew_le : rawVecNewCap 4 cap.toNat * 48 ≤ 6144 := growOneDir_newBytes_le hcap
  have hnew_ge : 192 ≤ rawVecNewCap 4 cap.toNat * 48 := by
    unfold rawVecNewCap
    omega
  unfold rawVecGrowEvents
  split
  · intro ev hev
    unfold rustAllocEvents at hev
    split at hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
      simp only [eventStepReq, eventStepAlign] <;> decide
  · intro ev hev
    unfold rustReallocEvents at hev
    have h8_le : 8 ≤ rawVecNewCap 4 cap.toNat * 48 := by omega
    have h8_16 : (8 : Nat) ≤ 16 := by decide
    simp only [h8_16, h8_le, and_self, ↓reduceIte, List.mem_singleton] at hev
    subst hev
    simp only [eventStepReq, eventStepAlign]
    exact ⟨hnew_le, by decide⟩

/-- Small-regime `PhaseCreditSpec` for `GrowOneDir` (`rawVecGrowEvents 48 4 8 cap`, `cap ≤ 64`,
`6144 ≤ smallMaxReq M` gives `Δcum = 21827`, `Δlive = 0`, `Δpeak = 0`). -/
theorem phaseCreditSpec_growOneDir_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap : BitVec 64)
    (hcap : cap.toNat ≤ 64) (hsm : 6144 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rawVecGrowEvents 48 4 8 cap) 21827 0 0 6144 where
  req_align := by
    rintro _ rfl
    exact req_align_growOneDir cap hcap
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ := stepEvents_growOneDir_small M cap st0 hcap hsm hM.hSmallAff
    exact ⟨hc, by omega, Nat.le_trans hp (Nat.le_max_left _ _)⟩

/-- Regime-uniform `PhaseCreditSpec` for `GrowOneDir` (`rawVecGrowEvents 48 4 8 cap`, `cap ≤ 64`,
giving `Δcum = 21827`, `Δlive = 14339`, `Δpeak = 14339`). -/
theorem phaseCreditSpec_growOneDir_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap : BitVec 64) (hcap : cap.toNat ≤ 64) :
    PhaseCreditSpec M (· = rawVecGrowEvents 48 4 8 cap) 21827 14339 14339 6144 := by
  have hb : ∀ evs, evs = rawVecGrowEvents 48 4 8 cap →
      evs.length ≤ 1 ∧ ∀ ev ∈ evs, eventStepReq ev ≤ 6144 ∧ eventStepAlign ev ≤ 16 := by
    rintro _ rfl
    refine ⟨?_, req_align_growOneDir cap hcap⟩
    have hnew_ge : 192 ≤ rawVecNewCap 4 cap.toNat * 48 := by unfold rawVecNewCap; omega
    unfold rawVecGrowEvents
    split
    · unfold rustAllocEvents
      split <;> simp
    · unfold rustReallocEvents
      have h8_le : 8 ≤ rawVecNewCap 4 cap.toNat * 48 := by omega
      have h8_16 : (8 : Nat) ≤ 16 := by decide
      simp only [h8_16, h8_le, and_self, ↓reduceIte, List.length_singleton]
      exact Nat.le_refl 1
  have h0 := phaseCreditSpec_of_bounded_any hM (maxCount := 1) (maxReq := 6144) hb
  simpa using h0

/-- Parametric `maxEntries` `eventStepReq` / `eventStepAlign` bound for `GrowOneDir`
(`rawVecGrowEvents 48 4 8 cap`, `cap.toNat ≤ maxEntries`). -/
theorem req_align_growOneDir_of_le (cap : BitVec 64) {maxEntries : Nat}
    (hcap : cap.toNat ≤ maxEntries) :
    ∀ ev ∈ rawVecGrowEvents 48 4 8 cap,
      eventStepReq ev ≤ 48 * max 4 (2 * maxEntries) ∧ eventStepAlign ev ≤ 16 := by
  have hnew_le : rawVecNewCap 4 cap.toNat * 48 ≤ 48 * max 4 (2 * maxEntries) := by
    unfold rawVecNewCap; omega
  have hnew_ge : 192 ≤ rawVecNewCap 4 cap.toNat * 48 := by
    unfold rawVecNewCap; omega
  have h48_le : 192 ≤ 48 * max 4 (2 * maxEntries) := by omega
  intro ev hev
  unfold rawVecGrowEvents at hev
  split at hev
  · have hev' : ev = .alloc 192 := by
      unfold rustAllocEvents at hev
      simpa using hev
    subst hev'
    simp only [eventStepReq, eventStepAlign]
    exact ⟨h48_le, by decide⟩
  · unfold rustReallocEvents at hev
    have h8_le : 8 ≤ rawVecNewCap 4 cap.toNat * 48 := by omega
    have h8_16 : (8 : Nat) ≤ 16 := by decide
    simp only [h8_16, h8_le, and_self, ↓reduceIte, List.mem_singleton] at hev
    subst hev
    simp only [eventStepReq, eventStepAlign]
    exact ⟨hnew_le, by decide⟩

/-- Parametric `maxEntries` `PhaseCreditSpec` for `GrowOneDir` (`rawVecGrowEvents 48 4 8 cap`,
`cap.toNat ≤ maxEntries`). -/
theorem phaseCreditSpec_growOneDir_of_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap : BitVec 64) {maxEntries : Nat} (hcap : cap.toNat ≤ maxEntries) :
    PhaseCreditSpec M (· = rawVecGrowEvents 48 4 8 cap)
      (2 * (48 * max 4 (2 * maxEntries)) + 9539)
      (48 * max 4 (2 * maxEntries) + 8195)
      (48 * max 4 (2 * maxEntries) + 8195)
      (48 * max 4 (2 * maxEntries)) := by
  have hb : ∀ evs, evs = rawVecGrowEvents 48 4 8 cap →
      evs.length ≤ 1 ∧ ∀ ev ∈ evs,
        eventStepReq ev ≤ 48 * max 4 (2 * maxEntries) ∧ eventStepAlign ev ≤ 16 := by
    rintro _ rfl
    refine ⟨?_, req_align_growOneDir_of_le cap hcap⟩
    have hnew_ge : 192 ≤ rawVecNewCap 4 cap.toNat * 48 := by unfold rawVecNewCap; omega
    unfold rawVecGrowEvents
    split
    · unfold rustAllocEvents
      split <;> simp
    · unfold rustReallocEvents
      have h8_le : 8 ≤ rawVecNewCap 4 cap.toNat * 48 := by omega
      have h8_16 : (8 : Nat) ≤ 16 := by decide
      simp only [h8_16, h8_le, and_self, ↓reduceIte, List.length_singleton]
      exact Nat.le_refl 1
  have h0 := phaseCreditSpec_of_bounded_any hM
    (maxCount := 1) (maxReq := 48 * max 4 (2 * maxEntries)) hb
  simpa using h0

/-- Regime-aware `liveLarge` increment of a buffer of capacity `req` (`0` if small, `largeCost M req` if large). -/
def optLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then 0 else HasFineReallocCredit.largeCost M req

theorem optLargeLive_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req maxCap : Nat} (hle : req ≤ maxCap) :
    optLargeLive M req ≤ maxCap + 8195 := by
  unfold optLargeLive
  split_ifs with hsm
  · exact Nat.zero_le _
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
    have hlc := hM.largeCost_le hgt
    omega

/-- Regime-uniform `rustAllocEvents` spec preserving exact `optLargeLive M req` for subsequent `realloc` telescoping. -/
theorem phaseCreditSpec_rustAlloc_optLive {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (2 * req + 9539) (optLargeLive M req) (req + 8195) req := by
  unfold optLargeLive
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · simp only [hle, ↓reduceIte]
    exact (PhaseCreditSpec.rustAlloc_small_any hM hal hle).mono
      (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.zero_le _) (Nat.le_refl req)
  · simp only [hle, ↓reduceIte]
    have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
    have hm := hM.meta_le
    have hl := hM.largeCost_le hgt
    exact (PhaseCreditSpec.rustAlloc_large M hal hgt).mono
      (by omega) (Nat.le_refl _) hl (Nat.le_refl req)

/-- Regime-uniform `ConcatEnv` `rustReallocEvents` telescoping step (`0 < old ≤ new`, `al ≤ new`, `al ≤ 16`). -/
theorem phaseCreditSpec_concat_rustRealloc_optLive {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E₁ : List AllocEvent → Prop} {c₁ p₁ r₁ old new al : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ (optLargeLive M old) p₁ r₁)
    (hal : al ≤ 16) (hal_new : al ≤ new) (hold_pos : 0 < old) (hle_on : old ≤ new) :
    PhaseCreditSpec M (ConcatEnv E₁ (· = rustReallocEvents old new al))
      (c₁ + (2 * new + 9539))
      (optLargeLive M new)
      (max p₁ (old + new + 2 * 8195))
      (max r₁ new) := by
  unfold optLargeLive at h₁ ⊢
  by_cases hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M
  · have hold_le : old ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hle_on hnew_le
    simp only [hold_le, ↓reduceIte] at h₁
    simp only [hnew_le, ↓reduceIte]
    have h2 := PhaseCreditSpec.rustRealloc_small_small M hal hal_new hold_pos hold_le
      (by omega) hnew_le
    have hsr := hM.smallRealloc_le hnew_le
    exact (h₁.concat h2).mono (by omega) (by omega) (by omega) (Nat.le_refl _)
  · have hnew_gt : HasFineReallocCredit.smallMaxReq M < new := by omega
    simp only [hnew_le, ↓reduceIte]
    have hm := hM.meta_le
    have hln := hM.largeCost_le hnew_gt
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hold_le, ↓reduceIte] at h₁
      have h2 := PhaseCreditSpec.rustRealloc_small_large M hal hal_new hold_pos hold_le hnew_gt
      exact (h₁.concat h2).mono (by omega) (by omega) (by omega) (Nat.le_refl _)
    · simp only [hold_le, ↓reduceIte] at h₁
      have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      have hlo := hM.largeCost_le hold_gt
      have h1' : PhaseCreditSpec M E₁ c₁ (0 + HasFineReallocCredit.largeCost M old) p₁ r₁ := by
        simpa using h₁
      exact (h1'.concat_rustRealloc_large_large hal hal_new hold_gt hnew_gt).mono
        (by omega) (by omega) (by omega) (Nat.le_refl _)

end LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
