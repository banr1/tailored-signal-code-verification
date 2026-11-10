/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Common
public import VerifiedLibraries.Mallocng.Proofs.AccountingHelpers
public import VerifiedLibraries.Mallocng.Proofs.Cost.RootLen
public import LibsignalBinary.Heap.Fine.Tables

/-!
# Per-Size-Class `mallocng` Fine State Invariant

Defines `FineEvent`, `FineBudget`, per-size-class group geometry (`GroupFineGeom` and the slab
cutoff `Guaranteed63Threshold = 135,168`), ghost alignment agreement (`FineAlignWf`), the inductive
invariant `MallocngFineInv`, and the sealed separation-logic predicates `FineCoreImpl` and
`FineHeapImpl`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Thresholds, `FineBudget`, and Monotonicity Laws -/

/-- Threshold (`33 * 4096 = 135,168` B) above which no slab group (`g.sc < 48`, whose maximum root
    mapping is `maxRootBytes 47 = 135,168` B with `stride ≤ 135,152` B) can ever hold a `.liveUser`
    slot — even after an in-place `realloc` Stage 2 growth inside a single-slot `sc = 47` group. -/
def Guaranteed63Threshold : Nat := 135168

/-- Fine-model mirror of `AllocEvent`. -/
inductive FineEvent where
  | alloc (req : Nat)
  | aligned (align req : Nat)
  | free (align req : Nat)
  | realloc (align old new : Nat)
  deriving DecidableEq, Repr

/-- Requested byte count of `ev` (matches `AllocEvent.reqBytes`). -/
def FineEvent.reqBytes : FineEvent → Nat
  | .alloc req => req
  | .aligned align req => mallocngAlignedEffSize align req
  | .free _ _ => 0
  | .realloc _ _ new => new

/-- Declared byte cost of an individual `sc = 63` (`mmap`) allocation with payload `req` and
    effective alignment `effAlign ≥ 16`: bounds `g.maplen * 4096 ≤ req + (effAlign - 16) + 8195`. -/
def declCost63 (req effAlign : Nat) : Nat :=
  req + (effAlign - 16) + 8195

/-- Abstract state of the per-size-class `mallocng` cost model. -/
structure FineBudget where
  cumSmallBytes   : Nat
  cumSmallGroupsS : Nat
  live63Bytes     : Nat
  peak63Bytes     : Nat
  live63Count     : Nat
  peak63Count     : Nat
  liveUserBytes   : Nat
  deriving DecidableEq, Repr

/-- Normalized `sc = 63` byte high-water mark (`= b.peak63Bytes` whenever `b.live63Bytes ≤ b.peak63Bytes`). -/
def finePeak63Bytes (b : FineBudget) : Nat :=
  max b.peak63Bytes b.live63Bytes

/-- Normalized `sc = 63` count high-water mark (`= b.peak63Count` whenever `b.live63Count ≤ b.peak63Count`). -/
def finePeak63Count (b : FineBudget) : Nat :=
  max b.peak63Count b.live63Count

def FineBudget.init : FineBudget :=
  ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- Abstract transition for `aligned_alloc(align, req)` / `posix_memalign(..., align, req)`. -/
def FineBudget.stepAligned (align req : Nat) (b : FineBudget) : FineBudget :=
  let effAlign := max align 16
  let eff := req + (effAlign - 16)
  let pB0 := finePeak63Bytes b
  let pC0 := finePeak63Count b
  if Guaranteed63Threshold ≤ req then
    let c := declCost63 req effAlign
    let lB := b.live63Bytes + c
    let lC := b.live63Count + 1
    { b with
      live63Bytes   := lB
      peak63Bytes   := max pB0 lB
      live63Count   := lC
      peak63Count   := max pC0 lC
      liveUserBytes := b.liveUserBytes + req }
  else if eff ≤ MmapThresholdReq then
    let sc0 := sizeToClassUnits ((eff + 3) / 16)
    { b with
      cumSmallBytes   := b.cumSmallBytes + coarseSlotWt sc0
      cumSmallGroupsS := b.cumSmallGroupsS + coarseGrpWtS sc0
      peak63Bytes     := pB0
      peak63Count     := pC0
      liveUserBytes   := b.liveUserBytes + req }
  else
    { b with
      cumSmallBytes   := b.cumSmallBytes + declCost63 req effAlign
      cumSmallGroupsS := b.cumSmallGroupsS + FineScale
      peak63Bytes     := pB0
      peak63Count     := pC0
      liveUserBytes   := b.liveUserBytes + req }

/-- Abstract transition for `malloc(req)` / `calloc` (`align = 16`). -/
def FineBudget.stepAlloc (req : Nat) (b : FineBudget) : FineBudget :=
  FineBudget.stepAligned 16 req b

/-- Abstract transition for `free(p)` on a block of `(req, align)`. -/
def FineBudget.stepFree (align req : Nat) (b : FineBudget) : FineBudget :=
  let pB0 := finePeak63Bytes b
  let pC0 := finePeak63Count b
  if Guaranteed63Threshold ≤ req then
    let c := declCost63 req (max align 16)
    { b with
      live63Bytes   := b.live63Bytes - c
      peak63Bytes   := pB0
      live63Count   := b.live63Count - 1
      peak63Count   := pC0
      liveUserBytes := b.liveUserBytes - req }
  else
    { b with
      peak63Bytes   := pB0
      peak63Count   := pC0
      liveUserBytes := b.liveUserBytes - req }

/-- Allocation half of `realloc(p, newSz)` before crediting `stepFree align oldSz`. -/
def FineBudget.stepReallocAdd (align newSz : Nat) (b : FineBudget) : FineBudget :=
  let effAlign := max align 16
  let pB0 := finePeak63Bytes b
  let pC0 := finePeak63Count b
  if Guaranteed63Threshold ≤ newSz then
    FineBudget.stepAligned align newSz b
  else
    let c63 := declCost63 newSz effAlign
    let wSmall :=
      if newSz ≤ MmapThresholdReq then coarseSlotWt (sizeToClassUnits ((newSz + 3) / 16)) else 0
    let gSmall :=
      if newSz ≤ MmapThresholdReq then coarseGrpWtS (sizeToClassUnits ((newSz + 3) / 16)) else 0
    { b with
      cumSmallBytes   := b.cumSmallBytes + max wSmall c63
      cumSmallGroupsS := b.cumSmallGroupsS + max gSmall FineScale
      peak63Bytes     := pB0
      peak63Count     := pC0
      liveUserBytes   := b.liveUserBytes + newSz }

/-- Abstract transition for `realloc` from `(oldSz, align)` to `newSz`. -/
def FineBudget.stepRealloc (align oldSz newSz : Nat) (b : FineBudget) : FineBudget :=
  FineBudget.stepFree align oldSz (FineBudget.stepReallocAdd align newSz b)

def FineBudget.step : FineEvent → FineBudget → FineBudget
  | .alloc req => FineBudget.stepAlloc req
  | .aligned align req => FineBudget.stepAligned align req
  | .free align req => FineBudget.stepFree align req
  | .realloc align oldSz newSz => FineBudget.stepRealloc align oldSz newSz

/-- Upper bound on `st.groups.length` from `b : FineBudget`. -/
def fineMaxGroups (b : FineBudget) : Nat :=
  gBaseConst + (b.cumSmallGroupsS + FineScale - 1) / FineScale + finePeak63Count b

/-- Upper bound on `st.metaAreas.length` from `b : FineBudget`. -/
def fineMaxMetaAreas (b : FineBudget) : Nat :=
  1 + (7 + fineMaxGroups b) / 101

/-- Upper bound on `(dynamicRootRegions st).length` (`maxDynIvs`) from `b : FineBudget`. -/
def fineMaxDynIvs (b : FineBudget) : Nat :=
  3 * fineMaxMetaAreas b + 2 + fineMaxGroups b

/-- Upper bound on `((dynamicRootRegions st).map Prod.snd).sum` (`footprint`) from `b : FineBudget`. -/
def fineFootprint (b : FineBudget) : Nat :=
  BaseRootFine + b.cumSmallBytes + finePeak63Bytes b + 4096 * (3 * fineMaxMetaAreas b + 2)

/-- Per-call OOM-freedom step reserve (`stepReserve`) from `b : FineBudget`. -/
def fineStepReserve (ev : FineEvent) (b : FineBudget) : Nat :=
  match ev with
  | .alloc req => FineStepBound req 16 (fineMaxMetaAreas b)
  | .aligned align req => FineStepBound req align (fineMaxMetaAreas b)
  | .free _ _ => FineStepBound 0 16 (fineMaxMetaAreas b)
  | .realloc align _ newSz => FineStepBound newSz align (fineMaxMetaAreas b)

def fineLiveBytes (b : FineBudget) : Nat :=
  b.liveUserBytes

private theorem stepFree_peaks_eq (align req : Nat) (b : FineBudget) :
    (FineBudget.stepFree align req b).cumSmallBytes = b.cumSmallBytes ∧
    (FineBudget.stepFree align req b).cumSmallGroupsS = b.cumSmallGroupsS ∧
    finePeak63Bytes (FineBudget.stepFree align req b) = finePeak63Bytes b ∧
    finePeak63Count (FineBudget.stepFree align req b) = finePeak63Count b := by
  unfold FineBudget.stepFree finePeak63Bytes finePeak63Count
  dsimp only
  split <;> simp <;> omega

private theorem stepAligned_bounds (align req : Nat) (b : FineBudget) :
    let b' := FineBudget.stepAligned align req b
    let eff := mallocngAlignedEffSize align req
    b.cumSmallBytes ≤ b'.cumSmallBytes ∧
    b.cumSmallGroupsS ≤ b'.cumSmallGroupsS ∧
    finePeak63Bytes b ≤ finePeak63Bytes b' ∧
    finePeak63Count b ≤ finePeak63Count b' ∧
    b'.cumSmallBytes + finePeak63Bytes b' ≤
      b.cumSmallBytes + finePeak63Bytes b + (eff + 131072) ∧
    b'.cumSmallGroupsS ≤ b.cumSmallGroupsS + 3 * FineScale ∧
    finePeak63Count b' ≤ finePeak63Count b + 1 := by
  have hEff : req + (max align 16 - 16) = mallocngAlignedEffSize align req := by
    unfold mallocngAlignedEffSize
    by_cases h : align ≤ 16 <;> simp [h] <;> omega
  have hCap := coarseWt_le_cap (sizeToClassUnits ((req + (max align 16 - 16) + 3) / 16))
  unfold FineBudget.stepAligned finePeak63Bytes finePeak63Count declCost63 FineScale at *
  dsimp only
  split
  · simp only [← hEff]; omega
  · split
    · simp only [← hEff]; omega
    · simp only [← hEff]; omega

private theorem stepReallocAdd_bounds (align newSz : Nat) (b : FineBudget) :
    let b' := FineBudget.stepReallocAdd align newSz b
    let eff := mallocngAlignedEffSize align newSz
    b.cumSmallBytes ≤ b'.cumSmallBytes ∧
    b.cumSmallGroupsS ≤ b'.cumSmallGroupsS ∧
    finePeak63Bytes b ≤ finePeak63Bytes b' ∧
    finePeak63Count b ≤ finePeak63Count b' ∧
    b'.cumSmallBytes + finePeak63Bytes b' ≤
      b.cumSmallBytes + finePeak63Bytes b + (eff + 131072) ∧
    b'.cumSmallGroupsS ≤ b.cumSmallGroupsS + 3 * FineScale ∧
    finePeak63Count b' ≤ finePeak63Count b + 1 := by
  unfold FineBudget.stepReallocAdd
  dsimp only
  by_cases hBig : Guaranteed63Threshold ≤ newSz
  · simp only [hBig, ↓reduceIte]
    exact stepAligned_bounds align newSz b
  · simp only [hBig, ↓reduceIte]
    have hEff : newSz + (max align 16 - 16) = mallocngAlignedEffSize align newSz := by
      unfold mallocngAlignedEffSize
      by_cases h : align ≤ 16 <;> simp [h] <;> omega
    have hCap := coarseWt_le_cap (sizeToClassUnits ((newSz + 3) / 16))
    unfold finePeak63Bytes finePeak63Count declCost63 FineScale at *
    by_cases hSm : newSz ≤ MmapThresholdReq
    · simp only [hSm, ↓reduceIte, ← hEff]; omega
    · simp only [hSm, ↓reduceIte, ← hEff]; omega

private theorem watermarks_mono (ev : FineEvent) (b : FineBudget) :
    b.cumSmallBytes ≤ (FineBudget.step ev b).cumSmallBytes ∧
    b.cumSmallGroupsS ≤ (FineBudget.step ev b).cumSmallGroupsS ∧
    finePeak63Bytes b ≤ finePeak63Bytes (FineBudget.step ev b) ∧
    finePeak63Count b ≤ finePeak63Count (FineBudget.step ev b) := by
  cases ev with
  | alloc req =>
    have h := stepAligned_bounds 16 req b
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | aligned align req =>
    have h := stepAligned_bounds align req b
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | free align req =>
    have h := stepFree_peaks_eq align req b
    simp only [FineBudget.step]
    omega
  | realloc align oldSz newSz =>
    have hAdd := stepReallocAdd_bounds align newSz b
    have hFr := stepFree_peaks_eq align oldSz (FineBudget.stepReallocAdd align newSz b)
    simp only [FineBudget.step, FineBudget.stepRealloc]
    omega

theorem fineMaxGroups_mono (ev : FineEvent) (b : FineBudget) :
    fineMaxGroups b ≤ fineMaxGroups (FineBudget.step ev b) := by
  have ⟨_, hGS, _, hPC⟩ := watermarks_mono ev b
  unfold fineMaxGroups
  have hDiv :
      (b.cumSmallGroupsS + FineScale - 1) / FineScale ≤
        ((FineBudget.step ev b).cumSmallGroupsS + FineScale - 1) / FineScale :=
    Nat.div_le_div_right (by omega)
  omega

theorem fineMaxMetaAreas_mono (ev : FineEvent) (b : FineBudget) :
    fineMaxMetaAreas b ≤ fineMaxMetaAreas (FineBudget.step ev b) := by
  have hG := fineMaxGroups_mono ev b
  unfold fineMaxMetaAreas
  have hDiv := Nat.div_le_div_right (c := 101) (a := 7 + fineMaxGroups b)
    (b := 7 + fineMaxGroups (FineBudget.step ev b)) (by omega)
  omega

theorem fineMaxDynIvs_mono (ev : FineEvent) (b : FineBudget) :
    fineMaxDynIvs b ≤ fineMaxDynIvs (FineBudget.step ev b) := by
  have hG := fineMaxGroups_mono ev b
  have hM := fineMaxMetaAreas_mono ev b
  unfold fineMaxDynIvs
  omega

theorem fineFootprint_mono (ev : FineEvent) (b : FineBudget) :
    fineFootprint b ≤ fineFootprint (FineBudget.step ev b) := by
  have ⟨hSB, _, hPB, _⟩ := watermarks_mono ev b
  have hM := fineMaxMetaAreas_mono ev b
  unfold fineFootprint
  omega

theorem fineStepReserve_mono (ev₀ ev : FineEvent) (b : FineBudget) :
    fineStepReserve ev₀ b ≤ fineStepReserve ev₀ (FineBudget.step ev b) := by
  have hM := fineMaxMetaAreas_mono ev b
  cases ev₀ <;> exact FineStepBound_mono_meta hM

theorem req_le_fineStepReserve (ev : FineEvent) (b : FineBudget) :
    ev.reqBytes ≤ fineStepReserve ev b := by
  cases ev with
  | alloc req =>
    exact req_le_FineStepBound req 16 (fineMaxMetaAreas b)
  | aligned align req =>
    unfold FineEvent.reqBytes fineStepReserve FineStepBound mallocngAlignedEffSize
    have hPageGe := pageAlignUp_le (req + (max align 16 - 16) + 8192)
    by_cases h : align ≤ 16 <;> simp [h] at hPageGe ⊢ <;> omega
  | free _ _ =>
    exact Nat.zero_le _
  | realloc align _ newSz =>
    exact req_le_FineStepBound newSz align (fineMaxMetaAreas b)

theorem fineLiveBytes_free_le (al n : Nat) (b : FineBudget) :
    fineLiveBytes (FineBudget.step (.free al n) b) ≤ fineLiveBytes b := by
  simp only [fineLiveBytes, FineBudget.step, FineBudget.stepFree]
  split <;> simp <;> omega

private theorem fineMaxMetaAreas_step_add_le {b b' : FineBudget}
    (hGS : b'.cumSmallGroupsS ≤ b.cumSmallGroupsS + 3 * FineScale)
    (hPC : finePeak63Count b' ≤ finePeak63Count b + 1) :
    fineMaxMetaAreas b' ≤ fineMaxMetaAreas b + 1 := by
  have hS : 0 < FineScale := by decide
  have hDivG :
      (b'.cumSmallGroupsS + FineScale - 1) / FineScale ≤
        (b.cumSmallGroupsS + FineScale - 1) / FineScale + 3 := by
    have hLe : b'.cumSmallGroupsS + FineScale - 1 ≤
        (b.cumSmallGroupsS + FineScale - 1) + 3 * FineScale := by
      unfold FineScale at hGS ⊢; omega
    have hD := Nat.div_le_div_right (c := FineScale) hLe
    rw [Nat.add_mul_div_right _ _ hS] at hD
    exact hD
  have hMG : fineMaxGroups b' ≤ fineMaxGroups b + 4 := by
    unfold fineMaxGroups; omega
  unfold fineMaxMetaAreas
  have hDM : (7 + fineMaxGroups b') / 101 ≤ (7 + fineMaxGroups b + 101) / 101 :=
    Nat.div_le_div_right (by omega)
  rw [Nat.add_div_right _ (by decide : 0 < 101)] at hDM
  omega

private theorem fineFootprint_step_le_arith
    (base sb sb' p63 p63' m m' req align eff pg : Nat)
    (hM : m' ≤ m + 1)
    (hEff : eff = req + (max align 16 - 16))
    (hPageGe : req + (max align 16 - 16) + 8192 ≤ pg)
    (hSum : sb' + p63' ≤ sb + p63 + (eff + 131072)) :
    base + sb' + p63' + 4096 * (3 * m' + 2) ≤
      (base + sb + p63 + 4096 * (3 * m + 2)) +
        (pg + 20 * 1024 * 1024 + 131072 * m) := by
  have hPageEff : eff + 8192 ≤ pg := hEff ▸ hPageGe
  have hC : 131072 + 12288 ≤ 8192 + 20 * 1024 * 1024 := by decide
  have hM3 : 3 * m' + 2 ≤ (3 * m + 2) + 3 := by omega
  have hM4096 : 4096 * (3 * m' + 2) ≤ 4096 * (3 * m + 2) + 12288 := by
    calc 4096 * (3 * m' + 2)
      _ ≤ 4096 * ((3 * m + 2) + 3) := Nat.mul_le_mul_left 4096 hM3
      _ = 4096 * (3 * m + 2) + 12288 := by rw [Nat.mul_add]
  have hMid : eff + (131072 + 12288) ≤ pg + 20 * 1024 * 1024 + 131072 * m := by
    calc eff + (131072 + 12288)
      _ ≤ eff + (8192 + 20 * 1024 * 1024) := Nat.add_le_add_left hC eff
      _ = (eff + 8192) + 20 * 1024 * 1024 := (Nat.add_assoc eff 8192 _).symm
      _ ≤ pg + 20 * 1024 * 1024 := Nat.add_le_add_right hPageEff _
      _ ≤ pg + 20 * 1024 * 1024 + 131072 * m := Nat.le_add_right _ _
  calc base + sb' + p63' + 4096 * (3 * m' + 2)
    _ = base + (sb' + p63') + 4096 * (3 * m' + 2) := by rw [Nat.add_assoc base sb' p63']
    _ ≤ base + (sb + p63 + (eff + 131072)) + (4096 * (3 * m + 2) + 12288) :=
        Nat.add_le_add (Nat.add_le_add_left hSum base) hM4096
    _ = (base + sb + p63 + 4096 * (3 * m + 2)) + (eff + (131072 + 12288)) := by
        generalize 4096 * (3 * m + 2) = gm
        generalize (131072 : Nat) = c1
        generalize (12288 : Nat) = c2
        ac_rfl
    _ ≤ (base + sb + p63 + 4096 * (3 * m + 2)) + (pg + 20 * 1024 * 1024 + 131072 * m) :=
        Nat.add_le_add_left hMid _

private theorem fineFootprint_step_le_aux {b b' : FineBudget} {req align eff : Nat}
    (hM : fineMaxMetaAreas b' ≤ fineMaxMetaAreas b + 1)
    (hEff : eff = req + (max align 16 - 16))
    (hSum : b'.cumSmallBytes + finePeak63Bytes b' ≤
      b.cumSmallBytes + finePeak63Bytes b + (eff + 131072)) :
    fineFootprint b' ≤ fineFootprint b + FineStepBound req align (fineMaxMetaAreas b) :=
  fineFootprint_step_le_arith BaseRootFine b.cumSmallBytes b'.cumSmallBytes
    (finePeak63Bytes b) (finePeak63Bytes b') (fineMaxMetaAreas b) (fineMaxMetaAreas b')
    req align eff (pageAlignUp (req + (max align 16 - 16) + 8192))
    hM hEff (pageAlignUp_le _) hSum

theorem fineFootprint_step_le (ev : FineEvent) (b : FineBudget) :
    fineFootprint (FineBudget.step ev b) ≤ fineFootprint b + fineStepReserve ev b := by
  cases ev with
  | free align req =>
    have ⟨hSB, hGS, hPB, hPC⟩ := stepFree_peaks_eq align req b
    have hEq : fineFootprint (FineBudget.step (.free align req) b) = fineFootprint b := by
      simp only [FineBudget.step, fineFootprint, fineMaxMetaAreas, fineMaxGroups, hSB, hGS, hPB, hPC]
    omega
  | alloc req =>
    have h := stepAligned_bounds 16 req b
    have hEff16 : mallocngAlignedEffSize 16 req = req := by
      unfold mallocngAlignedEffSize; simp
    refine fineFootprint_step_le_aux (eff := req)
      (fineMaxMetaAreas_step_add_le h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      (by simp) ?_
    simpa only [FineBudget.step, FineBudget.stepAlloc, hEff16] using h.2.2.2.2.1
  | aligned align req =>
    have h := stepAligned_bounds align req b
    refine fineFootprint_step_le_aux
      (fineMaxMetaAreas_step_add_le h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      (by unfold mallocngAlignedEffSize; by_cases ha : align ≤ 16 <;> simp [ha] <;> omega)
      h.2.2.2.2.1
  | realloc align oldSz newSz =>
    have hAdd := stepReallocAdd_bounds align newSz b
    have ⟨hSB, hGS, hPB, hPC⟩ :=
      stepFree_peaks_eq align oldSz (FineBudget.stepReallocAdd align newSz b)
    refine fineFootprint_step_le_aux (eff := mallocngAlignedEffSize align newSz)
      (fineMaxMetaAreas_step_add_le
        (b := b) (b' := FineBudget.step (.realloc align oldSz newSz) b)
        (by simp only [FineBudget.step, FineBudget.stepRealloc, hGS]; exact hAdd.2.2.2.2.2.1)
        (by simp only [FineBudget.step, FineBudget.stepRealloc, hPC]; exact hAdd.2.2.2.2.2.2))
      (by unfold mallocngAlignedEffSize; by_cases ha : align ≤ 16 <;> simp [ha] <;> omega) ?_
    simp only [FineBudget.step, FineBudget.stepRealloc, hSB, hPB]
    exact hAdd.2.2.2.2.1

/-! ## Per-Size-Class Group Projections and `GroupsSubGeometry` -/

def allGroups (st : MallocngSt) (sc : Nat) : List GroupDesc :=
  st.groups.filter (·.sc == sc)

/-- Nested child groups of class `ch` (`maplen = 0`) carved inside a parent slot of class `pSc`. -/
def nestedEdge (st : MallocngSt) (ch pSc : Nat) : List GroupDesc :=
  st.groups.filter fun g => decide (g.sc = ch ∧ g.maplen = 0 ∧ g.nestedCap = slotStride pSc - 4)

/-- Total `mmap` root bytes (`maplen * 4096`) of root groups in size class `sc`. -/
def rootBytes (st : MallocngSt) (sc : Nat) : Nat :=
  ((st.groups.filter fun g => decide (g.sc = sc ∧ 0 < g.maplen)).map fun g => g.maplen * 4096).sum

/-- Group-geometry inclusion (`st'.groups` is a `metaPtr`-indexed subset of `st.groups` preserving
    `sc`, `maplen`, `nestedCap`, `cnt`, and `stride`): holds across `free`, `try_avail`, `enframe`,
    and `realloc` Stage 2 in-place growth/shrink. -/
def GroupsSubGeometry (st' st : MallocngSt) : Prop :=
  (st'.groups.map (·.metaPtr)).Nodup ∧
  (st.groups.map (·.metaPtr)).Nodup ∧
  ∀ g' ∈ st'.groups, ∃ g ∈ st.groups,
    g.metaPtr = g'.metaPtr ∧
    g.sc = g'.sc ∧
    g.maplen = g'.maplen ∧
    g.nestedCap = g'.nestedCap ∧
    g.cnt = g'.cnt ∧
    g.stride = g'.stride

theorem GroupsSubGeometry.refl {st : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup) :
    GroupsSubGeometry st st :=
  ⟨hNd, hNd, fun g hg => ⟨g, hg, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem GroupsSubGeometry.trans {st₂ st₁ st₀ : MallocngSt}
    (h₂₁ : GroupsSubGeometry st₂ st₁) (h₁₀ : GroupsSubGeometry st₁ st₀) :
    GroupsSubGeometry st₂ st₀ := by
  refine ⟨h₂₁.1, h₁₀.2.1, fun g₂ hg₂ => ?_⟩
  obtain ⟨g₁, hg₁, hm₁, hsc₁, hml₁, hnc₁, hcnt₁, hstr₁⟩ := h₂₁.2.2 g₂ hg₂
  obtain ⟨g₀, hg₀, hm₀, hsc₀, hml₀, hnc₀, hcnt₀, hstr₀⟩ := h₁₀.2.2 g₁ hg₁
  exact ⟨g₀, hg₀, hm₀.trans hm₁, hsc₀.trans hsc₁, hml₀.trans hml₁,
    hnc₀.trans hnc₁, hcnt₀.trans hcnt₁, hstr₀.trans hstr₁⟩

private def eraseFirstMeta (m : BitVec 64) : List GroupDesc → List GroupDesc
  | [] => []
  | g :: gs => if g.metaPtr == m then gs else g :: eraseFirstMeta m gs

private theorem mem_eraseFirstMeta_of_ne {m : BitVec 64} {g : GroupDesc} {gs : List GroupDesc}
    (hg : g ∈ gs) (hne : g.metaPtr ≠ m) :
    g ∈ eraseFirstMeta m gs := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    simp only [eraseFirstMeta]
    by_cases hEq : (hd.metaPtr == m) = true
    · have hEq' : hd.metaPtr = m := beq_iff_eq.mp hEq
      rcases List.mem_cons.mp hg with rfl | htl
      · exact absurd hEq' hne
      · simp [hEq, htl]
    · simp only [Bool.not_eq_true] at hEq
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rcases List.mem_cons.mp hg with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

private theorem sub_map_eraseFirstMeta {m : BitVec 64} {gs : List GroupDesc} {x : BitVec 64}
    (hx : x ∈ (eraseFirstMeta m gs).map (·.metaPtr)) :
    x ∈ gs.map (·.metaPtr) := by
  induction gs with
  | nil => cases hx
  | cons hd tl ih =>
    simp only [eraseFirstMeta] at hx
    by_cases hEq : (hd.metaPtr == m) = true
    · simp only [hEq, ↓reduceIte] at hx
      exact List.mem_cons_of_mem _ hx
    · simp only [Bool.not_eq_true] at hEq
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.mem_cons] at hx ⊢
      exact hx.imp id ih

private theorem nodup_eraseFirstMeta {m : BitVec 64} {gs : List GroupDesc}
    (hNd : (gs.map (·.metaPtr)).Nodup) :
    ((eraseFirstMeta m gs).map (·.metaPtr)).Nodup := by
  induction gs with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNd
    simp only [eraseFirstMeta]
    by_cases hEq : (hd.metaPtr == m) = true
    · simp [hEq, hNd.2]
    · simp only [Bool.not_eq_true] at hEq
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.nodup_cons]
      exact ⟨fun hMem => hNd.1 (sub_map_eraseFirstMeta hMem), ih hNd.2⟩

private theorem sum_add_eraseFirstMeta_le (w : GroupDesc → Nat) {m : BitVec 64} {w₀ : Nat}
    {g : GroupDesc} {gs : List GroupDesc}
    (hNd : (gs.map (·.metaPtr)).Nodup)
    (hg : g ∈ gs) (hm : g.metaPtr = m) (hw : w₀ ≤ w g) :
    w₀ + ((eraseFirstMeta m gs).map w).sum ≤ (gs.map w).sum := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNd
    simp only [eraseFirstMeta, List.map_cons, List.sum_cons]
    by_cases hEq : (hd.metaPtr == m) = true
    · simp only [hEq, ↓reduceIte]
      have hEq' : hd.metaPtr = m := beq_iff_eq.mp hEq
      rcases List.mem_cons.mp hg with rfl | htl
      · omega
      · exfalso
        exact hNd.1 (hEq'.trans hm.symm ▸ List.mem_map_of_mem (f := (·.metaPtr)) htl)
    · simp only [Bool.not_eq_true] at hEq
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hg with rfl | htl
      · simp [hm] at hEq
      · have hSub := ih hNd.2 htl
        omega

/-- Weighted sum monotonicity across a `metaPtr`-injective mapping between duplicate-free group lists. -/
theorem sum_weight_le_of_inj_metaPtr (w' w : GroupDesc → Nat)
    {gs' gs : List GroupDesc}
    (hNd' : (gs'.map (·.metaPtr)).Nodup)
    (hNd : (gs.map (·.metaPtr)).Nodup)
    (hMap : ∀ g' ∈ gs', ∃ g ∈ gs, g.metaPtr = g'.metaPtr ∧ w' g' ≤ w g) :
    (gs'.map w').sum ≤ (gs.map w).sum := by
  induction gs' generalizing gs with
  | nil => simp
  | cons g' rest ih =>
    rw [List.map_cons, List.nodup_cons] at hNd'
    obtain ⟨g, hg, hm, hw⟩ := hMap g' (List.mem_cons_self ..)
    have hRest : ∀ r ∈ rest, ∃ gr ∈ eraseFirstMeta g'.metaPtr gs,
        gr.metaPtr = r.metaPtr ∧ w' r ≤ w gr := by
      intro r hr
      obtain ⟨gr, hgr, hmr, hwr⟩ := hMap r (List.mem_cons_of_mem _ hr)
      have hne : gr.metaPtr ≠ g'.metaPtr := by
        intro hContra
        exact hNd'.1 (hmr.symm.trans hContra ▸ List.mem_map_of_mem (f := (·.metaPtr)) hr)
      exact ⟨gr, mem_eraseFirstMeta_of_ne hgr hne, hmr, hwr⟩
    have hIH := ih hNd'.2 (nodup_eraseFirstMeta hNd) hRest
    have hStep := sum_add_eraseFirstMeta_le w hNd hg hm hw
    simp only [List.map_cons, List.sum_cons]
    omega

theorem nodup_filter_metaPtr (p : GroupDesc → Bool) {gs : List GroupDesc}
    (hNd : (gs.map (·.metaPtr)).Nodup) :
    (((gs.filter p).map (·.metaPtr))).Nodup := by
  induction gs with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNd
    simp only [List.filter_cons]
    cases hp : p hd with
    | false => exact ih hNd.2
    | true =>
      simp only [↓reduceIte, List.map_cons, List.nodup_cons]
      refine ⟨fun hMem => hNd.1 ?_, ih hNd.2⟩
      obtain ⟨g, hgF, hEq⟩ := List.mem_map.mp hMem
      exact hEq ▸ List.mem_map_of_mem (List.mem_filter.mp hgF).1

private theorem length_eq_sum_ones (xs : List GroupDesc) :
    xs.length = (xs.map fun _ => 1).sum := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => simp [ih]; omega

theorem GroupsSubGeometry.allGroups_length_le {st' st : MallocngSt}
    (hSub : GroupsSubGeometry st' st) (sc : Nat) :
    (allGroups st' sc).length ≤ (allGroups st sc).length := by
  rw [length_eq_sum_ones, length_eq_sum_ones]
  refine sum_weight_le_of_inj_metaPtr (fun _ => 1) (fun _ => 1)
    (nodup_filter_metaPtr _ hSub.1) (nodup_filter_metaPtr _ hSub.2.1) (fun g' hg' => ?_)
  unfold allGroups at hg' ⊢
  obtain ⟨hg'Mem, hScB⟩ := List.mem_filter.mp hg'
  obtain ⟨g, hgMem, hm, hsc, _, _, _, _⟩ := hSub.2.2 g' hg'Mem
  exact ⟨g, List.mem_filter.mpr ⟨hgMem, by rw [hsc]; exact hScB⟩, hm, Nat.le_refl 1⟩

theorem GroupsSubGeometry.nestedEdge_length_le {st' st : MallocngSt}
    (hSub : GroupsSubGeometry st' st) (ch pSc : Nat) :
    (nestedEdge st' ch pSc).length ≤ (nestedEdge st ch pSc).length := by
  rw [length_eq_sum_ones, length_eq_sum_ones]
  refine sum_weight_le_of_inj_metaPtr (fun _ => 1) (fun _ => 1)
    (nodup_filter_metaPtr _ hSub.1) (nodup_filter_metaPtr _ hSub.2.1) (fun g' hg' => ?_)
  unfold nestedEdge at hg' ⊢
  obtain ⟨hg'Mem, hPred⟩ := List.mem_filter.mp hg'
  obtain ⟨g, hgMem, hm, hsc, hml, hnc, _, _⟩ := hSub.2.2 g' hg'Mem
  exact ⟨g, List.mem_filter.mpr ⟨hgMem, by rw [hsc, hml, hnc]; exact hPred⟩, hm, Nat.le_refl 1⟩

theorem GroupsSubGeometry.rootBytes_le {st' st : MallocngSt}
    (hSub : GroupsSubGeometry st' st) (sc : Nat) :
    rootBytes st' sc ≤ rootBytes st sc := by
  unfold rootBytes
  refine sum_weight_le_of_inj_metaPtr (fun g => g.maplen * 4096) (fun g => g.maplen * 4096)
    (nodup_filter_metaPtr _ hSub.1) (nodup_filter_metaPtr _ hSub.2.1) (fun g' hg' => ?_)
  obtain ⟨hg'Mem, hPred⟩ := List.mem_filter.mp hg'
  obtain ⟨g, hgMem, hm, hsc, hml, _, _, _⟩ := hSub.2.2 g' hg'Mem
  exact ⟨g, List.mem_filter.mpr ⟨hgMem, by rw [hsc, hml]; exact hPred⟩, hm, by omega⟩

/-! ## Per-Group Fine Geometry and `Guaranteed63Threshold` Separation -/

/-- Fine per-group slot-count and `mmap` size bounds established at `alloc_group` creation and
    preserved across all subsequent mutations. -/
def GroupFineGeom (g : GroupDesc) : Prop :=
  (g.sc < 48 → cntMin g.sc ≤ g.cnt) ∧
  (g.sc < 48 → 0 < g.maplen →
    ValidRootCnt g.sc g.cnt ∧
    g.maplen * 4096 ≤ maxRootBytes g.sc ∧
    g.maplen * 4096 ≤ ceilRootPerSlot g.sc * g.cnt ∧
    g.maplen * 4096 ≤ Cost.grpMax g.sc 128) ∧
  (g.sc < 48 → g.maplen = 0 → ∀ pSc < 48, g.nestedCap = slotStride pSc - 4 →
    0 < minCntEdge g.sc pSc ∧ minCntEdge g.sc pSc ≤ g.cnt)

private theorem cntSel_le_32_check :
    ((List.range 48).all fun sc => decide (Cost.cntSel sc 128 ≤ 32)) = true := by
  decide +kernel

/-- Because every `cntSel sc u ≤ 32` (`4 * 32 ≤ 128`), `Cost.rootBytesAt sc u` saturates at `u = 128`. -/
theorem rootBytesAt_le_grpMax_128 {sc : Nat} (hsc : sc < 48) (u : Nat) :
    Cost.rootBytesAt sc u ≤ Cost.grpMax sc 128 := by
  by_cases hu : u ≤ 128
  · exact Cost.rootBytesAt_le_grpMax sc hu
  · have hcEq : Cost.cntSel sc u = Cost.cntSel sc 128 := by
      rw [Cost.cntSel_min sc u, Nat.min_eq_right (by omega)]
    have hcLe : Cost.cntSel sc 128 ≤ 32 :=
      of_decide_eq_true (List.all_eq_true.mp cntSel_le_32_check sc (List.mem_range.mpr hsc))
    have hEq : Cost.rootBytesAt sc u = Cost.rootBytesAt sc 128 := by
      dsimp only [Cost.rootBytesAt]
      rw [hcEq]
      by_cases hsz : slotStride sc * Cost.cntSel sc 128 + 16 ≤ 2048
      · simp only [hsz, ↓reduceIte]
      · have h4u : 4 * Cost.cntSel sc 128 ≤ u := by omega
        have h4_128 : 4 * Cost.cntSel sc 128 ≤ 128 := by omega
        simp only [hsz, ↓reduceIte, h4u, h4_128, or_true]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [hEq]
    exact Cost.rootBytesAt_le_grpMax sc (Nat.le_refl 128)

/-- Every `GroupFineGeom` group list satisfies `Cost.GroupsGrpBound 128`. -/
theorem groupsGrpBound_128_of_geom {gs : List GroupDesc}
    (hGeom : ∀ g ∈ gs, GroupFineGeom g) :
    Cost.GroupsGrpBound 128 gs :=
  fun g hg hPos hSc => ((hGeom g hg).2.1 hSc hPos).2.2.2

theorem GroupsSubGeometry.groupFineGeom {st' st : MallocngSt}
    (hSub : GroupsSubGeometry st' st)
    (hGeom : ∀ g ∈ st.groups, GroupFineGeom g) :
    ∀ g' ∈ st'.groups, GroupFineGeom g' := by
  intro g' hg'
  obtain ⟨g, hg, _, hsc, hml, hnc, hcnt, _⟩ := hSub.2.2 g' hg'
  have hG := hGeom g hg
  unfold GroupFineGeom at hG ⊢
  rw [← hsc, ← hml, ← hnc, ← hcnt]
  exact hG

private def checkSlabStrideBounds : Bool :=
  (List.range 48).all fun sc =>
    decide (ceilRootPerSlot sc ≤ Guaranteed63Threshold ∧ 16 ≤ slotStride sc ∧ slotStride sc ≤ 131072)

private theorem checkSlabStrideBounds_true : checkSlabStrideBounds = true := by
  decide +kernel

private theorem slab_sc_bounds {sc : Nat} (hsc : sc < 48) :
    ceilRootPerSlot sc ≤ Guaranteed63Threshold ∧ 16 ≤ slotStride sc ∧ slotStride sc ≤ 131072 :=
  of_decide_eq_true (List.all_eq_true.mp checkSlabStrideBounds_true sc (List.mem_range.mpr hsc))

/-- Key threshold separation lemma: no `.liveUser` slot with `Guaranteed63Threshold ≤ req`
    (`135,168 ≤ req`) can ever reside in a slab group (`g.sc < 48`), even after in-place `realloc`
    Stage 2 growth inside a single-slot `sc = 47` group (`stride = 135,152`, capacity `135,148`). -/
theorem no_slab_slot_ge_guaranteed63 {st : MallocngSt} {g : GroupDesc}
    (hgWf : GroupWf st g) (hgGeom : GroupFineGeom g)
    {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {req eff : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p req eff)
    (hBig : Guaranteed63Threshold ≤ req) :
    g.sc = 63 := by
  rcases hgWf.1 with hScLt | hSc63
  · exfalso
    have ⟨hCeilLe, hStrGe16, hStrLe⟩ := slab_sc_bounds hScLt
    have hMemFit : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := hgWf.2.2.2.2.2.2.1
    have hCntStride : 12 + g.cnt * g.stride ≤ g.totalBytes := hgWf.2.2.2.2.2.2.2.1
    have hSlotsLen : g.slots.length = g.cnt := hgWf.2.2.1
    have hIdxCnt : idx + 1 ≤ g.cnt := by omega
    have hStrideBounds : 4 ≤ g.stride ∧ g.stride ≤ Guaranteed63Threshold := by
      unfold GroupDesc.stride
      by_cases hCond : (g.lastIdx == 0 && decide (0 < g.maplen)) = true
      · simp only [hCond, ↓reduceIte]
        have ⟨hLastB, hPosB⟩ := Bool.and_eq_true_iff.mp hCond
        have hLast0 : g.lastIdx = 0 := beq_iff_eq.mp hLastB
        have hPos : 0 < g.maplen := of_decide_eq_true hPosB
        have hCnt1 : g.cnt = 1 := by unfold GroupDesc.cnt; omega
        have hMapLe : g.maplen * 4096 ≤ ceilRootPerSlot g.sc * g.cnt :=
          (hgGeom.2.1 hScLt hPos).2.2.1
        rw [hCnt1, Nat.mul_one] at hMapLe
        unfold Guaranteed63Threshold at hCeilLe ⊢
        omega
      · simp only [Bool.not_eq_true] at hCond
        simp only [hCond, Bool.false_eq_true, ↓reduceIte]
        unfold Guaranteed63Threshold
        omega
    have hMulLe : (idx + 1) * g.stride ≤ g.cnt * g.stride :=
      Nat.mul_le_mul_right g.stride hIdxCnt
    have hSpanFit : 16 + idx * g.stride + (g.stride - 4) ≤ g.totalBytes := by
      have : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
      omega
    have h248 : (2 : Nat) ^ 48 < 2 ^ 64 := by decide
    have h16Nat : (16#64).toNat = 16 := rfl
    have hStorageNat : g.storage.toNat = g.mem.toNat + 16 := by
      unfold GroupDesc.storage
      rw [BitVec.toNat_add, h16Nat]
      exact Nat.mod_eq_of_lt (by omega)
    have hIdxStrLt : idx * g.stride < 2 ^ 64 := by omega
    have hStartNat : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride := by
      unfold GroupDesc.slotStart
      rw [BitVec.toNat_add, hStorageNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hIdxStrLt]
      exact Nat.mod_eq_of_lt (by omega)
    have hStrSubLt : g.stride - 4 < 2 ^ 64 := by omega
    have hEndNat : (g.slotEnd idx).toNat = (g.slotStart idx).toNat + (g.stride - 4) := by
      unfold GroupDesc.slotEnd
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hStrSubLt, hStartNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hSWf := hgWf.slot_wf idx hIdx
    rw [hSlot] at hSWf
    have hStartLe : (g.slotStart idx).toNat ≤ p.toNat := hSWf.2.2.2.2.2.1
    have hEndGe : p.toNat + req ≤ (g.slotEnd idx).toNat := hSWf.2.2.2.2.2.2.1
    omega
  · exact hSc63

/-- Deallocation-phase group & `.liveUser` preservation relation (`st'` after freeing/retiring
    non-`.liveUser` slots/groups from `st`):
    1. `GroupsSubGeometry st' st`: every group in `st'` comes from a matching-`metaPtr` group in
       `st` with identical `(metaPtr, sc, maplen, nestedCap, parentMeta, lastIdx)`;
    2. `live_slots_iff`: matching-`metaPtr` groups have equal slot length and identical `.liveUser`
       slots at every slot index;
    3. `retired_no_liveUser`: every group in `st` whose `metaPtr` is absent from `st'.groups` had
       zero `.liveUser` slots in `st`;
    4. `metaAreas_eq` and `liveMap_eq`: `st'.metaAreas = st.metaAreas` and `st'.liveMap = st.liveMap`. -/
structure SameLiveUserSub (st' st : MallocngSt) : Prop where
  geom_sub : GroupsSubGeometry st' st
  live_slots_iff :
    ∀ g' ∈ st'.groups, ∀ g ∈ st.groups, g'.metaPtr = g.metaPtr →
      g'.slots.length = g.slots.length ∧
      ∀ (j : Nat) (hj' : j < g'.slots.length) (hj : j < g.slots.length)
        (q : BitVec 64) (rq eq : Nat),
        g'.slots[j]'hj' = .liveUser q rq eq ↔ g.slots[j]'hj = .liveUser q rq eq
  retired_no_liveUser :
    ∀ g ∈ st.groups, g.metaPtr ∉ st'.groups.map GroupDesc.metaPtr →
      ∀ (j : Nat) (hj : j < g.slots.length) (q : BitVec 64) (rq eq : Nat),
        g.slots[j]'hj ≠ .liveUser q rq eq
  metaAreas_eq : st'.metaAreas = st.metaAreas
  liveMap_eq : st'.liveMap = st.liveMap

/-! ## Live Slot Counters, `FineAlignWf`, `MallocngFineInv`, and `FineHeapImpl` -/

def groupLiveUserCount (g : GroupDesc) : Nat :=
  (g.slots.filter fun s => match s with | .liveUser _ _ _ => true | _ => false).length

def groupClaimedCount (g : GroupDesc) : Nat :=
  (g.slots.filter SlotState.isClaimed).length

def groupNestedCount (g : GroupDesc) : Nat :=
  (g.slots.filter fun s => match s with | .liveNested _ => true | _ => false).length

/-- Total live user allocations currently residing in slab class `sc`. -/
def liveSlotsInClass (st : MallocngSt) (sc : Nat) : Nat :=
  ((allGroups st sc).map groupLiveUserCount).sum

def slotIs63Large : SlotState → Bool
  | .liveUser _ req _ => decide (Guaranteed63Threshold ≤ req)
  | _ => false

/-- Declared `sc = 63` cost of a large `.liveUser` slot under ghost alignment map `alignMap`. -/
def slotDecl63 (alignMap : BitVec 64 → Option Nat) : SlotState → Nat
  | .liveUser p req _ =>
    if Guaranteed63Threshold ≤ req then declCost63 req ((alignMap p).getD 16) else 0
  | _ => 0

def groups63 (st : MallocngSt) : List GroupDesc :=
  st.groups.filter (·.sc == 63)

def isLarge63Group (g : GroupDesc) : Bool :=
  g.slots.any slotIs63Large

def large63Groups (st : MallocngSt) : List GroupDesc :=
  (groups63 st).filter isLarge63Group

def straddle63Groups (st : MallocngSt) : List GroupDesc :=
  (groups63 st).filter (fun g => !isLarge63Group g)

def straddle63Bytes (st : MallocngSt) : Nat :=
  ((straddle63Groups st).map fun g => g.maplen * 4096).sum

def large63DeclBytes (st : MallocngSt) (alignMap : BitVec 64 → Option Nat) : Nat :=
  ((large63Groups st).map fun g => (g.slots.map (slotDecl63 alignMap)).sum).sum

/-- Ghost alignment map agreement with `st`:
    every `alignMap` entry has `16 ≤ al` and belongs to `st.liveMap`, and every `.liveUser` slot
    in `st.groups` carries an `alignMap` entry bounding `g.maplen * 4096` when `g.sc = 63`. -/
def FineAlignWf (st : MallocngSt) (alignMap : BitVec 64 → Option Nat) : Prop :=
  (∀ (p : BitVec 64) (al : Nat), alignMap p = some al → 16 ≤ al ∧ ∃ n, st.liveMap p = some n) ∧
  (∀ g ∈ st.groups, ∀ idx : Nat, (hIdx : idx < g.slots.length) →
    ∀ (p : BitVec 64) (req eff : Nat),
      g.slots[idx]'hIdx = .liveUser p req eff →
      ∃ al : Nat, alignMap p = some al ∧
        (g.sc = 63 →
          eff - max req MallocngMinBlockCost ≤ al - 16 ∧
          g.maplen * 4096 ≤ declCost63 req al))

/-- Inductive per-size-class heap state invariant layered alongside `MallocngWFInflight`. -/
structure MallocngFineInv (inflight : Nat) (b : FineBudget)
    (ivs : List (BitVec 64 × Nat)) (alignMap : BitVec 64 → Option Nat)
    (st : MallocngSt) : Prop where
  ivs_eq : inflight = 0 → ivs = dynamicRootRegions st
  groups_geom : ∀ g ∈ st.groups, GroupFineGeom g
  alignMap_wf : FineAlignWf st alignMap
  live63_eq :
    large63DeclBytes st alignMap = b.live63Bytes ∧
    (large63Groups st).length = b.live63Count
  live63_le_peak :
    b.live63Bytes ≤ b.peak63Bytes ∧
    b.live63Count ≤ b.peak63Count
  metaAreas_le : st.metaAreas.length ≤ fineMaxMetaAreas b
  small_witness :
    ∃ (pk : List Nat) (pkStraddleCnt pkStraddleBytes : Nat),
      pk.length = 48 ∧
      (∀ sc < 48, liveSlotsInClass st sc ≤ pk.getD sc 0) ∧
      (∀ sc < 48, (allGroups st sc).length ≤ gBound pk sc) ∧
      (∀ ch < 48, ∀ pSc < 48, (nestedEdge st ch pSc).length ≤ edgeBound pk ch pSc) ∧
      (∀ sc < 48, rootBytes st sc ≤ rBound pk sc) ∧
      (straddle63Groups st).length ≤ pkStraddleCnt ∧
      straddle63Bytes st ≤ pkStraddleBytes ∧
      linForm grpWtS pk + FineScale * pkStraddleCnt ≤ b.cumSmallGroupsS ∧
      linForm slotWt pk + pkStraddleBytes ≤ b.cumSmallBytes

abbrev fineBaseGam (γ : GhostName) : GhostName := (natUnpair γ).1

abbrev fineAlignGam (γ : GhostName) : GhostName := (natUnpair γ).2

/-- Per-block ownership token `BlockM γ p n effAlign` for the fine `mallocng` cost model. -/
def FineBlock (γ : GhostName) (p : BitVec 64) (n effAlign : Nat) : SepProp :=
  ⌜16 ≤ effAlign⌝ ∗
  MallocngBlockToken (fineBaseGam γ) p n ∗
  ghostMapElem (fineAlignGam γ) p effAlign

/-- Exclusive non-RO body of `FineCoreImpl` at `inflight` bound. -/
noncomputable def FineCoreStInflightA (inflight : Nat) (γ : GhostName)
    (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat))
    (alignMap : BitVec 64 → Option Nat)
    (liveCost peakCost : Nat) (st : MallocngSt) : SepProp :=
  ⌜MallocngFineInv inflight b ivs alignMap st⌝ ∗
  ghostMapAuth (fineAlignGam γ) alignMap ∗
  MallocngCoreStInflightA inflight (fineBaseGam γ) A brkStart brk liveCost peakCost st

/-- Sealed allocator-private invariant `CoreM` for the fine `mallocng` cost model. -/
@[irreducible] noncomputable def FineCoreImpl
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngRoTablesA A ∗
  ∃∗ st : MallocngSt,
  ∃∗ alignMap : BitVec 64 → Option Nat,
  ∃∗ liveCost : Nat,
  ∃∗ peakCost : Nat,
    FineCoreStInflightA 0 γ A brkStart brk b ivs alignMap liveCost peakCost st

/-- Sealed full heap + runtime invariant `HeapM` for the fine `mallocng` cost model. -/
@[irreducible] noncomputable def FineHeapImpl
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  FineCoreImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp

theorem FineCoreImpl_eq (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineCoreImpl γ A brkStart brk b ivs =
      (MallocngRoTablesA A ∗
       ∃∗ st : MallocngSt,
       ∃∗ alignMap : BitVec 64 → Option Nat,
       ∃∗ liveCost : Nat,
       ∃∗ peakCost : Nat,
         FineCoreStInflightA 0 γ A brkStart brk b ivs alignMap liveCost peakCost st) := by
  unfold FineCoreImpl
  rfl

theorem FineHeapImpl_eq (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineHeapImpl γ A tp brkStart brk b ivs =
      (FineCoreImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp) := by
  unfold FineHeapImpl
  rfl

/-! ## Startup Non-Vacuity -/

private theorem getD_replicate_zero : ∀ (n j : Nat), (List.replicate n 0).getD j 0 = 0
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, j + 1 => getD_replicate_zero n j

private theorem linForm_zero48 (w : Nat → Nat) :
    linForm w (List.replicate 48 0) = 0 := by
  unfold linForm
  have hMap :
      ((List.range 48).map fun j => w j * (List.replicate 48 0).getD j 0) =
        (List.range 48).map fun _ => 0 := by
    refine List.map_congr_left fun j _ => ?_
    rw [getD_replicate_zero, Nat.mul_zero]
  rw [hMap]
  decide

theorem emptyMallocngStOpt_fineInv (auxvPtr : BitVec 64) (snap : Option MallocngAuxvSnap) :
    MallocngFineInv 0 FineBudget.init [] (fun _ => none) (emptyMallocngStOpt auxvPtr snap) := by
  have hGroupsEmpty : (emptyMallocngStOpt auxvPtr snap).groups = [] := rfl
  have hMetaEmpty : (emptyMallocngStOpt auxvPtr snap).metaAreas = [] := rfl
  have hGuardEmpty : (emptyMallocngStOpt auxvPtr snap).guardPages = [] := rfl
  have hAvailEmpty : (emptyMallocngStOpt auxvPtr snap).availMetaPages = [] := rfl
  refine
    { ivs_eq := fun _ => by
        unfold dynamicRootRegions
        rw [hMetaEmpty, hGuardEmpty, hAvailEmpty, hGroupsEmpty]
        rfl
      groups_geom := fun g hg => by rw [hGroupsEmpty] at hg; cases hg
      alignMap_wf := by
        refine ⟨?_, ?_⟩
        · intro _ _ h; cases h
        · intro g hg; rw [hGroupsEmpty] at hg; cases hg
      live63_eq := by
        unfold large63DeclBytes large63Groups groups63 FineBudget.init
        rw [hGroupsEmpty]
        simp
      live63_le_peak := ⟨Nat.le_refl 0, Nat.le_refl 0⟩
      metaAreas_le := by
        rw [hMetaEmpty]
        unfold fineMaxMetaAreas
        simp
      small_witness := ⟨List.replicate 48 0, 0, 0, ?_⟩ }
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sc _
    unfold liveSlotsInClass allGroups
    rw [hGroupsEmpty]; simp
  · intro sc _
    unfold allGroups gBound
    rw [hGroupsEmpty]; simp
  · intro ch _ pSc _
    unfold nestedEdge
    rw [hGroupsEmpty]; simp
  · intro sc _
    unfold rootBytes
    rw [hGroupsEmpty]; simp
  · unfold straddle63Groups groups63
    rw [hGroupsEmpty]; simp
  · unfold straddle63Bytes straddle63Groups groups63
    rw [hGroupsEmpty]; simp
  · rw [linForm_zero48]; simp [FineBudget.init]
  · rw [linForm_zero48]; simp [FineBudget.init]

end LibsignalBinary.Heap.Fine
