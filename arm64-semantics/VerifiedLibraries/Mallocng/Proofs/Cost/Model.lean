/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Cost
public import VerifiedLibraries.Mallocng.Proofs.Cost.ModelAttr

/-!
# Lawful Allocator Cost Models and Fit Predicates

Event-log folds (`stepEvents`, `evalLog`, `peakOver`), monotonicity laws (`LawfulCostModel`) over
`AllocCostModel`, dynamic capacity fit predicates (`FitsEvent`, `FitsEvents`), and budget invariants
for `mallocngTight2CostModel`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open VerifiedLibraries.Mallocng

/-! ## Event Logs -/

/-- Fold `evs` left-to-right through `M.step` from `st`. -/
def stepEvents (M : AllocCostModel) (evs : List AllocEvent) (st : M.σ) : M.σ :=
  evs.foldl (fun acc ev => M.step ev acc) st

/-- Model state after a full ghost log from `M.init`. -/
def evalLog (M : AllocCostModel) (evs : List AllocEvent) : M.σ :=
  stepEvents M evs M.init

@[simp, cost_simp] theorem stepEvents_nil (M : AllocCostModel) (st : M.σ) :
    stepEvents M [] st = st := rfl

@[simp, cost_simp] theorem stepEvents_cons (M : AllocCostModel) (ev : AllocEvent)
    (evs : List AllocEvent) (st : M.σ) :
    stepEvents M (ev :: evs) st = stepEvents M evs (M.step ev st) := rfl

@[simp, cost_simp] theorem stepEvents_append (M : AllocCostModel) (evs₁ evs₂ : List AllocEvent)
    (st : M.σ) : stepEvents M (evs₁ ++ evs₂) st = stepEvents M evs₂ (stepEvents M evs₁ st) :=
  List.foldl_append

@[simp, cost_simp] theorem evalLog_nil (M : AllocCostModel) : evalLog M [] = M.init := rfl

@[cost_simp] theorem evalLog_cons (M : AllocCostModel) (ev : AllocEvent) (evs : List AllocEvent) :
    evalLog M (ev :: evs) = stepEvents M evs (M.step ev M.init) := rfl

@[simp, cost_simp] theorem evalLog_append (M : AllocCostModel) (evs₁ evs₂ : List AllocEvent) :
    evalLog M (evs₁ ++ evs₂) = stepEvents M evs₂ (evalLog M evs₁) :=
  stepEvents_append M evs₁ evs₂ M.init

theorem evalLog_concat (M : AllocCostModel) (evs : List AllocEvent) (ev : AllocEvent) :
    evalLog M (evs ++ [ev]) = M.step ev (evalLog M evs) := by
  simp

/-- Largest `footprint + stepReserve` reached while executing `evs` from `st` (`0` for `[]`): the
    physical capacity a caller must provide for the whole log. -/
def peakOver (M : AllocCostModel) : M.σ → List AllocEvent → Nat
  | _, [] => 0
  | st, ev :: evs => max (M.footprint st + M.stepReserve ev st) (peakOver M (M.step ev st) evs)

@[simp, cost_simp] theorem peakOver_nil (M : AllocCostModel) (st : M.σ) : peakOver M st [] = 0 := rfl

@[simp, cost_simp] theorem peakOver_cons (M : AllocCostModel) (st : M.σ) (ev : AllocEvent)
    (evs : List AllocEvent) :
    peakOver M st (ev :: evs) =
      max (M.footprint st + M.stepReserve ev st) (peakOver M (M.step ev st) evs) := rfl

@[simp, cost_simp] theorem peakOver_append (M : AllocCostModel) :
    ∀ (evs₁ evs₂ : List AllocEvent) (st : M.σ),
      peakOver M st (evs₁ ++ evs₂) =
        max (peakOver M st evs₁) (peakOver M (stepEvents M evs₁ st) evs₂)
  | [], _, _ => by simp
  | ev :: evs₁, evs₂, st => by
    simp only [List.cons_append, peakOver_cons, stepEvents_cons, peakOver_append M evs₁ evs₂,
      Nat.max_assoc]

/-! ## Lawful Cost Models -/

/-- User payload bytes requested by `ev` (`0` for `free`). -/
def evReqBytes : AllocEvent → Nat
  | .alloc req => req
  | .aligned align req => mallocngAlignedEffSize align req
  | .free _ _ => 0
  | .realloc align _ new => mallocngAlignedEffSize align new

/-- Monotonicity laws for a cost model `M`, stated on an over-approximation `peakFootprint` of the
    possibly shrinking `footprint` under an inductive invariant `Inv`. -/
structure LawfulCostModel (M : AllocCostModel) where
  Inv : M.σ → Prop
  inv_init : Inv M.init
  inv_step : ∀ (ev : AllocEvent) (st : M.σ), Inv st → Inv (M.step ev st)
  peakFootprint : M.σ → Nat
  footprint_le_peak : ∀ st : M.σ, Inv st → M.footprint st ≤ peakFootprint st
  peakFootprint_mono : ∀ (ev : AllocEvent) (st : M.σ), Inv st →
    peakFootprint st ≤ peakFootprint (M.step ev st)
  maxDynIvs_mono : ∀ (ev : AllocEvent) (st : M.σ), Inv st →
    M.maxDynIvs st ≤ M.maxDynIvs (M.step ev st)
  stepReserve_mono : ∀ (ev₀ ev : AllocEvent) (st : M.σ), Inv st →
    M.stepReserve ev₀ st ≤ M.stepReserve ev₀ (M.step ev st)
  req_le_stepReserve : ∀ (ev : AllocEvent) (st : M.σ), evReqBytes ev ≤ M.stepReserve ev st
  liveBytes : M.σ → Nat
  liveBytes_free_le : ∀ (al n : Nat) (st : M.σ), liveBytes (M.step (.free al n) st) ≤ liveBytes st

namespace LawfulCostModel

variable {M : AllocCostModel} (L : LawfulCostModel M)

theorem inv_stepEvents : ∀ (evs : List AllocEvent) (st : M.σ), L.Inv st → L.Inv (stepEvents M evs st)
  | [], _, h => h
  | ev :: evs, st, h => inv_stepEvents evs (M.step ev st) (L.inv_step ev st h)

theorem inv_evalLog (evs : List AllocEvent) : L.Inv (evalLog M evs) :=
  L.inv_stepEvents evs M.init L.inv_init

theorem peakFootprint_mono_events : ∀ (evs : List AllocEvent) (st : M.σ), L.Inv st →
    L.peakFootprint st ≤ L.peakFootprint (stepEvents M evs st)
  | [], _, _ => Nat.le_refl _
  | ev :: evs, st, h => Nat.le_trans (L.peakFootprint_mono ev st h)
      (peakFootprint_mono_events evs (M.step ev st) (L.inv_step ev st h))

theorem maxDynIvs_mono_events : ∀ (evs : List AllocEvent) (st : M.σ), L.Inv st →
    M.maxDynIvs st ≤ M.maxDynIvs (stepEvents M evs st)
  | [], _, _ => Nat.le_refl _
  | ev :: evs, st, h => Nat.le_trans (L.maxDynIvs_mono ev st h)
      (maxDynIvs_mono_events evs (M.step ev st) (L.inv_step ev st h))

theorem stepReserve_mono_events (ev₀ : AllocEvent) : ∀ (evs : List AllocEvent) (st : M.σ),
    L.Inv st → M.stepReserve ev₀ st ≤ M.stepReserve ev₀ (stepEvents M evs st)
  | [], _, _ => Nat.le_refl _
  | ev :: evs, st, h => Nat.le_trans (L.stepReserve_mono ev₀ ev st h)
      (stepReserve_mono_events ev₀ evs (M.step ev st) (L.inv_step ev st h))

theorem footprint_le_peak_events (evs : List AllocEvent) (st : M.σ) (h : L.Inv st) :
    M.footprint st ≤ L.peakFootprint (stepEvents M evs st) :=
  Nat.le_trans (L.footprint_le_peak st h) (L.peakFootprint_mono_events evs st h)

theorem peakOver_le (maxStep : Nat) : ∀ (evs : List AllocEvent) (st : M.σ), L.Inv st →
    (∀ ev ∈ evs, M.stepReserve ev (stepEvents M evs st) ≤ maxStep) →
    peakOver M st evs ≤ L.peakFootprint (stepEvents M evs st) + maxStep
  | [], _, _, _ => Nat.zero_le _
  | ev :: evs, st, h, hB => by
    have h1 := L.inv_step ev st h
    have hFp : M.footprint st ≤ L.peakFootprint (stepEvents M evs (M.step ev st)) :=
      Nat.le_trans (L.footprint_le_peak st h)
        (Nat.le_trans (L.peakFootprint_mono ev st h) (L.peakFootprint_mono_events evs _ h1))
    have hSt : M.stepReserve ev st ≤ maxStep :=
      Nat.le_trans (L.stepReserve_mono ev ev st h)
        (Nat.le_trans (L.stepReserve_mono_events ev evs _ h1) (hB ev List.mem_cons_self))
    have ih := peakOver_le maxStep evs (M.step ev st) h1
      (fun e he => hB e (List.mem_cons_of_mem ev he))
    simp only [peakOver_cons, stepEvents_cons]
    exact Nat.max_le.mpr ⟨by omega, ih⟩

end LawfulCostModel

/-! ## Fit Predicates -/

/-- Event `ev` fits at state `st` within dynamic physical capacity `physCap` (conserved
    `physPlusRw` minus static mapped bytes). -/
def FitsEvent (M : AllocCostModel) (physCap : Nat) (st : M.σ) (ev : AllocEvent) : Prop :=
  M.footprint st + M.stepReserve ev st ≤ physCap

/-- Every event of `evs` fits along `stepEvents M evs st`. -/
def FitsEvents (M : AllocCostModel) (physCap : Nat) : M.σ → List AllocEvent → Prop
  | _, [] => True
  | st, ev :: evs => FitsEvent M physCap st ev ∧ FitsEvents M physCap (M.step ev st) evs

@[simp, cost_simp] theorem fitsEvents_nil (M : AllocCostModel) (physCap : Nat) (st : M.σ) :
    FitsEvents M physCap st [] = True := rfl

@[simp, cost_simp] theorem fitsEvents_cons (M : AllocCostModel) (physCap : Nat) (st : M.σ)
    (ev : AllocEvent) (evs : List AllocEvent) :
    FitsEvents M physCap st (ev :: evs) =
      (FitsEvent M physCap st ev ∧ FitsEvents M physCap (M.step ev st) evs) := rfl

theorem fitsEvents_iff_peakOver (M : AllocCostModel) (physCap : Nat) :
    ∀ (st : M.σ) (evs : List AllocEvent), FitsEvents M physCap st evs ↔ peakOver M st evs ≤ physCap
  | _, [] => by simp
  | st, ev :: evs => by
    rw [fitsEvents_cons, peakOver_cons, Nat.max_le, fitsEvents_iff_peakOver M physCap _ evs]
    rfl

@[simp, cost_simp] theorem fitsEvents_append (M : AllocCostModel) (physCap : Nat)
    (evs₁ evs₂ : List AllocEvent) (st : M.σ) :
    FitsEvents M physCap st (evs₁ ++ evs₂) ↔
      FitsEvents M physCap st evs₁ ∧ FitsEvents M physCap (stepEvents M evs₁ st) evs₂ := by
  simp only [fitsEvents_iff_peakOver, peakOver_append, Nat.max_le]

theorem fitsEvents_of_peak {M : AllocCostModel} (L : LawfulCostModel M) {physCap maxStep : Nat}
    (evs : List AllocEvent) (st : M.σ) (h : L.Inv st)
    (hStep : ∀ ev ∈ evs, M.stepReserve ev (stepEvents M evs st) ≤ maxStep)
    (hCap : L.peakFootprint (stepEvents M evs st) + maxStep ≤ physCap) :
    FitsEvents M physCap st evs :=
  (fitsEvents_iff_peakOver M physCap st evs).mpr
    (Nat.le_trans (L.peakOver_le maxStep evs st h hStep) hCap)

/-! ## Budget Transitions of `mallocngTight2CostModel` -/

/-- Budget invariant of `mallocngTight2CostModel`: live counters never exceed their peaks. -/
def TightInv (b : MallocngBudget) : Prop := b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount

theorem tight_step_inv (ev : AllocEvent) (b : MallocngBudget) (h : TightInv b) :
    TightInv (mallocngTight2CostModel.step ev b) := by
  obtain ⟨h1, h2⟩ := h
  cases ev <;>
    simp only [mallocngTight2CostModel, mallocngAllocBudget, mallocngAlignedBudget,
      mallocngFreeBudget, mallocngReallocBudget, TightInv, ↓reduceIte, Bool.false_eq_true] <;>
    omega

theorem tight_step_peaks (ev : AllocEvent) (b : MallocngBudget) :
    b.peakCount ≤ (mallocngTight2CostModel.step ev b).peakCount ∧
      b.peakCost ≤ (mallocngTight2CostModel.step ev b).peakCost := by
  cases ev <;>
    simp only [mallocngTight2CostModel, mallocngAllocBudget, mallocngAlignedBudget,
      mallocngFreeBudget, mallocngReallocBudget, ↓reduceIte, Bool.false_eq_true] <;>
    omega

end VerifiedLibraries.Mallocng.Proofs.Cost
