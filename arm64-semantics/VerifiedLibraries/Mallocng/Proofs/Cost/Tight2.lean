/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Model
public import VerifiedLibraries.Mallocng.Proofs.Cost.Tight2Table

/-!
# Tight Cost Model Laws and Client Bounds

Proves that `mallocngTight2CostModel` (`Spec/Cost.lean`, `U = peakCount + 6`) is a
`LawfulCostModel` (`tight2Lawful`) via `tight2Footprint` and `mallocngTight2StepBoundG`, and derives
closed-form client bounds (`tight2_footprint_le`, `tight2_stepReserve_le`, `tight2_fits_le`,
`tight2_fitsEvent`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open VerifiedLibraries.Mallocng

/-! ## Implementation-Shaped Bound Bridges -/

theorem tight2_footprint_eq (b : MallocngBudget) :
    mallocngTight2CostModel.footprint b =
      tight2Footprint (b.peakCount + 6) b.peakCount b.liveCount b.liveCost := by
  show mallocngKeptGroupsTab _ + _ + _ + mallocngGroupMaxTab _ * _ + _ = _
  rw [← keptSum_eq_tab, ← grpMaxAll_eq_tab]
  rfl

theorem tight2_stepReserve_eq (ev : AllocEvent) (b : MallocngBudget) :
    mallocngTight2CostModel.stepReserve ev b =
      mallocngTight2StepBoundG (tight2RootG b.peakCount) (evReqBytes ev) b.peakCount := by
  cases ev <;> exact mallocngTight2Reserve_eq _ _

/-! ## Lawfulness -/

/-- `mallocngTight2CostModel` is lawful, with
    `peakFootprint b = tight2Footprint U pc pc peakCost` and `liveBytes = liveCost`. -/
def tight2Lawful : LawfulCostModel mallocngTight2CostModel where
  Inv := TightInv
  inv_init := ⟨Nat.le_refl _, Nat.le_refl _⟩
  inv_step := tight_step_inv
  peakFootprint b := tight2Footprint (b.peakCount + 6) b.peakCount b.peakCount b.peakCost
  footprint_le_peak := fun b ⟨h1, h2⟩ =>
    Nat.le_trans (Nat.le_of_eq (tight2_footprint_eq b))
      (tight2Footprint_mono (Nat.le_refl _) (Nat.le_refl _) h2 h1)
  peakFootprint_mono := fun ev b _ => by
    have h1 := (tight_step_peaks ev b).1
    have h2 := (tight_step_peaks ev b).2
    exact tight2Footprint_mono (by omega) h1 h1 h2
  maxDynIvs_mono := fun ev b _ => by
    have := (tight_step_peaks ev b).1
    show 48 + 2 * b.peakCount ≤ 48 + 2 * (mallocngTight2CostModel.step ev b).peakCount
    omega
  stepReserve_mono := fun ev₀ ev b _ => by
    have h := (tight_step_peaks ev b).1
    have e1 := tight2_stepReserve_eq ev₀ b
    have e2 := tight2_stepReserve_eq ev₀ (mallocngTight2CostModel.step ev b)
    have hm := mallocngTight2StepBoundG_mono (tight2RootG_mono h) (Nat.le_refl (evReqBytes ev₀)) h
    omega
  req_le_stepReserve := fun ev b => by
    have e := tight2_stepReserve_eq ev b
    have : evReqBytes ev ≤
        mallocngTight2StepBoundG (tight2RootG b.peakCount) (evReqBytes ev) b.peakCount := by
      unfold mallocngTight2StepBoundG mallocngLargeReserve; omega
    omega
  liveBytes := MallocngBudget.liveCost
  liveBytes_free_le := fun al n b => by
    show (mallocngTight2CostModel.step (.free al n) b).liveCost ≤ b.liveCost
    simp only [mallocngTight2CostModel, mallocngFreeBudget, Bool.false_eq_true, ↓reduceIte]; omega

/-! ## Closed-Form Client Bounds -/

theorem tight2_footprint_le {n p c : Nat} (b : MallocngBudget)
    (hn : b.liveCount ≤ n) (hp : b.peakCount ≤ p) (hc : b.liveCost ≤ c) :
    mallocngTight2CostModel.footprint b ≤ tight2Footprint (p + 6) p n c := by
  rw [tight2_footprint_eq]
  exact tight2Footprint_mono (by omega) hp hn hc

theorem tight2_stepReserve_le {p r : Nat} (ev : AllocEvent) (b : MallocngBudget)
    (hp : b.peakCount ≤ p) (hr : evReqBytes ev ≤ r) :
    mallocngTight2CostModel.stepReserve ev b ≤ mallocngTight2StepBoundG (tight2RootG p) r p := by
  rw [tight2_stepReserve_eq]
  exact mallocngTight2StepBoundG_mono (tight2RootG_mono hp) hr hp

theorem tight2_fits_le {n p c r : Nat} (ev : AllocEvent) (b : MallocngBudget)
    (hn : b.liveCount ≤ n) (hp : b.peakCount ≤ p) (hc : b.liveCost ≤ c)
    (hr : evReqBytes ev ≤ r) :
    mallocngTight2CostModel.footprint b + mallocngTight2CostModel.stepReserve ev b ≤
      tight2EventBudget 6 n p c r :=
  Nat.add_le_add (tight2_footprint_le b hn hp hc) (tight2_stepReserve_le ev b hp hr)

theorem tight2_fitsEvent {n p c r physCap : Nat} {ev : AllocEvent} {b : MallocngBudget}
    (hn : b.liveCount ≤ n) (hp : b.peakCount ≤ p) (hc : b.liveCost ≤ c) (hr : evReqBytes ev ≤ r)
    (hCap : tight2EventBudget 6 n p c r ≤ physCap) :
    FitsEvent mallocngTight2CostModel physCap b ev :=
  Nat.le_trans (tight2_fits_le ev b hn hp hc hr) hCap

end VerifiedLibraries.Mallocng.Proofs.Cost
