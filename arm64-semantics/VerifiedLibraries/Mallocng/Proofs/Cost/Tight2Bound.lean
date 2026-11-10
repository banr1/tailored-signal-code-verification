/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Cost.GroupTable
public import VerifiedLibraries.Mallocng.Proofs.Cost.Reserve
public import VerifiedLibraries.Mallocng.Proofs.Cost.IvsTight2

/-!
# Usage-Indexed Tight Footprint and Budget Numerics

Defines `tight2Footprint`, `tight2RootG`, and `tight2EventBudget` at usage bound
`U = peakCount + slack` without importing `AllocCostModel`, proves monotonicity and `MallocngHeap`
interval bounds, and evaluates closed-form constants at `peakCount ≤ 5` and `liveCount ≤ 4`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 ProofLib VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Table monotonicity -/

private theorem foldr_max_le {xs : List Nat} {M : Nat} (h : ∀ x ∈ xs, x ≤ M) :
    xs.foldr max 0 ≤ M := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons y ys ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h y (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem grpMaxAll_mono {U V : Nat} (h : U ≤ V) : grpMaxAll U ≤ grpMaxAll V := by
  unfold grpMaxAll
  refine foldr_max_le (fun x hx => ?_)
  obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hx
  exact Nat.le_trans (grpMax_mono sc h) (grpMax_le_grpMaxAll (List.mem_range.mp hsc) V)

private theorem sum_map_le_sum_map {f g : Nat → Nat} :
    ∀ (xs : List Nat), (∀ x ∈ xs, f x ≤ g x) → (xs.map f).sum ≤ (xs.map g).sum
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (List.mem_cons_self ..))
      (sum_map_le_sum_map xs (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem keptSum_mono {U V : Nat} (h : U ≤ V) : keptSum U ≤ keptSum V :=
  sum_map_le_sum_map _ (fun sc _ => keptMax_mono sc h)

/-! ## Footprint, root-group bound, and event budget -/

/-- Dynamic footprint of the usage-indexed tight bound at usage bound `U`. -/
def tight2Footprint (U pc lc cost : Nat) : Nat :=
  keptSum U + 24576 * ((88 + 8 * pc) / 101) + 40960 + grpMaxAll U * lc + cost

theorem tight2Footprint_mono {U U' pc pc' lc lc' cost cost' : Nat} (hU : U ≤ U') (hp : pc ≤ pc')
    (hl : lc ≤ lc') (hc : cost ≤ cost') :
    tight2Footprint U pc lc cost ≤ tight2Footprint U' pc' lc' cost' := by
  have h1 := keptSum_mono hU
  have h2 : (88 + 8 * pc) / 101 ≤ (88 + 8 * pc') / 101 := Nat.div_le_div_right (by omega)
  have h3 : grpMaxAll U * lc ≤ grpMaxAll U' * lc' := Nat.mul_le_mul (grpMaxAll_mono hU) hl
  unfold tight2Footprint; omega

/-- Root-group `mmap` bound `G` charged by the per-call reserve at `peakCount = pc` (the single
    place the reserve's `G` is chosen): `mallocngRootGroupBoundAt pc = min (grpMaxAll (pc + 6)) 1 MiB`,
    the bound the placed entry contracts' per-call deltas use. -/
def tight2RootG (pc : Nat) : Nat := mallocngRootGroupBoundAt pc

theorem tight2RootG_mono {p q : Nat} (h : p ≤ q) : tight2RootG p ≤ tight2RootG q := by
  unfold tight2RootG mallocngRootGroupBoundAt
  have := grpMaxAll_mono (U := p + 6) (V := q + 6) (by omega)
  omega

/-- Client-facing per-call budget: footprint plus reserve at caps `n`, `p`, `c`, `r`. -/
def tight2EventBudget (slack n p c r : Nat) : Nat :=
  tight2Footprint (p + slack) p n c + mallocngTight2StepBoundG (tight2RootG p) r p

theorem tight2EventBudget_mono {slack slack' n n' p p' c c' r r' : Nat} (hs : slack ≤ slack')
    (hn : n ≤ n') (hp : p ≤ p') (hc : c ≤ c') (hr : r ≤ r') :
    tight2EventBudget slack n p c r ≤ tight2EventBudget slack' n' p' c' r' :=
  Nat.add_le_add (tight2Footprint_mono (by omega) hp hn hc)
    (mallocngTight2StepBoundG_mono (tight2RootG_mono hp) hr hp)

/-! ## Heap bounds -/

theorem mallocngHeap_ivs_tight2Footprint {slack : Nat} (hs : 6 ≤ slack)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (mallocngIface.MallocngHeap γ A tp brkStart brk b ivs) h) :
    ivs.length ≤ 48 + 2 * b.peakCount ∧
    (ivs.map Prod.snd).sum ≤
      tight2Footprint (b.peakCount + slack) b.peakCount b.liveCount b.liveCost := by
  obtain ⟨_, hLen, hSum⟩ := mallocngHeap_ivs_tight2_bound γ A tp brkStart brk b ivs h hHolds
  have hMono : tight2Footprint (b.peakCount + 6) b.peakCount b.liveCount b.liveCost ≤
      tight2Footprint (b.peakCount + slack) b.peakCount b.liveCount b.liveCost :=
    tight2Footprint_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨hLen, Nat.le_trans (by unfold tight2Footprint; exact hSum) hMono⟩

theorem mallocngHeap_ivs_tight2Footprint_caps {slack n p c : Nat} (hs : 6 ≤ slack)
    {γ : GhostName} {A : MallocngAddrs} {tp brkStart brk : BitVec 64}
    {b : MallocngBudget} {ivs : List (BitVec 64 × Nat)} {h : Heap}
    (hHolds : SepProp.Holds (mallocngIface.MallocngHeap γ A tp brkStart brk b ivs) h)
    (hn : b.liveCount ≤ n) (hp : b.peakCount ≤ p) (hc : b.liveCost ≤ c) :
    ivs.length ≤ 48 + 2 * p ∧ (ivs.map Prod.snd).sum ≤ tight2Footprint (p + slack) p n c := by
  obtain ⟨hLen, hSum⟩ := mallocngHeap_ivs_tight2Footprint hs γ A tp brkStart brk b ivs h hHolds
  exact ⟨by omega, Nat.le_trans hSum (tight2Footprint_mono (by omega) hp hn hc)⟩

/-! ## Closed-form constants at `peakCount ≤ 5`, `liveCount ≤ 4` -/

theorem grpMaxAll_five : grpMaxAll 5 = 176128 := by decide +kernel
theorem keptSum_eleven : keptSum 11 = 704512 := by decide +kernel
theorem grpMaxAll_eleven : grpMaxAll 11 = 315392 := by decide +kernel

theorem tight2EventBudget_slack0_p5_n4 (c r : Nat) :
    tight2EventBudget 0 4 5 c r = 1445888 + c + max 1042788 (r + 185964) := by
  have hk : keptSum (5 + 0) = keptSum 5 := rfl
  have hg : grpMaxAll (5 + 0) = grpMaxAll 5 := rfl
  unfold tight2EventBudget tight2Footprint mallocngTight2StepBoundG mallocngSlotReserve
    mallocngLargeReserve mallocngMetaStep tight2RootG
  rw [mallocngRootGroupBoundAt_five]
  generalize hK : keptSum (5 + 0) = K
  generalize hG : grpMaxAll (5 + 0) = G
  rw [hk, keptSum_five] at hK
  rw [hg, grpMaxAll_five] at hG
  subst hK hG
  omega

theorem tight2EventBudget_slack6_p5_n4 (c r : Nat) :
    tight2EventBudget 6 4 5 c r = 2031616 + c + max 1042788 (r + 185964) := by
  have hk : keptSum (5 + 6) = keptSum 11 := rfl
  have hg : grpMaxAll (5 + 6) = grpMaxAll 11 := rfl
  unfold tight2EventBudget tight2Footprint mallocngTight2StepBoundG mallocngSlotReserve
    mallocngLargeReserve mallocngMetaStep tight2RootG
  rw [mallocngRootGroupBoundAt_five]
  generalize hK : keptSum (5 + 6) = K
  generalize hG : grpMaxAll (5 + 6) = G
  rw [hk, keptSum_eleven] at hK
  rw [hg, grpMaxAll_eleven] at hG
  subst hK hG
  omega

theorem tight2EventBudget_p5_n4_slot {c r : Nat} :
    (r ≤ 856824 → tight2EventBudget 0 4 5 c r = 2488676 + c) ∧
    (r ≤ 856824 → tight2EventBudget 6 4 5 c r = 3074404 + c) := by
  rw [tight2EventBudget_slack0_p5_n4, tight2EventBudget_slack6_p5_n4]
  constructor <;> intro h <;> omega

theorem tight2_hb_budget (c r : Nat) :
    tight2EventBudget 6 4 5 c r ≤ (if r ≤ 856824 then 3074404 + c else 2217580 + c + r) := by
  rw [tight2EventBudget_slack6_p5_n4]
  split <;> omega

end VerifiedLibraries.Mallocng.Proofs.Cost
