/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Cost
public import VerifiedLibraries.Mallocng.Proofs.Cost.Tight2Bound

/-!
# Breakpoint Tables of the Tight Cost Model

Equates `grpMaxAll` and `keptSum` to `mallocngGroupMaxTab` and `mallocngKeptGroupsTab`
by monotonicity on each breakpoint interval and saturation at usage `128`, then derives
`mallocngTight2Reserve_eq`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Saturation at usage `128` -/

private theorem halveUsage_of_le : ∀ (f u c : Nat), 4 * c ≤ u → halveUsage f u c = c
  | 0, _, _, _ => rfl
  | f + 1, u, c, h => by
    simp only [halveUsage]
    split
    · omega
    · rfl

private theorem smallCnt_le_tab : ∀ sc < 9, ∀ i < 3, smallCnt sc i ≤ 31 := by decide +kernel

private theorem medCnt_le_tab : ∀ k < 4, (medCntTabBytes.getD k 0#8).toNat ≤ 32 := by
  decide +kernel

private theorem medCnt_le (sc : Nat) : medCnt sc ≤ 32 :=
  medCnt_le_tab (sc % 4) (Nat.mod_lt _ (by decide))

private theorem cntRaw_sat (sc u : Nat) (hu : 128 ≤ u) : cntRaw sc u = cntRaw sc 128 := by
  unfold cntRaw
  split
  · rename_i hsc
    have h0 := smallCnt_le_tab sc hsc 0 (by decide)
    simp only [show 4 * smallCnt sc 0 ≤ u by omega, show 4 * smallCnt sc 0 ≤ 128 by omega,
      ↓reduceIte]
  · have hm := medCnt_le sc
    rw [halveUsage_of_le 8 u _ (by omega), halveUsage_of_le 8 128 _ (by omega)]

private theorem cntSel_128_le : ∀ sc < 48, cntSel sc 128 ≤ 32 := by decide +kernel

private theorem rootBytesAt_sat {sc u : Nat} (hsc : sc < 48) (hu : 128 ≤ u) :
    rootBytesAt sc u = rootBytesAt sc 128 := by
  have hc : cntSel sc u = cntSel sc 128 := by unfold cntSel; rw [cntRaw_sat sc u hu]
  have hle := cntSel_128_le sc hsc
  unfold rootBytesAt
  simp only [hc]
  generalize cntSel sc 128 = c at hle ⊢
  have h1 : 4 * c ≤ u := by omega
  have h2 : 4 * c ≤ 128 := by omega
  have h3 : ¬ 2 * c > u := by omega
  have h4 : ¬ 2 * c > 128 := by omega
  simp only [h1, h2, h3, h4, or_true, ↓reduceIte, and_false, false_and]

private theorem grpMax_sat {sc : Nat} (hsc : sc < 48) :
    ∀ k, grpMax sc (128 + k) = grpMax sc 128
  | 0 => rfl
  | k + 1 => by
    show max (grpMax sc (128 + k)) (rootBytesAt sc (128 + k + 1)) = _
    rw [grpMax_sat hsc k, rootBytesAt_sat hsc (by omega)]
    have := rootBytesAt_le_grpMax sc (Nat.le_refl 128)
    omega

private theorem grpMax_sat' {sc U : Nat} (hsc : sc < 48) (hU : 128 ≤ U) :
    grpMax sc U = grpMax sc 128 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hU
  exact grpMax_sat hsc k

private theorem keptSum_sat {U : Nat} (hU : 128 ≤ U) : keptSum U = keptSum 128 := by
  unfold keptSum
  refine congrArg List.sum (List.map_congr_left fun sc hsc => ?_)
  unfold keptMax
  split
  · exact grpMax_sat' (List.mem_range.mp hsc) hU
  · rfl

private theorem grpMaxAll_sat {U : Nat} (hU : 128 ≤ U) : grpMaxAll U = grpMaxAll 128 := by
  unfold grpMaxAll
  exact congrArg (List.foldr max 0)
    (List.map_congr_left fun sc hsc => grpMax_sat' (List.mem_range.mp hsc) hU)

/-! ## Table equalities -/

private theorem eq_of_mono_between (f : Nat → Nat) (hf : ∀ {a b : Nat}, a ≤ b → f a ≤ f b)
    {lo hi U v : Nat} (hlo : f lo = v) (hhi : f hi = v) (h1 : lo ≤ U) (h2 : U ≤ hi) : f U = v := by
  have := hf h1
  have := hf h2
  omega

private theorem grpMaxAll_vals :
    grpMaxAll 0 = 131072 ∧ grpMaxAll 3 = 131072 ∧ grpMaxAll 4 = 176128 ∧
    grpMaxAll 5 = 176128 ∧ grpMaxAll 6 = 315392 ∧ grpMaxAll 15 = 315392 ∧
    grpMaxAll 16 = 524288 ∧ grpMaxAll 31 = 524288 ∧ grpMaxAll 32 = 1048576 ∧
    grpMaxAll 128 = 1048576 := by
  decide +kernel

theorem grpMaxAll_eq_tab (U : Nat) : grpMaxAll U = mallocngGroupMaxTab U := by
  obtain ⟨v0, v3, v4, v5, v6, v15, v16, v31, v32, v128⟩ := grpMaxAll_vals
  have hm : ∀ {a b : Nat}, a ≤ b → grpMaxAll a ≤ grpMaxAll b := grpMaxAll_mono
  unfold mallocngGroupMaxTab
  split
  · exact eq_of_mono_between grpMaxAll hm v0 v3 (by omega) (by omega)
  split
  · exact eq_of_mono_between grpMaxAll hm v4 v5 (by omega) (by omega)
  split
  · exact eq_of_mono_between grpMaxAll hm v6 v15 (by omega) (by omega)
  split
  · exact eq_of_mono_between grpMaxAll hm v16 v31 (by omega) (by omega)
  rcases Nat.lt_or_ge U 128 with h | h
  · exact eq_of_mono_between grpMaxAll hm v32 v128 (by omega) (by omega)
  · rw [grpMaxAll_sat h, v128]

private theorem keptSum_vals_lo :
    keptSum 0 = 675840 ∧ keptSum 7 = 675840 ∧ keptSum 8 = 704512 ∧ keptSum 15 = 704512 ∧
    keptSum 16 = 770048 ∧ keptSum 23 = 770048 ∧ keptSum 24 = 901120 ∧ keptSum 31 = 901120 ∧
    keptSum 32 = 1032192 ∧ keptSum 39 = 1032192 ∧ keptSum 40 = 1294336 ∧
    keptSum 47 = 1294336 ∧ keptSum 48 = 1556480 ∧ keptSum 55 = 1556480 := by
  decide +kernel

private theorem keptSum_vals_hi :
    keptSum 56 = 1818624 ∧ keptSum 63 = 1818624 ∧ keptSum 64 = 2080768 ∧
    keptSum 79 = 2080768 ∧ keptSum 80 = 2605056 ∧ keptSum 95 = 2605056 ∧
    keptSum 96 = 3129344 ∧ keptSum 111 = 3129344 ∧ keptSum 112 = 3653632 ∧
    keptSum 123 = 3653632 ∧ keptSum 124 = 3657728 ∧ keptSum 127 = 3657728 ∧
    keptSum 128 = 4177920 := by
  decide +kernel

theorem keptSum_eq_tab (U : Nat) : keptSum U = mallocngKeptGroupsTab U := by
  obtain ⟨a0, a7, a8, a15, a16, a23, a24, a31, a32, a39, a40, a47, a48, a55⟩ := keptSum_vals_lo
  obtain ⟨b56, b63, b64, b79, b80, b95, b96, b111, b112, b123, b124, b127, b128⟩ :=
    keptSum_vals_hi
  have hm : ∀ {a b : Nat}, a ≤ b → keptSum a ≤ keptSum b := keptSum_mono
  unfold mallocngKeptGroupsTab
  by_cases h0 : U < 8
  · simp only [h0, ↓reduceIte]; exact eq_of_mono_between keptSum hm a0 a7 (by omega) (by omega)
  simp only [h0, ↓reduceIte]
  by_cases h1 : U < 16
  · simp only [h1, ↓reduceIte]; exact eq_of_mono_between keptSum hm a8 a15 (by omega) (by omega)
  simp only [h1, ↓reduceIte]
  by_cases h2 : U < 24
  · simp only [h2, ↓reduceIte]; exact eq_of_mono_between keptSum hm a16 a23 (by omega) (by omega)
  simp only [h2, ↓reduceIte]
  by_cases h3 : U < 32
  · simp only [h3, ↓reduceIte]; exact eq_of_mono_between keptSum hm a24 a31 (by omega) (by omega)
  simp only [h3, ↓reduceIte]
  by_cases h4 : U < 40
  · simp only [h4, ↓reduceIte]; exact eq_of_mono_between keptSum hm a32 a39 (by omega) (by omega)
  simp only [h4, ↓reduceIte]
  by_cases h5 : U < 48
  · simp only [h5, ↓reduceIte]; exact eq_of_mono_between keptSum hm a40 a47 (by omega) (by omega)
  simp only [h5, ↓reduceIte]
  by_cases h6 : U < 56
  · simp only [h6, ↓reduceIte]; exact eq_of_mono_between keptSum hm a48 a55 (by omega) (by omega)
  simp only [h6, ↓reduceIte]
  by_cases h7 : U < 64
  · simp only [h7, ↓reduceIte]; exact eq_of_mono_between keptSum hm b56 b63 (by omega) (by omega)
  simp only [h7, ↓reduceIte]
  by_cases h8 : U < 80
  · simp only [h8, ↓reduceIte]; exact eq_of_mono_between keptSum hm b64 b79 (by omega) (by omega)
  simp only [h8, ↓reduceIte]
  by_cases h9 : U < 96
  · simp only [h9, ↓reduceIte]; exact eq_of_mono_between keptSum hm b80 b95 (by omega) (by omega)
  simp only [h9, ↓reduceIte]
  by_cases h10 : U < 112
  · simp only [h10, ↓reduceIte]; exact eq_of_mono_between keptSum hm b96 b111 (by omega) (by omega)
  simp only [h10, ↓reduceIte]
  by_cases h11 : U < 124
  · simp only [h11, ↓reduceIte]; exact eq_of_mono_between keptSum hm b112 b123 (by omega) (by omega)
  simp only [h11, ↓reduceIte]
  by_cases h12 : U < 128
  · simp only [h12, ↓reduceIte]; exact eq_of_mono_between keptSum hm b124 b127 (by omega) (by omega)
  simp only [h12, ↓reduceIte]
  rw [keptSum_sat (by omega), b128]

/-! ## Reserve bridge -/

/-- At usage bound `pc + 6` the group table equals `mallocngRootGroupBoundAt pc`
    (the `1 MiB` cap of `mallocngRootGroupBoundAt` is inactive). -/
theorem mallocngGroupMaxTab_eq_rootGroupBoundAt (pc : Nat) :
    mallocngGroupMaxTab (pc + 6) = mallocngRootGroupBoundAt pc := by
  have h : mallocngGroupMaxTab (pc + 6) ≤ 1048576 := by
    unfold mallocngGroupMaxTab; repeat' split
    all_goals omega
  unfold mallocngRootGroupBoundAt mallocngRootGroupBound
  rw [grpMaxAll_eq_tab]
  omega

theorem mallocngTight2Reserve_eq (req pc : Nat) :
    mallocngTight2Reserve req pc = mallocngTight2StepBound req pc := by
  rw [mallocngTight2StepBound_eq, ← mallocngGroupMaxTab_eq_rootGroupBoundAt]
  rfl

end VerifiedLibraries.Mallocng.Proofs.Cost
