/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack

/-!
# Frame Carving and Stack Splitting for Panicking/OOM Callees

Provides `subroutine_ok_carve_frame` (frame preservation across normal return, panic, exit, and OOM
outcomes) and `stackAt_split_of_le` (splitting `stackAt sp m` into a lower `m - n` region and top
`stackAt sp n` frame) to lift fixed-stack callee contracts to arbitrary `stk ≥ need`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib

/-- Refines and frames `subroutine_ok` across all four outcomes (`post`, `onPanic`, `onExit`, and
`onOom`), returning the carved frame `F` alongside the caller frame `R` on each branch. -/
theorem subroutine_ok_carve_frame {α β : Type} {prog : Program} {entry : BitVec 64}
    {specC : Spec α} {specA : Spec β}
    (hok : subroutine_ok prog entry specC)
    (h : ∀ x R s0, (s0.mem ⊨ specA.pre x s0 ∗ R) →
      ∃ y F, (s0.mem ⊨ specC.pre y s0 ∗ (F ∗ R)) ∧
        (∀ sf, (sf.mem ⊨ specC.post y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ specA.post x s0 sf ∗ R)) ∧
        (∀ sf, (sf.mem ⊨ specC.onPanic y s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ specA.onPanic x s0 sf ∗ R)) ∧
        (∀ code sf, (sf.mem ⊨ specC.onExit y code s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ specA.onExit x code s0 sf ∗ R)) ∧
        (∀ sf, (sf.mem ⊨ specC.onOom y s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ specA.onOom x s0 sf ∗ R))) :
    subroutine_ok prog entry specA := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  obtain ⟨y, F, hy, hpost, hpanic, hexit, hoom⟩ := h x R s0 hp
  refine hok.mono_outcome y (F ∗ R) s0 hpc hrun hy hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost sf hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hpanic sf hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hexit code sf hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom sf hq⟩))

/-- Splits `stackAt sp m` into `memRegion (sp - m) (m - n) ∗ stackAt sp n` when `n ≤ m ≤ sp.toNat`. -/
theorem stackAt_split_of_le (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hbound : m ≤ sp.toNat) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  unfold stackAt
  have hsum : (m - n) + n = m := by omega
  have hsp : sp.toNat < 2 ^ 64 := sp.isLt
  refine memRegion_split'
    (b := sp - BitVec.ofNat 64 m)
    (b' := sp - BitVec.ofNat 64 n)
    (n := m - n) (k := n)
    hsum.symm ?_ (by omega)
  bv_omega

end CryptoVerification.SignalSession.Cli.Slots
