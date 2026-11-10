/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.CostModel
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Fine Budget Pool `libc.need_locks` Projection

Projects `((A.libc + 3#64) ↦₈ 0#8) ∗ anyHeap` from `mallocngBudgetPoolAt`,
`fineRustCliAllocBudget.pool`, and `fineHookRustCliAllocBudget.pool` so normal `main` return
supplies `__libc.need_locks = 0` to `musl` exit (`__stdio_exit_needed`).
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj
open ProofLib (
  Entails SepProp entails_anyHeap sepConj_mono_left sepConj_mono_right
)
open VerifiedLibraries.Mallocng (MallocngAddrs MallocngRuntime mallocngAddrsOfPlacement)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits MallocngCostModelIface MallocngCostModelSound
  mallocngBudgetPoolAt mallocngBudgetPoolAt_split_runtime mallocngBudgetPoolInv
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX fineHookRustCliAllocBudget
)

theorem mallocngAddrsOfPlacement_libc_eq (mmpl : Obj.MultiPlacement) :
    (mallocngAddrsOfPlacement mmpl).libc = mmpl.ρ "__libc" :=
  rfl

/-- Project `((A.libc + 3#64) ↦₈ 0#8) ∗ anyHeap` from any sound `mallocngBudgetPoolAt`. -/
theorem mallocngBudgetPoolAt_entails_needLocks_anyHeap
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s ⊢
      ((A.libc + 3#64) ↦₈ 0#8) ∗ anyHeap := by
  rw [mallocngBudgetPoolAt_split_runtime hS γ A tp brkStart lim st s]
  unfold MallocngRuntime
  have hEq :
      ((∃∗ staticIvs : List (BitVec 64 × Nat),
        ∃∗ ivs : List (BitVec 64 × Nat),
          ⌜mallocngBudgetPoolInv lim staticIvs ivs s ∧ s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
          I.CoreM γ A brkStart s.brk st ivs) ∗
        ((∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          ((A.libc + 3#64) ↦₈ 0#8) ∗
          ((A.libc + 48#64) ↦₆₄ 4096#64))) =
      (((A.libc + 3#64) ↦₈ 0#8) ∗
        ((∃∗ staticIvs : List (BitVec 64 × Nat),
          ∃∗ ivs : List (BitVec 64 × Nat),
            ⌜mallocngBudgetPoolInv lim staticIvs ivs s ∧ s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
            I.CoreM γ A brkStart s.brk st ivs) ∗
          (∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          ((A.libc + 48#64) ↦₆₄ 4096#64))) := by
    sep_ac_rfl
  rw [hEq]
  exact sepConj_mono_right (entails_anyHeap _)

/-- Project `(((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap` from
    `(fineRustCliAllocBudget γ mmpl tp brkStart).pool lim st s`. -/
theorem pool_entails_needLocks_anyHeap
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : FineBudget) (s : State) :
    (fineRustCliAllocBudget γ mmpl tp brkStart).pool lim st s ⊢
      (((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap :=
  mallocngBudgetPoolAt_entails_needLocks_anyHeap fineCostModelSound γ
    (mallocngAddrsOfPlacement mmpl) tp brkStart lim st s

/-- Project `(((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap` from
    `(fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st s`. -/
theorem hookPool_entails_needLocks_anyHeap
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : FineBudget) (s : State) :
    (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st s ⊢
      (((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap := by
  change VerifiedLibraries.mallocngLib.codeRO mmpl ∗
      (fineRustCliAllocBudget γ mmpl tp brkStart).pool lim st s ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝ ⊢
    (((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (pool_entails_needLocks_anyHeap γ mmpl tp brkStart lim st s))) ?_
  have hEq :
      VerifiedLibraries.mallocngLib.codeRO mmpl ∗
        ((((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap) ∗
        ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝ =
      (((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗
        (VerifiedLibraries.mallocngLib.codeRO mmpl ∗ anyHeap ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝) := by
    sep_ac_rfl
  rw [hEq]
  exact sepConj_mono_right (entails_anyHeap _)

end LibsignalBinary.Heap.Fine
