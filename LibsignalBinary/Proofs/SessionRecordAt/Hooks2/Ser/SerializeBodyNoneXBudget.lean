/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep

/-!
# Budget-Threaded `SessionRecord::serialize` `None` Branch (Block `52`)

Verifies relocatable `SessionRecord::serialize` (Block `52`) on a `SessionRecord` with no current
session (`serializeNoneSpecX M A lim`), transporting `A.pool lim st` unchanged (`0` allocations).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneXBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded
  lsmpl withLsCodeLoaded withLsCl sepWP_seq_lscl lsρ lsMemcpySym
)
open CryptoVerification.RustHeap (vecHeader vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap okTagVec)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  bytes336_to_w012 cells_12_pack
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  memRegion_out32_stack_noneX sepWP_exists_left_sepX
  vecU8_nil_from_out_cellsX repack_stack_none_cellsX
)
open LibsignalBinary.Heap (
  VmPreserved AllocCostModel BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget (
  vecVecCloneSubSpecX memcpySubSpecX
  vecVecClone_placed_sub_clX memcpy_placed_sub_clX
)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Specification -/

/-- `SessionRecord::serialize` on a record with no current session (`0` allocations), threading
    `A.pool lim st s` to `A.pool lim st sf` at `serializeStackX`. -/
def serializeNoneSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((self, out, prevPtr), st) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = out⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      A.pool lim st s ∗ memRegion out 32 ∗ stackAt s.sp serializeStackX
  post := fun ((self, out, prevPtr), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      (out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (out + 8#64) [] ∗
      A.pool lim st sf ∗ stackAt s0.sp serializeStackX

/-! ## Relocatable `[LibsignalPlacement]` proof (Block `52`) -/

section Placed

theorem serialize_none_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeNoneSpecX M A lim)) := by
  have hmemcpy := memcpy_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hvv := vecVecClone_placed_sub_clX (callerProg := lsProg_52 H)
  change subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) (withLsCl lsmpl memcpySubSpecX) at hmemcpy
  change subroutine_ok (lsProg_52 H) (lsmpl.base 117) (withLsCl lsmpl vecVecCloneSubSpecX) at hvv
  dsimp only [withLsCl, memcpySubSpecX, vecVecCloneSubSpecX] at hmemcpy hvv
  unfold withLsCodeLoaded serializeNoneSpecX
  simp only [noneCap, okTagVec, memRegion_out32_stack_noneX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨⟨self, out, prevPtr⟩, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 117)
  wp_steps_sync_pool (lsmpl.base 117)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hvv ⟨s0.sp - 800#64, prevPtr⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  conv => arg 4; simp only [vecHeader, arm64_norm, *]
  wp_steps_sync_pool (lsρ lsMemcpySym)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  have hbs336 : v_stk_12.length = 336 := by assumption
  rw [← hbs336]
  wp_call hmemcpy (s0.sp - 768#64, s0.sp - 432#64, v_stk_12)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  conv => arg 4; simp only [*]
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  wp_steps_sync_pool (s0.readReg64 .lr)
  refine SepWP.fold (vecU8_nil_from_out_cellsX A.repAlloc out) (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  refine SepWP.fold (repack_stack_none_cellsX s0.sp _ _ _ _ hbs336) (by sep_frame) ?_
  wp_done

end Placed

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneXBudget
