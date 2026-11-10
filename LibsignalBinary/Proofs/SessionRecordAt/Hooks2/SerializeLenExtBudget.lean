/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved`-Carrying Relocatable Serialization Pure Leaves

Establishes the `VmPreserved`-carrying contracts (`DefsBudget.vecVecCloneEmptySpec`,
`DefsBudget.msgKeyLenSpec`, and `DefsBudget.chainLenSpec`) for Blocks `117`, `118`, and `88` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExtBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
  subroutine_ok_withLsCodeLoaded_of_plain
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record.Placed (
  blkPl_88 blkPl_117 blkPl_118 lsProg_88 lsProg_117 lsProg_118
)
open CryptoVerification.E2E.Record.Serialization (vecVecCloneStack)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  vecVecCloneEmptySpec msgKeyLenSpec chainLenSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget (msgKeyLen_placed_ok)
open LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenBudget (chainLen_placed_ok)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Block `117`: `<Vec<Vec<u8>> as Clone>::clone` on an empty vector -/

private theorem stackAt_vecVecClone (sp : BitVec 64) :
    stackAt sp vecVecCloneStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        stackAt (sp - 96#64) allocHookStack ∗
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := stackAt_split_cells sp allocHookStack 12 (by decide)
  have hadd : allocHookStack + 8 * 12 = vecVecCloneStack := by decide
  rw [hadd] at h1
  change stackAt sp vecVecCloneStack =
    stackAt (sp - 96#64) allocHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]
  simp only [sepExists_sepConj_right]

private theorem memRegion_24_cells (dst : BitVec 64) :
    memRegion dst 24 =
      (∃∗ d0 : BitVec 64, dst ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (dst + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (dst + 16#64) ↦₆₄ d2) := by
  have h1 := memRegion_split dst 8 16 (by decide)
  have h2 := memRegion_split (dst + 8#64) 8 8 (by decide)
  have hadd : dst + 8#64 + 8#64 = dst + 16#64 := by rw [BitVec.add_assoc]; rfl
  change memRegion dst 24 = memRegion dst 8 ∗ memRegion (dst + 8#64) 16 at h1
  change memRegion (dst + 8#64) 16 = memRegion (dst + 8#64) 8 ∗ memRegion (dst + 8#64 + 8#64) 8 at h2
  rw [h1, h2, hadd, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]

/-- Block `117` (`<Vec<Vec<u8>> as Clone>::clone` on empty source) meets
`DefsBudget.vecVecCloneEmptySpec` (`VmPreserved`-carrying). -/
theorem vecVecCloneEmpty_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_117 H) (blkPl_117).base vecVecCloneEmptySpec := by
  let S0 := CryptoVerification.E2E.Record.Serialization.vecVecCloneEmptySpec
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hsp_align =>
    ⟨S0.pre x s0, R, hpre, ?_⟩
  have hstep : SepWP (lsProg_117 H) (s0.readReg64 .x30) s0 (S0.pre x s0)
      (fun sf P_f => VmPreserved s0 sf ∧
        ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ S0.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) := by
    obtain ⟨dst, src⟩ := x
    dsimp only [S0, CryptoVerification.E2E.Record.Serialization.vecVecCloneEmptySpec] at *
    simp only [stackAt_vecVecClone, memRegion_24_cells, vecHeader,
      sepExists_sepConj_left, sepExists_sepConj_right] at *
    by_vm_steps (
      wp_pull_exists
      refine SepWP.pure_elim ?_
      rintro ⟨rfl, rfl, hx2⟩
      wp_steps
      wp_done
    )
  refine SepWP.mono hstep fun sf P_f _ _ ⟨hvm, hq, hsp, hcs⟩ => ⟨fun hm => ?_, hsp, hcs⟩
  have hq' := hq hm
  dsimp only [S0, CryptoVerification.E2E.Record.Serialization.vecVecCloneEmptySpec,
    vecVecCloneEmptySpec] at hq' ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq' ⊢
  exact ⟨⟨hq'.1, hvm⟩, hq'.2⟩

/-! ## Relocatable `[LibsignalPlacement]` leaves -/

/-- Block `117` (`Vec<Vec<u8>>::clone` on empty source) wrapped in `withLsCodeLoaded lsmpl`. -/
theorem vecVecCloneEmpty_placed_ok_ext [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_117 H) (blkPl_117).base
      (withLsCodeLoaded lsmpl vecVecCloneEmptySpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (vecVecCloneEmpty_placed_ok H)

theorem vecVecCloneEmpty_placed_ok_cl [LibsignalPlacement]
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 117)
      (withLsCl lsmpl vecVecCloneEmptySpec) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (vecVecCloneEmpty_placed_ok_ext H)

/-- Block `118` (`MessageKey::encoded_len`) wrapped in `withLsCodeLoaded lsmpl`. -/
theorem msgKeyLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (msgKeyLen_placed_ok A H)

theorem msgKeyLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 118)
      (withLsCl lsmpl (msgKeyLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (msgKeyLen_placed_ok_ext A H)

/-- Block `88` (`Chain::encoded_len`) under `[LibsignalPlacement]`. -/
theorem chainLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) :=
  chainLen_placed_ok A H

theorem chainLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 88)
      (withLsCl lsmpl (chainLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (chainLen_placed_ok A H)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExtBudget
