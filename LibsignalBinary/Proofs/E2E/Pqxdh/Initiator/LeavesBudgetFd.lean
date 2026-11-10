/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesDecode
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# `fs`-Preserving Placed Contract for `<kem::Ciphertext>::serialize` (Block `71`)

Proves `kemCiphertextSerialize_keepsFs_placed_ok` on Block `71` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`, preserving `sf.fs = s0.fs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudgetFd

open Arm64 ProofLib
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_71 blkPl_71
  ls_hook_ok_of_mem lsMemcpySym lsRustAllocSym lsRustNoAllocShimSym lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (tryCloneFromRefStack)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget
  VmPreserved rustAllocEvents rustCliAllocBudgetSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack subroutine_ok_rustCliAllocNoOom_withStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  rustAllocShimVmSpec allocMemcpyVmSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget (
  kemCiphertextSerializeSpec
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_kemSerialize48_fd (sp : BitVec 64) :
    stackAt sp tryCloneFromRefStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp 4096 6 (by decide)

private theorem memRegion_1569_split_fd (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), memRegion_one]

/-- Relocatable `[LibsignalPlacement]` verification of `<kem::Ciphertext>::serialize` (Block `71`)
against `keepsFs (kemCiphertextSerializeSpec M A lim)`. -/
theorem kemCiphertextSerialize_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_71).rebase (blkPl_71).base H) (blkPl_71).base
      (keepsFs (kemCiphertextSerializeSpec M A lim)) := by
  unfold keepsFs kemCiphertextSerializeSpec
  simp only [stackAt_kemSerialize48_fd]
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustNoAllocShimSym) rustAllocShimVmSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hmemcpy' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsMemcpySym) allocMemcpyVmSpec := ls_hook_ok_of_mem hmemcpy
  dsimp only [rustAllocShimVmSpec] at hshim'
  dsimp only [allocMemcpyVmSpec] at hmemcpy'
  dsimp only [rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init g s0
  rcases g with ⟨⟨hdrPtr, boxPtr, ctBytes⟩, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x0 = hdrPtr›
  have hfe_raw : FitsEvents M lim st [.alloc 1569] := by
    simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 1569 1)›
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (1569 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (1569 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have htr_shim : sf.trace = s0.trace := ‹AllocCallPreserved _ sf›.2.1
  have hfs_shim : sf.fs = s0.fs := ‹AllocCallPreserved _ sf›.1
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (1569, 1, st)
  have htr_alloc : sf_1.trace = sf.trace := ‹AllocCallPreserved _ sf_1›.2.1
  have hfs_alloc : sf_1.fs = sf.fs := ‹AllocCallPreserved _ sf_1›.1
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [memRegion_1569_split_fd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => ?_
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  have hlen_lt : ctBytes.length < 2 ^ 64 := by rw [‹ctBytes.length = 1568›]; decide
  rw [← ‹ctBytes.length = 1568›]
  wp_call hmemcpy' (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, ctBytes)
  have htr_mc : sf_2.trace = sf_1.trace := ‹AllocCallPreserved _ sf_2›.2.1
  have hfs_mc : sf_2.fs = sf_1.fs := ‹AllocCallPreserved _ sf_2›.1
  have htr_all : sf_2.trace = s0.trace := by
    rw [htr_mc, htr_alloc, htr_shim]
  have hfs_all : sf_2.fs = s0.fs := by
    rw [hfs_mc, hfs_alloc, hfs_shim]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps
  simp only [pointsToBytes_cons]
  wp_done

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudgetFd
