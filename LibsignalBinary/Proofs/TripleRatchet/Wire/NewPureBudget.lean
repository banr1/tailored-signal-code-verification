/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPure

/-!
# Budget-Threaded Placed Hook Helpers for `<SignalMessage>::new`

Re-exports `RustAlloc`-independent panic-stub helpers from `Wire.NewPure` and provides
`VmPreserved`-strengthened `[LibsignalPlacement]` extern hook wrappers (`__rust_alloc`,
`__rust_dealloc`, `__rust_no_alloc_shim_is_unstable_v2`, and `memcpy`) for Block `63`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg libsignalMutatedBlocks lsρ
   lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsMemcpySym)
open CryptoVerification.LibsignalTripleRatchet
  (framelessMemcpySpec noAllocShimSpec mac_ls_hook_ok_of_mem
   lsRawVecHandleErrorSym lsAllocHandleErrorSym
   new_externAt?_handle_error new_externAt?_handle_alloc_error)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget allocMemcpyVmSpec
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustCliDeallocNoOomSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

/-! ## Re-exports of panic-stub helpers from `Wire.NewPure` -/

export CryptoVerification.LibsignalTripleRatchet
  (lsRawVecHandleErrorSym lsAllocHandleErrorSym
   new_externAt?_handle_error new_externAt?_handle_alloc_error)

/-! ## Relocatable `[LibsignalPlacement]` budget hook helpers (Block `63`) -/

/-- `VmPreserved`-strengthened counterpart of `noAllocShimSpec`. -/
abbrev noAllocShimBudgetSpec : Spec Unit :=
  withVmPreserved noAllocShimSpec

/-- `VmPreserved`-strengthened counterpart of `framelessMemcpySpec`. -/
abbrev framelessMemcpyBudgetSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved framelessMemcpySpec

theorem new_shim_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec :=
  mac_ls_hook_ok_of_mem h_shim (by decide) hi hunmut

theorem new_shim_placed_ok_of_rustAllocShimVm [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_shim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec := by
  have h0 : subroutine_ok prog (lsρ lsRustNoAllocShimSym) rustAllocShimVmSpec :=
    mac_ls_hook_ok_of_mem h_shim (by decide) hi hunmut
  refine subroutine_ok_mono h0 (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustAllocShimVmSpec, noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1.2.1, hq.2⟩

theorem new_alloc_placed_ok [LibsignalPlacement] {M : AllocCostModel} {prog : Program} {i : Nat}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zero : Bool}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim zero))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim zero) :=
  mac_ls_hook_ok_of_mem h_alloc (by decide) hi hunmut

theorem new_allocNoOom_placed_ok [LibsignalPlacement] {M : AllocCostModel} {prog : Program}
    {i : Nat} {A : RustCliAllocBudget M} {lim : BudgetLimits} {zero : Bool}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim zero))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim zero) :=
  subroutine_ok_allocNoOom_of_budget (new_alloc_placed_ok h_alloc hi hunmut)

theorem new_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel} {prog : Program} {i : Nat}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  mac_ls_hook_ok_of_mem h_dealloc (by decide) hi hunmut

theorem new_deallocNoOom_placed_ok [LibsignalPlacement] {M : AllocCostModel} {prog : Program}
    {i : Nat} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustCliDeallocNoOomSpec M A lim) :=
  mac_ls_hook_ok_of_mem h_dealloc (by decide) hi hunmut

set_option maxRecDepth 200000 in
theorem new_memcpy_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsMemcpySym) framelessMemcpyBudgetSpec :=
  mac_ls_hook_ok_of_mem h_mc (by decide) hi hunmut

set_option maxRecDepth 200000 in
theorem new_memcpy_placed_ok_of_allocMemcpyVm [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_mc : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsMemcpySym) framelessMemcpyBudgetSpec := by
  have h0 : subroutine_ok prog (lsρ lsMemcpySym) allocMemcpyVmSpec :=
    mac_ls_hook_ok_of_mem h_mc (by decide) hi hunmut
  refine subroutine_ok_mono h0 ?_ ?_
  · rintro ⟨dst, src, bs⟩ R s0 hp
    dsimp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec,
      allocMemcpyVmSpec] at hp ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
    have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
      rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_bv, hlt⟩, ?_⟩
    rw [sepConj_assoc]
    exact hm
  · rintro ⟨dst, src, bs⟩ R s0 sf hq
    dsimp only [allocMemcpyVmSpec, framelessMemcpyBudgetSpec, withVmPreserved,
      framelessMemcpySpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0, hacp, hvm⟩, hm⟩
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, ⟨hx0, hacp.2.1⟩, hm⟩

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
