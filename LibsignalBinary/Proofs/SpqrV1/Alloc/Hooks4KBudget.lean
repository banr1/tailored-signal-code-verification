/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WP.StateNorm

/-!
# Budget-Threaded 4 KiB Stack Allocator and Memory Contract Bundle

Provides `VmPreserved`-strengthened `sessionMemcpyROSpec4K` and the budget-threaded
`AllocContracts4K` bundle (`allocHookStack = 4096`) on `tripleRatchetProgAtExt b ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget

open Arm64 ProofLib
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  allocName deallocName memcpyName memmoveName memsetName reallocName shimName
  sessionMemcpyRegionSpec sessionMemcpySpec sessionMemmoveSpec sessionMemsetRegionSpec
  sessionMemsetSpec sessionShimSpec sub_ok_at_of_fnAddr tripleRatchetProgAtExt withStack
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Read-only `memcpy(dst, src, len)` region contract (`src ↦ᵣ bs`) with trace and VM preservation. -/
def sessionMemcpyROSpec4K : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K

theorem hookMemcpy_sessionMemcpyROSpec4K_ok : HookOk hookMemcpy sessionMemcpyROSpec4K := by
  intro x R s0 hrun hpre hsp
  rcases CryptoVerification.SpqrV1.Alloc.hookMemcpy_sessionMemcpyROSpec4K_ok x R s0 hrun hpre hsp
    with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyROSpec4K, withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨?_, hpost⟩
    dsimp only [hookMemcpy, retHook]
    simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]
  · exact Or.inr hrest

theorem libcMemcpyRO_of_sessionMemcpyRO4K {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (withStack sessionMemcpyROSpec4K stk)) :
    subroutine_ok prog addr (withVmPreserved (libcMemcpyROSpec stk)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  refine ⟨(dst, src, bs), R, ?_, ?_⟩
  · dsimp only [withVmPreserved, libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K,
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hle : bs.length ≤ 2 ^ 64 := by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt
    exact ⟨⟨hx0, hx1, hx2, hle⟩, hm⟩
  · intro sf hpost
    dsimp only [withVmPreserved, libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K,
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1.1, hpost.2.2⟩

/-- Budget-threaded 4 KiB (`allocHookStack`) allocator, `VmPreserved` memory, and shim contract bundle. -/
structure AllocContracts4K (b : BitVec 64) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop where
  alloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustCliAllocBudgetSpecBase M A lim false)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustCliDeallocBudgetSpecBase M A lim)
  realloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustCliReallocBudgetSpecBase M A lim)
  shim :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) (withVmPreserved sessionShimSpec)
  memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withVmPreserved (libcMemcpySpec hookStack))
  session_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withVmPreserved (sessionMemcpySpec hookStack))
  memcpy_ro : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withVmPreserved (libcMemcpyROSpec hookStack))
  session_memcpy_region_ro : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyROSpec4K hookStack)
  memcpy_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack (withVmPreserved memcpyRegionSpec) hookStack)
  session_memcpy_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack (withVmPreserved sessionMemcpyRegionSpec) hookStack)
  memmove : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName)
      (withVmPreserved (libcMemmoveSpec hookStack))
  session_memmove : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName)
      (withVmPreserved (sessionMemmoveSpec hookStack))
  memset : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName)
      (withVmPreserved (libcMemsetSpec hookStack))
  session_memset : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName)
      (withVmPreserved (sessionMemsetSpec hookStack))
  memset_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName)
      (withStack (withVmPreserved memsetRegionSpec) hookStack)
  session_memset_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName)
      (withStack (withVmPreserved sessionMemsetRegionSpec) hookStack)

namespace AllocContracts4K

variable {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {ext : String → Option (State → State)}

theorem alloc_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocBudgetSpecBase M A lim) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem shim_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved sessionShimSpec) :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem session_shim_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved sessionShimSpec) :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem memcpy_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (libcMemcpySpec hookStack)) :=
  sub_ok_at_of_fnAddr (hA.memcpy hookStack hstack hstack_le) name k hk

theorem session_memcpy_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (sessionMemcpySpec hookStack)) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack hstack hstack_le) name k hk

theorem memcpy_ro_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (libcMemcpyROSpec hookStack)) :=
  sub_ok_at_of_fnAddr (hA.memcpy_ro hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ro_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack sessionMemcpyROSpec4K hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region_ro hookStack hstack hstack_le) name k hk

theorem memcpy_region_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack (withVmPreserved memcpyRegionSpec) hookStack) :=
  sub_ok_at_of_fnAddr (hA.memcpy_region hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack (withVmPreserved sessionMemcpyRegionSpec) hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region hookStack hstack hstack_le) name k hk

theorem memmove_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (libcMemmoveSpec hookStack)) :=
  sub_ok_at_of_fnAddr (hA.memmove hookStack hstack hstack_le) name k hk

theorem session_memmove_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (sessionMemmoveSpec hookStack)) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack hstack hstack_le) name k hk

theorem memset_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (libcMemsetSpec hookStack)) :=
  sub_ok_at_of_fnAddr (hA.memset hookStack hstack hstack_le) name k hk

theorem session_memset_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (sessionMemsetSpec hookStack)) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack hstack_le) name k hk

theorem memset_region_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack (withVmPreserved memsetRegionSpec) hookStack) :=
  sub_ok_at_of_fnAddr (hA.memset_region hookStack hstack hstack_le) name k hk

theorem session_memset_region_ok_at (hA : AllocContracts4K b A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack (withVmPreserved sessionMemsetRegionSpec) hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memset_region hookStack hstack hstack_le) name k hk

end AllocContracts4K

end LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
