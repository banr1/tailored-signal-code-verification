/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Unplaced-to-Placed Heap Contract Bridges

Precondition-strengthening lifts from unplaced (`…Base`) allocator contracts to
`LsRetAddr624`-narrowed placed contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

theorem hookOk_rustCliAllocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {zeroed : Bool} {f : State → State}
    (h : HookOk f (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    HookOk f (rustCliAllocBudgetSpec M A lim zeroed) :=
  fun ⟨size, align, st⟩ R s0 hrun hpre hsp => by
    have hpreB : s0.mem ⊨ (rustCliAllocBudgetSpecBase M A lim zeroed).pre (size, align, st) s0 ∗ R := by
      dsimp only [rustCliAllocBudgetSpec, rustCliAllocBudgetSpecBase] at hpre ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
    exact h (size, align, st) R s0 hrun hpreB hsp

theorem hookOk_rustCliDeallocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {f : State → State}
    (h : HookOk f (rustCliDeallocBudgetSpecBase M A lim)) :
    HookOk f (rustCliDeallocBudgetSpec M A lim) :=
  fun ⟨p, size, align, st⟩ R s0 hrun hpre hsp => by
    have hpreB : s0.mem ⊨ (rustCliDeallocBudgetSpecBase M A lim).pre (p, size, align, st) s0 ∗ R := by
      dsimp only [rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecBase] at hpre ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
    exact h (p, size, align, st) R s0 hrun hpreB hsp

theorem hookOk_rustCliReallocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {f : State → State}
    (h : HookOk f (rustCliReallocBudgetSpecBase M A lim)) :
    HookOk f (rustCliReallocBudgetSpec M A lim) :=
  fun ⟨p, old, align, new, bs, st⟩ R s0 hrun hpre hsp => by
    have hpreB : s0.mem ⊨ (rustCliReallocBudgetSpecBase M A lim).pre (p, old, align, new, bs, st) s0 ∗ R := by
      dsimp only [rustCliReallocBudgetSpec, rustCliReallocBudgetSpecBase] at hpre ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1, hpre.1.2.2.2.2.1, hpre.1.2.2.2.2.2.1, hpre.1.2.2.2.2.2.2.1⟩, hpre.2⟩
    exact h (p, old, align, new, bs, st) R s0 hrun hpreB hsp

theorem hookSat_rustCliAllocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {zeroed : Bool} {hooks : String → Option (State → State)} {name : String}
    (h : HookSat hooks name (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    HookSat hooks name (rustCliAllocBudgetSpec M A lim zeroed) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_rustCliAllocBudget_of_base hok⟩

theorem hookSat_rustCliDeallocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {name : String}
    (h : HookSat hooks name (rustCliDeallocBudgetSpecBase M A lim)) :
    HookSat hooks name (rustCliDeallocBudgetSpec M A lim) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_rustCliDeallocBudget_of_base hok⟩

theorem hookSat_rustCliReallocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {name : String}
    (h : HookSat hooks name (rustCliReallocBudgetSpecBase M A lim)) :
    HookSat hooks name (rustCliReallocBudgetSpec M A lim) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_rustCliReallocBudget_of_base hok⟩

theorem subroutine_ok_rustCliAllocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64} {zeroed : Bool}
    (h : subroutine_ok P entry (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    subroutine_ok P entry (rustCliAllocBudgetSpec M A lim zeroed) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp _
  have hpreB : s0.mem ⊨ (rustCliAllocBudgetSpecBase M A lim zeroed).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustCliAllocBudgetSpec, rustCliAllocBudgetSpecBase] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
  exact subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpreB hsp (fun _ hout => hout)

theorem subroutine_ok_rustCliDeallocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok P entry (rustCliDeallocBudgetSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, size, align, st⟩ R s0 hpc hrun hpre hsp _
  have hpreB : s0.mem ⊨ (rustCliDeallocBudgetSpecBase M A lim).pre (p, size, align, st) s0 ∗ R := by
    dsimp only [rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecBase] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
  exact subroutine_ok.mono_outcome h (p, size, align, st) R s0 hpc hrun hpreB hsp (fun _ hout => hout)

theorem subroutine_ok_rustCliReallocBudget_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P entry (rustCliReallocBudgetSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hsp _
  have hpreB : s0.mem ⊨ (rustCliReallocBudgetSpecBase M A lim).pre (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [rustCliReallocBudgetSpec, rustCliReallocBudgetSpecBase] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1, hpre.1.2.2.2.2.1, hpre.1.2.2.2.2.2.1, hpre.1.2.2.2.2.2.2.1⟩, hpre.2⟩
  exact subroutine_ok.mono_outcome h (p, old, align, new, bs, st) R s0 hpc hrun hpreB hsp (fun _ hout => hout)

theorem subroutine_ok_rustCliAllocNoOom_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64} {zeroed : Bool}
    (h : subroutine_ok P entry (rustCliAllocNoOomSpecBase M A lim zeroed)) :
    subroutine_ok P entry (rustCliAllocNoOomSpec M A lim zeroed) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp _
  have hpreB : s0.mem ⊨ (rustCliAllocNoOomSpecBase M A lim zeroed).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustCliAllocNoOomSpec, rustCliAllocNoOomSpecBase] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1⟩, hpre.2⟩
  exact subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpreB hsp (fun _ hout => hout)

abbrev subroutine_ok_rustCliDeallocNoOom_of_base := @subroutine_ok_rustCliDeallocBudget_of_base

theorem subroutine_ok_rustCliReallocNoOom_of_base [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliReallocNoOomSpecBase M A lim)) :
    subroutine_ok P entry (rustCliReallocNoOomSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hsp _
  have hpreB : s0.mem ⊨ (rustCliReallocNoOomSpecBase M A lim).pre (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [rustCliReallocNoOomSpec, rustCliReallocNoOomSpecBase] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1, hpre.1.2.2.2.2.1, hpre.1.2.2.2.2.2.1, hpre.1.2.2.2.2.2.2.1, hpre.1.2.2.2.2.2.2.2.1⟩, hpre.2⟩
  exact subroutine_ok.mono_outcome h (p, old, align, new, bs, st) R s0 hpc hrun hpreB hsp (fun _ hout => hout)

theorem RustCliAllocBudgetHooksBase.toPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (h : RustCliAllocBudgetHooksBase M A hooks) :
    RustCliAllocBudgetHooks M A hooks where
  alloc lim := hookSat_rustCliAllocBudget_of_base (h.alloc lim)
  dealloc lim := hookSat_rustCliDeallocBudget_of_base (h.dealloc lim)
  realloc lim := hookSat_rustCliReallocBudget_of_base (h.realloc lim)

theorem RustCliAllocBudgetEntriesBase.toPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M A P addrs) :
    RustCliAllocBudgetEntries M A P addrs where
  alloc lim := subroutine_ok_rustCliAllocBudget_of_base (h.alloc lim)
  dealloc lim := subroutine_ok_rustCliDeallocBudget_of_base (h.dealloc lim)
  realloc lim := subroutine_ok_rustCliReallocBudget_of_base (h.realloc lim)

theorem RustCliAllocNoOomEntriesBase.toPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocNoOomEntriesBase M A lim P addrs) :
    RustCliAllocNoOomEntries M A lim P addrs where
  alloc := subroutine_ok_rustCliAllocNoOom_of_base h.alloc
  dealloc := subroutine_ok_rustCliDeallocBudget_of_base h.dealloc
  realloc := subroutine_ok_rustCliReallocNoOom_of_base h.realloc

end LibsignalBinary.Heap
