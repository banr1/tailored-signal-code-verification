/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.HooksE.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded External Hook Contract Bundles

`RustCliAllocBudget`-threaded and `VmPreserved`-preserving `[LibsignalPlacement]` hook contract
bundles: conditional-OOM `Stage2ContractsPlaced` and total-correctness (`FitsEvents`)
`Stage2NoOomContractsPlaced`, plus `rustDeallocLayoutBudgetSpec'` and `rustAllocNoOomNW` bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
  lsρ lsRustAllocSym lsRustDeallocSym lsRustReallocSym lsRustNoAllocShimSym lsHandleErrorSym
)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionShimSpec sessionMemcpySpec sessionMemcpyROXSpec
  sessionMemmoveSpec sessionMemsetSpec
  ls_hook_ok_of_caller ls_subroutine_ok_cl_of_plain_prog ls_subroutine_ok_cl_of_callee
)
open Proofs.libsignal.Hooks2 (
  subroutine_ok_withExternStackFromAlloc' subroutine_ok_withLsCl_map'
  subroutine_ok_withLsCl_withHookStack_mono
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits NullAllowed RustCliAllocBudget RustLayoutOk
  not_nullAllowed_of_fitsAllocEvents rustAllocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  rustCliAllocNoOomSpec rustCliReallocNoOomSpec
  subroutine_ok_allocNoOom_of_budget subroutine_ok_reallocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceLemmas (
  withExternStackFromAllocOom' subroutine_ok_withExternStackFromAllocOom'
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.HooksE.CommonBudget (
  rustAllocNWSpec rustAllocNoOomNWSpec e2eBcmpSpec
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (AllocContractsXPlaced)

/-! ## 1. Budget-Threaded `rustDeallocLayoutSpec'` & `rustAllocNoOomNWSpec` Helpers -/

/-- `rustCliDeallocBudgetSpec M A lim` with the `RustLayoutOk size align` precondition required by
`Externs.deallocSpec`. -/
def rustDeallocLayoutBudgetSpec' [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜RustLayoutOk size align⌝ ∗ (rustCliDeallocBudgetSpec M A lim).pre (p, size, align, st) s
  post := (rustCliDeallocBudgetSpec M A lim).post

abbrev rustDeallocLayoutSpec' := @rustDeallocLayoutBudgetSpec'

theorem subroutine_ok_rustDeallocLayoutBudgetSpec'_of_rustCliDeallocBudgetSpec [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (rustDeallocLayoutBudgetSpec' M A lim) := by
  refine subroutine_ok_map h (fun ⟨p, sz, al, st⟩ R s0 hpre => ?_)
  dsimp only [rustDeallocLayoutBudgetSpec'] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨(p, sz, al, st), R, hpre.2, fun _ hp => hp⟩

/-- Specialize conditional-OOM `rustAllocNWSpec M A lim` to total-correctness
`rustAllocNoOomNWSpec M A lim` under `FitsEvents`. -/
theorem subroutine_ok_rustAllocNoOomNW_of_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustAllocNWSpec M A lim)) :
    subroutine_ok P entry (rustAllocNoOomNWSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustAllocNoOomNWSpec, LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget.rustAllocNoOomNWSpec,
    rustCliAllocNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay, hFit, hlr⟩, hrest⟩
  have hpreB : s0.mem ⊨ (rustAllocNWSpec M A lim).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustAllocNWSpec, LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget.rustAllocNWSpec,
      rustCliAllocBudgetSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hlr⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpreB hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocNWSpec,
      LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget.rustAllocNWSpec] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hna : NullAllowed size align := by
        have hEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
              stackAt s0.sp allocHookStack ∗ ⌜NullAllowed size align⌝) ∗ R =
            ⌜NullAllowed size align⌝ ∗
              (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
                stackAt s0.sp allocHookStack ∗ R) := by sep_ac_rfl
        rw [hEq, satisfies_pure_sepConj] at hpost
        exact hpost.1
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hFit hna)
    · simp only [hnull, ↓reduceIte] at hpost
      dsimp only [rustAllocNoOomNWSpec,
        LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget.rustAllocNoOomNWSpec]
      have hEq1 :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0 ∧
                (sf.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
              A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0 ∧
                (sf.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
              (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
                stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
                memRegion (sf.readReg64 .x0) size ∗ R)) := by sep_ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨⟨hal, hnw⟩, hspRest⟩
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := hnull
      have hEq2 :
          (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0 ∧
              (sf.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
            memRegion (sf.readReg64 .x0) size) ∗ R =
          ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0 ∧
              (sf.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size ∗ R) := by sep_ac_rfl
      rw [hEq2, satisfies_pure_sepConj]
      exact ⟨⟨hacp, hne0, hal, hnw⟩, hspRest⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [rustAllocNWSpec,
      LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget.rustAllocNWSpec,
      rustCliAllocBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hFit)

/-! ## 2. Conditional-OOM `Stage2ContractsPlaced` Bundle -/

set_option maxRecDepth 2000000

/-- Conditional-OOM budget-threaded `[LibsignalPlacement]` counterpart of
`Stage2ContractsA0Placed` (`externStack = 16384`). -/
structure Stage2ContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpec M A lim false).withExternStackFromAllocOom')
  allocNW : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocNWSpec M A lim).withExternStackFromAllocOom')
  deallocLayout : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustDeallocLayoutBudgetSpec' M A lim).withExternStackFromAllocOom')
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustCliReallocBudgetSpec M A lim).withExternStackFromAllocOom')
  shim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl ((withVmPreserved sessionShimSpec).withHookStack extHookStack))
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack)))
  memcpyROX : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (withVmPreserved sessionMemcpyROXSpec))
  memmove : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memmove")
      (withLsCl lsmpl (withVmPreserved (sessionMemmoveSpec extHookStack)))
  memset : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memset")
      (withLsCl lsmpl (withVmPreserved (sessionMemsetSpec extHookStack)))
  bcmp : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "bcmp")
      (withLsCl lsmpl e2eBcmpSpec)
  panic_handle_error : H lsHandleErrorSym = some Rust.panicked
  panic_handle_alloc_error :
    H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked

theorem Stage2ContractsPlaced.shim_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsPlaced A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (withVmPreserved (sessionShimSpec.withHookStack extHookStack))) := by
  refine subroutine_ok_withLsCl_map' hC.shim fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩
  dsimp only [Spec.withHookStack, withVmPreserved] at hpost ⊢
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem Stage2ContractsPlaced.of_block0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustCliAllocBudgetSpec M A lim false).withExternStackFromAllocOom'))
    (hallocNW : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustAllocNWSpec M A lim).withExternStackFromAllocOom'))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustDeallocLayoutBudgetSpec' M A lim).withExternStackFromAllocOom'))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustCliReallocBudgetSpec M A lim).withExternStackFromAllocOom'))
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl ((withVmPreserved sessionShimSpec).withHookStack extHookStack)))
    (hmemcpy : subroutine_ok blk0Prog (lsρ "memcpy")
      (withLsCodeLoaded lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    (hmemcpyROX : subroutine_ok blk0Prog (lsρ "memcpy")
      (withLsCodeLoaded lsmpl (withVmPreserved sessionMemcpyROXSpec)))
    (hmemmove : subroutine_ok blk0Prog (lsρ "memmove")
      (withLsCodeLoaded lsmpl (withVmPreserved (sessionMemmoveSpec extHookStack))))
    (hmemset : subroutine_ok blk0Prog (lsρ "memset")
      (withLsCodeLoaded lsmpl (withVmPreserved (sessionMemsetSpec extHookStack))))
    (hbcmp : subroutine_ok blk0Prog (lsρ "bcmp")
      (withLsCodeLoaded lsmpl e2eBcmpSpec))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2ContractsPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_callee (j := 0) halloc
  allocNW := ls_subroutine_ok_cl_of_callee (j := 0) hallocNW
  deallocLayout := ls_subroutine_ok_cl_of_callee (j := 0) hdealloc
  realloc := ls_subroutine_ok_cl_of_callee (j := 0) hrealloc
  shim := ls_subroutine_ok_cl_of_callee (j := 0) hshim
  memcpy := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpy
  memcpyROX := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpyROX
  memmove := ls_subroutine_ok_cl_of_callee (j := 0) hmemmove
  memset := ls_subroutine_ok_cl_of_callee (j := 0) hmemset
  bcmp := ls_subroutine_ok_cl_of_callee (j := 0) hbcmp
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

theorem Stage2ContractsPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocNW : HookSat H lsRustAllocSym (rustAllocNWSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved sessionShimSpec))
    (hmemcpy : HookSat H "memcpy" (withVmPreserved (sessionMemcpySpec extHookStack)))
    (hmemcpyROX : HookSat H "memcpy" (withVmPreserved sessionMemcpyROXSpec))
    (hmemmove : HookSat H "memmove" (withVmPreserved (sessionMemmoveSpec extHookStack)))
    (hmemset : HookSat H "memset" (withVmPreserved (sessionMemsetSpec extHookStack)))
    (hbcmp : HookSat H "bcmp" e2eBcmpSpec)
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2ContractsPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAllocOom' (ls_hook_ok_of_caller halloc))
  allocNW := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAllocOom' (ls_hook_ok_of_caller hallocNW))
  deallocLayout := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAllocOom'
      (subroutine_ok_rustDeallocLayoutBudgetSpec'_of_rustCliDeallocBudgetSpec
        (ls_hook_ok_of_caller hdealloc)))
  realloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAllocOom' (ls_hook_ok_of_caller hrealloc))
  shim := fun {callerProg callerBlk _} => by
    have h0 : subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
        (withLsCl lsmpl ((withVmPreserved sessionShimSpec).withHookStack 0)) := by
      refine subroutine_ok_withLsCl_map'
        (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hshim))
        fun x R s0 hpre => ⟨x, stackAt s0.sp 0 ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [Spec.withHookStack] at hpre
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      · dsimp only [Spec.withHookStack]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    exact subroutine_ok_withLsCl_withHookStack_mono (by decide) (by decide) h0
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)
  memcpyROX := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpyROX)
  memmove := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemmove)
  memset := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemset)
  bcmp := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hbcmp)
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

/-! ## 3. Total-Correctness (`NoOom`) `Stage2NoOomContractsPlaced` Bundle -/

/-- Total-correctness (`NoOom` under `FitsEvents`) `[LibsignalPlacement]` counterpart of
`Stage2ContractsA0Placed` (`externStack = 16384`). -/
structure Stage2NoOomContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpec M A lim false).withExternStackFromAlloc')
  allocNW : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocNoOomNWSpec M A lim).withExternStackFromAlloc')
  deallocLayout : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustDeallocLayoutBudgetSpec' M A lim).withExternStackFromAlloc')
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustCliReallocNoOomSpec M A lim).withExternStackFromAlloc')
  shim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl ((withVmPreserved sessionShimSpec).withHookStack extHookStack))
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack)))
  memcpyROX : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (withVmPreserved sessionMemcpyROXSpec))
  memmove : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memmove")
      (withLsCl lsmpl (withVmPreserved (sessionMemmoveSpec extHookStack)))
  memset : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memset")
      (withLsCl lsmpl (withVmPreserved (sessionMemsetSpec extHookStack)))
  bcmp : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "bcmp")
      (withLsCl lsmpl e2eBcmpSpec)
  panic_handle_error : H lsHandleErrorSym = some Rust.panicked
  panic_handle_alloc_error :
    H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked

theorem Stage2NoOomContractsPlaced.shim_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2NoOomContractsPlaced A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (withVmPreserved (sessionShimSpec.withHookStack extHookStack))) := by
  refine subroutine_ok_withLsCl_map' hC.shim fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩
  dsimp only [Spec.withHookStack, withVmPreserved] at hpost ⊢
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem Stage2NoOomContractsPlaced.of_block0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustCliAllocNoOomSpec M A lim false).withExternStackFromAlloc'))
    (hallocNW : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustAllocNoOomNWSpec M A lim).withExternStackFromAlloc'))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustDeallocLayoutBudgetSpec' M A lim).withExternStackFromAlloc'))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustCliReallocNoOomSpec M A lim).withExternStackFromAlloc'))
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl ((withVmPreserved sessionShimSpec).withHookStack extHookStack)))
    (hmemcpy : subroutine_ok blk0Prog (lsρ "memcpy")
      (withLsCodeLoaded lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    (hmemcpyROX : subroutine_ok blk0Prog (lsρ "memcpy")
      (withLsCodeLoaded lsmpl (withVmPreserved sessionMemcpyROXSpec)))
    (hmemmove : subroutine_ok blk0Prog (lsρ "memmove")
      (withLsCodeLoaded lsmpl (withVmPreserved (sessionMemmoveSpec extHookStack))))
    (hmemset : subroutine_ok blk0Prog (lsρ "memset")
      (withLsCodeLoaded lsmpl (withVmPreserved (sessionMemsetSpec extHookStack))))
    (hbcmp : subroutine_ok blk0Prog (lsρ "bcmp")
      (withLsCodeLoaded lsmpl e2eBcmpSpec))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2NoOomContractsPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_callee (j := 0) halloc
  allocNW := ls_subroutine_ok_cl_of_callee (j := 0) hallocNW
  deallocLayout := ls_subroutine_ok_cl_of_callee (j := 0) hdealloc
  realloc := ls_subroutine_ok_cl_of_callee (j := 0) hrealloc
  shim := ls_subroutine_ok_cl_of_callee (j := 0) hshim
  memcpy := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpy
  memcpyROX := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpyROX
  memmove := ls_subroutine_ok_cl_of_callee (j := 0) hmemmove
  memset := ls_subroutine_ok_cl_of_callee (j := 0) hmemset
  bcmp := ls_subroutine_ok_cl_of_callee (j := 0) hbcmp
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

theorem Stage2NoOomContractsPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocNW : HookSat H lsRustAllocSym (rustAllocNWSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved sessionShimSpec))
    (hmemcpy : HookSat H "memcpy" (withVmPreserved (sessionMemcpySpec extHookStack)))
    (hmemcpyROX : HookSat H "memcpy" (withVmPreserved sessionMemcpyROXSpec))
    (hmemmove : HookSat H "memmove" (withVmPreserved (sessionMemmoveSpec extHookStack)))
    (hmemset : HookSat H "memset" (withVmPreserved (sessionMemsetSpec extHookStack)))
    (hbcmp : HookSat H "bcmp" e2eBcmpSpec)
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2NoOomContractsPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc'
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_caller halloc)))
  allocNW := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc'
      (subroutine_ok_rustAllocNoOomNW_of_budget (ls_hook_ok_of_caller hallocNW)))
  deallocLayout := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc'
      (subroutine_ok_rustDeallocLayoutBudgetSpec'_of_rustCliDeallocBudgetSpec
        (ls_hook_ok_of_caller hdealloc)))
  realloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc'
      (subroutine_ok_reallocNoOom_of_budget (ls_hook_ok_of_caller hrealloc)))
  shim := fun {callerProg callerBlk _} => by
    have h0 : subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
        (withLsCl lsmpl ((withVmPreserved sessionShimSpec).withHookStack 0)) := by
      refine subroutine_ok_withLsCl_map'
        (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hshim))
        fun x R s0 hpre => ⟨x, stackAt s0.sp 0 ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [Spec.withHookStack] at hpre
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      · dsimp only [Spec.withHookStack]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    exact subroutine_ok_withLsCl_withHookStack_mono (by decide) (by decide) h0
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)
  memcpyROX := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpyROX)
  memmove := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemmove)
  memset := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemset)
  bcmp := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hbcmp)
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget
