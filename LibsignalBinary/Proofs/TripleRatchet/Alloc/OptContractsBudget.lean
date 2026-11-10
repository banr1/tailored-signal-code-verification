/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import Lean.Elab.Tactic -- shake: keep

/-!
# Stack- and Optional-Image-Parameterized Budget Allocator Contracts

Provides `VmPreserved`-strengthened `shimSpecWithStack` and `memcpySpecWithStack`, re-exports the
`*SpecWithStack` allocator contracts from `Alloc.DefsBudget` and `Heap.IfaceBudgetLemmas`, supplies
hook adapters for `AllocContractsBudget{,X}` and placed `HookSat` assumptions, and defines
`sepWP_optImage_rebase_vm` / `wp_steps_opt_sync_pool` for synchronizing `A.pool lim st` across
fixed-base `SepWP` instruction segments.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.InImageLift (OptCallInv)
open CryptoVerification.LibsignalTripleRatchet (
  SepWP.seq_optImage SepWPp.of_sepWP_optImage
  extHookStack specWithOptInv subroutine_ok_to_optNone
  subroutine_ok_withStack_of_subroutine_ok tripleRatchetProgAtExt withStack
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits NullAllowed RustCliAllocBudget VmPreserved
  not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetExternSpecWithStack rustCliAllocBudgetSpecWithStack
  rustCliAllocNoOomExternSpecWithStack rustCliAllocNoOomSpecWithStack
  rustCliDeallocBudgetExternSpecWithStack rustCliDeallocBudgetSpecWithStack
  rustCliDeallocNoOomExternSpecWithStack rustCliDeallocNoOomSpecWithStack
  rustCliReallocBudgetExternSpecWithStack rustCliReallocBudgetSpecWithStack
  rustCliReallocNoOomExternSpecWithStack rustCliReallocNoOomSpecWithStack
  subroutine_ok_rustCliAllocBudget_externWithStack subroutine_ok_rustCliAllocBudget_withStack
  subroutine_ok_rustCliAllocNoOom_externWithStack subroutine_ok_rustCliAllocNoOom_withStack
  subroutine_ok_rustCliDeallocBudget_externWithStack
  subroutine_ok_rustCliReallocBudget_externWithStack
  subroutine_ok_rustCliReallocNoOom_externWithStack subroutine_ok_rustCliReallocNoOom_withStack

  rustCliAllocBudgetExternSpecWithStackBase rustCliAllocBudgetSpecWithStackBase
  rustCliAllocNoOomExternSpecWithStackBase rustCliAllocNoOomSpecWithStackBase
  rustCliDeallocBudgetExternSpecWithStackBase rustCliDeallocBudgetSpecWithStackBase
  rustCliDeallocNoOomExternSpecWithStackBase rustCliDeallocNoOomSpecWithStackBase
  rustCliReallocBudgetExternSpecWithStackBase rustCliReallocBudgetSpecWithStackBase
  rustCliReallocNoOomExternSpecWithStackBase rustCliReallocNoOomSpecWithStackBase
  subroutine_ok_rustCliAllocBudget_externWithStackBase subroutine_ok_rustCliAllocBudget_withStackBase
  subroutine_ok_rustCliAllocNoOom_externWithStackBase subroutine_ok_rustCliAllocNoOom_withStackBase
  subroutine_ok_rustCliDeallocBudget_externWithStackBase
  subroutine_ok_rustCliReallocBudget_externWithStackBase
  subroutine_ok_rustCliReallocNoOom_externWithStackBase subroutine_ok_rustCliReallocNoOom_withStackBase
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  sepWP_rebase_vmPreserved trapHooks
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  AllocContractsBudget AllocContractsXBudget
  alloc_ok_at_norm_ext alloc_ok_at_norm_ext_x
  dealloc_ok_at_norm_ext dealloc_ok_at_norm_ext_x
  framelessMemcpyBudgetSpec memcpy_ok_at2_ext_x noAllocShimBudgetSpec
  realloc_ok_at_norm_ext realloc_ok_at_norm_ext_x
  shim_ok_at2_ext_x
)

/-! ## 1. `VmPreserved` Shim & `memcpy` Stack Contracts & Spec Re-Exports -/

/-- Stack-equipped `VmPreserved` no-op shim spec at `hookStack`
(`= session2ShimBudgetSpecX` at `extHookStack` by `rfl`). -/
def shimSpecWithStack (hookStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp hookStack

abbrev shimBudgetSpecWithStack := shimSpecWithStack

/-- Stack-equipped `VmPreserved` `memcpy` spec at `hookStack`
(`= session2MemcpyBudgetSpecX` at `extHookStack` by `rfl`). -/
def memcpySpecWithStack (hookStack : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ (dst ↦ₛ bs) ∗
      (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

abbrev memcpyBudgetSpecWithStack := memcpySpecWithStack

abbrev finishGrowSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack
abbrev finishGrowBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowBudgetSpecWithStack
abbrev doReserveRawSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack
abbrev doReserveRawBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawBudgetSpecWithStack
abbrev doReserveSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack
abbrev doReserveBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveBudgetSpecWithStack
abbrev intoBoxedSliceSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.intoBoxedSliceSpecWithStack
abbrev intoBoxedSliceBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.intoBoxedSliceBudgetSpecWithStack
abbrev tryCloneFromRefSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack
abbrev tryCloneFromRefBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefBudgetSpecWithStack
abbrev chainKeyToPbSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.chainKeyToPbSpecWithStack
abbrev chainKeyToPbBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.chainKeyToPbBudgetSpecWithStack
abbrev publicKeySerializeSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack
abbrev publicKeySerializeBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeBudgetSpecWithStack

abbrev rustAllocSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocBudgetSpecWithStack inst
abbrev rustAllocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocBudgetExternSpecWithStack inst
abbrev rustDeallocSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocBudgetSpecWithStack inst
abbrev rustDeallocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocBudgetExternSpecWithStack inst
abbrev rustReallocSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocBudgetSpecWithStack inst
abbrev rustReallocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocBudgetExternSpecWithStack inst

abbrev rustAllocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocNoOomSpecWithStack inst
abbrev rustAllocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocNoOomExternSpecWithStack inst
abbrev rustDeallocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocNoOomSpecWithStack inst
abbrev rustDeallocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocNoOomExternSpecWithStack inst
abbrev rustReallocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocNoOomSpecWithStack inst
abbrev rustReallocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocNoOomExternSpecWithStack inst

abbrev rustDeallocExternSpecWithStackBase := @rustCliDeallocBudgetExternSpecWithStackBase
abbrev rustAllocNoOomExternSpecWithStackBase := @rustCliAllocNoOomExternSpecWithStackBase
abbrev rustReallocNoOomExternSpecWithStackBase := @rustCliReallocNoOomExternSpecWithStackBase

/-! ## 2. Placed `noAllocShim` / `framelessMemcpy` Stack Adapters -/

theorem shimWithStack_of_noAllocShim {P : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok P addr noAllocShimBudgetSpec) :
    subroutine_ok P addr (shimSpecWithStack hookStack) := by
  have hw := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_mono hw (fun _ R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withStack, noAllocShimBudgetSpec, shimSpecWithStack] at hpre ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hpre

theorem shimWithStack_of_hookSat {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} (hookStack : Nat)
    (hsat : HookSat hooks hname noAllocShimBudgetSpec)
    (hext : prog.externAt? entry = hooks hname) :
    subroutine_ok prog entry (shimSpecWithStack hookStack) := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact shimWithStack_of_noAllocShim hookStack (subroutine_ok_of_hookOk (hext.trans hf) hok)

theorem memcpyWithStack_of_framelessMemcpy {P : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok P addr framelessMemcpyBudgetSpec) :
    subroutine_ok P addr (memcpySpecWithStack hookStack) := by
  have hw := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_mono hw (fun _ R s0 hpre => ?_) (fun _ R s0 sf hpost => ?_)
  · dsimp only [withStack, framelessMemcpyBudgetSpec, memcpySpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [withStack, framelessMemcpyBudgetSpec, memcpySpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem memcpyWithStack_of_hookSat {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} (hookStack : Nat)
    (hsat : HookSat hooks hname framelessMemcpyBudgetSpec)
    (hext : prog.externAt? entry = hooks hname) :
    subroutine_ok prog entry (memcpySpecWithStack hookStack) := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact memcpyWithStack_of_framelessMemcpy hookStack (subroutine_ok_of_hookOk (hext.trans hf) hok)

/-! ## 3. `.inImage` `Budget → NoOom` Lifts for `AllocContractsXBudget` -/

theorem allocNoOomWithStack_inImage_of_budget {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr ((rustCliAllocBudgetSpecWithStackBase M A lim zeroed stk).inImage img)) :
    subroutine_ok P addr ((rustCliAllocNoOomSpecWithStackBase M A lim zeroed stk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨size, align, st⟩ R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage, rustCliAllocNoOomSpecWithStackBase] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre_rest⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_rest
  rcases hpre_rest with ⟨⟨hx0, hx1, hlay, hfit⟩, hmem⟩
  have hpre' : s0.mem ⊨
      ((rustCliAllocBudgetSpecWithStackBase M A lim zeroed stk).inImage img).pre
        (size, align, st) s0 ∗ R := by
    dsimp only [Spec.inImage, rustCliAllocBudgetSpecWithStackBase]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, hmem⟩
  refine h.mono_outcome (size, align, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, rustCliAllocBudgetSpecWithStackBase,
      rustCliAllocNoOomSpecWithStackBase] at hpost ⊢
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte] at hpost
      have hnull_abs : sf.mem ⊨ ⌜NullAllowed size align⌝ ∗
          (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗ stackAt s0.sp stk ∗ R) := by
        ac_nf at hpost ⊢
      rw [satisfies_pure_sepConj] at hnull_abs
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hfit hnull_abs.1)
    · simp only [h0, ↓reduceIte] at hpost
      have hpost' : sf.mem ⊨ ⌜AllocCallPreserved s0 sf⌝ ∗
          (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size) ∗ R)) := by
        ac_nf at hpost ⊢
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hpost'.1, h0, hpost'.2.1⟩, ?_⟩
      simpa only [sepConj_assoc] using hpost'.2.2
  · dsimp only [Spec.inImage, rustCliAllocBudgetSpecWithStackBase] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [Spec.inImage, rustCliAllocBudgetSpecWithStackBase] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [Spec.inImage, rustCliAllocBudgetSpecWithStackBase] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfit)

theorem allocNoOomExternWithStack_inImage_of_budget {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr ((rustCliAllocBudgetSpecWithStackBase M A lim zeroed stk).inImage img)) :
    subroutine_ok P addr ((rustCliAllocNoOomExternSpecWithStackBase M A lim zeroed stk).inImage img) := by
  have hno := allocNoOomWithStack_inImage_of_budget h
  refine subroutine_ok_mono hno (fun _ _ _ hpre => hpre) (fun ⟨size, align, st⟩ R s0 sf hpost => ?_)
  dsimp only [Spec.inImage, rustCliAllocNoOomSpecWithStackBase,
    rustCliAllocNoOomExternSpecWithStackBase,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStackBase] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1.2.1, hpost.1.2.1, hpost.1.2.2⟩, hpost.2⟩

theorem reallocNoOomExternWithStack_inImage_of_budget {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr ((rustCliReallocBudgetExternSpecWithStackBase M A lim stk).inImage img)) :
    subroutine_ok P addr ((rustCliReallocNoOomExternSpecWithStackBase M A lim stk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage, rustCliReallocNoOomExternSpecWithStackBase,
    LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStackBase] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre_rest⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_rest
  rcases hpre_rest with ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hblo, hbln, hfit⟩, hmem⟩
  have hpre' : s0.mem ⊨
      ((rustCliReallocBudgetExternSpecWithStackBase M A lim stk).inImage img).pre
        (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [Spec.inImage, rustCliReallocBudgetExternSpecWithStackBase,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hblo, hbln⟩, hmem⟩
  refine h.mono_outcome (p, old, align, new, bs, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, rustCliReallocBudgetExternSpecWithStackBase,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase,
      rustCliReallocNoOomExternSpecWithStackBase,
      LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStackBase] at hpost ⊢
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte] at hpost
      have hnull_abs : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ NullAllowed new align⌝ ∗
          (A.pool lim st sf ∗ stackAt s0.sp stk ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R) := by
        ac_nf at hpost ⊢
      rw [satisfies_pure_sepConj] at hnull_abs
      exact False.elim (not_nullAllowed_of_fitsReallocEvents hnew hfit hnull_abs.1.2)
    · simp only [h0, ↓reduceIte] at hpost
      have hpost' : sf.mem ⊨ ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) new align ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R) := by
        ac_nf at hpost ⊢
      rw [satisfies_pure_sepConj] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hpost'.1.2, h0, hpost'.1.1⟩, ?_⟩
      simpa only [sepConj_assoc] using hpost'.2
  · dsimp only [Spec.inImage, rustCliReallocBudgetExternSpecWithStackBase,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [Spec.inImage, rustCliReallocBudgetExternSpecWithStackBase,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [Spec.inImage, rustCliReallocBudgetExternSpecWithStackBase,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfit)

/-! ## 4. Individual Hook Adapters (`oimg = none` from `AllocContractsBudget`, `oimg = some img` from `AllocContractsXBudget`) -/

theorem shim_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (shimSpecWithStack allocHookStack)) := by
  apply subroutine_ok_to_optNone
  exact shimWithStack_of_noAllocShim allocHookStack (hA.shim_ok_at name k hk)

theorem shim_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (shimSpecWithStack extHookStack)) :=
  shim_ok_at2_ext_x hA hk

theorem memcpy_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (memcpySpecWithStack allocHookStack)) := by
  apply subroutine_ok_to_optNone
  exact memcpyWithStack_of_framelessMemcpy allocHookStack
    (hA.session_memcpy_region_ok_at name k hk)

theorem memcpy_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (memcpySpecWithStack extHookStack)) :=
  memcpy_ok_at2_ext_x hA hk

theorem alloc_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustCliAllocBudgetSpecWithStackBase M A lim false allocHookStack)) :=
  subroutine_ok_to_optNone
    (subroutine_ok_rustCliAllocBudget_withStackBase (by decide) (by decide) (alloc_ok_at_norm_ext hA hk))

theorem alloc_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustCliAllocBudgetSpecWithStackBase M A lim false extHookStack)) :=
  alloc_ok_at_norm_ext_x hA hk

theorem allocNoOom_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustCliAllocNoOomSpecWithStackBase M A lim false allocHookStack)) :=
  subroutine_ok_to_optNone
    (subroutine_ok_rustCliAllocNoOom_withStackBase (by decide) (by decide) (hA.allocNoOom_ok_at name k hk))

theorem allocNoOom_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustCliAllocNoOomSpecWithStackBase M A lim false extHookStack)) :=
  allocNoOomWithStack_inImage_of_budget (alloc_ok_at_norm_ext_x hA hk)

theorem allocNoOomExtern_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustCliAllocNoOomExternSpecWithStackBase M A lim false allocHookStack)) :=
  subroutine_ok_to_optNone
    (subroutine_ok_rustCliAllocNoOom_externWithStackBase (by decide) (by decide)
      (hA.allocNoOom_ok_at name k hk))

theorem allocNoOomExtern_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustCliAllocNoOomExternSpecWithStackBase M A lim false extHookStack)) :=
  allocNoOomExternWithStack_inImage_of_budget (alloc_ok_at_norm_ext_x hA hk)

theorem dealloc_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustCliDeallocBudgetExternSpecWithStackBase M A lim allocHookStack)) :=
  subroutine_ok_to_optNone
    (subroutine_ok_rustCliDeallocBudget_externWithStackBase (by decide) (by decide)
      (dealloc_ok_at_norm_ext hA hk))

theorem dealloc_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustCliDeallocBudgetExternSpecWithStackBase M A lim extHookStack)) :=
  dealloc_ok_at_norm_ext_x hA hk

theorem realloc_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustCliReallocBudgetExternSpecWithStackBase M A lim allocHookStack)) :=
  subroutine_ok_to_optNone
    (subroutine_ok_rustCliReallocBudget_externWithStackBase (by decide) (by decide)
      (realloc_ok_at_norm_ext hA hk))

theorem realloc_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustCliReallocBudgetExternSpecWithStackBase M A lim extHookStack)) :=
  realloc_ok_at_norm_ext_x hA hk

theorem reallocNoOom_opt_of_base {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustCliReallocNoOomExternSpecWithStackBase M A lim allocHookStack)) :=
  subroutine_ok_to_optNone
    (subroutine_ok_rustCliReallocNoOom_externWithStackBase (by decide) (by decide)
      (hA.reallocNoOom_ok_at name k hk))

theorem reallocNoOom_opt_of_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustCliReallocNoOomExternSpecWithStackBase M A lim extHookStack)) :=
  reallocNoOomExternWithStack_inImage_of_budget (realloc_ok_at_norm_ext_x hA hk)

/-! ## 5. Fixed-Base Segment `VmPreserved` / `OptCallInv` Pool Synchronization -/

/-- `(P.rebase b trapHooks).fnAddr name` agrees with `(P.rebase b Hk).fnAddr name` without
requiring callers with `local irreducible Program.fetch` to unfold `fnOff`. -/
theorem rebase_trapHooks_fnAddr (P : Program) (b : BitVec 64)
    (Hk : String → Option (State → State)) (name : String) :
    (P.rebase b trapHooks).fnAddr name = (P.rebase b Hk).fnAddr name :=
  rfl

/-- Thread both `OptCallInv oimg` and `VmPreserved s sm` across a pure CPU instruction segment
of `P.rebase b Hk` up to `mid`, enabling `SepWP.transport_budgetPool` after `stp`/`str` writes. -/
theorem sepWP_optImage_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {oimg : Option Obj.Image}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} (hinv : OptCallInv oimg s)
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (OptCallInv oimg sm → VmPreserved s sm →
          SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post := by
  refine SepWP.seq_optImage (mid := mid) hinv ?_
  exact ProofLib.SepWP.mono (sepWP_rebase_vmPreserved (Hk := Hk) hseg)
    fun _ _ _ _ ⟨hvm, hnext⟩ hinv' => hnext hinv' hvm

/-- `SepWPp` counterpart of `sepWP_optImage_rebase_vm`. -/
theorem sepWPp_optImage_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {oimg : Option Obj.Image}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} (hinv : OptCallInv oimg s)
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (OptCallInv oimg sm → VmPreserved s sm →
          SepWPp (P.rebase b Hk) ret sm Pm Q Qp))) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp := by
  refine SepWPp.of_sepWP_optImage (mid := mid) hinv ?_
  exact ProofLib.SepWP.mono (sepWP_rebase_vmPreserved (Hk := Hk) hseg)
    fun _ _ _ _ ⟨hvm, hnext⟩ hinv' => hnext hinv' hvm

public meta section

open Lean Meta Elab Tactic Arm64 ProofLib in
/-- Step CPU instructions of `P.rebase b Hk` up to `mid` under `hinv : OptCallInv oimg s`,
introducing `(hinv_next : OptCallInv oimg sm)` and `(hvm_next : VmPreserved s sm)` and
synchronizing `A.pool lim st s` to `A.pool lim st sm` in the continuation `SepWP` or `SepWPp` goal.
Pair with `code_fetches ... trapHooks ...` so fetch hypotheses match `P.rebase b trapHooks`. -/
elab "wp_steps_opt_sync_pool " mid:term:max hinv:term:max : tactic => do
  let g0 ← getMainGoal
  let isWpp ← g0.withContext do
    let ty0 := (← instantiateMVars (← g0.getType)).consumeMData
    let ty ← if ty0.isAppOfArity ``SepWP 6 || ty0.isAppOfArity ``SepWPp 7 then pure ty0
      else withReducible (whnf ty0)
    if ty.isAppOfArity ``SepWP 6 then pure false
    else if ty.isAppOfArity ``SepWPp 7 then pure true
    else throwError "wp_steps_opt_sync_pool: expected SepWP or SepWPp goal, got{indentExpr ty0}"
  if isWpp then
    evalTactic (← `(tactic|
      apply LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget.sepWPp_optImage_rebase_vm
        (mid := $mid) $hinv))
  else
    evalTactic (← `(tactic|
      apply LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget.sepWP_optImage_rebase_vm
        (mid := $mid) $hinv))
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
      throwError "wp_steps_opt_sync_pool: expected SepWP on withSvc, got{indentExpr ty}"
    let e2 := ty.getArg! 0
    unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
      throwError "wp_steps_opt_sync_pool: expected Program.withSvc, got{indentExpr e2}"
    let e1 := e2.getArg! 0
    let ty1 := mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← mkFreshExprMVar ty1
    let savedGoals ← getGoals
    setGoals [g1.mvarId!]
    evalTactic (← `(tactic| (
      wp_steps
      refine ProofLib.SepWP.done
        (by first | rfl | wp_norm_lhs | simp only [wp_norm, arm64_norm])
        (by first | assumption | wp_norm_lhs)
        ⟨by first | rfl | simp only [wp_norm, arm64_norm], fun hinv_next hvm_next => ?_⟩
    )))
    let rem ← getGoals
    let prf1 ← instantiateMVars g1
    let prf2 := prf1.replace fun sub => if sub.eqv e1 then some e2 else none
    g.assign prf2
    setGoals (rem ++ savedGoals.tail!)
    if isWpp then
      evalTactic (← `(tactic| (
        try first
          | refine ProofLib.SepWPp.transport_budgetPool hvm_next (hnext := ?_)
          | refine ProofLib.SepWPp.transport_atStatePool hvm_next (hnext := ?_)
      )))
    else
      evalTactic (← `(tactic| (
        try first
          | refine ProofLib.SepWP.transport_budgetPool hvm_next (hnext := ?_)
          | refine ProofLib.SepWP.transport_atStatePool hvm_next (hnext := ?_)
      )))

end

end LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
