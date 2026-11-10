/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs

/-!
# Budget-Threaded `HashbrownBin` Hook Contracts

`VmPreserved` and `RustCliAllocBudget M` hook contracts (`e2eBcmpSpec`, `randomKeysSpec`,
`rustAllocNWSpec`, `rustAllocNoOomNWSpec`, `stringCloneSpec`, `HashbrownBinHooks`) for compiled
`hashbrown` proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.E2E.InMem.HashbrownBin
  (HookMap BcmpCall bcmpName randomKeysName stringCloneHookName stringCloneName
   fallibilityAllocErrName)
open LibsignalBinary.Heap
  (VmPreserved AllocCallPreserved NullAllowed RustLayoutOk AllocCostModel BudgetLimits
   RustCliAllocBudget FitsEvents rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (withVmPreserved AllocHooksBudget)

/-- Budget-compatible `bcmp` contract (`VmPreserved`-carrying `Defs.e2eBcmpSpec`, 0 allocations). -/
def e2eBcmpSpec : Spec BcmpCall :=
  withVmPreserved CryptoVerification.E2E.InMem.HashbrownBin.e2eBcmpSpec

/-- Budget-compatible `hashmap_random_keys` contract (`VmPreserved`-carrying `Defs.randomKeysSpec`,
    0 allocations). -/
def randomKeysSpec : Spec Unit :=
  withVmPreserved CryptoVerification.E2E.InMem.HashbrownBin.randomKeysSpec

/-- Conditional-OOM budget-threaded `__rust_alloc(size = x0, align = x1)` contract strengthening
    `rustCliAllocBudgetSpec M A lim false` with `(sf.readReg64 .x0).toNat + size < 2 ^ 64` on
    non-null return. -/
def rustAllocNWSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) where
  pre := (rustCliAllocBudgetSpec M A lim false).pre
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧
         (sf.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)
  onOom := (rustCliAllocBudgetSpec M A lim false).onOom

/-- Total-correctness (`FitsEvents`) `__rust_alloc` contract with non-wrapping upper bound
    `(sf.readReg64 .x0).toNat + size < 2 ^ 64`. -/
def rustAllocNoOomNWSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) where
  pre := (rustCliAllocNoOomSpec M A lim false).pre
  post := fun (size, align, st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0 ∧
      (sf.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size
  onOom := fun _ _ _ => ⌜False⌝

theorem hookOk_rustAllocSpec_of_NW [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {f : Arm64.State → Arm64.State}
    (h : HookOk f (rustAllocNWSpec M A lim)) :
    HookOk f (rustCliAllocBudgetSpec M A lim false) := by
  intro (size, align, st) R s0 hrun hpre hsp
  obtain ⟨hkf, hsp_eq, Out⟩ := h (size, align, st) R s0 hrun hpre hsp
  refine ⟨hkf, hsp_eq, ?_⟩
  rcases Out with ⟨hret, hregs, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hregs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [rustAllocNWSpec, rustCliAllocBudgetSpec]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
    split
    · exact Entails.refl _
    · exact Entails.pure_left fun ⟨hal, _⟩ => Entails.pure_right hal (Entails.refl _)
  · exact Or.inr hrest

theorem hookSat_rustAllocSpec_of_NW [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : HookMap} {name : String}
    (h : HookSat ext name (rustAllocNWSpec M A lim)) :
    HookSat ext name (rustCliAllocBudgetSpec M A lim false) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_rustAllocSpec_of_NW hok⟩

abbrev stringCloneSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :=
  stringCloneBudgetSpec M A lim

/-- Budget-threaded external hook bundle for `HashbrownBin`. -/
structure HashbrownBinHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (Arm64.State → Arm64.State)) : Prop where
  alloc : AllocHooksBudget M A lim ext
  allocNW : HookSat ext "__rustc::__rust_alloc" (rustAllocNWSpec M A lim)
  bcmp : HookSat ext bcmpName e2eBcmpSpec
  randomKeys : HookSat ext randomKeysName randomKeysSpec
  stringClone : HookSat ext stringCloneHookName (stringCloneSpec M A lim)
  shim : ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" = some hookNoop
  memset : ext "memset" = some hookMemset
  memcpy : ext "memcpy" = some hookMemcpy
  blackBox : ext "subtle::black_box::<u8>" = some blackBoxHook
  fallibilityAllocErr : ext fallibilityAllocErrName = some Rust.panicked
  rawVecHandleError : ext "alloc::raw_vec::handle_error" = some Rust.panicked
  panicAsyncFnResumed : ext "core::panicking::panic_const::panic_const_async_fn_resumed" =
    some Rust.panicked

theorem HashbrownBinHooks.alloc_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : HookMap}
    (h : HashbrownBinHooks M A lim ext) :
    HookSat ext "__rustc::__rust_alloc" (rustCliAllocBudgetSpec M A lim false) :=
  hookSat_rustAllocSpec_of_NW h.allocNW

end LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget
