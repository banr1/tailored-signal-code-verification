/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat

/-!
# `HookSat` Sibling of `HashbrownBin.DefsBudget` (`DefsBudgetSat`)

Provides `HashbrownBinHooksSat`, replacing `ext "memset" = some hookMemset` in
`HashbrownBinHooks` (`DefsBudget.lean:118`) with
`HookSat ext "memset" sessionMemsetRegionBudgetSpec`, together with `HashbrownBinHooks.toSat`
and `HashbrownBinHooksSat.alloc_sat`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudgetSat

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E.InMem.HashbrownBin
  (HookMap bcmpName fallibilityAllocErrName randomKeysName stringCloneHookName)
open CryptoVerification.LibsignalSession (blackBoxHook)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (hookSat_hookMemset_budget_of_eq)
open LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget
  (HashbrownBinHooks e2eBcmpSpec hookSat_rustAllocSpec_of_NW randomKeysSpec
   rustAllocNWSpec stringCloneSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

/-- `HookSat`-parameterized sibling of `HashbrownBinHooks`: replaces
`ext "memset" = some hookMemset` with `HookSat ext "memset" sessionMemsetRegionBudgetSpec`. -/
structure HashbrownBinHooksSat [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (Arm64.State → Arm64.State)) : Prop where
  alloc : AllocHooksBudget M A lim ext
  allocNW : HookSat ext "__rustc::__rust_alloc" (rustAllocNWSpec M A lim)
  bcmp : HookSat ext bcmpName e2eBcmpSpec
  randomKeys : HookSat ext randomKeysName randomKeysSpec
  stringClone : HookSat ext stringCloneHookName (stringCloneSpec M A lim)
  shim : ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" = some hookNoop
  memset : HookSat ext "memset" sessionMemsetRegionBudgetSpec
  memcpy : ext "memcpy" = some hookMemcpy
  blackBox : ext "subtle::black_box::<u8>" = some blackBoxHook
  fallibilityAllocErr : ext fallibilityAllocErrName = some Rust.panicked
  rawVecHandleError : ext "alloc::raw_vec::handle_error" = some Rust.panicked
  panicAsyncFnResumed : ext "core::panicking::panic_const::panic_const_async_fn_resumed" =
    some Rust.panicked

/-- Coerce `HashbrownBinHooks` into `HashbrownBinHooksSat` via `hookSat_hookMemset_budget_of_eq`. -/
theorem HashbrownBinHooks.toSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : HookMap}
    (h : HashbrownBinHooks M A lim ext) :
    HashbrownBinHooksSat M A lim ext where
  alloc := h.alloc
  allocNW := h.allocNW
  bcmp := h.bcmp
  randomKeys := h.randomKeys
  stringClone := h.stringClone
  shim := h.shim
  memset := hookSat_hookMemset_budget_of_eq (H := ext) h.memset
  memcpy := h.memcpy
  blackBox := h.blackBox
  fallibilityAllocErr := h.fallibilityAllocErr
  rawVecHandleError := h.rawVecHandleError
  panicAsyncFnResumed := h.panicAsyncFnResumed

/-- `HookSat`-sibling of `HashbrownBinHooks.alloc_sat`. -/
theorem HashbrownBinHooksSat.alloc_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : HookMap}
    (h : HashbrownBinHooksSat M A lim ext) :
    HookSat ext "__rustc::__rust_alloc" (rustCliAllocBudgetSpec M A lim false) :=
  hookSat_rustAllocSpec_of_NW h.allocNW

end LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudgetSat
