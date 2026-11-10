/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `HookSat` Sibling of `AllocFsA1PlacedBudget` (`AllocFsA1PlacedBudgetSat`)

Replaces `(hmemset : H memsetName = some hookMemset)` in
`AllocFsA1PlacedBudget.allocContracts{Fs,XCli}Placed_of_hooks` (`:218, 264`) with
`HookSat H memsetName` bundles (`MemsetContractsFsBudgetSat H` / `MemsetContractsBudgetSat H`),
matching the 4 `memset` entries of `AllocContracts{Fs,XCli}Placed`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudgetSat

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.E2E (allocHook0 deallocHook reallocHook0)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName memmoveName memsetName withStack)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops
  (allocHook0_fs allocHookStack_le_extHookStack deallocHook_fs extHookStack_le hookMemcpy_fs
   hookMemmove_fs hookMemset_fs hookNoop_fs hook_stub_placed_ok pos_of_extHookStack_le
   reallocHook0_fs)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget
  (CliAllocHooks hookMemcpy_region_ro_vm_ok hookMemcpy_region_vm_ok hookMemcpy_vm_ok
   hookMemmove_vm_ok hookMemset_region_vm_ok hookMemset_vm_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget
  (ls_hook_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
  (hookOk_rustAllocWithStack hookOk_rustDeallocExternWithStack hookOk_rustReallocExternWithStack
   hookOk_withStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (sessionMemcpyBudget_hookOk sessionMemcpyRegionBudget_hookOk sessionMemmoveBudget_hookOk
   sessionMemsetBudget_hookOk sessionMemsetRegionBudget_hookOk sessionShimBudget_hookOk)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec
   sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)

/-- `HookSat` bundle for the 4 `.keepsFs` `memset` contracts consumed by
`AllocContractsFsPlaced`. -/
structure MemsetContractsFsBudgetSat (H : LibsignalHooks) : Prop where
  memset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (withVmPreserved (libcMemsetSpec stk)).keepsFs
  session_memset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (sessionMemsetBudgetSpec stk).keepsFs
  memset_region : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs
  session_memset_region : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (withStack sessionMemsetRegionBudgetSpec stk).keepsFs

/-- `HookSat` bundle for the 4 `memset` contracts consumed by `AllocContractsXCliPlaced`. -/
structure MemsetContractsBudgetSat (H : LibsignalHooks) : Prop where
  memset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (withVmPreserved (libcMemsetSpec stk))
  session_memset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (sessionMemsetBudgetSpec stk)
  memset_region : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (withStack (withVmPreserved memsetRegionSpec) stk)
  session_memset_region : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookSat H memsetName (withStack sessionMemsetRegionBudgetSpec stk)

/-- Discharge `MemsetContractsFsBudgetSat H` from `H memsetName = some hookMemset`. -/
theorem MemsetContractsFsBudgetSat.of_hookMemset_eq {H : LibsignalHooks}
    (hmemset : H memsetName = some hookMemset) : MemsetContractsFsBudgetSat H where
  memset stk hle _ :=
    ⟨hookMemset, hmemset, (hookMemset_vm_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs⟩
  session_memset stk hle _ :=
    ⟨hookMemset, hmemset,
      (sessionMemsetBudget_hookOk stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs⟩
  memset_region stk _ _ :=
    ⟨hookMemset, hmemset, (hookOk_withStack hookMemset_region_vm_ok stk).keepsFs hookMemset_fs⟩
  session_memset_region stk _ _ :=
    ⟨hookMemset, hmemset,
      (hookOk_withStack sessionMemsetRegionBudget_hookOk stk).keepsFs hookMemset_fs⟩

/-- Discharge `MemsetContractsBudgetSat H` from `H memsetName = some hookMemset`. -/
theorem MemsetContractsBudgetSat.of_hookMemset_eq {H : LibsignalHooks}
    (hmemset : H memsetName = some hookMemset) : MemsetContractsBudgetSat H where
  memset stk hle _ :=
    ⟨hookMemset, hmemset, hookMemset_vm_ok stk (pos_of_extHookStack_le hle)⟩
  session_memset stk hle _ :=
    ⟨hookMemset, hmemset, sessionMemsetBudget_hookOk stk (pos_of_extHookStack_le hle)⟩
  memset_region stk _ _ :=
    ⟨hookMemset, hmemset, hookOk_withStack hookMemset_region_vm_ok stk⟩
  session_memset_region stk _ _ :=
    ⟨hookMemset, hmemset, hookOk_withStack sessionMemsetRegionBudget_hookOk stk⟩

/-- `HookSat` sibling of `AllocFsA1PlacedBudget.allocContractsFsPlaced_of_hooks` (`:218`). -/
theorem allocContractsFsPlaced_of_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : CliAllocHooks A lim)
    (hshim : H lsRustNoAllocShimSymCli = some hookNoop)
    (halloc : H lsRustAllocSymCli = some allocHook0)
    (hdealloc : H lsRustDeallocSymCli = some deallocHook)
    (hrealloc : H lsRustReallocSymCli = some reallocHook0)
    (hmemset : MemsetContractsFsBudgetSat H)
    (hmemmove : H memmoveName = some hookMemmove)
    (hmemcpy : H memcpyName = some hookMemcpy) :
    AllocContractsFsPlaced A lim H where
  alloc := hook_stub_placed_ok halloc <|
    (hookOk_rustAllocWithStack (stk := extHookStack) hA.alloc allocHookStack_le_extHookStack
      extHookStack_le).keepsFs allocHook0_fs
  dealloc := hook_stub_placed_ok hdealloc <|
    (hookOk_rustDeallocExternWithStack (stk := extHookStack) hA.dealloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs deallocHook_fs
  realloc := hook_stub_placed_ok hrealloc <|
    (hookOk_rustReallocExternWithStack (stk := extHookStack) hA.realloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs reallocHook0_fs
  shim stk _ _ := hook_stub_placed_ok hshim <|
    (hookOk_withStack sessionShimBudget_hookOk stk).keepsFs hookNoop_fs
  memcpy stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookMemcpy_vm_ok stk).keepsFs hookMemcpy_fs
  session_memcpy stk _ _ := hook_stub_placed_ok hmemcpy <|
    (sessionMemcpyBudget_hookOk stk).keepsFs hookMemcpy_fs
  memcpy_region stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookOk_withStack hookMemcpy_region_vm_ok stk).keepsFs hookMemcpy_fs
  session_memcpy_region stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookOk_withStack sessionMemcpyRegionBudget_hookOk stk).keepsFs hookMemcpy_fs
  memmove stk _ _ := hook_stub_placed_ok hmemmove <|
    (hookMemmove_vm_ok stk).keepsFs hookMemmove_fs
  session_memmove stk _ _ := hook_stub_placed_ok hmemmove <|
    (sessionMemmoveBudget_hookOk stk).keepsFs hookMemmove_fs
  memset stk h1 h2 := ls_hook_placed_ok (hmemset.memset stk h1 h2)
  session_memset stk h1 h2 := ls_hook_placed_ok (hmemset.session_memset stk h1 h2)
  memset_region stk h1 h2 := ls_hook_placed_ok (hmemset.memset_region stk h1 h2)
  session_memset_region stk h1 h2 := ls_hook_placed_ok (hmemset.session_memset_region stk h1 h2)
  session_memcpy_region_ro stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookOk_withStack hookMemcpy_region_ro_vm_ok stk).keepsFs hookMemcpy_fs

/-- `HookSat` sibling of `AllocFsA1PlacedBudget.allocContractsXCliPlaced_of_hooks` (`:264`). -/
theorem allocContractsXCliPlaced_of_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : CliAllocHooks A lim)
    (hshim : H lsRustNoAllocShimSymCli = some hookNoop)
    (halloc : H lsRustAllocSymCli = some allocHook0)
    (hdealloc : H lsRustDeallocSymCli = some deallocHook)
    (hrealloc : H lsRustReallocSymCli = some reallocHook0)
    (hmemset : MemsetContractsBudgetSat H)
    (hmemmove : H memmoveName = some hookMemmove)
    (hmemcpy : H memcpyName = some hookMemcpy) :
    AllocContractsXCliPlaced A lim H where
  alloc := hook_stub_placed_ok halloc <|
    hookOk_rustAllocWithStack (stk := extHookStack) hA.alloc allocHookStack_le_extHookStack
      extHookStack_le
  dealloc := hook_stub_placed_ok hdealloc <|
    hookOk_rustDeallocExternWithStack (stk := extHookStack) hA.dealloc
      allocHookStack_le_extHookStack extHookStack_le
  realloc := hook_stub_placed_ok hrealloc <|
    hookOk_rustReallocExternWithStack (stk := extHookStack) hA.realloc
      allocHookStack_le_extHookStack extHookStack_le
  shim stk _ _ := hook_stub_placed_ok hshim <|
    hookOk_withStack sessionShimBudget_hookOk stk
  memcpy stk _ _ := hook_stub_placed_ok hmemcpy (hookMemcpy_vm_ok stk)
  session_memcpy stk _ _ := hook_stub_placed_ok hmemcpy (sessionMemcpyBudget_hookOk stk)
  memcpy_region stk _ _ := hook_stub_placed_ok hmemcpy (hookOk_withStack hookMemcpy_region_vm_ok stk)
  session_memcpy_region stk _ _ :=
    hook_stub_placed_ok hmemcpy (hookOk_withStack sessionMemcpyRegionBudget_hookOk stk)
  memmove stk _ _ := hook_stub_placed_ok hmemmove (hookMemmove_vm_ok stk)
  session_memmove stk _ _ := hook_stub_placed_ok hmemmove (sessionMemmoveBudget_hookOk stk)
  memset stk h1 h2 := ls_hook_placed_ok (hmemset.memset stk h1 h2)
  session_memset stk h1 h2 := ls_hook_placed_ok (hmemset.session_memset stk h1 h2)
  memset_region stk h1 h2 := ls_hook_placed_ok (hmemset.memset_region stk h1 h2)
  session_memset_region stk h1 h2 := ls_hook_placed_ok (hmemset.session_memset_region stk h1 h2)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudgetSat
