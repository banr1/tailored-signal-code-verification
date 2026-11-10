/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `AllocContractsFsPlaced` and `AllocContractsXCliPlaced`

`RustCliAllocBudget M` counterparts of `AllocFsA1Placed.lean` on Block `617` (`lsProg_617 H`),
constructing `AllocContractsFsPlaced A lim H` and `AllocContractsXCliPlaced A lim H` from
`HookSat H` witnesses or `CliAllocHooks A lim`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalSessionExterns ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E (allocHook0 deallocHook reallocHook0)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName memmoveName memsetName withStack)
open CryptoVerification.SignalSession
  ( lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
   lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (allocHook0_fs allocHookStack_le_extHookStack deallocHook_fs
   extHookStack_le hookMemcpy_fs hookMemmove_fs hookMemset_fs hookNoop_fs hook_stub_placed_ok
   pos_of_extHookStack_le reallocHook0_fs subroutine_ok_withLsCodeRoLoaded_of_keepsFs)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget
  (CliAllocHooks hookMemcpy_region_ro_vm_ok hookMemcpy_region_vm_ok hookMemcpy_vm_ok
   hookMemmove_vm_ok hookMemset_region_vm_ok hookMemset_vm_ok)
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
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack rustReallocExternSpecWithStack)

/-! ## `HookSat` Lift and `.keepsFs` Projection on Block `617` -/

/-- Lift a `HookSat H sym spec` witness to `subroutine_ok (lsProg_617 H) (lsρ sym)` wrapped in
`StoreKit.withLsCodeRoLoaded lsmpl`. -/
theorem ls_hook_placed_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat hmem

theorem allocContractsFsPlaced_toAllocContractsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsFsPlaced A lim H) : AllocContractsXCliPlaced A lim H where
  alloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.alloc
  dealloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.dealloc
  realloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.realloc
  shim stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.shim stk h1 h2)
  memcpy stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memcpy stk h1 h2)
  session_memcpy stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memcpy stk h1 h2)
  memcpy_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memcpy_region stk h1 h2)
  session_memcpy_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memcpy_region stk h1 h2)
  memmove stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memmove stk h1 h2)
  session_memmove stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memmove stk h1 h2)
  memset stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memset stk h1 h2)
  session_memset stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memset stk h1 h2)
  memset_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memset_region stk h1 h2)
  session_memset_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memset_region stk h1 h2)

/-- Assemble `AllocContractsFsPlaced A lim H` on Block `617` from `HookSat H` witnesses. -/
theorem allocContractsFsPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpecWithStack M A lim false extHookStack).keepsFs)
    (hdealloc : HookSat H lsRustDeallocSymCli
      (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs)
    (hrealloc : HookSat H lsRustReallocSymCli
      (rustReallocExternSpecWithStack M A lim extHookStack).keepsFs)
    (hshim : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H lsRustNoAllocShimSymCli (withStack sessionShimBudgetSpec stk).keepsFs)
    (hmemcpy : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (withVmPreserved (libcMemcpySpec stk)).keepsFs)
    (hsmemcpy : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (sessionMemcpyBudgetSpec stk).keepsFs)
    (hmemcpyR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs)
    (hsmemcpyR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs)
    (hmemmove : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memmoveName (withVmPreserved (libcMemmoveSpec stk)).keepsFs)
    (hsmemmove : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memmoveName (sessionMemmoveBudgetSpec stk).keepsFs)
    (hmemset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (withVmPreserved (libcMemsetSpec stk)).keepsFs)
    (hsmemset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (sessionMemsetBudgetSpec stk).keepsFs)
    (hmemsetR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs)
    (hsmemsetR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (withStack sessionMemsetRegionBudgetSpec stk).keepsFs)
    (hsmemcpyRO : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk).keepsFs) :
    AllocContractsFsPlaced A lim H where
  alloc := ls_hook_placed_ok halloc
  dealloc := ls_hook_placed_ok hdealloc
  realloc := ls_hook_placed_ok hrealloc
  shim stk h1 h2 := ls_hook_placed_ok (hshim stk h1 h2)
  memcpy stk h1 h2 := ls_hook_placed_ok (hmemcpy stk h1 h2)
  session_memcpy stk h1 h2 := ls_hook_placed_ok (hsmemcpy stk h1 h2)
  memcpy_region stk h1 h2 := ls_hook_placed_ok (hmemcpyR stk h1 h2)
  session_memcpy_region stk h1 h2 := ls_hook_placed_ok (hsmemcpyR stk h1 h2)
  memmove stk h1 h2 := ls_hook_placed_ok (hmemmove stk h1 h2)
  session_memmove stk h1 h2 := ls_hook_placed_ok (hsmemmove stk h1 h2)
  memset stk h1 h2 := ls_hook_placed_ok (hmemset stk h1 h2)
  session_memset stk h1 h2 := ls_hook_placed_ok (hsmemset stk h1 h2)
  memset_region stk h1 h2 := ls_hook_placed_ok (hmemsetR stk h1 h2)
  session_memset_region stk h1 h2 := ls_hook_placed_ok (hsmemsetR stk h1 h2)
  session_memcpy_region_ro stk h1 h2 := ls_hook_placed_ok (hsmemcpyRO stk h1 h2)

/-- Assemble `AllocContractsXCliPlaced A lim H` on Block `617` from `HookSat H` witnesses. -/
theorem allocContractsXCliPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpecWithStack M A lim false extHookStack))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustDeallocExternSpecWithStack M A lim extHookStack))
    (hrealloc : HookSat H lsRustReallocSymCli (rustReallocExternSpecWithStack M A lim extHookStack))
    (hshim : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H lsRustNoAllocShimSymCli (withStack sessionShimBudgetSpec stk))
    (hmemcpy : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (withVmPreserved (libcMemcpySpec stk)))
    (hsmemcpy : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (sessionMemcpyBudgetSpec stk))
    (hmemcpyR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (withStack (withVmPreserved memcpyRegionSpec) stk))
    (hsmemcpyR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memcpyName (withStack sessionMemcpyRegionBudgetSpec stk))
    (hmemmove : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memmoveName (withVmPreserved (libcMemmoveSpec stk)))
    (hsmemmove : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memmoveName (sessionMemmoveBudgetSpec stk))
    (hmemset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (withVmPreserved (libcMemsetSpec stk)))
    (hsmemset : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (sessionMemsetBudgetSpec stk))
    (hmemsetR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (withStack (withVmPreserved memsetRegionSpec) stk))
    (hsmemsetR : ∀ stk, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      HookSat H memsetName (withStack sessionMemsetRegionBudgetSpec stk)) :
    AllocContractsXCliPlaced A lim H where
  alloc := ls_hook_placed_ok halloc
  dealloc := ls_hook_placed_ok hdealloc
  realloc := ls_hook_placed_ok hrealloc
  shim stk h1 h2 := ls_hook_placed_ok (hshim stk h1 h2)
  memcpy stk h1 h2 := ls_hook_placed_ok (hmemcpy stk h1 h2)
  session_memcpy stk h1 h2 := ls_hook_placed_ok (hsmemcpy stk h1 h2)
  memcpy_region stk h1 h2 := ls_hook_placed_ok (hmemcpyR stk h1 h2)
  session_memcpy_region stk h1 h2 := ls_hook_placed_ok (hsmemcpyR stk h1 h2)
  memmove stk h1 h2 := ls_hook_placed_ok (hmemmove stk h1 h2)
  session_memmove stk h1 h2 := ls_hook_placed_ok (hsmemmove stk h1 h2)
  memset stk h1 h2 := ls_hook_placed_ok (hmemset stk h1 h2)
  session_memset stk h1 h2 := ls_hook_placed_ok (hsmemset stk h1 h2)
  memset_region stk h1 h2 := ls_hook_placed_ok (hmemsetR stk h1 h2)
  session_memset_region stk h1 h2 := ls_hook_placed_ok (hsmemsetR stk h1 h2)

/-! ## Constructors from `CliAllocHooks` and Read-Only `memcpy` -/

/-- Constructs `AllocContractsFsPlaced A lim H` from `CliAllocHooks A lim` and canonical hook lookups. -/
theorem allocContractsFsPlaced_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : CliAllocHooks A lim)
    (hshim : H lsRustNoAllocShimSymCli = some hookNoop)
    (halloc : H lsRustAllocSymCli = some allocHook0)
    (hdealloc : H lsRustDeallocSymCli = some deallocHook)
    (hrealloc : H lsRustReallocSymCli = some reallocHook0)
    (hmemset : H memsetName = some hookMemset)
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
  memset stk hle _ := hook_stub_placed_ok hmemset <|
    (hookMemset_vm_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  session_memset stk hle _ := hook_stub_placed_ok hmemset <|
    (sessionMemsetBudget_hookOk stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  memset_region stk _ _ := hook_stub_placed_ok hmemset <|
    (hookOk_withStack hookMemset_region_vm_ok stk).keepsFs hookMemset_fs
  session_memset_region stk _ _ := hook_stub_placed_ok hmemset <|
    (hookOk_withStack sessionMemsetRegionBudget_hookOk stk).keepsFs hookMemset_fs
  session_memcpy_region_ro stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookOk_withStack hookMemcpy_region_ro_vm_ok stk).keepsFs hookMemcpy_fs

/-- Constructs `AllocContractsXCliPlaced A lim H` from `CliAllocHooks A lim` and canonical hook lookups. -/
theorem allocContractsXCliPlaced_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : CliAllocHooks A lim)
    (hshim : H lsRustNoAllocShimSymCli = some hookNoop)
    (halloc : H lsRustAllocSymCli = some allocHook0)
    (hdealloc : H lsRustDeallocSymCli = some deallocHook)
    (hrealloc : H lsRustReallocSymCli = some reallocHook0)
    (hmemset : H memsetName = some hookMemset)
    (hmemmove : H memmoveName = some hookMemmove)
    (hmemcpy : H memcpyName = some hookMemcpy) :
    AllocContractsXCliPlaced A lim H :=
  allocContractsFsPlaced_toAllocContractsX
    (allocContractsFsPlaced_of_hooks hA hshim halloc hdealloc hrealloc hmemset hmemmove hmemcpy)

/-- Any extern map mapping `memcpyName` to `hookMemcpy` meets
    `withVmPreserved sessionMemcpyRegionROSpec`. -/
theorem cli_hookSat_memcpy_region_ro_vm_placed {H : LibsignalHooks}
    (hmemcpy : H memcpyName = some hookMemcpy) :
    HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec) :=
  ⟨hookMemcpy, hmemcpy, hookMemcpy_region_ro_vm_ok⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget
