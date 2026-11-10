/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# Budget-Threaded Cross-Block Call-Site Helpers for `AllocContractsFsPlaced` and `AllocContractsXCliPlaced`

Transfers each entry of `SpecsPlacedBudget.AllocContractsFsPlaced A lim H` and
`AllocContractsXCliPlaced A lim H` from Block `617` to any caller block `prog` (`IsLsBlockProg prog i H`,
`i < 619`) under `withLsRoCl lsmpl`.
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget

open Arm64 ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (ls_subroutine_ok_rocl_of_block withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName memmoveName memsetName sessionMemcpyRegionSpec sessionShimSpec withStack)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (session2MemcpyBudgetSpecX session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec
   sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack rustReallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)

/-! ## `AllocContractsFsPlaced` Call-Site Helpers -/

namespace AllocContractsFsPlaced

section CallerBlock
variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem alloc_rocl (hA : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack M A lim false extHookStack).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.alloc hi

theorem dealloc_rocl (hA : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.dealloc hi

theorem realloc_rocl (hA : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustReallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.realloc hi

theorem shim_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (withStack sessionShimBudgetSpec stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.shim stk h1 h2) hi

theorem memcpy_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (withVmPreserved (libcMemcpySpec stk)).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy stk h1 h2) hi

theorem session_memcpy_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (sessionMemcpyBudgetSpec stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memcpy stk h1 h2) hi

theorem memcpy_region_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy_region stk h1 h2) hi

theorem session_memcpy_region_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memcpy_region stk h1 h2) hi

theorem session_memcpy_region_ro_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memcpy_region_ro stk h1 h2) hi

theorem memmove_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (withLsRoCl lsmpl (withVmPreserved (libcMemmoveSpec stk)).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memmove stk h1 h2) hi

theorem session_memmove_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (withLsRoCl lsmpl (sessionMemmoveBudgetSpec stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memmove stk h1 h2) hi

theorem memset_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (withVmPreserved (libcMemsetSpec stk)).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset stk h1 h2) hi

theorem session_memset_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (sessionMemsetBudgetSpec stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memset stk h1 h2) hi

theorem memset_region_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset_region stk h1 h2) hi

theorem session_memset_region_rocl (hA : AllocContractsFsPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (withStack sessionMemsetRegionBudgetSpec stk).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memset_region stk h1 h2) hi

theorem shim2_rocl (hA : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl session2ShimBudgetSpecX.keepsFs) := by
  refine subroutine_ok_mono (shim_rocl hA extHookStack (by decide) (by decide) hi) ?_ ?_
  · intro x R s0 hp
    dsimp only [withLsRoCl, Spec.keepsFs, withStack, sessionShimBudgetSpec, sessionShimSpec,
      session2ShimBudgetSpecX] at hp ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hp
  · intro x R s0 sf hq
    dsimp only [withLsRoCl, Spec.keepsFs, withStack, sessionShimBudgetSpec, sessionShimSpec,
      session2ShimBudgetSpecX] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hro, hfs, hvm, htr, hrest⟩
    exact ⟨hro, hfs, ⟨htr, hvm⟩, hrest⟩

theorem memcpy2_rocl (hA : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpyBudgetSpecX.keepsFs) := by
  refine subroutine_ok_mono
    (session_memcpy_region_rocl hA extHookStack (by decide) (by decide) hi) ?_ ?_
  · intro x R s0 hp
    dsimp only [withLsRoCl, Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpyBudgetSpecX] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · intro x R s0 sf hq
    dsimp only [withLsRoCl, Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpyBudgetSpecX] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hro, hfs, hvm, ⟨hx0, htr⟩, hrest⟩
    exact ⟨hro, hfs, ⟨hx0, htr, hvm⟩, hrest⟩

end CallerBlock

end AllocContractsFsPlaced

/-! ## `AllocContractsXCliPlaced` Call-Site Helpers -/

namespace AllocContractsXCliPlaced

section CallerBlock
variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem alloc_rocl (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack M A lim false extHookStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.alloc hi

theorem dealloc_rocl (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.dealloc hi

theorem realloc_rocl (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustReallocExternSpecWithStack M A lim extHookStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.realloc hi

theorem shim_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (withStack sessionShimBudgetSpec stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.shim stk h1 h2) hi

theorem shim2_rocl (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl session2ShimBudgetSpecX) := by
  refine subroutine_ok_mono (shim_rocl hA extHookStack (by decide) (by decide) hi) ?_ ?_
  · intro x R s0 hp
    dsimp only [withLsRoCl, withStack, sessionShimBudgetSpec, sessionShimSpec,
      session2ShimBudgetSpecX] at hp ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hp
  · intro x R s0 sf hq
    dsimp only [withLsRoCl, withStack, sessionShimBudgetSpec, sessionShimSpec,
      session2ShimBudgetSpecX] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hro, hvm, htr, hrest⟩
    exact ⟨hro, ⟨htr, hvm⟩, hrest⟩

theorem memcpy_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (withVmPreserved (libcMemcpySpec stk))) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy stk h1 h2) hi

theorem session_memcpy_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (sessionMemcpyBudgetSpec stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memcpy stk h1 h2) hi

theorem memcpy_region_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack (withVmPreserved memcpyRegionSpec) stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy_region stk h1 h2) hi

theorem session_memcpy_region_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionBudgetSpec stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memcpy_region stk h1 h2) hi

theorem memcpy2_rocl (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpyBudgetSpecX) := by
  refine subroutine_ok_mono
    (session_memcpy_region_rocl hA extHookStack (by decide) (by decide) hi) ?_ ?_
  · intro x R s0 hp
    dsimp only [withLsRoCl, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpyBudgetSpecX] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · intro x R s0 sf hq
    dsimp only [withLsRoCl, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpyBudgetSpecX] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hro, hvm, ⟨hx0, htr⟩, hrest⟩
    exact ⟨hro, ⟨hx0, htr, hvm⟩, hrest⟩

theorem memmove_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (withLsRoCl lsmpl (withVmPreserved (libcMemmoveSpec stk))) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memmove stk h1 h2) hi

theorem session_memmove_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (withLsRoCl lsmpl (sessionMemmoveBudgetSpec stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memmove stk h1 h2) hi

theorem memset_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (withVmPreserved (libcMemsetSpec stk))) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset stk h1 h2) hi

theorem session_memset_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (sessionMemsetBudgetSpec stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memset stk h1 h2) hi

theorem memset_region_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (withStack (withVmPreserved memsetRegionSpec) stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset_region stk h1 h2) hi

theorem session_memset_region_rocl (hA : AllocContractsXCliPlaced A lim H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (withLsRoCl lsmpl (withStack sessionMemsetRegionBudgetSpec stk)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memset_region stk h1 h2) hi

end CallerBlock

end AllocContractsXCliPlaced

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
