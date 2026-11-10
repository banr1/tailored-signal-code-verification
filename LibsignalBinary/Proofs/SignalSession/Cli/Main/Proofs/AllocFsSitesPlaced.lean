/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSites
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

/-!
# Cross-Block Call-Site Helpers for `AllocContractsFsPlaced` and `AllocContractsXCliPlaced`

Transfers each entry of `AllocContractsFsPlaced A H` and `AllocContractsXCliPlaced A H` from
Block `617` (`lsProg_617 H`) to any caller block `prog` (`IsLsBlockProg prog i H`, `i < 619`) under
`withLsRoCl lsmpl`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed

/-! ## `AllocContractsFsPlaced` Call-Site Helpers -/

namespace AllocContractsFsPlaced

section CallerBlock
variable [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem alloc_rocl (hA : AllocContractsFsPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.alloc hi

theorem dealloc_rocl (hA : AllocContractsFsPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.dealloc hi

theorem realloc_rocl (hA : AllocContractsFsPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustReallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (rustReallocExternSpecWithStack A extHookStack).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.realloc hi

theorem shim_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack sessionShimSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.shim stk h1 h2) hi

theorem memcpy_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (libcMemcpySpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy stk h1 h2) hi

theorem session_memcpy_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (sessionMemcpySpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memcpy stk h1 h2) hi

theorem memcpy_region_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack memcpyRegionSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy_region stk h1 h2) hi

theorem session_memcpy_region_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack sessionMemcpyRegionSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    (hA.session_memcpy_region stk h1 h2) hi

theorem session_memcpy_region_ro_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    (hA.session_memcpy_region_ro stk h1 h2) hi

theorem memmove_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (libcMemmoveSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memmove stk h1 h2) hi

theorem session_memmove_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (sessionMemmoveSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memmove stk h1 h2) hi

theorem memset_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (libcMemsetSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset stk h1 h2) hi

theorem session_memset_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (sessionMemsetSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memset stk h1 h2) hi

theorem memset_region_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack memsetRegionSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset_region stk h1 h2) hi

theorem session_memset_region_rocl (hA : AllocContractsFsPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack sessionMemsetRegionSpec stk).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    (hA.session_memset_region stk h1 h2) hi

theorem shim2_rocl (hA : AllocContractsFsPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl session2ShimSpecX.keepsFs) := by
  refine subroutine_ok_mono (hA.shim_rocl extHookStack (by decide) (by decide) hi) ?_ (fun _ _ _ _ hq => hq)
  intro x s0 R hp
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs, withStack, sessionShimSpec,
    session2ShimSpecX] at hp ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hp

theorem memcpy2_rocl (hA : AllocContractsFsPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl session2MemcpySpecX.keepsFs) := by
  refine subroutine_ok_mono (hA.session_memcpy_region_rocl extHookStack (by decide) (by decide) hi) ?_ ?_
  · intro x s0 R hp
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecX] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · intro x s0 sf R hq
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecX] at hq ⊢
    simpa only [sepConj_assoc] using hq

end CallerBlock

end AllocContractsFsPlaced

/-! ## `AllocContractsXCliPlaced` Call-Site Helpers -/

namespace AllocContractsXCliPlaced

section CallerBlock
variable [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem alloc_rocl (hA : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.alloc hi

theorem dealloc_rocl (hA : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.dealloc hi

theorem realloc_rocl (hA : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustReallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (rustReallocExternSpecWithStack A extHookStack)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) hA.realloc hi

theorem shim_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack sessionShimSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.shim stk h1 h2) hi

theorem shim2_rocl (hA : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl session2ShimSpecX) := by
  refine subroutine_ok_mono (hA.shim_rocl extHookStack (by decide) (by decide) hi) ?_ (fun _ _ _ _ hq => hq)
  intro x s0 R hp
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, withStack, sessionShimSpec,
    session2ShimSpecX] at hp ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hp

theorem memcpy_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (libcMemcpySpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy stk h1 h2) hi

theorem session_memcpy_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (sessionMemcpySpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memcpy stk h1 h2) hi

theorem memcpy_region_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack memcpyRegionSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memcpy_region stk h1 h2) hi

theorem session_memcpy_region_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack sessionMemcpyRegionSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    (hA.session_memcpy_region stk h1 h2) hi

theorem memmove_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (libcMemmoveSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memmove stk h1 h2) hi

theorem session_memmove_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memmoveName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (sessionMemmoveSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memmove stk h1 h2) hi

theorem memset_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (libcMemsetSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset stk h1 h2) hi

theorem session_memset_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (sessionMemsetSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.session_memset stk h1 h2) hi

theorem memset_region_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack memsetRegionSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617) (hA.memset_region stk h1 h2) hi

theorem session_memset_region_rocl (hA : AllocContractsXCliPlaced A H) (stk : Nat := extHookStack)
    (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memsetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack sessionMemsetRegionSpec stk)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    (hA.session_memset_region stk h1 h2) hi

end CallerBlock

end AllocContractsXCliPlaced

end CryptoVerification.SignalSession.Cli.MainHops
