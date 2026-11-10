/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `memrchr` Hook Discharge for `signal_session::address`

`RustCliAllocBudget` counterparts of `AddressA1Placed.lean`, discharging the
`withVmPreserved (memrchrSpec extHookStack)` extern hypothesis of `AddressPlacedBudget.address_placed_ok`
against `CliRun.memrchrHook`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsMemrchrSym memrchrHook unmodelled)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_580)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliExternsPlaced_memrchr memrchrHook_ok memrchrSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_setPC vmPreserved_setStatus vmPreserved_writeReg64)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlacedBudget
  (address_placed_ok address_placed_ok_rocl)

private theorem subroutine_ok_rocl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_withLsCodeRoLoaded_of_plain h)

theorem memrchrHook_vmPreserved (s : State) : VmPreserved s (memrchrHook s) := by
  unfold memrchrHook
  change VmPreserved s
    (if (!s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat) = true then
      unmodelled "memrchr: unreadable bytes" s
    else
      match ((List.range (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat).length).filter
        fun i => (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)[i]? ==
          some ((s.readReg64 .x0).setWidth 8)).getLast? with
      | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
      | none => retHook (fun s => s.writeReg64 .x0 0#64) s)
  split
  · unfold unmodelled
    simp only [vmPreserved_setStatus, VmPreserved.refl]
  · split
    · unfold retHook
      simp only [vmPreserved_setPC, vmPreserved_writeReg64, VmPreserved.refl]
    · unfold retHook
      simp only [vmPreserved_setPC, vmPreserved_writeReg64, VmPreserved.refl]

/-- Budget-threaded relocatable `address_placed_ok_a1_of_hooks` for any `H : LibsignalHooks` with
`AllocContractsFsPlaced A lim H` and `H lsMemrchrSym = some memrchrHook`. -/
theorem address_placed_ok_a1_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hext : H lsMemrchrSym = some memrchrHook)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A lim uuidTryParse resStack)) := by
  refine address_placed_ok hFs ?_ hres hres64
  have hsat : HookSat H lsMemrchrSym (memrchrSpec extHookStack) :=
    ⟨memrchrHook, hext, memrchrHook_ok extHookStack⟩
  have hsat_vm : HookSat H lsMemrchrSym (withVmPreserved (memrchrSpec extHookStack)) :=
    hookSat_withVmPreserved hsat (fun f hf s => by
      cases hext.symm.trans hf
      exact memrchrHook_vmPreserved s)
  have hplain : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withVmPreserved (memrchrSpec extHookStack)) := by
    dsimp only [lsProg_580]
    exact ls_hook_ok_ultra_of_mem hsat_vm (by decide)
  exact subroutine_ok_rocl_of_plain hplain

theorem address_placed_ok_a1_rocl_of_hooks [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hext : H lsMemrchrSym = some memrchrHook)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A lim uuidTryParse resStack)) := by
  refine address_placed_ok_rocl (prog := prog) (i := i) hFs ?_ hres hres64 hi
  have hsat : HookSat H lsMemrchrSym (memrchrSpec extHookStack) :=
    ⟨memrchrHook, hext, memrchrHook_ok extHookStack⟩
  have hsat_vm : HookSat H lsMemrchrSym (withVmPreserved (memrchrSpec extHookStack)) :=
    hookSat_withVmPreserved hsat (fun f hf s => by
      cases hext.symm.trans hf
      exact memrchrHook_vmPreserved s)
  have hplain : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withVmPreserved (memrchrSpec extHookStack)) := by
    dsimp only [lsProg_580]
    exact ls_hook_ok_ultra_of_mem hsat_vm (by decide)
  exact subroutine_ok_rocl_of_plain hplain

theorem address_placed_ok_a1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (hFs : AllocContractsFsPlaced A lim (cliExternsPlaced mmpl W))
    {resStack : Nat}
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A lim uuidTryParse resStack)) :=
  address_placed_ok_a1_of_hooks hFs (cliExternsPlaced_memrchr mmpl W) hres hres64

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudget
