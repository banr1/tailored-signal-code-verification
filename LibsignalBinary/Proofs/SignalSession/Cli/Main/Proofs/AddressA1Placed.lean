/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `memrchr` Hook Discharge for `signal_session::address`

Discharges the `memrchr` extern hypothesis of `address_placed_ok` against `CliRun.memrchrHook`
for any `H : LibsignalHooks` (`address_placed_ok_a1_of_hooks`) and on `cliExternsPlaced mmpl W`
(`address_placed_ok_a1`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.HooksE
open Address.Helpers

private theorem subroutine_ok_rocl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp hL
  dsimp only [withLsRoCl] at hpre
  rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcrl0, hpre⟩
  obtain ⟨sf, hsteps, hout⟩ := h.to_outcome x R s0 hpc hrun hpre hsp hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨lscro_of_keepsFrozen hcrl0 hsteps.keepsFrozen, hpost⟩
  · exact Or.inr hrest

/-- Relocatable `address_ok_a1` for any `H : LibsignalHooks` with `AllocContractsFsPlaced A H`,
panic symbol `lsHandleErrorSym580`, and `H lsMemrchrSym = some memrchrHook`. -/
theorem address_placed_ok_a1_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hext : H lsMemrchrSym = some memrchrHook)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) := by
  refine address_placed_ok hCF hpan ?_ hres hres64
  have hsat : HookSat H lsMemrchrSym (memrchrSpec extHookStack) :=
    ⟨memrchrHook, hext, memrchrHook_ok extHookStack⟩
  have hplain : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym) (memrchrSpec extHookStack) := by
    dsimp only [lsProg_580]
    exact ls_hook_ok_ultra_of_mem hsat (by decide)
  exact subroutine_ok_rocl_of_plain hplain

theorem address_placed_ok_a1 [LibsignalPlacement] {A : RustAlloc}
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (hFs : AllocContractsFsPlaced A (cliExternsPlaced mmpl W)) {resStack : Nat}
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) :=
  address_placed_ok_a1_of_hooks
    hFs
    (by
      simp only [cliExternsPlaced, lsHandleErrorSym580, isCliPanicSymbolPlaced,
        cliPanicSymbolsPlaced, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.or_true,
        ↓reduceIte])
    (cliExternsPlaced_memrchr mmpl W)
    hres hres64

end CryptoVerification.SignalSession.Cli.MainHops
