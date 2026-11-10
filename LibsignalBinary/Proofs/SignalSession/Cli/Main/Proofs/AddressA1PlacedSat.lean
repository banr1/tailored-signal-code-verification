/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import

/-!
# `HookSat` Sibling of `AddressA1Placed` (`AddressA1PlacedSat`)

Replaces `hext : H lsMemrchrSym = some memrchrHook` in `address_placed_ok_a1_of_hooks`
(`AddressA1Placed.lean:65`) with
`hext : HookSat H lsMemrchrSym (withLsRet (memrchrSpec extHookStack))`,
plus the exact-hook bridges `hookSat_memrchr_of_eq` and `hookSat_memrchr_ls_of_eq`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedSat

open Arm64 ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsRoCl)
open CryptoVerification.SignalSession (lsMemrchrSym memrchrHook)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_580)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AllocContractsFsPlaced addressSpec address_placed_ok_ls memrchrHook_ok memrchrSpec)
open CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers (lsHandleErrorSym580)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (hookSat_withLsRet withLsRet)

private theorem subroutine_ok_rocl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_withLsCodeRoLoaded_of_plain h)

/-- Coercion from `H lsMemrchrSym = some memrchrHook` to `HookSat H lsMemrchrSym (memrchrSpec extHookStack)`. -/
theorem hookSat_memrchr_of_eq {H : LibsignalHooks}
    (hext : H lsMemrchrSym = some memrchrHook) :
    HookSat H lsMemrchrSym (memrchrSpec extHookStack) :=
  ⟨memrchrHook, hext, memrchrHook_ok extHookStack⟩

/-- Coercion from `H lsMemrchrSym = some memrchrHook` to
    `HookSat H lsMemrchrSym (withLsRet (memrchrSpec extHookStack))`. -/
theorem hookSat_memrchr_ls_of_eq [LibsignalPlacement] {H : LibsignalHooks}
    (hext : H lsMemrchrSym = some memrchrHook) :
    HookSat H lsMemrchrSym (withLsRet (memrchrSpec extHookStack)) :=
  hookSat_withLsRet (hookSat_memrchr_of_eq hext)

/-- `HookSat` sibling of `address_placed_ok_a1_of_hooks` (`AddressA1Placed.lean:65`). -/
theorem address_placed_ok_a1_of_hooks_sat [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hext : HookSat H lsMemrchrSym (withLsRet (memrchrSpec extHookStack)))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) := by
  refine address_placed_ok_ls hCF hpan ?_ hres hres64
  have hplain : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRet (memrchrSpec extHookStack)) := by
    dsimp only [lsProg_580]
    exact ls_hook_ok_ultra_of_mem hext (by decide)
  exact subroutine_ok_rocl_of_plain hplain

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedSat
