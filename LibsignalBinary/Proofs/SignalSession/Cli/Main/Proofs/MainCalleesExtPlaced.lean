/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainAllocExtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainStrlenAddrExtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainIoExtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.Library.CallInv

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Placed `MainCalleesBlk617` Bundle from `CliExternsOk`

Defines `Y_ext` via `wrapExtIo` and derives all `MainCalleesBlk617` fields on Block `617` from
`CliExternsOk P A ext`.
-/
namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Image-stub extern table pairing with `Z := Rust.withPanics (cliExternsWith ext)` via `wrapExtIo`. -/
noncomputable def Y_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    String → Option (State → State) :=
  Rust.withPanics (cliExternsWith (wrapExtIo img ext))

theorem Y_ext_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    Y_ext img ext = withCliPanics (wrapExtIo img ext) :=
  withPanics_withCliPanics (wrapExtIo img ext)

theorem Y_ext_isSome_eq (img : Obj.Image) (ext : String → Option (State → State)) (n : String) :
    (Y_ext img ext n).isSome = (Rust.withPanics (cliExternsWith ext) n).isSome := by
  rw [Y_ext_eq, show cliExternsWith ext = withCliPanics ext from rfl, withPanics_withCliPanics]
  unfold withCliPanics wrapExtIo
  by_cases hp : isCliPanicSymbol n = true
  · simp [hp]
  · by_cases hio : n ∈ CliExt.ioNames <;> simp [hp, hio]

theorem Y_ext_agree_of_callInv {img : Obj.Image} {ext : String → Option (State → State)} :
    ∀ n fY s, Y_ext img ext n = some fY → img.CallInv s →
      ∃ fZ, Rust.withPanics (cliExternsWith ext) n = some fZ ∧ fZ s = fY s := by
  intro n fY s hY hinv
  rw [Y_ext_eq] at hY
  rw [show cliExternsWith ext = withCliPanics ext from rfl, withPanics_withCliPanics]
  unfold withCliPanics at hY ⊢
  by_cases hp : isCliPanicSymbol n = true
  · simp only [hp, ↓reduceIte, Option.some.injEq] at hY ⊢
    exact ⟨Rust.panicked, rfl, hY ▸ rfl⟩
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hY ⊢
    by_cases hio : n ∈ CliExt.ioNames
    · rw [wrapExtIo_io img ext hio, Option.map_eq_some_iff] at hY
      obtain ⟨fZ, hfZ, rfl⟩ := hY
      exact ⟨fZ, hfZ, (wrapIoHook_eq_of_symtab hinv.2).symm⟩
    · rw [wrapExtIo_not_io img ext hio] at hY
      exact ⟨fY, hY, rfl⟩

theorem Y_ext_of_panic {img : Obj.Image} {ext : String → Option (State → State)} {n : String}
    (hp : isCliPanicSymbol n = true := by decide) :
    Y_ext img ext n = some Rust.panicked := by
  rw [Y_ext_eq]; exact withCliPanics_of_isCliPanicSymbol_true _ hp

theorem Y_ext_of_not_io {img : Obj.Image} {ext : String → Option (State → State)} {n : String}
    (hp : isCliPanicSymbol n = false := by decide)
    (hio : n ∉ CliExt.ioNames := by simp [CliExt.ioNames]) :
    Y_ext img ext n = ext n := by
  rw [Y_ext_eq, withCliPanics_of_isCliPanicSymbol_false _ hp, wrapExtIo_not_io img ext hio]

theorem Y_ext_of_io {img : Obj.Image} {ext : String → Option (State → State)} {n : String}
    (hp : isCliPanicSymbol n = false := by decide)
    (hio : n ∈ CliExt.ioNames := by simp [CliExt.ioNames]) :
    Y_ext img ext n = (ext n).map (wrapIoHook img) := by
  rw [Y_ext_eq, withCliPanics_of_isCliPanicSymbol_false _ hp, wrapExtIo_io img ext hio]

/-- Bundled placed lookup obligations for all 15 `main` callees/hooks on `H : LibsignalHooks`. -/
structure ExtFullLookup (img : Obj.Image) (ext : String → Option (State → State))
    (H : LibsignalHooks) : Prop where
  alloc : ExtAllocLookup ext H
  strlenAddr : ExtStrlenAddrLookup ext H
  io : ExtIoLookup img ext H

/-- Placed analogue of `mainCallees_of_alloc_and_cliExternsOk` / `mainCallees_of_cliExternsOk` on
Block `617`, deriving all `MainCalleesBlk617` fields directly from `CliExternsOk P A ext`. -/
theorem mainCalleesBlk617_of_lookup [LibsignalPlacement]
    {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)} {H : LibsignalHooks}
    (hA : ExtAllocLookup ext H) (hS : ExtStrlenAddrLookup ext H) (hOk : CliExternsOk P A ext)
    (hookStack : Nat := cliHookStack)
    (hle : extHookStack ≤ hookStack := by decide) (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    MainCalleesBlk617 A H uuidTryParse hookStack cliResStack :=
  let hCF := allocContractsFsPlaced_of_lookup hA hOk
  { alloc := allocContractsXCliPlaced_of_lookup hA hOk
    allocFs := hCF
    strlen := strlen_placed_ok_of_hookSat hS.strlen hOk.strlen hle hmax
    fromUtf8 := fromUtf8Ascii_placed_ok_of_hookSat hS.fromUtf8 hOk.fromUtf8 hle hmax
    address := address_placed_ok_of_lookup hCF hS hOk cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2
    reserve16 := reserve16_placed_ok hCF cli_resStack_callees.2.1 hS.handleError
    reserve1 := reserve1_placed_ok hCF cli_resStack_callees.2.1 hS.handleError
    tryAllocateIn3 := tryAllocateIn3_placed_okFs hCF cli_resStack_callees.1 cli_resStack_callees.2.2.2
    handleErrorPanic :=
      (ls_externAt?_of_mem (prog := lsProg_617 H) (i := 617) (by decide)).trans hS.handleError }

theorem mainCalleesAndIo_of_fullLookup [LibsignalPlacement]
    {P : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {H : LibsignalHooks}
    (hal : img.base.toNat % 4 = 0) (hL : ExtFullLookup img ext H) (hOk : CliExternsOk P A ext)
    (hookStack : Nat := cliHookStack)
    (hle : extHookStack ≤ hookStack := by decide) (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    MainCalleesBlk617 A H uuidTryParse hookStack cliResStack ∧
      MainIoPlaced A H cliIo hookStack :=
  ⟨mainCalleesBlk617_of_lookup hL.alloc hL.strlenAddr hOk hookStack hle hmax,
   mainIoPlaced_of_lookup hal hL.io hOk hookStack hle hmax⟩

end CryptoVerification.SignalSession.Cli.MainHops
