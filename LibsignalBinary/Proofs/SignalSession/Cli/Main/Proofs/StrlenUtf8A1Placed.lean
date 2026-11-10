/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Relocatable `strlen` and `from_utf8` Callee Contracts for `main`

Relocatable (`[LibsignalPlacement]`) subroutine contracts for `strlen` and
`core::str::converts::from_utf8` (ASCII) on Block `617`, discharging the corresponding fields of
`MainCalleesPlaced`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

theorem cliExternsPlaced_strlen (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "strlen" = some strlenHook :=
  main_cliExternsPlaced_row mmpl W
    (List.mem_append_right _ (List.mem_of_getElem? (i := 2) rfl))
    (by simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol])

theorem cliExternsPlaced_fromUtf8 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsFromUtf8Sym = some (fromUtf8Hook W.utf8Err) :=
  main_cliExternsPlaced_row mmpl W
    (List.mem_append_right _ (List.mem_of_getElem? (i := 6) rfl))
    (by simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol, lsFromUtf8Sym])

/-- `strlen` satisfies `withLsRoCl lsmpl (strlenSpec hookStack)` at `lsρ "strlen"` on Block `617`. -/
theorem strlen_ok_placed [LibsignalPlacement] {H : LibsignalHooks} {hookStack : Nat}
    (hext : H "strlen" = some strlenHook) :
    subroutine_ok (lsProg_617 H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpec hookStack)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨strlenHook, hext, strlenHook_ok hookStack⟩ (by decide)

/-- `core::str::converts::from_utf8` satisfies `withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack)` at `lsρ lsFromUtf8Sym` on Block `617`. -/
theorem fromUtf8Ascii_ok_placed [LibsignalPlacement] {H : LibsignalHooks} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hext : H lsFromUtf8Sym = some (fromUtf8Hook err)) :
    subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨fromUtf8Hook err, hext, fromUtf8Hook_ok hookStack err⟩ (by decide)

theorem strlen_ok_cliExterns_placed [LibsignalPlacement] {hookStack : Nat}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpec hookStack)) :=
  strlen_ok_placed (cliExternsPlaced_strlen mmpl W)

theorem fromUtf8Ascii_ok_cliExterns_placed [LibsignalPlacement] {hookStack : Nat}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack)) :=
  fromUtf8Ascii_ok_placed (err := W.utf8Err) (cliExternsPlaced_fromUtf8 mmpl W)

end CryptoVerification.SignalSession.Cli.MainHops
