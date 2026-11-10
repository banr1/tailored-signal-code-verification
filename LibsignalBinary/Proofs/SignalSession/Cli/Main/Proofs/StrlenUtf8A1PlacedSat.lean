/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1Placed -- proof-setup: allow-public-import

/-!
# `HookSat` Sibling of `StrlenUtf8A1Placed.fromUtf8Ascii_ok_placed` (`StrlenUtf8A1PlacedSat`)

Replaces `hext : H lsFromUtf8Sym = some (fromUtf8Hook err)` (and drops the unused `err`
parameter) in `fromUtf8Ascii_ok_placed` (`StrlenUtf8A1Placed.lean:62`) with
`hext : HookSat H lsFromUtf8Sym (fromUtf8AsciiSpec hookStack)`, plus the exact-hook coercion
`hookSat_fromUtf8_of_eq`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1PlacedSat

open Arm64 ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.SignalSession (fromUtf8Hook lsFromUtf8Sym)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (fromUtf8AsciiSpec fromUtf8Hook_ok)

/-- Coercion from `H lsFromUtf8Sym = some (fromUtf8Hook err)` to
    `HookSat H lsFromUtf8Sym (fromUtf8AsciiSpec hookStack)`. -/
theorem hookSat_fromUtf8_of_eq {H : LibsignalHooks} (hookStack : Nat)
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hext : H lsFromUtf8Sym = some (fromUtf8Hook err)) :
    HookSat H lsFromUtf8Sym (fromUtf8AsciiSpec hookStack) :=
  ⟨fromUtf8Hook err, hext, fromUtf8Hook_ok hookStack err⟩

/-- `HookSat` sibling of `fromUtf8Ascii_ok_placed` (`StrlenUtf8A1Placed.lean:62`), dropping the
    unused `err` parameter. -/
theorem fromUtf8Ascii_ok_placed_sat [LibsignalPlacement] {H : LibsignalHooks} {hookStack : Nat}
    (hext : HookSat H lsFromUtf8Sym (fromUtf8AsciiSpec hookStack)) :
    subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hext (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1PlacedSat
