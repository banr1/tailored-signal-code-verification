/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Exec

/-!
# Verification of `signal_session::stores::decimal`

Verifies `signal_session::stores::decimal` (`0x50`-byte frame), which formats a `u32` in base 10
(`decimalText`) via recursion on `n / 10` (at most 10 nested frames, stack budget
`10 * 0x50 + resStack`) followed by `do_reserve_and_handle` and pushing `'0' + (n % 10)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Decimal

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `decimal` satisfies `decimalSpec A img stk` at any 4 KiB-aligned image base, given
`do_reserve_and_handle` with stack budget `resStack`. -/
theorem decimal_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 10 * 0x50 + resStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img stk) := by
  exact Helpers.decimal_ok_main hRes hstk hb

end CryptoVerification.SignalSession.Cli.Decimal
