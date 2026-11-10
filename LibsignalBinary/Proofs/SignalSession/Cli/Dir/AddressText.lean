/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Steps

/-!
# Verification of `signal_session::stores::address_text`

Verifies `signal_session::stores::address_text` (`0x70`-byte frame), which formats a
`ProtocolAddress` as `name ++ "." ++ decimal(device)` (`addressText g.val`) by cloning the owned
name slice, reserving and appending `"."`, formatting the zero-extended device byte via `decimal`,
appending the decimal string, and tail-deallocating the temporary `decimal` buffer.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.AddressText

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `address_text` satisfies `addrTextSpec A img stk` at any 4 KiB-aligned image base, given
allocator/memcpy contracts, `do_reserve_and_handle` (stack `resStack`), and `decimal` (stack `decStk`). -/
theorem addressText_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack decStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hstk : 0x70 + max (max resStack extHookStack) decStk ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img stk) := by
  let _ := hb
  exact Helpers.addrText_ok_impl hC hRes hDec hstk

end CryptoVerification.SignalSession.Cli.AddressText
