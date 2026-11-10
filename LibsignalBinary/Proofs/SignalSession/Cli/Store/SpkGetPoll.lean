/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.Sym

/-!
# `<SignedPreKeyFiles as SignedPreKeyStore>::get_signed_pre_key` Future Poll

Proves that `get_signed_pre_key::{closure#0}` (`spkGetPoll_fnOff`, `0x180`-byte frame, 88-byte sret)
formats the decimal key ID, reads the key file via `Dir::get`, decodes nonempty payloads via
`decode_kyber_pre_key` (`decodeSignedPreKeySpec`), drops the eagerly constructed
`InvalidSignedPreKeyId` word on `Ok`, frees temporary buffers, sets the future state byte to `1`,
and satisfies `spkGetPollSpec`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- The `get_signed_pre_key` poll meets `spkGetPollSpec rd pathOk A img stk` at any 4
KiB-aligned image base, given the hook contracts, `decimal`, `Dir::get`, `decode_kyber_pre_key`
(as the signed decoder) and the payload-free SPE drop. -/
theorem spkGetPoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec A img))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName)
      (spkGetPollSpec rd pathOk A img stk) := by
  let _ := hb
  exact Helpers.spkGetPoll_of_inner
    (fun hhi => Helpers.spkGetPollInner_ok hC hDecimal hGet hDec hDrop hFs hhi) hstk

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll
