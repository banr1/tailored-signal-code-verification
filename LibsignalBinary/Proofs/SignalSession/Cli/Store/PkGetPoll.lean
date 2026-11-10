/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Sym

/-!
# `<OneTimePreKeyFiles as PreKeyStore>::get_pre_key` Future Poll

Proves that `get_pre_key::{closure#0}` (`pkGetPoll_fnOff`, `0x100`-byte frame, 56-byte sret)
formats the decimal key ID, reads the key file via `Dir::get`, decodes nonempty payloads with
`PreKeyRecord::deserialize` (dropping the eagerly constructed `InvalidPreKeyId` word on `Ok`),
frees temporary buffers, sets the future state byte to `1`, and satisfies `pkGetPollSpec`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- The `get_pre_key` poll meets `pkGetPollSpec rd pathOk A img stk` at any 4 KiB-aligned
image base, given the hook contracts, `decimal`, `Dir::get`, `PreKeyRecord::deserialize` and the
payload-free SPE drop. -/
theorem pkGetPoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
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
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName)
      (pkGetPollSpec rd pathOk A img stk) := by
  let _ := hb
  exact Helpers.pkGetPoll_of_inner
    (calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)))
    (fun hhi => Helpers.pkGetPollInner_ok hC hDecimal hGet hDec hDrop hFs hhi)
    hstk

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll
