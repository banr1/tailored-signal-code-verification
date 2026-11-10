/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.ErrPath

/-!
# Subroutine Contract for `signal_session::public::split_id`

Verifies `splitIdSpec` for `signal_session::public::split_id` (`0x60`-byte stack frame): eagerly
allocates a 14-byte `"malformed file"` `SignalProtocolError` (`"bundle"`), returns it as `Err` when
`file.length < 4`, and otherwise drops it via `drop_glue::<SignalProtocolError>` before reading the
4-byte little-endian `u32` ID and returning `Ok((id, rest))`.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.SplitId

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- `split_id` satisfies `splitIdSpec` from its callee contracts. -/
theorem splitId_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img))
    (hstk : 0x60 + dropSpeStackX ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName)
      (splitIdSpec A img stk) := by
  exact Helpers.splitId_ok_of_loads himg hC hDrop hstk

end CryptoVerification.SignalSession.Cli.SplitId
