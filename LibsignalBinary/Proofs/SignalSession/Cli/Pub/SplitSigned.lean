/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.OkPath

/-!
# Subroutine Contract for `signal_session::public::split_signed`

Verifies `splitSignedSpec` for `signal_session::public::split_signed` (`0x60`-byte stack frame):
calls `split_id`, propagates any 48-byte `Err` to `sret`, returns a 14-byte `"malformed file"`
`SignalProtocolError` (`"bundle"`) when `rest.length < 64`, and otherwise drops the eager error
before splitting `rest` into `(key, sig)` of lengths `(rest.length - 64, 64)`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.SplitSigned

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- `split_signed` satisfies `splitSignedSpec` from its callee contracts. -/
theorem splitSigned_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {splitStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hSplit : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName)
      (splitIdSpec A img splitStk))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img))
    (hstk : 0x60 + max splitStk dropSpeStackX ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitSignedName)
      (splitSignedSpec A img stk) := by
  exact Helpers.splitSigned_ok_of_loads hC himg hSplit hDrop hstk hb

end CryptoVerification.SignalSession.Cli.SplitSigned
