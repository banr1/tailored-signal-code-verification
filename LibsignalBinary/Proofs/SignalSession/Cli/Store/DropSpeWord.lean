/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWord.Sym

/-!
# `drop_glue::<SignalProtocolError>` on Payload-Free Variants

Verifies the CLI crate's `drop_glue::<SignalProtocolError> [local#4]` against `dropSpeWordSpec`
for payload-free `InvalidPreKeyId` (`speWord 13`) and `InvalidSignedPreKeyId` (`speWord 14`)
variants via the `.rodata` jump table `Getters.speJumpTable`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.DropSpeWord

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- The CLI crate's `drop_glue::<SignalProtocolError>` meets `dropSpeWordSpec` on
`InvalidPreKeyId` / `InvalidSignedPreKeyId`. -/
theorem dropSpeWord_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img) := by
  exact Helpers.dropSpeWord_ok_main himg hA

end CryptoVerification.SignalSession.Cli.Store.DropSpeWord
