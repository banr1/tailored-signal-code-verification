/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SR.ModelW
public import Symbolic.Specifications.Concrete.ExternInterpretation

/-!
# Extern-interpretation instance of whole-message AES

Constructs the `AesW` instance `interpW` backed by `aesCbcEncryptSymbol` and `aesCbcDecryptSymbol`
of an `ExternInterpretation`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.SR

open CryptoVerification
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

def interpW (interpretation : CryptoProofLib.Refinement.ExternInterpretation) : AesW where
  enc := fun k iv pt =>
    (interpretation DY.Libsignal.Refinement.aesCbcEncryptSymbol
      [pt, HMAC.keyToBytes32 k, CBC.blockToBytesLE iv]).getD []
  dec := fun k iv ct =>
    interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [ct, HMAC.keyToBytes32 k, CBC.blockToBytesLE iv]

end Proofs.libsignal.SR
