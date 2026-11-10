/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem

/-!
# Error-Arm Layout Bridge for `encResAt`

Proves that `encResAt A r (.error e)` for any non-store error `e` exposes `errTag` at `r`, an owned
48-byte `SignalProtocolError` at `r + 8`, and a 192-byte trailing region at `r + 56`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose

set_option linter.unusedVariables false in
/-- Decomposes `encResAt A r (.error e)` for `e ≠ .store ()` into `errTag` at `r`, an owned
`SignalProtocolError` (`SpeOwned`) at `r + 8`, and a 192-byte trailing region at `r + 56`. -/
theorem encResAt_err_owned (A : RustAlloc) (r : BitVec 64)
    (e : ApiError AddrVal Unit) (he : e ≠ .store ()) :
    encResAt A r (.error e) ⊢
      (r ↦₆₄ errTag) ∗ (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (r + 8#64) k) ∗
        memRegion (r + 56#64) 192 :=
  Entails.refl _

end CryptoVerification.SignalSession.Cli.RunProofs
