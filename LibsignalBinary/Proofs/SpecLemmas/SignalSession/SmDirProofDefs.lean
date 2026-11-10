/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.SmDir
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi

/-!
# Proof-Side Session-Model CLI Specification (`CliSpecE`)

Defines the reachable classical Double Ratchet (`spqrOffSessionParams`) CLI refinement
predicate `CliSpecE` over `LibsignalBinary.Specifications.SignalSession.SmDir`.
-/

@[expose] public section

set_option autoImplicit false
namespace CryptoVerification.SignalSession
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchetRepr

/-- `run` refines the classical session model (`smSendModel` / `smRecvModel`) on every
state `g` reachable under `spqrOffSessionParams C` for messages and ciphertexts shorter
than `2 ^ 32` bytes (matching `shortCiphertext` in DEV-M1), exiting `2` above
`stdinCapBytes` (`2 ^ 20`), exiting `1` on `send` above `maxPlaintextBytes` (`10 ^ 6`),
and matching `observe` otherwise. -/
def CliSpecE (run : CliRun) (C : Crypto) : Prop :=
  (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams C) g → m.length < 2 ^ 32 →
    run (smSendInputs g m) =
      if m.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (smSendInputs g m).files))
      else if m.length > maxPlaintextBytes then
        some (.exited 1 [] (filesOf (smSendInputs g m).files))
      else
        some (observe (smSendInputs g m).files (smSendModel C g m))) ∧
  (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams C) g →
    c.length < 2 ^ 32 →
    run (smRecvInputs g c rc) =
      if (msgTypeWhisper :: c).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (smRecvInputs g c rc).files))
      else
        some (observe (smRecvInputs g c rc).files (smRecvModel C g c rc)))

end CryptoVerification.SignalSession
