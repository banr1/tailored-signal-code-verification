/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# Whisper and Pre-Key Wire Tag Disjointness

Proves `pqRecvWhisper_wirePrekey_false`, ruling out `InputsEquiv` between whisper and pre-key
`pqRecvInputs` calls.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli.SDet

open DY.Libsignal (HwBytes)
open CryptoVerification.E2E (PEParams wireWhisper wirePrekey)
open CryptoVerification.SignalSession

theorem pqRecvWhisper_wirePrekey_false {P : PEParams} {st₀ st₁ : PqParty}
    {body₀ body₁ : HwBytes} {rc₀ rc₁ : BitVec 256}
    (h : InputsEquiv (pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
                     (pqRecvInputs P st₁ (wirePrekey :: body₁) rc₁)) : False := by
  have h0 : wireWhisper = wirePrekey := (List.cons.inj h.2.2.1).1
  revert h0; decide

end DY.Libsignal.Composed.Refinement.Cli.SDet
