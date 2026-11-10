/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewFs -- shake: keep

/-!
# PQXDH Directory Invariant Re-Exports for Fresh Pre-Key Receive

Re-exports `DirInvBridge` directory invariants and specializes identity-secret length and
one-time pre-key usage characterizations at `r.bob`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF secretBytes)
open DY.Libsignal.Composed.Refinement.Cli
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)
open Symbolic.Swarm.CREF.Cli (PqPartyInv)

theorem rpkNew_secretBytes_0_length {r : ProtocolSetup} (hr : ProtocolSetupWF r) :
    (secretBytes r 0).length = 32 :=
  Symbolic.Swarm.CREF.Cli.secretBytes_0_length hr

theorem rpkNew_opkUsed_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {t : CliTurn} {stB : PqParty}
    (hne : r.alice ≠ r.bob) (hB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob)) :
    (r.withOpk = false → t.opkUsed r = false) ∧
    (r.withOpk = true →
      (t.opkUsed r = false ↔ stB.oneTime = [(r.opkId, some (bytesToVec 32 (secretBytes r 6)))]) ∧
      (t.opkUsed r = true ↔ stB.oneTime = [(r.opkId, none)])) :=
  Symbolic.Swarm.CREF.Cli.opkUsed_of_pqPartyInv hne hB

end Symbolic.Swarm.CREF.Cli.Slots
