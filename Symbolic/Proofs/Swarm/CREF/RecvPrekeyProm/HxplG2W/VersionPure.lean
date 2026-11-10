/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Promote Message-Version and Zero-RNG Obligations

Proves `PromVersionOK` (`prom_versionOK_proved`) and `PromNoDrawOK` (`prom_noDrawOK_proved`) for
accepting promote calls.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)

/-- Every accepting promote call (`PromAcceptCallBy₂`) parses an inner `SignalMessage` of version 4. -/
def PromVersionOK (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    pf.inner.messageVersion = 4#8

theorem prom_versionOK_proved {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} :
    PromVersionOK interpretation r S who ok := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ hC
  exact hC.ver

theorem prom_noDrawOK_proved {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} :
    PromNoDrawOK interpretation r S who ok := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hC
  exact hC.nodraw rfl

end Symbolic.Swarm.CREF.CliPure
