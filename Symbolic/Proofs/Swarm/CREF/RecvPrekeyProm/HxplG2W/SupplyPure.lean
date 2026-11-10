/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.IfacePure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SupplyPkPure
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# `PromRawCtxSupply` Assembly

Assembles `PromRawCtxSupply` at every clean explanation of an accepting, non-colliding promote call
from `CHist`, `TRRecvFreshAll`, `prom_g1cAttackerBuiltSeedExcl'_of_matchedPrefix`, and the
`NoRatchet` and `Skipped` ratchet-key dispatches.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Asserts `P g ms acc` at every clean explanation `(g, ms)` of `acc` on an accepting,
non-colliding promote call. -/
def PromCtxAt (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (P : Ghost → List Move → List MachineEvent → Prop) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt) →
    ∀ g ms, CleanBy interpretation r S who ok g ms acc → P g ms acc

theorem prom_cHist_at_clean
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    {g : Ghost} {ms : List Move} (hc : CleanBy interpretation r S who ok g ms acc) :
    CHist interpretation r S g ms :=
  hC.entry.ready.2.1.hist hc

theorem prom_recvAtFacts_at_clean
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    {g : Ghost} {ms : List Move} (hc : CleanBy interpretation r S who ok g ms acc)
    (hfresh : TR.TRRecvFreshAll r ms) :
    TR.RecvDecStepAt.RecvAtFacts interpretation r S g ms := by
  obtain ⟨hlen, hlow, hbf, hh⟩ := prom_cHist_at_clean hC hc
  exact ⟨hlen, hlow, hbf, hh, hfresh⟩

/-- Constructs `PromRawCtxSupply` from `TRRecvFreshAll` and the `NoRatchet` and `Skipped`
ratchet-key dispatches. -/
theorem promRawCtxSupply_of
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hfresh : PromCtxAt interpretation r S who ok fun _ ms _ => TR.TRRecvFreshAll r ms)
    (hPkNR : PromCtxAt interpretation r S who ok fun g ms acc =>
      TR.RecvDecStepAt.NoRatchetPkDispatchAt interpretation r S g ms acc)
    (hPkSk : PromCtxAt interpretation r S who ok fun g ms acc =>
      SkippedPkDispatchAtK interpretation r S g ms acc) :
    PromRawCtxSupply interpretation r S who ok := by
  intro j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol g ms hc
  exact
    { atF := prom_recvAtFacts_at_clean hC hc
        (hfresh j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol g ms hc)
      pkNR := hPkNR j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol g ms hc
      pkSk := hPkSk j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol g ms hc
      abs' := prom_g1cAttackerBuiltSeedExcl'_of_matchedPrefix hc.matched }

end Symbolic.Swarm.CREF.CliPure
