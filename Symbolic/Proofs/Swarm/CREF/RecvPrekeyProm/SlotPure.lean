/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.EntryPure

/-!
# Promote Pre-Key Accept Step

Proves `slot_rpk_prom_accept_pure`, stepping `CReadyPure` across an accepting, non-colliding
`.preKey` promote call by supplying `prom_noDrawOK_proved` and `prom_versionOK_proved`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)

/-- Advances `CReadyPure` across an accepting, non-colliding `.preKey` promote call. -/
theorem slot_rpk_prom_accept_pure
    (interpretation : ExternInterpretation)
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (r : ProtocolSetup) (hwf : ProtocolSetupWF r) (S : OpaqueSymbolSemantics)
    (hS : SemReady interpretation r S) (hSeq : S = compSemOf interpretation r)
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hcol : ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt)) :
    (∃ g ms, MatchedPrefix interpretation r S who g ms (acc ++ promAccBlk b mid pt)) ∧
    (ok j = true →
      CReadyPure interpretation r S who ok
        (fun q => if q = r.bob then some sm.state else e'.records q)
        e'.sent e'.accepted e'.opkUsed (acc ++ promAccBlk b mid pt)) :=
  cEntry_recvPrekey_prom_of_noDraw_and_ver interpretation hext r hwf S hS hSeq
    prom_noDrawOK_proved prom_versionOK_proved hC hcol

end Symbolic.Swarm.CREF.CliPure
