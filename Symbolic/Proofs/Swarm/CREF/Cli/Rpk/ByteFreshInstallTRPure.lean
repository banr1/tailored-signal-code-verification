/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Refinement.RecordBytesBridge
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Receiver-Chain Ratchet-Key Correspondence under `StateRel`

Proves `senderRatchetKey_of_mem_recv_of_stateRel_tr`: under `StateRel`, every model receive
chain `c ∈ st.recv` has a matching concrete `ReceiverChain` in `(ratchetStateOf s.state).receiverChains`
whose `senderRatchetKey` equals `vec32 (gamma interpretation S g c.ratchetKey)`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR

cref_open

open DY.Libsignal.TripleRatchet (RecvChain findRecvChain)
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF.CliPure.TR
open CryptoGames.LibsignalSession (PublicKey ReceiverChain RatchetState)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoProofLib.Refinement (ExternInterpretation)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Proofs.libsignal.RngG.R3 (ratchetStateOf)
open Proofs.libsignal.RngG.CliPure.R3 (eraseRecvChain recChainOfErased findReceiverChainKey_ok_none publicKey_eq_vec32_of_toList_eq)

local notation "SpqrSem_bfitrp26f" => OpaqueSymbolSemantics

private theorem receiverChains_of_stateRel_bfi
    {interpretation : ExternInterpretation} {S : SpqrSem_bfitrp26f} {g : Ghost}
    {st : TRState} {s : Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s)) :
    (s.state.receiverChains.map eraseRecvChain).map recChainOfErased =
      (sessionOf interpretation (gamma interpretation S g) st).receiverChains := by
  have heq : eraseSkipped (eraseUnmodelled (sessionToSessionRec s)) =
      sessionOf interpretation (gamma interpretation S g) st := by
    simpa [StateRel, sessionToRecordRec] using hrel
  rw [← congrArg SessionRec.receiverChains heq]
  simp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, List.map_map]; rfl

theorem senderRatchetKey_of_mem_recv_of_stateRel_tr
    (interpretation : ExternInterpretation) (S : SpqrSem_bfitrp26f) (g : Ghost)
    {st : TRState} {s : Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    {c : RecvChain} (hc : c ∈ st.recv) :
    ∃ rc ∈ (ratchetStateOf s.state).receiverChains,
      rc.senderRatchetKey = ⟨vec32 (gamma interpretation S g c.ratchetKey)⟩ := by
  have hmap := congrArg (List.map ChainRec.senderRatchetKey) (receiverChains_of_stateRel_bfi hrel)
  simp only [sessionOf, List.map_map, Function.comp_def, recChainOfErased, eraseRecvChain,
    PublicKey.serialize, CryptoGames.LibsignalSession.djbType, serializedKey, ecKey] at hmap
  have hmem : (0x05#8 :: gamma interpretation S g c.ratchetKey) ∈
      List.map (fun c => 0x05#8 :: gamma interpretation S g c.ratchetKey) st.recv :=
    List.mem_map_of_mem hc
  rw [← hmap] at hmem
  obtain ⟨rc, hrcMem, hrcEq⟩ := List.mem_map.mp hmem
  have htoList : rc.senderRatchetKey.bytes.toList = gamma interpretation S g c.ratchetKey :=
    (List.cons.inj hrcEq).2
  exact ⟨rc, hrcMem, (publicKey_eq_vec32_of_toList_eq htoList).1⟩

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

namespace Symbolic.Swarm.CREF.CliPure.TR.G1
open Symbolic.Swarm.CREF.TR

cref_open

open DY.Libsignal.TripleRatchet (RecvChain findRecvChain)
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF.CliPure.TR
open CryptoGames.LibsignalSession (PublicKey ReceiverChain RatchetState)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoProofLib.Refinement (ExternInterpretation)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Proofs.libsignal.RngG.R3 (ratchetStateOf)
open Proofs.libsignal.RngG.CliPure.R3 (eraseRecvChain findReceiverChainKey_ok_none)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep (senderRatchetKey_of_mem_recv_of_stateRel_tr)

local notation "SpqrSem_bfitrp26f" => OpaqueSymbolSemantics

end Symbolic.Swarm.CREF.CliPure.TR.G1

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
