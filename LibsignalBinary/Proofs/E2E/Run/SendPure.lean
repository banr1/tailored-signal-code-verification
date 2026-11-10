/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Run
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E

def canonChainGhostOf (rc : ReceiverChain) : ChainGhost where
  srk   := ⟨0#64, 0#64, rc.senderRatchetKey.serialize⟩
  priv  := ⟨0#64, 0#64, []⟩
  mkCap := 0#64
  mkPtr := 0#64
  keys  := []
  ck    := ⟨0#64, 0#64⟩

def canonGhostOf (s : Session (List (BitVec 8))) : SessionGhost where
  localIk   := ⟨0#64, 0#64, s.state.localIdentity.serialize⟩
  remoteIk  := ⟨0#64, 0#64, (s.state.remoteIdentity.map IdentityKey.serialize).getD []⟩
  root      := ⟨0#64, 0#64⟩
  chainsCap := 0#64
  chainsPtr := 0#64
  chains    := s.state.receiverChains.map canonChainGhostOf
  alice     := ⟨0#64, 0#64, []⟩
  pq        := ⟨0#64, 0#64⟩
  sender    := s.state.senderChain.map fun sc =>
    ⟨⟨0#64, 0#64, sc.ratchetKey.publicKey.serialize⟩,
     ⟨0#64, 0#64, sc.ratchetKey.privateKey.bytes.toList⟩,
     0#64, 0#64, ⟨0#64, 0#64⟩⟩
  pending   := s.pendingPreKey.map fun p =>
    ⟨⟨0#64, 0#64, p.baseKey.serialize⟩, []⟩
  kyber     := none
  regIds    := []

private theorem canonChain_of_mem_zip_canonChainGhostOf :
    ∀ (cs : List ReceiverChain) (gc : ChainGhost × ReceiverChain),
      gc ∈ (cs.map canonChainGhostOf).zip cs → Record.Serialization.CanonChain gc
  | [], _, h => by simp at h
  | rc :: cs, gc, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, rfl⟩
    · exact canonChain_of_mem_zip_canonChainGhostOf cs gc h

theorem canonGhostOf_remoteIk (s : Session (List (BitVec 8))) :
    match s.state.remoteIdentity with
    | none => (canonGhostOf s).remoteIk.bytes = []
    | some ik => (canonGhostOf s).remoteIk.bytes = ik.serialize := by
  unfold canonGhostOf
  cases s.state.remoteIdentity <;> rfl

theorem canonGhostOf_canonSender (s : Session (List (BitVec 8))) :
    Record.Serialization.CanonSender (canonGhostOf s).sender s.state.senderChain := by
  unfold canonGhostOf Record.Serialization.CanonSender
  cases s.state.senderChain with
  | none => exact True.intro
  | some _ => exact ⟨rfl, rfl⟩

theorem canonGhostOf_sender (s : Session (List (BitVec 8))) :
    match (canonGhostOf s).sender, s.state.senderChain with
    | none, none => True
    | some sg, some sc => sg.srk.bytes = sc.ratchetKey.publicKey.serialize
    | _, _ => False := by
  unfold canonGhostOf
  cases s.state.senderChain with
  | none => exact True.intro
  | some _ => rfl

theorem canonGhostOf_canonPending (s : Session (List (BitVec 8))) :
    Record.Serialization.CanonPending (canonGhostOf s).pending s.pendingPreKey := by
  unfold canonGhostOf Record.Serialization.CanonPending
  cases s.pendingPreKey with
  | none => exact True.intro
  | some _ => rfl

theorem canonGhostOf_chains_srk_priv (s : Session (List (BitVec 8))) :
    ∀ cg ∈ (canonGhostOf s).chains, cg.srk.bytes.length = 33 ∧ cg.priv.bytes = [] := by
  intro cg hcg
  unfold canonGhostOf at hcg
  simp only [List.mem_map] at hcg
  rcases hcg with ⟨rc, _, rfl⟩
  exact ⟨PublicKey.serialize_length rc.senderRatchetKey, rfl⟩

theorem serializationCanonSession_canonGhostOf (s : Session (List (BitVec 8))) :
    Record.Serialization.CanonSession (canonGhostOf s) s :=
  ⟨rfl, rfl, canonGhostOf_canonSender s, List.length_map canonChainGhostOf,
   fun gc hgc => canonChain_of_mem_zip_canonChainGhostOf s.state.receiverChains gc hgc,
   canonGhostOf_canonPending s⟩

theorem encSession_length_le_encodeRecord (s : Session (List (BitVec 8))) :
    (Record.encSession s).length ≤ (Record.encodeRecord ⟨some s⟩).length := by
  unfold Record.encodeRecord Record.msgField Record.lenField
  dsimp only [Option.map_some]
  simp only [List.length_append]
  omega

end CryptoVerification.E2E.Run
