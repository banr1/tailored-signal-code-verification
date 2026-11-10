/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import Symbolic.Proofs.Swarm.COMPOSED.CompInv

/-!
# PQXDH Handshake Security in the Composed Protocol

Exports Bhargavan et al.'s Theorems 7-9 (`alice_initiator_secrecy`, `bob_responder_secrecy`,
`authentication`) for the composed protocol and derives the five Theorem 1 corollaries
(`peer_authentication`, `handshake_forward_secrecy`, `kci_resistance`, `session_independence`,
`hndl_resistance`) from them for `Symbolic.Theorems.Composed.ComposedHandshake`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Handshake

open DY DY.Libsignal.Composed
open DY.Libsignal.PQXDH (AliceInitiatorSecrecyQuery BobResponderSecrecyQuery AuthenticationQuery
  PeerAuthenticationQuery ForwardSecrecyQuery KCIQuery SessionIndependenceQuery HNDLQuery)

/-! ## Query-level Theorem 1 corollaries -/

section Corollaries

variable [DY.Libsignal.Composed.HasExecTrace] {tr : ExecTrace}

/-- Peer authentication (`PeerAuthenticationQuery`) follows from `AuthenticationQuery`. -/
theorem peerAuthentication_of_authentication (h : AuthenticationQuery tr) :
    PeerAuthenticationQuery tr :=
  fun b a ikB ikA spk pqpk opk ek ct keys i hBob hNoExc =>
    (h b a ikB ikA spk pqpk opk ek ct keys i hBob).resolve_right hNoExc

/-- Key-compromise-impersonation resistance (`KCIQuery`) follows from `AuthenticationQuery`,
since `HandshakeAuthWasCompromised` is independent of Bob's identity key. -/
theorem kci_of_authentication (h : AuthenticationQuery tr) : KCIQuery tr :=
  fun b a ikB ikA spk pqpk opk ek ct keys i hBob _hIkB hNoExc =>
    (h b a ikB ikA spk pqpk opk ek ct keys i hBob).resolve_right hNoExc

/-- Handshake forward secrecy (`ForwardSecrecyQuery`) follows from `AliceInitiatorSecrecyQuery`
and `BobResponderSecrecyQuery`. -/
theorem forwardSecrecy_of_secrecy {Knows}
    (h7 : AliceInitiatorSecrecyQuery tr Knows)
    (h9 : BobResponderSecrecyQuery tr Knows) :
    ForwardSecrecyQuery tr Knows := by
  intro a b ikA ikB spk pqpk opk keys i hDone hFS k hk hNotExp hKnows
  rcases hDone with ⟨ek, ct, hAlice⟩ | ⟨ek, ct, hBob⟩
  · rcases hFS with ⟨_hIkA, hIkB, hSpk, _hPqpk, hDH, _hKEM⟩
    rcases (h7 a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hKnows).resolve_right hNotExp with
      ⟨j, hj, hlt | ⟨hS, _⟩⟩ | ⟨j, hj, _⟩
    · exact Nat.lt_asymm hlt (hIkB j hj)
    · exact hSpk hS
    · exact hDH ⟨j, hj⟩
  · rcases hFS with ⟨hIkA, _hIkB, hSpk, _hPqpk, hDH, _hKEM⟩
    rcases (h9 b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hKnows).resolve_right hNotExp with
      (⟨j, hj, hlt⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨_, hS, _⟩ | ⟨hD, _⟩
    · exact Nat.lt_asymm hlt (hIkA j hj)
    · exact hSpk ⟨j, hj⟩
    · exact hDH ⟨j, hj⟩
    · exact hSpk hS
    · exact hDH hD

/-- Session independence (`SessionIndependenceQuery`) follows from `AliceInitiatorSecrecyQuery`
and `BobResponderSecrecyQuery`. -/
theorem sessionIndependence_of_secrecy {Knows}
    (h7 : AliceInitiatorSecrecyQuery tr Knows)
    (h9 : BobResponderSecrecyQuery tr Knows) :
    SessionIndependenceQuery tr Knows := by
  intro a b ikA ikB spk pqpk opk keys i hDone hSI k hk hNotExp hKnows
  rcases hDone with ⟨ek, ct, hAlice⟩ | ⟨ek, ct, hBob⟩
  · rcases hSI with ⟨_hIkA, hIkB, hDH, _hKEM, _hSpk, _hPqpk, _hOpk⟩
    rcases (h7 a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hKnows).resolve_right hNotExp with
      ⟨j, hj, _⟩ | ⟨j, hj, _⟩
    · exact hIkB ⟨j, hj⟩
    · exact hDH ⟨j, hj⟩
  · rcases hSI with ⟨hIkA, hIkB, hDH, _hKEM, hSpk, _hPqpk, _hOpk⟩
    rcases (h9 b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hKnows).resolve_right hNotExp with
      (⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨hI, _⟩ | ⟨hD, _⟩
    · exact hIkA ⟨j, hj⟩
    · exact hSpk spk ⟨j, hj⟩ rfl
    · exact hDH ⟨j, hj⟩
    · exact hIkB hI
    · exact hDH hD

/-- Harvest-now-decrypt-later resistance (`HNDLQuery`) follows from `AliceInitiatorSecrecyQuery`
and `BobResponderSecrecyQuery`. -/
theorem hndl_of_secrecy {Knows}
    (h7 : AliceInitiatorSecrecyQuery tr Knows)
    (h9 : BobResponderSecrecyQuery tr Knows) :
    HNDLQuery tr Knows := by
  intro a b ikA ikB spk pqpk opk keys i hDone hHNDL k hk hNotExp hKnows
  rcases hDone with ⟨ek, ct, hAlice⟩ | ⟨ek, ct, hBob⟩
  · rcases hHNDL with ⟨hDH, hKEM, _hIkA, hIkB, _hSpk, hPqpk⟩
    rcases (h7 a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hKnows).resolve_right hNotExp with
      ⟨j, hj, _⟩ | ⟨j, hj, hlt | hP | hK⟩
    · exact hIkB ⟨j, hj⟩
    · exact Nat.lt_asymm hlt (hDH j hj)
    · exact hPqpk hP
    · exact hKEM hK
  · rcases hHNDL with ⟨hDH, hKEM, hIkA, hIkB, hSpk, hPqpk⟩
    rcases (h9 b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hKnows).resolve_right hNotExp with
      (⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, hlt⟩) | ⟨hI, _⟩ | ⟨_, hP | hK⟩
    · exact hIkA ⟨j, hj⟩
    · exact hSpk ⟨j, hj⟩
    · exact Nat.lt_asymm hlt (hDH j hj)
    · exact hIkB hI
    · exact hPqpk hP
    · exact hKEM hK

end Corollaries

/-! ## Theorems 7-9 -/

/-- Theorem 7 (Alice initiator secrecy) in the composed protocol. -/
theorem alice_initiator_secrecy : Security.AliceInitiatorSecrecy :=
  Symbolic.Swarm.COMPOSED.CompInv.alice_initiator_secrecy

/-- Theorem 9 (Bob responder secrecy) in the composed protocol. -/
theorem bob_responder_secrecy : Security.BobResponderSecrecy :=
  Symbolic.Swarm.COMPOSED.CompInv.bob_responder_secrecy

/-- Theorem 8 (responder authentication) in the composed protocol. -/
theorem authentication : Security.Authentication :=
  Symbolic.Swarm.COMPOSED.CompInv.authentication

/-! ## Theorem 1 corollaries in the composed protocol -/

/-- Peer authentication (Theorem 1) in the whole protocol, from `authentication`. -/
theorem peer_authentication : Security.PeerAuthentication := fun _ h =>
  peerAuthentication_of_authentication (authentication _ h)

/-- Handshake forward secrecy (Theorem 1) in the whole protocol, from `alice_initiator_secrecy` and
`bob_responder_secrecy`. -/
theorem handshake_forward_secrecy : Security.HandshakeForwardSecrecy := fun _ h =>
  forwardSecrecy_of_secrecy (alice_initiator_secrecy _ h) (bob_responder_secrecy _ h)

/-- Key-compromise-impersonation resistance (Theorem 1) in the whole protocol, from
`authentication`. -/
theorem kci_resistance : Security.KCIResistance := fun _ h =>
  kci_of_authentication (authentication _ h)

/-- Session independence (Theorem 1) in the whole protocol, from `alice_initiator_secrecy` and
`bob_responder_secrecy`. -/
theorem session_independence : Security.SessionIndependence := fun _ h =>
  sessionIndependence_of_secrecy (alice_initiator_secrecy _ h) (bob_responder_secrecy _ h)

/-- Harvest-now-decrypt-later resistance (Theorem 1) in the whole protocol, from
`alice_initiator_secrecy` and `bob_responder_secrecy`. -/
theorem hndl_resistance : Security.HNDLResistance := fun _ h =>
  hndl_of_secrecy (alice_initiator_secrecy _ h) (bob_responder_secrecy _ h)

end Symbolic.Proofs.TopLevelHelpers.Composed.Handshake
