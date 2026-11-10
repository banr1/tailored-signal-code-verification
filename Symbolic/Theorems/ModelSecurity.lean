/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import Symbolic.Proofs.TopLevelHelpers.Composed.FS
import Symbolic.Proofs.TopLevelHelpers.Composed.Handshake
import Symbolic.Proofs.TopLevelHelpers.Composed.PCS

/-!
# Protocol Security Theorems in the Composed Symbolic Model

**Trusted: the statement.**

Proves the ten symbolic security properties (`Symbolic/Specifications/Security/Model.lean`) over
every reachable trace of the composed `PQXDH ∘ SPQR ∘ Triple Ratchet` DyLean model
(`Symbolic/Specifications/Model/Instance.lean`), with unbounded sessions and participants, optional
one-time prekeys, and dynamic state and primitive compromises:
- **Ratchet security** (`forward_secrecy`, `post_compromise_security`), extending Cheval, Jacomme &
  Richards (IEEE S&P 2026) to the composed protocol from message 0 onward.
- **Handshake security** (`alice_initiator_secrecy`, `bob_responder_secrecy`, `authentication`, and
  five corollaries), lifting Theorems 7–9 and Theorem 1 of Bhargavan et al. (USENIX Security 2024)
  into the composed protocol with per-block session-state leak excuses (`SessionStateExposed`).

Role names follow `libsignal`: Alice fetches Bob's prekey bundle and sends first (`AliceDone`),
while Bob publishes the bundle and receives first (`BobDone`). `Symbolic/Theorems/Security.lean`
lifts all ten theorems to the compiled binary via `Symbolic/Theorems/RefinementPreservation.lean`.
-/

@[expose] public section

namespace Proven.ForwardSecrecy

open DY.Libsignal.Composed

/-- Forward secrecy (`Security.ForwardSecrecy`; Cheval et al., 2026, Table 2): every message key
used on a reachable trace is unknown to the attacker unless that message key, an ancestor chain key,
or an ancestor root key (including an initial root or chain key whose producing handshakes are all
excused) was compromised. Exposing SPQR state (`ExposedSpqr`) does not excuse message-key recovery. -/
theorem forward_secrecy : Security.ForwardSecrecy :=
  Symbolic.Proofs.TopLevelHelpers.Composed.FS.forward_secrecy

end Proven.ForwardSecrecy

namespace Proven.PostCompromiseSecurity

open DY.Libsignal.Composed

/-- Post-compromise security (`Security.PostCompromiseSecurity`; Cheval et al., 2026, Table 2): for
any message key derived at or after a DH ratchet step between honest DH keys, an earlier root-key
compromise excuses attacker knowledge only if one of the two healing DH secrets was compromised or a
post-step root, chain, or message key was leaked. -/
theorem post_compromise_security : Security.PostCompromiseSecurity :=
  Symbolic.Proofs.TopLevelHelpers.Composed.PCS.post_compromise_security

end Proven.PostCompromiseSecurity

namespace Proven.Handshake

open DY.Libsignal.Composed

/-- Secrecy of Alice's PQXDH handshake keys (`Security.AliceInitiatorSecrecy`; Bhargavan et al.,
2024, Theorem 7): when Alice (`AliceDone`) initiates a session, each output block (`rk`, `ck`,
`pqr`) is unknown to the attacker unless `AliceHandshakeWasCompromised` holds or that block was
leaked from session state (`SessionStateExposed`). -/
theorem alice_initiator_secrecy : Security.AliceInitiatorSecrecy :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.alice_initiator_secrecy

/-- Secrecy of Bob's PQXDH handshake keys (`Security.BobResponderSecrecy`; Bhargavan et al., 2024,
Theorem 9): when Bob (`BobDone`) accepts a session from Alice, each output block (`rk`, `ck`, `pqr`)
is unknown to the attacker unless `BobHandshakeWasCompromised` holds or that block was leaked from
session state (`SessionStateExposed`). -/
theorem bob_responder_secrecy : Security.BobResponderSecrecy :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.bob_responder_secrecy

/-- Handshake authentication of Alice to Bob (`Security.Authentication`; Bhargavan et al., 2024,
Theorem 8): whenever Bob (`BobDone`) accepts a handshake from Alice, Alice previously completed a
matching handshake (`ResponderSessionAgreement`, agreeing on `pqpk` and on `spk` and `opk` up to
canonical X25519 decoding) unless Alice's identity key, Bob's session signed prekey, or DH was
compromised beforehand. -/
theorem authentication : Security.Authentication :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.authentication

/-- Peer authentication (`Security.PeerAuthentication`; Bhargavan et al., 2024, Theorem 1): if Bob
accepts a handshake from Alice and neither Alice's identity key, Bob's session signed prekey, nor DH
was compromised beforehand, then Alice previously completed a matching handshake. -/
theorem peer_authentication : Security.PeerAuthentication :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.peer_authentication

/-- Handshake forward secrecy (`Security.HandshakeForwardSecrecy`; Bhargavan et al., 2024,
Theorem 1): compromising either party's identity key after handshake completion reveals no unexposed
handshake key block (even if one-time prekeys are compromised), provided Bob's session signed and
Kyber prekeys are uncompromised and DH and KEM remain unbroken. -/
theorem handshake_forward_secrecy : Security.HandshakeForwardSecrecy :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.handshake_forward_secrecy

/-- Key-compromise-impersonation resistance (`Security.KCIResistance`; Bhargavan et al., 2024,
Theorem 1): compromising Bob's identity key does not enable impersonating Alice to Bob unless
Alice's identity key, Bob's session signed prekey, or DH was compromised before Bob accepted. -/
theorem kci_resistance : Security.KCIResistance :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.kci_resistance

/-- Session independence (`Security.SessionIndependence`; Bhargavan et al., 2024, Theorem 1):
compromising signed, Kyber, or one-time prekeys outside the target session reveals no unexposed
handshake key block when both parties' identity keys are uncompromised and DH and KEM remain
unbroken. -/
theorem session_independence : Security.SessionIndependence :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.session_independence

/-- Harvest-now-decrypt-later resistance (`Security.HNDLResistance`; Bhargavan et al., 2024,
Theorem 1): breaking classical DH (`BrokenDH`) after handshake completion reveals no unexposed
handshake key block when KEM hardness holds and the session's identity, signed, and Kyber prekeys
are uncompromised. -/
theorem hndl_resistance : Security.HNDLResistance :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.hndl_resistance

end Proven.Handshake
