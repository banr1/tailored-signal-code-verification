/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model

/-!
# Comparator challenge: model security (`Symbolic/Theorems/ModelSecurity.lean`)

**Trusted: the statements.** Each theorem below has the same name and the same statement, byte for
byte, as the theorem of `Symbolic/Theorems/ModelSecurity.lean`, with `sorry` as its proof. It
imports only the specification module that `ModelSecurity.lean` imports publicly. See
`comparator/README.md`.
-/

@[expose] public section

namespace Proven.ForwardSecrecy

open DY.Libsignal.Composed

theorem forward_secrecy : Security.ForwardSecrecy :=
  sorry

end Proven.ForwardSecrecy

namespace Proven.PostCompromiseSecurity

open DY.Libsignal.Composed

theorem post_compromise_security : Security.PostCompromiseSecurity :=
  sorry

end Proven.PostCompromiseSecurity

namespace Proven.Handshake

open DY.Libsignal.Composed

theorem alice_initiator_secrecy : Security.AliceInitiatorSecrecy :=
  sorry

theorem bob_responder_secrecy : Security.BobResponderSecrecy :=
  sorry

theorem authentication : Security.Authentication :=
  sorry

theorem peer_authentication : Security.PeerAuthentication :=
  sorry

theorem handshake_forward_secrecy : Security.HandshakeForwardSecrecy :=
  sorry

theorem kci_resistance : Security.KCIResistance :=
  sorry

theorem session_independence : Security.SessionIndependence :=
  sorry

theorem hndl_resistance : Security.HNDLResistance :=
  sorry

end Proven.Handshake
