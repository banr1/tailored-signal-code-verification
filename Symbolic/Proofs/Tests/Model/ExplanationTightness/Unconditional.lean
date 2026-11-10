/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
public import Symbolic.Proofs.Tests.Model.ExplanationTightness.Scope
public import Symbolic.Proofs.Tests.Model.ExplanationTightness.Compromised
public import Symbolic.Proofs.Tests.Model.ExplanationTightness.Handshake
import Symbolic.Theorems.ModelSecurity

/-!
# Unconditional Premise and Compromise Redundancy Corollaries

Instantiates the conditional redundancy theorems from `Scope`, `Compromised`, and `Handshake` with
the proved composed security theorems (`Proven.*`), yielding unconditional strengthened security
statements on reachable traces.
-/

@[expose] public section

set_option autoImplicit false

open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (TestTracePredicates mkTestTracePredicates FSQueryP PCSQueryP fsQuery_iff_test pcsQuery_iff_test)

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.Unconditional

open DY DY.Libsignal DY.Libsignal.Composed

theorem handshakeForwardSecrecy_withoutPQSPK : Scope.HandshakeForwardSecrecy_withoutPQSPK :=
  Scope.handshakeForwardSecrecy_withoutPQSPK_of_real
    Proven.Handshake.alice_initiator_secrecy Proven.Handshake.bob_responder_secrecy

theorem handshakeForwardSecrecy_withoutKEM : Scope.HandshakeForwardSecrecy_withoutKEM :=
  Scope.handshakeForwardSecrecy_withoutKEM_of_real
    Proven.Handshake.alice_initiator_secrecy Proven.Handshake.bob_responder_secrecy

theorem sessionIndependence_withoutKEM : Scope.SessionIndependence_withoutKEM :=
  Scope.sessionIndependence_withoutKEM_of_real
    Proven.Handshake.alice_initiator_secrecy Proven.Handshake.bob_responder_secrecy

theorem sessionIndependence_withoutPQSPK : Scope.SessionIndependence_withoutPQSPK :=
  Scope.sessionIndependence_withoutPQSPK_of_real
    Proven.Handshake.alice_initiator_secrecy Proven.Handshake.bob_responder_secrecy

theorem sessionIndependence_withoutOPK : Scope.SessionIndependence_withoutOPK :=
  Scope.sessionIndependence_withoutOPK_of_real
    Proven.Handshake.alice_initiator_secrecy Proven.Handshake.bob_responder_secrecy

theorem kciResistance_withoutIK : Scope.KCIResistance_withoutIK :=
  Scope.kciResistance_withoutIK_of_real Proven.Handshake.authentication

theorem forwardSecrecy_compromisedWithoutDHs : Compromised.ForwardSecrecyWithout (some .dhs) :=
  Compromised.forwardSecrecy_compromisedWithoutDHs_of_real Proven.ForwardSecrecy.forward_secrecy

theorem forwardSecrecy_compromisedWithoutBDH : Compromised.ForwardSecrecyWithout (some .bdh) :=
  Compromised.forwardSecrecy_compromisedWithoutBDH_of_real Proven.ForwardSecrecy.forward_secrecy

theorem forwardSecrecy_bdhStoredOnly :
    Compromised.ForwardSecrecyWithBDH Compromised.HonestDHStoredOnly :=
  Compromised.forwardSecrecy_bdhStoredOnly_of_real Proven.ForwardSecrecy.forward_secrecy

theorem postCompromiseSecurity_bdhStoredOnly :
    Compromised.PostCompromiseSecurityWithBDH Compromised.HonestDHStoredOnly :=
  Compromised.postCompromiseSecurity_bdhStoredOnly_of_real
    Proven.PostCompromiseSecurity.post_compromise_security

theorem responderSecrecy_withoutCks : Handshake.ResponderSecrecy_withoutCks :=
  Handshake.responderSecrecy_withoutCks_of_real Proven.Handshake.alice_initiator_secrecy

theorem initiatorSecrecy_withoutCks : Handshake.InitiatorSecrecy_withoutCks :=
  Handshake.initiatorSecrecy_withoutCks_of_real Proven.Handshake.bob_responder_secrecy

theorem responderSecrecy_withoutRk : Handshake.ResponderSecrecy_withoutRk :=
  Handshake.responderSecrecy_withoutRk_of_real Proven.Handshake.alice_initiator_secrecy

theorem initiatorSecrecy_withoutRk : Handshake.InitiatorSecrecy_withoutRk :=
  Handshake.initiatorSecrecy_withoutRk_of_real Proven.Handshake.bob_responder_secrecy

end Symbolic.Proofs.Tests.Model.ExplanationTightness.Unconditional
