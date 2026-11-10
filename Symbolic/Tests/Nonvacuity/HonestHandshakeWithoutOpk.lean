/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance

/-!
# Honest PQXDH Handshake Trace Without One-Time Prekey

Defines `honestHandshakeWithoutOpkTrace`, a 47-entry composed-protocol trace in which Alice and Bob
register honest identities, Bob publishes signed X25519 and signed Kyber-1024 prekeys (`opk = none`),
and Bob accepts Alice's initial SPQR-salted prekey message (`SanityHonestWithoutOPK`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.Nonvacuity

open DY
open DY.Libsignal
open DY.Libsignal.Composed

/-- Concrete 47-entry uncompromised trace completing a PQXDH handshake and initial message delivery
without a one-time prekey (`opk = none`). -/
def honestHandshakeWithoutOpkTrace : ExecTrace :=
  ((show Traceful Unit from do
    let ikA ← PQXDH.registerIdentity "alice"
    let ikB ← PQXDH.registerIdentity "bob"
    let spkB ← PQXDH.genSignedPrekey "bob" ikB
    let pqspkB ← PQXDH.genPQPrekey "bob" ikB
    let bundle : PQXDH.BundleHandles :=
      { spk := spkB + 1, spkSig := spkB + 2
        pqpk := pqspkB + 1, pqpkSig := pqspkB + 2
        opk := none }
    let stA0 ← Composed.aliceStart "alice" "bob" ikA (ikB - 3) bundle
    let msg0 ← TripleRatchet.messageEncrypt "alice" stA0 32 (stA0 + 3)
    let bobKeys : PQXDH.BobKeyHandles :=
      { ik := ikB, spk := spkB, pqspk := pqspkB, opk := none }
    let preKeyMsg : PQXDH.PreKeyMsgHandles :=
      { ek := stA0 - 5, ct := stA0 - 4, msg := msg0 }
    let _ ← Composed.bobStart "bob" "alice" bobKeys (ikA - 3) preKeyMsg (stA0 + 3) 1
    pure ()).run Trace.nil).2.val

end Symbolic.Tests.Nonvacuity
