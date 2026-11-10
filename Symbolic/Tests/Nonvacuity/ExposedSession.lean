/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance

/-!
# Session-State Exposure Trace Without Long-Term Key Compromise

Defines `exposedSessionTrace`, a 90-entry composed-protocol trace extending the honest bidirectional
session with chain-key exposures (`ExposedCKr` on Bob's signed prekey and `ExposedCKs` on Alice's
sending chain) followed by an Alice-to-Bob ratchet message exchange, with no long-term PQXDH
compromise. Witnesses both `FSPremiseSatisfiable` and `HandshakeSecrecyPremiseSatisfiable`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.Nonvacuity

open DY
open DY.Libsignal
open DY.Libsignal.Composed

/-- Concrete 90-entry trace extending `honestSessionTrace` with `ExposedCKr` and `ExposedCKs`
session-state leaks and a subsequent Alice-to-Bob message under the exposed sending chain. -/
def exposedSessionTrace : ExecTrace :=
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
    let msg1 ← TripleRatchet.messageEncrypt "alice" (msg0 - 1) 32 (msg0 + 3)
    let bobKeys : PQXDH.BobKeyHandles :=
      { ik := ikB, spk := spkB, pqspk := pqspkB, opk := none }
    let preKeyMsg : PQXDH.PreKeyMsgHandles :=
      { ek := stA0 - 5, ct := stA0 - 4, msg := msg0 }
    let stB1 ← Composed.bobStart "bob" "alice" bobKeys (ikA - 3) preKeyMsg (stA0 + 3) 1
    let stB2 ← TripleRatchet.messageDecrypt "bob" stB1 msg1 (msg0 + 3) 2
    let reply0 ← TripleRatchet.messageEncrypt "bob" stB2 32 (stB2 + 3)
    let stA4 ← TripleRatchet.messageDecrypt "alice" (msg1 - 1) reply0 (stB2 + 3) 1
    let spkBPk ← Network.receiveMessage (spkB + 1)
    let _ ← TripleRatchet.exposeKey "alice" stA4 (.ckr spkBPk)
    let cksNet ← TripleRatchet.exposeKey "alice" stA4 .cks
    let msg2 ← TripleRatchet.messageEncrypt "alice" stA4 32 (cksNet + 3)
    let _ ← TripleRatchet.messageDecrypt "bob" (reply0 - 1) msg2 (cksNet + 3) 3
    pure ()).run Trace.nil).2.val

end Symbolic.Tests.Nonvacuity
