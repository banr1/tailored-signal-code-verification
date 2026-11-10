/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement

/-!
# Whole-turn leakable-secret predicates

Defines `LeakableSecret` and `Cli.KeyInDirs`, characterizing secrets held across both parties'
session records and setup DH and Kyber keys at a `CliTurn`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Rust (recordBytes KeyInRecord)

/-- Holds when `k` is Bob's Kyber pre-key secret, an active setup DH secret, or a secret stored in
either party's current session record. -/
def LeakableSecret (r : ProtocolSetup) (records : Participant → Option HwBytes) (opkUsed : Bool)
    (k : HwBytes) : Prop :=
  k = r.kyberSecB ∨ Cli.SetupDHSecret r (opkUsed = false) k ∨
    ∃ p rec, records p = some (recordBytes rec) ∧ KeyInRecord rec k

end DY.Libsignal.Composed.Refinement

namespace DY.Libsignal.Composed.Refinement.Cli

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (ProtocolSetup LeakableSecret)

/-- Specialization of `LeakableSecret` to `t.records r` and `t.opkUsed r`. -/
def KeyInDirs (r : ProtocolSetup) (t : CliTurn) (k : HwBytes) : Prop :=
  LeakableSecret r (t.records r) (t.opkUsed r) k

end DY.Libsignal.Composed.Refinement.Cli
