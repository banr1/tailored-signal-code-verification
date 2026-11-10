/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Stamp Bounds for `BobDone` Base Keys

Proves that every `PQXDHEvent.BobDone` entry on a reachable trace of length `≤ ts` has its
ephemeral base key stamped below `ts`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH (PQXDHEvent)
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt PQEvEntry traceEntriesLt_at?_pqev
  traceEntriesLt_of_reachable)

theorem g2b_bobDoneEk_stampsLt_of_reachable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts : Nat) {tr : ExecTrace} (hreach : tr.Reachable reachability) (hlen : tr.length ≤ ts) :
    ∀ j b a ikB ikA spk pqpk opk ek ct keys,
      tr.getEventAt PQXDHEvent j = some (.BobDone b a ikB ikA spk pqpk opk ek ct keys) →
      StampsLt i S g ts ek := by
  have hlt := traceEntriesLt_of_reachable i S g ts hreach hlen
  intro j b a ikB ikA spk pqpk opk ek ct keys hj
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hj
  rcases hat : (tr.at? j : Option PQEvEntry) with _ | ⟨⟨ev⟩⟩ <;> rw [hat] at hj
  · cases hj
  · injection hj with hEq; subst hEq
    exact traceEntriesLt_at?_pqev hlt hat

end Symbolic.Swarm.CREF
