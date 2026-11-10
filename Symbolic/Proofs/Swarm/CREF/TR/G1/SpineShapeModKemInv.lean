/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRkCore
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Skipped-Seed Event Predicate and Stored-State Spine Extraction

Defines `SkippedSeedLogged` (message-key seeds logged in `TREvent.SkippedKeyStored`) and extracts
`SpStateRk (LoggedIkmRk T) idx st` from `TRStoredAt T me st idx` via `spStateRk_of_trStoredAt`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.COMPOSED.CompInv (TRStoredAt)

/-- `u` was logged as the `mkSeed` of a `TREvent.SkippedKeyStored` event on `T`. -/
def SkippedSeedLogged (T : ExecTrace) (u : DY.Bytes) : Prop :=
  ∃ j ses pk n rIdx src,
    T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n u rIdx src) j

theorem spStateRk_of_trStoredAt {T : ExecTrace} (htr : TraceOkR T T)
    {me : Participant} {st : TRState} {idx : Nat}
    (h : TRStoredAt T me st idx) : SpStateRk (LoggedIkmRk T) idx st := by
  unfold TRStoredAt DY.Trace.at? at h
  split at h
  · next hj => exact (htr idx hj).1 ⟨⟨me, st⟩⟩ h
  · cases h

end Symbolic.Swarm.CREF.TR.G1.Spine
