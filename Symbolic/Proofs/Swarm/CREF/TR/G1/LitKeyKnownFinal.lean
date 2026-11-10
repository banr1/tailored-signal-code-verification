/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnown
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CkSafeTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnownSInv

/-!
# Skipped-Seed Knowledge for Non-Honest Ratchet Keys

Proves `skippedSeedKnownTR_of_litJunk`: on any reachable composed trace, a logged
`SkippedKeyStored` event whose ratchet key satisfies `LitJunk` has both its ratchet key and its
skipped seed attacker-known.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (SessionInfo)
open Symbolic.Swarm.CREF.TR

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-- On a reachable trace, a logged skipped seed on a `LitJunk` ratchet key is attacker-known,
as is the ratchet key. -/
theorem skippedSeedKnownTR_of_litJunk {tr : ExecTrace} (hreach : ReachableTrace tr)
    {evIdx : Nat} {ses : SessionInfo} {pk : DY.Bytes} {n : UInt32} {seed : DY.Bytes}
    {rIdx src : Nat}
    (hlog : tr.EventLoggedAt (TREvent.SkippedKeyStored ses pk n seed rIdx src) evIdx)
    (hj : LitJunk pk) :
    pk.AttackerKnows tr ∧ seed.AttackerKnows tr :=
  skippedSeedKnownTR_of_sinv (sinvTR_reachable ckKnownCasesTR hreach) hlog hj

end Symbolic.Swarm.CREF.TR.G1
