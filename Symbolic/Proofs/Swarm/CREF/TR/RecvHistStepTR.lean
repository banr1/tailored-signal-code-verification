/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.EvalDist.ProbabilityNotation

/-!
# Receiver Ratchet-Key History Invariant

Defines `RecvHistInvTR`, stating that every available `TRState` on `runTraceMoves r₀ ms` has
pairwise distinct concretized receiver ratchet keys, and proves step-preservation lemmas via
`StateRel`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal.TripleRatchet (TRState)
open CryptoProofLib.Refinement (ExternInterpretation)

namespace G1

/-- Every available `TRState` on `runTraceMoves r₀ ms` has `Nodup` concretized receiver ratchet keys. -/
def RecvHistInvTR (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms),
    (st.recv.map fun c => gamma interpretation S g c.ratchetKey).Nodup

end G1

namespace RecvHistStep

theorem map_senderRatchetKey_of_stateRel
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {rec : RecordRec}
    (hrel : StateRel interpretation S g st rec) :
    rec.current.receiverChains.map ChainRec.senderRatchetKey =
      (st.recv.map fun c => gamma interpretation S g c.ratchetKey).map serializedKey := by
  have hrc := congrArg (fun sr => sr.receiverChains.map ChainRec.senderRatchetKey) hrel.2
  simp only [eraseSkipped, eraseUnmodelled, sessionOf, List.map_map, Function.comp_def] at hrc
  rw [List.map_map]
  exact hrc

theorem recvRk_nodup_of_stateRel
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {rec : RecordRec}
    (hrel : StateRel interpretation S g st rec)
    (hnd : (rec.current.receiverChains.map ChainRec.senderRatchetKey).Nodup) :
    (st.recv.map fun c => gamma interpretation S g c.ratchetKey).Nodup := by
  rw [map_senderRatchetKey_of_stateRel hrel] at hnd
  exact hnd.of_map serializedKey

/-- `RecvHistInvTR` extends from `ms` to `ms'` when every available state of `ms'` was already
available in `ms` or equals `newSt` with `Nodup` concretized receiver ratchet keys. -/
theorem recvHistInvTR_step
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {r₀ : ProtocolSetup}
    {ms ms' : List Move} {newSt : TRState}
    (hhist : Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms)
    (havail : ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms'),
      st ∈ availableStates r₀ (runTraceMoves r₀ ms) ∨ st = newSt)
    (hnew : (newSt.recv.map fun c => gamma interpretation S g c.ratchetKey).Nodup) :
    Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms' := by
  intro st hst
  rcases havail st hst with hold | rfl
  · exact hhist st hold
  · exact hnew

/-- `recvHistInvTR_step` with `Nodup` of `newSt`'s concretized receiver ratchet keys deduced
from `StateRel` and `Nodup` of `rec'.current.receiverChains.map ChainRec.senderRatchetKey`. -/
theorem recvHistInvTR_step_of_rel
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {r₀ : ProtocolSetup}
    {ms ms' : List Move} {newSt : TRState} {rec' : RecordRec}
    (hhist : Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms)
    (havail : ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms'),
      st ∈ availableStates r₀ (runTraceMoves r₀ ms) ∨ st = newSt)
    (hrel' : StateRel interpretation S g newSt rec')
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup) :
    Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms' :=
  recvHistInvTR_step hhist havail (recvRk_nodup_of_stateRel hrel' hnd')

end RecvHistStep

end Symbolic.Swarm.CREF.TR
