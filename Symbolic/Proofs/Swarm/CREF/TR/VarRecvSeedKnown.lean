/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Concretization
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Byte-Fresh Receiver-Chain Lookup Disjointness

Proves that when every receiver chain in `st₀_src.recv` has concretized ratchet-key bytes distinct
from `pk`, `findRecvChain st₀_src.recv rk` cannot succeed for any `rk` with the same bytes as `pk`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.RecvDecStep.VarRecvSeedKnown

cref_open

abbrev SpqrSem := OpaqueSymbolSemantics

open DY.Libsignal.TripleRatchet (RecvChain findRecvChain)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)

private theorem mem_recv_of_findRecvChain_eq_some {chains : List RecvChain} {pk : DY.Bytes}
    {c : RecvChain} (hfind : findRecvChain chains pk = some c) :
    c ∈ chains ∧ c.ratchetKey = pk := by
  unfold findRecvChain at hfind
  exact ⟨List.mem_of_find?_eq_some hfind,
    beq_iff_eq.mp (List.find?_some (p := fun (x : RecvChain) => x.ratchetKey == pk) hfind)⟩

/-- If no chain of `st₀_src.recv` has the concretized ratchet-key bytes of `pk`, then `st₀_src` has
no receiver chain for any `rk` whose concretized bytes equal those of `pk`. -/
theorem false_of_existing_of_byteFresh
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st₀_src : TRState} {rk pk : DY.Bytes} {c_ex : RecvChain}
    (hfind : findRecvChain st₀_src.recv rk = some c_ex)
    (hγ : gamma interpretation S g rk = gamma interpretation S g pk)
    (hByteFresh : ∀ c ∈ st₀_src.recv,
      gamma interpretation S g c.ratchetKey ≠ gamma interpretation S g pk) :
    False := by
  obtain ⟨hmem, hrk⟩ := mem_recv_of_findRecvChain_eq_some hfind
  exact hByteFresh c_ex hmem (by rw [hrk]; exact hγ)

end Symbolic.Swarm.CREF.TR.RecvDecStep.VarRecvSeedKnown
