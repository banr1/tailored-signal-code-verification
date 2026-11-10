/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR

/-!
# MAC Headedness and Plaintext-Atom Disjointness for `recvRepresentations`

Combines the `spqrHeaded msg₀.mac = false` clause of `recvRepresentations` with `g1_rep_ptAtoms_tr`
to establish `g1_rep_of_recvRepresentations`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)

open DY DY.Comparse DY.Literal DY.Libsignal
open CryptoProofLib.Refinement (ExternInterpretation)

private theorem isNone_of_isSome_eq_false_tr {α : Type} {o : Option α}
    (h : o.isSome = false) : o.isNone = true := by
  cases o <;> simp_all

theorem notSpqrHeaded_of_spqrHeaded_eq_false {u : DY.Bytes}
    (h : spqrHeaded u = false) :
    notSpqrHeaded u := by
  simp only [spqrHeaded, Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨isNone_of_isSome_eq_false_tr h1, isNone_of_isSome_eq_false_tr h2,
    isNone_of_isSome_eq_false_tr h3, isNone_of_isSome_eq_false_tr h4,
    isNone_of_isSome_eq_false_tr h5, isNone_of_isSome_eq_false_tr h6,
    isNone_of_isSome_eq_false_tr h7⟩

/-- A received representation's parsed MAC satisfies `notSpqrHeaded` and is disjoint from
`plaintextTerms (runVis r₀ ms)`. -/
theorem g1_rep_of_recvRepresentations
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (b : HwBytes) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) :
    notSpqrHeaded msg₀.mac ∧ msg₀.mac ∉ plaintextTerms (runVis r₀ ms) := by
  refine ⟨notSpqrHeaded_of_spqrHeaded_eq_false (ht₀.2.2.2 msg₀ hparse₀).2.2.1, ?_⟩
  have h := g1_rep_ptAtoms_tr r₀ ms [] (fun _ h => absurd h List.not_mem_nil) hparse₀
  rwa [List.append_nil] at h

end Symbolic.Swarm.CREF.TR.G1
