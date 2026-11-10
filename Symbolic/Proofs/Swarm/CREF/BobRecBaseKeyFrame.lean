/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix

/-!
# Frame Preservation of Bob's Session Base-Key Invariant

Proves `bks_of_ext` and `bks_frame`, transporting `BobRecordBaseKeyInSession` across move blocks
that either preserve Bob's current session descriptor (`NewBobSinfo`) or have `NoSessionEffect`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry)

private theorem bksF_at?_of_le_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (Trace.length_le tr tr' hle)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr tr' i hi hle]

private theorem bksF_at?_none_of_ge {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {j : Nat}
    (hj : tr.length ≤ j) : (tr.at? j : Option E) = none := by
  simp only [Trace.at?, show ¬ j < tr.length by omega, ↓reduceDIte]

private theorem bksF_noNewSt_of_noSessionEffect {tr : ExecTrace} {m : Move}
    (hq : NoSessionEffect tr m) :
    ∀ j, tr.length ≤ j → ((m.next tr).at? j : Option TRStEntry) = none := by
  intro j hj
  by_cases hj' : j < (m.next tr).length
  · refine (hq j ?_).1
    simp only [newIndices, List.mem_range'_1]
    omega
  · exact bksF_at?_none_of_ge (by omega)

theorem bksF_le_runMoves :
    ∀ (tr : ExecTrace) (δ : List Move), tr ≤ (runMoves δ tr).1
  | tr, [] => Trace.le_refl tr
  | tr, m :: δ =>
    Trace.le_trans _ _ _ ((Move.act m).run tr).2.property (bksF_le_runMoves (m.next tr) δ)

theorem bksF_noNewSt_of_movesFrom :
    ∀ (tr : ExecTrace) (δ : List Move),
      MovesFrom (fun tr m => NoSessionEffect tr m) tr δ →
      ∀ j, tr.length ≤ j → (((runMoves δ tr).1).at? j : Option TRStEntry) = none
  | tr, [], _ => fun _ hj => bksF_at?_none_of_ge hj
  | tr, m :: δ, ⟨hm, hδ⟩ => fun j hj => by
    simp only [runMoves]
    by_cases hlt : j < (m.next tr).length
    · rw [bksF_at?_of_le_lt (bksF_le_runMoves (m.next tr) δ) hlt]
      exact bksF_noNewSt_of_noSessionEffect hm j hj
    · exact bksF_noNewSt_of_movesFrom (m.next tr) δ hδ j (Nat.le_of_not_lt hlt)

theorem newBobSinfo_of_noSessionEffect {bob : Participant} {tr : ExecTrace} {m : Move}
    (hq : NoSessionEffect tr m) : NewBobSinfo bob tr (m.next tr) :=
  newBobSinfo_of_noNewSt (bksF_noNewSt_of_noSessionEffect hq)

theorem newBobSinfo_of_movesFrom_noSessionEffect {bob : Participant} {tr : ExecTrace}
    {δ : List Move} (hq : MovesFrom (fun tr m => NoSessionEffect tr m) tr δ) :
    NewBobSinfo bob tr (runMoves δ tr).1 :=
  newBobSinfo_of_noNewSt (bksF_noNewSt_of_movesFrom tr δ hq)

/-- Transports `BobRecordBaseKeyInSession` from `ms₀` to `ms₀ ++ δ` when every new Bob snapshot
continues a current one and Bob's post-block record preserves `current.aliceBaseKey`. -/
theorem bks_of_ext {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms₀ δ : List Move} {records records' : Participant → Option HwBytes}
    (hnew : NewBobSinfo r.bob (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ δ)))
    (hrec : ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey)
    (h : BobRecordBaseKeyInSession interpretation r S g ms₀ records) :
    BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ δ) records' := by
  intro rr' hrr'
  obtain ⟨rr, hrr, heq⟩ := hrec rr' hrr'
  show BobBaseKeyOn interpretation S g r.bob (runTraceMoves r (ms₀ ++ δ)) rr'.current.aliceBaseKey
  rw [heq]
  exact bobBaseKeyOn_ext (runTrace_le_append r ms₀ δ) hnew (h rr hrr)

theorem bks_rec_of_eq {r : ProtocolSetup} {records records' : Participant → Option HwBytes}
    (h : records' r.bob = records r.bob) :
    ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey :=
  fun rr' hrr' => ⟨rr', h ▸ hrr', rfl⟩

/-- Preserves `BobRecordBaseKeyInSession` across a `NoSessionEffect` block that leaves Bob's
record unchanged. -/
theorem bks_frame {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms₀ δ : List Move} {records records' : Participant → Option HwBytes}
    (hq : MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) δ)
    (hrec : records' r.bob = records r.bob)
    (h : BobRecordBaseKeyInSession interpretation r S g ms₀ records) :
    BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ δ) records' := by
  have hnew : NewBobSinfo r.bob (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ δ)) := by
    rw [runTrace_append]
    exact newBobSinfo_of_movesFrom_noSessionEffect hq
  exact bks_of_ext hnew (bks_rec_of_eq hrec) h

end Symbolic.Swarm.CREF
