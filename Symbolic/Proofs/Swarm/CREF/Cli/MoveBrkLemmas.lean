/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
import DY.Trace.Monad
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
import DY.Trace.Manipulation
import Mathlib.Data.List.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Manipulation

/-!
# Quantum-Break Trace Step Lemmas

Characterizes trace extensions that log only quantum-break marker events (`BrokenDH` and
`BrokenKEM`) via `isBreakPQEv` and `NonSessionPQAt`, showing they add no session state or
session-completion events and preserve `bobDoneBaseKeys` and `eventIdx`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas

open DY (ExecTrace Participant Trace TraceEntryHas)
open DY.PersistentGlobalState.State (ExecEntryT)
open DY.PersistentLocalState (LocalState)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement (bobDoneBaseKeys eventIdx newIndices)
open DY.Libsignal.PQXDH (PQXDHEvent breakDH breakKEM)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open scoped DY.Libsignal.Composed

/-- Whether a `PQXDHEvent` is one of the two quantum-break marker events (`BrokenDH` / `BrokenKEM`),
which emit no visible entry and create/modify no session or prekey state. -/
def isBreakPQEv : PQXDHEvent → Bool
  | .BrokenDH | .BrokenKEM => true
  | _ => false

/-- At trace index `i`, any logged `PQXDHEvent` is a quantum-break marker (`BrokenDH` / `BrokenKEM`). -/
def NonSessionPQAt (tr : ExecTrace) (i : Nat) : Prop :=
  ∀ e : DY.ProtocolEvent.ExecEntryT PQXDHEvent, tr.at? i = some e → isBreakPQEv e.ev = true

theorem nonSessionPQAt_of_eq_none {tr : ExecTrace} {i : Nat}
    (h : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    NonSessionPQAt tr i := by
  intro e he
  rw [h] at he
  cases he

theorem nonSessionPQAt_le {tr₁ tr₂ : ExecTrace} (hle : tr₁ ≤ tr₂) {i : Nat}
    (hi : i < tr₁.length) (h : NonSessionPQAt tr₁ i) :
    NonSessionPQAt tr₂ i := by
  have hi₂ : i < tr₂.length := Nat.lt_of_lt_of_le hi (Trace.length_le tr₁ tr₂ hle)
  intro e he
  apply h e
  simpa only [Trace.at?, hi, hi₂, ↓reduceDIte, Trace.at_le tr₁ tr₂ i hi hle] using he

/-- Appending a break event (`isBreakPQEv ev = true`) adds no `TRState`, non-break `PQXDHEvent`,
`TREvent`, or `ComposedEvent` on `newIndices`. -/
theorem break_append_noSessionAt (tr : ExecTrace) (ev : PQXDHEvent)
    (hb : isBreakPQEv ev = true) :
    ∀ i ∈ newIndices tr (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)),
      ((tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)).at? i :
          Option (ExecEntryT (LocalState TRState))) = none ∧
        NonSessionPQAt (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)) i ∧
        ((tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)).at? i :
          Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none ∧
        ((tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)).at? i :
          Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) = none := by
  intro i hi
  have hlen : (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt : tr.length < (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)).length := by
    omega
  have hi' : i = tr.length := by
    simp only [newIndices, List.mem_range'] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    omega
  subst hi'
  have hat_len :
      (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)).at tr.length hlt =
        TraceEntryHas.inj (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent) := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte, hat_len]; rfl
  · intro e he
    rw [Trace.at?_append] at he
    injection he with he'
    cases he'
    exact hb
  · simp only [Trace.at?, hlt, ↓reduceDIte, hat_len]; rfl
  · simp only [Trace.at?, hlt, ↓reduceDIte, hat_len]; rfl

theorem nonSessionPQAt_pred_eq_false {tr : ExecTrace} {i : Nat}
    (h : NonSessionPQAt tr i) {e : DY.ProtocolEvent.ExecEntryT PQXDHEvent}
    (he : tr.at? i = some e) {p : PQXDHEvent → Bool}
    (hp : p .BrokenDH = false ∧ p .BrokenKEM = false := by exact ⟨rfl, rfl⟩) :
    p e.ev = false := by
  have hb := h e he
  cases hev : e.ev <;> rw [hev] at hb <;> try cases hb
  · exact hp.1
  · exact hp.2

/-- Extending `tr ≤ tr'` with `NonSessionPQAt` at all new indices preserves `bobDoneBaseKeys`. -/
theorem bobDoneBaseKeys_eq_of_nonSessionPQExt {tr tr' : ExecTrace} (hle : tr ≤ tr')
    (hnew : ∀ i, tr.length ≤ i → i < tr'.length → NonSessionPQAt tr' i) :
    bobDoneBaseKeys tr' = bobDoneBaseKeys tr := by
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  have hpre : ∀ i ∈ List.range tr.length,
      tr'.getEventAt PQXDHEvent i = tr.getEventAt PQXDHEvent i := by
    intro i hi
    have hlt : i < tr.length := List.mem_range.mp hi
    have hlt' : i < tr'.length := Nat.lt_of_lt_of_le hlt hlen
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    simp only [Trace.at?, hlt, hlt', ↓reduceDIte, Trace.at_le tr tr' i hlt hle]
  unfold bobDoneBaseKeys
  rw [show tr'.length = tr.length + (tr'.length - tr.length) by omega, List.range_add,
    List.filterMap_append, List.filterMap_map,
    List.filterMap_congr fun i hi => by rw [hpre i hi]]
  convert List.append_nil _ using 2
  refine List.filterMap_eq_nil_iff.mpr fun k hk => ?_
  have hklt : k < tr'.length - tr.length := List.mem_range.mp hk
  simp only [Function.comp_apply]
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  cases hat : (tr'.at? (tr.length + k) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => rfl
  | some e =>
    dsimp only
    have hb := hnew (tr.length + k) (by omega) (by omega) e hat
    cases hev : e.ev <;> first | rfl | (rw [hev] at hb; cases hb)

/-- Extending `tr ≤ tr'` with `NonSessionPQAt` at all new indices yields `eventIdx p tr tr' = none`
whenever `p` rejects `BrokenDH` and `BrokenKEM`. -/
theorem eventIdx_eq_none_of_nonSessionPQExt {tr tr' : ExecTrace}
    {p : PQXDHEvent → Bool} (hle : tr ≤ tr')
    (hnew : ∀ i, tr.length ≤ i → i < tr'.length → NonSessionPQAt tr' i)
    (hp : p .BrokenDH = false ∧ p .BrokenKEM = false := by exact ⟨rfl, rfl⟩) :
    eventIdx p tr tr' = none := by
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  unfold eventIdx newIndices
  apply List.find?_eq_none.mpr
  intro i hi
  have hi' := List.mem_range'_1.mp hi
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  cases hat : (tr'.at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => simp
  | some e =>
    have hb := hnew i hi'.1 (by omega) e hat
    cases hev : e.ev <;> rw [hev] at hb <;> try cases hb
    · simp [hev, hp.1]
    · simp [hev, hp.2]

end Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas
