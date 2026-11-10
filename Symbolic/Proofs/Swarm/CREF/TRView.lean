/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
import Mathlib.Data.List.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Triple-Ratchet-Shaped Visible Entry Views

Defines `trLayout` and `trEntry` for single-term visible entries in the composed model and proves
unfolding and trace-append lemmas for `Move.vis`, `newIndices`, `newRandoms`, `receivedPlaintext`,
and `exposures`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY DY.Comparse DY.Libsignal
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (TREvent)
open DY.Libsignal.PQXDH (PQXDHEvent)

/-! ## Triple-Ratchet-Shaped Entries -/

/-- Byte layout of a single-term Triple Ratchet visible entry of kind `k`. -/
def trLayout : VisEventKind → VisByteLayout
  | .send | .recv => .whisper
  | .leak => .leakRecord
  | _ => .single

/-- Composed `VisEntry` for a single-term Triple Ratchet entry `(k, t)` with no anchor. -/
def trEntry (k : VisEventKind) (t : DY.Bytes) : VisEntry := ⟨k, [t], trLayout k, none⟩

@[simp] theorem trLayout_send : trLayout .send = .whisper := rfl
@[simp] theorem trLayout_recv : trLayout .recv = .whisper := rfl
@[simp] theorem trLayout_leak : trLayout .leak = .leakRecord := rfl
@[simp] theorem trLayout_pt : trLayout .pt = .single := rfl
@[simp] theorem trLayout_rng : trLayout .rng = .single := rfl
@[simp] theorem trLayout_accept : trLayout .accept = .single := rfl

@[simp] theorem trEntry_kind (k : VisEventKind) (t : DY.Bytes) : (trEntry k t).kind = k := rfl
@[simp] theorem trEntry_terms (k : VisEventKind) (t : DY.Bytes) : (trEntry k t).terms = [t] := rfl
@[simp] theorem trEntry_layout (k : VisEventKind) (t : DY.Bytes) : (trEntry k t).layout = trLayout k := rfl
@[simp] theorem trEntry_anchor (k : VisEventKind) (t : DY.Bytes) : (trEntry k t).anchor = none := rfl

/-! ## `Move.vis` Unfolding -/

@[simp] theorem encDraws_nil : encDraws [] = [] := rfl

theorem decVis_false (tr tr' : ExecTrace) (stateIdx msgIdx : Nat) :
    decVis tr tr' stateIdx msgIdx false =
      ((tr.getMessageSentAt msgIdx).map (trEntry .recv)).toList ++
        (newRandoms tr tr').map (fun r => trEntry .rng r.1) ++
        ((receivedPlaintext tr tr').map (trEntry .accept)).toList := rfl

theorem decVis_true (tr tr' : ExecTrace) (stateIdx msgIdx : Nat) :
    decVis tr tr' stateIdx msgIdx true =
      ((tr.getMessageSentAt msgIdx).map fun b =>
          (⟨.recv, [b], .preKeyInner (sessionBaseKeys tr stateIdx), none⟩ : VisEntry)).toList ++
        (newRandoms tr tr').map (fun r => trEntry .rng r.1) ++
        ((receivedPlaintext tr tr').map (trEntry .accept)).toList := rfl

theorem vis_decrypt {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32}
    {wrapped : Bool} {tr tr' : ExecTrace}
    (h : (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr = tr') :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr =
      decVis tr tr' stateIdx msgIdx wrapped ++ exposures tr tr' := by
  subst h; rfl

theorem vis_decrypt_false {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32}
    {tr tr' : ExecTrace} (h : (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false).next tr = tr') :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false).vis tr =
      ((tr.getMessageSentAt msgIdx).map (trEntry .recv)).toList ++
        (newRandoms tr tr').map (fun r => trEntry .rng r.1) ++
        ((receivedPlaintext tr tr').map (trEntry .accept)).toList ++ exposures tr tr' := by
  rw [vis_decrypt h, decVis_false]

theorem vis_decryptSkipped {me : Participant} {stateIdx msgIdx skIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool} {tr tr' : ExecTrace}
    (h : (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr = tr') :
    (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis tr =
      decVis tr tr' stateIdx msgIdx wrapped ++ exposures tr tr' := by
  subst h; rfl

theorem vis_decryptSkipped_false {me : Participant} {stateIdx msgIdx skIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {tr tr' : ExecTrace}
    (h : (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false).next tr = tr') :
    (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false).vis tr =
      ((tr.getMessageSentAt msgIdx).map (trEntry .recv)).toList ++
        (newRandoms tr tr').map (fun r => trEntry .rng r.1) ++
        ((receivedPlaintext tr tr').map (trEntry .accept)).toList ++ exposures tr tr' := by
  rw [vis_decryptSkipped h, decVis_false]

theorem vis_attackerSend {msg : DY.Bytes} {tr tr' : ExecTrace}
    (h : (Move.attackerSend msg).next tr = tr') :
    (Move.attackerSend msg).vis tr = exposures tr tr' := by
  subst h; rfl

/-! ## Trace-Append Algebra for `Move.vis` Components -/

section Append

variable {E : Type} [ExecTraceTypes.Has E]

theorem length_append' (tr : ExecTrace) (e : E) : (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem at?_append_lt {E2 : Type} [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E) {i : Nat}
    (hi : i < tr.length) : ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_length {E2 : Type} [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  have hlt : tr.length < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

theorem at?_append_self' (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e := by
  rw [at?_append_length, TraceEntryHas.inj_proj_eq]

theorem at?_ge_length {E2 : Type} [ExecTraceTypes.Has E2] (tr : ExecTrace) {i : Nat}
    (hi : tr.length ≤ i) : (tr.at? i : Option E2) = none := by
  simp only [Trace.at?]
  split
  · omega
  · rfl

theorem getEventAt_append_lt (EventT : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    (tr.append e).getEventAt EventT i = tr.getEventAt EventT i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_lt tr e hi]

@[simp] theorem newIndices_self (tr : ExecTrace) : newIndices tr tr = [] := by
  simp [newIndices]

@[simp] theorem newRandoms_self (tr : ExecTrace) : newRandoms tr tr = [] := by
  simp [newRandoms]

@[simp] theorem receivedPlaintext_self (tr : ExecTrace) : receivedPlaintext tr tr = none := by
  simp [receivedPlaintext]

@[simp] theorem exposures_self' (tr : ExecTrace) : exposures tr tr = [] := by
  simp [exposures]

theorem mem_newIndices {tr0 tr : ExecTrace} {i : Nat} :
    i ∈ newIndices tr0 tr ↔ tr0.length ≤ i ∧ i < tr.length := by
  simp only [newIndices, List.mem_range'_1]
  omega

theorem newIndices_append {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newIndices tr0 (tr.append e) = newIndices tr0 tr ++ [tr.length] := by
  simp only [newIndices, length_append']
  rw [show tr.length + 1 - tr0.length = (tr.length - tr0.length) + 1 by omega, List.range'_concat]
  congr 2
  omega

theorem newRandoms_append {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newRandoms tr0 (tr.append e) = newRandoms tr0 tr ++
      (((tr.append e).at? tr.length : Option DY.Random.ExecEntryT).map
        fun r => (randTerm tr.length r.length, r.length)).toList := by
  unfold newRandoms
  rw [newIndices_append h, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  congr 1
  refine List.filterMap_congr fun i hi => ?_
  rw [at?_append_lt tr e (mem_newIndices.mp hi).2]

theorem newRandoms_append_rnd {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (n : Nat) :
    newRandoms tr0 (tr.append (DY.Random.ExecEntryT.mk n)) =
      newRandoms tr0 tr ++ [(randTerm tr.length n, n)] := by
  rw [newRandoms_append h, at?_append_self']
  rfl

theorem newRandoms_append_of_proj {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none) :
    newRandoms tr0 (tr.append e) = newRandoms tr0 tr := by
  rw [newRandoms_append h, at?_append_length, hproj]
  simp

/-- The plaintext of a `Received` event at index `i` of `tr`, if any. -/
def receivedAt (tr : ExecTrace) (i : Nat) : Option DY.Bytes :=
  match tr.getEventAt TREvent i with
  | some (.Received _ _ _ _ m) => some m
  | _ => none

private theorem findSome?_congr' {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem receivedPlaintext_eq (tr0 tr : ExecTrace) :
    receivedPlaintext tr0 tr = (newIndices tr0 tr).findSome? (receivedAt tr) := rfl

theorem receivedAt_append_lt (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    receivedAt (tr.append e) i = receivedAt tr i := by
  simp only [receivedAt, getEventAt_append_lt TREvent tr e hi]

theorem receivedPlaintext_append {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    receivedPlaintext tr0 (tr.append e) =
      (receivedPlaintext tr0 tr).or (receivedAt (tr.append e) tr.length) := by
  rw [receivedPlaintext_eq, receivedPlaintext_eq, newIndices_append h, List.findSome?_append]
  have hcongr : (newIndices tr0 tr).findSome? (receivedAt (tr.append e)) =
      (newIndices tr0 tr).findSome? (receivedAt tr) := by
    refine findSome?_congr' fun i hi => ?_
    exact receivedAt_append_lt tr e (mem_newIndices.mp hi).2
  rw [hcongr, List.findSome?_singleton]

theorem receivedAt_append_of_proj (tr : ExecTrace) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    receivedAt (tr.append e) tr.length = none := by
  simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_length, hproj]

theorem receivedPlaintext_append_of_proj {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    receivedPlaintext tr0 (tr.append e) = receivedPlaintext tr0 tr := by
  rw [receivedPlaintext_append h, receivedAt_append_of_proj tr e hproj, Option.or_none]

/-! ## Exposure Helpers -/

/-- A move that logs no compromise or exposure event has no `leak` entry. -/
theorem exposures_eq_nil {tr tr' : ExecTrace}
    (h : ∀ j ∈ newIndices tr tr', pqExposureAt tr' j = none ∧ trExposureAt tr' j = none) :
    exposures tr tr' = [] := by
  unfold exposures
  rw [List.filterMap_eq_nil_iff.mpr fun j hj => (h j hj).1,
    List.filterMap_eq_nil_iff.mpr fun j hj => (h j hj).2, List.nil_append]

/-- An index holding no `TREvent` has no Triple Ratchet exposure. -/
theorem trExposureAt_of_getEventAt_none {tr' : ExecTrace} {j : Nat}
    (h : tr'.getEventAt TREvent j = none) : trExposureAt tr' j = none := by
  simp only [trExposureAt, h]

/-- An index holding no `PQXDHEvent` has no PQXDH exposure. -/
theorem pqExposureAt_of_getEventAt_none {tr' : ExecTrace} {j : Nat}
    (h : tr'.getEventAt PQXDHEvent j = none) : pqExposureAt tr' j = none := by
  simp only [pqExposureAt, h]

end Append

end Symbolic.Swarm.CREF
