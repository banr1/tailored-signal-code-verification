/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Network
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.TRView
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Session-Record Exposure Moves and Leak Simulation

Proves composed-run extension and visible-entry lemmas for Triple Ratchet exposure moves
(`exposeKey`, `exposeSpqr`, `exposeSkipped`) and shows that exposure extensions satisfy
`AppendsOnlyExposure`, preserving `TRRecordStateInv` and `TRNsBound`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent RecvChain findRecvChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (PQXDHEvent)

local notation "StEntry" =>
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
local notation "TREntry" => DY.ProtocolEvent.ExecEntryT TREvent

/-! ## Composed Run Algebra -/

theorem runTrace_eq (r : ProtocolSetup) (ms : List Move) :
    runTraceMoves r ms = (runMoves ms (setupTrace r)).1 := rfl

theorem compromisesCurrentFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    compromisesCurrentFrom tr (ms₁ ++ ms₂) =
      (compromisesCurrentFrom tr ms₁ && compromisesCurrentFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [compromisesCurrentFrom]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, compromisesCurrentFrom, runMoves_cons_fst,
      compromisesCurrentFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem compromisesCurrent_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) :
    compromisesCurrentFrom (setupTrace r) (ms₁ ++ ms₂) = true ↔
      compromisesCurrentFrom (setupTrace r) ms₁ = true ∧
        compromisesCurrentFrom (runTraceMoves r ms₁) ms₂ = true := by
  simp [compromisesCurrentFrom_append, runTrace_eq]

theorem ownSaltsFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    ownSaltsFrom tr (ms₁ ++ ms₂) =
      (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [ownSaltsFrom]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, ownSaltsFrom, runMoves_cons_fst,
      ownSaltsFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem ownSalts_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) :
    ownSaltsFrom (setupTrace r) (ms₁ ++ ms₂) = true ↔
      ownSaltsFrom (setupTrace r) ms₁ = true ∧ ownSaltsFrom (runTraceMoves r ms₁) ms₂ = true := by
  simp [ownSaltsFrom_append, runTrace_eq]

theorem movesAnchored_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    MovesAnchored (ms₁ ++ ms₂) tr ↔
      MovesAnchored ms₁ tr ∧ MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _ => by simp [MovesAnchored]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, MovesAnchored, runMoves_cons_fst,
      movesAnchored_append ms₁ ms₂ (m.next tr), and_assoc]

/-! ## `ModelRun` Extension by Exposure Moves -/

theorem exposeKey_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx : Nat} {k : KeyComponent} :
    ((TripleRatchet.exposeKey me stateIdx k).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base DY.Libsignal.TripleRatchet.exposeKey.reachability
    reachability (me, stateIdx, k) tr h trivial).1

theorem exposeSpqr_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx : Nat} :
    ((TripleRatchet.exposeSpqr me stateIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base DY.Libsignal.TripleRatchet.exposeSpqr.reachability
    reachability (me, stateIdx) tr h trivial).1

theorem exposeSkipped_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {skippedKeyEventIdx : Nat} :
    ((TripleRatchet.exposeSkipped skippedKeyEventIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base DY.Libsignal.TripleRatchet.exposeSkipped.reachability
    reachability skippedKeyEventIdx tr h trivial).1

theorem exposeKey_next_eq (me : Participant) (stH : Nat) (k : KeyComponent) (tr : ExecTrace) :
    (Move.exposeKey me stH k).next tr = ((TripleRatchet.exposeKey me stH k).run tr).2.val := by
  simp only [Move.next, Move.act, Traceful.run_bind]
  rcases (TripleRatchet.exposeKey me stH k).run tr with ⟨o, t1, hle⟩
  cases o <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem exposeSkipped_next_eq (evH : Nat) (tr : ExecTrace) :
    (Move.exposeSkipped evH).next tr = ((TripleRatchet.exposeSkipped evH).run tr).2.val := by
  simp only [Move.next, Move.act, Traceful.run_bind]
  rcases (TripleRatchet.exposeSkipped evH).run tr with ⟨o, t1, hle⟩
  cases o <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem exposeSpqr_next_eq (me : Participant) (stH : Nat) (tr : ExecTrace) :
    (Move.exposeSpqr me stH).next tr = ((TripleRatchet.exposeSpqr me stH).run tr).2.val := by
  simp only [Move.next, Move.act, Traceful.run_bind]
  rcases (TripleRatchet.exposeSpqr me stH).run tr with ⟨o, t1, hle⟩
  cases o <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

/-- Extension of `ModelRun` by a non-setup, anchored move with `stateLoad? = none` that keeps the
trace reachable and preserves `compromisesCurrentFrom` and `ownSaltsFrom`. -/
theorem modelRun_snoc_of (r : ProtocolSetup) (ms : List Move) (m : Move) (hrun : ModelRun r ms)
    (hsetup : m.isSetup = false) (hreach : (m.next (runTraceMoves r ms)).Reachable reachability)
    (hanch : m.LogsSessionCompletion (runTraceMoves r ms))
    (hcc : compromisesCurrentFrom (runTraceMoves r ms) [m] = true)
    (hos : ownSaltsFrom (runTraceMoves r ms) [m] = true)
    (hpeer : m.MatchesSetupPeer r := by trivial)
    (hsl : m.stateLoad? = none := by rfl) :
    ModelRun r (ms ++ [m]) := by
  refine modelRun_snoc_of_old hrun ?_ hpeer
    (Stage1Wire.stateFaithful_snoc_of_stateLoad_none hrun.2.2.2.2.2.2 hsl)
  obtain ⟨hlen, hns, ⟨_, hanc, -⟩, hcc0, hos0, -⟩ := hrun
  refine ⟨hlen, fun m' hm => ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.mp hm with hm | hm
    · exact hns m' hm
    · rw [List.mem_singleton.mp hm]; exact hsetup
  · rw [runTrace_snoc]; exact hreach
  · rw [movesAnchored_append]
    exact ⟨hanc, by simpa [MovesAnchored, runTrace_eq] using hanch⟩
  · rw [compromisesCurrent_append]; exact ⟨hcc0, hcc⟩
  · rw [ownSalts_append]; exact ⟨hos0, hos⟩

theorem modelRun_snoc_exposeKey (r : ProtocolSetup) (ms : List Move) (me : Participant) (stH : Nat)
    (k : KeyComponent) (hrun : ModelRun r ms)
    (hcurr : isCurrentSnapshot (runTraceMoves r ms) stH = true) :
    ModelRun r (ms ++ [.exposeKey me stH k]) :=
  modelRun_snoc_of r ms _ hrun rfl
    (by rw [exposeKey_next_eq]; exact exposeKey_reachable hrun.2.2.1.1) trivial
    (by simp [compromisesCurrentFrom, hcurr]) (by simp [ownSaltsFrom])

theorem modelRun_snoc_exposeSpqr (r : ProtocolSetup) (ms : List Move) (me : Participant) (stH : Nat)
    (hrun : ModelRun r ms)
    (hcurr : isCurrentSnapshot (runTraceMoves r ms) stH = true) :
    ModelRun r (ms ++ [.exposeSpqr me stH]) :=
  modelRun_snoc_of r ms _ hrun rfl
    (by rw [exposeSpqr_next_eq]; exact exposeSpqr_reachable hrun.2.2.1.1) trivial
    (by simp [compromisesCurrentFrom, hcurr]) (by simp [ownSaltsFrom])

theorem modelRun_snoc_exposeSkipped (r : ProtocolSetup) (ms : List Move) (skIdx : Nat)
    (hrun : ModelRun r ms) :
    ModelRun r (ms ++ [.exposeSkipped skIdx]) :=
  modelRun_snoc_of r ms _ hrun rfl
    (by rw [exposeSkipped_next_eq]; exact exposeSkipped_reachable hrun.2.2.1.1) trivial
    (by simp [compromisesCurrentFrom]) (by simp [ownSaltsFrom])

/-! ## Visible Entries of Exposure Moves -/

theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option StEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  unfold _root_.guard
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]; dsimp only
    change (((if p = me then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).1 =
      if p = me then some st else none
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd hp h]
      simp only [Traceful.run_bind, Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, ite_eq_right_iff.mpr fun h => absurd h hp]
      simp only [Traceful.run_bind, Traceful.run_failure]

theorem getLocalState_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  unfold _root_.guard
  rw [run_bind_snd, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]; dsimp only
    change (((if p = me then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).2.val = tr
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h]
      simp only [Traceful.run_bind, Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp]
      simp only [Traceful.run_bind, Traceful.run_failure]

private theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem exposeSkipped_trace (evH : Nat) (t : ExecTrace) :
    ((TripleRatchet.exposeSkipped evH).run t).2.val = t ∨
    ∃ s seed n r, ((TripleRatchet.exposeSkipped evH).run t).2.val =
      (t.append (⟨.ExposedMK s seed n r⟩ : TREntry)).append (⟨seed⟩ : Network.ExecEntryT) := by
  unfold TripleRatchet.exposeSkipped
  simp only [Traceful.run_bind, Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  split
  · simp only
    split
    · simp only [Traceful.run_bind, TripleRatchet.guardTrace, Traceful.run_mk]
      split
      · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind,
          Traceful.run_mk, Traceful.run_pure]
        exact Or.inr ⟨_, _, _, _, rfl⟩
      · left; rfl
    · left; simp only [Traceful.run_failure, Traceful.run_mk]
  · left; rfl

/-- Any exposure event on a Triple Ratchet trace (the 5 DR exposure events plus `ExposedSpqr`). -/
def IsAnyExposureEv : TREvent → Prop
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr .. | .ExposedMK ..
  | .ExposedSpqr .. => True
  | _ => False

theorem newIndices_append_pair {E₁ E₂ : Type} [ExecTraceTypes.Has E₁] [ExecTraceTypes.Has E₂]
    (tr : ExecTrace) (e₁ : E₁) (e₂ : E₂) :
    newIndices tr ((tr.append e₁).append e₂) = [tr.length, tr.length + 1] := by
  rw [newIndices_append (by simp [length_append']) e₂,
    newIndices_append (Nat.le_refl _) e₁]
  simp [newIndices, length_append']

/-- `exposures` over an appended Triple Ratchet exposure-event and message pair produces a single
`.leakRecord` entry anchored at `tr.length`. -/
theorem exposures_append_tr_pair (tr : ExecTrace) (ev : TREvent) (msg : DY.Bytes)
    (hev : IsAnyExposureEv ev) :
    exposures tr ((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)) =
      [⟨.leak, [msg], .leakRecord, some tr.length⟩] := by
  unfold exposures
  rw [newIndices_append_pair]
  have hlt : tr.length < (tr.append (⟨ev⟩ : TREntry)).length := by simp [length_append']
  have hA0 : ∀ {E₂ : Type} [ExecTraceTypes.Has E₂],
      (((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).at? tr.length :
        Option E₂) = (TraceEntryHas.proj (TraceEntryHas.inj (⟨ev⟩ : TREntry) : ExecTrace.Entry)) :=
    fun {_ _} => by rw [at?_append_lt _ _ hlt, at?_append_length]
  have hA1 : ∀ {E₂ : Type} [ExecTraceTypes.Has E₂],
      (((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).at? (tr.length + 1) :
        Option E₂) =
        (TraceEntryHas.proj (TraceEntryHas.inj (⟨msg⟩ : Network.ExecEntryT) : ExecTrace.Entry)) :=
    fun {_ _} => by
      have hlen : tr.length + 1 = (tr.append (⟨ev⟩ : TREntry)).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [hlen]
      exact at?_append_length _ _
  have hmsg : ((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).getMessageSentAt
      (tr.length + 1) = some msg := by
    simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hA1, proj_inj]
  have hpq0 : ((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).getEventAt
      PQXDHEvent tr.length = none := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA0]; rfl
  have hpq1 : ((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).getEventAt
      PQXDHEvent (tr.length + 1) = none := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA1]; rfl
  have htr0 : ((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).getEventAt
      TREvent tr.length = some ev := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA0, proj_inj]
  have htr1 : ((tr.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).getEventAt
      TREvent (tr.length + 1) = none := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA1]; rfl
  simp only [List.filterMap_cons, List.filterMap_nil, pqExposureAt, trExposureAt, hpq0, hpq1,
    htr1, htr0, hmsg, Option.toList_some]
  cases ev <;> simp_all [IsAnyExposureEv]

theorem visOf_exposeSpqr {p : Participant} {stateIdx : Nat} {st : TRState} {tr : ExecTrace}
    (hget : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st) :
    Move.vis (.exposeSpqr p stateIdx) tr = [⟨.leak, [st.spqr], .leakRecord, some tr.length⟩] := by
  show [] ++ exposures tr (Move.next _ tr) = _
  rw [List.nil_append]
  have hnext : (Move.exposeSpqr p stateIdx).next tr =
      (tr.append (⟨.ExposedSpqr (st.sessionInfo p) st.spqr st.rIdx⟩ : TREntry)).append
        (⟨st.spqr⟩ : Network.ExecEntryT) := by
    rw [exposeSpqr_next_eq]; unfold TripleRatchet.exposeSpqr
    rw [run_bind_snd, hget, getLocalState_snd]
    simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  rw [hnext]; exact exposures_append_tr_pair tr _ _ trivial

theorem visOf_exposeKey_rk {p : Participant} {stateIdx : Nat} {st : TRState} {tr : ExecTrace}
    (hget : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st) :
    Move.vis (.exposeKey p stateIdx .rk) tr = [⟨.leak, [st.rk], .leakRecord, some tr.length⟩] := by
  show [] ++ exposures tr (Move.next _ tr) = _
  rw [List.nil_append]
  have hnext : (Move.exposeKey p stateIdx .rk).next tr =
      (tr.append (⟨.ExposedRK (st.sessionInfo p) st.rk st.rIdx⟩ : TREntry)).append
        (⟨st.rk⟩ : Network.ExecEntryT) := by
    rw [exposeKey_next_eq]; unfold TripleRatchet.exposeKey
    rw [run_bind_snd, hget, getLocalState_snd]
    simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  rw [hnext]; exact exposures_append_tr_pair tr _ _ trivial

theorem visOf_exposeKey_dhs {p : Participant} {stateIdx : Nat} {st : TRState} {tr : ExecTrace}
    (hget : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st) :
    Move.vis (.exposeKey p stateIdx .dhs) tr = [⟨.leak, [st.dhs], .leakRecord, some tr.length⟩] := by
  show [] ++ exposures tr (Move.next _ tr) = _
  rw [List.nil_append]
  have hnext : (Move.exposeKey p stateIdx .dhs).next tr =
      (tr.append (⟨.ExposedDHs (st.sessionInfo p) st.dhs st.rIdx⟩ : TREntry)).append
        (⟨st.dhs⟩ : Network.ExecEntryT) := by
    rw [exposeKey_next_eq]; unfold TripleRatchet.exposeKey
    rw [run_bind_snd, hget, getLocalState_snd]
    simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  rw [hnext]; exact exposures_append_tr_pair tr _ _ trivial

theorem visOf_exposeKey_cks {p : Participant} {stateIdx : Nat} {st : TRState} {tr : ExecTrace}
    (hget : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st) :
    Move.vis (.exposeKey p stateIdx .cks) tr = [⟨.leak, [st.cks], .leakRecord, some tr.length⟩] := by
  show [] ++ exposures tr (Move.next _ tr) = _
  rw [List.nil_append]
  have hnext : (Move.exposeKey p stateIdx .cks).next tr =
      (tr.append (⟨.ExposedCKs (st.sessionInfo p) st.cks st.ns st.rIdx⟩ : TREntry)).append
        (⟨st.cks⟩ : Network.ExecEntryT) := by
    rw [exposeKey_next_eq]; unfold TripleRatchet.exposeKey
    rw [run_bind_snd, hget, getLocalState_snd]
    simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  rw [hnext]; exact exposures_append_tr_pair tr _ _ trivial

theorem visOf_exposeKey_ckr {p : Participant} {stateIdx : Nat} {st : TRState}
    {pk : DY.Bytes} {c : RecvChain} {tr : ExecTrace}
    (hget : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st)
    (hf : findRecvChain st.recv pk = some c) :
    Move.vis (.exposeKey p stateIdx (.ckr pk)) tr = [⟨.leak, [c.chainKey], .leakRecord, some tr.length⟩] := by
  show [] ++ exposures tr (Move.next _ tr) = _
  rw [List.nil_append]
  have hnext : (Move.exposeKey p stateIdx (.ckr pk)).next tr =
      (tr.append (⟨.ExposedCKr (st.sessionInfo p) c.chainKey c.index c.rIdx⟩ : TREntry)).append
        (⟨c.chainKey⟩ : Network.ExecEntryT) := by
    rw [exposeKey_next_eq]; unfold TripleRatchet.exposeKey
    rw [run_bind_snd, hget, getLocalState_snd]
    simp [hf, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  rw [hnext]; exact exposures_append_tr_pair tr _ _ trivial

theorem visOf_exposeSkipped {skIdx : Nat} {tr : ExecTrace}
    {s : SessionInfo} {pk : DY.Bytes} {n : UInt32} {seed : DY.Bytes} {rIdx srcIdx : Nat}
    (hat : (tr.at? skIdx : Option TREntry) = some ⟨.SkippedKeyStored s pk n seed rIdx srcIdx⟩)
    (hru : (!receiverKeyUsedB tr s seed n rIdx) = true) :
    Move.vis (.exposeSkipped skIdx) tr = [⟨.leak, [seed], .leakRecord, some tr.length⟩] := by
  show [] ++ exposures tr (Move.next _ tr) = _
  rw [List.nil_append]
  have hnext : (Move.exposeSkipped skIdx).next tr =
      (tr.append (⟨.ExposedMK s seed n rIdx⟩ : TREntry)).append (⟨seed⟩ : Network.ExecEntryT) := by
    rw [exposeSkipped_next_eq]; unfold TripleRatchet.exposeSkipped
    simp only [Traceful.run_bind, Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk, hat, guardTrace, hru, ↓reduceIte,
      Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_pure]
  rw [hnext]; exact exposures_append_tr_pair tr _ _ trivial

/-! ## `AppendsOnlyExposure` for Exposure Moves -/

/-- Every entry appended is not a stored-state snapshot (`StEntry`), and any protocol event entry
(`TREntry`) is an exposure event (`IsAnyExposureEv`). -/
def IsExposureEntry (ent : ExecTrace.Entry) : Prop :=
  (TraceEntryHas.proj ent : Option StEntry) = none ∧
  ∀ ev : TREntry, TraceEntryHas.proj ent = some ev → IsAnyExposureEv ev.ev

/-- Every entry appended from `t` to `t'` satisfies `IsExposureEntry`. -/
def AppendsOnlyExposure (t t' : ExecTrace) : Prop :=
  t ≤ t' ∧ ∀ i (h : i < t'.length), t.length ≤ i → IsExposureEntry (t'.at i h)

theorem AppendsOnlyExposure.refl (t : ExecTrace) : AppendsOnlyExposure t t :=
  ⟨Trace.le_refl t, fun _ h hi => by omega⟩

theorem AppendsOnlyExposure.trans {t t1 t2 : ExecTrace}
    (a : AppendsOnlyExposure t t1) (b : AppendsOnlyExposure t1 t2) :
    AppendsOnlyExposure t t2 := by
  refine ⟨Trace.le_trans _ _ _ a.1 b.1, fun i h hi => ?_⟩
  by_cases hl : i < t1.length
  · rw [← Trace.at_le t1 t2 i hl b.1]; exact a.2 i hl hi
  · exact b.2 i h (by omega)

theorem AppendsOnlyExposure.pair (t : ExecTrace) (ev : TREvent) (msg : DY.Bytes)
    (hev : IsAnyExposureEv ev) :
    AppendsOnlyExposure t ((t.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)) := by
  refine ⟨Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _), fun i h hi => ?_⟩
  have hlen : (((t.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT))).length =
      t.length + 2 := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases (show i = t.length ∨ i = t.length + 1 by omega) with rfl | rfl
  · have : ((t.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).at t.length h =
        TraceEntryHas.inj (⟨ev⟩ : TREntry) := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [this]; refine ⟨rfl, fun ev' hev' => ?_⟩
    rw [proj_inj] at hev'; cases hev'; exact hev
  · have : ((t.append (⟨ev⟩ : TREntry)).append (⟨msg⟩ : Network.ExecEntryT)).at (t.length + 1) h =
        TraceEntryHas.inj (⟨msg⟩ : Network.ExecEntryT) := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [this]; exact ⟨rfl, fun _ he => by cases he⟩

theorem exposeSpqr_appendsOnlyExposure (me : Participant) (stH : Nat) (t : ExecTrace) :
    AppendsOnlyExposure t ((TripleRatchet.exposeSpqr me stH).run t).2.val := by
  unfold TripleRatchet.exposeSpqr
  rw [run_bind_snd, getLocalState_fst, getLocalState_snd]
  rcases (t.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · exact AppendsOnlyExposure.refl t
  · dsimp only
    by_cases hp : p = me
    · simp only [hp, ↓reduceIte, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact AppendsOnlyExposure.pair t _ _ trivial
    · simp only [hp, ↓reduceIte]; exact AppendsOnlyExposure.refl t

theorem exposeKey_appendsOnlyExposure (me : Participant) (stH : Nat) (k : KeyComponent)
    (t : ExecTrace) :
    AppendsOnlyExposure t ((TripleRatchet.exposeKey me stH k).run t).2.val := by
  unfold TripleRatchet.exposeKey
  rw [run_bind_snd, getLocalState_fst, getLocalState_snd]
  rcases (t.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · exact AppendsOnlyExposure.refl t
  · dsimp only
    by_cases hp : p = me
    · simp only [hp, ↓reduceIte]
      cases k with
      | rk | dhs | cks =>
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
          Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
        exact AppendsOnlyExposure.pair t _ _ trivial
      | ckr pk =>
        cases hf : findRecvChain st.recv pk with
        | none => simp only [hf, Traceful.run_failure]; exact AppendsOnlyExposure.refl t
        | some c =>
          simp only [hf, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
            Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
          exact AppendsOnlyExposure.pair t _ _ trivial
    · simp only [hp, ↓reduceIte]; exact AppendsOnlyExposure.refl t

theorem exposeSkipped_appendsOnlyExposure (evH : Nat) (t : ExecTrace) :
    AppendsOnlyExposure t ((TripleRatchet.exposeSkipped evH).run t).2.val := by
  rcases exposeSkipped_trace evH t with heq | ⟨s, seed, n, r, heq⟩
  · rw [heq]; exact AppendsOnlyExposure.refl t
  · rw [heq]; exact AppendsOnlyExposure.pair t _ _ trivial

/-! ## Preservation of `TRRecordStateInv` and `TRNsBound` -/

private theorem at?_stEntry_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : AppendsOnlyExposure t t') (i : Nat) :
    (t'.at? i : Option StEntry) = (t.at? i : Option StEntry) := by
  by_cases hi : i < t.length
  · have hi' : i < t'.length := Nat.lt_of_lt_of_le hi (Trace.length_le t t' h.1)
    simp only [Trace.at?, hi, hi', ↓reduceDIte, Trace.at_le t t' i hi h.1]
  · by_cases hi' : i < t'.length
    · simp only [Trace.at?, hi, hi', ↓reduceDIte, (h.2 i hi' (Nat.le_of_not_lt hi)).1]
    · simp only [Trace.at?, hi, hi', ↓reduceDIte]

theorem getLocalState_fst_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : AppendsOnlyExposure t t') (me : Participant) (stH : Nat) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run t').1 =
      ((PersistentLocalState.getLocalState me stH : Traceful TRState).run t).1 := by
  rw [getLocalState_fst, getLocalState_fst, at?_stEntry_of_appendsOnlyExposure h]

theorem isCurrentSnapshot_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : AppendsOnlyExposure t t') (stateIdx : Nat) :
    isCurrentSnapshot t' stateIdx = isCurrentSnapshot t stateIdx := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [at?_stEntry_of_appendsOnlyExposure h stateIdx]
  rcases hat : (t.at? stateIdx : Option StEntry) with _ | e
  · rfl
  · dsimp only
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_range'_1]
    constructor
    · intro h1 j ⟨hj_lo, hj_hi⟩
      have hlen := Trace.length_le t t' h.1
      have hj := h1 j ⟨hj_lo, by omega⟩
      rwa [at?_stEntry_of_appendsOnlyExposure h j] at hj
    · intro h1 j ⟨hj_lo, _⟩
      rw [at?_stEntry_of_appendsOnlyExposure h j]
      rcases hj_at : (t.at? j : Option StEntry) with _ | e'
      · rfl
      · have hj_lt : j < t.length := by
          have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) t j
          rwa [hj_at] at this
        have hj := h1 j ⟨hj_lo, by omega⟩
        rwa [hj_at] at hj

theorem trNsBound_of_appendsOnlyExposure
    {r₀ : ProtocolSetup} {ms ms' : List Move} {sent : List HwBytes}
    (hexp : AppendsOnlyExposure (runTraceMoves r₀ ms) (runTraceMoves r₀ ms'))
    (hbnd : TRNsBound r₀ ms sent) :
    TRNsBound r₀ ms' sent := by
  intro p stateIdx st hget
  rw [getLocalState_fst_of_appendsOnlyExposure hexp] at hget
  exact hbnd p stateIdx st hget

theorem forall₂_append {α β : Type} {R : α → β → Prop}
    {l₁ l₁' : List α} {l₂ l₂' : List β}
    (h1 : List.Forall₂ R l₁ l₂) (h2 : List.Forall₂ R l₁' l₂') :
    List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂') := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact List.Forall₂.cons h ih

end Symbolic.Swarm.CREF.TR
