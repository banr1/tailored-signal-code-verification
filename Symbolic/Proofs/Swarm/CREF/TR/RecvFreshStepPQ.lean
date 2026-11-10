/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.Trace.Basic
import DY.Trace.Monad
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Frame Preservation of Receiver Freshness

Proves one-move preservation of `TRRecvFreshAll r₀` across moves that store no `TRState` and
log no receiver `TREvent`: key-compromise moves, `Move.reject`, and `Move.attackerSend`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot)
open DY.Libsignal.PQXDH (PQXDHEvent)
open Symbolic.Swarm.CREF.TR.RecvDec (StEntry TREntry at?_append_non_entry
  isCurrentSnapshot_append_non_st getLocalState_fst)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves Preserves.bind Preserves.pure Preserves.guardP
  Preserves.getLocalState_pq)

/-- `TRRecvFreshAll r₀` stated as a predicate on an arbitrary execution trace. -/
def rfs_RF (r₀ : ProtocolSetup) (tr : ExecTrace) : Prop :=
  ∀ q stateIdx st,
    (q = r₀.alice ∨ q = r₀.bob) →
    ((PersistentLocalState.getLocalState q stateIdx : Traceful TRState).run tr).1 = some st →
    isCurrentSnapshot tr stateIdx = true →
    TRRecvCountersFresh tr q st ∧ TRSkippedRIdxChainRel tr q st

theorem rfs_RF_iff (r₀ : ProtocolSetup) (ms : List Move) :
    TRRecvFreshAll r₀ ms ↔ rfs_RF r₀ (runTraceMoves r₀ ms) := Iff.rfl

private theorem rfs_eventLoggedAt_append_non_tr {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (ev : TREvent) (i : Nat) :
    (tr.append e).EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rw [at?_append_non_entry tr e hnone i]

theorem rfs_RF_append_non {E : Type} [ExecTraceTypes.Has E] {r₀ : ProtocolSetup} {tr : ExecTrace}
    (e : E)
    (hnone_st : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (hnone_tr : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : rfs_RF r₀ tr) : rfs_RF r₀ (tr.append e) := by
  intro q stateIdx st hq hget hcur
  rw [getLocalState_fst, at?_append_non_entry _ e hnone_st, ← getLocalState_fst] at hget
  rw [isCurrentSnapshot_append_non_st _ e hnone_st] at hcur
  obtain ⟨hcf, hsk⟩ := h q stateIdx st hq hget hcur
  exact ⟨trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ i hev => (rfs_eventLoggedAt_append_non_tr tr e hnone_tr _ i).mp hev)
      (fun _ _ _ _ _ i hev => (rfs_eventLoggedAt_append_non_tr tr e hnone_tr _ i).mp hev) hcf,
    trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ i hev => (rfs_eventLoggedAt_append_non_tr tr e hnone_tr _ i).mp hev) hsk⟩

section Prims
variable {r₀ : ProtocolSetup}

theorem rfs_pres_sendMessage (m : DY.Bytes) :
    Preserves (rfs_RF r₀) (Network.sendMessage m) := by
  intro _ h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact rfs_RF_append_non (⟨m⟩ : DY.Network.ExecEntryT) rfl rfl h

theorem rfs_pres_logPQ (ev : PQXDHEvent) :
    Preserves (rfs_RF r₀) (ProtocolEvent.logEvent ev) := by
  intro _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact rfs_RF_append_non (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl rfl h

theorem rfs_pres_getKey (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (rfs_RF r₀) (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

end Prims

theorem rfs_snoc_of_pres {r₀ : ProtocolSetup} {ms : List Move} {m : Move}
    (hp : Preserves (rfs_RF r₀) m.act) (h : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀ (ms ++ [m]) := by
  rw [rfs_RF_iff, runTrace_snoc]
  exact hp _ h

theorem trRecvFreshAll_snoc_compromiseIK (r₀ : ProtocolSetup) (ms : List Move) (p : Participant)
    (stateIdx : Nat) (h : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀ (ms ++ [Move.compromiseIK p stateIdx]) := by
  refine rfs_snoc_of_pres ?_ h
  unfold Move.act DY.Libsignal.PQXDH.compromiseIK
  exact Preserves.bind (Preserves.bind (rfs_pres_getKey _ _ _) fun _ =>
    Preserves.bind (rfs_pres_logPQ _) fun _ => rfs_pres_sendMessage _) fun _ => Preserves.pure _

theorem trRecvFreshAll_snoc_compromiseSPK (r₀ : ProtocolSetup) (ms : List Move) (b : Participant)
    (stateIdx : Nat) (h : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀ (ms ++ [Move.compromiseSPK b stateIdx]) := by
  refine rfs_snoc_of_pres ?_ h
  unfold Move.act DY.Libsignal.PQXDH.compromiseSPK
  exact Preserves.bind (Preserves.bind (rfs_pres_getKey _ _ _) fun _ =>
    Preserves.bind (rfs_pres_logPQ _) fun _ => rfs_pres_sendMessage _) fun _ => Preserves.pure _

theorem trRecvFreshAll_snoc_compromisePQSPK (r₀ : ProtocolSetup) (ms : List Move) (b : Participant)
    (stateIdx : Nat) (h : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀ (ms ++ [Move.compromisePQSPK b stateIdx]) := by
  refine rfs_snoc_of_pres ?_ h
  unfold Move.act DY.Libsignal.PQXDH.compromisePQSPK
  exact Preserves.bind (Preserves.bind (rfs_pres_getKey _ _ _) fun _ =>
    Preserves.bind (rfs_pres_logPQ _) fun _ => rfs_pres_sendMessage _) fun _ => Preserves.pure _

theorem trRecvFreshAll_snoc_compromiseOPK (r₀ : ProtocolSetup) (ms : List Move) (b : Participant)
    (stateIdx : Nat) (h : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀ (ms ++ [Move.compromiseOPK b stateIdx]) := by
  refine rfs_snoc_of_pres ?_ h
  unfold Move.act DY.Libsignal.PQXDH.compromiseOPK
  exact Preserves.bind (Preserves.bind (rfs_pres_getKey _ _ _) fun _ =>
    Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (rfs_pres_logPQ _) fun _ => rfs_pres_sendMessage _) fun _ => Preserves.pure _

theorem trRecvFreshAll_snoc_reject (r₀ : ProtocolSetup) (ms : List Move) (draws : List Nat)
    (h : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀ (ms ++ [Move.reject draws]) :=
  rfs_snoc_of_pres (Preserves.pure _) h

theorem trRecvFreshAll_snoc_attackerSend (r₀ : ProtocolSetup) (ms : List Move) (t : DY.Bytes)
    (h : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀ (ms ++ [Move.attackerSend t]) := by
  refine rfs_snoc_of_pres ?_ h
  unfold Move.act
  exact Preserves.bind (rfs_pres_sendMessage _) fun _ => Preserves.pure _

end Symbolic.Swarm.CREF.TR
