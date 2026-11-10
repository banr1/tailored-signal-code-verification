/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Actions.ProtocolEvent
import all DY.Actions.ProtocolEvent

public section

namespace Symbolic.DYBridge

theorem DY.Trace.EventLoggedAt_eq_1 :
    ∀ {EventT : Type} [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT EventT)] (ev : EventT) (time : Nat) (tr : DY.ExecTrace),
      DY.Trace.EventLoggedAt ev time tr = (DY.Trace.at? tr time = some ({ ev := ev } : DY.ProtocolEvent.ExecEntryT EventT)) :=
  @_root_.DY.Trace.EventLoggedAt.eq_1

theorem DY.Trace.getEventAt_eq_1 (EventT : Type) [DY.ExecTraceTypes]
    [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT EventT)]
    (i : Nat) (tr : DY.ExecTrace) :
    DY.Trace.getEventAt EventT i tr =
      match (DY.Trace.at? tr i : Option (DY.ProtocolEvent.ExecEntryT EventT)) with
      | none => none
      | some entry => some entry.ev :=
  @_root_.DY.Trace.getEventAt.eq_1 EventT _ _ i tr

theorem DY.ProtocolEvent.logEvent_eq_1 :
    ∀ {EventT : Type} [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT EventT)] (ev : EventT),
      DY.ProtocolEvent.logEvent ev = (do
          let _ ← DY.appendEntry ({ ev := ev } : DY.ProtocolEvent.ExecEntryT EventT)
          pure ()) :=
  @_root_.DY.ProtocolEvent.logEvent.eq_1

theorem DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows
    [DY.BytesFunctor] [DY.ExecTraceTypes] (EventT : Type)
    (tr : DY.ExecTrace) (entry : DY.ProtocolEvent.ExecEntryT EventT) (b : DY.Bytes) :
    (DY.ProtocolEvent.baseAttackerKnowledge EventT).attackerKnows tr entry b = False := by rfl

end Symbolic.DYBridge

end
