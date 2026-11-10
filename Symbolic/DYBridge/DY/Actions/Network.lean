/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Actions.Network
import all DY.Actions.Network

public section

namespace Symbolic.DYBridge

theorem DY.Trace.MessageSentAt_eq_1 :
    ∀ [DY.BytesFunctor] [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has DY.Network.ExecEntryT] (tr : DY.ExecTrace) (b : DY.Bytes) (i : Nat),
      DY.Trace.MessageSentAt tr b i = (DY.Trace.at? tr i = some ({ msg := b } : DY.Network.ExecEntryT)) :=
  @_root_.DY.Trace.MessageSentAt.eq_1

theorem DY.Trace.MessageSent_eq_1 :
    ∀ [DY.BytesFunctor] [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has DY.Network.ExecEntryT] (tr : DY.ExecTrace) (b : DY.Bytes),
      DY.Trace.MessageSent tr b = (∃ i, DY.Trace.MessageSentAt tr b i) :=
  @_root_.DY.Trace.MessageSent.eq_1

theorem DY.Trace.getMessageSentAt_eq_1 [DY.BytesFunctor] [DY.ExecTraceTypes]
    [DY.ExecTraceTypes.Has DY.Network.ExecEntryT] (i : Nat) (tr : DY.ExecTrace) :
    DY.Trace.getMessageSentAt i tr =
      match (DY.Trace.at? tr i : Option DY.Network.ExecEntryT) with
      | none => none
      | some entry => some entry.msg :=
  @_root_.DY.Trace.getMessageSentAt.eq_1 _ _ _ i tr

theorem DY.Network.sendMessage_eq_1 :
    ∀ [DY.BytesFunctor] [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has DY.Network.ExecEntryT] (msg : DY.Bytes),
      DY.Network.sendMessage msg = DY.appendEntry ({ msg := msg } : DY.Network.ExecEntryT) :=
  @_root_.DY.Network.sendMessage.eq_1

theorem DY.Network.receiveMessage_eq_1 :
    ∀ [DY.BytesFunctor] [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has DY.Network.ExecEntryT] (handle : Nat),
      DY.Network.receiveMessage handle = (do
          let msg : DY.Network.ExecEntryT ← DY.getEntry handle
          pure msg.msg) :=
  @_root_.DY.Network.receiveMessage.eq_1

theorem DY.Network.baseAttackerKnowledge_attackerKnows
    [DY.BytesFunctor] [DY.ExecTraceTypes]
    (tr : DY.ExecTrace) (entry : DY.Network.ExecEntryT) (msg : DY.Bytes) :
    DY.Network.baseAttackerKnowledge.attackerKnows tr entry msg = (msg = entry.msg) := by rfl

end Symbolic.DYBridge

end
