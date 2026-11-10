/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Trace.Manipulation
import all DY.Trace.Manipulation

public section

namespace Symbolic.DYBridge

theorem DY.getEntry_eq_1 [DY.ExecTraceTypes] {EntryT : Type} [DY.ExecTraceTypes.Has EntryT]
    (timestamp : Nat) :
    (DY.getEntry timestamp : DY.Traceful EntryT) =
      DY.Traceful.mk fun tr =>
        ((DY.Trace.at? tr timestamp : Option EntryT), ⟨tr, DY.Trace.le_refl tr⟩) :=
  @_root_.DY.getEntry.eq_1 _ EntryT _ timestamp

theorem DY.appendEntry_eq_1 [DY.ExecTraceTypes] {EntryT : Type} [DY.ExecTraceTypes.Has EntryT]
    (entry : EntryT) :
    DY.appendEntry entry =
      DY.Traceful.mk fun tr =>
        (some tr.length, ⟨tr.append entry, DY.Trace.append_le tr entry⟩) :=
  @_root_.DY.appendEntry.eq_1 _ EntryT _ entry

theorem DY.getTimestamp_eq_1 [DY.ExecTraceTypes] :
    DY.getTimestamp =
      DY.Traceful.mk fun tr => (some tr.length, ⟨tr, DY.Trace.le_refl tr⟩) :=
  @_root_.DY.getTimestamp.eq_1 _

end Symbolic.DYBridge

end
