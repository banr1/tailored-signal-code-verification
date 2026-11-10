/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Actions.PersistentGlobalState
import all DY.Actions.PersistentGlobalState

public section

namespace Symbolic.DYBridge

theorem DY.PersistentGlobalState.getGlobalState_eq_1 :
    ∀ {StateT : Type} [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has (DY.PersistentGlobalState.State.ExecEntryT StateT)] (handle : Nat),
      DY.PersistentGlobalState.getGlobalState handle = (do
          let e : DY.PersistentGlobalState.State.ExecEntryT StateT ← DY.getEntry handle
          pure e.st) :=
  @_root_.DY.PersistentGlobalState.getGlobalState.eq_1

theorem DY.PersistentGlobalState.storeGlobalState_eq_1 :
    ∀ {StateT : Type} [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has (DY.PersistentGlobalState.State.ExecEntryT StateT)] (st : StateT),
      DY.PersistentGlobalState.storeGlobalState st = DY.appendEntry ({ st := st } : DY.PersistentGlobalState.State.ExecEntryT StateT) :=
  @_root_.DY.PersistentGlobalState.storeGlobalState.eq_1

theorem DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
    [DY.BytesFunctor] [DY.ExecTraceTypes] (StateT : Type)
    (tr : DY.ExecTrace) (entry : DY.PersistentGlobalState.State.ExecEntryT StateT) (b : DY.Bytes) :
    (DY.PersistentGlobalState.State.baseAttackerKnowledge StateT).attackerKnows tr entry b = False := by rfl

end Symbolic.DYBridge

end
