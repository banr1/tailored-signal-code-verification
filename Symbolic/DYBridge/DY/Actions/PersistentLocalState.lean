/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Actions.PersistentLocalState
import all DY.Actions.PersistentLocalState

public section

namespace Symbolic.DYBridge

theorem DY.PersistentLocalState.getLocalState_eq_1 :
    ∀ {StateT : Type} [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has (DY.PersistentLocalState.State.ExecEntryT StateT)] (participant : DY.Participant)
      (handle : Nat),
      DY.PersistentLocalState.getLocalState participant handle = (do
          let st : DY.PersistentLocalState.LocalState StateT ← DY.PersistentGlobalState.getGlobalState handle
          guard (st.participant = participant)
          pure st.state) :=
  @_root_.DY.PersistentLocalState.getLocalState.eq_1

theorem DY.PersistentLocalState.storeLocalState_eq_1 :
    ∀ {StateT : Type} [DY.ExecTraceTypes]
      [DY.ExecTraceTypes.Has (DY.PersistentLocalState.State.ExecEntryT StateT)] (participant : DY.Participant)
      (state : StateT),
      DY.PersistentLocalState.storeLocalState participant state =
        DY.PersistentGlobalState.storeGlobalState ({ participant := participant, state := state } : DY.PersistentLocalState.LocalState StateT) :=
  @_root_.DY.PersistentLocalState.storeLocalState.eq_1

end Symbolic.DYBridge

end
