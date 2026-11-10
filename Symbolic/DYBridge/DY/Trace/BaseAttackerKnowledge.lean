/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Trace.BaseAttackerKnowledge
import all DY.Trace.BaseAttackerKnowledge

public section

namespace Symbolic.DYBridge

theorem DY.Trace.BaseAttackerKnows_eq_1 :
    ∀ [DY.BytesFunctor] [DY.ExecTraceTypes]
      [DY.BaseAttackerKnowledge] (b : DY.Bytes),
      DY.Trace.nil.BaseAttackerKnows b = False :=
  @_root_.DY.Trace.BaseAttackerKnows.eq_1

theorem DY.Trace.BaseAttackerKnows_eq_2 :
    ∀ [DY.BytesFunctor] [DY.ExecTraceTypes]
      [DY.BaseAttackerKnowledge] (b : DY.Bytes) (trBefore : DY.Trace DY.ExecTrace.Entry)
      (entry : DY.ExecTrace.Entry),
      (trBefore.snoc entry).BaseAttackerKnows b =
        (DY.BaseAttackerKnowledge.attackerKnows.attackerKnows trBefore entry b ∨ trBefore.BaseAttackerKnows b) :=
  @_root_.DY.Trace.BaseAttackerKnows.eq_2

theorem DY.SubBaseAttackerKnowledge.combine_attackerKnows
    [DY.BytesFunctor] [DY.ExecTraceTypes] {n : Nat} {Types : Fin n → Type}
    (subs : (id : Fin n) → DY.SubBaseAttackerKnowledge (Types id))
    (tr : DY.ExecTrace) (x : DY.ExecTraceTypes.combine Types) (b : DY.Bytes) :
    (DY.SubBaseAttackerKnowledge.combine subs).attackerKnows tr x b =
      (subs x.id).attackerKnows tr x.entry b := by
  cases x
  rfl

end Symbolic.DYBridge

end
