/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Bytes.AttackerKnowledge
import all DY.Bytes.AttackerKnowledge

public section

namespace Symbolic.DYBridge

theorem DY.Bytes.AttackerKnows.baseKnowledge_eq_1 :
    ∀ [DY.BytesFunctor] [DY.ExecTraceTypes]
      [DY.BaseAttackerKnowledge] (tr : DY.ExecTrace),
      DY.Bytes.AttackerKnows.baseKnowledge tr = DY.SubAttackerKnowledge.fromPred (DY.Trace.BaseAttackerKnows tr) :=
  @_root_.DY.Bytes.AttackerKnows.baseKnowledge.eq_1

theorem DY.SubAttackerKnowledge.combine'_pred
    [DY.BytesFunctor] {SubF : Type → Type} {t : Type}
    (atts : t → DY.SubAttackerKnowledge SubF) :
    (DY.SubAttackerKnowledge.combine' atts).pred =
      DY.Fixpoint.combine fun id => (atts id).pred := by
  rfl

end Symbolic.DYBridge

end
