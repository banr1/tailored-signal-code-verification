/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Actions.Random
import all DY.Actions.Random

public section

namespace Symbolic.DYBridge

theorem DY.Random.genRand_eq_1 [DY.BytesFunctor] [DY.BytesFunctor.Has DY.Random.SubF]
    [DY.ExecTraceTypes] [DY.ExecTraceTypes.Has DY.Random.ExecEntryT] (size : Nat) :
    DY.Random.genRand size = (do
      let time ← DY.appendEntry ({ length := size } : DY.Random.ExecEntryT)
      pure (({ timestamp := time, size := size } : DY.Random.Random DY.Bytes).pack)) :=
  @_root_.DY.Random.genRand.eq_1 _ _ _ _ size

theorem DY.Random.Random.length_eq_1 :
    ∀ [DY.BytesFunctor] (timestamp size : Nat)
      (x_2 :
      (y : DY.Bytes) →
      autoParam (sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf ({ timestamp := timestamp, size := size } : DY.Random.Random DY.Bytes))
      DY.Bytes.PartialFunction._auto_1 →
      Nat),
      ({ timestamp := timestamp, size := size } : DY.Random.Random DY.Bytes).length @x_2 = size :=
  @_root_.DY.Random.Random.length.eq_1

theorem DY.Random.attKnowsRand_pred [DY.BytesFunctor] (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Random.attKnowsRand.pred p out = False := by rfl

theorem DY.Random.baseAttackerKnowledge_attackerKnows
    [DY.BytesFunctor] [DY.ExecTraceTypes]
    (tr : DY.ExecTrace) (entry : DY.Random.ExecEntryT) (b : DY.Bytes) :
    DY.Random.baseAttackerKnowledge.attackerKnows tr entry b = False := by rfl

end Symbolic.DYBridge

end
