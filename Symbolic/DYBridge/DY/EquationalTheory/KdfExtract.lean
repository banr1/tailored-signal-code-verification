/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.EquationalTheory.KdfExtract
import all DY.EquationalTheory.KdfExtract

public section

namespace Symbolic.DYBridge

theorem DY.KdfExtract.KdfExtract.SubF.length_eq_1 :
    ∀ [DY.BytesFunctor] (x : DY.KdfExtract.KdfExtract.SubF DY.Bytes)
      (x_1 :
      (y : DY.Bytes) → autoParam (sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x) DY.Bytes.PartialFunction._auto_1 → Nat),
      x.length @x_1 = 32 :=
  @_root_.DY.KdfExtract.KdfExtract.SubF.length.eq_1

theorem DY.KdfExtract.kdfExtract.attackerKnowledge_pred
    [DY.BytesFunctor] [DY.BytesFunctor.Has DY.KdfExtract.SubF]
    (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.KdfExtract.kdfExtract.attackerKnowledge.pred p out =
      (∃ salt ikm, out = DY.KdfExtract.kdfExtract salt ikm ∧ p salt ∧ p ikm) := by rfl

end Symbolic.DYBridge

end
