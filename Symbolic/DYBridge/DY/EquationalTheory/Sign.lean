/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.EquationalTheory.Sign
import all DY.EquationalTheory.Sign

public section

namespace Symbolic.DYBridge

theorem DY.Signature.vk.attackerKnowledge_pred
    [DY.BytesFunctor] [DY.BytesFunctor.Has DY.Signature.SubF]
    (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Signature.vk.attackerKnowledge.pred p out =
      (∃ sk, out = DY.Signature.vk sk ∧ p sk) := by rfl

theorem DY.Signature.sign.attackerKnowledge_pred
    [DY.BytesFunctor] [DY.BytesFunctor.Has DY.Signature.SubF]
    (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Signature.sign.attackerKnowledge.pred p out =
      (∃ sk nonce msg, out = DY.Signature.sign sk nonce msg ∧ p sk ∧ p nonce ∧ p msg) := by rfl

end Symbolic.DYBridge

end
