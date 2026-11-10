/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.EquationalTheory.DiffieHellman
import all DY.EquationalTheory.DiffieHellman

public section

namespace Symbolic.DYBridge

theorem DY.DiffieHellman.dhPk.attackerKnowledge_pred
    [DY.BytesFunctor] [DY.BytesFunctor.Has DY.DiffieHellman.SubF]
    (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.DiffieHellman.dhPk.attackerKnowledge.pred p out =
      (∃ sk, out = DY.DiffieHellman.dhPk sk ∧ p sk) := by rfl

theorem DY.DiffieHellman.dh.attackerKnowledge_pred
    [DY.BytesFunctor] [DY.BytesFunctor.Has DY.DiffieHellman.SubF]
    (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.DiffieHellman.dh.attackerKnowledge.pred p out =
      (∃ pk sk, out = DY.DiffieHellman.dh pk sk ∧ p pk ∧ p sk) := by rfl

end Symbolic.DYBridge

end
