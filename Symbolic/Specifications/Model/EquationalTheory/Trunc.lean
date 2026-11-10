/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Bytes.AttackerKnowledge
public import Symbolic.Specifications.Model.EquationalTheory.Representable
import DY.Meta.CombineMacro

/-!
# 8-Byte MAC Truncation

DyLean term constructor and attacker deduction rule for 8-byte tag truncation (`MAC_LENGTH = 8`).
-/

namespace DY.Trunc

public
class CanTrunc8 (Bytes: Type u) where
  trunc8: (x: Bytes) → Bytes

export CanTrunc8 (trunc8)

@[expose] public
def trunc8Length := 8

namespace Trunc8

public
structure SubF (Bytes: Type) where
  input: Bytes

public instance: ALaCarte.FunctorSizeOf SubF := .unary SubF.input
public instance: SubBytesFunctor SubF := .unary SubF.input SubF.mk

@[expose] public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun ⟨input⟩ rec => Nat.min (rec input) trunc8Length

end Trunc8

#combine into BytesFunctor, BytesLength from
  Trunc8,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev Trunc8.SubF.pack (x: Trunc8.SubF Bytes) := BytesView.pack x

public
instance: CanTrunc8 Bytes where
  trunc8 input := ({input}: Trunc8.SubF Bytes).pack

@[expose] public
def trunc8.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ inp, out = trunc8 inp ∧ p inp

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  trunc8,

end DY.Trunc
