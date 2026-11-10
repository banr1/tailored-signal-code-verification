/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Misc.Instances
public import DY.Bytes.AttackerKnowledge
import DY.Meta.CombineMacro

/-!
# Double Ratchet `SignalMessage` Wire Terms

Six-argument DyLean term constructor and attacker deduction rules for the MAC-authenticated portion
of a Double Ratchet `SignalMessage`.
-/

namespace DY.Wire

namespace WireMsg

public
structure SubF (Bytes: Type) where
  version: Bytes
  senderRatchetKey: Bytes
  counter: Bytes
  previousCounter: Bytes
  ciphertext: Bytes
  encodingVariation: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf
  | ⟨v, rk, c, pc, ct, ev⟩ => sizeOf v + sizeOf rk + sizeOf c + sizeOf pc + sizeOf ct + sizeOf ev

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 6 }
  toRepr | ⟨v, rk, c, pc, ct, ev⟩ => { id := (), data := (), as := #v[v, rk, c, pc, ct, ev] }
  fromRepr
  | {id, data, as} =>
    { version := as[0], senderRatchetKey := as[1], counter := as[2], previousCounter := as[3],
      ciphertext := as[4], encodingVariation := as[5] }
  from_to | ⟨v, rk, c, pc, ct, ev⟩ => by rfl
  to_from
  | {id, data, as} => by
    obtain ⟨⟨l⟩, hl⟩ := as
    match l, hl with
    | [_, _, _, _, _, _], _ => rfl
  sizeOf_eq | ⟨v, rk, c, pc, ct, ev⟩ => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun ⟨v, rk, c, pc, ct, ev⟩ rec => rec v + rec rk + rec c + rec pc + rec ct + rec ev

end WireMsg

#combine into BytesFunctor, BytesLength from
  WireMsg,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev WireMsg.SubF.pack (x: WireMsg.SubF Bytes) := BytesView.pack x

@[expose] public
def wireMsg.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ x: WireMsg.SubF Bytes,
      out = x.pack ∧
      p x.version ∧ p x.senderRatchetKey ∧ p x.counter ∧ p x.previousCounter ∧ p x.ciphertext ∧
      p x.encodingVariation

@[expose] public
def wireMsgArg.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ x: WireMsg.SubF Bytes,
      p x.pack ∧
      (out = x.version ∨ out = x.senderRatchetKey ∨ out = x.counter ∨ out = x.previousCounter ∨
        out = x.ciphertext ∨ out = x.encodingVariation)

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  wireMsg,
  wireMsgArg,

end DY.Wire
