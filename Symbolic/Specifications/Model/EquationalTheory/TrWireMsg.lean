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
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Triple Ratchet `SignalMessage` Wire Terms

DyLean term algebra and attacker deduction rules for the MAC-authenticated portion of a Triple
Ratchet `SignalMessage` (version byte plus protobuf body, parameterized by `EncodingVariation` for
non-canonical `prost` encodings).
-/

namespace DY.TrWire

/-- A protobuf wire value: varint (type 0), length-delimited bytes (type 2), or skipped payload
(types 1, 3, and 5). -/
public
inductive PbValue where
  | varint (n : Nat)
  | bytes (b : List (BitVec 8))
  | unknown (wireType : Nat) (payload : List (BitVec 8))
  deriving DecidableEq

@[expose] section

/-- One field occurrence of the `SignalMessage` protobuf body in wire order. -/
public
inductive FieldItem where
  /-- Known field `tag` (1 to 6) carrying its value from the message. -/
  | known (tag keyPad valuePad : Nat)
  /-- Overridden, repeated, or unknown field carrying an explicit `PbValue`. -/
  | extra (tag : Nat) (value : PbValue) (keyPad valuePad : Nat)
  deriving DecidableEq

/-- Injective `List Nat` encoding of a `FieldItem`. -/
public
def FieldItem.toNats : FieldItem → List Nat
  | .known t kp vp => [0, t, kp, vp]
  | .extra t (.varint n) kp vp => [1, t, kp, vp, n]
  | .extra t (.bytes b) kp vp => 2 :: t :: kp :: vp :: b.map BitVec.toNat
  | .extra t (.unknown wt p) kp vp => 3 :: t :: kp :: vp :: wt :: p.map BitVec.toNat

/-- Non-canonical protobuf and version-byte encoding choices accepted by `prost` and libsignal
relative to `canonicalVariation`. -/
public
structure EncodingVariation where
  /-- Low 4 bits of byte 0 (ignored by libsignal). -/
  versionLowNibble : Nat
  /-- Trailing bytes after the 32-byte key in field 1 (ignored by `PublicKey::deserialize`). -/
  ratchetKeyTrailingBytes : List (BitVec 8)
  /-- High bits above bit 31 in `known 2` varints (truncated by `as u32`). -/
  counterHigh : Nat
  /-- High bits above bit 31 in `known 3` varints (truncated by `as u32`). -/
  previousCounterHigh : Nat
  fields : List FieldItem
  deriving DecidableEq

end

/-- Canonical encoding emitted by `SignalMessage::new`: byte `0x44`, fields 1 to 4 in order, minimal
varints. -/
@[expose] public
def canonicalVariation : EncodingVariation :=
  ⟨4, [], 0, 0, [.known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0]⟩

public
class CanTrWireMsg (Bytes: Type u) where
  trWireMsg: (version: UInt8) → (senderRatchetKey: Bytes) → (counter previousCounter: UInt32) →
    (ciphertext pqRatchet: Bytes) → (encodingVariation: EncodingVariation) → Bytes

export CanTrWireMsg (trWireMsg)

namespace TrWireMsg

public
abbrev TrWireHeaderData := UInt8 × UInt32 × UInt32 × EncodingVariation

@[expose] public
def TrWireHeaderData.code (d : TrWireHeaderData) : List (List Nat) :=
  let (v, c, pc, ev) := d
  [v.toNat, c.toNat, pc.toNat, ev.versionLowNibble, ev.counterHigh, ev.previousCounterHigh] ::
    ev.ratchetKeyTrailingBytes.map BitVec.toNat :: ev.fields.map FieldItem.toNats

public
structure SubF (Bytes: Type) where
  version: UInt8
  senderRatchetKey: Bytes
  counter: UInt32
  previousCounter: UInt32
  ciphertext: Bytes
  pqRatchet: Bytes
  encodingVariation: EncodingVariation

public instance: ALaCarte.FunctorSizeOf SubF :=
  .ternary SubF.senderRatchetKey SubF.ciphertext SubF.pqRatchet

public instance: SubBytesFunctor SubF :=
  .ternaryByCode TrWireHeaderData.code
    (fun {x y} hcode => by
      have map_bv : ∀ {l₁ l₂ : List (BitVec 8)},
          l₁.map BitVec.toNat = l₂.map BitVec.toNat → l₁ = l₂ := by
        intro l₁; induction l₁ with
        | nil => intro l₂ hm; cases l₂ <;> simp at hm ⊢
        | cons a as ih =>
          intro l₂ hm; cases l₂ with
          | nil => simp at hm
          | cons b bs =>
            simp only [List.map, List.cons.injEq] at hm
            rw [BitVec.eq_of_toNat_eq hm.1, ih hm.2]
      have item_inj : ∀ {a b : FieldItem}, a.toNats = b.toNats → a = b := by
        intro a b hi
        rcases a with ⟨t₁, kp₁, vp₁⟩ | ⟨t₁, n₁ | b₁ | ⟨wt₁, p₁⟩, kp₁, vp₁⟩ <;>
        rcases b with ⟨t₂, kp₂, vp₂⟩ | ⟨t₂, n₂ | b₂ | ⟨wt₂, p₂⟩, kp₂, vp₂⟩ <;>
        simp only [FieldItem.toNats, List.cons.injEq] at hi <;> grind
      have map_item : ∀ {l₁ l₂ : List FieldItem},
          l₁.map FieldItem.toNats = l₂.map FieldItem.toNats → l₁ = l₂ := by
        intro l₁; induction l₁ with
        | nil => intro l₂ hm; cases l₂ <;> simp at hm ⊢
        | cons a as ih =>
          intro l₂ hm; cases l₂ with
          | nil => simp at hm
          | cons b bs =>
            simp only [List.map, List.cons.injEq] at hm
            rw [item_inj hm.1, ih hm.2]
      rcases x with ⟨v₁, c₁, pc₁, ⟨low₁, tr₁, ch₁, pch₁, fs₁⟩⟩
      rcases y with ⟨v₂, c₂, pc₂, ⟨low₂, tr₂, ch₂, pch₂, fs₂⟩⟩
      simp only [TrWireHeaderData.code, List.cons.injEq, and_true] at hcode
      obtain ⟨⟨hv, hc, hpc, rfl, rfl, rfl⟩, htr, hfs⟩ := hcode
      rw [UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hv),
          UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hc),
          UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hpc),
          map_bv htr, map_item hfs])
    (fun x => (x.version, x.counter, x.previousCounter, x.encodingVariation))
    SubF.senderRatchetKey SubF.ciphertext SubF.pqRatchet
    (fun d rk ct pq =>
      { version := d.1, senderRatchetKey := rk, counter := d.2.1, previousCounter := d.2.2.1,
        ciphertext := ct, pqRatchet := pq, encodingVariation := d.2.2.2 })

@[expose] public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun ⟨_, rk, _, _, ct, pq, _⟩ rec => 1 + rec rk + 4 + 4 + rec ct + rec pq

end TrWireMsg

#combine into BytesFunctor, BytesLength from
  TrWireMsg,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev TrWireMsg.SubF.pack (x: TrWireMsg.SubF Bytes) := BytesView.pack x

public
instance: CanTrWireMsg Bytes where
  trWireMsg version senderRatchetKey counter previousCounter ciphertext pqRatchet
      encodingVariation :=
    ({version, senderRatchetKey, counter, previousCounter, ciphertext, pqRatchet,
      encodingVariation}: TrWireMsg.SubF Bytes).pack

@[expose] public
def trWireMsgFields? (b: Bytes): Option (TrWireMsg.SubF Bytes) := b.view? TrWireMsg.SubF

@[expose] public
def trWireMsg.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ x: TrWireMsg.SubF Bytes,
      out = x.pack ∧ p x.senderRatchetKey ∧ p x.ciphertext ∧ p x.pqRatchet

@[expose] public
def trWireMsgArg.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ x: TrWireMsg.SubF Bytes,
      p x.pack ∧ (out = x.senderRatchetKey ∨ out = x.ciphertext ∨ out = x.pqRatchet)

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  trWireMsg,
  trWireMsgArg,

end DY.TrWire
