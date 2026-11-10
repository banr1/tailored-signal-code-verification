/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import DY.Bytes.AttackerKnowledgeTheorem

@[expose] public section

set_option autoImplicit false

/-!
# Destructor, attacker-knowledge, and invariant lemmas for `TrWire`

Proves `trWireMsgFields?` round-trip and inversion, attacker-knowledge introduction and projection
rules for `trWireMsg`, and `BytesInvariants` and `SubAttackerKnowledgeTheorem` instances.
-/

namespace DY.TrWire

section Constructors

variable [BytesFunctor] [BytesFunctor.Has SubF]

theorem trWireMsgFields?_trWireMsg (v: UInt8) (rk: Bytes) (c pc: UInt32) (ct pq: Bytes)
    (ev: EncodingVariation) :
    trWireMsgFields? (trWireMsg v rk c pc ct pq ev) = some ⟨v, rk, c, pc, ct, pq, ev⟩ := by
  simp only [trWireMsgFields?, trWireMsg]
  grind

theorem trWireMsg_of_fields? {b: Bytes} {x: TrWireMsg.SubF Bytes}
    (h: trWireMsgFields? b = some x) :
    b = trWireMsg x.version x.senderRatchetKey x.counter x.previousCounter x.ciphertext
      x.pqRatchet x.encodingVariation := by
  have := Bytes.pack_view? TrWireMsg.SubF b
  simp only [trWireMsgFields?] at h
  simp only [h] at this
  exact this.symm

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

theorem attacker_knows_trWireMsg (v: UInt8) (rk: Bytes) (c pc: UInt32) (ct pq: Bytes)
    (ev: EncodingVariation) (tr: ExecTrace) :
    rk.AttackerKnows tr → ct.AttackerKnows tr → pq.AttackerKnows tr →
    (trWireMsg v rk c pc ct pq ev).AttackerKnows tr := by
  intro h1 h2 h3
  apply Bytes.AttackerKnows.prove trWireMsg.attackerKnowledge
  exact ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, h1, h2, h3⟩

theorem attacker_knows_trWireMsg_args (v: UInt8) (rk: Bytes) (c pc: UInt32) (ct pq: Bytes)
    (ev: EncodingVariation) (tr: ExecTrace) :
    (trWireMsg v rk c pc ct pq ev).AttackerKnows tr →
    rk.AttackerKnows tr ∧ ct.AttackerKnows tr ∧ pq.AttackerKnows tr := by
  intro h
  have arg : ∀ out, (out = rk ∨ out = ct ∨ out = pq) →
      out.AttackerKnows tr := fun out hout => by
    apply Bytes.AttackerKnows.prove trWireMsgArg.attackerKnowledge
    exact ⟨⟨v, rk, c, pc, ct, pq, ev⟩, h, hout⟩
  exact ⟨arg _ (by simp), arg _ (by simp), arg _ (by simp)⟩

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/-- Well-formed and invariant if every `Bytes` argument is; label is the meet of the three `Bytes`
arguments' labels. -/
def TrWireMsg.invariants: Bytes.PartialInvariants TrWireMsg.SubF where
  well_formed := fun {senderRatchetKey := rk, ciphertext := ct, pqRatchet := pq, ..} rec tr =>
    (rec rk) tr ∧ (rec ct) tr ∧ (rec pq) tr
  usage := fun _ _ _ => Usage.nothing
  label := fun {senderRatchetKey := rk, ciphertext := ct, pqRatchet := pq, ..} rec tr =>
    Label.meet ((rec rk) tr) (Label.meet ((rec ct) tr) ((rec pq) tr))
  invariant := fun {senderRatchetKey := rk, ciphertext := ct, pqRatchet := pq, ..} rec tr =>
    (rec rk) tr ∧ (rec ct) tr ∧ (rec pq) tr

theorem TrWireMsg.invariantsProofs [BytesInvariants]:
    Bytes.PartialInvariantsProofs TrWireMsg.invariants where

end Definition

#combine into
  BytesInvariants,
  BytesInvariantsProofs
from
  TrWireMsg,

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
theorem trWireMsg.label
    (v: UInt8) (rk: Bytes) (c pc: UInt32) (ct pq: Bytes) (ev: EncodingVariation)
    (tr: ProofTrace) :
    (trWireMsg v rk c pc ct pq ev).label tr =
      Label.meet (rk.label tr) (Label.meet (ct.label tr) (pq.label tr)) := by
  simp [trWireMsg, Bytes.label.eq, TrWireMsg.invariants]

@[simp]
theorem trWireMsg.Invariant
    (v: UInt8) (rk: Bytes) (c pc: UInt32) (ct pq: Bytes) (ev: EncodingVariation)
    (tr: ProofTrace) :
    (trWireMsg v rk c pc ct pq ev).Invariant tr =
      (rk.Invariant tr ∧ ct.Invariant tr ∧ pq.Invariant tr) := by
  simp [trWireMsg, Bytes.Invariant.eq, TrWireMsg.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

instance: SubAttackerKnowledgeTheorem trWireMsg.attackerKnowledge where
  pf := by
    simp only [trWireMsg.attackerKnowledge]
    intro out tr h_tr ⟨⟨v, rk, c, pc, ct, pq, ev⟩, h_out, h_args⟩
    subst h_out
    change Bytes.Publishable (trWireMsg v rk c pc ct pq ev) tr
    simp only [Bytes.Publishable, trWireMsg.Invariant, trWireMsg.label] at *
    grind

instance: SubAttackerKnowledgeTheorem trWireMsgArg.attackerKnowledge where
  pf := by
    simp only [trWireMsgArg.attackerKnowledge]
    intro out tr h_tr ⟨⟨v, rk, c, pc, ct, pq, ev⟩, h_in, h_out⟩
    change Bytes.Publishable (trWireMsg v rk c pc ct pq ev) tr at h_in
    simp only [Bytes.Publishable, trWireMsg.Invariant, trWireMsg.label] at *
    grind

end AttackerKnowledgeTheorem

section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into
  SubAttackerKnowledgeTheorem' from
  trWireMsg,
  trWireMsgArg,

end AttackerKnowledgeTheorem

end DY.TrWire
