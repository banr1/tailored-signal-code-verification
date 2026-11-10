/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.EquationalTheory.Trunc
public import DY.Bytes.AttackerKnowledgeTheorem

/-!
# Truncation Equational Theory Lemmas

Symbolic injectivity, length, attacker-knowledge, and byte-invariant instances for 8-byte
truncation `DY.Trunc.trunc8`.
-/

@[expose] public section

namespace DY.Trunc

section Constructors

variable [BytesFunctor] [BytesFunctor.Has SubF]

theorem trunc8_inj
  (inp1 inp2: Bytes)
  :
    trunc8 inp1 = trunc8 inp2 →
    inp1 = inp2
:= by
  simp only [trunc8]
  grind

@[simp]
theorem length_trunc8
  [BytesLength] [BytesLength.Has SubF.length]
  (inp: Bytes)
  : Bytes.length (trunc8 inp) = Nat.min inp.length trunc8Length
:= by
  simp only [trunc8]
  grind [Trunc8.SubF.length]

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

theorem attacker_knows_trunc8
  (inp: Bytes) (tr: ExecTrace)
  : inp.AttackerKnows tr →
    (trunc8 inp).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove trunc8.attackerKnowledge
  simp only [trunc8.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/-- Partial byte invariants for `Trunc8.SubF`, delegating well-formedness, label, and invariant to
the input term. -/
def Trunc8.invariants: Bytes.PartialInvariants Trunc8.SubF where
  well_formed := fun {input := input} rec tr =>
    (rec input) tr

  usage := fun {input := input} rec tr => Usage.nothing

  label := fun {input := input} rec tr =>
    (rec input) tr

  invariant := fun {input := input} rec tr =>
    (rec input) tr

theorem Trunc8.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Trunc8.invariants where

end Definition

#combine into
  BytesInvariants,
  BytesInvariantsProofs
from
  Trunc8,

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
theorem trunc8.label
  (inp: Bytes) (tr: ProofTrace)
  : (trunc8 inp).label tr = inp.label tr
:= by
  simp [trunc8, Bytes.label.eq, Trunc8.invariants]

@[simp]
theorem trunc8.Invariant
  (inp: Bytes) (tr: ProofTrace)
  :
    (trunc8 inp).Invariant tr =
    inp.Invariant tr
:= by
  simp [trunc8, Bytes.Invariant.eq, Trunc8.invariants]

end Invariants

section HoareTriples

instance
  [BytesFunctor] [BytesFunctor.Has SubF]
  [ExecTraceTypes] [ProofTraceTypes]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (b: Bytes)
  : HoareTriplePure
    (trunc8 b)
    (fun tr => b.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = b.label tr
    )
where
  pf := by
    simp

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

instance: SubAttackerKnowledgeTheorem trunc8.attackerKnowledge where
  pf := by
    simp only [trunc8.attackerKnowledge]
    intro out tr h_tr ⟨inp, ⟨ h_out, h_inp ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  trunc8,

end AttackerKnowledgeTheorem

end DY.Trunc
