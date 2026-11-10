/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.EquationalTheory.SymEnc
public import DY.Bytes.AttackerKnowledgeTheorem

/-!
# Equational, attacker-knowledge, and invariant lemmas for `SymEnc`

Proves decryption round-trip and inversion (`symDec_symEnc`, `symDec_eq_some`), attacker-knowledge
closure (`attacker_knows_symEnc`, `attacker_knows_symDec`), and `BytesInvariants`, Hoare triples,
and `SubAttackerKnowledgeTheorem` instances parameterized by `SymEncPred`.
-/

@[expose] public section

namespace DY.SymEnc

section Constructors

variable [BytesFunctor] [BytesFunctor.Has SubF]

theorem symDec_symEnc
  (key iv msg: Bytes)
  : symDec key iv (symEnc key iv msg) = some msg
:= by
  simp only [symEnc, symDec]
  grind

theorem symDec_eq_some
  (key iv ct msg: Bytes)
  : symDec key iv ct = some msg → ct = symEnc key iv msg
:= by
  simp only [symEnc, symDec]
  split
  · rename_i key' iv' msg' heq
    have := Bytes.pack_view? Enc.SubF ct
    simp only [heq] at this
    split <;> grind
  · grind

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

theorem attacker_knows_symEnc
  (key iv msg: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    iv.AttackerKnows tr →
    msg.AttackerKnows tr →
    (symEnc key iv msg).AttackerKnows tr
:= by
  intro h_key h_iv h_msg
  apply Bytes.AttackerKnows.prove symEnc.attackerKnowledge
  simp only [symEnc.attackerKnowledge]
  grind

theorem attacker_knows_symDec
  (key iv ct msg: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    iv.AttackerKnows tr →
    ct.AttackerKnows tr →
    symDec key iv ct = some msg →
    msg.AttackerKnows tr
:= by
  intro h_key h_iv h_ct h_dec
  apply Bytes.AttackerKnows.prove symDec.attackerKnowledge
  simp only [symDec.attackerKnowledge]
  exact ⟨key, iv, ct, h_dec.symm, h_key, h_iv, h_ct⟩

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/-- Protocol-specific invariant on honestly encrypted messages. -/
class SymEncPred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop

class SymEncPredProof [BytesInvariants] [SymEncPred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ keyUsg key msg tr1 tr2,
      key.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      SymEncPred.pred keyUsg key msg tr1 →
      SymEncPred.pred keyUsg key msg tr2

grind_pattern SymEncPredProof.pred_later => tr1 ≤ tr2, SymEncPred.pred keyUsg key msg tr1

/-- Ciphertext `PartialInvariants`: ciphertexts have public label, and either `key` has `"SymKey"`
usage satisfying `SymEncPred` with `msg` flowing to `key`, or both `key` and `msg` are public. -/
def Enc.invariants [SymEncPred]: Bytes.PartialInvariants Enc.SubF where
  well_formed := fun {key, iv, msg} rec tr =>
      (rec key) tr ∧
      (rec iv) tr ∧
      (rec msg) tr

  usage := fun {key, iv, msg} rec tr =>
    Usage.nothing

  label := fun {key, iv, msg} rec tr =>
    Label.pub

  invariant := fun {key, iv, msg} rec tr =>
      (rec key) tr ∧
      (rec iv) tr ∧
      (rec msg) tr ∧
      (
        (
          ∃ keyUsg,
          key.HasUsage keyUsg tr ∧
          keyUsg.type = "SymKey" ∧
          SymEncPred.pred keyUsg key msg tr ∧
          (msg.label tr).canFlow (key.label tr) tr.erase
        ) ∨ (
          (key.label tr).canFlow Label.pub tr.erase ∧
          (msg.label tr).canFlow Label.pub tr.erase
        )
      )

theorem Enc.invariantsProofs [BytesInvariants] [SymEncPred] [SymEncPredProof]: Bytes.PartialInvariantsProofs Enc.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind

end Definition

#combine [SymEncPred] into
  BytesInvariants,
  BytesInvariantsProofs [SymEncPredProof]
from
  Enc,

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [SymEncPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
theorem symEnc.label
  (key iv msg: Bytes) (tr: ProofTrace)
  : (symEnc key iv msg).label tr = Label.pub
:= by
  simp [symEnc, Bytes.label.eq, Enc.invariants]

theorem symEnc.Invariant
  (key iv msg: Bytes) (keyUsg: Usage) (tr: ProofTrace)
  : (
      key.Invariant tr ∧
      iv.Invariant tr ∧
      msg.Invariant tr ∧
      (
        (
          key.HasUsage keyUsg tr ∧
          keyUsg.type = "SymKey" ∧
          SymEncPred.pred keyUsg key msg tr ∧
          (msg.label tr).canFlow (key.label tr) tr.erase
        ) ∨ (
          (key.label tr).canFlow Label.pub tr.erase ∧
          (msg.label tr).canFlow Label.pub tr.erase
        )
      )
    ) →
    (symEnc key iv msg).Invariant tr
:= by
  simp [symEnc, Bytes.Invariant.eq, Enc.invariants]
  grind

theorem symDec.Invariant
  (key iv ct msg: Bytes) (tr: ProofTrace)
  : ct.Invariant tr →
    symDec key iv ct = some msg →
    msg.Invariant tr ∧ (
      (
        ∃ keyUsg,
        key.HasUsage keyUsg tr ∧
        keyUsg.type = "SymKey" ∧
        SymEncPred.pred keyUsg key msg tr ∧
        (msg.label tr).canFlow (key.label tr) tr.erase
      ) ∨ (
        (msg.label tr).canFlow Label.pub tr.erase
      )
    )
:= by
  intro h_ct h_dec
  have h_eq := symDec_eq_some key iv ct msg h_dec
  subst h_eq
  simp [symEnc, Bytes.Invariant.eq, Enc.invariants] at h_ct
  grind

end Invariants

section HoareTriples

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes]
variable [SymEncPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

instance
  (key iv msg: Bytes)
  : HasGhostArgumentType (symEnc key iv msg) Usage
where
  dummy := ()

instance symEnc_hoareTriple
  (key iv msg: Bytes) (keyUsg: Usage)
  : HoareTriplePureGhost
    (symEnc key iv msg)
    (keyUsg)
    (fun tr =>
      key.Invariant tr ∧
      iv.Invariant tr ∧
      msg.Invariant tr ∧
      (
        (
          key.HasUsage keyUsg tr ∧
          keyUsg.type = "SymKey" ∧
          SymEncPred.pred keyUsg key msg tr ∧
          (msg.label tr).canFlow (key.label tr) tr.erase
        ) ∨ (
          (key.label tr).canFlow Label.pub tr.erase ∧
          (msg.label tr).canFlow Label.pub tr.erase
        )
      )
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
    )
where
  pf := by
    intro tr h
    exact ⟨symEnc.Invariant key iv msg keyUsg tr h, symEnc.label key iv msg tr⟩

instance symDec_hoareTriple
  [TraceInvariant]
  (key iv ct: Bytes)
  : HoareTriple
    (symDec key iv ct)
    (fun tr =>
      ct.Invariant tr
    )
    (fun msg tr =>
      symDec key iv ct = some msg ∧
      msg.Invariant tr ∧ (
        (
          ∃ keyUsg,
          key.HasUsage keyUsg tr ∧
          keyUsg.type = "SymKey" ∧
          SymEncPred.pred keyUsg key msg tr ∧
          (msg.label tr).canFlow (key.label tr) tr.erase
        ) ∨ (
          (msg.label tr).canFlow Label.pub tr.erase
        )
      )
    )
where
  pf := by
    simp only [hoareTriple, wp, OptionT.run]
    intro tr h_pre _
    split
    · trivial
    rename_i msg heq
    exact ⟨heq, symDec.Invariant key iv ct msg tr h_pre heq⟩

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [SymEncPred]
variable [BytesInvariants.Has invariants]

instance: SubAttackerKnowledgeTheorem symEnc.attackerKnowledge where
  pf := by
    simp only [symEnc.attackerKnowledge]
    intro out tr h_tr ⟨key, iv, msg, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp only [Bytes.Publishable] at *
    refine ⟨symEnc.Invariant key iv msg Usage.nothing tr ?_, ?_⟩
    · grind
    · simp [canFlowRefl]

instance: SubAttackerKnowledgeTheorem symDec.attackerKnowledge where
  pf := by
    simp only [symDec.attackerKnowledge]
    intro out tr h_tr ⟨key, iv, ct, ⟨ h_out, h_inputs ⟩⟩
    simp only [Bytes.Publishable] at *
    have := symDec.Invariant key iv ct out tr h_inputs.2.2.1 h_out.symm
    grind [canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [SymEncPred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  symEnc,
  symDec,

end AttackerKnowledgeTheorem

end DY.SymEnc
