/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr

/-!
# SPQR State Lemmas and Four-Case Handshake Compromise Decomposition

Proves `spqrSend` and `spqrRecv` evaluation lemmas on initial and post-receive SPQR states,
establishes `AttackerKnows` projection lemmas for `spqrInit` and `RecvState`, and defines the
four-case `Thm7Case` decomposition of `AliceHandshakeWasCompromised` used by the explanation-tightness
tests.
-/

@[expose] public section

namespace Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas

section

open DY DY.Spqr

section Literals

variable [BytesFunctor] [BytesFunctor.Has Literal.SubF]

theorem spqrEmptyMsg_of_not_literal (msg: Bytes) (hmsg: Literal.bytesToLiteral msg = none) :
    spqrEmptyMsg msg = false := by
  simp [spqrEmptyMsg, hmsg]

end Literals

section Functions

variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesFunctor.Has Literal.SubF]

theorem spqrSend_key_init (k p coins: Bytes) :
    (spqrSend (spqrInit k p) coins).2.1 = spqrChainKey k p (encodeSpqrIndexTerm 1) := by
  simp [spqrSend, spqrInit, BytesView.view_pack]

theorem spqrRecv_init_zero (k msg: Bytes) (d: Direction)
    (hmsg: Literal.bytesToLiteral msg = none) :
    spqrRecv (spqrInit k (encodeSpqrDirectionParams d)) msg 0 =
      some (({st := spqrInit k (encodeSpqrDirectionParams d), msg}: RecvState.SubF Bytes).pack, zeroKey) := by
  simp [spqrRecv, spqrEmptyMsg_of_not_literal msg hmsg, spqrInit, BytesView.view_pack]

theorem spqrRecv_init_pos (k msg: Bytes) (d: Direction) (idx: UInt32) (hidx: idx ≠ 0)
    (hmsg: Literal.bytesToLiteral msg = none) :
    spqrRecv (spqrInit k (encodeSpqrDirectionParams d)) msg idx =
      some (({st := spqrInit k (encodeSpqrDirectionParams d), msg}: RecvState.SubF Bytes).pack,
        spqrChainKey k (encodeSpqrDirectionParams d.flip) (encodeSpqrIndexTerm idx)) := by
  simp [spqrRecv, spqrEmptyMsg_of_not_literal msg hmsg, spqrInit, BytesView.view_pack, hidx]

/-- On fresh states with opposite directions, `spqrRecv` at index `1` on any non-literal message
yields the sender's `spqrSend` key. -/
theorem spqrRecv_init_agree (k coins msg: Bytes) (d: Direction)
    (hmsg: Literal.bytesToLiteral msg = none) :
    spqrRecv (spqrInit k (encodeSpqrDirectionParams d)) msg 1 =
      some (({st := spqrInit k (encodeSpqrDirectionParams d), msg}: RecvState.SubF Bytes).pack,
        (spqrSend (spqrInit k (encodeSpqrDirectionParams d.flip)) coins).2.1) := by
  rw [spqrSend_key_init]
  exact spqrRecv_init_pos k msg d 1 (by decide) hmsg

theorem spqrRecv_not_init (st msg: Bytes) (idx: UInt32) (hst: st.view? InitState.SubF = none)
    (hmsg: Literal.bytesToLiteral msg = none) :
    spqrRecv st msg idx =
      some (({st, msg}: RecvState.SubF Bytes).pack, ({st, msg}: RecvKey.SubF Bytes).pack) := by
  simp [spqrRecv, spqrEmptyMsg_of_not_literal msg hmsg, hst]

end Functions

section AttackerKnowledgeBuild

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge]

theorem attacker_knows_spqrInit_args [AttackerKnowledge.Has spqrStateArg.attackerKnowledge]
    (authKey params: Bytes) (tr: ExecTrace) :
    (spqrInit authKey params).AttackerKnows tr →
    authKey.AttackerKnows tr ∧ params.AttackerKnows tr := by
  intro h
  refine ⟨?_, ?_⟩ <;> apply Bytes.AttackerKnows.prove spqrStateArg.attackerKnowledge
  · exact Or.inl ⟨{authKey, params}, h, Or.inl rfl⟩
  · exact Or.inl ⟨{authKey, params}, h, Or.inr rfl⟩

theorem attacker_knows_spqrRecv_args [AttackerKnowledge.Has spqrStateArg.attackerKnowledge]
    (st msg: Bytes) (tr: ExecTrace) :
    (({st, msg}: RecvState.SubF Bytes).pack).AttackerKnows tr →
    st.AttackerKnows tr ∧ msg.AttackerKnows tr := by
  intro h
  refine ⟨?_, ?_⟩ <;> apply Bytes.AttackerKnows.prove spqrStateArg.attackerKnowledge
  · exact Or.inr (Or.inr ⟨{st, msg}, h, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨{st, msg}, h, Or.inr rfl⟩)

end AttackerKnowledgeBuild

end

section

open DY DY.Libsignal DY.Libsignal.PQXDH

open scoped DY.Libsignal.Composed

section

attribute [-instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

variable [Composed.HasExecTrace]

/-- Four-case indexing (`Fin 4`) of the disjuncts of `AliceHandshakeWasCompromised` for
initiator-side PQXDH tightness checks. -/
def Thm7Case (b: Participant) (ikB spk pqpk: Bytes) (i: Nat) (tr: ExecTrace): Fin 4 → Prop
  | 0 => LoggedBefore (PQXDHEvent.CompromisedIK b ikB) i tr
  | 1 => tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      (tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨ tr.EventLogged PQXDHEvent.BrokenKEM)
  | 2 => LoggedBefore PQXDHEvent.BrokenDH i tr
  | 3 => tr.EventLogged PQXDHEvent.BrokenDH ∧
      (tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨ tr.EventLogged PQXDHEvent.BrokenKEM)

end

end

end Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
