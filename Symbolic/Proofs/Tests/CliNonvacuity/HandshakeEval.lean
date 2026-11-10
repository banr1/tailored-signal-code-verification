/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import Comparse.Basic
import Comparse.Formats.Basic
import Comparse.Formats.Derived
import DY.Comparse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.Comparse.Basic
import Symbolic.DYBridge.DY.Comparse
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace

/-!
# Shared Handshake Setup, Pre-Key Field, and Decryption Helpers

Provides shared computable setup and pre-key field helpers (`mkRecordsComp`, `p0Fields`,
`honestPreKeyRep`, `honestSalts_msPrefix2_*`) and symbolic decryption non-match lemmas
(`zeroKey_ne_spqrSendKey`, `symDec_ne_salt`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval

open scoped DY.Libsignal.Composed

open DY.PQKem (kemPk)
open DY.Libsignal.PQXDH (errToOption)
open DY.Libsignal.TripleRatchet (TRState trMsgKeys kdfCk)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Step PreKeyFields PreKeyRep parsePreKeyWire preKeySpqrIndex
   setupSecret setupRandoms newRandoms newIndices randTerm honestSaltsOf honestKeysOf)
open Symbolic.Swarm.CREF (b1_setupPublic_6 b1_setupTrace_eq)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (pqskB bh1 bhOpk o1 stA0 coins0 key0 m0 t4 t4_length t5 t6 t5_length
   oOpk stA0Opk coins0Opk key0Opk m0Opk t4Opk t4Opk_length t5Opk t6Opk t5Opk_length)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (NetE RndE encTr rnd encSig encMsg kemDecap_kemEncap)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (freshBytes myKyberPubBytes myKyberSecField mkRecords)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (decEqBytesFast)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel (wire0)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (m0Of m1Of msPrefix2 setupTrace_false_eq setupTrace_true_eq
   m0_next_false m0_next_true m1_next_false m1_next_true)

attribute [local instance]
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

/-! ## Computable Setup Wrapper and Pre-Key Fields -/

noncomputable def mkRecordsComp (withOpk : Bool) : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := withOpk, regIdA := 10#32, regIdB := 20#32,
    spkId := 1#32, kpkId := 2#32, opkId := 3#32, kyberSecB := myKyberSecField,
    fresh := freshBytes, opaqueBytes := fun t =>
      match decEqBytesFast t (kemPk (randTerm 16 64)) with
      | isTrue _ => myKyberPubBytes
      | isFalse _ => List.replicate 64 0#8 }

theorem mkRecords_eq_comp (withOpk : Bool) : mkRecords withOpk = mkRecordsComp withOpk := by
  unfold mkRecords mkRecordsComp; dsimp only; congr 1; funext t
  rw [b1_setupPublic_6 _ (by show "alice" ≠ "bob"; decide)]
  cases decEqBytesFast t (kemPk (randTerm 16 64)) with
  | isTrue h => simp [h]
  | isFalse h => simp [h]

def p0Fields (withOpk : Bool) : PreKeyFields :=
  (parsePreKeyWire (wire0 withOpk)).get (by cases withOpk <;> decide +kernel)

theorem parsePreKeyWire_wire0 (withOpk : Bool) :
    parsePreKeyWire (wire0 withOpk) = some (p0Fields withOpk) :=
  (Option.some_get _).symm

def honestPreKeyRep (withOpk : Bool) : PreKeyRep :=
  if withOpk then
    { ek := oOpk.ek, ct := oOpk.ct, msg := encMsg stA0Opk coins0Opk key0Opk m0Opk }
  else
    { ek := o1.ek, ct := o1.ct, msg := encMsg stA0 coins0 key0 m0 }

theorem p0_pkId_false : (p0Fields false).preKeyId = none := by decide +kernel
theorem p0_pkId_true : (p0Fields true).preKeyId = some 3#32 := by decide +kernel
theorem p0_spqrIdx_false : preKeySpqrIndex (p0Fields false) = 1 := by decide +kernel
theorem p0_spqrIdx_true : preKeySpqrIndex (p0Fields true) = 1 := by decide +kernel

theorem honestSalts_msPrefix2_false :
    honestSaltsOf (mkRecords false) (msPrefix2 false) = [DY.Spqr.zeroKey, key0] := by
  unfold honestSaltsOf msPrefix2
  simp only [m0Of, m1Of, Bool.false_eq_true, ↓reduceIte, honestKeysOf,
    Step.publishedSpqrKey?, DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx,
    DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx]
  rw [setupTrace_false_eq,
    show (Step.aliceStart "alice" "bob" 4 6 bh1).next t4 = t5 from m0_next_false,
    show (Step.messageEncrypt "alice" 30 32 33).next t5 = t6 from m1_next_false,
    t5_length]
  have hat33 : (t6.at? 33 : Option DY.Network.ExecEntryT) = some (NetE key0) := by
    unfold t6 encTr
    dsimp only
    rw [t5_length]
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    have hlen : ((t5.append (RndE 32)).append (RndE 32)).length = 33 := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t5_length]
    exact hlen ▸ DY.Trace.at?_append _ _
  simp only [Nat.reduceAdd, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat33]
  rfl

theorem honestSalts_msPrefix2_true :
    honestSaltsOf (mkRecords true) (msPrefix2 true) = [DY.Spqr.zeroKey, key0Opk] := by
  unfold honestSaltsOf msPrefix2
  simp only [m0Of, m1Of, ↓reduceIte, honestKeysOf,
    Step.publishedSpqrKey?, DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx,
    DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx]
  rw [setupTrace_true_eq,
    show (Step.aliceStart "alice" "bob" 4 6 bhOpk).next t4Opk = t5Opk from m0_next_true,
    show (Step.messageEncrypt "alice" 34 32 37).next t5Opk = t6Opk from m1_next_true,
    t5Opk_length]
  have hat37 : (t6Opk.at? 37 : Option DY.Network.ExecEntryT) = some (NetE key0Opk) := by
    unfold t6Opk encTr
    dsimp only
    rw [t5Opk_length]
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    have hlen : ((t5Opk.append (RndE 32)).append (RndE 32)).length = 37 := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t5Opk_length]
    exact hlen ▸ DY.Trace.at?_append _ _
  simp only [Nat.reduceAdd, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat37]
  rfl

/-! ## Symbolic Decryption Helpers -/

section UnsealHelpers
unseal DY.Bytes

theorem zeroKey_ne_spqrSendKey (st coins : DY.Bytes) :
    DY.Spqr.zeroKey ≠ (DY.Spqr.spqrSend st coins).2.1 := by
  intro h
  have h1 := congrArg (fun b => (b.view? DY.Literal.Literal.SubF).isSome) h
  have hz : (DY.Spqr.zeroKey.view? DY.Literal.Literal.SubF).isSome = true := by
    simp only [DY.Spqr.zeroKey, DY.Literal.literalToBytes, DY.Literal.CanMkLiteral.literalToBytes,
      DY.BytesView.view_pack]
    rfl
  rw [hz] at h1
  dsimp only [DY.Spqr.spqrSend] at h1
  rcases hst : st.view? DY.Spqr.InitState.SubF with _ | ⟨⟨authKey, params⟩⟩
  · simp only [hst] at h1
    have hn := Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ st := st, coins := coins } : DY.Spqr.SendKey.SubF DY.Bytes)
    rw [hn] at h1
    exact Bool.noConfusion h1
  · simp only [hst, DY.Spqr.spqrChainKey] at h1
    have hn := Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ authKey := authKey, params := params, idx := DY.Spqr.encodeSpqrIndexTerm 1 } :
        DY.Spqr.ChainKey.SubF DY.Bytes)
    rw [hn] at h1
    exact Bool.noConfusion h1

theorem symDec_ne_salt {stS : TRState}
    {coins salt pq m : DY.Bytes} (hne : salt ≠ pq) :
    DY.SymEnc.symDec (trMsgKeys salt (kdfCk stS.cks).2).cipherKey
      (trMsgKeys salt (kdfCk stS.cks).2).iv
      (encSig stS coins pq m).ciphertext = none := by
  dsimp only [encSig, DY.SymEnc.symDec, DY.SymEnc.symEnc, DY.SymEnc.instCanSymEncBytes]
  rw [DY.BytesView.view_pack]
  simp only [ite_eq_right_iff]
  rintro ⟨hck, _⟩
  apply False.elim (hne ?_)
  have h1 := congrArg (fun b : DY.Bytes => b.view? DY.KdfExtract.KdfExtract.SubF) hck
  simp only [trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1, DY.Libsignal.TripleRatchet.hmac,
    DY.KdfExtract.kdfExtract, DY.BytesView.view_pack, Option.some.injEq,
    DY.KdfExtract.KdfExtract.SubF.mk.injEq] at h1
  have h2 := congrArg (fun b : DY.Bytes => b.view? DY.KdfExtract.KdfExtract.SubF) h1.1
  simp only [DY.BytesView.view_pack, Option.some.injEq,
    DY.KdfExtract.KdfExtract.SubF.mk.injEq] at h2
  exact h2.1

end UnsealHelpers

end Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
