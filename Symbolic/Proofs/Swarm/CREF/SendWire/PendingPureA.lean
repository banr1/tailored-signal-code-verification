/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
public import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj
import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Pending-PreKey `SendWire` Model-to-Wire Bridge

Defines `PendingRecordCanon`, reduces `PureRecPending` under `PureCRecRelH` to
`PureAliceInitPending`, and proves `sendPendingGhost` transfer and inner-message `gamma`
correspondence on pending-prekey records.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.SndPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.SendWire
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt TraceEntriesLt traceEntriesLt_at?_net)
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet (TRState trMsgKeys kdfCk)
open DY.Libsignal.TripleRatchet.Refinement (trWireBytes)
open DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction encodeField)
open DY.TrWire (canonicalVariation)
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open Proofs.libsignal.SR (interpW)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

def PendingRecordCanon (rec : HwBytes) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec sess ∧
    TR.Pure.slots_RecordInScopeP ⟨some sess⟩ ∧
    TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩ ∧
    sess.state.remoteIdentity.isSome = true ∧
    rec.length < 2 ^ 62 ∧
    rec.length < 2 ^ 32 - 2 ^ 20 ∧
    SpqrOooBounded sess.state.pqRatchetState

theorem ooo_of_pendingRecordCanon {recBytes : HwBytes}
    {gs : Session (List (BitVec 8))}
    (hcanon : PendingRecordCanon recBytes)
    (hrc : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes gs) :
    SpqrOooBounded gs.state.pqRatchetState ∧ gs.state.pqRatchetState.length < 2 ^ 32 := by
  obtain ⟨sess₀, hrc₀, -, -, -, h62, -, hooo₀⟩ := hcanon
  have hpq : sess₀.state.pqRatchetState = gs.state.pqRatchetState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₀.1 hrc.1 h62
  obtain ⟨-, -, -, -, -, -, -, hpqlen, -⟩ := hrc
  exact ⟨hpq ▸ hooo₀, hpqlen⟩

theorem ooo_of_pureTRRecordCanon_sess {r : ProtocolSetup} {p : Participant} {recBytes : HwBytes}
    {gs : Session (List (BitVec 8))}
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hrc : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes gs) :
    SpqrOooBounded gs.state.pqRatchetState ∧ gs.state.pqRatchetState.length < 2 ^ 32 := by
  obtain ⟨sess₀, hrc₀, -, -, -, h62, -, -, hooo₀⟩ := hcanon
  have hpq : sess₀.state.pqRatchetState = gs.state.pqRatchetState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₀.1 hrc.1 h62
  obtain ⟨-, -, -, -, -, -, -, hpqlen, -⟩ := hrc
  exact ⟨hpq ▸ hooo₀, hpqlen⟩

theorem pqStateOf_recordBytes_pure (rr : RecordRec) :
    pqStateOf (recordBytes rr) = rr.current.pqRatchetState := by
  have hex : ∃ r' : RecordRec, recordBytes rr = recordBytes r' := ⟨rr, rfl⟩
  simp only [pqStateOf, hex, ↓reduceDIte]
  have hinj := Symbolic.Swarm.CREF.TR.recordBytes_injective (Classical.choose_spec hex).symm
  exact congrArg (fun x => x.current.pqRatchetState) hinj

theorem pqStateOf_eq_gamma_of_stateRel_pure {interpretation : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {st : TRState} {recR : RecordRec} {b : HwBytes}
    (hb : b = recordBytes recR) (hrel : TR.StateRel interpretation S g st recR) :
    pqStateOf b = gamma interpretation S g st.spqr := by
  subst hb
  rw [pqStateOf_recordBytes_pure]
  exact congrArg SessionRec.pqRatchetState hrel.2

/-- Under `PureRecPending rec` and `PureCRecRelH`, the caller is Alice holding a
`PureAliceInitPending` record. -/
theorem recPending_imp_alice_pending_of_recRel
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (p : Participant) (rec : HwBytes) (g : Ghost) (ms : List Move)
    (hreclen : rec.length < 2 ^ 32 - 2 ^ 20)
    (hpend_rec : PureRecPending rec)
    (hrec_rel : PureCRecRelH interpretation r S g ms p rec) :
    p = r.alice ∧ PureAliceInitPending interpretation r S g ms rec := by
  rcases hpend_rec with ⟨sess_p, hrc_p, hppk_p⟩
  have hss : SingleSession rec :=
    ⟨TR.SendRetCoinsCliPure.sessionToRecordRecPending sess_p,
      hrc_p.1.trans (TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q hrc_p).symm,
      rfl⟩
  rcases pureCRecRelH_single hrec_rel hss with htr | hpend
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, _, hcanon_fn, _, _⟩ := htr p rec (by simp)
    have hcanon : TR.Pure.TRRecordCanon r p rec := hcanon_fn hreclen
    have hnone : sess_p.pendingPreKey = none :=
      TR.SendRetCoinsCliPure.pendingPreKey_eq_none_of_canon hcanon hrc_p
    rw [hnone] at hppk_p
    cases hppk_p
  · exact hpend

theorem pqStateOf_of_canonical_Q_pend {Q : HwBytes → Prop} {rec : HwBytes}
    {sess : Session (List (BitVec 8))}
    (hrc : TR.Pure.slots_RecordCanonical_Q Q rec sess) :
    pqStateOf rec = sess.state.pqRatchetState := by
  have hrb : rec = recordBytes (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess) :=
    hrc.1.trans (TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q hrc).symm
  rw [hrb, pqStateOf_recordBytes_pure]
  rfl

theorem pendingRecordCanon_of_aliceInitPending
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (rec : HwBytes)
    (hpend : PureAliceInitPending interpretation r S g ms rec)
    (hreclen : rec.length < 2 ^ 32 - 2 ^ 20)
    (hooo : SpqrOooBounded (pqStateOf rec)) :
    PendingRecordCanon rec := by
  obtain ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    hrc, hscope1, hscope2, _hget, _hcur, _hinit, _hpeer, _hek, _hct,
    _hreg, _hver, _hpn, _hlid, hrem, _hrem_ser, _hsc, _hrk, _hck, _hidx,
    _hppk, _hts, _hbk, _hkpk, _hct_ser, _hpq, _hrecR⟩ := hpend
  have hpq_eq : pqStateOf rec = sess.state.pqRatchetState :=
    pqStateOf_of_canonical_Q_pend hrc
  rw [hpq_eq] at hooo
  refine ⟨sess, hrc, hscope1, hscope2, ?_, by omega, hreclen, hooo⟩
  rw [hrem]
  rfl

theorem stampsLt_of_getMessageSentAt {i : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {tr : ExecTrace}
    (htr : TraceEntriesLt i S g ts tr) {j : Nat} {x : DY.Bytes}
    (h : tr.getMessageSentAt j = some x) : StampsLt i S g ts x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h
  rcases hat : (tr.at? j : Option DY.Network.ExecEntryT) with _ | ⟨m⟩
  · rw [hat] at h; cases h
  · rw [hat] at h; injection h with h; subst h
    exact traceEntriesLt_at?_net htr hat

section PurePendingWire

theorem encodeBytesField6_pqHarnessAddrBytes :
    CryptoVerification.LibsignalProtoCodec.encodeBytesField 6 (some pqHarnessAddrBytes) =
      (if pqHarnessAddrBytes = [] then [] else encodeField 6 0 0 (.bytes pqHarnessAddrBytes)) := by
  decide +kernel

theorem serializeContent_some_addr_eq (rk : PublicKey)
    (counter previousCounter : BitVec 32) (ctext pqMsgBytes addr : List (BitVec 8)) :
    serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext pqMsgBytes (some addr) =
      serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext pqMsgBytes none ++
        CryptoVerification.LibsignalProtoCodec.encodeBytesField 6 (some addr) := by
  cases pqMsgBytes <;>
    simp [serializeContent, protoSignalCodec, CryptoVerification.LibsignalProtoCodec.encode,
      CryptoVerification.LibsignalProtoCodec.encodeBytesField, List.append_assoc]

theorem serializeContent_pending_eq_trWireBytes (rk : PublicKey)
    (counter previousCounter : BitVec 32) (ctext pqMsgBytes : List (BitVec 8))
    (hct : ctext.length < 2 ^ 64) (hpq : pqMsgBytes.length < 2 ^ 64) :
    serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext pqMsgBytes
      (some pqHarnessAddrBytes) =
      trWireBytes pqHarnessAddrBytes canonicalVariation
        ⟨4, rk.bytes.toList, counter.toNat, previousCounter.toNat, ctext⟩ pqMsgBytes := by
  rw [serializeContent_some_addr_eq,
      TR.SendRetCoinsCliPure.serializeContent_tr_eq_encodeWith rk counter previousCounter ctext pqMsgBytes hct hpq,
      encodeBytesField6_pqHarnessAddrBytes,
      DY.Libsignal.TripleRatchet.Refinement.trWireBytes_canonical]

theorem psm_field_lengths_lt_of_wire_lt
    (regId : BitVec 32) (preKeyId : Option (BitVec 32)) (spkId kpkId : BitVec 32)
    (kpkCt : HwBytes) (baseKey : PublicKey) (localId : IdentityKey) (innerMsg : SignalMessage)
    (hw_lt : (wirePrekeyTag :: (PreKeySignalMessage.new 4#8 regId preKeyId spkId
      (some ⟨kpkId, kpkCt⟩) baseKey localId innerMsg).serialized).length < 2 ^ 64) :
    kpkCt.length < 2 ^ 64 ∧ innerMsg.serialized.length < 2 ^ 64 := by
  dsimp only [PreKeySignalMessage.new, Option.map_some,
    CryptoGames.LibsignalSessionApi.ProtoPreKeySignalMessage.encode] at hw_lt
  have h4 : innerMsg.serialized.length ≤
      (CryptoGames.LibsignalSessionApi.Prost.bytesField 4 (some innerMsg.serialized)).length := by
    simp [CryptoGames.LibsignalSessionApi.Prost.bytesField]; omega
  have h8 : kpkCt.length ≤
      (CryptoGames.LibsignalSessionApi.Prost.bytesField 8 (some kpkCt)).length := by
    simp [CryptoGames.LibsignalSessionApi.Prost.bytesField]; omega
  simp only [List.length_cons, List.length_append] at hw_lt; omega

theorem ctext_and_pq_length_lt_of_inner_lt (F : ShaCompress) (macKey : BitVec 256)
    (rk : PublicKey) (counter previousCounter : BitVec 32) (ctext pqMsgBytes : List (BitVec 8))
    (localId remote : IdentityKey)
    (hmsg : (SignalMessage.new F protoSignalCodec 4#8 macKey (some pqHarnessAddrBytes)
      rk counter previousCounter ctext localId remote pqMsgBytes).serialized.length < 2 ^ 64) :
    ctext.length < 2 ^ 64 ∧ pqMsgBytes.length < 2 ^ 64 := by
  dsimp only [SignalMessage.new] at hmsg
  rw [List.length_append, serializeContent_some_addr_eq, List.length_append,
      TR.SendRetCoinsCliPure.serializeContent_eq_append_bytesField5,
      List.length_append] at hmsg
  have h1 : ctext.length ≤
      (serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext [] none).length := by
    dsimp [serializeContent, protoSignalCodec, CryptoVerification.LibsignalProtoCodec.encode,
      CryptoVerification.LibsignalProtoCodec.encodeBytesField]
    simp only [List.length_append]; omega
  have h2 : pqMsgBytes.length ≤ (CryptoVerification.E2E.Record.bytesField 5 pqMsgBytes).length := by
    unfold CryptoVerification.E2E.Record.bytesField CryptoVerification.E2E.Record.lenField
    split_ifs with h <;> simp [h]; omega
  omega

unseal DY.Bytes in
private instance subFunction_gTrWire0_pend (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, trWireFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

theorem gamma_trHonestWireMsg_addr
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.trHonestWireMsg rk c pc ct pq) =
      trWireBytes
        (g.addr (DY.Libsignal.TripleRatchet.trHonestWireMsg rk c pc ct pq))
        canonicalVariation
        ⟨4, gamma interpretation S g rk, c.toNat, pc.toNat, gamma interpretation S g ct⟩
        (gamma interpretation S g pq) := by
  unfold DY.Libsignal.TripleRatchet.trHonestWireMsg gamma gamma'
  change (((⟨4, rk, c, pc, ct, pq, DY.TrWire.canonicalVariation⟩ :
    DY.TrWire.TrWireMsg.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll interpretation S g)]
  rfl

theorem sendMatches_of_preKeyWire_comp (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (preKeyId : Option (BitVec 32)) (spkId kpkId : BitVec 32)
    (ek ct msg : DY.Bytes) :
    SendMatches interpretation r S g (some (preKeyId, spkId, kpkId))
      (preKeyWire preKeyId spkId kpkId r.regIdA
        (ecKey (pubBytes interpretation (secretBytes r 0)))
        (gamma interpretation S g ek) (gamma interpretation S g ct) (gamma interpretation S g msg))
      [ek, ct, msg] :=
  ⟨preKeyId, spkId, kpkId, rfl, rfl⟩

unseal DY.Bytes in
private instance subFunction_gRandom_pend (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

theorem gamma_sendPendingGhost_coins_all_pend (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    gamma interpretation S (sendPendingGhost g ts pt coins)
      (randTerm (ts + 1) coins.length) = coins := by
  by_cases h : coins.length = 0
  · have hnil := List.eq_nil_of_length_eq_zero h
    subst hnil
    unfold gamma gamma' randTerm
    rw [DY.Bytes.rec_eq (concretizeRandom (sendPendingGhost g ts pt []))
      (concretizeAll interpretation S (sendPendingGhost g ts pt []))]
    rfl
  · exact gamma_sendPendingGhost_coins interpretation S g ts pt coins h

end PurePendingWire

section PendingSendWireBridge

unseal DY.Bytes in
private instance subFunction_gConcat0_pend (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

private theorem gamma_concat_pend (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) :
    gamma interpretation S g (DY.Concat.concat a b) =
      gamma interpretation S g a ++ gamma interpretation S g b := by
  unfold gamma gamma'
  show ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interpretation S g)]
  rfl

theorem innerMsg_serialized_eq_gamma_encMsg
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (hEq : ExternCryptoLawsHold interpretation)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) (st : TRState)
    (sc : SenderChain) (localId remote : IdentityKey) (previousCounter : BitVec 32)
    (newPqState pqMsgBytes : HwBytes) (salt?)
    (hinit : TR.SendRetCoinsCliPure.SpqrInitA2BKdf st.spqr)
    (hsend : (spqrModelOf interpretation).send
      (gamma interpretation (compSemOf interpretation r₀)
        (sendPendingGhost g ts pt coins) st.spqr)
      coins = some (newPqState, salt?, pqMsgBytes))
    (hidx : sc.chainKey.index = st.ns.toBitVec)
    (hpctr : previousCounter = st.pn.toBitVec)
    (hck : keyToBytes32 sc.chainKey.key =
      gamma interpretation (compSemOf interpretation r₀)
        (sendPendingGhost g ts pt coins) st.cks)
    (hrk : sc.ratchetKey.publicKey.bytes.toList =
      gamma interpretation (compSemOf interpretation r₀)
        (sendPendingGhost g ts pt coins) (DY.DiffieHellman.dhPk st.dhs))
    (hloc : localId.serialize =
      gamma interpretation (compSemOf interpretation r₀)
        (sendPendingGhost g ts pt coins) st.myIk)
    (hrem : remote.serialize =
      gamma interpretation (compSemOf interpretation r₀)
        (sendPendingGhost g ts pt coins) st.peerIk)
    (hinner_lt :
      let F := sha256CompressFunction interpretation
      let mk := (sc.chainKey.messageKeys F).generateKeys F salt?
      let ctext := (interpW interpretation).enc mk.cipherKey mk.iv pt
      (SignalMessage.new F protoSignalCodec 4#8 mk.macKey (some pqHarnessAddrBytes)
        sc.ratchetKey.publicKey sc.chainKey.index previousCounter ctext localId remote pqMsgBytes).serialized.length < 2 ^ 64) :
    let S := compSemOf interpretation r₀
    let g' := sendPendingGhost g ts pt coins
    let F := sha256CompressFunction interpretation
    let mk := (sc.chainKey.messageKeys F).generateKeys F salt?
    let ctext := (interpW interpretation).enc mk.cipherKey mk.iv pt
    let coinsTerm := randTerm (ts + 1) coins.length
    gamma interpretation S g' (DY.Spqr.spqrSend st.spqr coinsTerm).1 = newPqState ∧
    gamma interpretation S g' (kdfCk st.cks).1 =
      CryptoGames.Ratchet.chainHmac F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed ∧
    (SignalMessage.new F protoSignalCodec 4#8 mk.macKey (some pqHarnessAddrBytes)
      sc.ratchetKey.publicKey sc.chainKey.index previousCounter ctext localId remote pqMsgBytes).serialized =
      gamma interpretation S g' (encMsg st coins.length ts) := by
  dsimp only
  set S := compSemOf interpretation r₀
  set g' := sendPendingGhost g ts pt coins
  set F := sha256CompressFunction interpretation
  set coinsTerm := randTerm (ts + 1) coins.length
  have hcoins_gam : gamma interpretation S g' coinsTerm = coins :=
    gamma_sendPendingGhost_coins_all_pend interpretation S g ts pt coins
  have hsend_gam : (spqrModelOf interpretation).send (gamma interpretation S g' st.spqr)
      (gamma interpretation S g' coinsTerm) = some (newPqState, salt?, pqMsgBytes) := by
    rw [hcoins_gam]; exact hsend
  obtain ⟨hspqr1, hspqr2, hspqr3⟩ := TR.SendRetCoinsCliPure.gamma_spqrSend_bridge interpretation hEq r₀ g'
    st.spqr coinsTerm (TR.SendRetCoinsCliPure.spqrInitA2B32_of_kdf interpretation S g' hinit) hsend_gam
  have hstep : gamma interpretation S g' (kdfCk st.cks).1 =
      CryptoGames.Ratchet.chainHmac F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed := by
    rw [TR.SendRetCoinsCliPure.gamma_kdfCk_fst_tr, ← hck]; rfl
  refine ⟨hspqr1, hstep, ?_⟩
  set seed := (kdfCk st.cks).2
  set pqSalt := (DY.Spqr.spqrSend st.spqr coinsTerm).2.1
  set pqTerm := (DY.Spqr.spqrSend st.spqr coinsTerm).2.2
  set keys := trMsgKeys pqSalt seed
  set mk := (sc.chainKey.messageKeys F).generateKeys F salt?
  set ctext := (interpW interpretation).enc mk.cipherKey mk.iv pt
  obtain ⟨hct_lt, hpq_lt⟩ := ctext_and_pq_length_lt_of_inner_lt F mk.macKey
    sc.ratchetKey.publicKey sc.chainKey.index previousCounter ctext pqMsgBytes localId remote hinner_lt
  have hseed : (sc.chainKey.messageKeys F).seed = gamma interpretation S g' seed := by
    rw [TR.SendRetCoinsCliPure.gamma_kdfCk_snd_tr, ← hck]; rfl
  have hmkg : sc.chainKey.messageKeys F = ⟨gamma interpretation S g' seed, sc.chainKey.index⟩ := by
    cases hmk : sc.chainKey.messageKeys F
    have hs : (sc.chainKey.messageKeys F).seed = gamma interpretation S g' seed := hseed
    have hc : (sc.chainKey.messageKeys F).counter = sc.chainKey.index := rfl
    rw [hmk] at hs hc; subst hs hc; rfl
  have hgen := TR.SendRetCoinsCliPure.gamma_trMsgKeys_eq_generateKeys interpretation S g' pqSalt seed sc.chainKey.index salt? hspqr2
  dsimp only at hgen
  have hmk_c : keyToBytes32 mk.cipherKey = gamma interpretation S g' keys.cipherKey := by
    dsimp only [mk]; rw [hmkg]; exact hgen.1
  have hmk_m : keyToBytes32 mk.macKey = gamma interpretation S g' keys.macKey := by
    dsimp only [mk]; rw [hmkg]; exact hgen.2.1
  have hmk_iv : CryptoGames.CBC.blockToBytesLE mk.iv = (gamma interpretation S g' keys.iv).take 16 := by
    dsimp only [mk]; rw [hmkg]; exact hgen.2.2.1
  have hpt_gam : pt = gamma interpretation S g' (randTerm ts 32) :=
    (gamma_sendPendingGhost_pt interpretation S g ts pt coins).symm
  have hct_gam : ctext = gamma interpretation S g' (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ts 32)) := by
    dsimp only [ctext, interpW]; rw [hpt_gam, hmk_c, hmk_iv, TR.SendRetCoinsCliPure.gamma_symEnc_tr]
  have hwire_def : encWire st coins.length ts =
      DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn
        (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ts 32)) pqTerm := rfl
  have haddr_pq : g'.addr (DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs)
      st.ns st.pn (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ts 32)) pqTerm) = pqHarnessAddrBytes := by
    rw [← hwire_def]; exact sendPendingGhost_addr_encWire g st coins.length ts pt coins
  have hwire_gam : serializeContent protoSignalCodec 4#8 sc.ratchetKey.publicKey sc.chainKey.index
      previousCounter ctext pqMsgBytes (some pqHarnessAddrBytes) =
      gamma interpretation S g' (encWire st coins.length ts) := by
    rw [serializeContent_pending_eq_trWireBytes _ _ _ _ _ hct_lt hpq_lt, hwire_def,
        gamma_trHonestWireMsg_addr, haddr_pq, hrk, hidx, hpctr, hct_gam, hspqr3]
    rfl
  have hmac_gam := TR.SendRetCoinsCliPure.gamma_computeMac_tr interpretation S g' keys.macKey st.myIk st.peerIk
    (encWire st coins.length ts) localId remote mk.macKey hmk_m hloc hrem _ hwire_gam
  dsimp only [SignalMessage.new, encMsg, encMac]
  rw [gamma_concat_pend interpretation S g' _ _, ← hwire_gam, ← hmac_gam]

end PendingSendWireBridge

end Symbolic.Swarm.CREF.CliPure.SndPure
