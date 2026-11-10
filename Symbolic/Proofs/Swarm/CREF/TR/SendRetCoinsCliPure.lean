/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts
public import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureA
import Symbolic.Proofs.Refinement.ExecBridgeSendCtOS
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.SHARED.HmacLen
import Symbolic.Proofs.Swarm.SHARED.SpqrBytesOblig
import Symbolic.Proofs.Swarm.TRREF.MacFormBridge

/-!
# Pure Send-Wire State and Ciphertext Correspondence

Proves `pureEvalSendWire_stateRel_and_message_64`, establishing post-send `StateRel` and
wire-ciphertext correspondence for `pureEvalSendWire` under `sendGhost`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure
open Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal.TripleRatchet (kdfCk)
open DY.Libsignal.Refinement (sha256CompressFunction x25519PublicKeySymbol ExternCryptoLawsHold
  encodeWith canonicalVariation encodeField)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open CryptoVerification
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record (encSession)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.SR
open Proofs.libsignal.Hooks2 (cryptoOf' cryptoOf'_F)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.Pure (slots_NonEmptyV1Q slots_RecordCanonical_Q)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes spqrSendOf_of_send_some)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec senderChainToChainRec)
attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set mut_exec_modifyGet mut_exec_liftE mut_exec_bind
attribute [local instance] subFunction_gRandom_src

theorem stateRel_sessionToRecordRec_extract_TR
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (st : TRState)
    (s : Session (List (BitVec 8))) (hrel : StateRel interpretation S g st (sessionToRecordRec s)) :
    let gam := gamma interpretation S g; let sk := clamp (gam st.dhs)
    s.state.sessionVersion = 4#32 ∧ s.state.previousCounter = st.pn.toBitVec ∧ s.state.pqRatchetState = gam st.spqr ∧
    s.state.localIdentity.serialize = serializedKey ((gam st.myIk).drop 1) ∧
    (∃ remote : IdentityKey, s.state.remoteIdentity = some remote ∧ remote.serialize = serializedKey ((gam st.peerIk).drop 1)) ∧
    (∃ sc : SenderChain, s.state.senderChain = some sc ∧
      sc.ratchetKey.publicKey.serialize = serializedKey ((interpretation x25519PublicKeySymbol [sk]).getD []) ∧
      sc.ratchetKey.privateKey.bytes.toList = sk ∧ sc.chainKey.index = st.ns.toBitVec ∧
      CryptoGames.HMAC.keyToBytes32 sc.chainKey.key = gam st.cks) := by
  dsimp only; have heq := hrel.2
  change eraseSkipped (eraseUnmodelled (sessionToSessionRec s)) = sessionOf interpretation (gamma interpretation S g) st at heq
  rw [eraseSkipped_eraseUnmodelled_sessionToSessionRec_TR] at heq; unfold sessionOf at heq
  injection heq with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  refine ⟨h1, h5, h13, h2, ?_, ?_⟩
  · cases hrem : s.state.remoteIdentity with
    | none => rw [hrem] at h3; simp [ecKey] at h3
    | some rem => rw [hrem] at h3; exact ⟨rem, rfl, h3⟩
  · cases hsc : s.state.senderChain with
    | none => rw [hsc] at h6; simp at h6
    | some sc =>
      rw [hsc] at h6; dsimp only [Option.map_some, senderChainToChainRec] at h6
      injection h6 with hchain_eq; injection hchain_eq with hpub hpriv hck _
      injection hck with hpair; injection hpair with hidx hkey; exact ⟨sc, rfl, hpub, hpriv, hidx, hkey⟩

theorem stateRel_sessionToRecordRec_advance_TR
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (st : TRState)
    (s : Session (List (BitVec 8))) (sc : SenderChain) (nextCk : ChainKey)
    (cks' spqr' : DY.Bytes) (newPqState : List (BitVec 8))
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hsc : s.state.senderChain = some sc) (hidx_eq : nextCk.index = (st.ns + 1).toBitVec)
    (hkey_eq : CryptoGames.HMAC.keyToBytes32 nextCk.key = gamma interpretation S g cks')
    (hpq_eq : newPqState = gamma interpretation S g spqr') :
    StateRel interpretation S g { st with cks := cks', ns := st.ns + 1, spqr := spqr' }
      (sessionToRecordRec { s with state := { s.state with
        senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }) := by
  refine ⟨rfl, ?_⟩; have heq := hrel.2
  change eraseSkipped (eraseUnmodelled (sessionToSessionRec s)) = sessionOf interpretation (gamma interpretation S g) st at heq
  change eraseSkipped (eraseUnmodelled (sessionToSessionRec _)) = sessionOf interpretation (gamma interpretation S g) _
  rw [eraseSkipped_eraseUnmodelled_sessionToSessionRec_TR] at heq ⊢; unfold sessionOf at heq ⊢
  injection heq with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rw [hsc] at h6; dsimp only [Option.map_some, senderChainToChainRec] at h6 ⊢
  injection h6 with hsc_eq; injection hsc_eq with hpub hpriv hck _
  rw [h1, h2, h3, h4, h5, h7, hpub, hpriv, hidx_eq, hkey_eq, hpq_eq]

abbrev spqrSemOf := compSemOf

theorem spqrSendOf_compSemOf_of_send_some (i : ExternInterpretation)
    (hEq : ExternCryptoLawsHold i)
    {stBytes coinsBytes st' msg : HwBytes} {salt? : Salt}
    (hsend : (spqrModelOf i).send stBytes coinsBytes = some (st', salt?, msg)) :
    Symbolic.Swarm.SHARED.SpqrBytes.spqrSendStateOf i stBytes coinsBytes = st' ∧
    Symbolic.Swarm.SHARED.SpqrBytes.spqrSendKeyOf i stBytes coinsBytes = saltToBytes salt? ∧
    Symbolic.Swarm.SHARED.SpqrBytes.spqrSendMsgOf i stBytes coinsBytes = msg := by
  have hlen := Symbolic.Swarm.SHARED.HmacLen.hmacLen_of_ceh hEq
  obtain ⟨h1, h2, h3⟩ := spqrSendOf_of_send_some i hsend
  rw [Symbolic.Swarm.TRREF.MacFormBridge.spqrSendStateOf_spqrSemOf_eq_spqrBytes i hlen] at h1
  rw [Symbolic.Swarm.TRREF.MacFormBridge.spqrSendKeyOf_spqrSemOf_eq_spqrBytes i hlen] at h2
  rw [Symbolic.Swarm.TRREF.MacFormBridge.spqrSendMsgOf_spqrSemOf_eq_spqrBytes i hlen] at h3
  exact ⟨h1, h2, h3⟩

def SpqrInitA2BKdf (b : DY.Bytes) : Prop :=
  ∀ authKey params,
    b.view? DY.Spqr.InitState.SubF = some ⟨authKey, params⟩ →
    params = spqrA2B ∧ ∃ s m, authKey = DY.KdfExtract.kdfExtract s m

def SpqrInitA2B32 (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (b : DY.Bytes) : Prop :=
  ∀ authKey params,
    b.view? DY.Spqr.InitState.SubF = some ⟨authKey, params⟩ →
    (gamma i S g authKey).length = 32 ∧ gamma i S g params = [0#8]

theorem spqrInitA2B32_of_kdf (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {b : DY.Bytes} (h : SpqrInitA2BKdf b) :
    SpqrInitA2B32 i S g b := by
  intro authKey params hx
  obtain ⟨rfl, s, m, rfl⟩ := h authKey params hx
  exact ⟨by rw [gamma_kdfExtract_tr]; exact length_hmacWith _ _ _,
    Symbolic.Swarm.CREF.TR.gamma_spqrParams_a2b i S g⟩

theorem spqrSendB_compSemOf_of_send_some (i : ExternInterpretation)
    (hEq : ExternCryptoLawsHold i)
    {stBytes coinsBytes st' msg : HwBytes} {salt? : Salt}
    (hsend : (spqrModelOf i).send stBytes coinsBytes = some (st', salt?, msg)) :
    Symbolic.Swarm.SHARED.SpqrBytes.spqrSendB (sha256CompressFunction i)
      (Symbolic.Swarm.SHARED.HookAuth.mlkemOf i)
      (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf i) stBytes coinsBytes =
      some (st', saltToBytes salt?, msg) := by
  have hlen := Symbolic.Swarm.SHARED.HmacLen.hmacLen_of_ceh hEq
  rw [← Symbolic.Swarm.TRREF.MacFormBridge.spqrSendB_spqrSemOf_eq_spqrBytes _ _ hlen]
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrSendB
  change (match (spqrModelOf i).send stBytes coinsBytes with
    | some (st', salt?, msg) => some (st', saltToBytes salt?, msg)
    | none => none) = _
  rw [hsend]

theorem gamma_spqrSend_bridge (i : ExternInterpretation) (hEq : ExternCryptoLawsHold i)
    (r₀ : ProtocolSetup) (g : Ghost)
    (stSpqr coinsTerm : DY.Bytes) {newPqState pqMsgBytes : HwBytes} {salt? : Salt}
    (hinit : SpqrInitA2B32 i (spqrSemOf i r₀) g stSpqr)
    (hsend : (spqrModelOf i).send (gamma i (spqrSemOf i r₀) g stSpqr)
      (gamma i (spqrSemOf i r₀) g coinsTerm) = some (newPqState, salt?, pqMsgBytes)) :
    let S := spqrSemOf i r₀
    gamma i S g (DY.Spqr.spqrSend stSpqr coinsTerm).1 = newPqState ∧
    gamma i S g (DY.Spqr.spqrSend stSpqr coinsTerm).2.1 = spqrKeyBytes (saltToBytes salt?) ∧
    gamma i S g (DY.Spqr.spqrSend stSpqr coinsTerm).2.2 = pqMsgBytes := by
  dsimp only
  set S := spqrSemOf i r₀
  obtain ⟨h1, h2, h3⟩ := spqrSendOf_compSemOf_of_send_some i hEq hsend
  refine ⟨(gamma_spqrSendState i S g stSpqr coinsTerm).trans h1, ?_,
    (gamma_spqrSendMsg i S g stSpqr coinsTerm).trans h3⟩
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF stSpqr
  unfold DY.Spqr.spqrSend; dsimp only; split
  · next authKey params hx =>
    obtain ⟨hk, hp⟩ := hinit authKey params hx
    rw [hx] at hpv; dsimp only at hpv
    have hst_eq : stSpqr = DY.Spqr.spqrInit authKey params := hpv.symm
    have hsendB := spqrSendB_compSemOf_of_send_some i hEq hsend
    rw [hst_eq, gamma_spqrInit i S g authKey params, hp] at hsendB
    have hkey := (Symbolic.Swarm.SHARED.SpqrBytes.spqrSendB_fresh_first_of_some
      (sha256CompressFunction i) (Symbolic.Swarm.SHARED.HookAuth.mlkemOf i)
      (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf i)
      (gamma i S g authKey) (gamma i S g coinsTerm)
      newPqState (saltToBytes salt?) pqMsgBytes hk hsendB).1
    rw [gamma_spqrChainKey, gamma_spqrIdx_one, hp]
    exact congrArg spqrKeyBytes hkey.symm
  · rw [gamma_spqrSendKey]; exact congrArg spqrKeyBytes h2

theorem mut_exec_encryptW_of_send_some (C : Crypto) (W : AesW) (S : SpqrModel)
    (o : OutgoingTripleRatchet (List (BitVec 8))) (ptext : List (BitVec 8))
    (addresses : Option (List (BitVec 8))) (coins newPqState pqMsgBytes : List (BitVec 8))
    (salt? : Salt) (hsend : S.send o.pqrState coins = some (newPqState, salt?, pqMsgBytes))
    (hidx : o.senderChainKey.index ≠ BitVec.allOnes 32)
    (hnp : ¬ S.sendPanics o.pqrState coins) :
    Mut.exec (OutgoingTripleRatchet.encryptW C W protoSignalCodec (spqrOfModel S) ptext addresses coins) o =
      (.ok (SignalMessage.new C.F protoSignalCodec o.sessionVersion
          ((o.senderChainKey.messageKeys C.F).generateKeys C.F salt?).macKey
          addresses o.senderRatchetKey.publicKey o.senderChainKey.index o.previousCounter
          (W.enc ((o.senderChainKey.messageKeys C.F).generateKeys C.F salt?).cipherKey
            ((o.senderChainKey.messageKeys C.F).generateKeys C.F salt?).iv ptext)
          o.localIdentityKey o.remoteIdentityKey pqMsgBytes),
        { o with senderChainKey := ⟨CryptoGames.HKDF.bytesToKey32 (CryptoGames.Ratchet.chainHmac C.F
            o.senderChainKey.key CryptoGames.Ratchet.chainKeySeed), o.senderChainKey.index + 1⟩, pqrState := newPqState }) := by
  unfold OutgoingTripleRatchet.encryptW
  simp only [mut_exec_bind, mut_exec_get, spqrOfModel, hnp, Bool.false_eq_true, ↓reduceIte, hsend]
  unfold ChainKey.nextChainKey
  simp only [mut_exec_liftE, hidx, ↓reduceIte, mut_exec_set, mut_exec_pure]

theorem mut_exec_encryptW_allOnes_of_send_some (C : Crypto) (W : AesW) (S : SpqrModel)
    (o : OutgoingTripleRatchet (List (BitVec 8))) (ptext : List (BitVec 8))
    (addresses : Option (List (BitVec 8))) (coins newPqState pqMsgBytes : List (BitVec 8))
    (salt? : Salt) (hsend : S.send o.pqrState coins = some (newPqState, salt?, pqMsgBytes))
    (hidx : o.senderChainKey.index = BitVec.allOnes 32) :
    Mut.exec (OutgoingTripleRatchet.encryptW C W protoSignalCodec (spqrOfModel S) ptext addresses coins) o = (.error .panic, o) := by
  unfold OutgoingTripleRatchet.encryptW
  by_cases hpan : S.sendPanics o.pqrState coins = true
  · simp only [mut_exec_bind, mut_exec_get, spqrOfModel, hpan, ↓reduceIte, mut_exec_throw]
  · simp only [mut_exec_bind, mut_exec_get, spqrOfModel, hpan, Bool.false_eq_true, ↓reduceIte, hsend]
    unfold ChainKey.nextChainKey
    simp only [mut_exec_liftE, hidx, ↓reduceIte]

private theorem applyToSessionState_taken_eq (st : SessionState HwBytes) (sc : SenderChain)
    (nextCk : ChainKey) (newPqState : HwBytes) (ver8 : BitVec 8) (remote : IdentityKey)
    (hsc : st.senderChain = some sc) :
    ({ senderRatchetKey := sc.ratchetKey, senderChainKey := nextCk,
       previousCounter := st.previousCounter, pqrState := newPqState,
       sessionVersion := ver8, localIdentityKey := st.localIdentity,
       remoteIdentityKey := remote } : OutgoingTripleRatchet HwBytes).applyToSessionState
      { st with pqRatchetState := default } =
    { st with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } := by
  cases st; cases sc
  dsimp only [OutgoingTripleRatchet.applyToSessionState] at hsc ⊢
  rw [hsc]; rfl

theorem pureEvalSendWire_exec (C : Crypto) (W : AesW) (S : SpqrModel)
    (sess : Session HwBytes) (pendingAddrs : Option HwBytes) (ptext coins : HwBytes)
    (out : HwBytes × HwBytes)
    (sc : SenderChain) (remote : IdentityKey) (newPqState pqMsgBytes : HwBytes) (salt? : Salt)
    (hev : pureEvalSendWire C W S sess pendingAddrs ptext coins = some out)
    (hppk : sess.pendingPreKey = none) (hver : sess.state.sessionVersion = 4#32)
    (hsc : sess.state.senderChain = some sc) (hrem : sess.state.remoteIdentity = some remote)
    (hsend : S.send sess.state.pqRatchetState coins = some (newPqState, salt?, pqMsgBytes)) :
    let mkg := sc.chainKey.messageKeys C.F; let mk := mkg.generateKeys C.F salt?
    let ctext := W.enc mk.cipherKey mk.iv ptext
    let msg := SignalMessage.new C.F protoSignalCodec 4#8 mk.macKey none
      sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext sess.state.localIdentity remote pqMsgBytes
    let nextCk : ChainKey := ⟨CryptoGames.HKDF.bytesToKey32 (CryptoGames.Ratchet.chainHmac C.F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed), sc.chainKey.index + 1⟩
    sc.chainKey.index ≠ BitVec.allOnes 32 ∧
    out = (CryptoVerification.E2E.Record.encodeRecord
      ⟨some { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }⟩,
      wireWhisperTag :: msg.serialized) := by
  dsimp only
  have hnp : ¬ S.sendPanics sess.state.pqRatchetState coins := by
    rcases out with ⟨s0, m0⟩; exact (pureEvalSendWire_some_inv hev).1
  unfold pureEvalSendWire at hev
  have hfrom := mut_exec_fromSessionState_v4 sess.state sc remote hver hsc hrem
  rw [hfrom] at hev; dsimp only at hev; rw [hppk] at hev; dsimp only at hev
  by_cases hidx : sc.chainKey.index = BitVec.allOnes 32
  · have henc := mut_exec_encryptW_allOnes_of_send_some C W S
      ⟨sc.ratchetKey, sc.chainKey, sess.state.previousCounter, sess.state.pqRatchetState, 4#8, sess.state.localIdentity, remote⟩
      ptext none coins newPqState pqMsgBytes salt? hsend hidx
    rw [henc] at hev; cases hev
  · refine ⟨hidx, ?_⟩
    have henc := mut_exec_encryptW_of_send_some C W S
      ⟨sc.ratchetKey, sc.chainKey, sess.state.previousCounter, sess.state.pqRatchetState, 4#8, sess.state.localIdentity, remote⟩
      ptext none coins newPqState pqMsgBytes salt? hsend hidx hnp
    dsimp only at henc
    rw [henc] at hev; dsimp only at hev
    rw [applyToSessionState_taken_eq sess.state sc _ newPqState 4#8 remote hsc] at hev
    rw [hppk]
    exact (Option.some.inj hev).symm

theorem pureEvalSendWire_exec_pending (C : Crypto) (W : AesW) (S : SpqrModel)
    (sess : Session HwBytes) (pendingAddrs : Option HwBytes) (ptext coins : HwBytes)
    (out : HwBytes × HwBytes)
    (sc : SenderChain) (remote : IdentityKey)
    (items : PendingPreKey) (kpk : PendingKyberPreKey)
    (newPqState pqMsgBytes : HwBytes) (salt? : Salt)
    (hev : pureEvalSendWire C W S sess pendingAddrs ptext coins = some out)
    (hver : sess.state.sessionVersion = 4#32)
    (hsc : sess.state.senderChain = some sc)
    (hrem : sess.state.remoteIdentity = some remote)
    (hppk : sess.pendingPreKey = some items)
    (hkpk : sess.pendingKyberPreKey = some kpk)
    (hsend : S.send sess.state.pqRatchetState coins = some (newPqState, salt?, pqMsgBytes)) :
    let mkg := sc.chainKey.messageKeys C.F
    let mk := mkg.generateKeys C.F salt?
    let ctext := W.enc mk.cipherKey mk.iv ptext
    let innerMsg := SignalMessage.new C.F protoSignalCodec 4#8 mk.macKey pendingAddrs
      sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext
      sess.state.localIdentity remote pqMsgBytes
    let psm := PreKeySignalMessage.new 4#8 sess.localRegistrationId items.preKeyId
      items.signedPreKeyId (some ⟨kpk.preKeyId, kpk.ciphertext⟩) items.baseKey
      sess.state.localIdentity innerMsg
    let nextCk : ChainKey :=
      ⟨CryptoGames.HKDF.bytesToKey32
        (CryptoGames.Ratchet.chainHmac C.F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed),
       sc.chainKey.index + 1⟩
    sc.chainKey.index ≠ BitVec.allOnes 32 ∧
    out = (CryptoVerification.E2E.Record.encodeRecord
      ⟨some { sess with state :=
        { sess.state with
          senderChain := some { sc with chainKey := nextCk }
          pqRatchetState := newPqState } }⟩,
      wirePrekeyTag :: psm.serialized) := by
  dsimp only
  have hnp : ¬ S.sendPanics sess.state.pqRatchetState coins := by
    rcases out with ⟨s0, m0⟩; exact (pureEvalSendWire_some_inv hev).1
  unfold pureEvalSendWire at hev
  have hfrom := mut_exec_fromSessionState_v4 sess.state sc remote hver hsc hrem
  rw [hfrom] at hev; dsimp only at hev; rw [hppk] at hev; dsimp only at hev
  by_cases hidx : sc.chainKey.index = BitVec.allOnes 32
  · have henc := mut_exec_encryptW_allOnes_of_send_some C W S
      ⟨sc.ratchetKey, sc.chainKey, sess.state.previousCounter, sess.state.pqRatchetState, 4#8, sess.state.localIdentity, remote⟩
      ptext pendingAddrs coins newPqState pqMsgBytes salt? hsend hidx
    rw [henc] at hev; cases hev
  · refine ⟨hidx, ?_⟩
    have henc := mut_exec_encryptW_of_send_some C W S
      ⟨sc.ratchetKey, sc.chainKey, sess.state.previousCounter, sess.state.pqRatchetState, 4#8, sess.state.localIdentity, remote⟩
      ptext pendingAddrs coins newPqState pqMsgBytes salt? hsend hidx hnp
    dsimp only at henc
    rw [henc, hkpk] at hev; dsimp only [Option.map] at hev
    rw [applyToSessionState_taken_eq sess.state sc _ newPqState 4#8 remote hsc] at hev
    rw [hppk, hkpk]
    exact (Option.some.inj hev).symm

theorem serializeContent_eq_append_bytesField5 (rk : PublicKey)
    (counter previousCounter : BitVec 32) (ctext pqMsgBytes : List (BitVec 8)) :
    serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext pqMsgBytes none =
      serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext [] none ++
        CryptoVerification.E2E.Record.bytesField 5 pqMsgBytes := by
  cases pqMsgBytes <;>
    simp [serializeContent, protoSignalCodec, CryptoVerification.LibsignalProtoCodec.encode,
      CryptoVerification.LibsignalProtoCodec.encodeBytesField, CryptoVerification.E2E.Record.bytesField,
      CryptoVerification.E2E.Record.lenField, List.append_assoc]

theorem ctext_and_pq_length_lt_of_serialized (F : ShaCompress) (macKey : BitVec 256)
    (rk : PublicKey) (counter previousCounter : BitVec 32) (ctext pqMsgBytes : List (BitVec 8))
    (localId remote : IdentityKey)
    (hmsg : (wireWhisperTag :: (SignalMessage.new F protoSignalCodec 4#8 macKey none rk counter previousCounter
      ctext localId remote pqMsgBytes).serialized).length < 2 ^ 64) :
    ctext.length < 2 ^ 64 ∧ pqMsgBytes.length < 2 ^ 64 := by
  dsimp only [SignalMessage.new] at hmsg
  rw [List.length_cons, List.length_append, serializeContent_eq_append_bytesField5, List.length_append] at hmsg
  have h1 : ctext.length ≤ (serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext [] none).length := by
    dsimp [serializeContent, protoSignalCodec, CryptoVerification.LibsignalProtoCodec.encode, CryptoVerification.LibsignalProtoCodec.encodeBytesField]
    simp only [List.length_append]; omega
  have h2 : pqMsgBytes.length ≤ (CryptoVerification.E2E.Record.bytesField 5 pqMsgBytes).length := by
    unfold CryptoVerification.E2E.Record.bytesField CryptoVerification.E2E.Record.lenField
    split_ifs with h <;> simp [h]; omega
  omega

theorem serializeContent_tr_eq_encodeWith (rk : PublicKey)
    (counter previousCounter : BitVec 32) (ctext pqMsgBytes : List (BitVec 8))
    (hct : ctext.length < 2 ^ 64) (hpq : pqMsgBytes.length < 2 ^ 64) :
    serializeContent protoSignalCodec 4#8 rk counter previousCounter ctext pqMsgBytes none =
      encodeWith canonicalVariation
        { version := 4, ratchetKey := rk.bytes.toList, counter := counter.toNat, previousCounter := previousCounter.toNat, ciphertext := ctext } ++
        (if pqMsgBytes = [] then [] else encodeField 5 0 0 (.bytes pqMsgBytes)) := by
  rw [serializeContent_eq_append_bytesField5,
    Proofs.libsignal.Refinement.ExecBridgeSendCtOS.serializeContent_eq_encodeWith_canonicalVariation rk counter previousCounter ctext hct,
    ← Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 5 pqMsgBytes hpq]; rfl

theorem gamma_computeMac_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (macKeyTerm myIk peerIk wire : DY.Bytes) (sender receiver : IdentityKey) (macKeyBv : BitVec 256)
    (hkey : keyToBytes32 macKeyBv = gamma interpretation S g macKeyTerm)
    (hsender : sender.serialize = gamma interpretation S g myIk)
    (hreceiver : receiver.serialize = gamma interpretation S g peerIk)
    (content : List (BitVec 8)) (hwire : content = gamma interpretation S g wire) :
    CryptoGames.LibsignalSession.computeMac (sha256CompressFunction interpretation) sender receiver macKeyBv content =
    gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKeyTerm myIk peerIk wire) := by
  change CryptoGames.HMAC.hmacSha256Trunc8 (sha256CompressFunction interpretation) (keyToBytes32 macKeyBv) ((sender.serialize ++ receiver.serialize) ++ content) =
    gamma interpretation S g (DY.Trunc.trunc8 (DY.KdfExtract.kdfExtract macKeyTerm (DY.Concat.concat myIk (DY.Concat.concat peerIk wire))))
  rw [gamma_trunc8_tr, gamma_kdfExtract_tr, gamma_concat_tr, gamma_concat_tr, hkey, hsender, hreceiver, hwire, List.append_assoc]; rfl

theorem ratchetKey_publicKey_bytes_eq_gamma_dhPk_tr (interpretation : ExternInterpretation)
    (_hEq : ExternCryptoLawsHold interpretation) (S : SpqrSem) (g : Ghost) (st : TRState) (sc : SenderChain)
    (_hdhs : (gamma interpretation S g st.dhs).length = 32)
    (hpub : sc.ratchetKey.publicKey.serialize = serializedKey ((interpretation x25519PublicKeySymbol [clamp (gamma interpretation S g st.dhs)]).getD [])) :
    sc.ratchetKey.publicKey.bytes.toList = gamma interpretation S g (DY.DiffieHellman.dhPk st.dhs) := by
  unfold PublicKey.serialize serializedKey ecKey at hpub; injection hpub with _ hbytes
  rw [← gamma_dhPk_tr] at hbytes; exact hbytes

private theorem encSession_length_le_encodeRecord (s : Session (List (BitVec 8))) :
    (encSession s).length ≤ (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField CryptoVerification.E2E.Record.lenField
  simp only [Option.map_some, List.length_append]; omega

private theorem pqRatchetState_length_le_encSession (s : Session (List (BitVec 8))) :
    s.state.pqRatchetState.length ≤ (encSession s).length := by
  unfold encSession
  have : s.state.pqRatchetState.length ≤ (CryptoVerification.E2E.Record.bytesField 15 s.state.pqRatchetState).length := by
    unfold CryptoVerification.E2E.Record.bytesField CryptoVerification.E2E.Record.lenField; split_ifs with h <;> simp [h]; omega
  simp only [List.length_append]; omega

theorem pureEvalSendWire_stateRel_and_message_64
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (_hwf : ProtocolSetupWF r₀) (_hik : IkShape interpretation r₀)
    (S : SpqrSem) (hS : S = spqrSemOf interpretation r₀) (hEq : ExternCryptoLawsHold interpretation)
    (_p : Participant) (recBytes pt coins : HwBytes) (g : Ghost) (ms₁ : List Move)
    (retState retMessage : HwBytes) (hmsg_lt : retMessage.length < 2 ^ 64) (hst_lt : retState.length < 2 ^ 64)
    (sess : Session HwBytes) (hrc : slots_RecordCanonical_Q slots_NonEmptyV1Q recBytes sess)
    (hppk : sess.pendingPreKey = none)
    (hev : pureEvalSendWire (cryptoOf' interpretation) (interpW interpretation) (spqrModelOf interpretation) sess none pt coins = some (retState, retMessage))
    (rec : RecordRec) (st : TRState) (hrecBytes : recBytes = recordBytes rec)
    (hrel : StateRel interpretation S (sendGhost g (runTraceMoves r₀ ms₁).length pt coins) st rec)
    (hks : TRKeyShape interpretation S (sendGhost g (runTraceMoves r₀ ms₁).length pt coins) st)
    (hinit : SpqrInitA2BKdf st.spqr) :
    ∃ (rec' : RecordRec), retState = recordBytes rec' ∧
      StateRel interpretation S (sendGhost g (runTraceMoves r₀ ms₁).length pt coins) (encSt st coins.length (runTraceMoves r₀ ms₁).length) rec' ∧
      rec'.current.receiverChains = rec.current.receiverChains ∧
      retMessage = wireWhisperTag :: gamma interpretation S (sendGhost g (runTraceMoves r₀ ms₁).length pt coins) (encMsg st coins.length (runTraceMoves r₀ ms₁).length) := by
  subst hS; set ts := (runTraceMoves r₀ ms₁).length; set g' := sendGhost g ts pt coins; set S := spqrSemOf interpretation r₀
  obtain ⟨hnorm_eq, halice_lt, hseeds⟩ := rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes hrc
  have hrel_sess : StateRel interpretation S g' st (sessionToRecordRec sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq, stateRel_normPending_iff]
    exact hrel
  obtain ⟨hver, hpctr, hpq, hloc_ser, ⟨remote, hrem, hrem_ser⟩, ⟨sc, hsc, hpub, _, hidx, hck_key⟩⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g' st sess hrel_sess
  have hsend_some := pureEvalSendWire_some_send_isSome _ _ _ sess none pt coins (retState, retMessage) hev
  obtain ⟨⟨newPqState, salt?, pqMsgBytes⟩, hsend⟩ := Option.isSome_iff_exists.mp hsend_some
  obtain ⟨_, hout⟩ := pureEvalSendWire_exec (cryptoOf' interpretation) (interpW interpretation)
    (spqrModelOf interpretation) sess none pt coins (retState, retMessage) sc remote newPqState pqMsgBytes salt? hev hppk hver hsc hrem hsend
  rw [cryptoOf'_F] at hout; injection hout with hstate_eq hmsg_eq
  set F := sha256CompressFunction interpretation
  set nextCk : ChainKey := ⟨CryptoGames.HKDF.bytesToKey32 (CryptoGames.Ratchet.chainHmac F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed), sc.chainKey.index + 1⟩
  set sess' : Session (List (BitVec 8)) :=
    { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }
  have hsess'_len : (encSession sess').length < 2 ^ 64 := lt_of_le_of_lt (encSession_length_le_encodeRecord sess') (hstate_eq ▸ hst_lt)
  have hpq'_len : sess'.state.pqRatchetState.length < 2 ^ 64 := by have := pqRatchetState_length_le_encSession sess'; omega
  have hrec'_bytes : recordBytes (sessionToRecordRecPending sess') = retState := by
    rw [hstate_eq]; exact recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 sess' (by dsimp only [sess']; omega) hpq'_len hseeds hsess'_len
  set coinsTerm := randTerm (ts + 1) coins.length
  have hcoins_gam : gamma interpretation S g' coinsTerm = coins := gamma_sendGhost_coins_all interpretation S g ts pt coins
  have hsend_gam : (spqrModelOf interpretation).send (gamma interpretation S g' st.spqr) (gamma interpretation S g' coinsTerm) =
      some (newPqState, salt?, pqMsgBytes) := by rw [← hpq, hcoins_gam]; exact hsend
  obtain ⟨hspqr1, hspqr2, hspqr3⟩ := gamma_spqrSend_bridge interpretation hEq r₀ g' st.spqr coinsTerm
    (spqrInitA2B32_of_kdf interpretation S g' hinit) hsend_gam
  have hck_eq : keyToBytes32 sc.chainKey.key = gamma interpretation S g' st.cks := hck_key
  have hstep : gamma interpretation S g' (kdfCk st.cks).1 = CryptoGames.Ratchet.chainHmac F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed := by
    rw [gamma_kdfCk_fst_tr, ← hck_eq]; rfl
  have hlen_cks' : (gamma interpretation S g' (kdfCk st.cks).1).length = 32 := by rw [gamma_kdfCk_fst_tr]; exact length_hmacWith _ _ _
  have hrel' : StateRel interpretation S g' (encSt st coins.length ts) (sessionToRecordRec sess') := by
    apply stateRel_sessionToRecordRec_advance_TR interpretation S g' st sess sc nextCk
      (kdfCk st.cks).1 (DY.Spqr.spqrSend st.spqr coinsTerm).1 newPqState hrel_sess hsc
    · dsimp only [nextCk]; rw [hidx]; rfl
    · dsimp only [nextCk]; rw [← hstep, keyToBytes32_bytesToKey32_c _ hlen_cks']
    · exact hspqr1.symm
  have hchains_eq : (sessionToRecordRecPending sess').current.receiverChains = rec.current.receiverChains := by
    have h := congrArg (fun x => x.current.receiverChains) hnorm_eq
    dsimp only [normPending, normPendingS, sessionToRecordRecPending, sessionToSessionRec, sess'] at h ⊢
    exact h.symm
  refine ⟨sessionToRecordRecPending sess', hrec'_bytes.symm,
    (stateRel_sessionToRecordRecPending_iff interpretation S g' _ sess').mpr hrel', hchains_eq, ?_⟩
  rw [hmsg_eq]; congr 1
  set seed := (kdfCk st.cks).2; set pqSalt := (DY.Spqr.spqrSend st.spqr coinsTerm).2.1
  set pqTerm := (DY.Spqr.spqrSend st.spqr coinsTerm).2.2; set keys := trMsgKeys pqSalt seed
  set mk := (sc.chainKey.messageKeys F).generateKeys F salt?
  set ctext := (interpW interpretation).enc mk.cipherKey mk.iv pt
  obtain ⟨hct_lt, hpq_lt⟩ := ctext_and_pq_length_lt_of_serialized F mk.macKey
    sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext pqMsgBytes sess.state.localIdentity remote (hmsg_eq ▸ hmsg_lt)
  have hseed : (sc.chainKey.messageKeys F).seed = gamma interpretation S g' seed := by rw [gamma_kdfCk_snd_tr, ← hck_eq]; rfl
  have hmkg : sc.chainKey.messageKeys F = ⟨gamma interpretation S g' seed, sc.chainKey.index⟩ := by
    cases hmk : sc.chainKey.messageKeys F
    have hs : (sc.chainKey.messageKeys F).seed = gamma interpretation S g' seed := hseed
    have hc : (sc.chainKey.messageKeys F).counter = sc.chainKey.index := rfl
    rw [hmk] at hs hc; subst hs hc; rfl
  have hgen := gamma_trMsgKeys_eq_generateKeys interpretation S g' pqSalt seed sc.chainKey.index salt? hspqr2; dsimp only at hgen
  have hmk_c : keyToBytes32 mk.cipherKey = gamma interpretation S g' keys.cipherKey := by dsimp only [mk]; rw [hmkg]; exact hgen.1
  have hmk_m : keyToBytes32 mk.macKey = gamma interpretation S g' keys.macKey := by dsimp only [mk]; rw [hmkg]; exact hgen.2.1
  have hmk_iv : CryptoGames.CBC.blockToBytesLE mk.iv = (gamma interpretation S g' keys.iv).take 16 := by dsimp only [mk]; rw [hmkg]; exact hgen.2.2.1
  have hpt_gam : pt = gamma interpretation S g' (randTerm ts 32) := by rw [gamma_sendGhost_pt]
  have hct_gam : ctext = gamma interpretation S g' (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ts 32)) := by
    dsimp only [ctext, interpW]; rw [hpt_gam, hmk_c, hmk_iv, gamma_symEnc_tr]
  have hrk_gam : sc.ratchetKey.publicKey.bytes.toList = gamma interpretation S g' (DY.DiffieHellman.dhPk st.dhs) :=
    ratchetKey_publicKey_bytes_eq_gamma_dhPk_tr interpretation hEq S g' st sc hks.dhs_len hpub
  have hwire_def : encWire st coins.length ts =
      trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ts 32)) pqTerm := rfl
  have haddr_nil : g'.addr (trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ts 32)) pqTerm) = [] := by
    rw [← hwire_def]; exact sendGhost_addr_encWire g st coins.length ts pt coins
  have hwire_gam : serializeContent protoSignalCodec 4#8 sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext pqMsgBytes none =
      gamma interpretation S g' (encWire st coins.length ts) := by
    rw [serializeContent_tr_eq_encodeWith _ _ _ _ _ hct_lt hpq_lt, hwire_def, gamma_trHonestWireMsg _ _ _ _ _ _ _ _ haddr_nil, hrk_gam, hidx, hpctr, hct_gam, hspqr3]; rfl
  have hloc_gam : sess.state.localIdentity.serialize = gamma interpretation S g' st.myIk := hloc_ser.trans hks.myIk_ser
  have hrem_gam : remote.serialize = gamma interpretation S g' st.peerIk := hrem_ser.trans hks.peerIk_ser
  have hmac_gam := gamma_computeMac_tr interpretation S g' keys.macKey st.myIk st.peerIk
    (encWire st coins.length ts) sess.state.localIdentity remote mk.macKey hmk_m hloc_gam hrem_gam _ hwire_gam
  dsimp only [SignalMessage.new, encMsg, encMac]
  rw [gamma_concat_tr, ← hwire_gam, ← hmac_gam]

end Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure
