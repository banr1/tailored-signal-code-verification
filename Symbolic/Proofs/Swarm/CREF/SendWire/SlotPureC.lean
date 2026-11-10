/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.SendWire.PendingPure
public import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPureA
import Symbolic.Proofs.Swarm.CREF.Initiate.TransferPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendPA
import Symbolic.Proofs.Swarm.CREF.SendWire.GhostInvariance
import Symbolic.Proofs.Swarm.CREF.SendWire.RecvSimV3SendPure
import Symbolic.Proofs.Swarm.CREF.SendWire.StateInv
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPure
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach

/-!
# Pending-PreKey `SendWire` Outcome and Per-Explanation Step

Defines `SndPendingRetOut` and proves `matchedPrefix_snoc_encrypt_wrap`,
`snd_ret_eval_and_matchedPrefix`, and `sndP_ret_pureCRelAt_of_faithful` for returning
pending-prekey sends.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.SndPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.IniSndPure
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
open Symbolic.Swarm.CREF.SendWire
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open Proofs.libsignal.SR
open Proofs.libsignal.Hooks2 (cryptoOf' cryptoOf'_F)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open CryptoGames.HMAC CryptoGames.HKDF
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR

/-- Pure postcondition of an exit-`0` `send_wire` call on Alice's pending-prekey record. -/
structure SndPendingRetOut (interpretation : ExternInterpretation) (_r : ProtocolSetup)
    (recBytes pt coins_cli : HwBytes)
    (mid : List MachineEvent) (retState retMessage : HwBytes) : Prop where
  msg_lt : retMessage.length < 2 ^ 64
  eval : ∀ (sess : CryptoGames.LibsignalSessionApi.Session HwBytes),
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes sess →
    TR.Pure.slots_RecordInScopeP ⟨some sess⟩ →
    TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩ →
    sess.state.remoteIdentity.isSome = true →
    recBytes.length < 2 ^ 62 →
    recBytes.length < 2 ^ 32 - 2 ^ 20 →
    SpqrOooBounded sess.state.pqRatchetState →
    PendingWireRecCanon retState ∧
    ∃ (coins : HwBytes),
      ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      coins <+: coins_cli ∧
      TR.SendRetCoinsCliPure.pureEvalSendWire (cryptoOf' interpretation) (interpW interpretation)
        (spqrModelOf interpretation) sess (some pqHarnessAddrBytes) pt coins =
        some (retState, retMessage)

theorem roleSnapshots_xplBlock_send_pend {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent}
    {p : Participant}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hf : DeltaFaithful p (runTraceMoves r ms₀) δ)
    (hshape : SendBlockShape blk)
    (h0 : RoleSnapshots r (runTraceMoves r ms₀)) :
    RoleSnapshots r (runTraceMoves r (ms₀ ++ δ)) := by
  rw [TR.runTrace_append]
  refine roleSnapshots_of_oneMove (fun _ m hm hr => ?_) (xplInv_send hB hf hshape) h0
  have hsb := hm.1; clear hm; cases m <;> try exact False.elim hsb
  case encrypt me stateIdx coinsLen pqIdx wrap =>
    exact roleSnapshots_encrypt me stateIdx coinsLen pqIdx wrap hr
  case encryptAbort me stateIdx => exact roleSnapshots_encryptAbort me stateIdx hr
  case encryptFail me stateIdx coinsLen => exact roleSnapshots_encryptFail me stateIdx coinsLen hr

theorem matchedPrefix_snoc_encrypt_wrap {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ : List Move}
    {acc mid : List MachineEvent} {p : Participant} {stateIdx ekIdx ctIdx : Nat}
    {st : TripleRatchet.TRState} {ek ct : DY.Bytes} {pt coins msg : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ acc)
    (hwho : who[(callStarts acc).length]? = some p)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hcur : TripleRatchet.isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hns : st.ns ≠ TripleRatchet.u32Max)
    (hek : (runTraceMoves r₀ ms₁).getMessageSentAt ekIdx = some ek)
    (hct : (runTraceMoves r₀ ms₁).getMessageSentAt ctIdx = some ct)
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    (hsend : ∃ ids, SendMatches interpretation r₀ S
      (sendPendingGhost g (runTraceMoves r₀ ms₁).length pt coins) (some ids) msg
      [ek, ct, encMsg st coins.length (runTraceMoves r₀ ms₁).length]) :
    MatchedPrefix interpretation r₀ S who
      (sendPendingGhost g (runTraceMoves r₀ ms₁).length pt coins)
      (ms₁ ++ [Move.encrypt p stateIdx coins.length ((runTraceMoves r₀ ms₁).length + 2) (some (ekIdx, ctIdx))])
      (acc ++ ((.pt pt :: mid) ++ [.send msg])) := by
  have hmp' := matchedPrefix_sendPendingGhost hmp pt coins
  have hrun' := modelRun_snoc_encrypt_wrap (p := p) (coinsLen := coins.length)
    (wrap := some (ekIdx, ctIdx)) hmp'.2.1 hcur
  have hcs : callStarts ((MachineEvent.pt pt :: mid) ++ [MachineEvent.send msg]) = [.pt pt] :=
    snd_callStarts_ret pt msg ⟨coins, hmid⟩
  refine matchedPrefix_snoc_send
    (m := Move.encrypt p stateIdx coins.length ((runTraceMoves r₀ ms₁).length + 2) (some (ekIdx, ctIdx)))
    (evs := (.pt pt :: mid) ++ [.send msg])
    hmp' hrun' rfl hwho rfl hcs ?_ ?_
  · rcases hmid with ⟨rfl, rfl⟩ | ⟨hc_ne, rfl⟩
    · rw [List.length_nil, visOf_encrypt_wrap_zero hst hns hek hct]
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> nofun
    · have hclen : coins.length ≠ 0 := fun h => hc_ne (List.eq_nil_of_length_eq_zero h)
      rw [visOf_encrypt_wrap_ne_zero hst hns hclen hek hct]
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> nofun
  · rcases hmid with ⟨rfl, rfl⟩ | ⟨hc_ne, rfl⟩
    · rw [List.length_nil, visOf_encrypt_wrap_zero hst hns hek hct]
      refine List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, hsend⟩ List.Forall₂.nil)
      exact congrArg (· :: []) (gamma_sendPendingGhost_pt interpretation S g (runTraceMoves r₀ ms₁).length pt [])
    · have hclen : coins.length ≠ 0 := fun h => hc_ne (List.eq_nil_of_length_eq_zero h)
      rw [visOf_encrypt_wrap_ne_zero hst hns hclen hek hct]
      refine List.Forall₂.cons ⟨rfl, ?_⟩
        (List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, hsend⟩ List.Forall₂.nil))
      · exact congrArg (· :: []) (gamma_sendPendingGhost_pt interpretation S g (runTraceMoves r₀ ms₁).length pt coins)
      · exact congrArg (· :: []) (gamma_sendPendingGhost_coins interpretation S g (runTraceMoves r₀ ms₁).length pt coins hclen)

theorem snd_ret_eval_and_matchedPrefix (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r) (who : List Participant)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes)
    (rec pt coins_cli retState retMessage : HwBytes) (acc mid : List MachineEvent)
    (g₀ : Ghost) (ms₀ : List Move)
    (hmp₀ : MatchedPrefix interpretation r S who g₀ ms₀ acc)
    (hwho₀ : who[(callStarts acc).length]? = some r.alice)
    (hpend₀ : PureAliceInitPending interpretation r S g₀ ms₀ rec)
    (hbook₀ : CBook interpretation r S g₀ ms₀ sent accepted acc) (hoooAll : COooAll records)
    (hrec : records r.alice = some rec) (hreclen : rec.length < 2 ^ 32 - 2 ^ 20)
    (hsent_lt : sent.length < 2 ^ 32 - 1)
    (hout : SndPendingRetOut interpretation r rec pt coins_cli mid retState retMessage) :
    PendingRecordCanon rec ∧ PendingWireRecCanon retState ∧
    ∃ (sess : Session HwBytes) (coins : HwBytes),
      TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec sess ∧
      ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      coins <+: coins_cli ∧
      TR.SendRetCoinsCliPure.pureEvalSendWire (cryptoOf' interpretation) (interpW interpretation)
        (spqrModelOf interpretation) sess (some pqHarnessAddrBytes) pt coins = some (retState, retMessage) ∧
      ∃ stateIdx ekIdx ctIdx, TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₀) stateIdx = true ∧
        MatchedPrefix interpretation r S who (sendPendingGhost g₀ (runTraceMoves r ms₀).length pt coins)
          (ms₀ ++ [Move.encrypt r.alice stateIdx coins.length ((runTraceMoves r ms₀).length + 2) (some (ekIdx, ctIdx))])
          (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) := by
  have hcanon : PendingRecordCanon rec := pendingRecordCanon_of_aliceInitPending
    interpretation r S g₀ ms₀ rec hpend₀ hreclen (hoooAll r.alice rec hrec)
  have hlen62 : rec.length < 2 ^ 62 := by rcases hcanon with ⟨_, _, _, _, _, h, _, _⟩; exact h
  obtain ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    hrc, hscope1, hscope2, hget, hcur, _, hpeer, hek, hct, hreg, hver, hpn, hlid, hrem, hrem_ser, hsc, hrk, hck, hidx,
    hppk, _hts_z, hbk, hkpk, hct_ser, hpq, recR, hrecR, hrel, hks, hmk, hnd⟩ := hpend₀
  have hooo : SpqrOooBounded sess.state.pqRatchetState := pqStateOf_of_canonical_Q_pend hrc ▸ hoooAll r.alice rec hrec
  have hrid : sess.state.remoteIdentity.isSome = true := by rw [hrem]; rfl
  obtain ⟨hwc, coins, hmid, hpref, hev⟩ :=
    hout.eval sess hrc hscope1 hscope2 hrid hlen62 hreclen hooo
  refine ⟨hcanon, hwc, sess, coins, hrc, hmid, hpref, hev, stateIdx, ekIdx, ctIdx, hcur, ?_⟩
  let ts := (runTraceMoves r ms₀).length
  let g' := sendPendingGhost g₀ ts pt coins
  have htr : TR.FreshSigma.TraceEntriesLt interpretation S g₀ ts (runTraceMoves r ms₀) :=
    TR.FreshSigma.traceEntriesLt_of_reachable interpretation S g₀ ts hmp₀.2.1.2.2.1.1 (Nat.le_refl _)
  have hst_lt : TR.FreshSigma.StateStampsLt interpretation S g₀ ts st :=
    TR.FreshSigma.traceEntriesLt_at?_st htr (TR.FreshSigma.at?_eq_some_of_getLocalState_some hget)
  have hek_lt : TR.FreshSigma.StampsLt interpretation S g₀ ts ek := stampsLt_of_getMessageSentAt htr hek
  have hct_lt0 : TR.FreshSigma.StampsLt interpretation S g₀ ts ct := stampsLt_of_getMessageSentAt htr hct
  have hdhs_pk_lt : TR.FreshSigma.StampsLt interpretation S g₀ ts (DY.DiffieHellman.dhPk st.dhs) :=
    (TR.FreshSigma.stampsLt_dhPk_pack interpretation S g₀ ts ⟨st.dhs⟩).mpr hst_lt.2.2.2.1
  have hlid' : sess.state.localIdentity.serialize = gamma interpretation S g' st.myIk := by
    rw [gamma_sendPendingGhost_of_stampsLt hst_lt.1]; exact hlid
  have hrem_ser' : remote.serialize = gamma interpretation S g' st.peerIk := by
    rw [gamma_sendPendingGhost_of_stampsLt hst_lt.2.1]; exact hrem_ser
  have hrk' : sc.ratchetKey.publicKey.bytes.toList = gamma interpretation S g' (DY.DiffieHellman.dhPk st.dhs) := by
    rw [gamma_sendPendingGhost_of_stampsLt hdhs_pk_lt]; exact hrk
  have hck' : CryptoGames.HMAC.keyToBytes32 sc.chainKey.key = gamma interpretation S g' st.cks := by
    rw [gamma_sendPendingGhost_of_stampsLt hst_lt.2.2.2.2.1]; exact hck
  have hbk' : items.baseKey.serialize = ecKey (gamma interpretation S g' ek) := by
    rw [gamma_sendPendingGhost_of_stampsLt hek_lt]; exact hbk
  have hct_ser' : kpk.ciphertext = kyberKey (gamma interpretation S g' ct) := by
    rw [gamma_sendPendingGhost_of_stampsLt hct_lt0]; exact hct_ser
  have hpq' : sess.state.pqRatchetState = gamma interpretation S g' st.spqr := by
    rw [gamma_sendPendingGhost_of_stampsLt hst_lt.2.2.2.2.2.1]; exact hpq
  have hns : st.ns ≠ TripleRatchet.u32Max := ns_ne_u32Max_of_trNsBound hbook₀.2.1 hsent_lt hget
  have hsend_some := TR.SendRetCoinsCliPure.pureEvalSendWire_some_send_isSome _ _ _ sess (some pqHarnessAddrBytes) pt coins (retState, retMessage) hev
  obtain ⟨⟨newPqState, salt?, pqMsgBytes⟩, hsend⟩ := Option.isSome_iff_exists.mp hsend_some
  obtain ⟨_, hexec⟩ := TR.SendRetCoinsCliPure.pureEvalSendWire_exec_pending
    (cryptoOf' interpretation) (interpW interpretation) (spqrModelOf interpretation)
    sess (some pqHarnessAddrBytes) pt coins (retState, retMessage) sc remote items kpk newPqState pqMsgBytes salt?
    hev hver hsc hrem hppk hkpk hsend
  rw [cryptoOf'_F] at hexec; injection hexec with _ hmsg_eq
  set F := DY.Libsignal.Refinement.sha256CompressFunction interpretation
  set mk := (sc.chainKey.messageKeys F).generateKeys F salt?
  set ctext := (interpW interpretation).enc mk.cipherKey mk.iv pt
  set innerMsg := CryptoGames.LibsignalSession.SignalMessage.new F CryptoVerification.LibsignalProtoCodec.protoSignalCodec 4#8 mk.macKey
    (some pqHarnessAddrBytes) sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext sess.state.localIdentity remote pqMsgBytes
  have hw_lt : (DY.Libsignal.PQXDH.Refinement.wirePrekeyTag :: (CryptoGames.LibsignalSessionApi.PreKeySignalMessage.new 4#8 r.regIdA items.preKeyId
      items.signedPreKeyId (some ⟨kpk.preKeyId, kpk.ciphertext⟩) items.baseKey sess.state.localIdentity innerMsg).serialized).length < 2 ^ 64 := by
    rw [← hreg, ← hmsg_eq]; exact hout.msg_lt
  obtain ⟨hct_lt, hinner_lt⟩ := psm_field_lengths_lt_of_wire_lt r.regIdA items.preKeyId
    items.signedPreKeyId kpk.preKeyId kpk.ciphertext items.baseKey sess.state.localIdentity innerMsg hw_lt
  have hsend_g' : (spqrModelOf interpretation).send (gamma interpretation (compSemOf interpretation r) g' st.spqr) coins = some (newPqState, salt?, pqMsgBytes) := by
    rw [← hSeq, ← hpq']; exact hsend
  have hinner_eq := innerMsg_serialized_eq_gamma_encMsg
    interpretation r hext.1 g₀ ts pt coins st sc sess.state.localIdentity remote
    sess.state.previousCounter newPqState pqMsgBytes salt? (TR.spqrInitA2BKdf_of_getLocalState hget) hsend_g'
    hidx hpn (hSeq ▸ hck') (hSeq ▸ hrk') (hSeq ▸ hlid') (hSeq ▸ hrem_ser') hinner_lt
  have hpub_a : gamma interpretation S g' st.myIk = ecKey (pubBytes interpretation (secretBytes r 0)) := by
    rw [AliceIk.alice_myIk_of_getLocalState hwf.1 hmp₀.2.1 hget, TR.gamma_serializedIk,
      (TR.gamma_setupPublic_0_2_6 interpretation r S g' (matchedPrefix_sendPendingGhost hmp₀ pt coins).1 hwf.1).1]
  have hwire_eq := preKeySignalMessage_serialized_eq_preKeyWire
    r.regIdA items.preKeyId items.signedPreKeyId kpk.preKeyId (gamma interpretation S g' ek) (gamma interpretation S g' ct)
    items.baseKey sess.state.localIdentity (ecKey (pubBytes interpretation (secretBytes r 0))) innerMsg
    hbk' (hlid'.trans hpub_a) (by rw [← hct_ser']; exact hct_lt) hinner_lt
  refine matchedPrefix_snoc_encrypt_wrap hmp₀ hwho₀ hget hcur hns hek hct hmid
    ⟨(items.preKeyId, items.signedPreKeyId, kpk.preKeyId), ?_⟩
  rw [hmsg_eq, hreg, hct_ser', hwire_eq, show innerMsg.serialized =
    gamma interpretation S g' (TR.SendRetCoinsCliPure.encMsg st coins.length ts) by rw [hSeq]; exact hinner_eq.2.2]
  exact sendMatches_of_preKeyWire_comp interpretation r S g'
    items.preKeyId items.signedPreKeyId kpk.preKeyId ek ct (TR.SendRetCoinsCliPure.encMsg st coins.length ts)

theorem sndP_ret_pureCRelAt_of_faithful (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r)
    {who : List Participant} {records : Participant → Option HwBytes}
    {sent accepted : List HwBytes}
    {acc mid : List MachineEvent} {recBytes pt coins_cli retState retMessage coins : HwBytes}
    {g : Ghost} {ms₀ δ : List Move}
    (hrec : records r.alice = some recBytes)
    (hpend_rec : PureRecPending recBytes)
    (hreclen : recBytes.length < 2 ^ 32 - 2 ^ 20)
    (hout : SndPendingRetOut interpretation r recBytes pt coins_cli mid retState retMessage)
    (hcanon : PendingRecordCanon recBytes) (hwc : PendingWireRecCanon retState)
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    (hdf : DeltaFaithful r.alice (runTraceMoves r ms₀) δ)
    (hB : XplBlock interpretation r S who g ms₀ δ acc ((.pt pt :: mid) ++ [.send retMessage]))
    (hrel₀ : PureCRelAt interpretation r S g ms₀ records sent accepted acc) :
    PureCRelAt interpretation r S g (ms₀ ++ δ)
      (fun q => if q = r.alice then some retState else records q)
      (sent ++ (sentBody retMessage).toList) accepted
      (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) := by
  have hshape := snd_ret_blockShape pt retMessage mid ⟨coins, hmid⟩
  have hrole_out := roleSnapshots_xplBlock_send_pend hB hdf hshape hrel₀.2.2.2
  obtain ⟨pre, m, post, rfl, hpre, ⟨hsb, hsend⟩, hpost⟩ := xplInv_send hB hdf hshape
  obtain ⟨me, stateIdx, cLen, pqIdx, wrap, rfl⟩ := hsend ⟨.send retMessage, by simp, rfl⟩
  have hme_eq : r.alice = me := hsb.symm; subst hme_eq
  have hpq : pqIdx = (runTraceMoves r (ms₀ ++ pre)).length + 2 := snd_encrypt_pqIdx hB.run.2.2.2.2.1; subst hpq
  rw [← TR.runTrace_append r ms₀ pre] at hpost
  have hm_vis : List.Forall₂ (EventMatchesEntry interpretation r S g)
      ((.pt pt :: mid) ++ [.send retMessage])
      ((Move.encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap).vis (runTraceMoves r (ms₀ ++ pre))) := by
    have hfor := hB.matched
    rw [TR.runMoves_append, (snd_invisible_runMoves hpre).1, List.nil_append, ← TR.runTrace_append] at hfor
    simpa [runMoves, (snd_invisible_runMoves hpost).1] using hfor
  obtain ⟨⟨st_m, hst_m, hns_m⟩, _, hcoins_gam⟩ := snd_encrypt_vis_match hm_vis hmid
  have hcur_m := snd_isCurrentSnapshot_of_encrypt hB.run.2.2.1.1 hst_m hns_m
  have hq1 : XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]; exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hrole₁ : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) :=
    snd_roleSnapshots_quiet (movesFrom_mono (fun _ _ h => h.2) _ _ hpre) hrel₀.2.2.2
  have hpost' : MovesFrom InvisibleNoEffect
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap])) post := by
    rwa [TR.runTrace_snoc]
  have htr_wrap : runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) none]) =
      runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) := by
    rw [TR.runTrace_snoc, TR.runTrace_snoc]; rfl
  have hq2 : XplQuiet.QuietExt
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) none]))
      (runTraceMoves r (((ms₀ ++ pre) ++ [.encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post)) := by
    rw [htr_wrap, TR.runTrace_append r _ post]
    exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost')
  have hms_eq : ms₀ ++ (pre ++ .encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post) =
      ((ms₀ ++ pre) ++ [.encrypt r.alice stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post := by simp
  obtain ⟨_, hpend₀⟩ := recPending_imp_alice_pending_of_recRel interpretation r S r.alice recBytes g ms₀
    hreclen hpend_rec (hrel₀.1 r.alice recBytes hrec).2.2
  have hpend₁ : PureAliceInitPending interpretation r S g (ms₀ ++ pre) recBytes :=
    XplQuiet.quiet_pureAliceInitPending hq1 hpend₀
  have hlen62 : recBytes.length < 2 ^ 62 := by rcases hcanon with ⟨_, _, _, _, _, h, _, _⟩; exact h
  obtain ⟨sess, sc, remote, items, kpk, st₀, stateIdx₀, ekIdx, ctIdx, ek, ct,
    hrc, hscope1, hscope2, hget, hcur, his_a, hpeer, hek, hct, hreg, hver, hpn, hlid, hrem, hrem_ser, hsc, hrk, hck, hidx,
    hppk, hts_z, hbk, hkpk, hct_ser, hpq, recR, hrecR, hrel, hks, hmk, hnd⟩ := hpend₁
  obtain ⟨rfl, rfl⟩ := isCurrentSnapshot_unique_of_role hrole₁ hst_m hget hcur_m hcur
  obtain ⟨hooo, _⟩ := ooo_of_pendingRecordCanon hcanon hrc
  have hrid : sess.state.remoteIdentity.isSome = true := by rw [hrem]; rfl
  obtain ⟨_, coins', hmid', _, hev⟩ :=
    hout.eval sess hrc hscope1 hscope2 hrid hlen62 hreclen hooo
  have hcoins_eq : coins = coins' := snd_coins_eq_of_mid hmid hmid'; subst hcoins_eq
  have hsend_some := TR.SendRetCoinsCliPure.pureEvalSendWire_some_send_isSome _ _ _ sess (some pqHarnessAddrBytes) pt coins (retState, retMessage) hev
  obtain ⟨⟨newPqState, salt?, pqMsgBytes⟩, hsend_spqr⟩ := Option.isSome_iff_exists.mp hsend_some
  obtain ⟨_, hexec⟩ := TR.SendRetCoinsCliPure.pureEvalSendWire_exec_pending
    (cryptoOf' interpretation) (interpW interpretation) (spqrModelOf interpretation)
    sess (some pqHarnessAddrBytes) pt coins (retState, retMessage) sc remote items kpk newPqState pqMsgBytes salt?
    hev hver hsc hrem hppk hkpk hsend_spqr
  rw [cryptoOf'_F] at hexec; injection hexec with hstate_eq hmsg_eq
  have hct_ser' : kpk.ciphertext = kyberKey (gamma interpretation S g ct) := hct_ser
  have hmsg_eq' : retMessage = wirePrekeyTag :: (PreKeySignalMessage.new 4#8 r.regIdA items.preKeyId
      items.signedPreKeyId (some ⟨kpk.preKeyId, kyberKey (gamma interpretation S g ct)⟩)
      items.baseKey sess.state.localIdentity
      (SignalMessage.new (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
        protoSignalCodec 4#8
        ((sc.chainKey.messageKeys (DY.Libsignal.Refinement.sha256CompressFunction interpretation)).generateKeys
          (DY.Libsignal.Refinement.sha256CompressFunction interpretation) salt?).macKey
        (some pqHarnessAddrBytes) sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter
        ((interpW interpretation).enc
          ((sc.chainKey.messageKeys (DY.Libsignal.Refinement.sha256CompressFunction interpretation)).generateKeys
            (DY.Libsignal.Refinement.sha256CompressFunction interpretation) salt?).cipherKey
          ((sc.chainKey.messageKeys (DY.Libsignal.Refinement.sha256CompressFunction interpretation)).generateKeys
            (DY.Libsignal.Refinement.sha256CompressFunction interpretation) salt?).iv pt)
        sess.state.localIdentity remote pqMsgBytes)).serialized := by
    rw [hmsg_eq, hreg, hct_ser']
  obtain ⟨body, hbody_eq⟩ := sentBody_pending_wire _ r.regIdA items.preKeyId items.signedPreKeyId
    kpk.preKeyId (gamma interpretation S g ct) items.baseKey sess.state.localIdentity remote _
    sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter _ pqMsgBytes (hmsg_eq' ▸ hout.msg_lt)
  rw [← hmsg_eq'] at hbody_eq
  have hbd_eq := snd_frame_bobDoneBaseKeys hpre hst_m hns_m hpost
  refine ⟨fun q b hqb => ?_, ⟨?_, ?_, ?_, ?_⟩,
    snd_cHist_step interpretation r S g ms₀ pre post r.alice stateIdx cLen _ wrap hpre hpost hrel₀.2.2.1,
    hrole_out⟩
  · dsimp only at hqb; by_cases hqa : q = r.alice
    · subst hqa; simp only [↓reduceIte, Option.some.injEq] at hqb; subst hqb
      set ts := (runTraceMoves r (ms₀ ++ pre)).length
      set F := DY.Libsignal.Refinement.sha256CompressFunction interpretation
      set nextCk : CryptoGames.LibsignalSession.ChainKey :=
        ⟨CryptoGames.HKDF.bytesToKey32
          (CryptoGames.Ratchet.chainHmac F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed),
          sc.chainKey.index + 1⟩
      set sc' : SenderChain := { sc with chainKey := nextCk }
      set sess' : Session (List (BitVec 8)) :=
        { sess with state := { sess.state with senderChain := some sc', pqRatchetState := newPqState } }
      obtain ⟨hrc', hscope1', hscope2'⟩ := recordCanonical_of_sendPending_step hrc hscope1 hscope2 hsc hwc hstate_eq
      have hsm_bytes : retState = recordBytes (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess') := by
        rw [hrc'.1, ← TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q hrc']
      refine ⟨Or.inl rfl, hsm_bytes ▸ snd_recordBytes_ne_nil _, Or.inl (Or.inr ⟨rfl, ?_⟩)⟩
      rw [hms_eq]; refine XplQuiet.quiet_pureAliceInitPending hq2 ?_
      have htr_enc : runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt r.alice stateIdx cLen (ts + 2) none]) =
          encTr (runTraceMoves r (ms₀ ++ pre)) r.alice stateIdx cLen st_m := by
        rw [TR.runTrace_snoc]; exact encrypt_next_of_some hst_m hns_m
      have hsend_gam : (spqrModelOf interpretation).send
          (gamma interpretation (compSemOf interpretation r) g st_m.spqr)
          (gamma interpretation (compSemOf interpretation r) g (randTerm (ts + 1) cLen)) =
          some (newPqState, salt?, pqMsgBytes) := by rw [← hSeq, ← hpq, hcoins_gam]; exact hsend_spqr
      obtain ⟨hspqr1, _, _⟩ := TR.SendRetCoinsCliPure.gamma_spqrSend_bridge interpretation hext.1 r g
        st_m.spqr (randTerm (ts + 1) cLen)
        (TR.SendRetCoinsCliPure.spqrInitA2B32_of_kdf interpretation (compSemOf interpretation r) g
          (TR.spqrInitA2BKdf_of_getLocalState hst_m)) hsend_gam
      have hspqr1_S : gamma interpretation S g (DY.Spqr.spqrSend st_m.spqr (randTerm (ts + 1) cLen)).1 = newPqState :=
        hSeq ▸ hspqr1
      have hstep : gamma interpretation S g (TripleRatchet.kdfCk st_m.cks).1 =
          CryptoGames.Ratchet.chainHmac F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed := by
        rw [TR.SendRetCoinsCliPure.gamma_kdfCk_fst_tr, ← hck]; rfl
      have hlen_cks' : (gamma interpretation S g (TripleRatchet.kdfCk st_m.cks).1).length = 32 := by
        rw [TR.SendRetCoinsCliPure.gamma_kdfCk_fst_tr]
        exact TR.length_hmacWith _ _ _
      have hck'_key : CryptoGames.HMAC.keyToBytes32 nextCk.key = gamma interpretation S g (TripleRatchet.kdfCk st_m.cks).1 := by
        dsimp only [nextCk]; rw [← hstep, TR.SendRetCoinsCliPure.keyToBytes32_bytesToKey32_c _ hlen_cks']
      obtain ⟨hnorm_eq, _, _⟩ := TR.SendRetCoinsCliPure.rec_eq_sessionToRecordRec_of_canonical_Q hrecR hrc
      have hrel_sess : TR.StateRel interpretation S g st_m (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec sess) := by
        rw [← TR.SendRetCoinsCliPure.stateRel_sessionToRecordRecPending_iff,
            ← TR.SendRetCoinsCliPure.stateRel_normPending_iff, ← hnorm_eq,
            TR.SendRetCoinsCliPure.stateRel_normPending_iff]
        exact hrel
      have hrel'_sess : TR.StateRel interpretation S g (TR.SendRetCoinsCliPure.encSt st_m cLen ts)
          (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec sess') :=
        TR.SendRetCoinsCliPure.stateRel_sessionToRecordRec_advance_TR interpretation S g st_m sess sc nextCk
          (TripleRatchet.kdfCk st_m.cks).1 (DY.Spqr.spqrSend st_m.spqr (randTerm (ts + 1) cLen)).1
          newPqState hrel_sess hsc (by dsimp only [nextCk]; rw [hidx]; rfl)
          hck'_key hspqr1_S.symm
      have hchains_eq : (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess').current.receiverChains = recR.current.receiverChains := by
        have h := congrArg (fun x => x.current.receiverChains) hnorm_eq
        dsimp only [TR.normPending, TR.normPendingS, TR.SendRetCoinsCliPure.sessionToRecordRecPending,
          Swarm.Phase0WholeFunctionBridge.sessionToSessionRec, sess'] at h ⊢
        exact h.symm
      refine ⟨sess', sc', remote, items, kpk, TR.SendRetCoinsCliPure.encSt st_m cLen ts, ts + 5, ekIdx, ctIdx, ek, ct,
        hrc', hscope1', hscope2', by rw [htr_enc, getLocalState_fst_encTr_new],
        by rw [htr_enc, isCurrentSnapshot_encTr_new], his_a, hpeer,
        by rw [htr_enc]; exact getMessageSentAt_encTr_of_some hek,
        by rw [htr_enc]; exact getMessageSentAt_encTr_of_some hct,
        hreg, hver, hpn, hlid, hrem, hrem_ser, rfl, hrk, hck'_key,
        by dsimp only [sc', nextCk, TR.SendRetCoinsCliPure.encSt]; rw [hidx]; rfl,
        hppk, hts_z, hbk, hkpk, hct_ser, hspqr1_S.symm, TR.SendRetCoinsCliPure.sessionToRecordRecPending sess', hsm_bytes,
        (TR.SendRetCoinsCliPure.stateRel_sessionToRecordRecPending_iff interpretation S g _ sess').mpr hrel'_sess,
        ⟨hks.dhs_len, hlen_cks', hks.myIk_ser, hks.peerIk_ser⟩, hchains_eq ▸ hmk, hchains_eq ▸ hnd⟩
    · simp only [hqa, ↓reduceIte] at hqb; obtain ⟨hq_ab, hb_ne, hrec_q⟩ := hrel₀.1 q b hqb
      exact ⟨hq_ab, hb_ne, ini_pureCRecRelH_mono (fun _ => snd_frame_other hpre hst_m hns_m hpost hqa) hrec_q⟩
  · have hsb_eq : TR.sentBodies (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) =
        TR.sentBodies acc ++ (sentBody retMessage).toList := by
      rcases hmid with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        (simp [TR.sentBodies, List.filterMap_append, List.filterMap_cons, List.filterMap_nil];
         cases sentBody retMessage <;> rfl)
    rw [hsb_eq, hrel₀.2.1.1]
  · have hns₁ : TR.TRNsBound r (ms₀ ++ pre) sent := XplQuiet.quiet_trNsBound hq1 hrel₀.2.1.2.1
    rw [hbody_eq, hms_eq]
    exact XplQuiet.quiet_trNsBound hq2 (trNsBound_snoc_encrypt_wrap (wrap := none) body hns₁ hst_m hns_m)
  · rw [hbd_eq]; exact hrel₀.2.1.2.2.1
  · rw [hbd_eq]; exact hrel₀.2.1.2.2.2

end Symbolic.Swarm.CREF.CliPure.SndPure
