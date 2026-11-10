/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecStepPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepNoRatchetWAtHelpersPure
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Existing-Chain Whisper Decrypt Tie Core

Proves `PureTRRecordStateInv` and `TRNsBound` preservation for a no-ratchet `Move.decrypt` step
when `pureEvalRecvWireWithCoinsW` takes the existing-chain branch.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPureRcv.TRPure
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain setRecvChain consumeMessageKey chainKeyAt
  kdfCk computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SessionModel.AdvanceAndFrame (mem_set_or)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (recordBytes_sessionToRecordRecPending_eq_encodeRecord_64
  encSession_length_le_encodeRecord pqRatchetState_length_le_encSession)

/-- Preserves `PureTRRecordStateInv` (singleton table at `p`) and `TRNsBound` across a no-ratchet
`Move.decrypt` aligned with the existing-chain branch of `pureEvalRecvWireWithCoinsW`. -/
theorem a2b_tieA_core
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms : List Move) (records : Participant → Option HwBytes) (sent : List HwBytes)
    (hcompat : GhostAndSemMatchSetup interpretation r₀ S g) (hrun : ModelRun r₀ ms)
    (hrsi : PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g ms records)
    (hns : TRNsBound r₀ ms sent) (hrole : RoleSnapshots r₀ (runTraceMoves r₀ ms))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g ms)
    (p : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (st : TRState) (t : DY.Bytes) (msg : TRSignalMsg) (c c' : RecvChain)
    (seed spqr' key pqSalt ptTerm : DY.Bytes)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true)
    (hmsg : (runTraceMoves r₀ ms).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (recBytes body : HwBytes) (r : StateAndMessage) (g_rw : RecvWireGhost)
    (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hrec : records p = some recBytes)
    (hrep : t ∈ recvRepresentations interpretation r₀ S g ms body)
    (hstate_lt : r.state.length < 2 ^ 64)
    (hcanon' : r.state.length < 2 ^ 32 - 2 ^ 20 → (pureTrSlots r₀).canon p r.state)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hstep_idx : ck.index ≤ m.counter)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw
        (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins none) =
        some (r.state, r.message)) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) sent := by
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrsi p recBytes hrec
  have hidx : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcur hcur₀
  cases hidx
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff]
    change StateRel interpretation S g st (normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess))
    rw [← hnorm_eq, stateRel_normPending_iff]; exact hrel₀
  have hsk_pre_sess : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains,
      ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r₀ ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB (runTraceMoves r₀ ms) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r₀ ms) (st.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st.toDRState.recv pk).isSome = true :=
    hrc_rec₀ ▸ hsk_pre₀
  have hnd_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  have hnodup_rc : (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map
          ChainRec.senderRatchetKey =
        (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map
          PublicKey.serialize := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd_sess.1)
  obtain ⟨role, remIk, ck_adv, ck_next, r_adv, r2, mkGen, st',
      _hrole, hVer, hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hMac, hDec, hSt', hr_enc⟩ :=
    evalRecvWireWithCoinsW_noRatchet_inv interpretation body r g_rw m ci rc ck newPqrState pqrKey
      hwire htry hrc hrc_key hck hstep_idx hnodup_rc hrecv_spqr heval
  let s' : Session (List (BitVec 8)) :=
    { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hrel₀'_rec₀ : StateRel interpretation S g st rec₀ := hrel₀
  obtain ⟨_, _, hpq_sess, _, _, _hver_sess, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interpretation S g recBytes rec₀ st st g_rw hrecBytes₀
      hrel₀'_rec₀ hcanon_q rfl
  have hspqr'_eq : spqr' =
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack :=
    DY.Spqr.spqrRecv_state _ _ _ _ hspqr
  have hspqr'_gam : gamma interpretation S g spqr' = newPqrState := by
    rw [hspqr'_eq]
    exact (spqrRecv_step_gamma_state_and_key interpretation hceh r₀ S hS g ms body st g_rw t msg m
      newPqrState pqrKey hpq_sess hrep hparse htry hrecv_spqr).1
  have hst_avail : st ∈ availableStates r₀ (runTraceMoves r₀ ms) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r₀ ms
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  have hRkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.ratchetKey).length = 32 :=
    hat.lens st hst_avail
  have hst_rci : TrStateRkCkIk r₀ st := trStateRkCkIk_of_getLocalState hrun hst₀
  have hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst_rci.recv_ck_len interpretation S g hwf hcompat
  have hNodupSym : (st.recv.map RecvChain.ratchetKey).Nodup :=
    nodup_ratchetKey_of_stateRel_tr hrel_sess hnd_sess.1
  obtain ⟨ci₀, ch, c₀, mks', seed₀, c₀', hch0, hc0, _hfind₀, hsrk0, htheir, _hck, _hch_ck,
      hcons₀_bv, hSeedEq, hCntEq, _hc'_rk, _hc'_rIdx, hR2Eq, hRel_c, hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_existing_tr interpretation S g hrel_sess hNodupSym hCkLens
      hspqr'_gam hFind hNotLt hJump hAdv hNext hSet
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc0
  have hch_mem : ch ∈ g_rw.sess.state.receiverChains := List.mem_of_getElem? hch0
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, hver_m⟩ := hfld m htry
  have hγ_c₀_rk : gamma interpretation S g c₀.ratchetKey = m.senderRatchetKey.bytes.toList := by
    rw [htheir]; simp [vec32, hRkLens c₀ hc₀_mem]
  have hfind' := hfind
  unfold findRecvChain at hfind'
  have hc_mem : c ∈ st.recv := List.mem_of_find?_eq_some hfind'
  have hc_rk : c.ratchetKey = msg.ratchetKey := by simpa using List.find?_some hfind'
  have hcc : c₀ = c :=
    a2b_recvChain_eq_of_gamma hrel_sess hnd_sess.1 hc₀_mem hc_mem
      (by rw [hγ_c₀_rk, hc_rk, hrk_m])
  cases hcc
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hcons_eq : some (seed₀, c₀') = some (seed, c') :=
    hcons₀_bv.symm.trans (hctr_eq ▸ hcons)
  injection hcons_eq with hpair_eq; injection hpair_eq with hseed_eq hc'_eq
  cases hseed_eq; cases hc'_eq
  have hRcs' : s'.state.receiverChains = g_rw.sess.state.receiverChains.set ci₀
      { ch with chainKey := some ck_next, messageKeys := mks' } := by
    dsimp only [s']; rw [hSt', hR2Eq]; rfl
  have hnew : r.state = recordBytes (sessionToRecordRec s') := by
    have hst_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some s'⟩).length < 2 ^ 64 :=
      hr_enc ▸ hstate_lt
    have hsess'_len : (CryptoVerification.E2E.Record.encSession s').length < 2 ^ 64 :=
      lt_of_le_of_lt (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins.encSession_length_le_encodeRecord s') hst_lt
    have hpq'_len : s'.state.pqRatchetState.length < 2 ^ 64 :=
      lt_of_le_of_lt (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins.pqRatchetState_length_le_encSession s')
        hsess'_len
    obtain ⟨_, _, ⟨_, _, hchains_sc, halice_lt, _, _, _⟩⟩ := hcanon_q
    have hseeds : ∀ rc0 ∈ g_rw.sess.state.receiverChains, ∀ mk ∈ rc0.messageKeys,
        mk.seed.length < 2 ^ 63 := by
      intro rc0 hrc0 mk hmk; have h32 := (hchains_sc rc0 hrc0).2 mk hmk; omega
    have hseeds' : ∀ rc' ∈ s'.state.receiverChains, ∀ mk ∈ rc'.messageKeys,
        mk.seed.length < 2 ^ 63 := by
      intro rc' hrc' mk hmk; rw [hRcs'] at hrc'
      rcases mem_set_or g_rw.sess.state.receiverChains ci₀
          { ch with chainKey := some ck_next, messageKeys := mks' } rc' hrc' with rfl | hrc_old
      · exact (hMks' mk hmk).elim (hseeds ch hch_mem mk) fun ⟨_, _, _, _, _, _, hlen32⟩ => by omega
      · exact hseeds rc' hrc_old mk hmk
    have hpend : Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins.sessionToRecordRecPending s' =
        sessionToRecordRec s' := rfl
    rw [hr_enc, ← hpend, ← recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 s'
      (by dsimp only [s']; omega) hpq'_len hseeds' hsess'_len]
  have hrel' : StateRel interpretation S g
      { st with recv := setRecvChain st.recv c', spqr := spqr' } (sessionToRecordRec s') :=
    stateRel_of_decrypt_update_tr (by rw [hR2Eq]) (by rw [hR2Eq]) (by rw [hR2Eq])
      (by dsimp [s']; rw [hSt']) hRel_c
  have hγ_msg_rk : gamma interpretation S g msg.ratchetKey = m.senderRatchetKey.bytes.toList := hrk_m
  have hSub_c' : ∀ c_k ∈ (sessionToRecordRec s').current.receiverChains, ∀ k ∈ c_k.messageKeys,
      (∃ c_old ∈ (sessionToRecordRec g_rw.sess).current.receiverChains,
        c_old.senderRatchetKey = c_k.senderRatchetKey ∧ k ∈ c_old.messageKeys) ∨
      (c_k.senderRatchetKey = serializedKey (gamma interpretation S g msg.ratchetKey) ∧
        ∃ j < msg.counter.toNat - c.index.toNat,
          UInt32.ofBitVec k.1 = c.index + UInt32.ofNat j ∧ UInt32.ofBitVec k.1 ≠ msg.counter ∧
          k.2 = gamma interpretation S g (kdfCk (chainKeyAt c.chainKey j)).2) := by
    intro c_k hc_k k hk
    simp only [sessionToRecordRec, sessionToSessionRec, hRcs', List.mem_map] at hc_k
    rcases hc_k with ⟨rc', hrc', rfl⟩
    simp only [receiverChainToChainRec, List.mem_map] at hk; rcases hk with ⟨mk, hmk, rfl⟩
    rcases mem_set_or g_rw.sess.state.receiverChains ci₀
        { ch with chainKey := some ck_next, messageKeys := mks' } rc' hrc' with rfl | hrc_old
    · rcases hMks' mk hmk with hmk_old | ⟨j, hjLt, _, hjU32, hjNe, hjSeed, _⟩
      · left; exact ⟨receiverChainToChainRec ch,
          by simp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hch_mem,
          rfl, by simp only [receiverChainToChainRec, List.mem_map]; exact ⟨mk, hmk_old, rfl⟩⟩
      · right; refine ⟨?_, j, hctr_eq ▸ hjLt, hjU32, hctr_eq ▸ hjNe, hjSeed⟩
        show ch.senderRatchetKey.serialize = serializedKey (gamma interpretation S g msg.ratchetKey)
        rw [hsrk0, hγ_msg_rk]; rfl
    · left; exact ⟨receiverChainToChainRec rc',
        by simp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hrc_old,
        rfl, by simp only [receiverChainToChainRec, List.mem_map]; exact ⟨mk, hmk, rfl⟩⟩
  have hFresh : TRRecvCountersFresh (runTraceMoves r₀ ms) p st :=
    (hat.fresh p stateIdx st hp_mem hst₀ hcur₀).1
  have htr := a2b_runTrace_decrypt_noRatchet (wrapped := wrapped) hst₀ hmsg hparse hver hfind hcons
    hspqr hpqSalt hmac_eq hdec
  have hsk' := a2b_skippedOk_existing_decTail hrun.2.2.1.1 hFresh hc_mem hc_rk hcons htr hsk_pre_sess
    hSub_c'
  have hnd' : RecordChainsWF3 (sessionToRecordRec s') :=
    nodup_and_lt_of_existing_tr hFind hNotLt hAdv hNext hSet (by dsimp [s']; rw [hSt']) hnd_sess
  exact ⟨TR.PureRecvEval.pureTRRecordStateInv_decTail_single hp_mem htr hnew hrel' hsk' hcanon' hks₀ hnd',
    a2b_trNsBound_decTail hns hst₀ htr⟩

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
