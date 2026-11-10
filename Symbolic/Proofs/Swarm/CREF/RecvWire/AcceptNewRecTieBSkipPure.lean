/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
import Batteries.Data.UInt
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3ChainsWFPresPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3GlueSkOkPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecSkipStepPure
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Cached Skipped-Key Whisper Decrypt Tie Core

Proves `PureTRRecordStateInv` and `TRNsBound` preservation for a `Move.decryptSkipped` step when
`pureEvalRecvWireWithCoinsW` takes the cached-skipped-key branch.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SessionModel.AdvanceAndFrame (mem_set_or mem_of_mem_eraseIdx)
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (recordBytes_sessionToRecordRecPending_eq_encodeRecord_64
  encSession_length_le_encodeRecord pqRatchetState_length_le_encSession)

/-- Preserves `PureTRRecordStateInv` (singleton table at `p`) and `TRNsBound` across a
`Move.decryptSkipped` aligned with the cached-skipped-key branch of `pureEvalRecvWireWithCoinsW`. -/
theorem a2b_tieB_skip_core
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms : List Move) (records : Participant → Option HwBytes) (sent : List HwBytes)
    (hrsi : PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g ms records)
    (hns : TRNsBound r₀ ms sent) (hrole : RoleSnapshots r₀ (runTraceMoves r₀ ms))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g ms)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (st : TRState) (t : DY.Bytes) (msg : TRSignalMsg) (seed : DY.Bytes) (rIdx srcIdx : Nat)
    (spqr' key pqSalt ptTerm : DY.Bytes)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true)
    (hmsg : (runTraceMoves r₀ ms).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hsk : ((runTraceMoves r₀ ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB (runTraceMoves r₀ ms) skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true)
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
    (hskip_idx : m.counter < ck.index)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 =
        some (r.state, r.message)) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped]) sent := by
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrsi p recBytes hrec
  have hidx : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcur hcur₀
  cases hidx
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff]; change StateRel interpretation S g st (normPending (sessionToRecordRecPending g_rw.sess)); rw [← hnorm_eq, stateRel_normPending_iff]; exact hrel₀
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
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey =
        (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map PublicKey.serialize := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd_sess.1)
  have hMksNodup : ∀ ch ∈ g_rw.sess.state.receiverChains,
      (ch.messageKeys.map MessageKeyGenerator.counter).Nodup := by
    intro ch hch
    have hmem_map : receiverChainToChainRec ch ∈ (sessionToRecordRec g_rw.sess).current.receiverChains := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hch
    have hnd_mk := hnd_sess.2.1 (receiverChainToChainRec ch) hmem_map
    have hmap_mk : (receiverChainToChainRec ch).messageKeys.map Prod.fst =
        ch.messageKeys.map MessageKeyGenerator.counter := by
      dsimp only [receiverChainToChainRec]; rw [List.map_map]; rfl
    rwa [hmap_mk] at hnd_mk
  obtain ⟨_role, _remIk, r2, _mkGen, st', _hrole, _hVer, _hRem, hTake, _hMac, _hDec, hSt', hr_enc⟩ :=
    evalRecvWireWithCoinsW_skipped_inv_g1 interpretation body r g_rw m ci rc ck newPqrState pqrKey
      hwire htry hrc hrc_key hck hskip_idx hnodup_rc hrecv_spqr heval
  obtain ⟨_, _, hpq_sess, _, _, _hver_sess, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interpretation S g recBytes rec₀ st st g_rw hrecBytes₀
      hrel₀ hcanon_q rfl
  have hspqr'_eq : spqr' =
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack :=
    DY.Spqr.spqrRecv_state _ _ _ _ hspqr
  have hspqr'_gam : gamma interpretation S g spqr' = newPqrState := by
    rw [hspqr'_eq]
    exact (spqrRecv_step_gamma_state_and_key interpretation hceh r₀ S hS g ms body st g_rw t msg m
      newPqrState pqrKey hpq_sess hrep hparse htry hrecv_spqr).1
  let s' : Session (List (BitVec 8)) :=
    { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hnew : r.state = recordBytes (sessionToRecordRec s') := by
    obtain ⟨ci_t, ch_t, idx_t, _hci_t, hch_t, _hsrk_t, _hfind_t, _hmk_at_t, _hmk_ctr_t, _hmk_mem_t,
      hr2_t, _⟩ := takeSkippedKey_ok_some_inv hTake
    have hch_mem : ch_t ∈ g_rw.sess.state.receiverChains := List.mem_of_getElem? hch_t
    have hRcs' : s'.state.receiverChains = g_rw.sess.state.receiverChains.set ci_t
        { ch_t with messageKeys := ch_t.messageKeys.eraseIdx idx_t } := by
      dsimp only [s']; rw [hSt', hr2_t]; rfl
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
      rcases mem_set_or g_rw.sess.state.receiverChains ci_t
          { ch_t with messageKeys := ch_t.messageKeys.eraseIdx idx_t } rc' hrc' with rfl | hrc_old
      · exact hseeds ch_t hch_mem mk (mem_of_mem_eraseIdx ch_t.messageKeys idx_t mk hmk)
      · exact hseeds rc' hrc_old mk hmk
    have hpend : Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins.sessionToRecordRecPending s' =
        sessionToRecordRec s' := rfl
    rw [hr_enc, ← hpend, ← recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 s'
      (by dsimp only [s']; omega) hpq'_len hseeds' hsess'_len]
  have hrel' : StateRel interpretation S g { st with spqr := spqr' } (sessionToRecordRec s') := by
    dsimp only [s']; rw [hSt']
    exact (stateRel_of_takeSkippedKey_tr_g1 interpretation S g hrel_sess hTake hspqr'_gam).2
  have hnd' : RecordChainsWF3 (sessionToRecordRec s') := by
    have := nodup_and_lt_of_takeSkippedKey_tr_g1 (newPqrState := newPqrState) hTake hnd_sess
    dsimp only [s']; rwa [← hSt'] at this
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld m htry
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hRIdxFun : TRSkippedRIdxFun (runTraceMoves r₀ ms) (st.sessionInfo p) :=
    (hat.fresh p stateIdx st hp_mem hst₀ hcur₀).2.1
  have htr := a2b_runTrace_decryptSkipped (msgIdx := msgIdx) (wrapped := wrapped) hst₀ hmsg hparse
    hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind
  have hsk'' : ∀ c_k ∈ (sessionToRecordRec s').current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk_k rIdx_k srcIdx_k skIdx_k seed_k,
        (runTraceMoves r₀ (ms ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k)
          skIdx_k ∧
        !skippedKeyUsedB
          (runTraceMoves r₀ (ms ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])) skIdx_k ∧
        !receiverKeyUsedB
          (runTraceMoves r₀ (ms ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped]))
          (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain st.toDRState.recv pk_k).isSome = true := by
    intro c_k hc_k k hk
    have hRcs' : s'.state.receiverChains = r2.receiverChains := by dsimp only [s']; rw [hSt']
    obtain ⟨c_old, hc_old, hsrk_eq, hk_old, hNeOrSrk⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.takeSkippedKey_remaining_counter_ne_or_srk_ne
        hTake hRcs' hnodup_rc hMksNodup hc_k hk
    obtain ⟨pk_k, rIdx_k, srcIdx_k, skIdx_k, seed_k, hlog_k, hsu_k, hru_k, hgam_k, hpk_k, hfind_k⟩ :=
      hsk_pre_sess c_old hc_old k hk_old
    have hpk_k' : c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) :=
      hsrk_eq.symm.trans hpk_k
    have hne_triple : ¬ (seed = seed_k ∧ msg.counter = UInt32.ofBitVec k.1 ∧ rIdx = rIdx_k) := by
      rintro ⟨rfl, hctr_k, rfl⟩
      rcases hNeOrSrk with hCntNe | hSrkNe
      · exact hCntNe (hctr_k.symm.trans hctr_eq.symm)
      · have hpk_eq : msg.ratchetKey = pk_k :=
          hRIdxFun _ _ _ _ _ _ _ _ _ _ _ (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]) hlog_k
        apply hSrkNe
        rw [hpk_k, ← hpk_eq, hrk_m]; rfl
    rw [htr]
    exact ⟨pk_k, rIdx_k, srcIdx_k, skIdx_k, seed_k,
      a2b_hsk'_decSkipped hsk hlog_k hsu_k hru_k hgam_k hpk_k' hfind_k hne_triple⟩
  exact ⟨a2b_trRecordStateInv_decSkipped_single hp_mem htr hnew hrel' hsk'' hcanon' hks₀ hnd',
    a2b_trNsBound_decSkipped hns hst₀ htr⟩

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
