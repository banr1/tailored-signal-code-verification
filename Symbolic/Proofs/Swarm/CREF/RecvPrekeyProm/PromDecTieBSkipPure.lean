/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure
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
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecSkipStepPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3ChainsWFPresPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3GlueSkOkPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.SkippedHit
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj
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
# Promote Record-State Tie for the Skipped-Key Branch

Proves `prom_tieB_skip_leaf`, re-establishing `PureTRRecordStateInv` and `TRNsBound` when an
accepting promote call in the `PromDecSelSkipped` branch is explained by a model
`Move.decryptSkipped` of Bob.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec receiverChainToChainRec)
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

private theorem promSkip_flatten_lenField_ge {α : Type} (tag : Nat) (f : α → HwBytes)
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten.length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem promSkip_encSession_length_le (s : Session HwBytes) :
    (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord
    CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  simp only [Option.map_some, List.length_append]
  omega

private theorem promSkip_encReceiverChain_length_le (s : Session HwBytes)
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := promSkip_flatten_lenField_ge 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession
  simp only [List.length_append]
  omega

private theorem promSkip_seed_length_le_encReceiverChain (rc : ReceiverChain)
    (mk : MessageKeyGenerator) (hmk : mk ∈ rc.messageKeys) :
    mk.seed.length ≤ (CryptoVerification.E2E.Record.encReceiverChain rc).length := by
  have h1 := promSkip_flatten_lenField_ge 4 CryptoVerification.E2E.Record.encMessageKey
    rc.messageKeys mk hmk
  have h2 : mk.seed.length ≤ (CryptoVerification.E2E.Record.encMessageKey mk).length := by
    unfold CryptoVerification.E2E.Record.encMessageKey
      CryptoVerification.E2E.Record.bytesField
      CryptoVerification.E2E.Record.lenField
    split <;> simp_all only [List.length_nil, List.length_append] <;> omega
  unfold CryptoVerification.E2E.Record.encReceiverChain
  simp only [List.length_append]
  omega

theorem recordBytes_of_promAcceptOut'
    {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {rec b : HwBytes} {mid : List MachineEvent} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt) :
    recordBytes (TR.RecvDecStep.sessionToRecordRecPending sess') = sm.state := by
  obtain ⟨_, _, ⟨_, _, _, halice_in, _, _, _⟩⟩ := hOut.hcan_in
  obtain ⟨sess₁, hrc₁, -, -, -, h62, -⟩ := hOut.hwrc
  obtain ⟨hrc₁_bytes, _, ⟨_, _, _, _, _, hpq₁, _⟩⟩ := hrc₁
  have hpq_eq : sess₁.state.pqRatchetState = sess'.state.pqRatchetState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁_bytes hOut.hstate h62
  have hsess'_len : (CryptoVerification.E2E.Record.encSession sess').length < 2 ^ 62 := by
    have hle := promSkip_encSession_length_le sess'
    rw [← hOut.hstate] at hle
    omega
  rw [hOut.hstate]
  exact recordBytes_sessionToRecordRecPending_eq_encodeRecord sess'
    (by rw [hOut.halice]; omega)
    (by rw [← hpq_eq]; omega)
    (fun rc hrc mk hmk => Nat.lt_of_le_of_lt
      (Nat.le_trans (promSkip_seed_length_le_encReceiverChain rc mk hmk)
        (promSkip_encReceiverChain_length_le sess' rc hrc))
      (by omega))
    (fun rc hrc => Nat.lt_of_le_of_lt (promSkip_encReceiverChain_length_le sess' rc hrc) (by omega))
    (by omega)

/-- Re-establishes `PureTRRecordStateInv` and `TRNsBound` for the `PromDecSelSkipped` branch
against a model `Move.decryptSkipped` of Bob. -/
theorem prom_tieB_skip_leaf
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation) (hceh : ExternCryptoLawsHold interpretation)
    (hwf : ProtocolSetupWF r) (hik : IkShape interpretation r) (hS : S = compSemOf interpretation r)
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hsel : PromDecSelSkipped sess pf.inner mid coins)
    (g : Ghost) (ms₀ pre post : List Move)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ .decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r (ms₀ ++ pre))
        (.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r S g (ms₀ ++ pre) pf.message
      (.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre)
      (fun q => if q = r.bob then some rec else none))
    (hns : TRNsBound r (ms₀ ++ pre) e'.sent)
    (hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r S g (ms₀ ++ pre))
    (habs : G1.G1cAttackerBuiltSeedExcl' interpretation r S g (ms₀ ++ pre)) :
    PureTRRecordStateInv interpretation r S (pureTrSlots r) g
        (ms₀ ++ pre ++ [.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = r.bob then some sm.state else none) ∧
      TRNsBound r
        (ms₀ ++ pre ++ [.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        e'.sent := by
  let ms := ms₀ ++ pre
  have hacc : ∃ e ∈ promAccBlk b mid pt, eventKind e = .accept := prom_accBlk_has_accept b mid pt
  have hmatch := a2b_block_vis hB hpre hpost
  have hacc_vis : ∃ v ∈ (Move.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis
      (runTraceMoves r ms), v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  obtain ⟨st, t, msg, seed, rIdx, srcIdx, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver,
      hsk, hunused, hspqr, hpqSalt, hmac_eq, hdec, _hpt, hfind⟩ :=
    skippedHit_of_decryptSkipped hacc_vis
  have hrep : t ∈ recvRepresentations interpretation r S g ms pf.message := hcurR.2 t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrr r.bob rec (by simp only [↓reduceIte])
  have hidx : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  have hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess := hC.out.hcan_in
  have hnorm_eq : normPending rec₀ = normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq,
      stateRel_normPending_iff]; exact hrel₀
  have hsk_pre_sess : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains,
      ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo r.bob) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB (runTraceMoves r ms) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r ms) (st.sessionInfo r.bob) seed (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st.toDRState.recv pk).isSome = true :=
    hrc_rec₀ ▸ hsk_pre₀
  have hnd_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  have hnodup_rc : (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey =
        (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map PublicKey.serialize := by
      dsimp only [g_rw, sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd_sess.1)
  have hMksNodup : ∀ ch ∈ sess.state.receiverChains,
      (ch.messageKeys.map MessageKeyGenerator.counter).Nodup := by
    intro ch hch
    have hmem_map : receiverChainToChainRec ch ∈ (sessionToRecordRec g_rw.sess).current.receiverChains := by
      dsimp only [g_rw, sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hch
    have hnd_mk := hnd_sess.2.1 (receiverChainToChainRec ch) hmem_map
    have hmap_mk : (receiverChainToChainRec ch).messageKeys.map Prod.fst =
        ch.messageKeys.map MessageKeyGenerator.counter := by
      dsimp only [receiverChainToChainRec]; rw [List.map_map]; rfl
    rwa [hmap_mk] at hnd_mk
  obtain ⟨_remIk, _ck, r2, _mkGen, newPqrState, pqrKey, st',
      _hmid_nil, _hcoins_zero, _hRem, _hFind, _hLt, hTake,
      hrecv_spqr, _hMac, _hDec, hSt', hsess'_st, _hsm_st⟩ :=
    prom_adapter_skipped_out hC.out hnodup_rc hsel
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  obtain ⟨_, _, hpq_sess, _, _, _hver_sess, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st st g_rw hrecBytes₀
      hrel₀ hcanon_q rfl
  have hspqr'_eq : spqr' =
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack :=
    DY.Spqr.spqrRecv_state _ _ _ _ hspqr
  have hspqr'_gam : gamma interpretation S g spqr' = newPqrState := by
    rw [hspqr'_eq]
    exact (spqrRecv_step_gamma_state_and_key interpretation hceh r S hS g ms pf.message st g_rw t msg pf.inner
      newPqrState pqrKey hpq_sess hrep hparse htry hrecv_spqr).1
  let s' : Session (List (BitVec 8)) :=
    { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hnew : sm.state = recordBytes (TR.RecvDecStep.sessionToRecordRecPending sess') :=
    (recordBytes_of_promAcceptOut' hC.out).symm
  have hrel'_s' : StateRel interpretation S g { st with spqr := spqr' } (sessionToRecordRec s') := by
    dsimp only [s']; rw [hSt']
    exact (stateRel_of_takeSkippedKey_tr_g1 interpretation S g hrel_sess hTake hspqr'_gam).2
  have hrel' : StateRel interpretation S g { st with spqr := spqr' } (TR.RecvDecStep.sessionToRecordRecPending sess') := by
    rw [stateRel_sessionToRecordRecPending_iff]
    dsimp only [StateRel, sessionToRecordRec, sessionToSessionRec] at hrel'_s' ⊢
    dsimp only [s'] at hrel'_s'
    rwa [hsess'_st]
  have hnd'_s' : RecordChainsWF3 (sessionToRecordRec s') := by
    have := nodup_and_lt_of_takeSkippedKey_tr_g1 (newPqrState := newPqrState) hTake hnd_sess
    dsimp only [s']; rwa [← hSt'] at this
  have hrc_pend : (TR.RecvDecStep.sessionToRecordRecPending sess').current.receiverChains =
      (sessionToRecordRec s').current.receiverChains := by
    dsimp only [TR.RecvDecStep.sessionToRecordRecPending, sessionToRecordRec, sessionToSessionRec, s']
    rw [hsess'_st]
  have hnd' : RecordChainsWF3 (TR.RecvDecStep.sessionToRecordRecPending sess') :=
    ⟨hrc_pend ▸ hnd'_s'.1, hrc_pend ▸ hnd'_s'.2.1, hrc_pend ▸ hnd'_s'.2.2⟩
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld pf.inner htry
  have hctr_eq : UInt32.ofBitVec pf.inner.counter = msg.counter := UInt32.ext hctr_m.symm
  have hRIdxFun : TRSkippedRIdxFun (runTraceMoves r ms) (st.sessionInfo r.bob) :=
    (hat.fresh r.bob stateIdx st hp_mem hst₀ hcur₀).2.1
  have htr := a2b_runTrace_decryptSkipped (msgIdx := msgIdx) (wrapped := wrapped) hst₀ hmsg hparse
    hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind
  have hsk'' : ∀ c_k ∈ (TR.RecvDecStep.sessionToRecordRecPending sess').current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk_k rIdx_k srcIdx_k skIdx_k seed_k,
        (runTraceMoves r (ms ++ [.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo r.bob) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k)
          skIdx_k ∧
        !skippedKeyUsedB
          (runTraceMoves r (ms ++ [.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])) skIdx_k ∧
        !receiverKeyUsedB
          (runTraceMoves r (ms ++ [.decryptSkipped r.bob stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped]))
          (st.sessionInfo r.bob) seed_k (UInt32.ofBitVec k.1) rIdx_k ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain st.toDRState.recv pk_k).isSome = true := by
    intro c_k hc_k k hk
    rw [hrc_pend] at hc_k
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
  exact ⟨a2b_trRecordStateInv_decSkipped_single hp_mem htr hnew hrel' hsk''
      hC.out.hcanon_out hks₀ hnd',
    a2b_trNsBound_decSkipped hns hst₀ htr⟩

end Symbolic.Swarm.CREF.CliPure
