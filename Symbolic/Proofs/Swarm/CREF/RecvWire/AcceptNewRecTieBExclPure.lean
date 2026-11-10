/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SkippedSeedLineage
import Batteries.Data.UInt
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import Symbolic.Proofs.Swarm.CREF.Xpl.SkippedHit
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Whisper Decrypt Branch-Mismatch Exclusions

Rules out mismatched pairs of implementation receive branches and symbolic decrypt moves:
cached-skipped-key evaluation against a no-RNG `Move.decrypt`, existing-chain evaluation against
`Move.decryptSkipped` (given `A2bSkStepSeedEq`), and DH-ratchet evaluation against
`Move.decryptSkipped`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain consumeMessageKey computeMac
  messageVersion)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR

/-- Extracts the model receiver chain at `ci` matching the session's receiver chain under `StateRel`. -/
theorem a2b_modelChain_of_binChain {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {s : Session (List (BitVec 8))} {ci : Nat} {rc : ReceiverChain} {ck : ChainKey}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hrc : s.state.receiverChains[ci]? = some rc) (hck : rc.chainKey = some ck) :
    ∃ c₀ : RecvChain, st.recv[ci]? = some c₀ ∧ c₀.index.toBitVec = ck.index ∧
      gamma interpretation S g c₀.ratchetKey = rc.senderRatchetKey.bytes.toList := by
  have h := congrArg (fun l => l[ci]?) (receiverChains_of_stateRel_tr hrel)
  simp only [List.getElem?_map, hrc, Option.map_some, sessionOf] at h
  cases hc : st.recv[ci]? with
  | none => rw [hc] at h; simp at h
  | some c₀ =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨c₀, rfl, ?_, ?_⟩
    · have hk := congrArg ChainRec.chainKey h
      simp only [recChainOfErased, eraseRecvChain, hck, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hk
      exact hk.1.symm
    · have hk := congrArg ChainRec.senderRatchetKey h
      simp only [recChainOfErased, eraseRecvChain, PublicKey.serialize,
        Symbolic.Swarm.CREF.TR.serializedKey, ecKey, djbType] at hk
      injection hk with _ hbytes
      exact hbytes.symm

/-- The cached-skipped-key evaluation branch (`m.counter < ck.index`) excludes a no-RNG accepting
`Move.decrypt` in the block. -/
theorem a2b_not_decrypt_of_binSkip
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc blk : List MachineEvent)
    (p : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body : HwBytes)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hno_rng : ∀ e ∈ blk, eventKind e ≠ .rng) (hacc : ∃ e ∈ blk, eventKind e = .accept)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g (ms₀ ++ pre)
      (fun q => if q = p then some rec else none))
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (g_rw : RecvWireGhost) (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hskip_idx : m.counter < ck.index) : False := by
  have hmatch := a2b_block_vis hB hpre hpost
  obtain ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver, _hrcf,
      hfind, hidx, _hcons, _hspqr, _hpqSalt, _hmac_eq, _hdec, _hpt⟩ :=
    noRatchet_of_matched hmatch hno_rng hacc
  have hrep : t ∈ recvRepresentations interpretation r₀ S g (ms₀ ++ pre) body := hcurR.2 t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, _hks₀,
      hnd₀⟩ := hrr p rec (by simp)
  have hidx₀ : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx₀
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff]
    rw [← hnorm_eq, stateRel_normPending_iff]; exact hrel₀
  have hnd1 : ((sessionToRecordRec g_rw.sess).current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup := hrc_rec₀ ▸ hnd₀.1
  obtain ⟨c₀, hc₀, hidx_eq, hrk₀⟩ := a2b_modelChain_of_binChain hrel_sess hrc hck
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld m htry
  have hfind' := hfind
  unfold findRecvChain at hfind'
  have hc_mem : c ∈ st.recv := List.mem_of_find?_eq_some hfind'
  have hc_rk : c.ratchetKey = msg.ratchetKey := by simpa using List.find?_some hfind'
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc₀
  have hcc : c₀ = c :=
    a2b_recvChain_eq_of_gamma hrel_sess hnd1 hc₀_mem hc_mem
      (by rw [hrk₀, hrc_key, hc_rk, hrk_m])
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hlt : msg.counter < c.index := by
    rw [← hctr_eq, ← hcc]; show m.counter < c₀.index.toBitVec; rw [hidx_eq]; exact hskip_idx
  exact UInt32.not_lt.mpr hidx hlt

/-- An accepting `Move.decryptSkipped` emits no `.rng` event, excluding any block with `.rng`. -/
theorem a2b_not_decryptSkipped_of_rng
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc blk : List MachineEvent)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hacc : ∃ e ∈ blk, eventKind e = .accept) (hrng : ∃ e ∈ blk, eventKind e = .rng) : False := by
  have hmatch := a2b_block_vis hB hpre hpost
  have hacc_vis : ∃ v ∈ (Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis
      (runTraceMoves r₀ (ms₀ ++ pre)), v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  obtain ⟨st, t, msg, seed, rIdx, srcIdx, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver,
      hsk, hunused, hspqr, hpqSalt, hmac_eq, hdec, _hpt, hfind⟩ :=
    skippedHit_of_decryptSkipped hacc_vis
  have hnext := Symbolic.Swarm.CREF.TR.RecvDec.decryptSkipped_next_eq (wrapped := wrapped)
    hst hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind
  have hnr := Symbolic.Swarm.CREF.TR.RecvDec.newRandoms_decSkippedTr (runTraceMoves r₀ (ms₀ ++ pre)) p
    stateIdx skIdx rIdx srcIdx st msg.ratchetKey seed key pqSalt ptTerm spqr' msg.counter
  rw [← hnext] at hnr
  obtain ⟨e, he, hk⟩ := hrng
  obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
  have hvk : v.kind = .rng := hev.1.symm.trans hk
  rw [vis_decryptSkipped rfl, List.mem_append] at hv
  rcases hv with hv | hv
  · exact (newRandoms_eq_nil_iff_no_rng_decVis _ _ stateIdx msgIdx wrapped).mpr hnr v hv hvk
  · rw [exposures_kind_eq_leak hv] at hvk; cases hvk

/-- Seed-equality obligation between a cached skipped seed `seed_s` read by `Move.decryptSkipped`
and the existing receiver chain's consumed seed at `msg.counter`. -/
def A2bSkStepSeedEq (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (acc : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx : Nat) (st : TRState) (c : RecvChain) (t : DY.Bytes)
    (msg : TRSignalMsg) (skIdx rIdx_s srcIdx : Nat) (seed_s pqSalt : DY.Bytes) (body : HwBytes)
    (r : StateAndMessage) (g_rw : RecvWireGhost) (m : SignalMessage) (ci : Nat)
    (rc : ReceiverChain) (ck : ChainKey),
    ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 =
      some st →
    isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true →
    StateRel interpretation S g st (sessionToRecordRec g_rw.sess) →
    st.recv[ci]? = some c →
    t ∈ recvRepresentations interpretation r₀ S g ms body →
    parseTrSignalMsg t = some msg →
    ¬ RecvCollision interpretation r₀ S g ms t →
    ((runTraceMoves r₀ ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩ →
    msg.mac = computeMac (trMsgKeys pqSalt seed_s).macKey st.peerIk st.myIk msg.wire →
    (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true →
    g_rw.wireBytes = wireWhisperTag :: body →
    SignalMessage.tryFrom protoSignalCodec body = .ok m →
    g_rw.sess.state.receiverChains[ci]? = some rc →
    rc.senderRatchetKey = m.senderRatchetKey → rc.chainKey = some ck → ck.index ≤ m.counter →
    TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 =
        some (r.state, r.message) →
    ∀ (newPqrState : HwBytes) (pqrKey : HKDF.Salt),
    msg.version = messageVersion →
    ((sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey).Nodup →
    g_rw.sess.state.pqRatchetState = gamma interpretation S g st.spqr →
    TRKeyShape interpretation S g st →
    (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey) →
    ∃ seed_c c', consumeMessageKey c msg.counter = some (seed_c, c') ∧ seed_s = seed_c

/-- The existing-chain step branch (`ck.index ≤ m.counter`) excludes an accepting
`Move.decryptSkipped` in the block. -/
theorem a2b_not_decryptSkipped_of_binStep
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc blk : List MachineEvent)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body : HwBytes)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hacc : ∃ e ∈ blk, eventKind e = .accept)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r₀ (ms₀ ++ pre))
        (.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r₀ S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped))
    (Z : PureTRSlots) (hrr : PureTRRecordStateInv interpretation r₀ S Z g (ms₀ ++ pre)
      (fun q => if q = p then some rec else none))
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g (ms₀ ++ pre))
    (hsklin : SkippedSeedNeChainSeed r₀ (ms₀ ++ pre))
    (hres : A2bSkStepSeedEq interpretation r₀ S g (ms₀ ++ pre) acc)
    (r : StateAndMessage) (g_rw : RecvWireGhost) (m : SignalMessage) (ci : Nat)
    (rc : ReceiverChain) (ck : ChainKey)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hstep_idx : ck.index ≤ m.counter)
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 =
        some (r.state, r.message))
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey)) : False := by
  have hmatch := a2b_block_vis hB hpre hpost
  have hacc_vis : ∃ v ∈ (Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis
      (runTraceMoves r₀ (ms₀ ++ pre)), v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  obtain ⟨st, t, msg, seed_s, rIdx_s, srcIdx, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver,
      hsk, _hunused, _hspqr, _hpqSalt, hmac_eq, _hdec, _hpt, hfind⟩ :=
    skippedHit_of_decryptSkipped hacc_vis
  have hrep : t ∈ recvRepresentations interpretation r₀ S g (ms₀ ++ pre) body := hcurR.2 t hmsg
  have hnc : ¬ RecvCollision interpretation r₀ S g (ms₀ ++ pre) t := hnocol t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀,
      hnd₀⟩ := hrr p rec (by simp)
  have hidx₀ : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx₀
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff]
    rw [← hnorm_eq, stateRel_normPending_iff]; exact hrel₀
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hnd_sess : ((sessionToRecordRec g_rw.sess).current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup := hrc_rec₀ ▸ hnd₀.1
  obtain ⟨_, _, hpq_sess, _, _, _, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interpretation S g rec rec₀ st st g_rw hrecBytes₀ hrel₀
      hcanon_q rfl
  obtain ⟨c₀, hc₀, hidx_eq, _hrk₀⟩ := a2b_modelChain_of_binChain hrel_sess hrc hck
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, _hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld m htry
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hle : c₀.index ≤ msg.counter := by
    rw [← hctr_eq]; show c₀.index.toBitVec ≤ m.counter; rw [hidx_eq]; exact hstep_idx
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc₀
  obtain ⟨seed_c, c', hcons, hseq⟩ :=
    hres p stateIdx st c₀ t msg skIdx rIdx_s srcIdx seed_s pqSalt body r g_rw m ci rc ck
      hst hcurR.1 hrel_sess hc₀ hrep hparse hnc hsk hmac_eq hfind hwire htry hrc hrc_key hck hstep_idx heval
      newPqrState pqrKey hver hnd_sess hpq_sess hks₀ hrecv_spqr
  have hr : rIdx_s = c₀.rIdx :=
    hsklin p stateIdx st c₀ msg.counter seed_c c' skIdx msg.ratchetKey msg.counter seed_s rIdx_s
      srcIdx hst hc₀_mem hcons hsk hseq
  have hlog : (runTraceMoves r₀ (ms₀ ++ pre)).EventLoggedAt
      (TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s c₀.rIdx srcIdx) skIdx := by
    rw [← hr, Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact hsk
  have hlt : msg.counter < c₀.index :=
    ((hat.fresh p stateIdx st hp_mem hst hcurR.1).1.1 c₀ hc₀_mem).2 _ _ _ _ _ hlog
  exact UInt32.not_lt.mpr hle hlt

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
