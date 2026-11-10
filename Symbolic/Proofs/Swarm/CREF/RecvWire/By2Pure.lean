/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieSeedShapePure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptSplitPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPureA
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedKeyRunInvPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.A2bSameOriginPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieDispatchPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieSeedEqCliPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.HistStepPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvTiePure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkPairUniq
import Symbolic.Proofs.Swarm.CREF.TR.G1.SkippedPkLineage
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineLink
import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.Xpl.RatchetHit
import Symbolic.Proofs.Swarm.TRREF.HooksOKXTRPure

/-!
# Per-Move `SkippedInstallByteFresh` and Seed-Exclusion Dischargers for Whisper Receive

Proves `SkippedInstallByteFresh` preservation across whisper receive moves under
`PureRcvAcceptCall`, along with `RcvCurrentRead`, `A2bCrossSeedExcl`, and `A2bSeedShapeEqRes`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure hiding StEntry TREntry

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames.LibsignalSession (SignalMessage PublicKey)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG.R3 (ratchetStateOf)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

private theorem pureDrawsCoins_cases (C)
    (st : CryptoGames.LibsignalSession.SessionState (List (BitVec 8)))
    (their : CryptoGames.LibsignalSession.PublicKey)
    (h : TR.PureRecvEval.pureDrawsCoins C st their = true) :
    CryptoGames.LibsignalSession.RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter,
          CryptoGames.LibsignalSession.maxForwardJumps⟩ their = .ok none ∧
      ∃ sc r, st.senderChain = some sc ∧
        CryptoGames.LibsignalSession.rootCreateChain C st.rootKey their sc.ratchetKey.privateKey = .ok r := by
  unfold TR.PureRecvEval.pureDrawsCoins at h
  rw [Bool.and_eq_true] at h; obtain ⟨_, h⟩ := h
  split at h
  · rename_i hf; refine ⟨hf, ?_⟩
    split at h
    · rename_i sc hsc
      split at h
      · rename_i r hr; exact ⟨sc, r, hsc, hr⟩
      · cases h
    · cases h
  · cases h

private theorem a2b_not_lt_of_current' {tr : ExecTrace} {p : Participant} {a b : Nat}
    {sa sb : TRState}
    (ha : (tr.at? a : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = some ⟨⟨p, sa⟩⟩)
    (hb : (tr.at? b : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = some ⟨⟨p, sb⟩⟩)
    (hca : isCurrentSnapshot tr a = true) (hinit : sa.initiator = sb.initiator) : ¬ a < b := by
  intro hlt
  have hblt : b < tr.length := by
    by_contra hge
    have hnone : (tr.at? b : Option (PersistentGlobalState.State.ExecEntryT
        (PersistentLocalState.LocalState TRState))) = none := by
      simp only [Trace.at?, hge, ↓reduceDIte]
    rw [hnone] at hb; cases hb
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hca
  rw [ha] at hca
  have hmem : b ∈ List.range' (a + 1) (tr.length - (a + 1)) :=
    List.mem_range'_1.mpr ⟨by omega, by omega⟩
  have hall := List.all_eq_true.mp hca b hmem
  rw [hb] at hall
  simp [hinit] at hall

private theorem a2b_currentSnapshot_unique_of_role {r : ProtocolSetup} {tr : ExecTrace} {p : Participant}
    {i j : Nat} {st₁ st₂ : TRState} (hrole : RoleSnapshots r tr)
    (h₁ : ((PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st₁)
    (h₂ : ((PersistentLocalState.getLocalState p j : Traceful TRState).run tr).1 = some st₂)
    (hc₁ : isCurrentSnapshot tr i = true) (hc₂ : isCurrentSnapshot tr j = true) : i = j := by
  have ha₁ := FreshSigma.at?_eq_some_of_getLocalState_some h₁
  have ha₂ := FreshSigma.at?_eq_some_of_getLocalState_some h₂
  have hinit : st₁.initiator = st₂.initiator :=
    (hrole p st₁ i ha₁).trans (hrole p st₂ j ha₂).symm
  rcases lt_trichotomy i j with h | h | h
  · exact absurd h (a2b_not_lt_of_current' ha₁ ha₂ hc₁ hinit)
  · exact h
  · exact absurd h (a2b_not_lt_of_current' ha₂ ha₁ hc₂ hinit.symm)

private theorem a2b_invisible_vis_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, a2b_invisible_vis_nil δ (m.next tr) hδ, List.nil_append]

private theorem a2b_block_vis {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
  have hm := hB.matched
  rw [b5_runMoves_append_snd, a2b_invisible_vis_nil pre _ hpre, List.nil_append,
    runMoves_cons_snd, a2b_invisible_vis_nil post _ hpost, List.append_nil] at hm
  rwa [TR.runTrace_append]

variable (interpretation : ExternInterpretation)

set_option maxHeartbeats 400000 in
/-- DH-ratchet (`mid = [.rng rngBytes]`) `Move.decrypt` step under `PureRcvAcceptCall` preserves
`SkippedInstallByteFresh`. -/
theorem rcv_skippedInstallByteFresh_decrypt_ratchet₂
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant} {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc : List MachineEvent} {rec body rngBytes : HwBytes} {sm : StateAndMessage}
    {g : Ghost} {ms₀ pre post : List Move}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hC : PureRcvAcceptCall interpretation r₀ S who ok j p records sent accepted opkUsed acc [.rng rngBytes] rec body sm)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (rcvAccBlk body [.rng rngBytes] sm))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureCRecRel interpretation r₀ S g (ms₀ ++ pre) p rec)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hBF : TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre)) :
    TR.SkippedInstallByteFresh interpretation S g r₀
      (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) := by
  let ms := ms₀ ++ pre
  have hmatch := a2b_block_vis hB hpre hpost
  have hrng_blk : .rng rngBytes ∈ rcvAccBlk body [.rng rngBytes] sm := by simp [rcvAccBlk]
  have hacc_blk : ∃ e ∈ rcvAccBlk body [.rng rngBytes] sm, eventKind e = VisEventKind.accept :=
    ⟨.accept sm.message, by simp [rcvAccBlk], rfl⟩
  obtain ⟨_hRng, st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
      hst, hmsg, hparse, hver, hfind, hlow, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    ratchet_of_matched hmatch hrng_blk hacc_blk
  obtain ⟨g_rw, coins, _, hwire, hcanon_q, hmid_cases, _, heval_u⟩ := hC.heval
  have htry_ex : ∃ m_bin, SignalMessage.tryFrom protoSignalCodec body = .ok m_bin := by
    unfold TR.PureRecvEval.pureEvalRecvWireWithCoinsW at heval_u
    rw [hwire] at heval_u
    change (match SignalMessage.tryFrom protoSignalCodec body with
      | .error _ => none | .ok msg => _) = some (sm.state, sm.message) at heval_u
    rcases htry : SignalMessage.tryFrom protoSignalCodec body with _ | m_bin
    · rw [htry] at heval_u; cases heval_u
    · exact ⟨m_bin, rfl⟩
  obtain ⟨m_bin, htry⟩ := htry_ex
  have hdraws : TR.PureRecvEval.pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state m_bin.senderRatchetKey = true := by
    rcases hmid_cases with ⟨_, hmid, _⟩ | ⟨_, _, _, _, hdr⟩
    · nomatch hmid
    · exact hdr m_bin htry
  obtain ⟨hfind_bin, _⟩ := pureDrawsCoins_cases _ _ _ hdraws
  have hci : (ratchetStateOf g_rw.sess.state).findReceiverChainIndex m_bin.senderRatchetKey = none :=
    Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_none
      (ratchetStateOf g_rw.sess.state) m_bin.senderRatchetKey hfind_bin
  have hrc_none : ∀ rc ∈ g_rw.sess.state.receiverChains, rc.senderRatchetKey ≠ m_bin.senderRatchetKey := by
    intro rc hMem hEq
    unfold CryptoGames.LibsignalSession.RatchetState.findReceiverChainIndex at hci
    rw [List.findIdx?_eq_none_iff] at hci; have hFalse := hci rc hMem; simp [hEq] at hFalse
  have hrr_inv : ∃ rec₀ st₀ stateIdx₀,
      rec = recordBytes rec₀ ∧
      ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms)).1 = some st₀ ∧
      isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx₀ = true ∧ TR.StateRel interpretation S g st₀ rec₀ := by
    rcases hrr with hrsi | ⟨hp, hpend⟩
    · obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _⟩ := hrsi p rec (by simp)
      exact ⟨rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀⟩
    · subst hp
      obtain ⟨_sess, _sc, _remote, _items, _kpk, st₀, stateIdx₀, _ekIdx, _ctIdx, _ek, _ct,
        _hcanon_q, _hscopeP, _hscopeQ, hst₀, hcur₀, _hinit, _hpeer, _hek, _hct,
        _hreg, _hver, _hpn, _hmyIk, _hrem, _hpeerIk, _hsc, _hrk, _hck, _hidx,
        _hppk, _hts, _hbase, _hkpk, _hkyber, _hpq,
        rec₀, hrecBytes₀, hrel₀, _⟩ := hpend
      exact ⟨rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀⟩
  obtain ⟨rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀⟩ := hrr_inv
  have hidx : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx.symm
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq.symm
  have hnorm_eq : normPending rec₀ = normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrel_sess : TR.StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← TR.RecvDecStep.stateRel_sessionToRecordRecPending_iff, ← TR.RecvDecStep.stateRel_normPending_iff,
      ← hnorm_eq, TR.RecvDecStep.stateRel_normPending_iff]
    exact hrel₀
  have hrep : t ∈ recvRepresentations interpretation r₀ S g ms body := hcurR.2 t hmsg
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, _hctr_m, _hver_m⟩ := hfld m_bin htry
  have hTheir' : m_bin.senderRatchetKey.bytes.toList = gamma interpretation S g msg.ratchetKey := hrk_m.symm
  have hTheir : m_bin.senderRatchetKey = ⟨vec32 (gamma interpretation S g msg.ratchetKey)⟩ :=
    (Proofs.libsignal.RngG.CliPure.R3.publicKey_eq_vec32_of_toList_eq hTheir').1
  have hByteFresh_new : ∀ c_m ∈ st.recv,
      gamma interpretation S g c_m.ratchetKey ≠ gamma interpretation S g msg.ratchetKey := by
    intro c_m hc_m hγ_eq
    have hmap := RecvHistStep.map_senderRatchetKey_of_stateRel hrel_sess
    have hmem : serializedKey (gamma interpretation S g c_m.ratchetKey) ∈
        (sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey := by
      rw [hmap, List.map_map]
      exact List.mem_map_of_mem (f := serializedKey ∘ fun c : RecvChain =>
        gamma interpretation S g c.ratchetKey) hc_m
    dsimp only [sessionToRecordRec, Swarm.Phase0WholeFunctionBridge.sessionToSessionRec] at hmem
    rw [List.map_map] at hmem
    obtain ⟨rc, hrcMem, hSrk⟩ := List.mem_map.mp hmem
    have hSrk' : 5#8 :: rc.senderRatchetKey.bytes.toList =
        5#8 :: gamma interpretation S g c_m.ratchetKey := hSrk
    have htoList : rc.senderRatchetKey.bytes.toList =
        gamma interpretation S g msg.ratchetKey := by
      injection hSrk' with _ htl
      rwa [hγ_eq] at htl
    have hrc_eq : rc.senderRatchetKey = ⟨vec32 (gamma interpretation S g msg.ratchetKey)⟩ :=
      (Proofs.libsignal.RngG.CliPure.R3.publicKey_eq_vec32_of_toList_eq htoList).1
    exact hrc_none rc hrcMem (hrc_eq.trans hTheir.symm)
  let tr₀ := runTraceMoves r₀ ms
  let st1 := (RecvDec.trDhRatchetState st msg.ratchetKey tr₀.length).1
  let c_new := (RecvDec.trDhRatchetState st msg.ratchetKey tr₀.length).2
  let tr_pre := RecvDec.decRatchetPreTr tr₀ p st1 msg.ratchetKey key
  let T := RecvDec.decTailTr tr_pre p stateIdx st1 c_new c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter
  have htr : runTraceMoves r₀ (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) = T := by
    rw [runTrace_snoc]
    exact RecvDec.decrypt_next_ratchet_eq hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec
  have hle : tr₀ ≤ T :=
    DY.Trace.le_trans _ _ _ (le_decRatchetPreTr _ _ _ _ _) (le_decTailTr _ _ _ _ _ _ _ _ _ _ _ _)
  intro s pk n' seed' rIdx src i p₀ st_src c₀ hev hsrc hrcf
  rw [htr] at hev hsrc
  rcases eventLoggedAt_decTailTr_skippedKeyStored hev with hev_pre | ⟨hpk_eq, hsrc_eq⟩
  · have hev₀ : tr₀.EventLoggedAt (TREvent.SkippedKeyStored s pk n' seed' rIdx src) i :=
      eventLoggedAt_decRatchetPreTr_skippedKeyStored hev_pre
    have hlt_src : src < tr₀.length := RpkCli.Skr.skippedKeySrcLt_runTrace r₀ ms s pk n' seed' rIdx src i hev₀
    exact hBF s pk n' seed' rIdx src i p₀ st_src c₀ hev₀
      (trStateStoredAt_of_le_of_lt hle hlt_src hsrc) hrcf
  · cases hpk_eq; cases hsrc_eq.symm
    have hat₀ : TRStateStoredAt p st stateIdx tr₀ := FreshSigma.at?_eq_some_of_getLocalState_some hst
    have hlt_idx : stateIdx < tr₀.length := by
      have hlen := Trace.at?_eq_some_implies_length_le (EntryT := TieStEntry) tr₀ stateIdx
      change (tr₀.at? stateIdx : Option TieStEntry) = some _ at hat₀; rwa [hat₀] at hlen
    have hsrc₀ : TRStateStoredAt p₀ st_src stateIdx tr₀ := trStateStoredAt_of_le_of_lt hle hlt_idx hsrc
    have heq : (some ⟨⟨p, st⟩⟩ : Option TieStEntry) = some ⟨⟨p₀, st_src⟩⟩ := hat₀.symm.trans hsrc₀
    injection heq with h1; injection h1 with h2; injection h2 with _ hst_eq; subst hst_eq
    exact hByteFresh_new

/-- Combined per-move `SkippedInstallByteFresh` step under `PureRcvAcceptCall`. -/
theorem rcv_skippedInstallByteFresh_step₂
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant} {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {mid acc : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    (hC : PureRcvAcceptCall interpretation r₀ S who ok j p records sent accepted opkUsed acc mid rec body sm)
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc (rcvAccBlk body mid sm))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre) (hm : DecryptBy p m)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body m)
    (hrr : PureCRecRel interpretation r₀ S g (ms₀ ++ pre) p rec)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hBF : TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre)) :
    TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre ++ [m]) := by
  cases m with
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    exact RpkCli.Skr.skippedInstallByteFresh_decryptSkipped' interpretation S g r₀ (ms₀ ++ pre)
      me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped hBF
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    have hme : me = p := hm; subst hme
    rcases hC.hmid with rfl | ⟨rngBytes, _, rfl⟩
    · exact rcv_skippedInstallByteFresh_decrypt_noRatchet interpretation hB hpre hpost hBF
    · exact rcv_skippedInstallByteFresh_decrypt_ratchet₂ interpretation hC hB hpre hpost
        hcurR hrr hrole hBF
  | _ => nomatch hm

theorem rcv_accBlk_has_accept (body : HwBytes) (mid : List MachineEvent) (sm : StateAndMessage) :
    ∃ e ∈ rcvAccBlk body mid sm, eventKind e = .accept :=
  ⟨.accept sm.message,
   List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)),
   rfl⟩

/-- Under `CleanBy` on the extended trace, `RcvCurrentRead` holds at `ms₀ ++ pre`. -/
theorem rcv_currentRead_of_clean_pure {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc mid : List MachineEvent} {body : HwBytes} {sm : StateAndMessage}
    (hc : CleanBy interpretation r S who ok g (ms₀ ++ (pre ++ m :: post)) (acc ++ rcvAccBlk body mid sm))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (rcvAccBlk body mid sm))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    RcvCurrentRead interpretation r S g (ms₀ ++ pre) body m := by
  have hcur := TR.rcvCurrentSnapshot_of_xplBlock hB hpre hpost (rcv_accBlk_has_accept body mid sm)
  have hrep : ∀ t, rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t →
      t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) body :=
    fun t ht => rcv_rep_of_clean interpretation hc hB hpre hpost ht
  cases m <;> first | exact trivial | exact ⟨hcur, hrep⟩

/-- Discharges `A2bCrossSeedExcl` via `MacTagForgeryOrCollision`. -/
theorem rcv_hcross_pure {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {acc : List MachineEvent} :
    A2bCrossSeedExcl interpretation r S g ms acc := by
  intro t ⟨msg, hparse, hver, seed, hseed_mem, salt, st₀, hst₀_av, hfind₀, hmac_eq,
    st, hst_av, c, hc, seed', c', hγrk, hcons, hγ, k, hk, hmacγ⟩
  unfold skippedSeedsFor at hseed_mem
  obtain ⟨idx, _hidx_range, hidx_ev⟩ := List.mem_filterMap.mp hseed_mem
  cases hget : (runTraceMoves r ms).getEventAt DY.Libsignal.TripleRatchet.TREvent idx with
  | none => simp [hget] at hidx_ev
  | some ev =>
    rw [hget] at hidx_ev
    cases ev with
    | SkippedKeyStored s pk n seed₀ rIdx src =>
      dsimp only at hidx_ev
      split at hidx_ev
      · next hcond =>
        injection hidx_ev with hseed_eq; subst hseed_eq
        rcases hcond with ⟨rfl, rfl⟩
        have hev : (runTraceMoves r ms).EventLoggedAt
            (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s msg.ratchetKey msg.counter seed₀ rIdx src) idx := by
          rwa [DY.Trace.EventLoggedAt_eq_getEventAt]
        have hctx := Symbolic.Swarm.CREF.Stage1Trials.whisperTrials_mem_of_byteChain_some
          hver hst_av hc hγrk hcons
        have hctx₀ := Symbolic.Swarm.CREF.Stage1Trials.whisperTrials_mem_of_skippedKeyStored
          (interpretation := interpretation) (S := S) (g := g) hver hst₀_av hfind₀ hev rfl
        exact Symbolic.Swarm.CREF.Stage1Trials.RecvCollision.of_ownSaltMacCollision hparse
          (Symbolic.Swarm.CREF.Stage1Trials.MacTagForgeryOrCollision.of_crossSeedTerm_exact
            hctx rfl hk hmacγ hctx₀ rfl hγ hmac_eq)
      · cases hidx_ev
    | _ => cases hidx_ev

/-- Discharges `A2bSeedShapeEqRes` from `XplBlock` via `a2b_sameOrigin_seed_eq_core`. -/
theorem rcv_hshapeEq_pure {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre : List Move} {m : Move} {post : List Move}
    {acc mid : List MachineEvent} {body : HwBytes} {sm : StateAndMessage}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (rcvAccBlk body mid sm)) :
    A2bSeedShapeEqRes interpretation r S g (ms₀ ++ pre) acc := by
  have hrun_pre : ModelRun r (ms₀ ++ pre) := a2b_modelRun_pre hB
  intro p₀ stateIdx st c c' t msg skIdx rIdx_s srcIdx seed_s seed_c pqSalt body₀
    hst _hcur _hc_eq hfind _hrep _hparse _hver _hnc hsk _hmac_eq hcons _hγ hsh
  have hreach : TR.G1.ReachableTrace (runTraceMoves r (ms₀ ++ pre)) := hrun_pre.2.2.1.1
  obtain ⟨p₁, _, _, st₀, c₀, _, _, _,
    _, _, _, hc₀_rk, _hc₀_rIdx, hc₀_seed, _, _, hst₀, _hsinfo₀, hdisj⟩ :=
    TR.RecvDecStep.skippedPkLineage_of_reachable hreach skIdx (st.sessionInfo p₀) msg.ratchetKey
      msg.counter seed_s rIdx_s srcIdx hsk
  have hc₀_origin : c₀ ∈ st₀.recv ∨ c₀ = TR.G1.freshRecvChain st₀ msg.ratchetKey ∨
      (rIdx_s = 2 ∧ c₀.index = 0) :=
    hdisj.imp id (Or.imp id fun ⟨_, _, hr, hi⟩ => ⟨hr, hi⟩)
  exact (a2b_sameOrigin_seed_eq_core interpretation S g hreach
    (TR.G1.Spine.recvLinkStored_of_reachable hreach)
    (fun h₁ h₂ hd => (TR.G1.trStateStoredAt_rk_eq_of_dhs_eq hreach h₁ h₂ hd).1)
    hst hfind hcons hsk hsh hst₀ hc₀_rk hc₀_seed hc₀_origin).1

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
