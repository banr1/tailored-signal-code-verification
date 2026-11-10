/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedEqPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedShapePure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecStepPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieBExclPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetWAtHelpersPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTieBRatchetPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTieBSkipPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTiePureA
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet

/-!
# Promote Record-State Tie for the Existing-Chain Branch and Dispatcher

Proves `prom_tieA_leaf` for the existing-chain (`PromDecSelNoRatchet`) branch and dispatches all
binary-branch and model-move pairs in `prom_rcvDecTie_at`.
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
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain setRecvChain chainKeyAt kdfCk)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet
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
open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

section X2

variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
  {who : List Participant} {ok : Nat → Bool}
  {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
  {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
  {sess sess' : Session (List (BitVec 8))}
  {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}

/-- Re-establishes `PureTRRecordStateInv` and `TRNsBound` for the `PromDecSelNoRatchet` branch
against a model `Move.decrypt` of Bob. -/
theorem prom_tieA_leaf
    (hceh : ExternCryptoLawsHold interpretation)
    (hwf : ProtocolSetupWF r) (hS : S = compSemOf interpretation r)
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hsel : PromDecSelNoRatchet sess pf.inner mid coins)
    (g : Ghost) (ms₀ pre post : List Move) (sent : List HwBytes)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ .decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hcurR : RcvCurrentRead interpretation r S g (ms₀ ++ pre) pf.message
      (.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre)
      (fun q => if q = r.bob then some rec else none))
    (hns : TRNsBound r (ms₀ ++ pre) sent)
    (hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r S g (ms₀ ++ pre)) :
    PureTRRecordStateInv interpretation r S (pureTrSlots r) g
        (ms₀ ++ pre ++ [.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = r.bob then some sm.state else none) ∧
      TRNsBound r (ms₀ ++ pre ++ [.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        sent := by
  have hsel' := hsel
  obtain ⟨-, -, -, hmid, -, -, -, -, -⟩ := hsel'
  subst hmid
  have hmatch := a2b_block_vis hB hpre hpost
  obtain ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver, _hrcf,
      hfind, _hidx, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    noRatchet_of_matched hmatch (prom_accBlk_nil_no_rng' b pt) (prom_accBlk_has_accept b [] pt)
  have hreach : (runTraceMoves r (ms₀ ++ pre)).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have hrun : ModelRun r (ms₀ ++ pre) := by
    have h := hB.run
    rw [← List.append_assoc] at h
    exact modelRun_prefix_of_reachable h hreach
  have hcompat : GhostAndSemMatchSetup interpretation r S g := hB.pre.1
  have hrep : t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) pf.message := hcurR.2 t hmsg
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀, hks₀,
      hnd₀⟩ := hrr r.bob rec (by simp)
  have hidx : stateIdx = stateIdx₀ :=
    a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq := rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀ hC.out.hcan_in
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq,
      stateRel_normPending_iff]; exact hrel₀
  have hsk_pre_sess : ∀ c ∈ (sessionToRecordRec sess).current.receiverChains,
      ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r (ms₀ ++ pre)).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo r.bob) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx)
          skIdx ∧
        !skippedKeyUsedB (runTraceMoves r (ms₀ ++ pre)) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r (ms₀ ++ pre)) (st.sessionInfo r.bob) seed (UInt32.ofBitVec k.1)
          rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st.toDRState.recv pk).isSome = true :=
    hrc_rec₀ ▸ hsk_pre₀
  have hnd_sess : RecordChainsWF3 (sessionToRecordRec sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  have hnodup_rc : (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec sess).current.receiverChains.map
          ChainRec.senderRatchetKey =
        (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map
          PublicKey.serialize := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd_sess.1)
  obtain ⟨remIk, ck, ck_adv, ck_next, r_adv, r2, mkGen, newPqrState, pqrKey, st', _hmid, _hcoins,
      _hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, _hMkGen, hrecv_spqr, _hMac, _hDec, hSt',
      hsess', _hstate⟩ :=
    prom_adapter_noRatchet_out hC.out hnodup_rc hsel
  obtain ⟨_, _, hpq_sess, _, _, _hver_sess, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st st (promGhost rec sess)
      hrecBytes₀ hrel₀ hC.out.hcan_in rfl
  have hspqr'_eq : spqr' =
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack :=
    DY.Spqr.spqrRecv_state _ _ _ _ hspqr
  have hspqr'_gam : gamma interpretation S g spqr' = newPqrState := by
    rw [hspqr'_eq]
    exact (spqrRecv_step_gamma_state_and_key interpretation hceh r S hS g (ms₀ ++ pre) pf.message st
      (promGhost rec sess) t msg pf.inner newPqrState pqrKey hpq_sess hrep hparse htry
      hrecv_spqr).1
  have hst_avail : st ∈ availableStates r (runTraceMoves r (ms₀ ++ pre)) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r (ms₀ ++ pre)
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  have hRkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.ratchetKey).length = 32 :=
    hat.lens st hst_avail
  have hst_rci : TrStateRkCkIk r st := trStateRkCkIk_of_getLocalState hrun hst₀
  have hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst_rci.recv_ck_len interpretation S g hwf hcompat
  have hNodupSym : (st.recv.map RecvChain.ratchetKey).Nodup :=
    nodup_ratchetKey_of_stateRel_tr hrel_sess hnd_sess.1
  obtain ⟨ci₀, ch, c₀, mks', seed₀, c₀', hch0, hc0, _hfind₀, hsrk0, htheir, _hck, _hch_ck,
      hcons₀_bv, _hSeedEq, _hCntEq, _hc'_rk, _hc'_rIdx, hR2Eq, hRel_c, hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_existing_tr interpretation S g hrel_sess hNodupSym hCkLens
      hspqr'_gam hFind hNotLt hJump hAdv hNext hSet
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc0
  have hch_mem : ch ∈ sess.state.receiverChains := List.mem_of_getElem? hch0
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld pf.inner htry
  have hγ_c₀_rk : gamma interpretation S g c₀.ratchetKey = pf.inner.senderRatchetKey.bytes.toList := by
    rw [htheir]; simp [vec32, hRkLens c₀ hc₀_mem]
  have hfind' := hfind
  unfold findRecvChain at hfind'
  have hc_mem : c ∈ st.recv := List.mem_of_find?_eq_some hfind'
  have hc_rk : c.ratchetKey = msg.ratchetKey := by simpa using List.find?_some hfind'
  have hcc : c₀ = c :=
    a2b_recvChain_eq_of_gamma hrel_sess hnd_sess.1 hc₀_mem hc_mem
      (by rw [hγ_c₀_rk, hc_rk, hrk_m])
  cases hcc
  have hctr_eq : UInt32.ofBitVec pf.inner.counter = msg.counter := UInt32.ext hctr_m.symm
  have hcons_eq : some (seed₀, c₀') = some (seed, c') :=
    hcons₀_bv.symm.trans (hctr_eq ▸ hcons)
  injection hcons_eq with hpair_eq; injection hpair_eq with hseed_eq hc'_eq
  cases hseed_eq; cases hc'_eq
  have hRcs' : sess'.state.receiverChains = sess.state.receiverChains.set ci₀
      { ch with chainKey := some ck_next, messageKeys := mks' } := by
    rw [hsess', hSt', hR2Eq]; rfl
  have hnew := (recordBytes_of_promAcceptOut' hC.out).symm
  have hrel' : StateRel interpretation S g
      { st with recv := setRecvChain st.recv c', spqr := spqr' } (sessionToRecordRec sess') :=
    stateRel_of_decrypt_update_tr (by rw [hR2Eq]) (by rw [hR2Eq]) (by rw [hR2Eq])
      (hsess'.trans hSt') hRel_c
  have hγ_msg_rk : gamma interpretation S g msg.ratchetKey = pf.inner.senderRatchetKey.bytes.toList :=
    hrk_m
  have hSub_c' : ∀ c_k ∈ (sessionToRecordRec sess').current.receiverChains, ∀ k ∈ c_k.messageKeys,
      (∃ c_old ∈ (sessionToRecordRec sess).current.receiverChains,
        c_old.senderRatchetKey = c_k.senderRatchetKey ∧ k ∈ c_old.messageKeys) ∨
      (c_k.senderRatchetKey = Symbolic.Swarm.CREF.TR.serializedKey
          (gamma interpretation S g msg.ratchetKey) ∧
        ∃ j < msg.counter.toNat - c.index.toNat,
          UInt32.ofBitVec k.1 = c.index + UInt32.ofNat j ∧ UInt32.ofBitVec k.1 ≠ msg.counter ∧
          k.2 = gamma interpretation S g (kdfCk (chainKeyAt c.chainKey j)).2) := by
    intro c_k hc_k k hk
    simp only [sessionToRecordRec, sessionToSessionRec, hRcs', List.mem_map] at hc_k
    rcases hc_k with ⟨rc', hrc', rfl⟩
    simp only [receiverChainToChainRec, List.mem_map] at hk; rcases hk with ⟨mk, hmk, rfl⟩
    rcases CryptoVerification.SessionModel.AdvanceAndFrame.mem_set_or sess.state.receiverChains ci₀
        { ch with chainKey := some ck_next, messageKeys := mks' } rc' hrc' with rfl | hrc_old
    · rcases hMks' mk hmk with hmk_old | ⟨j, hjLt, _, hjU32, hjNe, hjSeed, _⟩
      · left; exact ⟨receiverChainToChainRec ch,
          by simp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hch_mem,
          rfl, by simp only [receiverChainToChainRec, List.mem_map]; exact ⟨mk, hmk_old, rfl⟩⟩
      · right; refine ⟨?_, j, hctr_eq ▸ hjLt, hjU32, hctr_eq ▸ hjNe, hjSeed⟩
        show ch.senderRatchetKey.serialize = Symbolic.Swarm.CREF.TR.serializedKey
          (gamma interpretation S g msg.ratchetKey)
        rw [hsrk0, hγ_msg_rk]; rfl
    · left; exact ⟨receiverChainToChainRec rc',
        by simp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hrc_old,
        rfl, by simp only [receiverChainToChainRec, List.mem_map]; exact ⟨mk, hmk, rfl⟩⟩
  have hFresh : TRRecvCountersFresh (runTraceMoves r (ms₀ ++ pre)) r.bob st :=
    (hat.fresh r.bob stateIdx st hp_mem hst₀ hcur₀).1
  have htr := a2b_runTrace_decrypt_noRatchet (wrapped := wrapped) hst₀ hmsg hparse hver hfind hcons
    hspqr hpqSalt hmac_eq hdec
  have hsk' := a2b_skippedOk_existing_decTail hrun.2.2.1.1 hFresh hc_mem hc_rk hcons htr hsk_pre_sess
    hSub_c'
  have hnd' : RecordChainsWF3 (sessionToRecordRec sess') :=
    nodup_and_lt_of_existing_tr hFind hNotLt hAdv hNext hSet (by rw [hsess', hSt']) hnd_sess
  have hrelP :=
    (Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.stateRel_sessionToRecordRecPending_iff interpretation S g
      { st with recv := setRecvChain st.recv c', spqr := spqr' } sess').mpr hrel'
  exact ⟨a2b_trRecordStateInv_decTail_single hp_mem htr hnew hrelP hsk'
      hC.out.hcanon_out hks₀ hnd',
    a2b_trNsBound_decTail hns hst₀ htr⟩

end X2

theorem prom_trRecvFreshAll_of_quietExt {r₀ : ProtocolSetup} {ms ms' : List Move}
    (hq : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r₀ ms) (runTraceMoves r₀ ms'))
    (h : TR.TRRecvFreshAll r₀ ms) : TR.TRRecvFreshAll r₀ ms' := by
  intro q stateIdx st hqab hget hcur
  rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_getLocalState hq] at hget
  rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_isCurrentSnapshot hq] at hcur
  obtain ⟨hc, hs⟩ := h q stateIdx st hqab hget hcur
  exact ⟨TR.trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ _ hl => (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_eventLoggedAt hq _ _).mp hl)
      (fun _ _ _ _ _ _ hl => (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hc,
    TR.trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ _ hl => (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hs⟩

theorem prom_roleSnapshots_of_quietPre {r₀ : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ ms₀)) :
    RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact roleSnapshots_of_movesFrom_invisibleNoEffect hpre hrole

theorem prom_recvAtFacts_of_quietPre {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hhist : TR.CHistStep.CHist interpretation r₀ S g ms₀)
    (hfresh : TRRecvFreshAll r₀ ms₀) :
    RecvDecStepAt.RecvAtFacts interpretation r₀ S g (ms₀ ++ pre) := by
  have hq := a2b_quietPre hpre
  obtain ⟨hlen, hlow, hbf, hh⟩ := Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_cHist hq hhist
  exact ⟨hlen, hlow, hbf, hh, prom_trRecvFreshAll_of_quietExt hq hfresh⟩

/-- Re-establishes `PureTRRecordStateInv` and `TRNsBound` at a single explanation
`(g, ms₀, pre, mv, post)` of an accepting promote call, given the five residual seed facts. -/
theorem prom_rcvDecTie_at
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
    (hsel : PromDecSelSkipped sess pf.inner mid coins ∨ PromDecSelNoRatchet sess pf.inner mid coins ∨
      PromDecSelRatchetDH sess pf.inner mid coins)
    (g : Ghost) (ms₀ pre : List Move) (mv : Move) (post : List Move)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ mv :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hdec : DecryptBy r.bob mv)
    (hpost : MovesFrom InvisibleNoEffect (mv.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hch₀ : CHistBy interpretation r S g ms₀)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) mv = some t →
      ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r S g (ms₀ ++ pre) pf.message mv)
    (hrel : PureCRecRel interpretation r S g (ms₀ ++ pre) r.bob rec)
    (hns : TR.TRNsBound r (ms₀ ++ pre) e'.sent)
    (hfresh : TR.TRRecvFreshAll r ms₀)
    (habs : TR.G1.G1cAttackerBuiltSeedExcl' interpretation r S g (ms₀ ++ pre))
    (hX : TR.RecvDecStep.A2bCrossSeedExcl interpretation r S g (ms₀ ++ pre) acc)
    (hA : TR.RecvDecStep.A2bSeedShapeEqRes interpretation r S g (ms₀ ++ pre) acc)
    (hRk : TR.RecvDecStep.A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc) :
    TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre ++ [mv])
        (fun q => if q = r.bob then some sm.state else none) ∧
      TR.TRNsBound r (ms₀ ++ pre ++ [mv]) e'.sent := by
  have hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) :=
    prom_roleSnapshots_of_quietPre hpre hch₀.2
  have hat : RecvDecStepAt.RecvAtFacts interpretation r S g (ms₀ ++ pre) :=
    prom_recvAtFacts_of_quietPre hpre hch₀.1 hfresh
  have hacc := prom_accBlk_has_accept b mid pt
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  have hrr : PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre)
      (fun q => if q = r.bob then some rec else none) := by
    rcases hrel with hrr | ⟨hab, _⟩
    · exact hrr
    · exact False.elim (hwf.1 hab.symm)
  cases mv
  case decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    have hme : me = r.bob := hdec
    subst hme
    rcases hsel with hsk | hnr | hdh
    ·
      obtain ⟨ci, rc, ck, hmid, _hcoins, hrc, hrc_key, hck, hlt⟩ := hsk
      subst hmid
      exact (a2b_not_decrypt_of_binSkip interpretation r S g ms₀ pre post acc _ r.bob stateIdx
        msgIdx pqIdx spqrMsgIdx wrapped rec pf.message hB hpre hpost (prom_accBlk_nil_no_rng' b pt)
        hacc hcurR hrr hrole (promGhost rec sess) pf.inner ci rc ck hC.out.hcan_in htry hrc hrc_key
        hck hlt).elim
    ·
      exact prom_tieA_leaf hceh hwf hS hC hnr g ms₀ pre post e'.sent stateIdx msgIdx pqIdx
        spqrMsgIdx wrapped hB hpre hpost hcurR hrr hns hrole hat
    ·
      exact prom_tieB_ratchet_leaf hext hceh hwf hik hS hC hdh g ms₀ pre post stateIdx msgIdx pqIdx
        spqrMsgIdx wrapped hB hpre hpost hnocol hcurR hrr hns hrole hat habs
  case decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    have hme : me = r.bob := hdec
    subst hme
    rcases hsel with hsk | hnr | hdh
    ·
      exact prom_tieB_skip_leaf hext hceh hwf hik hS hC hsk g ms₀ pre post stateIdx msgIdx skIdx
        pqIdx spqrMsgIdx wrapped hB hpre hpost hnocol hcurR hrr hns hrole hat habs
    ·
      exact (prom_not_decryptSkipped_of_binStep hceh hwf hS hC hnr g ms₀ pre post _ r.bob stateIdx
        msgIdx skIdx pqIdx spqrMsgIdx wrapped hB hpre hpost hacc hnocol hcurR _ hrr hrole hat hX hA
        hRk).elim
    ·
      obtain ⟨rngBytes, hmid, -, -, -⟩ := hdh
      subst hmid
      exact (a2b_not_decryptSkipped_of_rng interpretation r S g ms₀ pre post acc _ r.bob stateIdx
        msgIdx skIdx pqIdx spqrMsgIdx wrapped hB hpre hpost hacc (prom_accBlk_rng b rngBytes pt)).elim
  all_goals exact hdec.elim

end Symbolic.Swarm.CREF.CliPure
