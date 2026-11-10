/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptSplitPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureA
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecPendingAPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecPendingPureA
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import Symbolic.Proofs.Swarm.CREF.Xpl.RatchetHit
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Pending Pre-Key Branch: DH-Ratchet Receive and Counter-Comparison Exclusion

Establishes `PureTRRecordStateInv` and `TRNsBound` for `session_recv_wire` on `PureAliceInitPending`
in the DH-ratchet (`a2b_tieB_ratchet_pending_of_block`) and skipped-key
(`a2b_tieB_skip_pending_of_block`) cases, and rules out a model `decrypt` when `m.counter < ck.index`
(`a2b_not_decrypt_of_binSkip_pending`).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain setRecvChain chainKeyAt kdfCk
  maxForwardJumps)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 encSession_length_le_encodeRecord pqRatchetState_length_le_encSession)

/-- A DH-ratchet `decrypt` block of `p = r₀.alice` from `PureAliceInitPending` establishes
`PureTRRecordStateInv` (clearing the pending pre-key) and preserves `TRNsBound`. -/
theorem a2b_tieB_ratchet_pending_of_block
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (hik : IkShape interpretation r₀)
    (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc : List MachineEvent) (sent : List HwBytes)
    (p : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body rngBytes : HwBytes) (r : StateAndMessage)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (rcvAccBlk body [.rng rngBytes] r))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r₀ (ms₀ ++ pre))
        (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r₀ S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hp : p = r₀.alice)
    (hpend : PureAliceInitPending interpretation r₀ S g (ms₀ ++ pre) rec)
    (hns : TRNsBound r₀ (ms₀ ++ pre) sent)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g (ms₀ ++ pre))
    (hABS' : Symbolic.Swarm.CREF.TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g (ms₀ ++ pre))
    (g_rw : RecvWireGhost) (m : SignalMessage)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hstate_lt : r.state.length < 2 ^ 64)
    (hcanon' : r.state.length < 2 ^ 32 - 2 ^ 20 → (pureTrSlots r₀).canon p r.state)
    (hwho : g_rw.who = if p = r₀.alice then 0 else 1)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
      Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (hrng_len : rngBytes.length = 32)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc_none : ∀ rc ∈ g_rw.sess.state.receiverChains, rc.senderRatchetKey ≠ m.senderRatchetKey)
    (hcoins_ok : Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.PureDecryptCoinsOk
      (Proofs.libsignal.Hooks2.cryptoOf' interpretation)
      g_rw.sess.state m.senderRatchetKey
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)))
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureEvalRecvWireWithCoinsW
        (Proofs.libsignal.Hooks2.cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw
        (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)) =
        some (r.state, r.message)) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) sent := by
  let ms := ms₀ ++ pre
  have hnil_all := sess_messageKeys_eq_nil_of_aliceInitPending hpend hcanon_q
  have hrr := trRecordStateInv_pend_of_aliceInitPending hp hpend
  have hmatch := a2b_block_vis hB hpre hpost
  have hrng_blk : .rng rngBytes ∈ rcvAccBlk body [.rng rngBytes] r := by
    simp [rcvAccBlk]
  have hacc_blk : ∃ e ∈ rcvAccBlk body [.rng rngBytes] r, eventKind e = .accept :=
    ⟨.accept r.message, by simp [rcvAccBlk], rfl⟩
  obtain ⟨hRng, st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
      hst, hmsg, hparse, hver, hfind, hlow, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    ratchet_of_matched hmatch hrng_blk hacc_blk
  have hreach : (runTraceMoves r₀ ms).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 ms.length
    rwa [← List.append_assoc, List.take_left] at h
  have hrun : ModelRun r₀ ms := by
    have h := hB.run
    rw [← List.append_assoc] at h
    exact modelRun_prefix_of_reachable h hreach
  have hrep : t ∈ recvRepresentations interpretation r₀ S g ms body := hcurR.2 t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrr p rec (by simp)
  have hidx : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (sessionToRecordRecPending g_rw.sess) :=
    Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q
      hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff]; change StateRel interpretation S g st (normPending (sessionToRecordRecPending g_rw.sess)); rw [← hnorm_eq, stateRel_normPending_iff]; exact hrel₀
  have hnd_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  obtain ⟨role, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, st',
      _hRole, _hVer, _hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet,
      _hMkGen, _hMac, _hDec, hSt', hr_enc⟩ :=
    a2b_pend_evalRecvWireWithCoinsW_ratchetDH_inv interpretation body rngBytes r g_rw m
      newPqrState pqrKey hwire htry hrc_none hrecv_spqr heval
  let s' : Session (List (BitVec 8)) :=
    { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  obtain ⟨_, _, hpq_sess, _, _, _hver_sess, _⟩ :=
    Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure
      interpretation S g rec rec₀ st st g_rw hrecBytes₀ hrel₀ hcanon_q rfl
  have hspqr'_eq : spqr' =
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack :=
    DY.Spqr.spqrRecv_state _ _ _ _ hspqr
  have hspqr'_gam : gamma interpretation S g spqr' = newPqrState := by
    rw [hspqr'_eq]
    exact (spqrRecv_step_gamma_state_and_key
      interpretation hceh r₀ S hS g ms body st g_rw t msg m
      newPqrState pqrKey hpq_sess hrep hparse htry hrecv_spqr).1
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld m htry
  have hTheir' : m.senderRatchetKey.bytes.toList = gamma interpretation S g msg.ratchetKey :=
    hrk_m.symm
  have hPkLen : (gamma interpretation S g msg.ratchetKey).length = 32 :=
    hTheir' ▸ m.senderRatchetKey.bytes.2
  have hTheir : m.senderRatchetKey = ⟨vec32 (gamma interpretation S g msg.ratchetKey)⟩ := by
    cases hmk : m.senderRatchetKey with | mk b =>
    have hb : b.toList = (vec32 (gamma interpretation S g msg.ratchetKey)).toList := by
      rw [hmk] at hTheir'; exact hTheir'.trans (vec32_toList_of_length_eq_tr hPkLen).symm
    exact congrArg PublicKey.mk (Subtype.ext hb)
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hst_rci : TrStateRkCkIk r₀ st := trStateRkCkIk_of_getLocalState hrun hst₀
  have hRkLen : (gamma interpretation S g st.rk).length = 32 :=
    hst_rci.rk_len interpretation S g hwf hB.pre.1
  have hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst_rci.recv_ck_len interpretation S g hwf hB.pre.1
  have hJump' : (m.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps := by
    obtain ⟨_, _, _, _, _, _, _, hr1⟩ := dhRatchetStep_ok_inv hDh
    rw [hr1] at hJump; exact hJump
  obtain ⟨_hfind₀, mks', seed₀, c₀', hcons₀_bv, _hSeedEq, _hCntEq,
      _hc'_rk, _hc'_rIdx, _hc_idx0, _hc_rIdx, hR2Eq', hRel_c, hRcMem, hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_dhRatchetStep_tr
      interpretation S g hceh (hrel := hrel_sess)
      (hRkLen := hRkLen) (hDhsLen := hks₀.1) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len) (hspqr' := hspqr'_gam)
      (hFindNone := hFind) (hStep := hDh)
      (hNotLt := hNotLt) (hJump := hJump') (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
  have hcons_eq : some (seed₀, c₀') = some (seed, c') :=
    hcons₀_bv.symm.trans (hctr_eq ▸ hcons)
  injection hcons_eq with hpair_eq; injection hpair_eq with hseed_eq hc'_eq
  cases hseed_eq; cases hc'_eq
  have hnew : r.state = recordBytes (sessionToRecordRec s') := by
    have hst_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some s'⟩).length < 2 ^ 64 :=
      hr_enc ▸ hstate_lt
    have hsess'_len : (CryptoVerification.E2E.Record.encSession s').length < 2 ^ 64 :=
      lt_of_le_of_lt (encSession_length_le_encodeRecord s') hst_lt
    have hpq'_len : s'.state.pqRatchetState.length < 2 ^ 64 :=
      lt_of_le_of_lt (pqRatchetState_length_le_encSession s')
        hsess'_len
    obtain ⟨_, _, ⟨_, _, hchains_sc, _, _, _, _⟩⟩ := hcanon_q
    have hseeds : ∀ rc0 ∈ g_rw.sess.state.receiverChains, ∀ mk ∈ rc0.messageKeys,
        mk.seed.length < 2 ^ 63 := by
      intro rc0 hrc0 mk hmk; have h32 := (hchains_sc rc0 hrc0).2 mk hmk; omega
    have hseeds' : ∀ rc' ∈ s'.state.receiverChains, ∀ mk ∈ rc'.messageKeys,
        mk.seed.length < 2 ^ 63 := by
      intro rc' hrc' mk hmk
      rcases hRcMem rc' (by simpa [s', hSt'] using hrc') with hrc_old | rfl
      · exact hseeds rc' hrc_old mk hmk
      · obtain ⟨_, _, _, _, _, _, hlen32⟩ := hMks' mk hmk; omega
    have heq_rec : sessionToRecordRec s' = SendRetCoins.sessionToRecordRecPending s' := rfl
    rw [hr_enc, heq_rec, recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 s'
      (by dsimp only [s']; omega) hpq'_len hseeds' hsess'_len]
  have hrel' : StateRel interpretation S g
      { (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1 with
        recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.recv c',
        spqr := spqr' }
      (sessionToRecordRec s') := by
    dsimp only [s']; rw [hSt']; exact hRel_c
  have hR1Rc : r1.receiverChains =
      RatchetState.evictReceiverChains
        (g_rw.sess.state.receiverChains ++ [⟨m.senderRatchetKey, some ck, []⟩]) :=
    (dhRatchetStep_ok_eq_gamma_trDhRatchetState
      interpretation S g hceh (hrel := hrel_sess)
      (hRkLen := hRkLen) (hDhsLen := hks₀.1) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len) (hStep := hDh)).2.2.2.2.2.2.2.2.2.1
  have hMks'_c : ∀ k ∈ mks',
      ∃ j < msg.counter.toNat,
        k.counter = BitVec.ofNat 32 j ∧ UInt32.ofBitVec k.counter = UInt32.ofNat j ∧
        UInt32.ofBitVec k.counter ≠ msg.counter ∧
        k.seed = gamma interpretation S g
          (kdfCk (chainKeyAt
            (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2.chainKey j)).2 ∧
        k.seed.length = 32 := by
    intro k hk
    obtain ⟨j, hj, hk1, hk2, hk3, hk4, hk5⟩ := hMks' k hk
    have hj' : j < msg.counter.toNat := by
      change j < (UInt32.ofBitVec m.counter).toNat - 0 at hj
      rw [Nat.sub_zero, hctr_eq] at hj; exact hj
    have hk1' : k.counter = BitVec.ofNat 32 j :=
      hk1.trans (BitVec.zero_add (BitVec.ofNat 32 j))
    have hk2' : UInt32.ofBitVec k.counter = UInt32.ofNat j :=
      hk2.trans (UInt32.zero_add (UInt32.ofNat j))
    exact ⟨j, hj', hk1', hk2', hctr_eq ▸ hk3, hk4, hk5⟩
  have hFresh : TRRecvCountersFresh (runTraceMoves r₀ ms) p st :=
    (hat.fresh p stateIdx st hp_mem hst₀ hcur₀).1
  have htr := a2b_pend_runTrace_decrypt_ratchet (wrapped := wrapped)
    hst₀ hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec
  have hs'_rc : s'.state.receiverChains = r2.receiverChains := by
    change st'.receiverChains = r2.receiverChains; rw [hSt']
  have hsk' := a2b_pend_skippedOk_ratchet_decTail hreach hFresh htr hnil_all hTheir' hR1Rc
    (congrArg RatchetState.receiverChains hR2Eq') hMks'_c hs'_rc
  have hnd' : RecordChainsWF3 (sessionToRecordRec s') :=
    nodup_and_lt_of_dhRatchetStep_tr hFind hDh hNotLt hAdv hNext hSet hs'_rc hnd_sess
  have hRngLen_g : (g.σ (runTraceMoves r₀ ms).length 32).length = 32 := hRng.symm ▸ hrng_len
  exact ⟨a2b_pend_trRecordStateInv_decRatchet_single hp_mem htr hnew hrel' hsk' hcanon' hks₀
      hRngLen_g hnd',
    a2b_pend_trNsBound_decRatchet hns htr⟩

theorem a2b_tieB_skip_pending_of_block
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms₀ pre : List Move) (sent : List HwBytes)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body : HwBytes)
    (hpend : PureAliceInitPending interpretation r₀ S g (ms₀ ++ pre) rec)
    (r : StateAndMessage) (g_rw : RecvWireGhost)
    (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
      Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hskip_idx : m.counter < ck.index)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureEvalRecvWireWithCoinsW
        (Proofs.libsignal.Hooks2.cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 =
        some (r.state, r.message)) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms₀ ++ pre ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        sent :=
  False.elim (a2b_not_skipped_branch_of_pending interpretation r₀ S g (ms₀ ++ pre) rec body r g_rw
    m ci rc ck newPqrState pqrKey hpend hwire hcanon_q htry hrc hrc_key hck hskip_idx hrecv_spqr heval)

theorem a2b_pend_modelChain_of_binChain
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
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

/-- Rules out a no-ratchet model `decrypt` on `PureAliceInitPending` when the binary receiver chain
has `m.counter < ck.index`. -/
theorem a2b_not_decrypt_of_binSkip_pending
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
    (hp : p = r₀.alice)
    (hpend : PureAliceInitPending interpretation r₀ S g (ms₀ ++ pre) rec)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (g_rw : RecvWireGhost) (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
      Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hskip_idx : m.counter < ck.index) : False := by
  have hrr := trRecordStateInv_pend_of_aliceInitPending hp hpend
  have hmatch := a2b_block_vis hB hpre hpost
  obtain ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver, _hrcf,
      hfind, hidx, _hcons, _hspqr, _hpqSalt, _hmac_eq, _hdec, _hpt⟩ :=
    noRatchet_of_matched hmatch hno_rng hacc
  have hrep : t ∈ recvRepresentations interpretation r₀ S g (ms₀ ++ pre) body := hcurR.2 t hmsg
  obtain ⟨_hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, _hks₀,
      hnd₀⟩ := hrr p rec (by simp)
  have hidx₀ : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx₀
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (sessionToRecordRecPending g_rw.sess) :=
    Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q
      hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff]; change StateRel interpretation S g st (normPending (sessionToRecordRecPending g_rw.sess)); rw [← hnorm_eq, stateRel_normPending_iff]; exact hrel₀
  have hnd1 : ((sessionToRecordRec g_rw.sess).current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup := hrc_rec₀ ▸ hnd₀.1
  obtain ⟨c₀, hc₀, hidx_eq, hrk₀⟩ := a2b_pend_modelChain_of_binChain hrel_sess hrc hck
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

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
