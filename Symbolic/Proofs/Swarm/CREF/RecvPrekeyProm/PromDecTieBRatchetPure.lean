/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieBRatchetPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.RatchetHit
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj

/-!
# Promote Record-State Tie for the DH-Ratchet Branch

Proves `prom_tieB_ratchet_leaf`, re-establishing `PureTRRecordStateInv` and `TRNsBound` when an
accepting promote call in the `PromDecSelRatchetDH` branch is explained by a model `Move.decrypt`
of Bob.
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
open DY.Libsignal.TripleRatchet (setRecvChain chainKeyAt kdfCk maxForwardJumps)
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
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState)
open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

private theorem promRatchet_flatten_lenField_ge {α : Type} (tag : Nat) (f : α → HwBytes)
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten.length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem promRatchet_encSession_length_le (s : Session HwBytes) :
    (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord
    CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  simp only [Option.map_some, List.length_append]
  omega

private theorem promRatchet_encReceiverChain_length_le (s : Session HwBytes)
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := promRatchet_flatten_lenField_ge 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession
  simp only [List.length_append]
  omega

private theorem promRatchet_seed_length_le_encReceiverChain (rc : ReceiverChain)
    (mk : MessageKeyGenerator) (hmk : mk ∈ rc.messageKeys) :
    mk.seed.length ≤ (CryptoVerification.E2E.Record.encReceiverChain rc).length := by
  have h1 := promRatchet_flatten_lenField_ge 4 CryptoVerification.E2E.Record.encMessageKey
    rc.messageKeys mk hmk
  have h2 : mk.seed.length ≤ (CryptoVerification.E2E.Record.encMessageKey mk).length := by
    unfold CryptoVerification.E2E.Record.encMessageKey
      CryptoVerification.E2E.Record.bytesField
      CryptoVerification.E2E.Record.lenField
    split <;> simp_all only [List.length_nil, List.length_append] <;> omega
  unfold CryptoVerification.E2E.Record.encReceiverChain
  simp only [List.length_append]
  omega

private theorem promRatchet_recordBytes_of_promAcceptOut
    {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {rec b : HwBytes} {mid : List MachineEvent} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt) :
    recordBytes (sessionToRecordRecPending sess') = sm.state := by
  obtain ⟨_, _, ⟨_, _, _, halice_in, _, _, _⟩⟩ := hOut.hcan_in
  obtain ⟨sess₁, hrc₁, -, -, -, h62, -⟩ := hOut.hwrc
  obtain ⟨hrc₁_bytes, _, ⟨_, _, _, _, _, hpq₁, _⟩⟩ := hrc₁
  have hpq_eq : sess₁.state.pqRatchetState = sess'.state.pqRatchetState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁_bytes hOut.hstate h62
  have hsess'_len : (CryptoVerification.E2E.Record.encSession sess').length < 2 ^ 62 := by
    have hle := promRatchet_encSession_length_le sess'
    rw [← hOut.hstate] at hle
    omega
  rw [hOut.hstate]
  exact recordBytes_sessionToRecordRecPending_eq_encodeRecord sess'
    (by rw [hOut.halice]; omega)
    (by rw [← hpq_eq]; omega)
    (fun rc hrc mk hmk => Nat.lt_of_le_of_lt
      (Nat.le_trans (promRatchet_seed_length_le_encReceiverChain rc mk hmk)
        (promRatchet_encReceiverChain_length_le sess' rc hrc))
      (by omega))
    (fun rc hrc => Nat.lt_of_le_of_lt (promRatchet_encReceiverChain_length_le sess' rc hrc) (by omega))
    (by omega)

/-- Re-establishes `PureTRRecordStateInv` and `TRNsBound` for the `PromDecSelRatchetDH` branch
against a model `Move.decrypt` of Bob. -/
theorem prom_tieB_ratchet_leaf
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation) (hceh : ExternCryptoLawsHold interpretation)
    (hwf : ProtocolSetupWF r) (hik : IkShape interpretation r) (hS : S = compSemOf interpretation r)
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hsel : PromDecSelRatchetDH sess pf.inner mid coins)
    (g : Ghost) (ms₀ pre post : List Move)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ .decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r (ms₀ ++ pre))
        (.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r S g (ms₀ ++ pre) pf.message
      (.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre)
      (fun q => if q = r.bob then some rec else none))
    (hns : TRNsBound r (ms₀ ++ pre) e'.sent)
    (hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r S g (ms₀ ++ pre))
    (habs : Symbolic.Swarm.CREF.TR.G1.G1cAttackerBuiltSeedExcl' interpretation r S g (ms₀ ++ pre)) :
    PureTRRecordStateInv interpretation r S (pureTrSlots r) g
        (ms₀ ++ pre ++ [.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = r.bob then some sm.state else none) ∧
      TRNsBound r (ms₀ ++ pre ++ [.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        e'.sent := by
  obtain ⟨rngBytes, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen,
      newPqrState, pqrKey, st',
      hmid, hrng_len, _hcoins, _hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet,
      _hMkGen, hrecv_spqr, _hMac, _hDec, hSt', hsess'_st, _hstate⟩ :=
    prom_adapter_ratchetDH_out hC.out hsel
  subst hmid
  let ms := ms₀ ++ pre
  have hmatch := a2b_block_vis hB hpre hpost
  have hrng_blk : .rng rngBytes ∈ promAccBlk b [.rng rngBytes] pt := by
    simp [promAccBlk]
  have hacc_blk : ∃ e ∈ promAccBlk b [.rng rngBytes] pt, eventKind e = .accept :=
    prom_accBlk_has_accept b [.rng rngBytes] pt
  obtain ⟨hRng, st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
      hst, hmsg, hparse, hver, hfind, hlow, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    ratchet_of_matched hmatch hrng_blk hacc_blk
  have hreach : (runTraceMoves r ms).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 ms.length
    rwa [← List.append_assoc, List.take_left] at h
  have hrun : ModelRun r ms := by
    have h := hB.run
    rw [← List.append_assoc] at h
    exact modelRun_prefix_of_reachable h hreach
  have hrep : t ∈ recvRepresentations interpretation r S g ms pf.message := hcurR.2 t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrr r.bob rec (by simp)
  have hidx : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  have hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess := hC.out.hcan_in
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  obtain ⟨hnorm_eq, hrel_sess0, hpq_sess, _, _, _hver_sess, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st st g_rw hrecBytes₀
      hrel₀ hcanon_q rfl
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := hrel_sess0
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hsk_pre_sess : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains,
      ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo r.bob) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB (runTraceMoves r ms) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r ms) (st.sessionInfo r.bob) seed (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st.toDRState.recv pk).isSome = true :=
    hrc_rec₀ ▸ hsk_pre₀
  have hnd_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  let s' : Session (List (BitVec 8)) :=
    { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hspqr'_eq : spqr' =
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack :=
    DY.Spqr.spqrRecv_state _ _ _ _ hspqr
  have hspqr'_gam : gamma interpretation S g spqr' = newPqrState := by
    rw [hspqr'_eq]
    exact (spqrRecv_step_gamma_state_and_key interpretation hceh r S hS g ms pf.message st g_rw t msg
      pf.inner newPqrState pqrKey hpq_sess hrep hparse htry hrecv_spqr).1
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld pf.inner htry
  have hTheir' : pf.inner.senderRatchetKey.bytes.toList = gamma interpretation S g msg.ratchetKey :=
    hrk_m.symm
  have hPkLen : (gamma interpretation S g msg.ratchetKey).length = 32 :=
    hTheir' ▸ pf.inner.senderRatchetKey.bytes.2
  have hTheir : pf.inner.senderRatchetKey = ⟨vec32 (gamma interpretation S g msg.ratchetKey)⟩ :=
    (Proofs.libsignal.RngG.CliPure.R3.publicKey_eq_vec32_of_toList_eq hTheir').1
  have hctr_eq : UInt32.ofBitVec pf.inner.counter = msg.counter := UInt32.ext hctr_m.symm
  have hst_rci : TrStateRkCkIk r st := trStateRkCkIk_of_getLocalState hrun hst₀
  have hRkLen : (gamma interpretation S g st.rk).length = 32 :=
    hst_rci.rk_len interpretation S g hwf hB.pre.1
  have hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst_rci.recv_ck_len interpretation S g hwf hB.pre.1
  have hJump' : (pf.inner.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps := by
    obtain ⟨_, _, _, _, _, _, _, hr1⟩ := Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
    rw [hr1] at hJump; exact hJump
  obtain ⟨_hfind₀, mks', seed₀, c₀', hcons₀_bv, _hSeedEq, _hCntEq,
      _hc'_rk, _hc'_rIdx, _hc_idx0, _hc_rIdx, hR2Eq', hRel_c, _hRcMem, hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_dhRatchetStep_tr interpretation S g hceh (hrel := hrel_sess)
      (hRkLen := hRkLen) (hDhsLen := hks₀.1) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len) (hspqr' := hspqr'_gam)
      (hFindNone := hFind) (hStep := hDh)
      (hNotLt := hNotLt) (hJump := hJump') (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
  have hcons_eq : some (seed₀, c₀') = some (seed, c') :=
    hcons₀_bv.symm.trans (hctr_eq ▸ hcons)
  injection hcons_eq with hpair_eq; injection hpair_eq with hseed_eq hc'_eq
  cases hseed_eq; cases hc'_eq
  have hnew : sm.state = recordBytes (sessionToRecordRecPending sess') :=
    (promRatchet_recordBytes_of_promAcceptOut hC.out).symm
  have hrel_s' : StateRel interpretation S g
      { (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1 with
        recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1.recv c',
        spqr := spqr' }
      (sessionToRecordRec s') := by
    dsimp only [s']; rw [hSt']; exact hRel_c
  have hrel_sess' : StateRel interpretation S g
      { (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1 with
        recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1.recv c',
        spqr := spqr' }
      (sessionToRecordRec sess') :=
    stateRel_sessionToRecordRec_congr_tr
      (by dsimp only [s']; rw [hsess'_st]) (by dsimp only [s']; rw [hsess'_st])
      (by dsimp only [s']; rw [hsess'_st]) (by dsimp only [s']; rw [hsess'_st])
      (by dsimp only [s']; rw [hsess'_st]) (by dsimp only [s']; rw [hsess'_st])
      (by dsimp only [s']; rw [hsess'_st]) (by dsimp only [s']; rw [hsess'_st])
      hrel_s'
  have hrel' : StateRel interpretation S g
      { (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1 with
        recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1.recv c',
        spqr := spqr' }
      (sessionToRecordRecPending sess') :=
    (Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.stateRel_sessionToRecordRecPending_iff interpretation S g
      { (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1 with
        recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1.recv c',
        spqr := spqr' }
      sess').mpr hrel_sess'
  have hR1Rc : r1.receiverChains =
      RatchetState.evictReceiverChains
        (g_rw.sess.state.receiverChains ++ [⟨pf.inner.senderRatchetKey, some ck, []⟩]) :=
    (dhRatchetStep_ok_eq_gamma_trDhRatchetState interpretation S g hceh (hrel := hrel_sess)
      (hRkLen := hRkLen) (hDhsLen := hks₀.1) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len) (hStep := hDh)).2.2.2.2.2.2.2.2.2.1
  have hMks'_c : ∀ k ∈ mks',
      ∃ j < msg.counter.toNat,
        k.counter = BitVec.ofNat 32 j ∧ UInt32.ofBitVec k.counter = UInt32.ofNat j ∧
        UInt32.ofBitVec k.counter ≠ msg.counter ∧
        k.seed = gamma interpretation S g
          (kdfCk (chainKeyAt
            (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).2.chainKey j)).2 ∧
        k.seed.length = 32 := by
    intro k hk
    obtain ⟨j, hj, hk1, hk2, hk3, hk4, hk5⟩ := hMks' k hk
    have hj' : j < msg.counter.toNat := by
      change j < (UInt32.ofBitVec pf.inner.counter).toNat - 0 at hj
      rw [Nat.sub_zero, hctr_eq] at hj; exact hj
    have hk1' : k.counter = BitVec.ofNat 32 j :=
      hk1.trans (BitVec.zero_add (BitVec.ofNat 32 j))
    have hk2' : UInt32.ofBitVec k.counter = UInt32.ofNat j :=
      hk2.trans (UInt32.zero_add (UInt32.ofNat j))
    exact ⟨j, hj', hk1', hk2', hctr_eq ▸ hk3, hk4, hk5⟩
  have hFresh : TRRecvCountersFresh (runTraceMoves r ms) r.bob st :=
    (hat.fresh r.bob stateIdx st hp_mem hst₀ hcur₀).1
  have htr := a2b_runTrace_decrypt_ratchet (wrapped := wrapped)
    hst₀ hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec
  have hs'_rc : sess'.state.receiverChains = r2.receiverChains := by
    rw [hsess'_st, hSt']
  have hsk' : ∀ c_k ∈ (sessionToRecordRecPending sess').current.receiverChains,
      ∀ k ∈ c_k.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed_k,
        (runTraceMoves r (ms ++ [.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo r.bob) pk (UInt32.ofBitVec k.1) seed_k rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB (runTraceMoves r (ms ++ [.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped])) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r (ms ++ [.decrypt r.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped]))
          (st.sessionInfo r.bob) seed_k (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain
          { (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1 with
            recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r ms).length).1.recv c',
            spqr := spqr' }.toDRState.recv pk).isSome = true :=
    a2b_skippedOk_ratchet_decTail hreach hFresh htr hrel_sess hnd_sess.1 hsk_pre_sess hTheir' hR1Rc
      (congrArg RatchetState.receiverChains hR2Eq') hMks'_c hs'_rc
  have hnd' : RecordChainsWF3 (sessionToRecordRecPending sess') :=
    nodup_and_lt_of_dhRatchetStep_tr hFind hDh hNotLt hAdv hNext hSet hs'_rc hnd_sess
  have hRngLen_g : (g.σ (runTraceMoves r ms).length 32).length = 32 := hRng.symm ▸ hrng_len
  exact ⟨a2b_trRecordStateInv_decRatchet_single hp_mem htr hnew hrel' hsk'
      hC.out.hcanon_out hks₀
      hRngLen_g hnd',
    a2b_trNsBound_decRatchet hns htr⟩

end Symbolic.Swarm.CREF.CliPure
