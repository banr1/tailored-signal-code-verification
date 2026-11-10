/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Lift.Defs
import Batteries.Data.UInt
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.A2bSameOriginPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptCollisionPickPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendCoinsBridge
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTiePureA
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecPendingAPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieDispatchPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2BranchesPure
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import Symbolic.Proofs.Swarm.CREF.Xpl.SkippedHit
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Ratchet Decrypt Collision Bridge

Proves `BridgeCCaseBSpec`: when the binary session decrypts `inner_wire` with a DH ratchet
(`pureDrawsCoins = true`), any `ModelAcceptsTermAfterCoinSplit` explanation on `(g, ms)` whose cut
draws zero `.rng` events before `.accept out` yields `RecvCollision interp' r S g ms t_rep`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.Coinsplit.Lift.L06

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (interpW)
open Symbolic.Swarm.TRREF.GrowthRecordPure (pureSpqr)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure hiding pureDrawsCoins
open Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval (pureDrawsCoins)
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.Coinsplit.Lift

private theorem binarySessionDecryptOk_tryDecryptW
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted sent : List HwBytes} {records : Participant → Option HwBytes}
    {me : Participant} {st st' : PqParty} {d_me : DirectorySnapshot}
    {x : RecordExtras} {g_st : GhostState HwBytes}
    {w inner_wire out : HwBytes} {inner : SignalMessage} {rc : BitVec 256}
    (hagree : ModelAgree interp P)
    (hbin : BinarySessionDecryptOk (interpOfParams interp P) P r accepted sent records me st st'
      d_me x g_st w inner_wire out inner rc) :
    let interp' := interpOfParams interp P
    ∃ (tag : BitVec 8) (w_tl : HwBytes) (msgType : MessageType) (s' : SessionState HwBytes),
      w = tag :: w_tl ∧
      RecvMsgBody (.recv w) inner_wire ∧
      Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
        Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q
        (encodeRecordUnderExtras (fun _ => x) g_st) (pqSession x g_st) ∧
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
        (cryptoOf' interp') (interpW interp') (pureSpqr (spqrModelOf interp'))
        ((pqxdhSessionParams P).expectedAddrs g_st.party)
        inner msgType rc (pqSession x g_st).state = (.ok out, s') := by
  intro interp'
  obtain ⟨_hme, _hinv, hwfSt, hsess, _hrec, _hlen, _hhon, htry, hcases⟩ := hbin
  have hb : ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
  have hcan_q := recordCanonical_Q_of_wfPq hwfSt hsess
  rcases hcases with ⟨rfl, hmod⟩ | ⟨q, hparse_w, rfl, _hfm, hmod⟩
  · unfold pqRecvWhisperModel at hmod
    rw [hsess, htry] at hmod
    dsimp only at hmod
    unfold pqxdhSessionDecryptModel at hmod
    rcases hdec : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g_st.party) inner .whisper rc g_st.session with ⟨err | pt0, s'⟩
    · rw [hdec] at hmod; cases err <;> simp at hmod
    · rw [hdec] at hmod; dsimp only at hmod
      rcases hk : s'.remoteIdentity with _ | k
      · simp [hk] at hmod
      · rw [hk] at hmod; dsimp only at hmod
        split_ifs at hmod
        · simp at hmod
        · simp only [Option.some.injEq, Prod.mk.injEq] at hmod
          rcases hmod with ⟨_, rfl⟩
          refine ⟨wireWhisperTag, inner_wire, .whisper, s', rfl, ?_, hcan_q, ?_⟩
          · simp [RecvMsgBody]
          · change Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
                (cryptoOf' interp') (interpW interp') (Cli.pureSpqrOf interp')
                ((pqxdhSessionParams P).expectedAddrs g_st.party) inner .whisper rc g_st.session = (.ok pt0, s')
            rw [← tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_bridge hb]
            exact hdec
  · obtain ⟨s', _htrusts, _hrem, hdec, _hst'⟩ := pqRecvMatchingFieldsModel_ok_inv hmod
    unfold parsePreKeyWire at hparse_w
    cases w with
    | nil => simp at hparse_w
    | cons tag w_tl =>
      dsimp only at hparse_w
      split at hparse_w
      · next htag =>
        obtain ⟨_, _, htry_q, _⟩ := parsePreKey_some_inv hparse_w
        have hinner_eq : q.inner = inner := by
          rw [htry] at htry_q
          injection htry_q with hq_eq
          exact hq_eq.symm
        rw [hinner_eq] at hdec
        refine ⟨tag, w_tl, .preKey, s', rfl, ?_, hcan_q, ?_⟩
        · simp [RecvMsgBody, parsePreKeyWire, htag, hparse_w]
        · change Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
              (cryptoOf' interp') (interpW interp') (Cli.pureSpqrOf interp')
              ((pqxdhSessionParams P).expectedAddrs g_st.party) inner .preKey rc g_st.session = (.ok out, s')
          rw [← tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_bridge hb]
          exact hdec
      · simp at hparse_w

private theorem pinCoins_keyToBytes32 (rc : BitVec 256) :
    Symbolic.Swarm.CREF.CliPure.RpkCli.pinCoins (some (HMAC.keyToBytes32 rc)) = rc := by
  have hlen : (HMAC.keyToBytes32 rc).length = 32 := by simp [HMAC.keyToBytes32]
  unfold Symbolic.Swarm.CREF.CliPure.RpkCli.pinCoins Symbolic.Swarm.CREF.CliPure.RpkCli.pureCoinsOf
  dsimp only
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  exact Proofs.libsignal.RngG.CliPure.DecCrypto.bytesToKey32_keyToBytes32 rc

private theorem seed_shape_eq_contradicts_freshAll
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ : Ghost} {ms₁ : List Move}
    {me : Participant} {stateIdx₀ skIdx rIdx_s srcIdx ts : Nat}
    {st₀ : _root_.DY.Libsignal.TripleRatchet.TRState}
    {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    {seed_ratch seed_s : _root_.DY.Bytes}
    {c' : _root_.DY.Libsignal.TripleRatchet.RecvChain}
    (hreach : (runTraceMoves r ms₁).Reachable _root_.DY.Libsignal.Composed.reachability)
    (hfresh : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r ms₁)
    (hme : me = r.alice ∨ me = r.bob)
    (hst₀ : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx₀ :
        _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₁)).1 =
      some st₀)
    (hcur₀ : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx₀ = true)
    (hcons : _root_.DY.Libsignal.TripleRatchet.consumeMessageKey
      (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2 msg.counter =
      some (seed_ratch, c'))
    (hsk : ((runTraceMoves r ms₁).at? skIdx : Option Symbolic.Swarm.COMPOSED.CompTrace.TREntry) =
      some ⟨_root_.DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
        (st₀.sessionInfo me) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩)
    (hsh : (gamma' interp' S g₁ seed_ratch).shape = (gamma' interp' S g₁ seed_s).shape) :
    False := by
  have hInv := Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach
  have hst₀_at : Symbolic.Swarm.COMPOSED.CompTrace.TRStateStoredAt me st₀ stateIdx₀ (runTraceMoves r ms₁) :=
    Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀
  obtain ⟨hpos₀, hpar₀, _, ⟨doneIdx_c, ikm_c, dh₁_c, hs_c, hrk₀, _, _⟩, _⟩ :=
    hInv.stateOK me st₀ stateIdx₀ hst₀_at
  let cNew := (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2
  have hcNew_def : cNew =
      { ratchetKey := msg.ratchetKey
        chainKey := (_root_.DY.Libsignal.TripleRatchet.createChain st₀.rk msg.ratchetKey st₀.dhs).2
        index := 0
        rIdx := st₀.rIdx + 2 } := rfl
  have hroot_c : Symbolic.Swarm.COMPOSED.CompRatchet.CompChainRootFrom1 dh₁_c ikm_c (st₀.rIdx + 1)
      (_root_.DY.Libsignal.TripleRatchet.createChain st₀.rk msg.ratchetKey st₀.dhs).2 :=
    Symbolic.Swarm.COMPOSED.CompRatchet.CompChainRootFrom1.of_step_pos hpos₀ hrk₀ msg.ratchetKey st₀.dhs
  have hcNew_sched : Symbolic.Swarm.COMPOSED.CompRatchet.CompRecvChainScheduleOK dh₁_c ikm_c
      st₀.initiator (st₀.rIdx + 2) cNew := by
    refine ⟨by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      (_root_.DY.Libsignal.TripleRatchet.createChain st₀.rk msg.ratchetKey st₀.dhs).2, hroot_c, rfl⟩
  obtain ⟨_, _, _, _, _, ck₀_c, hroot_c', _hck_c, hseed_c, _⟩ :=
    Symbolic.Swarm.COMPOSED.CompRatchet.consumeMessageKey_compSchedule hcNew_sched hcons
  have hrIdx_cNew : cNew.rIdx - 1 = st₀.rIdx + 1 := rfl
  rw [hrIdx_cNew] at hroot_c'
  rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hsk
  obtain ⟨_hs_pos, _, doneIdx_s, ikm_s, dh₁_s, ck₀_s, hs_s, hroot_s, hseed_s⟩ :=
    hInv.eventOK (_root_.DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
      (st₀.sessionInfo me) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx) ⟨skIdx, hsk⟩
  obtain ⟨rfl, rfl⟩ :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.compSessionAt_same_sinfo_eq hs_c hs_s
  have hsh_ck₀ :
      (gamma' interp' S g₁ ck₀_c).shape = (gamma' interp' S g₁ ck₀_s).shape :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.shape_chainKeyAt_inj' interp' S g₁ msg.counter.toNat
      (Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.shape_kdfCk_snd_inj' interp' S g₁
        (by rwa [← hseed_c, ← hseed_s]))
  have hm_eq : st₀.rIdx + 1 = rIdx_s - 1 :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.compChainRootFrom1_depth_eq_of_shape_eq
      interp' S g₁ hroot_c' hroot_s hsh_ck₀
  have hrIdx_le : rIdx_s ≤ st₀.rIdx :=
    (hfresh me stateIdx₀ st₀ hme hst₀ hcur₀).1.2.2.1 _ _ _ _ _ _ hsk
  omega

private theorem ratchet_mac_of_tryDecryptW
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {slots : Symbolic.Swarm.CREF.TR.PureTRSlots}
    {rec_fn : Participant → Option HwBytes} {me : Participant}
    {x : RecordExtras} {g_st : GhostState HwBytes}
    {inner_wire out : HwBytes} {inner : SignalMessage}
    {expected : Option HwBytes} {msgType : MessageType} {rc : BitVec 256}
    {s' : SessionState HwBytes} {g₁ : Ghost} {ms₁ : List Move} {τ_pre : List MachineEvent}
    {t : _root_.DY.Bytes} {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hext' : ExternContractsHoldCli interp')
    (hwf : ProtocolSetupWF r)
    (hS : S = compSemOf interp' r)
    (hmp : MatchedPrefix interp' r S who g₁ ms₁ τ_pre)
    (hrsi : Symbolic.Swarm.CREF.TR.PureTRRecordStateInv interp' r S slots g₁ ms₁ rec_fn)
    (hrec : rec_fn me = some (encodeRecordUnderExtras (fun _ => x) g_st))
    (hcan_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
      Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q
      (encodeRecordUnderExtras (fun _ => x) g_st) (pqSession x g_st))
    (htry : SignalMessage.tryFrom protoSignalCodec inner_wire = .ok inner)
    (hdraws : pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state inner.senderRatchetKey = true)
    (hdecW : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
      (cryptoOf' interp') (interpW interp') (pureSpqr (spqrModelOf interp'))
      expected inner msgType rc (pqSession x g_st).state = (.ok out, s'))
    (ht : t ∈ recvRepresentations interp' r S g₁ ms₁ inner_wire)
    (hparse : _root_.DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg) :
    ∃ (stateIdx₀ : Nat) (st₀ : _root_.DY.Libsignal.TripleRatchet.TRState)
      (seed_ratch k_own : _root_.DY.Bytes)
      (c_ratch' : _root_.DY.Libsignal.TripleRatchet.RecvChain),
      ((_root_.DY.PersistentLocalState.getLocalState me stateIdx₀ :
          _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₁)).1 =
        some st₀ ∧
      _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx₀ = true ∧
      Symbolic.Swarm.CREF.TR.StateRel interp' S g₁ st₀
        (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec (pqSession x g_st)) ∧
      (Proofs.libsignal.RngG.R3.ratchetStateOf (pqSession x g_st).state).findReceiverChainKey
        inner.senderRatchetKey = .ok none ∧
      msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion ∧
      _root_.DY.Libsignal.TripleRatchet.findRecvChain st₀.recv msg.ratchetKey = none ∧
      _root_.DY.X25519.x25519LowOrder msg.ratchetKey = false ∧
      _root_.DY.Libsignal.TripleRatchet.consumeMessageKey
        (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey
          ((runTraceMoves r ms₁).length + 2)).2 msg.counter = some (seed_ratch, c_ratch') ∧
      recvSeed st₀ msg = some seed_ratch ∧
      k_own ∈ ownKeys r (runTraceMoves r ms₁) st₀ msg ∧
      gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
        (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_ratch).macKey
        st₀.peerIk st₀.myIk msg.wire) = gamma interp' S g₁ msg.mac := by
  let recBytes := encodeRecordUnderExtras (fun _ => x) g_st
  let sess := pqSession x g_st
  let g_rw := promGhost recBytes sess
  have hceh := hext'.1
  obtain ⟨_hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀,
      hks₀, _hnd₀⟩ := hrsi me recBytes hrec
  obtain ⟨_hnp_eq, hrel₀_sess, _, _, _, _, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interp' S g₁ recBytes rec₀ st₀ st₀
      g_rw hrecBytes₀ hrel₀ hcan_q rfl
  obtain ⟨hFindNone, _⟩ :=
    TR.PureRecvEval.pureDrawsCoins_cases (cryptoOf' interp') sess.state inner.senderRatchetKey hdraws
  have hFindNone' :
      (Proofs.libsignal.RngG.R3.ratchetStateOf (pqSession x g_st).state).findReceiverChainKey
        inner.senderRatchetKey = .ok none := hFindNone
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, hVer, hRem, hSpqr', _hDec, _hSt', hBr⟩ :=
    Proofs.libsignal.RngG.R3.decryptW_ok_branch hdecW
  have hrecv_spqr : (spqrModelOf interp').recv sess.state.pqRatchetState inner.pqRatchet =
      .ok (newPqrState, pqrKey) := hSpqr'
  cases hBr with
  | skipped ck' hFind _ _ _ =>
    rw [hFindNone'] at hFind; cases hFind
  | existing ck' _ _ _ hFind _ _ _ _ _ _ _ =>
    rw [hFindNone'] at hFind; cases hFind
  | ratchet ck ck_adv ck_next r1 r_adv _hFind hDh hNotLt hJump hAdv hNext hSet hMkGen hMac =>
    let rngBytes := HMAC.keyToBytes32 rc
    have hrng_len : rngBytes.length = 32 := by simp [rngBytes, HMAC.keyToBytes32]
    have hDh' :
        Mut.exec
          (RatchetState.dhRatchetStep (cryptoOf' interp') inner.senderRatchetKey
            (RpkCli.pinCoins (some rngBytes)))
          (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state) = (.ok ck, r1) := by
      dsimp [g_rw, promGhost]
      rwa [pinCoins_keyToBytes32 rc]
    have hctr₀ : msg.counter = UInt32.ofBitVec inner.counter :=
      UInt32.ext (((ht.2.2.2 msg hparse).2.2.2 inner htry).2.2.2.1)
    let ts := (runTraceMoves r ms₁).length + 2
    let g' : Ghost := { g₁ with σ := Symbolic.Swarm.CREF.TR.FreshSigma.updateFreshAt g₁.σ ts 32 rngBytes }
    have hmp_nil : MatchedPrefix interp' r S who g₁ ms₁ (τ_pre ++ []) := by
      simpa only [List.append_nil] using hmp
    obtain ⟨hRng, hmp', _hrsi', hrel₀', hks₀', _hst_lt, _hmsg_lt, _ht_gam, _hwire_gam, _hmac_gam,
        _hrk_gam, _hct_gam, _hpq_gam, _hspqr_gam, _hrecv_gam⟩ :=
      TR.PureRecvEval.pureRatchetDH_sigma_bridge interp' r hwf S slots g₁ ms₁ (τ_pre ++ [])
        rec_fn me stateIdx₀ st₀ (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec g_rw.sess)
        t msg ts rngBytes (by omega) hmp_nil hrsi hst₀ hrel₀_sess hks₀ ht.1 hparse
    obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
      TR.SendRetCoins.stateRel_sessionToRecordRec_extract_TR interp' S g' st₀ g_rw.sess hrel₀'
    have hst₀_rci : Symbolic.Swarm.CREF.TR.RecvDecStep.TrStateRkCkIk r st₀ :=
      Symbolic.Swarm.CREF.TR.RecvDecStep.trStateRkCkIk_of_getLocalState hmp'.2.1 hst₀
    have hRkLen : (gamma interp' S g' st₀.rk).length = 32 :=
      hst₀_rci.rk_len interp' S g' hwf hmp'.1
    have hCkLens : ∀ c ∈ st₀.recv, (gamma interp' S g' c.chainKey).length = 32 :=
      hst₀_rci.recv_ck_len interp' S g' hwf hmp'.1
    have hTheir' : inner.senderRatchetKey.bytes.toList = gamma interp' S g' msg.ratchetKey :=
      ((ht.2.2.2 msg hparse).2.2.2 inner htry).2.1.symm.trans _hrk_gam.symm
    have hPkLen : (gamma interp' S g' msg.ratchetKey).length = 32 :=
      hTheir' ▸ inner.senderRatchetKey.bytes.2
    have hTheir : inner.senderRatchetKey = ⟨vec32 (gamma interp' S g' msg.ratchetKey)⟩ := by
      cases hmk : inner.senderRatchetKey with | mk b =>
      have hb : b.toList = (vec32 (gamma interp' S g' msg.ratchetKey)).toList := by
        rw [hmk] at hTheir'
        exact hTheir'.trans
          (TR.RecvDecStep.vec32_toList_of_length_eq_tr hPkLen).symm
      exact congrArg PublicKey.mk (Subtype.ext hb)
    have ht₀' : t ∈ recvRepresentations interp' r S g' ms₁ inner_wire := by
      refine ⟨ht.1, _ht_gam.trans ht.2.1, ht.2.2.1, fun m0 hm0 => ?_⟩
      rcases Option.some.inj (hparse.symm.trans hm0) with rfl
      have h₀ := ht.2.2.2 msg hparse
      refine ⟨_hwire_gam.trans h₀.1, _hmac_gam.trans h₀.2.1, h₀.2.2.1, fun parsed hparsed => ?_⟩
      have hp := h₀.2.2.2 parsed hparsed
      exact ⟨_hct_gam.trans hp.1, _hrk_gam.trans hp.2.1, _hpq_gam.trans hp.2.2.1, hp.2.2.2⟩
    have hJump' : (inner.counter - ck.index).toNat ≤ maxForwardJumps := by
      obtain ⟨_, _, _, _, _, _, _, hr1⟩ := Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh'
      rw [hr1] at hJump; exact hJump
    obtain ⟨hfind₀, _mks', seed, c', hcons₀_bv, hSeedEq, hCntEq,
        _hc'_rk, _hc'_rIdx, _hc_idx0, _hc_rIdx, _hR2Eq', _hRel_lit, _hRcMem, _hMks'⟩ :=
      TR.RecvDecStep.stateRel_and_consumeMessageKey_of_dhRatchetStep_tr interp' S g' hceh
        (hrel := hrel₀') (hRkLen := hRkLen) (hDhsLen := hks₀'.dhs_len) (hCkLens := hCkLens)
        (hTheir := hTheir) (hPkLen := hPkLen) (hRng := hRng) (hRngLen := hrng_len)
        (hspqr' := TR.SendRetCoins.gamma_litOf interp' S g' newPqrState)
        (hFindNone := hFindNone') (hStep := hDh')
        (hNotLt := hNotLt) (hJump := hJump') (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
    have hcons₀ :
        _root_.DY.Libsignal.TripleRatchet.consumeMessageKey
          (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2 msg.counter =
          some (seed, c') := by
      rw [hctr₀]; exact hcons₀_bv
    have hlow₀ : _root_.DY.X25519.x25519LowOrder msg.ratchetKey = false :=
      TR.RecvDecStep.x25519LowOrder_false_of_dhRatchetStep_ok_tr
        interp' S g' hceh (hTheir := hTheir') (hDh := hDh')
    have hst_avail : st₀ ∈ availableStates r (runTraceMoves r ms₁) :=
      Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms₁
        (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
    let k_own : _root_.DY.Bytes :=
      ({ st := st₀.spqr, msg := msg.pqRatchet } : _root_.DY.Spqr.RecvKey.SubF _root_.DY.Bytes).pack
    have hk_own : k_own ∈ ownKeys r (runTraceMoves r ms₁) st₀ msg := by
      unfold ownKeys
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst_avail, beq_self_eq_true _⟩)
    have hpq_sess : g_rw.sess.state.pqRatchetState = gamma interp' S g' st₀.spqr :=
      congrArg _root_.DY.Libsignal.Rust.SessionRec.pqRatchetState hrel₀'.2
    have hver_sess : g_rw.sess.state.sessionVersion = 4#32 :=
      congrArg _root_.DY.Libsignal.Rust.SessionRec.sessionVersion hrel₀'.2
    have hk_own_gam :=
      (TR.RecvDecStep.spqrRecv_step_gamma_state_and_key
        interp' hceh r S hS g' ms₁ inner_wire st₀ g_rw t msg inner
        newPqrState pqrKey hpq_sess ht₀' hparse htry hrecv_spqr).2
    have hver₀_nat : msg.version.toNat = inner.messageVersion.toNat :=
      ((ht₀'.2.2.2 msg hparse).2.2.2 inner htry).2.2.2.2
    have hver_g : g_rw.sess.state.version.toNat = 4 := by
      unfold SessionState.version; rw [hver_sess]; rfl
    have hver₀ : msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion :=
      UInt8.ext (hver₀_nat.trans (hVer.symm.trans hver_g))
    have hseed : recvSeed st₀ msg = some seed := by
      unfold recvSeed
      simp only [hver₀, ↓reduceIte, _root_.DY.Libsignal.TripleRatchet.recvChainFor,
        hfind₀, hlow₀, Bool.false_eq_true]
      change Option.map Prod.fst
        (_root_.DY.Libsignal.TripleRatchet.consumeMessageKey
          (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2 msg.counter) =
        some seed
      rw [hcons₀]; rfl
    have hmkGen_eq : mkGen = ⟨gamma interp' S g' seed, inner.counter⟩ := by
      rw [hMkGen]
      change ck_adv.messageKeys (_root_.DY.Libsignal.Refinement.sha256CompressFunction interp') = _
      rcases h : ck_adv.messageKeys (_root_.DY.Libsignal.Refinement.sha256CompressFunction interp') with ⟨sd, ct⟩
      rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
    obtain ⟨_hck_mk, hmk_mk, _hiv_mk, _⟩ :=
      TR.SendRetCoins.gamma_trMsgKeys_eq_generateKeys interp' S g' k_own seed inner.counter pqrKey hk_own_gam
    dsimp [g_rw, promGhost, sess] at hrem0
    have hRem' : g_st.session.remoteIdentity = some remIk := hRem
    rw [hRem'] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
    have hpeer_ser : remIk.serialize = gamma interp' S g' st₀.peerIk :=
      hrem_ser.trans hks₀'.peerIk_ser
    have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interp' S g' st₀.myIk :=
      hloc_ser.trans hks₀'.myIk_ser
    have hwire₀_take : gamma interp' S g' msg.wire = inner_wire.take (inner_wire.length - 8) :=
      (ht₀'.2.2.2 msg hparse).1
    have hm_ser : inner.serialized = inner_wire :=
      Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.tryFrom_serialized_eq_slotG2 htry
    have hMacBytes :
        inner_wire.drop (inner_wire.length - 8) =
          gamma interp' S g' (_root_.DY.Libsignal.TripleRatchet.computeMac
            (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed).macKey
            st₀.peerIk st₀.myIk msg.wire) := by
      have hmac_ver : inner.verifyMac (cryptoOf' interp').F remIk g_rw.sess.state.localIdentity
          (mkGen.generateKeys (cryptoOf' interp').F pqrKey).macKey = true :=
        ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
      unfold SignalMessage.verifyMac macLength at hmac_ver
      dsimp only at hmac_ver
      have hmac_eq := (beq_iff_eq.mp hmac_ver).symm
      rw [hm_ser] at hmac_eq; rw [hmac_eq]
      have hkey_mk : HMAC.keyToBytes32 ((mkGen.generateKeys (cryptoOf' interp').F pqrKey).macKey) =
          gamma interp' S g' (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed).macKey := by
        rw [hmkGen_eq]; exact hmk_mk
      exact TR.SendRetCoins.gamma_computeMac_tr interp' S g'
        (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed).macKey
        st₀.peerIk st₀.myIk msg.wire remIk g_rw.sess.state.localIdentity
        ((mkGen.generateKeys (cryptoOf' interp').F pqrKey).macKey)
        hkey_mk hpeer_ser hmy_ser (inner_wire.take (inner_wire.length - 8)) hwire₀_take.symm
    have hc_lt : Symbolic.Swarm.CREF.TR.FreshSigma.ChainStampsLt interp' S g₁ ts
        (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2 :=
      ⟨_hmsg_lt.2.2.1,
        (Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_createChain
          _hst_lt.2.2.1 _hmsg_lt.2.2.1 _hst_lt.2.2.2.1).2⟩
    have hseed_lt : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp' S g₁ ts seed :=
      (Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_consumeMessageKey hc_lt hcons₀).1
    have hk_own_lt : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp' S g₁ ts k_own :=
      (Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_spqrRecvKey_pack interp' S g₁ ts
        ⟨st₀.spqr, msg.pqRatchet⟩).mpr ⟨_hst_lt.2.2.2.2.2.1, _hmsg_lt.2.2.2.2⟩
    have hkeys_lt := Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_trMsgKeys hk_own_lt hseed_lt
    have hmac_term_lt := Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_computeMac
      hkeys_lt.2.1 _hst_lt.2.1 _hst_lt.1 _hmsg_lt.1
    have hMacBytes₁ :
        gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
          (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed).macKey
          st₀.peerIk st₀.myIk msg.wire) = gamma interp' S g₁ msg.mac := by
      rw [← Symbolic.Swarm.CREF.TR.FreshSigma.gamma_updateFreshAt_of_stampsLt
            interp' S g₁ ts 32 rngBytes _ hmac_term_lt,
          ← hMacBytes, (ht.2.2.2 msg hparse).2.1]
    exact ⟨stateIdx₀, st₀, seed, k_own, c', hst₀, hcur₀, hrel₀_sess, hFindNone,
      hver₀, hfind₀, hlow₀, hcons₀, hseed, hk_own, hMacBytes₁⟩

private theorem movesFrom_invisible_map_attackerSend (ext : List _root_.DY.Bytes)
    (tr : ExecTrace) :
    MovesFrom InvisibleNoEffect tr (ext.map .attackerSend) := by
  induction ext generalizing tr with
  | nil => trivial
  | cons u rest ih =>
    exact ⟨⟨vis_attackerSend_nil u tr, XplSteps.xpl_noEff_attackerSend u tr⟩,
      ih ((Move.attackerSend u).next tr)⟩

private theorem matchedPrefix_append_map_attackerSend
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g₁ : Ghost} {ms : List Move} {τ_pre : List MachineEvent}
    (ext : List _root_.DY.Bytes)
    (hext_kn : ∀ u ∈ ext, u.AttackerKnows (runTraceMoves r ms))
    (hmp : MatchedPrefix interp' r S who g₁ ms τ_pre) :
    MatchedPrefix interp' r S who g₁ (ms ++ ext.map .attackerSend) τ_pre := by
  induction ext generalizing ms with
  | nil => simpa using hmp
  | cons u rest ih =>
    have hcons : ms ++ (u :: rest).map Move.attackerSend =
        (ms ++ [.attackerSend u]) ++ rest.map Move.attackerSend := by
      simp [List.append_assoc]
    rw [hcons]
    have hmp₁ := matchedPrefix_attackerSend hmp (hext_kn u List.mem_cons_self)
    have hle := Symbolic.Swarm.CREF.runTrace_le_append r ms [.attackerSend u]
    exact ih (fun v hv =>
      _root_.DY.Bytes.AttackerKnows_le v _ _ hle (hext_kn v (List.mem_cons_of_mem u hv))) hmp₁

private theorem recvCollision_of_skipped_and_ratchet
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₁ : Ghost} {ms₁ : List Move} {me : Participant}
    {stateIdx₀ skIdx rIdx_s srcIdx : Nat}
    {st₀ : _root_.DY.Libsignal.TripleRatchet.TRState}
    {t seed_ratch k_own seed_s pqSalt : _root_.DY.Bytes}
    {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    {c_ratch' : _root_.DY.Libsignal.TripleRatchet.RecvChain}
    (hreach : (runTraceMoves r ms₁).Reachable _root_.DY.Libsignal.Composed.reachability)
    (hfresh : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r ms₁)
    (hme : me = r.alice ∨ me = r.bob)
    (hst₀ : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx₀ :
        _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₁)).1 =
      some st₀)
    (hcur₀ : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx₀ = true)
    (hparse : _root_.DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg)
    (hver : msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion)
    (hfind₀ : _root_.DY.Libsignal.TripleRatchet.findRecvChain st₀.recv msg.ratchetKey = none)
    (hlow₀ : _root_.DY.X25519.x25519LowOrder msg.ratchetKey = false)
    (hcons₀ : _root_.DY.Libsignal.TripleRatchet.consumeMessageKey
      (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey
        ((runTraceMoves r ms₁).length + 2)).2 msg.counter = some (seed_ratch, c_ratch'))
    (hseed : recvSeed st₀ msg = some seed_ratch)
    (hk_own : k_own ∈ ownKeys r (runTraceMoves r ms₁) st₀ msg)
    (hMacBytes : gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_ratch).macKey
      st₀.peerIk st₀.myIk msg.wire) = gamma interp' S g₁ msg.mac)
    (hsk : ((runTraceMoves r ms₁).at? skIdx :
        Option Symbolic.Swarm.COMPOSED.CompTrace.TREntry) =
      some ⟨_root_.DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
        (st₀.sessionInfo me) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩)
    (hmac_eq : msg.mac = _root_.DY.Libsignal.TripleRatchet.computeMac
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed_s).macKey
      st₀.peerIk st₀.myIk msg.wire)
    (hfind_sk : (_root_.DY.Libsignal.TripleRatchet.findRecvChain st₀.toDRState.recv msg.ratchetKey).isSome = true) :
    RecvCollision interp' r S g₁ ms₁ t := by
  have hst_av : st₀ ∈ availableStates r (runTraceMoves r ms₁) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms₁
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  by_cases hγ : gamma interp' S g₁ seed_ratch = gamma interp' S g₁ seed_s
  · by_cases hsh : (gamma' interp' S g₁ seed_ratch).shape = (gamma' interp' S g₁ seed_s).shape
    · exact False.elim (seed_shape_eq_contradicts_freshAll hreach hfresh hme hst₀ hcur₀ hcons₀ hsk hsh)
    · obtain ⟨ks, ms_, hs_form⟩ := TR.RecvDecStep.a2b_skippedSeed_hmac hreach hsk
      obtain ⟨kc, mc, hc_form⟩ := TR.RecvDecStep.a2b_consume_seed_hmac hcons₀
      exact TR.RecvDecStep.a2b_recvCollision_of_seed_shape_ne interp' r S g₁ ms₁ [] t msg st₀
        hst_av seed_s seed_ratch pqSalt st₀.peerIk st₀.myIk ks ms_ kc mc hparse hmac_eq hseed
        hs_form hc_form hγ hsh
  · let c_fresh := (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey
      ((runTraceMoves r ms₁).length + 2)).2
    have hrc : _root_.DY.Libsignal.TripleRatchet.recvChainFor st₀.toDRState msg.ratchetKey =
        some (c_fresh, true) := by
      simp [_root_.DY.Libsignal.TripleRatchet.recvChainFor, hfind₀, hlow₀, c_fresh,
        Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]
    have hctx := Stage1Wire.mem_whisperTrials_of_recvChainFor_fresh
      (interpretation := interp') (S := S) (g := g₁) hver hst_av hrc
    have hseed_ctx : (Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg)
        c_fresh msg.counter).seed? = some seed_ratch := by
      unfold Stage1Wire.chainTrialCtx
      rw [hcons₀]
    have hMacCtx : gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
        (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_ratch).macKey
        (Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg) c_fresh msg.counter).peerIk
        (Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg) c_fresh msg.counter).myIk
        msg.wire) = gamma interp' S g₁ msg.mac := by
      have hp : (Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg) c_fresh msg.counter).peerIk =
          st₀.peerIk := by unfold Stage1Wire.chainTrialCtx; rw [hcons₀]
      have hm : (Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg) c_fresh msg.counter).myIk =
          st₀.myIk := by unfold Stage1Wire.chainTrialCtx; rw [hcons₀]
      rw [hp, hm]; exact hMacBytes
    have hsalts_ctx : k_own ∈ (Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg)
        c_fresh msg.counter).ownSalts := by
      unfold Stage1Wire.chainTrialCtx; rw [hcons₀]; exact hk_own
    have hsk_lt : skIdx < (runTraceMoves r ms₁).length := by
      by_contra hge
      rw [RpkCli.XplQuiet.at?_none_of_ge (by omega)] at hsk
      cases hsk
    have hget_sk : (runTraceMoves r ms₁).getEventAt _root_.DY.Libsignal.TripleRatchet.TREvent skIdx =
        some (.SkippedKeyStored (st₀.sessionInfo me) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx) := by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [hsk]
    have hctx₀ := Stage1Wire.mem_whisperTrials_of_skippedKeyStored
      (interpretation := interp') (S := S) (g := g₁) hver hst_av hfind_sk hsk_lt hget_sk rfl rfl
    exact Stage1Wire.recvCollision_of_ownSaltMacCollision hparse
      (Stage1Wire.ownSaltMacCollision_of_cross_seed_term
        hctx hseed_ctx hsalts_ctx hMacCtx hctx₀ rfl hγ hmac_eq rfl)

theorem bridgeC_caseB : BridgeCCaseBSpec := by
  intro interp P r who ok records sent accepted τ_pre τ₂ σ_rest me st st' d_me x g_st
    w inner_wire out inner rc g ms t_rep τ₂_tl
    interp' S hext hagree hwf hwho hcrel hclean hbin hdraws ht_rep _hcs hτ₂ hacc
  by_contra hnocol
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  obtain ⟨_tag, _w_tl, _msgType, s', _hw_eq, _hrb, hcan_q, hdecW⟩ :=
    binarySessionDecryptOk_tryDecryptW hagree hbin
  obtain ⟨hme, _hinvP, hwf_st, hsess, hrec_me, _hlen_rec, _hfrom, htry, _hbranch⟩ := hbin
  obtain ⟨ext, m, msgIdx, k, pt, g₁, hext_kn, hm_idx, haddr, hσ, hget, hk, hrng_take, hExpl⟩ := hacc
  subst hτ₂
  have hk0 : k = 0 := by
    cases k with
    | zero => rfl
    | succ k' => simp [eventKind] at hrng_take
  subst hk0
  simp only [List.getElem?_cons_zero, Option.some.injEq, MachineEvent.accept.injEq] at hk
  subst hk
  simp only [Nat.zero_add, List.take_succ_cons, List.take_zero] at hExpl
  let pre := ext.map Move.attackerSend
  let ms₁ := ms ++ pre
  have hfr : CBadSigmaFrame g g₁ (runTraceMoves r ms).length :=
    ⟨fun ts hts len => congrFun (hσ ts hts) len, haddr⟩
  have hc_by : CleanBy interp' r S who ok g ms τ_pre := hclean
  have hc₁ : CleanBy interp' r S who ok g₁ ms τ_pre :=
    cbadG2_cleanBy_transfer hfr hc_by
  have ht_rep₁_ms : t_rep ∈ recvRepresentations interp' r S g₁ ms inner_wire :=
    cbadG2_recvRep_of_sigmaFrame hfr hc_by.matched ht_rep
  have hnc₁_ms : ¬ RecvCollision interp' r S g₁ ms t_rep :=
    cbadG2_notRecvCollision_of_sigmaFrame hfr hc_by.matched ht_rep.1 hnocol
  have hnc₁ : ¬ RecvCollision interp' r S g₁ ms₁ t_rep :=
    not_recvCollision_append_map_attackerSend ext hext_kn hnc₁_ms
  have ht_rep₁ : t_rep ∈ recvRepresentations interp' r S g₁ ms₁ inner_wire :=
    ⟨_root_.DY.Bytes.AttackerKnows_le t_rep _ _
      (Symbolic.Swarm.CREF.runTrace_le_append r ms pre) ht_rep₁_ms.1, ht_rep₁_ms.2⟩
  have hmp₁ : MatchedPrefix interp' r S who g₁ ms₁ τ_pre :=
    matchedPrefix_append_map_attackerSend ext hext_kn hc₁.matched
  have hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms) pre :=
    movesFrom_invisible_map_attackerSend ext (runTraceMoves r ms)
  have hq : RpkCli.XplQuiet.QuietExt (runTraceMoves r ms) (runTraceMoves r ms₁) := by
    dsimp only [ms₁]
    rw [Symbolic.Swarm.CREF.runTrace_append]
    exact RpkCli.XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  obtain ⟨⟨hrec_at, _hbook_at, _hhist_at, hrole_ms⟩, _hbks⟩ := hcrel.clean g₁ ms hc₁
  have hrole₁ : RoleSnapshots r (runTraceMoves r ms₁) :=
    Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure.a2b_roleSnapshots_of_quietPre hpre hrole_ms
  have hfresh₀ : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r ms :=
    Symbolic.Swarm.CREF.trRecvFreshAll_of_matchedPrefix interp' hc₁.matched
  have hfresh₁ : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r ms₁ :=
    Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure.a2b_trRecvFreshAll_of_quietExt hq hfresh₀
  let recBytes := encodeRecordUnderExtras (fun _ => x) g_st
  obtain ⟨_hme_at, _hne_rec, hcrelH_ms⟩ := hrec_at me recBytes hrec_me
  have hss : SingleSession recBytes :=
    Symbolic.Swarm.CREF.Cli.Slots.singleSession_encodeRecordX_of_wfPq hwf_st hsess
  have hcrel_ms : PureCRecRel interp' r S g₁ ms me recBytes :=
    pureCRecRelH_single hcrelH_ms hss
  have hcrel_ms₁ : PureCRecRel interp' r S g₁ ms₁ me recBytes :=
    RpkCli.XplQuiet.quiet_pureCRecRel hq hcrel_ms
  have hrsi_ex : ∃ slots, Symbolic.Swarm.CREF.TR.PureTRRecordStateInv interp' r S slots g₁ ms₁
      (fun q => if q = me then some recBytes else none) := by
    rcases hcrel_ms₁ with hrsi | ⟨hme_alice, hpend⟩
    · exact ⟨pureTrSlots r, hrsi⟩
    · exact ⟨Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure.pureTrSlotsPend r,
        Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure.trRecordStateInv_pend_of_aliceInitPending
          hme_alice hpend⟩
  obtain ⟨slots, hrsi⟩ := hrsi_ex
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht_rep₁.2.2.1
  obtain ⟨stateIdx₀, st₀, seed_ratch, k_own, c_ratch', hst₀, hcur₀, _hrel₀_sess, _hFindNone,
      hver₀, hfind₀, hlow₀, hcons₀, hseed, hk_own, hMacBytes⟩ :=
    ratchet_mac_of_tryDecryptW (me := me) hext' hwf rfl hmp₁ hrsi (by simp only [↓reduceIte]; rfl) hcan_q htry hdraws hdecW
      ht_rep₁ hparse₀
  let blk : List MachineEvent := [.recv w, .accept out]
  have hfull_match : List.Forall₂ (EventMatchesEntry interp' r S g₁)
      (τ_pre ++ blk) (runVis r ms₁ ++ (runMoves [m] (runTraceMoves r ms₁)).2) := by
    rw [← Symbolic.Swarm.CREF.runVis_append]
    exact hExpl.1.2.2.2.2.2
  have hblk_match : List.Forall₂ (EventMatchesEntry interp' r S g₁)
      blk (runMoves [m] (runTraceMoves r ms₁)).2 :=
    (xpl_forall₂_append_split hmp₁.2.2.2.2.2.length_eq hfull_match).2
  have hmatch_m : List.Forall₂ (EventMatchesEntry interp' r S g₁) blk (m.vis (runTraceMoves r ms₁)) := by
    simpa [runMoves] using hblk_match
  have hB₁ : XplBlock interp' r S who g₁ ms₁ ([] ++ m :: []) τ_pre blk :=
    ⟨hmp₁, hExpl.1.2.1, hblk_match⟩
  have hacc_blk : ∃ e ∈ blk, eventKind e = .accept := ⟨.accept out, by simp [blk], rfl⟩
  have hcur_m := Symbolic.Swarm.CREF.TR.rcvCurrentSnapshot_of_xplBlock hB₁ trivial trivial hacc_blk
  have hparty_eq : ∀ p, m.party? = some p → p = me := by
    intro p hp
    have hget_m : (ms₁ ++ [m])[ms₁.length]? = some m := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have hrf := hExpl.1.2.2.1 ms₁.length m p hget_m hp
    rw [List.take_left, Symbolic.Swarm.CREF.callCount_eq_callStarts_length hmp₁.2.2.2.2.2, hwho] at hrf
    exact Option.some.inj hrf.symm
  have hreach₁ : (runTraceMoves r ms₁).Reachable _root_.DY.Libsignal.Composed.reachability :=
    b5_modelRun_reachable hmp₁.2.1
  cases m with
  | decrypt p stateIdx msgIdx' pqIdx spqrMsgIdx wrapped =>
    have hp : p = me := hparty_eq p rfl
    subst hp
    simp only [Move.decryptMsgIdx?, Option.some.injEq] at hm_idx
    subst hm_idx
    have hcur_idx : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx = true := by
      simpa using hcur_m
    have hno_rng : ∀ e ∈ blk, eventKind e ≠ .rng := by
      intro e he
      simp only [blk, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> intro h <;> cases h
    obtain ⟨st_m, t_m, msg_m, c_m, _c_m', _seed_m, _spqr_m, _key_m, _pqSalt_m, _ptTerm_m,
        hst_m, hmsg_m, hparse_m, _hver_m, _hrcf_m, hfind_m, _hidx_m, _hcons_m, _hspqr_m,
        _hpqSalt_m, _hmac_m, _hdec_m, _hpt_m⟩ :=
      noRatchet_of_matched hmatch_m hno_rng hacc_blk
    have hidx_eq : stateIdx = stateIdx₀ :=
      TR.RecvDecStep.a2b_currentSnapshot_unique_of_role hrole₁ hst_m hst₀ hcur_idx hcur₀
    subst hidx_eq
    have hst_eq : st_m = st₀ := Option.some.inj (hst_m.symm.trans hst₀)
    subst hst_eq
    have ht_eq : t_m = t_rep := Option.some.inj (hmsg_m.symm.trans hget)
    subst ht_eq
    have hmsg_eq : msg_m = msg₀ := Option.some.inj (hparse_m.symm.trans hparse₀)
    subst hmsg_eq
    rw [hfind₀] at hfind_m
    cases hfind_m
  | decryptSkipped p stateIdx msgIdx' skIdx pqIdx spqrMsgIdx wrapped =>
    have hp : p = me := hparty_eq p rfl
    subst hp
    simp only [Move.decryptMsgIdx?, Option.some.injEq] at hm_idx
    subst hm_idx
    have hcur_idx : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx = true := by
      simpa using hcur_m
    have hacc_vis : ∃ v ∈ (Move.decryptSkipped p stateIdx msgIdx' skIdx pqIdx spqrMsgIdx wrapped).vis
        (runTraceMoves r ms₁), v.kind = .accept := by
      obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hmatch_m (.accept out) (by simp [blk])
      exact ⟨v, hv, hev.1.symm⟩
    obtain ⟨st_m, t_m, msg_m, seed_s, rIdx_s, srcIdx, _spqr_m, _key_m, pqSalt, _ptTerm_m,
        hst_m, hmsg_m, hparse_m, _hver_m, hsk, _hunused, _hspqr_m, _hpqSalt_m, hmac_eq,
        _hdec_m, _hpt_m, hfind_m⟩ :=
      skippedHit_of_decryptSkipped hacc_vis
    have hidx_eq : stateIdx = stateIdx₀ :=
      TR.RecvDecStep.a2b_currentSnapshot_unique_of_role hrole₁ hst_m hst₀ hcur_idx hcur₀
    subst hidx_eq
    have hst_eq : st_m = st₀ := Option.some.inj (hst_m.symm.trans hst₀)
    subst hst_eq
    have ht_eq : t_m = t_rep := Option.some.inj (hmsg_m.symm.trans hget)
    subst ht_eq
    have hmsg_eq : msg_m = msg₀ := Option.some.inj (hparse_m.symm.trans hparse₀)
    subst hmsg_eq
    exact hnc₁ (recvCollision_of_skipped_and_ratchet hreach₁ hfresh₁ hme hst₀ hcur₀ hparse₀
      hver₀ hfind₀ hlow₀ hcons₀ hseed hk_own hMacBytes hsk hmac_eq hfind_m)
  | _ => cases hm_idx

end Symbolic.Swarm.Coinsplit.Lift.L06
