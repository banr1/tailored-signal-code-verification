/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Lift.Defs
import Batteries.Data.UInt
import DY.ALaCarte.Basic
import DY.Actions.ProtocolEvent
import DY.Bytes.Basic
import DY.EquationalTheory.KdfExtract
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.A2bSameOriginPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptCollisionPickPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSkippedG1LeavesPure
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
import Symbolic.Proofs.Swarm.CREF.Xpl.RatchetHit
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# No-Ratchet Decrypt Collision Bridge

Proves `BridgeCCaseASpec`: when the binary session decrypts `inner_wire` without drawing
DH-ratchet coins (`pureDrawsCoins = false`), any `ModelAcceptsTermAfterCoinSplit` explanation
on `(g, ms)` whose cut draws `.rng rb` before `.accept out` yields `RecvCollision interp' r S g ms t_rep`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.Coinsplit.Lift.L05

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

private theorem mem_blk_of_rng_cons_accept
    {w rb pt : HwBytes} {τ₂ τ₂_tl : List MachineEvent} {k : Nat}
    (hτ₂ : τ₂ = .rng rb :: τ₂_tl)
    (hk : τ₂[k]? = some (.accept pt)) :
    MachineEvent.rng rb ∈ (MachineEvent.recv w :: τ₂.take (k + 1)) ∧
      MachineEvent.accept pt ∈ (MachineEvent.recv w :: τ₂.take (k + 1)) := by
  subst hτ₂
  cases k with
  | zero => simp at hk
  | succ k' =>
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk
    refine ⟨List.mem_cons_of_mem _ (by simp), List.mem_cons_of_mem _ ?_⟩
    rw [List.mem_take_iff_getElem]
    exact ⟨k' + 1, by simp at hlt ⊢; omega, hget⟩

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

private theorem existing_seed_shape_eq_false
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ : Ghost} {ms₁ : List Move}
    {me : Participant} {stateIdx₀ ts : Nat}
    {st₀ : _root_.DY.Libsignal.TripleRatchet.TRState}
    {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    {c c_ex' c_mod' : _root_.DY.Libsignal.TripleRatchet.RecvChain}
    {seed_ex seed_mod : _root_.DY.Bytes}
    (hreach : (runTraceMoves r ms₁).Reachable _root_.DY.Libsignal.Composed.reachability)
    (hst₀ : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx₀ :
        _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₁)).1 =
      some st₀)
    (hc_mem : c ∈ st₀.recv)
    (hcons_ex : _root_.DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter =
      some (seed_ex, c_ex'))
    (hcons_mod : _root_.DY.Libsignal.TripleRatchet.consumeMessageKey
      (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2 msg.counter =
      some (seed_mod, c_mod'))
    (hsh : (gamma' interp' S g₁ seed_ex).shape = (gamma' interp' S g₁ seed_mod).shape) :
    False := by
  have hInv := Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach
  have hst₀_at : Symbolic.Swarm.COMPOSED.CompTrace.TRStateStoredAt me st₀ stateIdx₀ (runTraceMoves r ms₁) :=
    Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀
  obtain ⟨hpos₀, _hpar₀, _, ⟨_doneIdx_c, ikm_c, dh₁_c, _hs_c, hrk₀, _, hrecv_c⟩, _⟩ :=
    hInv.stateOK me st₀ stateIdx₀ hst₀_at
  let cNew := (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2
  have hroot_c : Symbolic.Swarm.COMPOSED.CompRatchet.CompChainRootFrom1 dh₁_c ikm_c (st₀.rIdx + 1)
      (_root_.DY.Libsignal.TripleRatchet.createChain st₀.rk msg.ratchetKey st₀.dhs).2 :=
    Symbolic.Swarm.COMPOSED.CompRatchet.CompChainRootFrom1.of_step_pos hpos₀ hrk₀ msg.ratchetKey st₀.dhs
  have hcNew_sched : Symbolic.Swarm.COMPOSED.CompRatchet.CompRecvChainScheduleOK dh₁_c ikm_c
      st₀.initiator (st₀.rIdx + 2) cNew := by
    refine ⟨by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      (_root_.DY.Libsignal.TripleRatchet.createChain st₀.rk msg.ratchetKey st₀.dhs).2, hroot_c, rfl⟩
  obtain ⟨_, _, _, _, _, ck₀_mod, hroot_mod, _hck_mod, hseed_mod, _⟩ :=
    Symbolic.Swarm.COMPOSED.CompRatchet.consumeMessageKey_compSchedule hcNew_sched hcons_mod
  have hrIdx_cNew : cNew.rIdx - 1 = st₀.rIdx + 1 := rfl
  rw [hrIdx_cNew] at hroot_mod
  have hc_sched := hrecv_c c hc_mem
  have hc_pos : 1 ≤ c.rIdx := hc_sched.1
  have hc_le : c.rIdx ≤ st₀.rIdx := hc_sched.2.1
  obtain ⟨_, _, _, _, _, ck₀_ex, hroot_ex, _hck_ex, hseed_ex, _⟩ :=
    Symbolic.Swarm.COMPOSED.CompRatchet.consumeMessageKey_compSchedule hc_sched hcons_ex
  have hsh_ck₀ :
      (gamma' interp' S g₁ ck₀_ex).shape = (gamma' interp' S g₁ ck₀_mod).shape :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.shape_chainKeyAt_inj' interp' S g₁ msg.counter.toNat
      (Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.shape_kdfCk_snd_inj' interp' S g₁
        (by rwa [← hseed_ex, ← hseed_mod]))
  have hm_eq : c.rIdx - 1 = st₀.rIdx + 1 :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.compChainRootFrom1_depth_eq_of_shape_eq
      interp' S g₁ hroot_ex hroot_mod hsh_ck₀
  omega

private theorem skipped_seed_shape_eq_false
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ : Ghost} {ms₁ : List Move}
    {me : Participant} {stateIdx₀ skIdx rIdx_s srcIdx ts : Nat}
    {st₀ : _root_.DY.Libsignal.TripleRatchet.TRState}
    {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    {pk_s seed_s seed_mod : _root_.DY.Bytes}
    {c_mod' : _root_.DY.Libsignal.TripleRatchet.RecvChain}
    (hreach : (runTraceMoves r ms₁).Reachable _root_.DY.Libsignal.Composed.reachability)
    (hfresh : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r ms₁)
    (hme : me = r.alice ∨ me = r.bob)
    (hst₀ : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx₀ :
        _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₁)).1 =
      some st₀)
    (hcur₀ : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx₀ = true)
    (hsk : ((runTraceMoves r ms₁).at? skIdx : Option Symbolic.Swarm.COMPOSED.CompTrace.TREntry) =
      some ⟨_root_.DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
        (st₀.sessionInfo me) pk_s msg.counter seed_s rIdx_s srcIdx⟩)
    (hcons_mod : _root_.DY.Libsignal.TripleRatchet.consumeMessageKey
      (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2 msg.counter =
      some (seed_mod, c_mod'))
    (hsh : (gamma' interp' S g₁ seed_s).shape = (gamma' interp' S g₁ seed_mod).shape) :
    False := by
  have hInv := Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach
  have hst₀_at : Symbolic.Swarm.COMPOSED.CompTrace.TRStateStoredAt me st₀ stateIdx₀ (runTraceMoves r ms₁) :=
    Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀
  obtain ⟨hpos₀, _hpar₀, _, ⟨_doneIdx_c, ikm_c, dh₁_c, hs_c, hrk₀, _, _⟩, _⟩ :=
    hInv.stateOK me st₀ stateIdx₀ hst₀_at
  let cNew := (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2
  have hroot_c : Symbolic.Swarm.COMPOSED.CompRatchet.CompChainRootFrom1 dh₁_c ikm_c (st₀.rIdx + 1)
      (_root_.DY.Libsignal.TripleRatchet.createChain st₀.rk msg.ratchetKey st₀.dhs).2 :=
    Symbolic.Swarm.COMPOSED.CompRatchet.CompChainRootFrom1.of_step_pos hpos₀ hrk₀ msg.ratchetKey st₀.dhs
  have hcNew_sched : Symbolic.Swarm.COMPOSED.CompRatchet.CompRecvChainScheduleOK dh₁_c ikm_c
      st₀.initiator (st₀.rIdx + 2) cNew := by
    refine ⟨by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      by dsimp [cNew, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]; omega,
      (_root_.DY.Libsignal.TripleRatchet.createChain st₀.rk msg.ratchetKey st₀.dhs).2, hroot_c, rfl⟩
  obtain ⟨_, _, _, _, _, ck₀_mod, hroot_mod, _hck_mod, hseed_mod, _⟩ :=
    Symbolic.Swarm.COMPOSED.CompRatchet.consumeMessageKey_compSchedule hcNew_sched hcons_mod
  have hrIdx_cNew : cNew.rIdx - 1 = st₀.rIdx + 1 := rfl
  rw [hrIdx_cNew] at hroot_mod
  rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hsk
  obtain ⟨_hs_pos, _, _doneIdx_s, ikm_s, dh₁_s, ck₀_s, hs_s, hroot_s, hseed_s⟩ :=
    hInv.eventOK (_root_.DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
      (st₀.sessionInfo me) pk_s msg.counter seed_s rIdx_s srcIdx) ⟨skIdx, hsk⟩
  obtain ⟨rfl, rfl⟩ :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.compSessionAt_same_sinfo_eq hs_c hs_s
  have hsh_ck₀ :
      (gamma' interp' S g₁ ck₀_s).shape = (gamma' interp' S g₁ ck₀_mod).shape :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.shape_chainKeyAt_inj' interp' S g₁ msg.counter.toNat
      (Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.shape_kdfCk_snd_inj' interp' S g₁
        (by rwa [← hseed_s, ← hseed_mod]))
  have hm_eq : rIdx_s - 1 = st₀.rIdx + 1 :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.compChainRootFrom1_depth_eq_of_shape_eq
      interp' S g₁ hroot_s hroot_mod hsh_ck₀
  have hrIdx_le : rIdx_s ≤ st₀.rIdx :=
    (hfresh me stateIdx₀ st₀ hme hst₀ hcur₀).1.2.2.1 _ _ _ _ _ _ hsk
  omega

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

private theorem recvCollision_of_binTrial_and_modelRatchet
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₁ : Ghost} {ms₁ : List Move}
    {st₀ : _root_.DY.Libsignal.TripleRatchet.TRState}
    {t : _root_.DY.Bytes}
    {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    {ctx_bin : TrialCtx}
    {seed_bin k_own seed_mod pqSalt_mod : _root_.DY.Bytes}
    {c_fresh c_mod' : _root_.DY.Libsignal.TripleRatchet.RecvChain}
    (hst_av : st₀ ∈ availableStates r (runTraceMoves r ms₁))
    (hparse : _root_.DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg)
    (hver : msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion)
    (hctx_bin : ctx_bin ∈ whisperTrials interp' r S g₁ (runTraceMoves r ms₁) msg)
    (hseed_bin : ctx_bin.seed? = some seed_bin)
    (hk_own_bin : k_own ∈ ctx_bin.ownSalts)
    (hpeer_bin : ctx_bin.peerIk = st₀.peerIk)
    (hmy_bin : ctx_bin.myIk = st₀.myIk)
    (hmac_bin : gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_bin).macKey
      st₀.peerIk st₀.myIk msg.wire) = gamma interp' S g₁ msg.mac)
    (hbin_hmac : ∃ kb mb, seed_bin = _root_.DY.Libsignal.TripleRatchet.hmac kb mb)
    (hrcf_mod : _root_.DY.Libsignal.TripleRatchet.recvChainFor st₀.toDRState msg.ratchetKey =
      some (c_fresh, true))
    (hcons_mod : _root_.DY.Libsignal.TripleRatchet.consumeMessageKey c_fresh msg.counter =
      some (seed_mod, c_mod'))
    (hmac_mod : msg.mac = _root_.DY.Libsignal.TripleRatchet.computeMac
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys pqSalt_mod seed_mod).macKey
      st₀.peerIk st₀.myIk msg.wire)
    (hno_shape_eq : (gamma' interp' S g₁ seed_bin).shape = (gamma' interp' S g₁ seed_mod).shape →
      False) :
    RecvCollision interp' r S g₁ ms₁ t := by
  by_cases hγ : gamma interp' S g₁ seed_bin = gamma interp' S g₁ seed_mod
  · by_cases hsh : (gamma' interp' S g₁ seed_bin).shape = (gamma' interp' S g₁ seed_mod).shape
    · exact False.elim (hno_shape_eq hsh)
    · obtain ⟨kb, mb, hb_form⟩ := hbin_hmac
      obtain ⟨km, mm, hm_form⟩ := TR.RecvDecStep.a2b_consume_seed_hmac hcons_mod
      unfold RecvCollision
      simp only [hparse]
      refine Or.inl ?_
      unfold MemoCollisionOn
      dsimp only
      have ht_cat := Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_eq_concat hparse
      have hm_t :
          (seed_mod, (gamma' interp' S g₁ seed_mod).shape, gamma interp' S g₁ seed_mod) ∈
            (gamma' interp' S g₁ t).memo := by
        rw [ht_cat]
        refine Symbolic.Swarm.CREF.TR.G1.memo_rhs_subset_memo_concat interp' S g₁ _ _ ?_
        rw [hmac_mod]
        exact TR.RecvDecStep.a2b_memo_mem_computeMac_seed interp' S g₁ _ _ _ _ _
          (TR.RecvDecStep.a2b_self_memo_of_hmac interp' S g₁ hm_form)
      have hb_rt :
          _root_.DY.Libsignal.TripleRatchet.computeMac
              (_root_.DY.Libsignal.TripleRatchet.trMsgKeys _root_.DY.Spqr.zeroKey seed_bin).macKey
              ctx_bin.peerIk ctx_bin.myIk msg.wire ∈
            (whisperTrials interp' r S g₁ (runTraceMoves r ms₁) msg).flatMap
              (trialTerms (honestSalts r ms₁) msg) :=
        List.mem_flatMap.mpr ⟨ctx_bin, hctx_bin,
          (Stage1Wire.keyTerms_sub_trialTerms hseed_bin (List.mem_cons_self ..)).2.2.2⟩
      have hb_new :
          (seed_bin, (gamma' interp' S g₁ seed_bin).shape, gamma interp' S g₁ seed_bin) ∈
            (t :: (whisperTrials interp' r S g₁ (runTraceMoves r ms₁) msg).flatMap
              (trialTerms (honestSalts r ms₁) msg)).flatMap
              (fun u => (gamma' interp' S g₁ u).memo) :=
        List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ hb_rt,
          TR.RecvDecStep.a2b_memo_mem_computeMac_seed interp' S g₁ _ _ _ _ _
            (TR.RecvDecStep.a2b_self_memo_of_hmac interp' S g₁ hb_form)⟩
      have hm_npt : seed_mod ∉ plaintextTerms (runVis r ms₁) := by
        have h := Symbolic.Swarm.CREF.TR.G1.not_mem_ptAtoms_of_view_random_isNone r ms₁ []
          (fun _ h => absurd h List.not_mem_nil) seed_mod (by
            subst hm_form
            show ((({ salt := km, ikm := mm } : _root_.DY.KdfExtract.KdfExtract.SubF _root_.DY.Bytes).pack).view? _root_.DY.Random.Random).isNone = true
            rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _root_.DY.Random.Random ({ salt := km, ikm := mm } : _root_.DY.KdfExtract.KdfExtract.SubF _root_.DY.Bytes)]; rfl)
        rwa [List.append_nil] at h
      have hb_npt : seed_bin ∉ plaintextTerms (runVis r ms₁) := by
        have h := Symbolic.Swarm.CREF.TR.G1.not_mem_ptAtoms_of_view_random_isNone r ms₁ []
          (fun _ h => absurd h List.not_mem_nil) seed_bin (by
            subst hb_form
            show ((({ salt := kb, ikm := mb } : _root_.DY.KdfExtract.KdfExtract.SubF _root_.DY.Bytes).pack).view? _root_.DY.Random.Random).isNone = true
            rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _root_.DY.Random.Random ({ salt := kb, ikm := mb } : _root_.DY.KdfExtract.KdfExtract.SubF _root_.DY.Bytes)]; rfl)
        rwa [List.append_nil] at h
      refine ⟨_, List.mem_flatMap.mpr ⟨t, List.mem_cons_self .., hm_t⟩,
        _, List.mem_append_right _ hb_new,
        fun h => hsh h.symm, Or.inl (by
          subst hm_form
          have hv : ((_root_.DY.Libsignal.TripleRatchet.hmac km mm).view? _root_.DY.KdfExtract.KdfExtract.SubF).isSome = true := by
            show ((({ salt := km, ikm := mm } : _root_.DY.KdfExtract.KdfExtract.SubF _root_.DY.Bytes).pack).view? _).isSome = true
            rw [_root_.DY.BytesView.view_pack]; rfl
          unfold assumedInjective; rw [hv]; simp), ?_, ?_, hγ.symm⟩
      · intro h; rw [List.append_nil] at h; exact absurd h hm_npt
      · intro h; rw [List.append_nil] at h; exact absurd h hb_npt
  · have hctx_mod := Stage1Wire.mem_whisperTrials_of_recvChainFor_fresh
      (interpretation := interp') (S := S) (g := g₁) hver hst_av hrcf_mod
    have hseed_mod_ctx : (Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg)
        c_fresh msg.counter).seed? = some seed_mod := by
      unfold Stage1Wire.chainTrialCtx
      rw [hcons_mod]
    have hmac_bin_ctx : gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
        (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_bin).macKey
        ctx_bin.peerIk ctx_bin.myIk msg.wire) = gamma interp' S g₁ msg.mac := by
      rw [hpeer_bin, hmy_bin]
      exact hmac_bin
    exact Stage1Wire.recvCollision_of_ownSaltMacCollision hparse
      (Stage1Wire.ownSaltMacCollision_of_cross_seed_term
        hctx_bin hseed_bin hk_own_bin hmac_bin_ctx hctx_mod hseed_mod_ctx hγ hmac_mod rfl)

private theorem binTrial_of_tryDecryptW_noDraws
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
    (hreach : (runTraceMoves r ms₁).Reachable _root_.DY.Libsignal.Composed.reachability)
    (hfresh : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r ms₁)
    (hme : me = r.alice ∨ me = r.bob)
    (hrsi : Symbolic.Swarm.CREF.TR.PureTRRecordStateInv interp' r S slots g₁ ms₁ rec_fn)
    (hrec : rec_fn me = some (encodeRecordUnderExtras (fun _ => x) g_st))
    (hcan_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
      Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q
      (encodeRecordUnderExtras (fun _ => x) g_st) (pqSession x g_st))
    (htry : SignalMessage.tryFrom protoSignalCodec inner_wire = .ok inner)
    (hdraws : pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state inner.senderRatchetKey = false)
    (hdecW : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
      (cryptoOf' interp') (interpW interp') (pureSpqr (spqrModelOf interp'))
      expected inner msgType rc (pqSession x g_st).state = (.ok out, s'))
    (ht : t ∈ recvRepresentations interp' r S g₁ ms₁ inner_wire)
    (hparse : _root_.DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg) :
    ∃ (stateIdx₀ : Nat) (st₀ : _root_.DY.Libsignal.TripleRatchet.TRState)
      (ctx_bin : TrialCtx) (seed_bin k_own : _root_.DY.Bytes),
      ((_root_.DY.PersistentLocalState.getLocalState me stateIdx₀ :
          _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₁)).1 =
        some st₀ ∧
      _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx₀ = true ∧
      msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion ∧
      ctx_bin ∈ whisperTrials interp' r S g₁ (runTraceMoves r ms₁) msg ∧
      ctx_bin.seed? = some seed_bin ∧
      k_own ∈ ctx_bin.ownSalts ∧
      ctx_bin.peerIk = st₀.peerIk ∧
      ctx_bin.myIk = st₀.myIk ∧
      gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
        (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_bin).macKey
        st₀.peerIk st₀.myIk msg.wire) = gamma interp' S g₁ msg.mac ∧
      (∃ kb mb, seed_bin = _root_.DY.Libsignal.TripleRatchet.hmac kb mb) ∧
      (∀ (ts : Nat) (seed_mod : _root_.DY.Bytes)
        (c_mod' : _root_.DY.Libsignal.TripleRatchet.RecvChain),
        _root_.DY.Libsignal.TripleRatchet.consumeMessageKey
          (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg.ratchetKey ts).2 msg.counter =
          some (seed_mod, c_mod') →
        (gamma' interp' S g₁ seed_bin).shape = (gamma' interp' S g₁ seed_mod).shape →
        False) := by
  let recBytes := encodeRecordUnderExtras (fun _ => x) g_st
  let sess := pqSession x g_st
  let g_rw := promGhost recBytes sess
  have hceh := hext'.1
  obtain ⟨_hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀,
      hks₀, hnd₀⟩ := hrsi me recBytes hrec
  have hnorm_eq : Symbolic.Swarm.CREF.TR.normPending rec₀ =
      Symbolic.Swarm.CREF.TR.normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcan_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  obtain ⟨_hnp_eq, hrel₀_sess, hpq_sess, _, _, hver_sess, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interp' S g₁ recBytes rec₀ st₀ st₀
      g_rw hrecBytes₀ hrel₀ hcan_q rfl
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, hVer, hRem, hSpqr', _hDec, _hSt', hBr⟩ :=
    Proofs.libsignal.RngG.R3.decryptW_ok_branch hdecW
  have hrecv_spqr : (spqrModelOf interp').recv g_rw.sess.state.pqRatchetState inner.pqRatchet =
      .ok (newPqrState, pqrKey) := hSpqr'
  have hst_av : st₀ ∈ availableStates r (runTraceMoves r ms₁) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms₁
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
    TR.SendRetCoins.stateRel_sessionToRecordRec_extract_TR interp' S g₁ st₀ g_rw.sess hrel₀_sess
  dsimp [g_rw, promGhost, sess] at hrem0
  have hRem' : g_st.session.remoteIdentity = some remIk := hRem
  rw [hRem'] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interp' S g₁ st₀.peerIk :=
    hrem_ser.trans hks₀.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interp' S g₁ st₀.myIk :=
    hloc_ser.trans hks₀.myIk_ser
  have hver₀_nat : msg.version.toNat = inner.messageVersion.toNat :=
    ((ht.2.2.2 msg hparse).2.2.2 inner htry).2.2.2.2
  have hver_g : g_rw.sess.state.version.toNat = 4 := by
    unfold SessionState.version; rw [hver_sess]; rfl
  have hver₀ : msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion :=
    UInt8.ext (hver₀_nat.trans (hVer.symm.trans hver_g))
  have hctr₀ : msg.counter = UInt32.ofBitVec inner.counter :=
    UInt32.ext (((ht.2.2.2 msg hparse).2.2.2 inner htry).2.2.2.1)
  have hrk_gam : gamma interp' S g₁ msg.ratchetKey = inner.senderRatchetKey.bytes.toList :=
    ((ht.2.2.2 msg hparse).2.2.2 inner htry).2.1
  let k_own : _root_.DY.Bytes :=
    ({ st := st₀.spqr, msg := msg.pqRatchet } : _root_.DY.Spqr.RecvKey.SubF _root_.DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r (runTraceMoves r ms₁) st₀ msg := by
    unfold ownKeys
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst_av, beq_self_eq_true _⟩)
  have hk_own_gam :=
    (TR.RecvDecStep.spqrRecv_step_gamma_state_and_key
      interp' hceh r S hS g₁ ms₁ inner_wire st₀ g_rw t msg inner
      newPqrState pqrKey hpq_sess ht hparse htry hrecv_spqr).2
  have hMacOfSeed : ∀ (seed_bin : _root_.DY.Bytes),
      mkGen = ⟨gamma interp' S g₁ seed_bin, inner.counter⟩ →
      inner.verifyMacWithAddresses (cryptoOf' interp').F expected remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interp').F pqrKey).macKey = true →
      gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
        (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_bin).macKey
        st₀.peerIk st₀.myIk msg.wire) = gamma interp' S g₁ msg.mac := by
    intro seed_bin hmkGen_eq hMac
    obtain ⟨_hck_mk, hmk_mk, _hiv_mk, _⟩ :=
      TR.SendRetCoins.gamma_trMsgKeys_eq_generateKeys interp' S g₁ k_own seed_bin inner.counter pqrKey hk_own_gam
    have hwire₀_take : gamma interp' S g₁ msg.wire = inner_wire.take (inner_wire.length - 8) :=
      (ht.2.2.2 msg hparse).1
    have hm_ser : inner.serialized = inner_wire :=
      Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.tryFrom_serialized_eq_slotG2 htry
    have hmac_ver : inner.verifyMac (cryptoOf' interp').F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interp').F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver
    dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm
    rw [hm_ser] at hmac_eq
    have hkey_mk : HMAC.keyToBytes32 ((mkGen.generateKeys (cryptoOf' interp').F pqrKey).macKey) =
        gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_bin).macKey := by
      rw [hmkGen_eq]; exact hmk_mk
    have hMacBytes : inner_wire.drop (inner_wire.length - 8) =
        gamma interp' S g₁ (_root_.DY.Libsignal.TripleRatchet.computeMac
          (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_bin).macKey
          st₀.peerIk st₀.myIk msg.wire) := by
      rw [hmac_eq]
      exact TR.SendRetCoins.gamma_computeMac_tr interp' S g₁
        (_root_.DY.Libsignal.TripleRatchet.trMsgKeys k_own seed_bin).macKey
        st₀.peerIk st₀.myIk msg.wire remIk g_rw.sess.state.localIdentity
        ((mkGen.generateKeys (cryptoOf' interp').F pqrKey).macKey)
        hkey_mk hpeer_ser hmy_ser (inner_wire.take (inner_wire.length - 8)) hwire₀_take.symm
    exact hMacBytes.symm.trans (ht.2.2.2 msg hparse).2.1.symm
  cases hBr with
  | ratchet ck _ck_adv _ck_next r1 _r_adv hFind hDh _hNotLt _hJump _hAdv _hNext _hSet _hMkGen _hMac =>
    obtain ⟨sc, newRootKey, _, _, hsc, hrc1, _, _⟩ :=
      Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
    have htrue : pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state inner.senderRatchetKey = true :=
      TR.PureRecvEval.pureDrawsCoins_true_of_ratchet hRem hFind hsc hrc1
    rw [hdraws] at htrue
    cases htrue
  | existing ck ck_adv ck_next r_adv hFind hNotLt hJump hAdv hNext hSet hMkGen hMac =>
    have hst₀_rci : Symbolic.Swarm.CREF.TR.RecvDecStep.TrStateRkCkIk r st₀ :=
      Symbolic.Swarm.CREF.TR.RecvDecStep.trStateRkCkIk_of_getLocalState hmp.2.1 hst₀
    have hCkLens : ∀ c ∈ st₀.recv, (gamma interp' S g₁ c.chainKey).length = 32 :=
      hst₀_rci.recv_ck_len interp' S g₁ hwf hmp.1
    have hNodupSym : (st₀.recv.map _root_.DY.Libsignal.TripleRatchet.RecvChain.ratchetKey).Nodup :=
      TR.RecvDecStep.nodup_ratchetKey_of_stateRel_tr hrel₀_sess (hrc_rec₀ ▸ hnd₀.1)
    obtain ⟨_ci, ch, c, _mks', seed_ex, c_ex', hch0, hc0, _hfind₀, hsrk0, _htheir, _hck, hch_ck,
        hcons_bv, hSeedEq, hCntEq, _hc'_rk, _hc'_rIdx, _hR2Eq, _hRel_lit, _hMks'⟩ :=
      TR.RecvDecStep.stateRel_and_consumeMessageKey_of_existing_tr interp' S g₁ hrel₀_sess hNodupSym
        hCkLens (TR.SendRetCoins.gamma_litOf interp' S g₁ newPqrState)
        hFind hNotLt hJump hAdv hNext hSet
    have hc_mem : c ∈ st₀.recv := List.mem_of_getElem? hc0
    have hcons_ex : _root_.DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter =
        some (seed_ex, c_ex') := hctr₀ ▸ hcons_bv
    obtain ⟨c₀, hc₀, _hidx_eq, hrk₀⟩ :=
      Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure.a2b_modelChain_of_binChain
        hrel₀_sess hch0 hch_ck
    have hc_eq : c₀ = c := Option.some.inj (hc₀.symm.trans hc0)
    subst hc_eq
    have hγ_c_rk : gamma interp' S g₁ c₀.ratchetKey = gamma interp' S g₁ msg.ratchetKey := by
      rw [hrk₀, hsrk0, hrk_gam]
    have hmkGen_eq : mkGen = ⟨gamma interp' S g₁ seed_ex, inner.counter⟩ := by
      rw [hMkGen]
      change ck_adv.messageKeys (_root_.DY.Libsignal.Refinement.sha256CompressFunction interp') = _
      rcases h : ck_adv.messageKeys (_root_.DY.Libsignal.Refinement.sha256CompressFunction interp') with ⟨sd, ct⟩
      rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
    let ctx_ex := Stage1Wire.chainTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg) c₀ msg.counter
    have hctx_ex : ctx_ex ∈ whisperTrials interp' r S g₁ (runTraceMoves r ms₁) msg :=
      Stage1Wire.mem_whisperTrials_of_recv_chain hver₀ hst_av hc_mem hγ_c_rk
    have hseed_ex : ctx_ex.seed? = some seed_ex := by
      unfold ctx_ex Stage1Wire.chainTrialCtx; rw [hcons_ex]
    have hk_own_ex : k_own ∈ ctx_ex.ownSalts := by
      unfold ctx_ex Stage1Wire.chainTrialCtx; rw [hcons_ex]; exact hk_own
    have hpeer_ex : ctx_ex.peerIk = st₀.peerIk := by
      unfold ctx_ex Stage1Wire.chainTrialCtx; rw [hcons_ex]
    have hmy_ex : ctx_ex.myIk = st₀.myIk := by
      unfold ctx_ex Stage1Wire.chainTrialCtx; rw [hcons_ex]
    refine ⟨stateIdx₀, st₀, ctx_ex, seed_ex, k_own, hst₀, hcur₀, hver₀,
      hctx_ex, hseed_ex, hk_own_ex, hpeer_ex, hmy_ex,
      hMacOfSeed seed_ex hmkGen_eq hMac,
      TR.RecvDecStep.a2b_consume_seed_hmac hcons_ex,
      fun ts seed_mod c_mod' hcons_mod hsh =>
        existing_seed_shape_eq_false hreach hst₀ hc_mem hcons_ex hcons_mod hsh⟩
  | skipped _ck _hFind _hLt hTake hMac =>
    obtain ⟨_ci, _ch, _pos, _hci, _hch, _hsrk, _hfind_mk, _hmk_at, hmk_ctr, _hmk_mem, _hr2, _⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.takeSkippedKey_ok_some_inv hTake
    obtain ⟨pk_s, rIdx_s, srcIdx, skIdx, seed_s, _hlog, hsk_bv, _hunused, _hru, hseed_gam, hpk_ser, hfind_pk⟩ :=
      TR.RecvDecStep.extract_skippedKeyStored_of_takeSkippedKey_g1
        interp' r S g₁ ms₁ rfl (hrc_rec₀ ▸ hsk_pre₀) hTake
    have hsk : ((runTraceMoves r ms₁).at? skIdx : Option Symbolic.Swarm.COMPOSED.CompTrace.TREntry) =
        some ⟨_root_.DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
          (st₀.sessionInfo me) pk_s msg.counter seed_s rIdx_s srcIdx⟩ := by
      rw [hctr₀]; exact hsk_bv
    have hγ_pk : gamma interp' S g₁ pk_s = gamma interp' S g₁ msg.ratchetKey := by
      simp only [Symbolic.Swarm.CREF.TR.serializedKey, PublicKey.serialize] at hpk_ser
      injection hpk_ser with _ hbytes
      exact hbytes.trans hrk_gam.symm
    have hsk_lt : skIdx < (runTraceMoves r ms₁).length := by
      by_contra hge
      rw [RpkCli.XplQuiet.at?_none_of_ge (by omega)] at hsk
      cases hsk
    have hget_sk : (runTraceMoves r ms₁).getEventAt _root_.DY.Libsignal.TripleRatchet.TREvent skIdx =
        some (.SkippedKeyStored (st₀.sessionInfo me) pk_s msg.counter seed_s rIdx_s srcIdx) := by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [hsk]
    let ctx_sk := Stage1Wire.skippedTrialCtx st₀ (ownKeys r (runTraceMoves r ms₁) st₀ msg) (st₀.sessionInfo me) seed_s
    have hctx_sk : ctx_sk ∈ whisperTrials interp' r S g₁ (runTraceMoves r ms₁) msg :=
      Stage1Wire.mem_whisperTrials_of_skippedKeyStored hver₀ hst_av hfind_pk hsk_lt hget_sk hγ_pk rfl
    have hk_own_sk : k_own ∈ ctx_sk.ownSalts := by
      unfold ctx_sk Stage1Wire.skippedTrialCtx
      simp [Stage1Wire.sinfo_me, hk_own]
    have hmkGen_eq : mkGen = ⟨gamma interp' S g₁ seed_s, inner.counter⟩ := by
      cases mkGen
      dsimp only at hseed_gam hmk_ctr
      subst hseed_gam hmk_ctr
      rfl
    refine ⟨stateIdx₀, st₀, ctx_sk, seed_s, k_own, hst₀, hcur₀, hver₀,
      hctx_sk, rfl, hk_own_sk, rfl, rfl,
      hMacOfSeed seed_s hmkGen_eq hMac,
      TR.RecvDecStep.a2b_skippedSeed_hmac hreach hsk,
      fun ts seed_mod c_mod' hcons_mod hsh =>
        skipped_seed_shape_eq_false hreach hfresh hme hst₀ hcur₀ hsk hcons_mod hsh⟩

theorem bridgeC_caseA : BridgeCCaseASpec := by
  intro interp P r who ok records sent accepted τ_pre τ₂ σ_rest me st st' d_me x g_st
    w inner_wire out rb inner rc g ms t_rep τ₂_tl
    interp' S hext hagree hwf hwho hcrel hclean hbin hdraws ht_rep _hcs hτ₂ hacc
  by_contra hnocol
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  obtain ⟨_tag, _w_tl, _msgType, s', _hw_eq, _hrb, hcan_q, hdecW⟩ :=
    binarySessionDecryptOk_tryDecryptW hagree hbin
  obtain ⟨hme, _hinvP, hwf_st, hsess, hrec_me, _hlen_rec, _hfrom, htry, _hbranch⟩ := hbin
  obtain ⟨ext, m, msgIdx, k, pt, g₁, hext_kn, hm_idx, haddr, hσ, hget, hk, _hrng_take, hExpl⟩ := hacc
  obtain ⟨hrng_blk, hacc_pt_blk⟩ := mem_blk_of_rng_cons_accept hτ₂ hk
  let pre := ext.map Move.attackerSend
  let ms₁ := ms ++ pre
  let blk : List MachineEvent := .recv w :: τ₂.take (k + 1)
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
  have hreach₁ : (runTraceMoves r ms₁).Reachable _root_.DY.Libsignal.Composed.reachability :=
    b5_modelRun_reachable hmp₁.2.1
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
  obtain ⟨stateIdx₀, st₀, ctx_bin, seed_bin, k_own, hst₀, hcur₀, hver₀,
      hctx_bin, hseed_bin, hk_own_bin, hpeer_bin, hmy_bin, hmac_bin, hbin_hmac, hno_shape_eq⟩ :=
    binTrial_of_tryDecryptW_noDraws (me := me) hext' hwf rfl hmp₁ hreach₁ hfresh₁ hme
      hrsi (by simp only [↓reduceIte]; rfl) hcan_q htry hdraws hdecW ht_rep₁ hparse₀
  have hst_av : st₀ ∈ availableStates r (runTraceMoves r ms₁) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms₁
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  have hfull_match : List.Forall₂ (EventMatchesEntry interp' r S g₁)
      (τ_pre ++ blk) (runVis r ms₁ ++ (runMoves [m] (runTraceMoves r ms₁)).2) := by
    rw [← Symbolic.Swarm.CREF.runVis_append]
    simpa [ms₁, pre, blk, List.append_assoc] using hExpl.1.2.2.2.2.2
  have hblk_match : List.Forall₂ (EventMatchesEntry interp' r S g₁)
      blk (runMoves [m] (runTraceMoves r ms₁)).2 :=
    (xpl_forall₂_append_split hmp₁.2.2.2.2.2.length_eq hfull_match).2
  have hmatch_m : List.Forall₂ (EventMatchesEntry interp' r S g₁) blk (m.vis (runTraceMoves r ms₁)) := by
    simpa [runMoves] using hblk_match
  have hrun_m : ModelRun r (ms₁ ++ ([] ++ m :: [])) := by
    simpa [ms₁, pre, List.append_assoc] using hExpl.1.2.1
  have hB₁ : XplBlock interp' r S who g₁ ms₁ ([] ++ m :: []) τ_pre blk :=
    ⟨hmp₁, hrun_m, hblk_match⟩
  have hacc_blk : ∃ e ∈ blk, eventKind e = .accept := ⟨.accept pt, hacc_pt_blk, rfl⟩
  have hrng_blk_ex : ∃ e ∈ blk, eventKind e = .rng := ⟨.rng rb, hrng_blk, rfl⟩
  have hcur_m := Symbolic.Swarm.CREF.TR.rcvCurrentSnapshot_of_xplBlock hB₁ trivial trivial hacc_blk
  have hparty_eq : ∀ p, m.party? = some p → p = me := by
    intro p hp
    have hget_m : (ms₁ ++ [m])[ms₁.length]? = some m := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have hmp_m : MatchedPrefix interp' r S who g₁ (ms₁ ++ [m]) (τ_pre ++ blk) := by
      simpa [ms₁, pre, blk, List.append_assoc] using hExpl.1
    have hrf := hmp_m.2.2.1 ms₁.length m p hget_m hp
    rw [List.take_left, Symbolic.Swarm.CREF.callCount_eq_callStarts_length hmp₁.2.2.2.2.2, hwho] at hrf
    exact Option.some.inj hrf.symm
  cases m with
  | decryptSkipped p stateIdx msgIdx' skIdx pqIdx spqrMsgIdx wrapped =>
    exact False.elim
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure.a2b_not_decryptSkipped_of_rng
        interp' r S g₁ ms₁ [] [] τ_pre blk p stateIdx msgIdx' skIdx pqIdx spqrMsgIdx wrapped
        hB₁ trivial trivial hacc_blk hrng_blk_ex)
  | decrypt p stateIdx msgIdx' pqIdx spqrMsgIdx wrapped =>
    have hp : p = me := hparty_eq p rfl
    subst hp
    simp only [Move.decryptMsgIdx?, Option.some.injEq] at hm_idx
    subst hm_idx
    have hcur_idx : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₁) stateIdx = true := by
      simpa using hcur_m
    obtain ⟨_hRng, st_m, t_m, msg_m, c_mod', seed_mod, _spqr_m, _key_m, pqSalt_mod, _ptTerm_m,
        hst_m, hmsg_m, hparse_m, _hver_m, hfind_m, hlow_m, hcons_mod, _hspqr_m, _hpqSalt_m,
        hmac_mod, _hdec_m, _hpt_m⟩ :=
      Symbolic.Swarm.CREF.ratchet_of_matched hmatch_m hrng_blk hacc_blk
    have hidx_eq : stateIdx = stateIdx₀ :=
      TR.RecvDecStep.a2b_currentSnapshot_unique_of_role hrole₁ hst_m hst₀ hcur_idx hcur₀
    subst stateIdx
    have hst_eq : st_m = st₀ := Option.some.inj (hst_m.symm.trans hst₀)
    subst st_m
    have ht_eq : t_m = t_rep := Option.some.inj (hmsg_m.symm.trans hget)
    subst t_m
    have hmsg_eq : msg_m = msg₀ := Option.some.inj (hparse_m.symm.trans hparse₀)
    subst msg_m
    let c_fresh := (Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState st₀ msg₀.ratchetKey
      (runTraceMoves r ms₁).length).2
    have hrcf_mod : _root_.DY.Libsignal.TripleRatchet.recvChainFor st₀.toDRState msg₀.ratchetKey =
        some (c_fresh, true) := by
      unfold _root_.DY.Libsignal.TripleRatchet.recvChainFor
      have hf' : _root_.DY.Libsignal.TripleRatchet.findRecvChain st₀.toDRState.recv msg₀.ratchetKey =
          none := hfind_m
      simp [hf', hlow_m, c_fresh, Symbolic.Swarm.CREF.TR.RecvDec.trDhRatchetState]
    exact hnc₁ (recvCollision_of_binTrial_and_modelRatchet hst_av hparse₀ hver₀
      hctx_bin hseed_bin hk_own_bin hpeer_bin hmy_bin hmac_bin hbin_hmac
      hrcf_mod hcons_mod hmac_mod (hno_shape_eq (runTraceMoves r ms₁).length seed_mod c_mod' hcons_mod))
  | _ => cases hm_idx

end Symbolic.Swarm.Coinsplit.Lift.L05
