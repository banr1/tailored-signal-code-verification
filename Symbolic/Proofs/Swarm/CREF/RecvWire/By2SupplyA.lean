/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshStepStart
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.FreshStepInit
import Symbolic.Proofs.Swarm.CREF.TR.BobSessionSidInv
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonPath
import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshDecB1
import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshStampInv
import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshStepBob
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Symbolic.Proofs.Swarm.CREF.Xpl.Steps
import VCVio.EvalDist.ProbabilityNotation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Receiver-Chain Ratchet-Key `Nodup` and `TRRecvFreshAll` on `MatchedPrefix` Runs

Proves `nodup_ratchetKey_of_runTrace_getLocalState` across all stored `TRState` snapshots and
derives `TR.TRRecvFreshAll` on `ModelRun` and `MatchedPrefix` executions.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open DY DY.Libsignal DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg receiveSignalMsg ensureReceiverChain
  verifyMacAndDecrypt logSkippedKeys logMessageKeyAndStore messageDecrypt messageDecryptSkipped
  messageEncrypt exposeKey exposeSpqr exposeSkipped guardTrace)
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent RecvChain findRecvChain setRecvChain
  createChain x25519LowOrder)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvHistStep2

variable (interpretation : ExternInterpretation)

/-! ## `Nodup` of `st.recv.map RecvChain.ratchetKey` on `runTraceMoves r₀ ms` -/

private abbrev PRk (st : TRState) : Prop := (st.recv.map RecvChain.ratchetKey).Nodup
private abbrev TracefulPRk {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  TracefulP PRk Q x

private theorem map_ratchetKey_setRecvChain_bsa (chains : List RecvChain) (c' : RecvChain) :
    (setRecvChain chains c').map RecvChain.ratchetKey = chains.map RecvChain.ratchetKey := by
  unfold setRecvChain
  rw [List.map_map]
  apply List.map_congr_left
  intro d _
  dsimp only [Function.comp_def]
  split
  · next hEq => exact (beq_iff_eq.mp hEq).symm
  · rfl

private theorem pRk_setRecvChain {st : TRState} (hst : PRk st) (c' : RecvChain) (spqr' : DY.Bytes) :
    PRk { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
  unfold PRk at hst ⊢
  dsimp only
  rw [map_ratchetKey_setRecvChain_bsa]
  exact hst

private theorem tracefulPRk_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat),
      TracefulPRk (fun _ => True) (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact TracefulP.pure trivial
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
      tracefulPRk_logSkippedKeys s pk rIdx src (TripleRatchet.kdfCk ck).1 (n + 1) k

private theorem tracefulPRk_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    TracefulPRk (fun _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulP.bind (TracefulP.guardP _) fun _ _ => ?_
  intro tr htr
  dsimp only [liftM, monadLift, MonadLift.monadLift]
  rw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

private theorem tracefulPRk_logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulPRk (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

private theorem tracefulPRk_lookupIdentity (p : Participant) (j : Nat) :
    TracefulPRk (fun _ => True) (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulP.bind (TracefulP.getEntry_any j) fun _ _ => ?_
  split
  · exact TracefulP.bind (TracefulP.guardP _) fun _ _ => TracefulP.pure trivial
  · exact TracefulP.failure

private theorem tracefulPRk_receiveSignalMsg (msgIdx : Nat) :
    TracefulPRk (fun _ => True) (receiveSignalMsg msgIdx) := by
  unfold receiveSignalMsg
  refine TracefulP.bind (TracefulP.receiveMessage msgIdx) fun _ _ => ?_
  split
  · exact TracefulP.bind (TracefulP.guardP _) fun _ _ => TracefulP.pure trivial
  · exact TracefulP.failure

private theorem tracefulPRk_ensureReceiverChain {st : TRState} (hst : PRk st) (pk : DY.Bytes) :
    TracefulPRk (fun x => PRk x.1) (ensureReceiverChain st pk) := by
  intro tr htr
  rcases hfind : findRecvChain st.recv pk with _ | c
  · by_cases hlow : x25519LowOrder pk = false
    · obtain ⟨hens1, hens2⟩ := TR.RecvDec.ensureReceiverChain_run_ratchet tr hfind hlow
      rw [hens1, hens2]
      refine ⟨traceStatesP_append (fun _ h => by cases h) htr, fun a ha => ?_⟩
      injection ha with ha; subst ha
      exact TR.nodup_map_ratchetKey_trDhRatchetState hst hfind
    · have hlow_true : x25519LowOrder pk = true := by
        cases h : x25519LowOrder pk
        · exact absurd h hlow
        · rfl
      have hens_fail : ((ensureReceiverChain st pk).run tr).1 = none ∧
          ((ensureReceiverChain st pk).run tr).2.val = tr := by
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold TripleRatchet.recvChainFor TRState.toDRState
        dsimp only; rw [hfind]
        simp only [hlow_true, ↓reduceIte, DY.Traceful.run_failure]
        exact ⟨trivial, trivial⟩
      rw [hens_fail.1, hens_fail.2]
      exact ⟨htr, fun _ ha => by cases ha⟩
  · obtain ⟨hens1, hens2⟩ := TR.RecvDec.ensureReceiverChain_run_noRatchet tr hfind
    rw [hens1, hens2]
    refine ⟨htr, fun a ha => ?_⟩
    injection ha with ha; subst ha
    exact hst

private theorem tracefulPRk_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulPRk (fun _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) :=
  tracefulP_messageEncrypt (fun st st' h hp => by unfold PRk at hp ⊢; rw [h]; exact hp)
    me stateIdx coinsLen pqIdx

private theorem tracefulPRk_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulPRk (fun _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st₀ hst₀ =>
    TracefulP.bind (tracefulPRk_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulP.bind (tracefulPRk_ensureReceiverChain hst₀ msg.ratchetKey) fun x hx => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hx ⊢
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      have hst' : PRk { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        pRk_setRecvChain hx c' spqr'
      refine TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPRk_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      have hrest : TracefulPRk (fun _ => True)
          (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                (msg.counter.toNat - c.index.toNat)
              DY.ProtocolEvent.logEvent (TripleRatchet.TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulP.bind (tracefulPRk_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
            tracefulP_logMessageKeyAndStore (P := PRk) me _ .receiver _ _ _ _ _ hst'
      split
      · exact TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ => hrest
      · exact hrest
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem tracefulPRk_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulPRk (fun _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st hst =>
    TracefulP.bind (tracefulPRk_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulP.bind (TracefulP.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TracefulP.bind (TracefulP.guardP _) fun _ _ =>
      TracefulP.bind (by intro tr' htr'; unfold guardTrace; rw [DY.Traceful.run_mk]; exact ⟨htr', fun _ _ => trivial⟩ :
        TracefulPRk (fun _ => True) (guardTrace _)) fun _ _ => ?_
    split
    · next spqr' key _ =>
      exact TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPRk_verifyMacAndDecrypt st msg pqSalt _) fun _ _ =>
        TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
        TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
        tracefulP_logMessageKeyAndStore (P := PRk) me _ .receiver _ _ _ _ _ hst
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem tracefulPRk_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulPRk (fun _ => True) (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun _ _ => ?_
  cases k with
  | rk => exact TracefulP.bind (TracefulP.logEvent _) fun _ _ => TracefulP.sendMessage _
  | dhs => exact TracefulP.bind (TracefulP.logEvent _) fun _ _ => TracefulP.sendMessage _
  | cks => exact TracefulP.bind (TracefulP.logEvent _) fun _ _ => TracefulP.sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact TracefulP.bind (TracefulP.logEvent _) fun _ _ => TracefulP.sendMessage _
    · exact TracefulP.failure

private theorem tracefulPRk_exposeSpqr (me : Participant) (stateIdx : Nat) :
    TracefulPRk (fun _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun _ _ => ?_
  exact TracefulP.bind (TracefulP.logEvent _) fun _ _ => TracefulP.sendMessage _

private theorem tracefulPRk_exposeSkipped (skippedKeyEventIdx : Nat) :
    TracefulPRk (fun _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulP.bind (TracefulP.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · exact TracefulP.bind (by intro tr' htr'; unfold guardTrace; rw [DY.Traceful.run_mk]; exact ⟨htr', fun _ _ => trivial⟩ :
        TracefulPRk (fun _ => True) (guardTrace _)) fun _ _ =>
      TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
      TracefulP.sendMessage _
  · exact TracefulP.failure

private theorem tracefulPRk_setupAct (a b : Participant) (withOpk : Bool) :
    TracefulPRk (fun _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  refine TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity a) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity b) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genSignedPrekey b _) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genPQPrekey b _) fun _ _ => ?_
  split
  · exact TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genOneTimePrekey b) fun _ _ =>
      TracefulP.pure (Q := fun _ => True) trivial
  · exact TracefulP.pure (Q := fun _ => True) trivial

private theorem tracefulPRk_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulPRk (fun _ => True)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulP.bind (TracefulP.getKey a idStateIdx .identity); intro ikA _
  apply TracefulP.bind (tracefulPRk_lookupIdentity b regIdxB); intro ikv _
  rcases ikv with ⟨ikB, _⟩; dsimp only
  apply TracefulP.bind (TracefulP.receiveMessage h.spk); intro spk _
  apply TracefulP.bind (TracefulP.receiveMessage h.spkSig); intro _ _
  apply TracefulP.bind (TracefulP.receiveMessage h.pqpk); intro pqpk _
  apply TracefulP.bind (TracefulP.receiveMessage h.pqpkSig); intro _ _
  apply TracefulP.bind (TracefulP.guardP _); intro _ _
  apply TracefulP.bind (TracefulP.guardP _); intro _ _
  split
  all_goals first
    | (apply TracefulP.bind (TracefulP.receiveMessage _); intro _ _)
    | skip
  all_goals
    apply TracefulP.bind (TracefulP.pure (Q := fun _ => True) trivial); intro opk _
    apply TracefulP.bind (TracefulP.genRand 32); intro ek _
    apply TracefulP.bind (TracefulP.guardP _); intro _ _
    apply TracefulP.bind (TracefulP.guardP _); intro _ _
    apply TracefulP.bind (TracefulP.genRand 32); intro entropy _
    rcases DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pqpk opk entropy with ⟨ct, keys⟩
    try dsimp only
    exact TracefulP.pure trivial

private theorem tracefulPRk_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulPRk (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulP.bind (tracefulPRk_aliceHandshake a b idStateIdx regIdxB h) fun o _ => ?_
  refine TracefulP.bind (TracefulP.genRand 32) fun dhsA _ => ?_
  rcases createChain o.keys.rk o.spk dhsA with ⟨rkA, cksA⟩
  exact TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind tracefulP_traceLength fun _ _ =>
    TracefulP.bind (TracefulP.logEventPQ _) fun _ _ =>
    TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
    TracefulP.bind (tracefulPRk_logEventC _) fun _ _ =>
    TracefulP.storeLocalState (P := PRk) a (List.nodup_singleton _)

private theorem tracefulPRk_bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulPRk (fun _ => True)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine TracefulP.bind (TracefulP.getKey b h.ik _) fun _ _ => ?_
  refine TracefulP.bind (TracefulP.getKey b h.spk _) fun _ _ => ?_
  refine TracefulP.bind (TracefulP.getKey b h.pqspk _) fun _ _ => ?_
  dsimp only
  split
  all_goals first
    | refine TracefulP.bind (TracefulP.getKey b _ _) fun _ _ => ?_
    | skip
  all_goals
    refine TracefulP.bind (TracefulP.pure (Q := fun _ => True) trivial) fun _ _ => ?_
    refine TracefulP.bind (tracefulPRk_lookupIdentity a regIdxA) fun ikv _ => ?_
    rcases ikv with ⟨_, _⟩
    dsimp only
    refine TracefulP.bind (TracefulP.receiveMessage ekIdx) fun _ _ => ?_
    refine TracefulP.bind (TracefulP.receiveMessage ctIdx) fun _ _ => ?_
    refine TracefulP.bind (TracefulP.guardP _) fun _ _ => ?_
    split
    · exact TracefulP.pure trivial
    · exact TracefulP.failure

private theorem tracefulPRk_bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulPRk (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulP.bind (tracefulPRk_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o _ =>
    TracefulP.bind (tracefulPRk_receiveSignalMsg mh.msg) fun msg _ => ?_
  refine TracefulP.bind (tracefulPRk_ensureReceiverChain (by exact List.nodup_nil) msg.ratchetKey) fun x hx => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hx ⊢
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      have hst' : PRk { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        pRk_setRecvChain hx c' spqr'
      refine TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPRk_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      split
      all_goals first
        | refine TracefulP.bind (TracefulP.requireTracePredicate _) fun _ _ =>
            TracefulP.bind (TracefulP.logEventPQ _) fun _ _ => ?_
        | skip
      all_goals refine TracefulP.bind tracefulP_traceLength fun _ _ =>
        TracefulP.bind (TracefulP.logEventPQ _) fun _ _ => ?_
      all_goals split
      all_goals first
        | refine TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
            TracefulP.bind (TracefulP.logEvent _) fun _ _ => ?_
        | skip
      all_goals exact TracefulP.bind (tracefulPRk_logEventC _) fun _ _ =>
          TracefulP.bind tracefulP_traceLength fun _ _ =>
          TracefulP.bind (tracefulPRk_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
          tracefulP_logMessageKeyAndStore (P := PRk) b _ .receiver _ _ _ _ _ hst'
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem traceStatesP_rk_move_next (m : Move) (tr : ExecTrace)
    (htr : TraceStatesP PRk tr) :
    TraceStatesP PRk (m.next tr) := by
  unfold Move.next Move.act
  cases m with
  | setup a b withOpk => exact (tracefulPRk_setupAct a b withOpk tr htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulP_run_snd (tracefulPRk_aliceStart a b idStateIdx regIdxB h) htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd (tracefulPRk_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulP_run_snd (tracefulPRk_messageEncrypt me stateIdx coinsLen pqIdx) htr
  | encryptAbort me stateIdx =>
    exact tracefulP_run_snd (tracefulP_messageEncryptAbort me stateIdx) htr
  | encryptFail me stateIdx coinsLen =>
    exact (TracefulP.bind tracefulP_traceLength
      (fun n _ => TracefulP.bind (tracefulPRk_messageEncrypt me stateIdx coinsLen (n + 3))
        fun _ _ => TracefulP.pure (Q := fun _ => True) trivial) tr htr).1
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd (tracefulPRk_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd
      (tracefulPRk_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) htr
  | reject _ => dsimp only; rw [DY.Traceful.run_pure]; exact htr
  | compromiseIK p stateIdx =>
    exact tracefulP_run_snd
      (by unfold DY.Libsignal.PQXDH.compromiseIK
          exact TracefulP.bind (TracefulP.getKey p stateIdx _) fun _ _ =>
            TracefulP.bind (TracefulP.logEventPQ _) fun _ _ => TracefulP.sendMessage _) htr
  | compromiseSPK p stateIdx =>
    exact tracefulP_run_snd
      (by unfold DY.Libsignal.PQXDH.compromiseSPK
          exact TracefulP.bind (TracefulP.getKey p stateIdx _) fun _ _ =>
            TracefulP.bind (TracefulP.logEventPQ _) fun _ _ => TracefulP.sendMessage _) htr
  | compromisePQSPK p stateIdx =>
    exact tracefulP_run_snd
      (by unfold DY.Libsignal.PQXDH.compromisePQSPK
          exact TracefulP.bind (TracefulP.getKey p stateIdx _) fun _ _ =>
            TracefulP.bind (TracefulP.logEventPQ _) fun _ _ => TracefulP.sendMessage _) htr
  | compromiseOPK p stateIdx =>
    exact tracefulP_run_snd
      (by unfold DY.Libsignal.PQXDH.compromiseOPK
          exact TracefulP.bind (TracefulP.getKey p stateIdx _) fun _ _ =>
            TracefulP.bind (TracefulP.requireTracePredicate _) fun _ _ =>
            TracefulP.bind (TracefulP.logEventPQ _) fun _ _ => TracefulP.sendMessage _) htr
  | exposeKey me stateIdx k =>
    exact tracefulP_run_snd (tracefulPRk_exposeKey me stateIdx k) htr
  | exposeSpqr me stateIdx =>
    exact tracefulP_run_snd (tracefulPRk_exposeSpqr me stateIdx) htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulP_run_snd (tracefulPRk_exposeSkipped skippedKeyEventIdx) htr
  | attackerSend msg =>
    exact tracefulP_run_snd (TracefulP.sendMessage msg) htr
  | brkDH =>
    exact (TracefulP.logEventPQ .BrokenDH tr htr).1
  | brkKEM =>
    exact (TracefulP.logEventPQ .BrokenKEM tr htr).1

private theorem traceStatesP_rk_runMoves (ms : List Move) (tr : ExecTrace)
    (htr : TraceStatesP PRk tr) :
    TraceStatesP PRk (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact htr
  | cons m ms ih => exact ih (m.next tr) (traceStatesP_rk_move_next m tr htr)

private theorem traceStatesP_rk_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    TraceStatesP PRk (runTraceMoves r₀ ms) :=
  traceStatesP_rk_runMoves ms (setupTrace r₀) (traceStatesP_setupTrace (P := PRk) r₀)

/-- Every `st` retrieved via `getLocalState p stateIdx` on `runTraceMoves r₀ ms` has
pairwise distinct receiver-chain ratchet keys (`(st.recv.map RecvChain.ratchetKey).Nodup`). -/
theorem nodup_ratchetKey_of_runTrace_getLocalState {r₀ : ProtocolSetup} {ms : List Move}
    {p : Participant} {stateIdx : Nat} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st) :
    (st.recv.map RecvChain.ratchetKey).Nodup :=
  (TracefulP.getLocalState (P := PRk) p stateIdx (runTraceMoves r₀ ms)
    (traceStatesP_rk_runTrace r₀ ms)).2 st hst

theorem trRecvFreshAll_snoc_aliceStart_of_reachable {r₀ : ProtocolSetup} {ms : List Move}
    (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (h : TR.TRRecvFreshAll r₀ ms) :
    TR.TRRecvFreshAll r₀ (ms ++ [Move.aliceStart a b idStateIdx regIdxB bh shown]) :=
  TR.trRecvFreshAll_snoc_aliceStart r₀ ms a b idStateIdx regIdxB bh shown h
    (fun L hL rk s hs => TR.trRecvSid_fresh_alice r₀ ms hreach L hL rk s hs)

theorem trRecvFreshAll_snoc_move {r₀ : ProtocolSetup} {ms : List Move} (m : Move)
    (hsetup : m.isSetup = false)
    (hreach_pre : (runTraceMoves r₀ ms).Reachable reachability)
    (hreach_post : (runTraceMoves r₀ (ms ++ [m])).Reachable reachability)
    (hbob : ∀ b a kh regIdxA mh pqIdx spqrMsgIdx shown,
      m = Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown →
      TR.TRRecvFreshAll r₀ (ms ++ [Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown]))
    (h : TR.TRRecvFreshAll r₀ ms) :
    TR.TRRecvFreshAll r₀ (ms ++ [m]) := by
  cases m with
  | setup _ _ _ => cases hsetup
  | aliceStart a b idStateIdx regIdxB bh shown =>
    exact trRecvFreshAll_snoc_aliceStart_of_reachable a b idStateIdx regIdxB bh shown hreach_pre h
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    exact hbob b a kh regIdxA mh pqIdx spqrMsgIdx shown rfl
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    exact TR.trRecvFreshAll_snoc_encrypt_reach me stateIdx coinsLen pqIdx wrap hreach_post h
  | encryptAbort me stateIdx =>
    exact TR.trRecvFreshAll_snoc_encryptAbort me stateIdx h
  | encryptFail me stateIdx coinsLen =>
    exact TR.trRecvFreshAll_snoc_encryptFail me stateIdx coinsLen h
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    exact TR.trRecvFreshAll_snoc_decrypt
      (fun _ hst => nodup_ratchetKey_of_runTrace_getLocalState hst) hreach_post h
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    exact TR.trRecvFreshAll_snoc_decryptSkipped hreach_post h
  | reject draws =>
    exact TR.trRecvFreshAll_snoc_reject r₀ ms draws h
  | compromiseIK p stateIdx =>
    exact TR.trRecvFreshAll_snoc_compromiseIK r₀ ms p stateIdx h
  | compromiseSPK p stateIdx =>
    exact TR.trRecvFreshAll_snoc_compromiseSPK r₀ ms p stateIdx h
  | compromisePQSPK p stateIdx =>
    exact TR.trRecvFreshAll_snoc_compromisePQSPK r₀ ms p stateIdx h
  | compromiseOPK p stateIdx =>
    exact TR.trRecvFreshAll_snoc_compromiseOPK r₀ ms p stateIdx h
  | exposeKey me stateIdx k =>
    exact TR.trRecvFreshAll_snoc_exposeKey me stateIdx k h
  | exposeSpqr me stateIdx =>
    exact TR.trRecvFreshAll_snoc_exposeSpqr me stateIdx h
  | exposeSkipped skIdx =>
    exact TR.trRecvFreshAll_snoc_exposeSkipped skIdx h
  | attackerSend msg =>
    exact TR.trRecvFreshAll_snoc_attackerSend r₀ ms msg h
  | brkDH =>
    exact TR.rfs_snoc_of_pres (TR.rfs_pres_logPQ .BrokenDH) h
  | brkKEM =>
    exact TR.rfs_snoc_of_pres (TR.rfs_pres_logPQ .BrokenKEM) h

theorem trRecvFreshAll_take_of_modelRun {r₀ : ProtocolSetup} {ms₀ : List Move}
    (hrun : ModelRun r₀ ms₀)
    (hbob : ∀ (i : Nat) b a kh regIdxA mh pqIdx spqrMsgIdx shown,
      ms₀[i]? = some (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown) →
      TR.TRRecvFreshAll r₀ (ms₀.take i) →
      TR.TRRecvFreshAll r₀
        (ms₀.take i ++ [Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown])) :
    ∀ k ≤ ms₀.length, TR.TRRecvFreshAll r₀ (ms₀.take k)
  | 0, _ => TR.trRecvFreshAll_nil r₀
  | k + 1, hk => by
    have hk_lt : k < ms₀.length := hk
    have htake_succ : ms₀.take (k + 1) = ms₀.take k ++ [ms₀[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt]; rfl
    rw [htake_succ]
    have hm_mem : ms₀[k] ∈ ms₀ := List.getElem_mem hk_lt
    have hsetup : ms₀[k].isSetup = false := hrun.2.1 ms₀[k] hm_mem
    have hreach_pre : (runTraceMoves r₀ (ms₀.take k)).Reachable reachability := hrun.2.2.1.2.2 k
    have hreach_post : (runTraceMoves r₀ (ms₀.take k ++ [ms₀[k]])).Reachable reachability := by
      rw [← htake_succ]
      exact hrun.2.2.1.2.2 (k + 1)
    exact trRecvFreshAll_snoc_move ms₀[k] hsetup hreach_pre hreach_post
      (fun b a kh regIdxA mh pqIdx spqrMsgIdx shown hm_eq =>
        hbob k b a kh regIdxA mh pqIdx spqrMsgIdx shown
          ((List.getElem?_eq_getElem hk_lt).trans (congrArg some hm_eq))
          (trRecvFreshAll_take_of_modelRun hrun hbob k (Nat.le_of_lt hk_lt)))
      (trRecvFreshAll_take_of_modelRun hrun hbob k (Nat.le_of_lt hk_lt))

/-- Full-run `TR.TRRecvFreshAll r₀ ms₀` from `ModelRun r₀ ms₀` and the `bobStart` step. -/
theorem trRecvFreshAll_of_modelRun {r₀ : ProtocolSetup} {ms₀ : List Move}
    (hrun : ModelRun r₀ ms₀)
    (hbob : ∀ (i : Nat) b a kh regIdxA mh pqIdx spqrMsgIdx shown,
      ms₀[i]? = some (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown) →
      TR.TRRecvFreshAll r₀ (ms₀.take i) →
      TR.TRRecvFreshAll r₀
        (ms₀.take i ++ [Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown])) :
    TR.TRRecvFreshAll r₀ ms₀ := by
  simpa [List.take_length] using trRecvFreshAll_take_of_modelRun hrun hbob ms₀.length (Nat.le_refl _)

/-! ## `bobStart` Base-Key Freshness under `MatchedPrefix` and `PathFaithful` -/

private theorem bobHandshake_run_ek_sent_bsa {T : ExecTrace} {b a : Participant}
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA ekIdx ctIdx : Nat}
    {o : DY.Libsignal.PQXDH.BobHandshakeOut}
    (ho : ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run T).1 = some o) :
    T.getMessageSentAt ekIdx = some o.ek := by
  classical
  let Goal : Prop := T.getMessageSentAt ekIdx = some o.ek
  let Inv (t : ExecTrace) : Prop := t = T ∨ Goal
  let f (o' : DY.Libsignal.PQXDH.BobHandshakeOut) : Traceful Unit :=
    if o' = o then Random.genRand 32 >>= fun _ => pure () else pure ()
  have hstep : Inv (((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx >>= f).run
      T).2.val) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_bobHandshake_at b a kh regIdxA ekIdx ctIdx T
      (Or.inl rfl) (fun _ _ _ _ _ _ ek _ _ _ _ _ _ _ _ hek _ _ _ => ?_)
    dsimp only [f]; split
    · next heq =>
      refine Or.inr ?_
      subst heq
      show T.getMessageSentAt ekIdx = some ek
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      unfold Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt at hek
      rw [hek]
    · refine Or.inl ?_
      rw [DY.Traceful.run_pure]
  have htr_eq : (((Random.genRand 32 >>= fun _ => pure () : Traceful Unit).run T).2.val) =
      T.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
      DY.Traceful.run_pure]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, ho] at hstep
  dsimp only at hstep
  rw [TR.bobHandshake_run_snd] at hstep
  dsimp only [f] at hstep
  rw [ite_eq_left_iff.mpr fun h => absurd rfl h, htr_eq] at hstep
  rcases hstep with heq | hgoal
  · have hlen := congrArg Trace.length heq
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hlen
  · exact hgoal

private theorem preKeyRecvOpkMatches_baseKey_bsa {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {wire : HwBytes} {ek : DY.Bytes} {rest : List DY.Bytes}
    (h : PreKeyRecvOpkMatches interpretation r S g wire (ek :: rest)) :
    ∃ p, parsePreKeyWire wire = some p ∧
      p.baseKey.take 33 = ecKey (gamma interpretation S g ek) := by
  match rest, h with
  | [_, _], ⟨⟨p, hp, hb, _⟩, _⟩ => exact ⟨p, hp, hb⟩
  | [_, _, _], ⟨⟨p, hp, hb, _⟩, _⟩ => exact ⟨p, hp, hb⟩

private theorem vis_bobStart_cons_of_pos_bsa {b a : Participant}
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    {shown : Nat} {tr : ExecTrace} (hsh : 1 ≤ shown) :
    ∃ tail,
      (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis tr =
        ⟨.recv, received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList, .preKeyRecv, none⟩ :: tail := by
  obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
  exact ⟨_, by rw [xpl_vis_eq, xpl_ownVis, bobVis, List.cons_append, List.take_succ_cons, List.cons_append]⟩

private theorem callStarts_length_of_forall₂_bsa {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ {τ : List MachineEvent} {vs : List VisEntry},
      List.Forall₂ (EventMatchesEntry interpretation r S g) τ vs →
      (callStarts τ).length = callCount vs
  | [], [], .nil => rfl
  | e :: τ, v :: vs, .cons h head_tl => by
    have ih := callStarts_length_of_forall₂_bsa head_tl
    have hkind : eventKind e = v.kind := h.1
    dsimp only [callStarts, callCount] at ih ⊢
    rw [List.filter_cons, List.filter_cons, hkind]
    cases (v.kind == VisEventKind.recv || v.kind == VisEventKind.pt) <;> simp [ih]

theorem bobStart_ek_not_mem_bobDoneBaseKeys_of_matchedPrefix_pathFaithful
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost}
    {ms : List Move} {τ : List MachineEvent} {i : Nat}
    {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat}
    {spqrMsgIdx : UInt32} {shown : Nat}
    {o : DY.Libsignal.PQXDH.BobHandshakeOut}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hpath : PathFaithful interpretation r S g ms τ)
    (hmi : ms[i]? = some (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown))
    (ho : ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA mh.ek mh.ct).run
      (runTraceMoves r (ms.take i))).1 = some o) :
    o.ek ∉ bobDoneBaseKeys (runTraceMoves r (ms.take i)) := by
  intro hmem
  have hlt : i < ms.length := (List.getElem?_eq_some_iff.mp hmi).1
  set m := Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown with hm_def
  have hdrop : ms.drop i = m :: ms.drop (i + 1) := by
    rw [← List.cons_getElem_drop_succ (h := hlt)]
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hmi
    rw [hmi]
  have hms : ms = ms.take i ++ (m :: ms.drop (i + 1)) := by
    rw [← hdrop, List.take_append_drop]
  have hvis_split : runVis r ms = runVis r (ms.take i) ++
      (m.vis (runTraceMoves r (ms.take i)) ++
        (runMoves (ms.drop (i + 1)) (m.next (runTraceMoves r (ms.take i)))).2) := by
    conv_lhs => rw [hms]
    rw [runVis_append, runMoves_cons_snd]
  have hanc := hmp.2.1.2.2.1.2.1
  rw [hms, b5_movesAnchored_append] at hanc
  have hsh : 1 ≤ shown := hanc.2.1.1
  obtain ⟨tail, hcons⟩ := vis_bobStart_cons_of_pos_bsa
    (b := b) (a := a) (kh := kh) (regIdxA := regIdxA) (mh := mh) (pqIdx := pqIdx)
    (spqrMsgIdx := spqrMsgIdx) (tr := runTraceMoves r (ms.take i)) hsh
  have hfull := hmp.2.2.2.2.2
  rw [hvis_split, hcons, List.cons_append] at hfull
  have hlen_full := hfull.length_eq
  have hle_vis : (runVis r (ms.take i)).length ≤ τ.length := by
    rw [hlen_full, List.length_append]
    omega
  have hτ_split : τ = τ.take (runVis r (ms.take i)).length ++ τ.drop (runVis r (ms.take i)).length :=
    (List.take_append_drop _ τ).symm
  rw [hτ_split] at hfull
  have hlen_take : (τ.take (runVis r (ms.take i)).length).length = (runVis r (ms.take i)).length :=
    List.length_take_of_le hle_vis
  obtain ⟨hF₁, hF₂⟩ := xpl_forall₂_append_split hlen_take hfull
  rcases hdrop_τ : τ.drop (runVis r (ms.take i)).length with _ | ⟨e, τ₂⟩
  · rw [hdrop_τ] at hF₂; cases hF₂
  · rw [hdrop_τ] at hF₂
    cases hF₂ with
    | cons hEME _ =>
      have hkind : eventKind e = .recv := hEME.1
      cases e <;> try cases hkind
      rename_i wire
      have hek_sent := bobHandshake_run_ek_sent_bsa ho
      have hrec_cons : received (runTraceMoves r (ms.take i)) [mh.ek, mh.ct, mh.msg] ++
          (bobOpkPk b kh (runTraceMoves r (ms.take i))).toList =
          o.ek :: (received (runTraceMoves r (ms.take i)) [mh.ct, mh.msg] ++
            (bobOpkPk b kh (runTraceMoves r (ms.take i))).toList) := by
        simp [received, hek_sent]
      have hmatch : PreKeyRecvOpkMatches interpretation r S g wire
          (received (runTraceMoves r (ms.take i)) [mh.ek, mh.ct, mh.msg] ++
            (bobOpkPk b kh (runTraceMoves r (ms.take i))).toList) := hEME.2
      rw [hrec_cons] at hmatch
      obtain ⟨p, hp, hbk⟩ := preKeyRecvOpkMatches_baseKey_bsa interpretation hmatch
      have hcs_split : callStarts τ =
          callStarts (τ.take (runVis r (ms.take i)).length) ++ (.recv wire :: callStarts τ₂) := by
        conv_lhs => rw [hτ_split, hdrop_τ]
        unfold callStarts
        rw [List.filter_append]
        rfl
      have hcc_eq : (callStarts (τ.take (runVis r (ms.take i)).length)).length =
          callCount (runVis r (ms.take i)) :=
        callStarts_length_of_forall₂_bsa interpretation hF₁
      have hcall : (callStarts τ)[callCount (runVis r (ms.take i))]? = some (.recv wire) := by
        rw [hcs_split, ← hcc_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      exact TR.G1.Spine.not_bobStart_of_bobDone hpath hmi hcall hp ⟨o.ek, hmem, hbk.symm⟩ rfl

theorem bobStart_sid_fresh_of_matchedPrefix_pathFaithful
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost}
    {ms : List Move} {τ : List MachineEvent} {i : Nat}
    {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat}
    {spqrMsgIdx : UInt32} {shown : Nat}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hpath : PathFaithful interpretation r S g ms τ)
    (hmi : ms[i]? = some (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown)) :
    ∀ o,
      ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA mh.ek mh.ct).run
        (runTraceMoves r (ms.take i))).1 = some o →
      ∀ (rkey : DY.Bytes),
        let s : SessionInfo := ⟨DY.Concat.concat (DY.X25519.normalizeX25519Key rkey) o.keys.rk, false, b, a⟩
        TR.rfs_NoRecvEv (runTraceMoves r (ms.take i)) s ∧ TR.rfs_NoStored (runTraceMoves r (ms.take i)) s := by
  intro o ho rkey
  have hreach : (runTraceMoves r (ms.take i)).Reachable reachability := hmp.2.1.2.2.1.2.2 i
  have hek := bobStart_ek_not_mem_bobDoneBaseKeys_of_matchedPrefix_pathFaithful
    interpretation hmp hpath hmi ho
  exact TR.bobStart_sid_fresh hreach ho hek rkey

theorem trRecvFreshAll_of_matchedPrefix_pathFaithful
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost}
    {ms : List Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hpath : PathFaithful interpretation r S g ms τ) :
    TR.TRRecvFreshAll r ms :=
  trRecvFreshAll_of_modelRun hmp.2.1
    (fun i b a kh regIdxA mh pqIdx spqrMsgIdx shown hmi hpre =>
      TR.trRecvFreshAll_snoc_bobStart r (ms.take i) b a kh regIdxA mh pqIdx spqrMsgIdx shown hpre
        (bobStart_sid_fresh_of_matchedPrefix_pathFaithful interpretation hmp hpath hmi))

/-- Full-run `TR.TRRecvFreshAll r ms` from `MatchedPrefix`. -/
theorem trRecvFreshAll_of_matchedPrefix
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost}
    {ms : List Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ) :
    TR.TRRecvFreshAll r ms :=
  trRecvFreshAll_of_matchedPrefix_pathFaithful interpretation hmp hmp.2.2.2.1

end Symbolic.Swarm.CREF
