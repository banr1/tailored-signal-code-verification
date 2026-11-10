/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
public import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPure
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Composed-Trace Preservation of `SpqrInitA2BKdf`

Proves `spqrInitA2BKdf_of_getLocalState`: every stored `TRState` snapshot retrieved along
`runTraceMoves r₀ ms` satisfies `SpqrInitA2BKdf st.spqr`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR hiding newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc setupTr1 setupTr2 setupTr3 setupTr4 setupTr5 setupTrace_eq

cref_open

open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent kdfCk setRecvChain createChain)
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvHistStep2

abbrev TREntry := DY.ProtocolEvent.ExecEntryT TREvent

private abbrev PKdf (st : TRState) : Prop := SendRetCoinsCliPure.SpqrInitA2BKdf st.spqr
private abbrev TracefulPKdf {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  TracefulP PKdf Q x

private def AlicePqrKdf (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : Prop :=
  ∃ s m, o.keys.pqr = DY.KdfExtract.kdfExtract s m

private theorem spqrInitA2BKdf_spqrInit_a2b {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    (ho : AlicePqrKdf o) :
    SendRetCoinsCliPure.SpqrInitA2BKdf (DY.Spqr.spqrInit o.keys.pqr spqrA2B) := by
  intro a p hview
  unfold DY.Spqr.spqrInit at hview
  rw [DY.BytesView.view_pack] at hview
  injection hview with hview; cases hview
  exact ⟨rfl, ho⟩

private theorem spqrInitA2BKdf_spqrSend_fst (st coins : DY.Bytes) :
    SendRetCoinsCliPure.SpqrInitA2BKdf (DY.Spqr.spqrSend st coins).1 := by
  intro _ _ hview
  unfold DY.Spqr.spqrSend at hview
  dsimp only at hview
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview
  cases hview

private theorem spqrInitA2BKdf_of_spqrRecv {st msg spqr' key : DY.Bytes} {idx : UInt32}
    (h : DY.Spqr.spqrRecv st msg idx = some (spqr', key)) :
    SendRetCoinsCliPure.SpqrInitA2BKdf spqr' := by
  have hst' := DY.Spqr.spqrRecv_state st msg idx (spqr', key) h
  dsimp only at hst'; subst hst'
  intro _ _ hview
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview
  cases hview

private theorem tracefulPKdf_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat),
      TracefulPKdf (fun _ => True) (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact TracefulP.pure trivial
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
      tracefulPKdf_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

private theorem tracefulPKdf_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    TracefulPKdf (fun _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulP.bind (TracefulP.guardP _) fun _ _ => ?_
  intro tr htr
  dsimp only [liftM, monadLift, MonadLift.monadLift]
  rw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

private theorem tracefulPKdf_logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulPKdf (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

private theorem tracefulPKdf_lookupIdentity (p : Participant) (j : Nat) :
    TracefulPKdf (fun _ => True) (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulP.bind (TracefulP.getEntry_any j) fun _ _ => ?_
  split
  · exact TracefulP.bind (TracefulP.guardP _) fun _ _ => TracefulP.pure trivial
  · exact TracefulP.failure

private theorem tracefulPKdf_receiveSignalMsg (msgIdx : Nat) :
    TracefulPKdf (fun _ => True) (receiveSignalMsg msgIdx) := by
  unfold receiveSignalMsg
  refine TracefulP.bind (TracefulP.receiveMessage msgIdx) fun _ _ => ?_
  split
  · exact TracefulP.bind (TracefulP.guardP _) fun _ _ => TracefulP.pure trivial
  · exact TracefulP.failure

private theorem tracefulPKdf_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    TracefulPKdf (fun _ => True) (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact TracefulP.bind (TracefulP.guardP _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand 32) fun _ _ =>
    TracefulP.pure trivial

private theorem tracefulPKdf_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    TracefulPKdf (fun _ => True) (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact TracefulP.pure trivial
  · exact TracefulP.bind (tracefulPKdf_dhRatchetStep st pk) fun _ _ =>
      TracefulP.pure trivial
  · exact TracefulP.failure

private theorem tracefulPKdf_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulPKdf (fun _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st _ =>
    TracefulP.bind (TracefulP.guardP _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand 32) fun _ _ =>
    TracefulP.bind (TracefulP.genRand coinsLen) fun coins _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.receiveMessage pqIdx) fun _ _ =>
    TracefulP.bind (TracefulP.logEvent _) fun _ _ => ?_
  exact TracefulP.bind
    (tracefulP_logMessageKeyAndStore (P := PKdf) me _ .sender _ _ _ _ _
      (spqrInitA2BKdf_spqrSend_fst st.spqr coins))
    fun _ _ => TracefulP.sendMessage _

private theorem tracefulPKdf_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulPKdf (fun _ => True) (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st₀ _ =>
    TracefulP.bind (tracefulPKdf_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulP.bind (tracefulPKdf_ensureReceiverChain st₀ msg.ratchetKey) fun x _ => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only
  split
  · next seed c' _ =>
    split
    · next spqr' key hspqr =>
      have hspqr' : PKdf { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        spqrInitA2BKdf_of_spqrRecv hspqr
      refine TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPKdf_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      have hrest : TracefulPKdf (fun _ => True)
          (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                (msg.counter.toNat - c.index.toNat)
              DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulP.bind (tracefulPKdf_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
            tracefulP_logMessageKeyAndStore (P := PKdf) me _ .receiver _ _ _ _ _ hspqr'
      split
      · exact TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ => hrest
      · exact hrest
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem tracefulPKdf_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulPKdf (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st _ =>
    TracefulP.bind (tracefulPKdf_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulP.bind (TracefulP.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TracefulP.bind (TracefulP.guardP _) fun _ _ =>
      TracefulP.bind (fun tr' htr' => by
        unfold guardTrace
        simp only [DY.Traceful.run_mk]
        split <;> exact ⟨htr', fun _ _ => trivial⟩ :
        TracefulPKdf (fun _ => True) (guardTrace _)) fun _ _ => ?_
    split
    · next spqr' key hspqr =>
      have hspqr' : PKdf { st with spqr := spqr' } := spqrInitA2BKdf_of_spqrRecv hspqr
      exact TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPKdf_verifyMacAndDecrypt st msg pqSalt _) fun _ _ =>
        TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
        TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
        tracefulP_logMessageKeyAndStore (P := PKdf) me _ .receiver _ _ _ _ _ hspqr'
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem tracefulPKdf_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulPKdf (fun _ => True) (exposeKey me stateIdx k) := by
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

private theorem tracefulPKdf_exposeSpqr (me : Participant) (stateIdx : Nat) :
    TracefulPKdf (fun _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun _ _ => ?_
  exact TracefulP.bind (TracefulP.logEvent _) fun _ _ => TracefulP.sendMessage _

private theorem tracefulPKdf_exposeSkipped (skippedKeyEventIdx : Nat) :
    TracefulPKdf (fun _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulP.bind (TracefulP.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · exact TracefulP.bind (fun tr' htr' => by
        unfold guardTrace
        simp only [DY.Traceful.run_mk]
        split <;> exact ⟨htr', fun _ _ => trivial⟩ :
        TracefulPKdf (fun _ => True) (guardTrace _)) fun _ _ =>
      TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
      TracefulP.sendMessage _
  · exact TracefulP.failure

private theorem tracefulPKdf_setupAct (a b : Participant) (withOpk : Bool) :
    TracefulPKdf (fun _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  refine TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity a) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity b) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genSignedPrekey b _) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genPQPrekey b _) fun _ _ => ?_
  split
  · exact TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genOneTimePrekey b) fun _ _ =>
      TracefulP.pure (Q := fun _ => True) trivial
  · exact TracefulP.pure (Q := fun _ => True) trivial

private theorem tracefulPKdf_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulPKdf AlicePqrKdf
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulP.bind (TracefulP.getKey a idStateIdx .identity); intro ikA _
  apply TracefulP.bind (tracefulPKdf_lookupIdentity b regIdxB); intro ikv _
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
    rcases hag : DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pqpk opk entropy with
      ⟨ct, keys⟩
    try dsimp only
    refine TracefulP.pure (Q := AlicePqrKdf) ?_
    unfold DY.Libsignal.PQXDH.aliceAgreement at hag
    rcases hke : DY.PQKem.kemEncap pqpk entropy with ⟨ct', ss⟩
    simp only [hke, Prod.mk.injEq] at hag
    unfold AlicePqrKdf; dsimp only
    rw [← hag.2]
    exact ⟨_, _, rfl⟩

private theorem tracefulPKdf_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulPKdf (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulP.bind (tracefulPKdf_aliceHandshake a b idStateIdx regIdxB h) fun o ho => ?_
  refine TracefulP.bind (TracefulP.genRand 32) fun dhsA _ => ?_
  rcases createChain o.keys.rk o.spk dhsA with ⟨rkA, cksA⟩
  exact TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind tracefulP_traceLength fun _ _ =>
    TracefulP.bind (TracefulP.logEventPQ _) fun _ _ =>
    TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
    TracefulP.bind (tracefulPKdf_logEventC _) fun _ _ =>
    TracefulP.storeLocalState (P := PKdf) a (spqrInitA2BKdf_spqrInit_a2b ho)

private theorem tracefulPKdf_bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulPKdf (fun _ => True)
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
    refine TracefulP.bind (tracefulPKdf_lookupIdentity a regIdxA) fun ikv _ => ?_
    rcases ikv with ⟨_, _⟩
    dsimp only
    refine TracefulP.bind (TracefulP.receiveMessage ekIdx) fun _ _ => ?_
    refine TracefulP.bind (TracefulP.receiveMessage ctIdx) fun _ _ => ?_
    refine TracefulP.bind (TracefulP.guardP _) fun _ _ => ?_
    split
    · exact TracefulP.pure trivial
    · exact TracefulP.failure

private theorem tracefulPKdf_bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulPKdf (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulP.bind (tracefulPKdf_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o _ =>
    TracefulP.bind (tracefulPKdf_receiveSignalMsg mh.msg) fun msg _ => ?_
  refine TracefulP.bind (tracefulPKdf_ensureReceiverChain _ msg.ratchetKey) fun x _ => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only
  split
  · next seed c' _ =>
    split
    · next spqr' key hspqr =>
      have hspqr' : PKdf { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        spqrInitA2BKdf_of_spqrRecv hspqr
      refine TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPKdf_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
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
      all_goals exact TracefulP.bind (tracefulPKdf_logEventC _) fun _ _ =>
          TracefulP.bind tracefulP_traceLength fun _ _ =>
          TracefulP.bind (tracefulPKdf_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
          tracefulP_logMessageKeyAndStore (P := PKdf) b _ .receiver _ _ _ _ _ hspqr'
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem traceStatesP_kdf_move_next (m : Move) (tr : ExecTrace)
    (htr : TraceStatesP PKdf tr) :
    TraceStatesP PKdf (m.next tr) := by
  unfold Move.next Move.act
  cases m with
  | setup a b withOpk => exact (tracefulPKdf_setupAct a b withOpk tr htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulP_run_snd (tracefulPKdf_aliceStart a b idStateIdx regIdxB h) htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd (tracefulPKdf_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulP_run_snd (tracefulPKdf_messageEncrypt me stateIdx coinsLen pqIdx) htr
  | encryptAbort me stateIdx =>
    exact tracefulP_run_snd (tracefulP_messageEncryptAbort me stateIdx) htr
  | encryptFail me stateIdx coinsLen =>
    exact ((TracefulP.bind tracefulP_traceLength fun n _ =>
      TracefulP.bind (tracefulPKdf_messageEncrypt me stateIdx coinsLen (n + 3))
        fun _ _ => TracefulP.pure (a := ()) (Q := fun _ => True) trivial) tr htr).1
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd (tracefulPKdf_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd
      (tracefulPKdf_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) htr
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
    exact tracefulP_run_snd (tracefulPKdf_exposeKey me stateIdx k) htr
  | exposeSpqr me stateIdx =>
    exact tracefulP_run_snd (tracefulPKdf_exposeSpqr me stateIdx) htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulP_run_snd (tracefulPKdf_exposeSkipped skippedKeyEventIdx) htr
  | attackerSend msg =>
    exact tracefulP_run_snd (TracefulP.sendMessage msg) htr
  | brkDH =>
    exact (TracefulP.logEventPQ .BrokenDH tr htr).1
  | brkKEM =>
    exact (TracefulP.logEventPQ .BrokenKEM tr htr).1

private theorem traceStatesP_kdf_runMoves (ms : List Move) (tr : ExecTrace)
    (htr : TraceStatesP PKdf tr) :
    TraceStatesP PKdf (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact htr
  | cons m ms ih => exact ih (m.next tr) (traceStatesP_kdf_move_next m tr htr)

private theorem traceStatesP_kdf_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    TraceStatesP PKdf (runTraceMoves r₀ ms) :=
  traceStatesP_kdf_runMoves ms (setupTrace r₀) (traceStatesP_setupTrace (P := PKdf) r₀)

/-- Every `st` retrieved via `getLocalState p stateIdx` on `runTraceMoves r₀ ms` satisfies
`SendRetCoinsCliPure.SpqrInitA2BKdf st.spqr`. -/
theorem spqrInitA2BKdf_of_getLocalState {r₀ : ProtocolSetup} {ms : List Move}
    {p : Participant} {stateIdx : Nat} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st) :
    SendRetCoinsCliPure.SpqrInitA2BKdf st.spqr :=
  (TracefulP.getLocalState (P := PKdf) p stateIdx (runTraceMoves r₀ ms)
    (traceStatesP_kdf_runTrace r₀ ms)).2 st hst

end Symbolic.Swarm.CREF.CliPure.TR
