/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.SHARED.HmacLen
import Symbolic.Proofs.Swarm.TRREF.MacFormBridge
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# SPQR Receive-Step State and Key Agreement

Proves composed-trace preservation of `SpqrInitDirOK` across protocol moves and
relates `spqrModelOf.recv` outputs to symbolic `DY.Spqr.spqrRecv` states and keys.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent RecvChain setRecvChain kdfCk createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (BundleHandles BobKeyHandles PreKeyMsgHandles aliceHandshake bobHandshake)
open DY.Libsignal.HwEvents
open DY.Libsignal.Rust
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.TRREF.SpqrSemOf (saltToBytes)
open Swarm.Phase0WholeFunctionBridge
  (senderChainToChainRec receiverChainToChainRec sessionToSessionRec sessionToRecordRec
   u32Field_eq_uint32Field msgField_eq_lenField bytesField_eq_record_bytesField
   lenField_length_le record_bytesField_length_le encChainKey_length_lt encMessageKey_length_le
   chainBytes_sender_eq_encSenderChain chainBytes_receiver_eq_encReceiverChain)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)

/-- Any `InitState.SubF` view of `b` has a valid `spqrParamsDir?`. -/
def SpqrInitDirOK (b : DY.Bytes) : Prop :=
  ∀ authKey params,
    b.view? DY.Spqr.InitState.SubF = some ⟨authKey, params⟩ →
    (DY.Spqr.spqrParamsDir? params).isSome = true
private theorem spqrInitDirOK_spqrInit (authKey : DY.Bytes) (dir : DY.Spqr.Direction) :
    SpqrInitDirOK (DY.Spqr.spqrInit authKey (DY.Spqr.encodeSpqrDirectionParams dir)) := by
  intro a p hview
  unfold DY.Spqr.spqrInit at hview
  rw [DY.BytesView.view_pack] at hview
  injection hview with hview; cases hview
  rw [DY.Spqr.spqrParamsDir?_spqrParams]; rfl

private theorem spqrInitDirOK_spqrInit_a2b (authKey : DY.Bytes) :
    SpqrInitDirOK (DY.Spqr.spqrInit authKey spqrA2B) :=
  spqrInitDirOK_spqrInit authKey .a2b

private theorem spqrInitDirOK_spqrInit_b2a (authKey : DY.Bytes) :
    SpqrInitDirOK (DY.Spqr.spqrInit authKey spqrB2A) :=
  spqrInitDirOK_spqrInit authKey .b2a

private theorem spqrInitDirOK_spqrSend_fst (st coins : DY.Bytes) :
    SpqrInitDirOK (DY.Spqr.spqrSend st coins).1 := by
  intro _ _ hview
  unfold DY.Spqr.spqrSend at hview
  dsimp only at hview
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview
  cases hview

private theorem spqrInitDirOK_of_spqrRecv {st msg spqr' key : DY.Bytes} {idx : UInt32}
    (h : DY.Spqr.spqrRecv st msg idx = some (spqr', key)) :
    SpqrInitDirOK spqr' := by
  have hst' := DY.Spqr.spqrRecv_state st msg idx (spqr', key) h
  dsimp only at hst'; subst hst'
  intro _ _ hview
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview
  cases hview

/-! ## Composed-trace preservation of `SpqrInitDirOK` -/

open Symbolic.Swarm.CREF.TR.RecvHistStep2

private abbrev PDir (st : TRState) : Prop := SpqrInitDirOK st.spqr
private abbrev TracefulPDir {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  TracefulP PDir Q x

private theorem tracefulPDir_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat),
      TracefulPDir (fun _ => True) (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact TracefulP.pure trivial
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
      tracefulPDir_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

private theorem tracefulPDir_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    TracefulPDir (fun _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulP.bind (TracefulP.guardP _) fun _ _ => ?_
  intro tr htr
  dsimp only [liftM, monadLift, MonadLift.monadLift]
  rw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

private theorem tracefulPDir_logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulPDir (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr htr
  have hsnd : ((DY.ProtocolEvent.logEvent ev).run tr).2.val =
      tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk,
      Symbolic.DYBridge.DY.Trace.append_eq_1]
  rw [hsnd]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

private theorem tracefulPDir_lookupIdentity (p : Participant) (j : Nat) :
    TracefulPDir (fun _ => True) (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulP.bind (TracefulP.getEntry_any j) fun _ _ => ?_
  split
  · exact TracefulP.bind (TracefulP.guardP _) fun _ _ => TracefulP.pure trivial
  · exact TracefulP.failure

private theorem tracefulPDir_receiveSignalMsg (msgIdx : Nat) :
    TracefulPDir (fun _ => True) (receiveSignalMsg msgIdx) := by
  unfold receiveSignalMsg
  refine TracefulP.bind (TracefulP.receiveMessage msgIdx) fun _ _ => ?_
  split
  · exact TracefulP.bind (TracefulP.guardP _) fun _ _ => TracefulP.pure trivial
  · exact TracefulP.failure

private theorem tracefulPDir_dhRatchetStep {st : TRState} (pk : DY.Bytes) (hst : PDir st) :
    TracefulPDir (fun p : TRState × RecvChain => PDir p.1) (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulP.bind (TracefulP.guardP _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand 32) fun _ _ =>
    TracefulP.pure hst

private theorem tracefulPDir_ensureReceiverChain {st : TRState} (pk : DY.Bytes) (hst : PDir st) :
    TracefulPDir (fun p : TRState × RecvChain × Bool => PDir p.1) (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact TracefulP.pure hst
  · exact TracefulP.bind (tracefulPDir_dhRatchetStep pk hst) fun x (h : PDir x.1) =>
      TracefulP.pure h
  · exact TracefulP.failure

private theorem tracefulPDir_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulPDir (fun _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st _ =>
    TracefulP.bind (TracefulP.guardP _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand 32) fun _ _ =>
    TracefulP.bind (TracefulP.genRand coinsLen) fun coins _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.receiveMessage pqIdx) fun _ _ =>
    TracefulP.bind (TracefulP.logEvent _) fun _ _ => ?_
  exact TracefulP.bind
    (tracefulP_logMessageKeyAndStore (P := PDir) me _ .sender _ _ _ _ _
      (spqrInitDirOK_spqrSend_fst st.spqr coins))
    fun _ _ => TracefulP.sendMessage _

private theorem tracefulPDir_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulPDir (fun _ => True) (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st₀ hst₀ =>
    TracefulP.bind (tracefulPDir_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulP.bind (tracefulPDir_ensureReceiverChain msg.ratchetKey hst₀) fun x _ => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only
  split
  · next seed c' _ =>
    split
    · next spqr' key hspqr =>
      have hspqr' : PDir { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        spqrInitDirOK_of_spqrRecv hspqr
      refine TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPDir_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      have hrest : TracefulPDir (fun _ => True)
          (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                (msg.counter.toNat - c.index.toNat)
              DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulP.bind (tracefulPDir_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
            tracefulP_logMessageKeyAndStore (P := PDir) me _ .receiver _ _ _ _ _ hspqr'
      split
      · exact TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ => hrest
      · exact hrest
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem tracefulPDir_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulPDir (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st _ =>
    TracefulP.bind (tracefulPDir_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulP.bind (TracefulP.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TracefulP.bind (TracefulP.guardP _) fun _ _ =>
      TracefulP.bind (fun tr' htr' => by
        unfold guardTrace; rw [DY.Traceful.run_mk]; exact ⟨htr', fun _ _ => trivial⟩ :
        TracefulPDir (fun _ => True) (guardTrace _)) fun _ _ => ?_
    split
    · next spqr' key hspqr =>
      have hspqr' : PDir { st with spqr := spqr' } := spqrInitDirOK_of_spqrRecv hspqr
      exact TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPDir_verifyMacAndDecrypt st msg pqSalt _) fun _ _ =>
        TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
        TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
        tracefulP_logMessageKeyAndStore (P := PDir) me _ .receiver _ _ _ _ _ hspqr'
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem tracefulPDir_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulPDir (fun _ => True) (exposeKey me stateIdx k) := by
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

private theorem tracefulPDir_exposeSpqr (me : Participant) (stateIdx : Nat) :
    TracefulPDir (fun _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun _ _ => ?_
  exact TracefulP.bind (TracefulP.logEvent _) fun _ _ => TracefulP.sendMessage _

private theorem tracefulPDir_exposeSkipped (skippedKeyEventIdx : Nat) :
    TracefulPDir (fun _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulP.bind (TracefulP.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · exact TracefulP.bind (fun tr' htr' => by
        unfold guardTrace; rw [DY.Traceful.run_mk]; exact ⟨htr', fun _ _ => trivial⟩ :
        TracefulPDir (fun _ => True) (guardTrace _)) fun _ _ =>
      TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
      TracefulP.sendMessage _
  · exact TracefulP.failure

private theorem tracefulPDir_setupAct (a b : Participant) (withOpk : Bool) :
    TracefulPDir (fun _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  refine TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity a) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity b) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genSignedPrekey b _) fun _ _ =>
    TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genPQPrekey b _) fun _ _ => ?_
  split
  · exact TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genOneTimePrekey b) fun _ _ =>
      TracefulP.pure (Q := fun _ => True) trivial
  · exact TracefulP.pure (Q := fun _ => True) trivial

private theorem tracefulPDir_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulPDir (fun _ => True)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulP.bind (TracefulP.getKey a idStateIdx .identity); intro _ _
  apply TracefulP.bind (tracefulPDir_lookupIdentity b regIdxB); intro ikv _
  rcases ikv with ⟨_, _⟩; dsimp only
  apply TracefulP.bind (TracefulP.receiveMessage h.spk); intro _ _
  apply TracefulP.bind (TracefulP.receiveMessage h.spkSig); intro _ _
  apply TracefulP.bind (TracefulP.receiveMessage h.pqpk); intro _ _
  apply TracefulP.bind (TracefulP.receiveMessage h.pqpkSig); intro _ _
  apply TracefulP.bind (TracefulP.guardP _); intro _ _
  apply TracefulP.bind (TracefulP.guardP _); intro _ _
  split
  · apply TracefulP.bind (TracefulP.receiveMessage _); intro _ _
    apply TracefulP.bind (TracefulP.pure (Q := fun _ => True) trivial); intro _ _
    apply TracefulP.bind (TracefulP.genRand 32); intro _ _
    apply TracefulP.bind (TracefulP.guardP _); intro _ _
    apply TracefulP.bind (TracefulP.guardP _); intro _ _
    apply TracefulP.bind (TracefulP.genRand 32); intro _ _
    exact TracefulP.pure trivial
  · apply TracefulP.bind (TracefulP.pure (Q := fun _ => True) trivial); intro _ _
    apply TracefulP.bind (TracefulP.genRand 32); intro _ _
    apply TracefulP.bind (TracefulP.guardP _); intro _ _
    apply TracefulP.bind (TracefulP.guardP _); intro _ _
    apply TracefulP.bind (TracefulP.genRand 32); intro _ _
    exact TracefulP.pure trivial

private theorem tracefulPDir_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulPDir (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulP.bind (tracefulPDir_aliceHandshake a b idStateIdx regIdxB h) fun o _ => ?_
  refine TracefulP.bind (TracefulP.genRand 32) fun dhsA _ => ?_
  rcases createChain o.keys.rk o.spk dhsA with ⟨rkA, cksA⟩
  exact TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind tracefulP_traceLength fun _ _ =>
    TracefulP.bind (TracefulP.logEventPQ _) fun _ _ =>
    TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
    TracefulP.bind (tracefulPDir_logEventC _) fun _ _ =>
    TracefulP.storeLocalState (P := PDir) a (spqrInitDirOK_spqrInit_a2b o.keys.pqr)

private theorem tracefulPDir_bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulPDir (fun _ => True)
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
    refine TracefulP.bind (tracefulPDir_lookupIdentity a regIdxA) fun ikv _ => ?_
    rcases ikv with ⟨_, _⟩
    dsimp only
    refine TracefulP.bind (TracefulP.receiveMessage ekIdx) fun _ _ => ?_
    refine TracefulP.bind (TracefulP.receiveMessage ctIdx) fun _ _ => ?_
    refine TracefulP.bind (TracefulP.guardP _) fun _ _ => ?_
    split
    · exact TracefulP.pure trivial
    · exact TracefulP.failure

private theorem tracefulPDir_bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulPDir (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulP.bind (tracefulPDir_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o _ =>
    TracefulP.bind (tracefulPDir_receiveSignalMsg mh.msg) fun msg _ => ?_
  refine TracefulP.bind
    (tracefulPDir_ensureReceiverChain
      (st :=
        { peer := a, myIk := DY.Libsignal.PQXDH.serializedIk o.ikB,
          peerIk := DY.Libsignal.PQXDH.serializedIk o.ikA, rk := o.keys.rk,
          dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
          sid := Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
          initiator := false, rIdx := 0, recv := [],
          spqr := DY.Spqr.spqrInit o.keys.pqr spqrB2A })
      msg.ratchetKey (spqrInitDirOK_spqrInit_b2a o.keys.pqr))
    fun x _ => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only
  split
  · next seed c' _ =>
    split
    · next spqr' key hspqr =>
      have hspqr' : PDir { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        spqrInitDirOK_of_spqrRecv hspqr
      refine TracefulP.bind (TracefulP.sendMessage key) fun _ _ =>
        TracefulP.bind (TracefulP.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulP.bind (tracefulPDir_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
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
      all_goals exact TracefulP.bind (tracefulPDir_logEventC _) fun _ _ =>
          TracefulP.bind tracefulP_traceLength fun _ _ =>
          TracefulP.bind (tracefulPDir_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
          tracefulP_logMessageKeyAndStore (P := PDir) b _ .receiver _ _ _ _ _ hspqr'
    · exact TracefulP.failure
  · exact TracefulP.failure

private theorem traceStatesP_dir_move_next (m : Move) (tr : ExecTrace)
    (htr : TraceStatesP PDir tr) :
    TraceStatesP PDir (m.next tr) := by
  unfold Move.next Move.act
  cases m with
  | setup a b withOpk => exact (tracefulPDir_setupAct a b withOpk tr htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulP_run_snd (tracefulPDir_aliceStart a b idStateIdx regIdxB h) htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd (tracefulPDir_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulP_run_snd (tracefulPDir_messageEncrypt me stateIdx coinsLen pqIdx) htr
  | encryptAbort me stateIdx =>
    exact tracefulP_run_snd (tracefulP_messageEncryptAbort me stateIdx) htr
  | encryptFail me stateIdx coinsLen =>
    dsimp only
    exact ((TracefulP.bind tracefulP_traceLength
      fun n _ => TracefulP.bind (tracefulPDir_messageEncrypt me stateIdx coinsLen (n + 3))
        fun _ _ => TracefulP.pure (a := ()) (Q := fun _ => True) trivial) tr htr).1
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd (tracefulPDir_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulP_run_snd
      (tracefulPDir_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) htr
  | reject _ =>
    dsimp only
    rw [DY.Traceful.run_pure]
    exact htr
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
    exact tracefulP_run_snd (tracefulPDir_exposeKey me stateIdx k) htr
  | exposeSpqr me stateIdx =>
    exact tracefulP_run_snd (tracefulPDir_exposeSpqr me stateIdx) htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulP_run_snd (tracefulPDir_exposeSkipped skippedKeyEventIdx) htr
  | attackerSend msg =>
    exact tracefulP_run_snd (TracefulP.sendMessage msg) htr
  | brkDH =>
    exact (TracefulP.logEventPQ .BrokenDH tr htr).1
  | brkKEM =>
    exact (TracefulP.logEventPQ .BrokenKEM tr htr).1

private theorem traceStatesP_dir_runMoves (ms : List Move) (tr : ExecTrace)
    (htr : TraceStatesP PDir tr) :
    TraceStatesP PDir (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact htr
  | cons m ms ih => exact ih (m.next tr) (traceStatesP_dir_move_next m tr htr)

private theorem traceStatesP_dir_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    TraceStatesP PDir (runTraceMoves r₀ ms) :=
  traceStatesP_dir_runMoves ms (setupTrace r₀) (traceStatesP_setupTrace (P := PDir) r₀)

/-- Every `st` retrieved via `getLocalState p stateIdx` on `runTraceMoves r₀ ms` satisfies
`SpqrInitDirOK st.spqr`. -/
theorem spqrInitDirOK_of_getLocalState {r₀ : ProtocolSetup} {ms : List Move}
    {p : Participant} {stateIdx : Nat} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st) :
    SpqrInitDirOK st.spqr :=
  (TracefulP.getLocalState (P := PDir) p stateIdx (runTraceMoves r₀ ms)
    (traceStatesP_dir_runTrace r₀ ms)).2 st hst

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_spqrRecvState (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (st msg : DY.Bytes) :
    gamma interpretation S g (({ st := st, msg := msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack) =
      S.recvState (gamma interpretation S g st) (gamma interpretation S g msg) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll interpretation S g)]
  rfl

theorem gamma_spqrRecvKey (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (st msg : DY.Bytes) :
    gamma interpretation S g (({ st := st, msg := msg } : DY.Spqr.RecvKey.SubF DY.Bytes).pack) =
      spqrKeyBytes (S.recvKey (gamma interpretation S g st) (gamma interpretation S g msg)) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrRecvKey S) (concretizeAll interpretation S g)]
  rfl

/-- Post-state and `RecvKey` byte agreement under `hS : S = compSemOf interpretation r₀` and `ExternCryptoLawsHold`. -/
theorem spqrRecv_step_gamma_state_and_key_of_cryptoEq
    (interpretation : ExternInterpretation)
    (hlen : ∀ k d t, Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation k d = some t → t.length = 32)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms₁ : List Move) (body : HwBytes) (st_in : TRState) (g_rw : RecvWireGhost)
    (t : DY.Bytes) (msg : TRSignalMsg) (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hpq_pre : g_rw.sess.state.pqRatchetState = gamma interpretation S g st_in.spqr)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hparse : parseTrSignalMsg t = some msg) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey)) :
    gamma interpretation S g
      (({ st := st_in.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack) = newPqrState ∧
    gamma interpretation S g
      (({ st := st_in.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack) =
      spqrKeyBytes (saltToBytes pqrKey) := by
  obtain ⟨hst_of, hkey_of⟩ := spqrRecvOf_of_recv_ok interpretation hrecv_spqr
  have hpq_msg : gamma interpretation S g msg.pqRatchet = m.pqRatchet :=
    ((ht_rep.2.2.2 msg hparse).2.2.2 m htry).2.2.1
  rw [gamma_spqrRecvState, gamma_spqrRecvKey, ← hpq_pre, hpq_msg, hS]
  dsimp only [compSemOf, compSemOf, Symbolic.Swarm.SHARED.SpqrBytes.spqrRecvStateOf,
    Symbolic.Swarm.SHARED.SpqrBytes.spqrRecvKeyOf]
  rw [← Symbolic.Swarm.TRREF.MacFormBridge.spqrRecvStateOf_spqrSemOf_eq_spqrBytes interpretation hlen,
      ← Symbolic.Swarm.TRREF.MacFormBridge.spqrRecvKeyOf_spqrSemOf_eq_spqrBytes interpretation hlen,
      hst_of, hkey_of]
  exact ⟨rfl, rfl⟩

theorem spqrRecv_step_gamma_state_and_key
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms₁ : List Move) (body : HwBytes) (st_in : TRState) (g_rw : RecvWireGhost)
    (t : DY.Bytes) (msg : TRSignalMsg) (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hpq_pre : g_rw.sess.state.pqRatchetState = gamma interpretation S g st_in.spqr)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hparse : parseTrSignalMsg t = some msg) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey)) :
    gamma interpretation S g
      (({ st := st_in.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack) = newPqrState ∧
    gamma interpretation S g
      (({ st := st_in.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack) =
      spqrKeyBytes (saltToBytes pqrKey) :=
  spqrRecv_step_gamma_state_and_key_of_cryptoEq interpretation
    (Symbolic.Swarm.SHARED.HmacLen.hmacLen_of_ceh hceh)
    r₀ S hS g ms₁ body st_in g_rw t msg m newPqrState pqrKey hpq_pre ht_rep hparse htry hrecv_spqr

theorem spqrRecv_step_bridge_of_not_empty_pending
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms₁ : List Move) (p : Participant) (stateIdx : Nat) (recBytes body : HwBytes)
    (rec : RecordRec) (st st_in : TRState) (g_rw : RecvWireGhost)
    (t : DY.Bytes) (msg : TRSignalMsg) (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec) (hspqr_eq : st_in.spqr = st.spqr)
    (hcanon_q : Pure.slots_RecordCanonical_Q Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body) (hparse : parseTrSignalMsg t = some msg)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) (hempty : DY.Spqr.spqrEmptyMsg msg.pqRatchet = false)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey)) :
    g_rw.sess.state.pqRatchetState = gamma interpretation S g st_in.spqr ∧
    SpqrRecvStepOut interpretation S g st_in msg newPqrState pqrKey := by
  obtain ⟨_, _, _, hpq_in, hpre_eq, _, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g recBytes rec st st_in g_rw hrecBytes hrel hcanon_q hspqr_eq
  obtain ⟨hgam_st, hgam_key⟩ :=
    spqrRecv_step_gamma_state_and_key interpretation hceh r₀ S hS g ms₁ body st_in g_rw
      t msg m newPqrState pqrKey hpq_in ht_rep hparse htry hrecv_spqr
  have hinit_in : SpqrInitDirOK st_in.spqr := by rw [hspqr_eq]; exact spqrInitDirOK_of_getLocalState hst
  obtain ⟨spqr', key, hstep⟩ := spqrRecv_zero_isSome_of_not_empty_of_initDir hempty hinit_in
  have hst' := DY.Spqr.spqrRecv_state st_in.spqr msg.pqRatchet 0 (spqr', key) hstep
  dsimp only at hst'; refine ⟨hpq_in, ⟨hpre_eq, 0, spqr', key, hstep, ?_, hgam_key⟩⟩
  rw [hst']; exact hgam_st

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
