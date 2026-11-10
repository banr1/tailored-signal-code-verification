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
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkKDefs
public import Symbolic.Specifications.Refinement.Concretization
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HmacWireMemo
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# PQXDH Handshake-Done Event Preservation Helpers

Defines `spk_DoneOpkEkAk` and `spk_NoDoneEv`, proving per-action non-logging of `AliceDone`/`BobDone`
events together with PQXDH input-key-material injectivity and MAC memo propagation lemmas.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (computeMac)
open DY.Libsignal.TripleRatchet
open CryptoGames CryptoGames.LibsignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR

theorem spk_memo_mem_of_computeMac_seed_pk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed peerIk myIk wire : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g seed).memo) :
    e ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.computeMac (trMsgKeys salt seed).macKey peerIk myIk wire)).memo := by
  unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.trMsgKeys
  exact TR.G1.memo_mem_of_trunc8 i S g _ (TR.G1.Spine.memo_mem_of_kdfExtract_left i S g _ _
    (TR.G1.Spine.memo_mem_of_kdfExtract_left i S g _ _
      (TR.G1.Spine.memo_mem_of_kdfExtract_right i S g salt seed he)))

theorem spk_pqxdhIkm_tail_eq_pk {a₁ b₁ e₁ a₂ b₂ e₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes}
    {ss₁ ss₂ : DY.Bytes} :
    DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ e₁ d₁ ss₁ =
      DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ e₂ d₂ ss₂ →
    a₁ = a₂ ∧ b₁ = b₂ ∧ e₁ = e₂ ∧
      (match d₁ with | some v₁ => Concat.concat v₁ ss₁ | none => ss₁) =
        (match d₂ with | some v₂ => Concat.concat v₂ ss₂ | none => ss₂) := by
  intro h
  unfold DY.Libsignal.PQXDH.pqxdhIkm at h
  have h1 := (TR.G1.concat_injective h).2
  obtain ⟨ha, h2⟩ := TR.G1.concat_injective h1
  obtain ⟨hb, h3⟩ := TR.G1.concat_injective h2
  obtain ⟨he, h4⟩ := TR.G1.concat_injective h3
  cases d₁ <;> cases d₂ <;> exact ⟨ha, hb, he, h4⟩

theorem spk_spineRkK_and_ikmHolesK_pk {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop}
    {b : Bool} {v : DY.Bytes} (hv : TR.G1.Spine.SpineRkK K B b v) :
    TR.G1.Spine.SpineRkK K (fun c ikm => B c ikm ∧ TR.G1.Spine.IkmHolesK K ikm) b v := by
  induction hv with
  | hsRk hB hI => exact .hsRk ⟨hB, hI⟩ hI
  | hsCk hB hI => exact .hsCk ⟨hB, hI⟩ hI
  | rkStep1 _ hRk hD ih => exact .rkStep1 ih hRk hD
  | rkStep2 _ hRk hD ih => exact .rkStep2 ih hRk hD
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

section DoneOpkEkAkProofPk

open DY.Libsignal.PQXDH (PQXDHEvent pqxdhIkm registerIdentity registerCorruptIdentity
  genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK
  compromiseOPK breakDH breakKEM invertDH invertKEM)
open DY.Libsignal.TripleRatchet (TREvent KeyComponent KeyDir dhRatchetStep ensureReceiverChain
  logMessageKeyAndStore logSkippedKeys verifyMacAndDecrypt messageEncryptAbort messageDecrypt
  messageDecryptSkipped exposeKey exposeSpqr exposeSkipped guardTrace)
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompPresPQXDH (eventLoggedAt_append_other eventLoggedAt_append_ev_iff)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

def spk_DoneOpkEkAk (tr : ExecTrace) : Prop :=
  (∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    ∀ o, opk = some o → o.AttackerKnows tr) ∧
  (∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ek.AttackerKnows tr)

set_option quotPrecheck false in
local notation "isDoneEv_sppa223" => (fun (ev : PQXDHEvent) => match ev with
  | .AliceDone .. => true
  | .BobDone .. => true
  | _ => false)

def spk_NoDoneEv {α : Type} (f : Traceful α) : Prop :=
  ∀ tr ev idx, isDoneEv_sppa223 ev = true → ((f.run tr).2.val).EventLoggedAt ev idx →
    tr.EventLoggedAt ev idx

theorem spk_NoDoneEv.pure {α : Type} (x : α) : spk_NoDoneEv (Pure.pure x) := by
  intro tr ev idx _ h; rw [DY.Traceful.run_pure] at h; exact h

theorem spk_NoDoneEv.failure {α : Type} : spk_NoDoneEv (Alternative.failure : Traceful α) := by
  intro tr ev idx _ h; rw [DY.Traceful.run_failure] at h; exact h

theorem spk_run_bind_snd_nde {α β : Type} (f : Traceful α) (g : α → Traceful β) (tr : ExecTrace) :
    ((f >>= g).run tr).2.val =
      match (f.run tr).1 with
      | none => (f.run tr).2.val
      | some a => ((g a).run (f.run tr).2.val).2.val := by
  rw [Traceful.run_bind]
  rcases f.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (g a).run tr1.val with ⟨_, _⟩; rfl

theorem spk_NoDoneEv.bind {α β : Type} {f : Traceful α} {g : α → Traceful β}
    (hf : spk_NoDoneEv f) (hg : ∀ x, spk_NoDoneEv (g x)) : spk_NoDoneEv (f >>= g) := by
  intro tr ev idx hd h
  rw [spk_run_bind_snd_nde] at h
  rcases hrun : (f.run tr).1 with _ | x
  · rw [hrun] at h; exact hf tr ev idx hd h
  · rw [hrun] at h; exact hf tr ev idx hd (hg x _ ev idx hd h)

theorem spk_NoDoneEv.guardP (p : Prop) [Decidable p] : spk_NoDoneEv (_root_.guard p) := by
  unfold _root_.guard; split
  · exact spk_NoDoneEv.pure _
  · exact spk_NoDoneEv.failure

private theorem noDoneEv_guardTrace_sppa223 (p : ExecTrace → Bool) : spk_NoDoneEv (guardTrace p) := by
  intro tr ev idx _ h; unfold guardTrace at h; rw [DY.Traceful.run_mk] at h; exact h

theorem spk_noDoneEv_guardOnTrace (p : ExecTrace → Bool) :
    spk_NoDoneEv (DY.Libsignal.PQXDH.guardTrace p) := by
  intro tr ev idx _ h
  unfold DY.Libsignal.PQXDH.guardTrace at h; rw [DY.Traceful.run_mk] at h; exact h

theorem spk_noDoneEv_traceLength : spk_NoDoneEv DY.Libsignal.TripleRatchet.traceLength := by
  intro tr ev idx _ h
  unfold DY.Libsignal.TripleRatchet.traceLength at h; rw [DY.Traceful.run_mk] at h; exact h

private theorem noDoneEv_getEntry_sppa223 (E : Type) [ExecTraceTypes.Has E] (j : Nat) :
    spk_NoDoneEv (DY.getEntry j : Traceful E) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1] at h; rw [Traceful.run_mk] at h; dsimp only at h
  cases (tr.at? j : Option E) <;> exact h

theorem spk_noDoneEv_receiveMessage (j : Nat) : spk_NoDoneEv (DY.Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact spk_NoDoneEv.bind (noDoneEv_getEntry_sppa223 _ j) fun _ => spk_NoDoneEv.pure _

theorem spk_noDoneEv_receiveSignalMsg (j : Nat) :
    spk_NoDoneEv (DY.Libsignal.TripleRatchet.receiveSignalMsg j) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine spk_NoDoneEv.bind (spk_noDoneEv_receiveMessage j) fun raw => ?_
  cases parseTrSignalMsg raw
  · exact spk_NoDoneEv.failure
  · exact spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ => spk_NoDoneEv.pure _

private theorem noDoneEv_getLocalStateTR_sppa223 (p : Participant) (j : Nat) :
    spk_NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact spk_NoDoneEv.bind (spk_NoDoneEv.bind (noDoneEv_getEntry_sppa223 _ j) fun _ => spk_NoDoneEv.pure _)
    fun _ => spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ => spk_NoDoneEv.pure _

private theorem noDoneEv_getLocalStatePQ_sppa223 (p : Participant) (j : Nat) :
    spk_NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful DY.Libsignal.PQXDH.PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact spk_NoDoneEv.bind (spk_NoDoneEv.bind (noDoneEv_getEntry_sppa223 _ j) fun _ => spk_NoDoneEv.pure _)
    fun _ => spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ => spk_NoDoneEv.pure _

private theorem noDoneEv_getKey_sppa223 (p : Participant) (j : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
    spk_NoDoneEv (DY.Libsignal.PQXDH.getKey p j k) :=
  spk_NoDoneEv.bind (noDoneEv_getLocalStatePQ_sppa223 p j) fun _ =>
    spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ => spk_NoDoneEv.pure _

private theorem noDoneEv_genRand_sppa223 (n : Nat) : spk_NoDoneEv (DY.Random.genRand n) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem spk_noDoneEv_sendMessage (m : DY.Bytes) : spk_NoDoneEv (DY.Network.sendMessage m) := by
  intro tr ev idx _ h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

theorem spk_noDoneEv_logEventTR (e : TREvent) : spk_NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem spk_noDoneEv_logEventC (e : DY.Libsignal.Composed.ComposedEvent) :
    spk_NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem spk_noDoneEv_logEventPQ {e : PQXDHEvent} (he : isDoneEv_sppa223 e = false) :
    spk_NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx hd h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  rcases eventLoggedAt_append_ev_iff.mp h with ⟨_, h⟩ | ⟨_, rfl⟩
  · exact h
  · rw [he] at hd; cases hd

private theorem noDoneEv_storeTR_sppa223 (p : Participant) (st : TRState) :
    spk_NoDoneEv (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr ev idx _ h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

private theorem noDoneEv_storePQ_sppa223 (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    spk_NoDoneEv (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr ev idx _ h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

private theorem noDoneEv_dhRatchetStep_sppa223 (st : TRState) (pk : DY.Bytes) :
    spk_NoDoneEv (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 32) fun _ => spk_NoDoneEv.pure _

theorem spk_noDoneEv_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    spk_NoDoneEv (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact spk_NoDoneEv.pure _
  · exact spk_NoDoneEv.bind (noDoneEv_dhRatchetStep_sppa223 st pk) fun _ => spk_NoDoneEv.pure _
  · exact spk_NoDoneEv.failure

theorem spk_noDoneEv_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    spk_NoDoneEv (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ => noDoneEv_storeTR_sppa223 me st

theorem spk_noDoneEv_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), spk_NoDoneEv (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact spk_NoDoneEv.pure _
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
      spk_noDoneEv_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

theorem spk_noDoneEv_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) : spk_NoDoneEv (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ => ?_
  intro tr ev idx _ h
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rw [DY.Traceful.run_mk] at h
  exact h

theorem spk_noDoneEv_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    spk_NoDoneEv (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  exact spk_NoDoneEv.bind (noDoneEv_getLocalStateTR_sppa223 me stateIdx) fun _ =>
    spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 32) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 coinsLen) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_receiveMessage pqIdx) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ =>
    spk_noDoneEv_sendMessage _

theorem spk_noDoneEv_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    spk_NoDoneEv (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact spk_NoDoneEv.bind (noDoneEv_getLocalStateTR_sppa223 me stateIdx) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 32) fun _ => spk_NoDoneEv.failure

theorem spk_noDoneEv_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) : spk_NoDoneEv (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine spk_NoDoneEv.bind (noDoneEv_getLocalStateTR_sppa223 me stateIdx) fun st₀ =>
    spk_NoDoneEv.bind (spk_noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    spk_NoDoneEv.bind (spk_noDoneEv_ensureReceiverChain st₀ msg.ratchetKey) fun ⟨st, c, _⟩ => ?_
  dsimp only
  split
  · split
    · refine spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ =>
        spk_NoDoneEv.bind (spk_noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        spk_NoDoneEv.bind (spk_noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      split
      · exact spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
          spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
          spk_NoDoneEv.bind (spk_noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
          spk_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · exact spk_NoDoneEv.bind (spk_noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
          spk_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact spk_NoDoneEv.failure
  · exact spk_NoDoneEv.failure

theorem spk_noDoneEv_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    spk_NoDoneEv (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine spk_NoDoneEv.bind (noDoneEv_getLocalStateTR_sppa223 me stateIdx) fun st =>
    spk_NoDoneEv.bind (spk_noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    spk_NoDoneEv.bind (noDoneEv_getEntry_sppa223 _ skippedKeyEventIdx) fun _ => ?_
  split
  · refine spk_NoDoneEv.bind (spk_NoDoneEv.guardP _) fun _ =>
      spk_NoDoneEv.bind (noDoneEv_guardTrace_sppa223 _) fun _ => ?_
    split
    · exact spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ =>
        spk_NoDoneEv.bind (spk_noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        spk_NoDoneEv.bind (spk_noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ =>
        spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
        spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ =>
        spk_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact spk_NoDoneEv.failure
  · exact spk_NoDoneEv.failure

theorem spk_noDoneEv_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    spk_NoDoneEv (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine spk_NoDoneEv.bind (noDoneEv_getLocalStateTR_sppa223 me stateIdx) fun _ => ?_
  cases k with
  | rk => exact spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ => spk_noDoneEv_sendMessage _
  | dhs => exact spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ => spk_noDoneEv_sendMessage _
  | cks => exact spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ => spk_noDoneEv_sendMessage _
  | ckr _ =>
    dsimp only; split
    · exact spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ => spk_noDoneEv_sendMessage _
    · exact spk_NoDoneEv.failure

theorem spk_noDoneEv_exposeSpqr (me : Participant) (stateIdx : Nat) :
    spk_NoDoneEv (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact spk_NoDoneEv.bind (noDoneEv_getLocalStateTR_sppa223 me stateIdx) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ => spk_noDoneEv_sendMessage _

theorem spk_noDoneEv_exposeSkipped (skippedKeyEventIdx : Nat) :
    spk_NoDoneEv (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine spk_NoDoneEv.bind (noDoneEv_getEntry_sppa223 _ skippedKeyEventIdx) fun _ => ?_
  split
  · exact spk_NoDoneEv.bind (noDoneEv_guardTrace_sppa223 _) fun _ =>
      spk_NoDoneEv.bind (spk_noDoneEv_logEventTR _) fun _ => spk_noDoneEv_sendMessage _
  · exact spk_NoDoneEv.failure

theorem spk_noDoneEv_registerIdentity (p : Participant) :
    spk_NoDoneEv (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact spk_NoDoneEv.bind (spk_noDoneEv_guardOnTrace _) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 32) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ => noDoneEv_storePQ_sppa223 p _

theorem spk_noDoneEv_genSignedPrekey (b : Participant) (j : Nat) :
    spk_NoDoneEv (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact spk_NoDoneEv.bind (noDoneEv_getKey_sppa223 b j _) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 32) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 64) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_storePQ_sppa223 b _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ => spk_NoDoneEv.pure _

theorem spk_noDoneEv_genPQPrekey (b : Participant) (j : Nat) :
    spk_NoDoneEv (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact spk_NoDoneEv.bind (noDoneEv_getKey_sppa223 b j _) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 64) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 64) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_storePQ_sppa223 b _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ => spk_NoDoneEv.pure _

theorem spk_noDoneEv_genOneTimePrekey (b : Participant) :
    spk_NoDoneEv (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact spk_NoDoneEv.bind (noDoneEv_genRand_sppa223 32) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ =>
    spk_NoDoneEv.bind (noDoneEv_storePQ_sppa223 b _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_sendMessage _) fun _ => spk_NoDoneEv.pure _

theorem spk_noDoneEv_compromiseIK (b : Participant) (j : Nat) :
    spk_NoDoneEv (compromiseIK b j) := by
  unfold compromiseIK
  exact spk_NoDoneEv.bind (noDoneEv_getKey_sppa223 b j _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ => spk_noDoneEv_sendMessage _

theorem spk_noDoneEv_compromiseSPK (b : Participant) (j : Nat) :
    spk_NoDoneEv (compromiseSPK b j) := by
  unfold compromiseSPK
  exact spk_NoDoneEv.bind (noDoneEv_getKey_sppa223 b j _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ => spk_noDoneEv_sendMessage _

theorem spk_noDoneEv_compromisePQSPK (b : Participant) (j : Nat) :
    spk_NoDoneEv (compromisePQSPK b j) := by
  unfold compromisePQSPK
  exact spk_NoDoneEv.bind (noDoneEv_getKey_sppa223 b j _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ => spk_noDoneEv_sendMessage _

theorem spk_noDoneEv_compromiseOPK (b : Participant) (j : Nat) :
    spk_NoDoneEv (compromiseOPK b j) := by
  unfold compromiseOPK
  exact spk_NoDoneEv.bind (noDoneEv_getKey_sppa223 b j _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_guardOnTrace _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ => spk_noDoneEv_sendMessage _

theorem spk_noDoneEv_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    spk_NoDoneEv (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  exact spk_NoDoneEv.bind (spk_noDoneEv_guardOnTrace _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_receiveMessage skIdx) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_logEventPQ rfl) fun _ => spk_noDoneEv_logEventPQ rfl

theorem spk_noDoneEv_breakDH : spk_NoDoneEv DY.Libsignal.PQXDH.breakDH :=
  spk_noDoneEv_logEventPQ rfl

theorem spk_noDoneEv_breakKEM : spk_NoDoneEv DY.Libsignal.PQXDH.breakKEM :=
  spk_noDoneEv_logEventPQ rfl

theorem spk_noDoneEv_invertDH (inp : Nat) : spk_NoDoneEv (DY.Libsignal.PQXDH.invertDH inp) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine spk_NoDoneEv.bind (spk_noDoneEv_guardOnTrace _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_receiveMessage inp) fun pk => ?_
  cases DY.Libsignal.PQXDH.extractDhSecretKey (DY.X25519.normalizeX25519Key pk)
  · exact spk_NoDoneEv.failure
  · exact spk_noDoneEv_sendMessage _

theorem spk_noDoneEv_invertKEM (inp : Nat) : spk_NoDoneEv (DY.Libsignal.PQXDH.invertKEM inp) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine spk_NoDoneEv.bind (spk_noDoneEv_guardOnTrace _) fun _ =>
    spk_NoDoneEv.bind (spk_noDoneEv_receiveMessage inp) fun pk =>
      spk_NoDoneEv.bind ?_ fun _ => spk_noDoneEv_sendMessage _
  intro tr ev idx _ h
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rw [DY.Traceful.run_mk] at h
  exact h

end DoneOpkEkAkProofPk

end Symbolic.Swarm.CREF.CliPure
