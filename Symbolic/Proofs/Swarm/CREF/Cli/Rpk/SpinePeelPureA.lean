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
import DY.Actions.Random
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkKDefs
public import Symbolic.Specifications.Refinement.Concretization
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedShapePure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Ratchet-Spine and PQXDH IKM Hole Invariants

Proves `spineRkK_and_ikmHolesK` and `ikmHolesKemK_of_loggedIkmRk` on reachable
composed traces under `AliceKemLen32`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo kdfCk computeMac)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

theorem memo_mem_of_computeMac_seed (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed peerIk myIk wire : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g seed).memo) :
    e ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.computeMac (trMsgKeys salt seed).macKey peerIk myIk wire)).memo :=
  TR.RecvDecStep.a2b_memo_mem_computeMac_seed i S g salt seed peerIk myIk wire he

theorem sp_pqxdhIkm_tail_eq {a₁ b₁ e₁ a₂ b₂ e₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes}
    {ss₁ ss₂ : DY.Bytes}
    (h : DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ e₁ d₁ ss₁ =
      DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ e₂ d₂ ss₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ e₁ = e₂ := by
  unfold DY.Libsignal.PQXDH.pqxdhIkm at h
  have h1 := (TR.G1.concat_injective h).2
  obtain ⟨ha, h2⟩ := TR.G1.concat_injective h1
  obtain ⟨hb, h3⟩ := TR.G1.concat_injective h2
  obtain ⟨he, _⟩ := TR.G1.concat_injective h3
  exact ⟨ha, hb, he⟩

theorem spineRkK_and_ikmHolesK {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop}
    {b : Bool} {v : DY.Bytes} (hv : TR.G1.Spine.SpineRkK K B b v) :
    TR.G1.Spine.SpineRkK K (fun c ikm => B c ikm ∧ TR.G1.Spine.IkmHolesK K ikm) b v := by
  induction hv with
  | hsRk hB hI => exact .hsRk ⟨hB, hI⟩ hI
  | hsCk hB hI => exact .hsCk ⟨hB, hI⟩ hI
  | rkStep1 _ hRk hD ih => exact .rkStep1 ih hRk hD
  | rkStep2 _ hRk hD ih => exact .rkStep2 ih hRk hD
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

section DoneOpkEkAkProof

open DY.Libsignal.PQXDH (PQXDHEvent pqxdhIkm registerIdentity registerCorruptIdentity
  genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK
  compromiseOPK breakDH breakKEM invertDH invertKEM)
open DY.Libsignal.TripleRatchet (TREvent KeyComponent KeyDir dhRatchetStep ensureReceiverChain
  logMessageKeyAndStore logSkippedKeys verifyMacAndDecrypt messageEncrypt messageEncryptAbort
  messageDecrypt messageDecryptSkipped exposeKey exposeSpqr exposeSkipped guardTrace)
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

def sp_DoneOpkEkAk (tr : ExecTrace) : Prop :=
  (∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    ∀ o, opk = some o → o.AttackerKnows tr) ∧
  (∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ek.AttackerKnows tr)

def isDoneEv : PQXDHEvent → Bool
  | .AliceDone .. => true
  | .BobDone .. => true
  | _ => false

def sp_NoDoneEv {α : Type} (f : Traceful α) : Prop :=
  ∀ tr ev idx, isDoneEv ev = true → ((f.run tr).2.val).EventLoggedAt ev idx →
    tr.EventLoggedAt ev idx

theorem sp_NoDoneEv.pure {α : Type} (x : α) : sp_NoDoneEv (Pure.pure x) :=
  fun _ _ _ _ h => by simpa only [DY.Traceful.run_pure] using h

theorem sp_NoDoneEv.failure {α : Type} : sp_NoDoneEv (Alternative.failure : Traceful α) :=
  fun _ _ _ _ h => by simpa only [DY.Traceful.run_failure] using h

theorem sp_run_bind_snd_nde {α β : Type} (f : Traceful α) (g : α → Traceful β) (tr : ExecTrace) :
    ((f >>= g).run tr).2.val =
      match (f.run tr).1 with
      | none => (f.run tr).2.val
      | some a => ((g a).run (f.run tr).2.val).2.val := by
  rw [Traceful.run_bind]
  rcases f.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (g a).run tr1.val with ⟨_, _⟩; rfl

theorem sp_NoDoneEv.bind {α β : Type} {f : Traceful α} {g : α → Traceful β}
    (hf : sp_NoDoneEv f) (hg : ∀ x, sp_NoDoneEv (g x)) : sp_NoDoneEv (f >>= g) := by
  intro tr ev idx hd h
  rw [sp_run_bind_snd_nde] at h
  rcases hrun : (f.run tr).1 with _ | x
  · rw [hrun] at h
    exact hf tr ev idx hd h
  · rw [hrun] at h
    exact hf tr ev idx hd (hg x _ ev idx hd h)

theorem sp_NoDoneEv.guardP (p : Prop) [Decidable p] : sp_NoDoneEv (_root_.guard p) := by
  intro tr ev idx hd h
  by_cases hp : p <;>
    simp only [_root_.guard, hp, ↓reduceIte, DY.Traceful.run_pure, DY.Traceful.run_failure] at h <;>
    exact h

private theorem noDoneEv_guardTrace (p : ExecTrace → Bool) : sp_NoDoneEv (guardTrace p) :=
  fun _ _ _ _ h => by simpa only [guardTrace, DY.Traceful.run_mk] using h

theorem sp_noDoneEv_guardOnTrace (p : ExecTrace → Bool) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.guardTrace p) :=
  fun _ _ _ _ h => by simpa only [DY.Libsignal.PQXDH.guardTrace, DY.Traceful.run_mk] using h

theorem sp_noDoneEv_traceLength : sp_NoDoneEv DY.Libsignal.TripleRatchet.traceLength :=
  fun _ _ _ _ h => by simpa only [DY.Libsignal.TripleRatchet.traceLength, DY.Traceful.run_mk] using h

private theorem noDoneEv_getEntry (E : Type) [ExecTraceTypes.Has E] (j : Nat) :
    sp_NoDoneEv (DY.getEntry j : Traceful E) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1] at h
  rw [Traceful.run_mk] at h
  dsimp only at h
  cases (tr.at? j : Option E) <;> exact h

theorem sp_noDoneEv_receiveMessage (j : Nat) : sp_NoDoneEv (DY.Network.receiveMessage j) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact sp_NoDoneEv.bind (noDoneEv_getEntry _ j) fun _ => sp_NoDoneEv.pure _

theorem sp_noDoneEv_receiveSignalMsg (j : Nat) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.receiveSignalMsg j) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine sp_NoDoneEv.bind (sp_noDoneEv_receiveMessage j) fun raw => ?_
  cases parseTrSignalMsg raw
  · exact sp_NoDoneEv.failure
  · exact sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ => sp_NoDoneEv.pure _

private theorem noDoneEv_getLocalStateTR (p : Participant) (j : Nat) :
    sp_NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact sp_NoDoneEv.bind (sp_NoDoneEv.bind (noDoneEv_getEntry _ j) fun _ => sp_NoDoneEv.pure _)
    fun _ => sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ => sp_NoDoneEv.pure _

private theorem noDoneEv_getLocalStatePQ (p : Participant) (j : Nat) :
    sp_NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful DY.Libsignal.PQXDH.PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact sp_NoDoneEv.bind (sp_NoDoneEv.bind (noDoneEv_getEntry _ j) fun _ => sp_NoDoneEv.pure _)
    fun _ => sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ => sp_NoDoneEv.pure _

private theorem noDoneEv_getKey (p : Participant) (j : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.getKey p j k) :=
  sp_NoDoneEv.bind (noDoneEv_getLocalStatePQ p j) fun _ =>
    sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ => sp_NoDoneEv.pure _

private theorem noDoneEv_genRand (n : Nat) : sp_NoDoneEv (DY.Random.genRand n) :=
  fun _ _ _ _ h => by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
    exact eventLoggedAt_append_other h rfl

theorem sp_noDoneEv_sendMessage (m : DY.Bytes) : sp_NoDoneEv (DY.Network.sendMessage m) :=
  fun _ _ _ _ h => by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
    exact eventLoggedAt_append_other h rfl

theorem sp_noDoneEv_logEventTR (e : TREvent) : sp_NoDoneEv (DY.ProtocolEvent.logEvent e) :=
  fun _ _ _ _ h => by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
    exact eventLoggedAt_append_other h rfl

theorem sp_noDoneEv_logEventC (e : DY.Libsignal.Composed.ComposedEvent) :
    sp_NoDoneEv (DY.ProtocolEvent.logEvent e) :=
  fun _ _ _ _ h => by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
    exact eventLoggedAt_append_other h rfl

private theorem noDoneEv_storeTR (p : Participant) (st : TRState) :
    sp_NoDoneEv (DY.PersistentLocalState.storeLocalState p st) :=
  fun _ _ _ _ h => by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
    exact eventLoggedAt_append_other h rfl

private theorem noDoneEv_storePQ (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    sp_NoDoneEv (DY.PersistentLocalState.storeLocalState p st) :=
  fun _ _ _ _ h => by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
    exact eventLoggedAt_append_other h rfl

theorem sp_noDoneEv_logEventPQ {e : PQXDHEvent} (he : isDoneEv e = false) :
    sp_NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx hd h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  rcases eventLoggedAt_append_ev_iff.mp h with ⟨_, h⟩ | ⟨_, rfl⟩
  · exact h
  · rw [he] at hd; cases hd

private theorem noDoneEv_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    sp_NoDoneEv (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 32) fun _ => sp_NoDoneEv.pure _

theorem sp_noDoneEv_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    sp_NoDoneEv (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact sp_NoDoneEv.pure _
  · exact sp_NoDoneEv.bind (noDoneEv_dhRatchetStep st pk) fun _ => sp_NoDoneEv.pure _
  · exact sp_NoDoneEv.failure

theorem sp_noDoneEv_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    sp_NoDoneEv (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ => noDoneEv_storeTR me st

theorem sp_noDoneEv_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), sp_NoDoneEv (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact sp_NoDoneEv.pure _
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
      sp_noDoneEv_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

theorem sp_noDoneEv_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) : sp_NoDoneEv (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ => ?_
  intro tr ev idx _ h
  cases DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
    (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext <;>
    simpa only [liftM, monadLift, MonadLift.monadLift, DY.Traceful.run_mk] using h

theorem sp_noDoneEv_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  exact sp_NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ =>
    sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand coinsLen) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_receiveMessage pqIdx) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ =>
    sp_noDoneEv_sendMessage _

theorem sp_noDoneEv_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact sp_NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 32) fun _ => sp_NoDoneEv.failure

theorem sp_noDoneEv_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine sp_NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun st₀ =>
    sp_NoDoneEv.bind (sp_noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    sp_NoDoneEv.bind (sp_noDoneEv_ensureReceiverChain st₀ msg.ratchetKey) fun ⟨st, c, _⟩ => ?_
  dsimp only
  split
  · split
    · refine sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ =>
        sp_NoDoneEv.bind (sp_noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        sp_NoDoneEv.bind (sp_noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      split
      · exact sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
          sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
          sp_NoDoneEv.bind (sp_noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
          sp_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · exact sp_NoDoneEv.bind (sp_noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
          sp_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact sp_NoDoneEv.failure
  · exact sp_NoDoneEv.failure

theorem sp_noDoneEv_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.messageDecryptSkipped
      me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine sp_NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun st =>
    sp_NoDoneEv.bind (sp_noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    sp_NoDoneEv.bind (noDoneEv_getEntry _ skippedKeyEventIdx) fun _ => ?_
  split
  · refine sp_NoDoneEv.bind (sp_NoDoneEv.guardP _) fun _ =>
      sp_NoDoneEv.bind (noDoneEv_guardTrace _) fun _ => ?_
    split
    · exact sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ =>
        sp_NoDoneEv.bind (sp_noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        sp_NoDoneEv.bind (sp_noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ =>
        sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
        sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ =>
        sp_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact sp_NoDoneEv.failure
  · exact sp_NoDoneEv.failure

theorem sp_noDoneEv_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine sp_NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ => ?_
  cases k with
  | rk => exact sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ => sp_noDoneEv_sendMessage _
  | dhs => exact sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ => sp_noDoneEv_sendMessage _
  | cks => exact sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ => sp_noDoneEv_sendMessage _
  | ckr _ =>
    dsimp only
    split
    · exact sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ => sp_noDoneEv_sendMessage _
    · exact sp_NoDoneEv.failure

theorem sp_noDoneEv_exposeSpqr (me : Participant) (stateIdx : Nat) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact sp_NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ => sp_noDoneEv_sendMessage _

theorem sp_noDoneEv_exposeSkipped (skippedKeyEventIdx : Nat) :
    sp_NoDoneEv (DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine sp_NoDoneEv.bind (noDoneEv_getEntry _ skippedKeyEventIdx) fun _ => ?_
  split
  · exact sp_NoDoneEv.bind (noDoneEv_guardTrace _) fun _ =>
      sp_NoDoneEv.bind (sp_noDoneEv_logEventTR _) fun _ => sp_noDoneEv_sendMessage _
  · exact sp_NoDoneEv.failure

theorem sp_noDoneEv_registerIdentity (p : Participant) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact sp_NoDoneEv.bind (sp_noDoneEv_guardOnTrace _) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ =>
    noDoneEv_storePQ p _

theorem sp_noDoneEv_genSignedPrekey (b : Participant) (j : Nat) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact sp_NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 64) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_storePQ b _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ => sp_NoDoneEv.pure _

theorem sp_noDoneEv_genPQPrekey (b : Participant) (j : Nat) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact sp_NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 64) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_genRand 64) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_storePQ b _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ => sp_NoDoneEv.pure _

theorem sp_noDoneEv_genOneTimePrekey (b : Participant) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact sp_NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ =>
    sp_NoDoneEv.bind (noDoneEv_storePQ b _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_sendMessage _) fun _ => sp_NoDoneEv.pure _

theorem sp_noDoneEv_compromiseIK (b : Participant) (j : Nat) :
    sp_NoDoneEv (compromiseIK b j) := by
  unfold compromiseIK
  exact sp_NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ => sp_noDoneEv_sendMessage _

theorem sp_noDoneEv_compromiseSPK (b : Participant) (j : Nat) :
    sp_NoDoneEv (compromiseSPK b j) := by
  unfold compromiseSPK
  exact sp_NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ => sp_noDoneEv_sendMessage _

theorem sp_noDoneEv_compromisePQSPK (b : Participant) (j : Nat) :
    sp_NoDoneEv (compromisePQSPK b j) := by
  unfold compromisePQSPK
  exact sp_NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ => sp_noDoneEv_sendMessage _

theorem sp_noDoneEv_compromiseOPK (b : Participant) (j : Nat) :
    sp_NoDoneEv (compromiseOPK b j) := by
  unfold compromiseOPK
  exact sp_NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_guardOnTrace _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ => sp_noDoneEv_sendMessage _

theorem sp_noDoneEv_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  exact sp_NoDoneEv.bind (sp_noDoneEv_guardOnTrace _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_receiveMessage skIdx) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_logEventPQ rfl) fun _ => sp_noDoneEv_logEventPQ rfl

theorem sp_noDoneEv_breakDH : sp_NoDoneEv DY.Libsignal.PQXDH.breakDH :=
  sp_noDoneEv_logEventPQ rfl

theorem sp_noDoneEv_breakKEM : sp_NoDoneEv DY.Libsignal.PQXDH.breakKEM :=
  sp_noDoneEv_logEventPQ rfl

theorem sp_noDoneEv_invertDH (inp : Nat) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.invertDH inp) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine sp_NoDoneEv.bind (sp_noDoneEv_guardOnTrace _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_receiveMessage inp) fun pk => ?_
  cases DY.Libsignal.PQXDH.extractDhSecretKey (DY.X25519.normalizeX25519Key pk)
  · exact sp_NoDoneEv.failure
  · exact sp_noDoneEv_sendMessage _

theorem sp_noDoneEv_invertKEM (inp : Nat) :
    sp_NoDoneEv (DY.Libsignal.PQXDH.invertKEM inp) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine sp_NoDoneEv.bind (sp_noDoneEv_guardOnTrace _) fun _ =>
    sp_NoDoneEv.bind (sp_noDoneEv_receiveMessage inp) fun pk =>
    sp_NoDoneEv.bind (fun tr ev idx _ h => ?_) fun _ => sp_noDoneEv_sendMessage _
  cases DY.PQKem.invertKemPublicKey pk <;>
    simpa only [liftM, monadLift, MonadLift.monadLift, DY.Traceful.run_mk] using h

end DoneOpkEkAkProof

end Symbolic.Swarm.CREF.CliPure
