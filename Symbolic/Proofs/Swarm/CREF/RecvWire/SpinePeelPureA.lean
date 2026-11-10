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
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieSeedShapePure
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
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
# `SpineRkK`, `IkmHolesK`, and `DoneOpkEkAk` Trace Combinators

Defines `DoneOpkEkAk` and `NoDoneEv`, and proves `spineRkK_and_ikmHolesK` along with `NoDoneEv`
preservation across `Traceful` ratchet and handshake subprograms.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo kdfCk computeMac)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

theorem rcv_resid_modelRun_pre {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc blk) :
    ModelRun r₀ (ms₀ ++ pre) := by
  have hreach : (runTraceMoves r₀ (ms₀ ++ pre)).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have h := hB.run
  rw [← List.append_assoc] at h
  exact modelRun_prefix_of_reachable h hreach

theorem memo_mem_of_computeMac_seed (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed peerIk myIk wire : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g seed).memo) :
    e ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.computeMac (trMsgKeys salt seed).macKey peerIk myIk wire)).memo :=
  TR.RecvDecStepTiePure.a2b_memo_mem_computeMac_seed i S g salt seed peerIk myIk wire he

theorem pqxdhIkm_tail_eq {a₁ b₁ e₁ a₂ b₂ e₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes}
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

def DoneOpkEkAk (tr : ExecTrace) : Prop :=
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

def NoDoneEv {α : Type} (f : Traceful α) : Prop :=
  ∀ tr ev idx, isDoneEv ev = true → ((f.run tr).2.val).EventLoggedAt ev idx →
    tr.EventLoggedAt ev idx

theorem NoDoneEv.pure {α : Type} (x : α) : NoDoneEv (Pure.pure x) := by
  intro _ _ _ _ h
  simp only [DY.Traceful.run_pure] at h
  exact h

theorem NoDoneEv.failure {α : Type} : NoDoneEv (Alternative.failure : Traceful α) := by
  intro _ _ _ _ h
  simp only [DY.Traceful.run_failure] at h
  exact h

theorem run_bind_snd_nde {α β : Type} (f : Traceful α) (g : α → Traceful β) (tr : ExecTrace) :
    ((f >>= g).run tr).2.val =
      match (f.run tr).1 with
      | none => (f.run tr).2.val
      | some a => ((g a).run (f.run tr).2.val).2.val := by
  rw [Traceful.run_bind]
  rcases f.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (g a).run tr1.val with ⟨_, _⟩; rfl

theorem NoDoneEv.bind {α β : Type} {f : Traceful α} {g : α → Traceful β}
    (hf : NoDoneEv f) (hg : ∀ x, NoDoneEv (g x)) : NoDoneEv (f >>= g) := by
  intro tr ev idx hd h
  rw [run_bind_snd_nde] at h
  rcases hrun : (f.run tr).1 with _ | x
  · rw [hrun] at h
    exact hf tr ev idx hd h
  · rw [hrun] at h
    exact hf tr ev idx hd (hg x _ ev idx hd h)

theorem NoDoneEv.guardP (p : Prop) [Decidable p] : NoDoneEv (_root_.guard p) := by
  intro tr ev idx hd h
  by_cases hp : p <;> simp [_root_.guard, hp, DY.Traceful.run_pure, DY.Traceful.run_failure] at h
  · exact h
  · exact h

theorem noDoneEv_guardTrace (p : ExecTrace → Bool) : NoDoneEv (guardTrace p) := by
  intro _ _ _ _ h
  unfold guardTrace at h
  rw [DY.Traceful.run_mk] at h
  exact h

theorem noDoneEv_guardOnTrace (p : ExecTrace → Bool) :
    NoDoneEv (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ _ _ _ h
  unfold DY.Libsignal.PQXDH.guardTrace at h
  rw [DY.Traceful.run_mk] at h
  exact h

theorem noDoneEv_traceLength : NoDoneEv DY.Libsignal.TripleRatchet.traceLength := by
  intro _ _ _ _ h
  unfold DY.Libsignal.TripleRatchet.traceLength at h
  rw [DY.Traceful.run_mk] at h
  exact h

theorem noDoneEv_getEntry (E : Type) [ExecTraceTypes.Has E] (j : Nat) :
    NoDoneEv (DY.getEntry j : Traceful E) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1] at h
  rw [Traceful.run_mk] at h
  dsimp only at h
  cases (tr.at? j : Option E) <;> exact h

theorem noDoneEv_receiveMessage (j : Nat) : NoDoneEv (DY.Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact NoDoneEv.bind (noDoneEv_getEntry _ j) fun _ => NoDoneEv.pure _

theorem noDoneEv_receiveSignalMsg (j : Nat) :
    NoDoneEv (DY.Libsignal.TripleRatchet.receiveSignalMsg j) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine NoDoneEv.bind (noDoneEv_receiveMessage j) fun raw => ?_
  cases parseTrSignalMsg raw
  · exact NoDoneEv.failure
  · exact NoDoneEv.bind (NoDoneEv.guardP _) fun _ => NoDoneEv.pure _

theorem noDoneEv_getLocalStateTR (p : Participant) (j : Nat) :
    NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact NoDoneEv.bind (NoDoneEv.bind (noDoneEv_getEntry _ j) fun _ => NoDoneEv.pure _)
    fun _ => NoDoneEv.bind (NoDoneEv.guardP _) fun _ => NoDoneEv.pure _

theorem noDoneEv_getLocalStatePQ (p : Participant) (j : Nat) :
    NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful DY.Libsignal.PQXDH.PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact NoDoneEv.bind (NoDoneEv.bind (noDoneEv_getEntry _ j) fun _ => NoDoneEv.pure _)
    fun _ => NoDoneEv.bind (NoDoneEv.guardP _) fun _ => NoDoneEv.pure _

theorem noDoneEv_getKey (p : Participant) (j : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
    NoDoneEv (DY.Libsignal.PQXDH.getKey p j k) :=
  NoDoneEv.bind (noDoneEv_getLocalStatePQ p j) fun _ =>
    NoDoneEv.bind (NoDoneEv.guardP _) fun _ => NoDoneEv.pure _

theorem noDoneEv_genRand (n : Nat) : NoDoneEv (DY.Random.genRand n) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem noDoneEv_sendMessage (m : DY.Bytes) : NoDoneEv (DY.Network.sendMessage m) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

theorem noDoneEv_logEventTR (e : TREvent) : NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem noDoneEv_logEventC (e : DY.Libsignal.Composed.ComposedEvent) :
    NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem noDoneEv_storeTR (p : Participant) (st : TRState) :
    NoDoneEv (DY.PersistentLocalState.storeLocalState p st) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

theorem noDoneEv_storePQ (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    NoDoneEv (DY.PersistentLocalState.storeLocalState p st) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

theorem noDoneEv_logEventPQ {e : PQXDHEvent} (he : isDoneEv e = false) :
    NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx hd h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  rcases eventLoggedAt_append_ev_iff.mp h with ⟨_, h⟩ | ⟨_, rfl⟩
  · exact h
  · rw [he] at hd; cases hd

theorem noDoneEv_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    NoDoneEv (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact NoDoneEv.bind (NoDoneEv.guardP _) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 32) fun _ => NoDoneEv.pure _

theorem noDoneEv_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    NoDoneEv (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact NoDoneEv.pure _
  · exact NoDoneEv.bind (noDoneEv_dhRatchetStep st pk) fun _ => NoDoneEv.pure _
  · exact NoDoneEv.failure

theorem noDoneEv_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    NoDoneEv (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact NoDoneEv.bind (noDoneEv_logEventTR _) fun _ => noDoneEv_storeTR me st

theorem noDoneEv_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), NoDoneEv (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact NoDoneEv.pure _
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
      noDoneEv_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

theorem noDoneEv_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) : NoDoneEv (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine NoDoneEv.bind (NoDoneEv.guardP _) fun _ => ?_
  intro tr ev idx _ h
  cases DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
    (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext
  · dsimp only [liftM, monadLift, MonadLift.monadLift] at h
    erw [DY.Traceful.run_mk] at h
    exact h
  · dsimp only [liftM, monadLift, MonadLift.monadLift] at h
    erw [DY.Traceful.run_mk] at h
    exact h

theorem noDoneEv_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    NoDoneEv (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  exact NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ =>
    NoDoneEv.bind (NoDoneEv.guardP _) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand coinsLen) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ =>
    NoDoneEv.bind (noDoneEv_receiveMessage pqIdx) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
    NoDoneEv.bind (noDoneEv_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ =>
    noDoneEv_sendMessage _

theorem noDoneEv_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    NoDoneEv (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 32) fun _ => NoDoneEv.failure

theorem noDoneEv_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    NoDoneEv (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun st₀ =>
    NoDoneEv.bind (noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    NoDoneEv.bind (noDoneEv_ensureReceiverChain st₀ msg.ratchetKey) fun ⟨st, c, _⟩ => ?_
  dsimp only
  split
  · split
    · refine NoDoneEv.bind (noDoneEv_sendMessage _) fun _ =>
        NoDoneEv.bind (noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        NoDoneEv.bind (noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      split
      · exact NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
          NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
          NoDoneEv.bind (noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
          noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · exact NoDoneEv.bind (noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
          noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact NoDoneEv.failure
  · exact NoDoneEv.failure

theorem noDoneEv_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    NoDoneEv (DY.Libsignal.TripleRatchet.messageDecryptSkipped
      me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun st =>
    NoDoneEv.bind (noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    NoDoneEv.bind (noDoneEv_getEntry _ skippedKeyEventIdx) fun _ => ?_
  split
  · refine NoDoneEv.bind (NoDoneEv.guardP _) fun _ =>
      NoDoneEv.bind (noDoneEv_guardTrace _) fun _ => ?_
    split
    · exact NoDoneEv.bind (noDoneEv_sendMessage _) fun _ =>
        NoDoneEv.bind (noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        NoDoneEv.bind (noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ =>
        NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
        NoDoneEv.bind (noDoneEv_logEventTR _) fun _ =>
        noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact NoDoneEv.failure
  · exact NoDoneEv.failure

theorem noDoneEv_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    NoDoneEv (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ => ?_
  cases k with
  | rk => exact NoDoneEv.bind (noDoneEv_logEventTR _) fun _ => noDoneEv_sendMessage _
  | dhs => exact NoDoneEv.bind (noDoneEv_logEventTR _) fun _ => noDoneEv_sendMessage _
  | cks => exact NoDoneEv.bind (noDoneEv_logEventTR _) fun _ => noDoneEv_sendMessage _
  | ckr _ =>
    dsimp only
    split
    · exact NoDoneEv.bind (noDoneEv_logEventTR _) fun _ => noDoneEv_sendMessage _
    · exact NoDoneEv.failure

theorem noDoneEv_exposeSpqr (me : Participant) (stateIdx : Nat) :
    NoDoneEv (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact NoDoneEv.bind (noDoneEv_getLocalStateTR me stateIdx) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventTR _) fun _ => noDoneEv_sendMessage _

theorem noDoneEv_exposeSkipped (skippedKeyEventIdx : Nat) :
    NoDoneEv (DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine NoDoneEv.bind (noDoneEv_getEntry _ skippedKeyEventIdx) fun _ => ?_
  split
  · exact NoDoneEv.bind (noDoneEv_guardTrace _) fun _ =>
      NoDoneEv.bind (noDoneEv_logEventTR _) fun _ => noDoneEv_sendMessage _
  · exact NoDoneEv.failure

theorem noDoneEv_registerIdentity (p : Participant) :
    NoDoneEv (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact NoDoneEv.bind (noDoneEv_guardOnTrace _) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ =>
    noDoneEv_storePQ p _

theorem noDoneEv_genSignedPrekey (b : Participant) (j : Nat) :
    NoDoneEv (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 64) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ =>
    NoDoneEv.bind (noDoneEv_storePQ b _) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ => NoDoneEv.pure _

theorem noDoneEv_genPQPrekey (b : Participant) (j : Nat) :
    NoDoneEv (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 64) fun _ =>
    NoDoneEv.bind (noDoneEv_genRand 64) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ =>
    NoDoneEv.bind (noDoneEv_storePQ b _) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ => NoDoneEv.pure _

theorem noDoneEv_genOneTimePrekey (b : Participant) :
    NoDoneEv (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact NoDoneEv.bind (noDoneEv_genRand 32) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ =>
    NoDoneEv.bind (noDoneEv_storePQ b _) fun _ =>
    NoDoneEv.bind (noDoneEv_sendMessage _) fun _ => NoDoneEv.pure _

theorem noDoneEv_compromiseIK (b : Participant) (j : Nat) :
    NoDoneEv (compromiseIK b j) := by
  unfold compromiseIK
  exact NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ => noDoneEv_sendMessage _

theorem noDoneEv_compromiseSPK (b : Participant) (j : Nat) :
    NoDoneEv (compromiseSPK b j) := by
  unfold compromiseSPK
  exact NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ => noDoneEv_sendMessage _

theorem noDoneEv_compromisePQSPK (b : Participant) (j : Nat) :
    NoDoneEv (compromisePQSPK b j) := by
  unfold compromisePQSPK
  exact NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ => noDoneEv_sendMessage _

theorem noDoneEv_compromiseOPK (b : Participant) (j : Nat) :
    NoDoneEv (compromiseOPK b j) := by
  unfold compromiseOPK
  exact NoDoneEv.bind (noDoneEv_getKey b j _) fun _ =>
    NoDoneEv.bind (noDoneEv_guardOnTrace _) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ => noDoneEv_sendMessage _

theorem noDoneEv_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    NoDoneEv (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  exact NoDoneEv.bind (noDoneEv_guardOnTrace _) fun _ =>
    NoDoneEv.bind (noDoneEv_receiveMessage skIdx) fun _ =>
    NoDoneEv.bind (noDoneEv_logEventPQ rfl) fun _ => noDoneEv_logEventPQ rfl

theorem noDoneEv_breakDH : NoDoneEv DY.Libsignal.PQXDH.breakDH :=
  noDoneEv_logEventPQ rfl

theorem noDoneEv_breakKEM : NoDoneEv DY.Libsignal.PQXDH.breakKEM :=
  noDoneEv_logEventPQ rfl

theorem noDoneEv_invertDH (inp : Nat) :
    NoDoneEv (DY.Libsignal.PQXDH.invertDH inp) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine NoDoneEv.bind (noDoneEv_guardOnTrace _) fun _ =>
    NoDoneEv.bind (noDoneEv_receiveMessage inp) fun pk => ?_
  cases DY.Libsignal.PQXDH.extractDhSecretKey (DY.X25519.normalizeX25519Key pk)
  · exact NoDoneEv.failure
  · exact noDoneEv_sendMessage _

theorem noDoneEv_invertKEM (inp : Nat) :
    NoDoneEv (DY.Libsignal.PQXDH.invertKEM inp) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine NoDoneEv.bind (noDoneEv_guardOnTrace _) fun _ =>
    NoDoneEv.bind (noDoneEv_receiveMessage inp) fun pk =>
    NoDoneEv.bind (by
      intro tr ev idx _ h
      cases DY.PQKem.invertKemPublicKey pk
      · dsimp only [liftM, monadLift, MonadLift.monadLift] at h
        erw [DY.Traceful.run_mk] at h
        exact h
      · dsimp only [liftM, monadLift, MonadLift.monadLift] at h
        erw [DY.Traceful.run_mk] at h
        exact h) fun _ => noDoneEv_sendMessage _

theorem doneOpkEkAk_nil : DoneOpkEkAk Trace.nil :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at h,
   fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at h⟩

end DoneOpkEkAkProof
end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
