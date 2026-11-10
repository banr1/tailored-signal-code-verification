/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.Actions.Network
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Mathlib.Tactic.Basic
public import Symbolic.Specifications.Concrete.SessionRecord
import Mathlib.Tactic.SplitIfs
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Reachability of Non-Empty Receiver Chains

Proves `allStoredRecvNonEmpty_runTrace`: every Triple Ratchet state stored along `runTraceMoves r₀ ms`
has `st.recv ≠ []`, so any `RecordRec` matching `st.recv.length` also has non-empty `receiverChains`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY DY.Comparse DY.Libsignal
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open DY.Libsignal.TripleRatchet (TRState SessionInfo RecvChain KeyComponent KeyDir findRecvChain
  setRecvChain recvChainFor maxReceiverChains dhRatchetStep ensureReceiverChain logSkippedKeys
  verifyMacAndDecrypt logMessageKeyAndStore receiveSignalMsg messageEncrypt messageEncryptAbort
  messageDecrypt messageDecryptSkipped exposeKey exposeSpqr exposeSkipped)
open Symbolic.Swarm.COMPOSED.CompTrace

abbrev PRecv (st : TRState) : Prop := st.recv ≠ []

/-- Every stored `(Participant × TRState)` entry in `tr` satisfies `st.recv ≠ []`. -/
def AllStoredRecvNonEmpty (tr : ExecTrace) : Prop :=
  ∀ (p : Participant) (st : TRState) (idx : Nat), TRStateStoredAt p st idx tr → PRecv st

/-- Lifts `AllStoredRecvNonEmpty` preservation to a `Traceful` computation with postcondition `Q`. -/
def TracefulPRecv {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr, AllStoredRecvNonEmpty tr →
    AllStoredRecvNonEmpty (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

private theorem tracefulPRecv_of_preserves {α : Type} {x : Traceful α}
    (hx : Preserves AllStoredRecvNonEmpty x) :
    TracefulPRecv (fun _ => True) x :=
  fun tr htr => ⟨hx tr htr, fun _ _ => trivial⟩

private theorem tracefulPRecv_pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    TracefulPRecv Q (Pure.pure a : Traceful α) := by
  intro tr htr
  rw [Traceful.run_pure]
  exact ⟨htr, fun _ h => by cases h; exact ha⟩

private theorem tracefulPRecv_failure {α : Type} {Q : α → Prop} :
    TracefulPRecv Q (failure : Traceful α) := by
  intro tr htr
  rw [Traceful.run_failure]
  exact ⟨htr, fun _ h => by cases h⟩

private theorem tracefulPRecv_bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulPRecv Q₁ x)
    (hf : ∀ a, Q₁ a → TracefulPRecv Q₂ (f a)) :
    TracefulPRecv Q₂ (x >>= f) := by
  intro tr htr
  obtain ⟨htr₁, hq₁⟩ := hx tr htr
  cases h : (x.run tr).1 with
  | none =>
    refine ⟨?_, ?_⟩
    · rw [run_bind_snd x f tr, h]; exact htr₁
    · intro b hb; rw [run_bind_fst x f tr, h] at hb; cases hb
  | some a =>
    obtain ⟨htr₂, hq₂⟩ := hf a (hq₁ a h) (x.run tr).2.val htr₁
    refine ⟨?_, ?_⟩
    · rw [run_bind_snd x f tr, h]; exact htr₂
    · intro b hb; rw [run_bind_fst x f tr, h] at hb; exact hq₂ b hb

private theorem preserves_genRand (n : Nat) :
    Preserves AllStoredRecvNonEmpty (Random.genRand n) := by
  intro tr htr p st idx hps
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure] at hps
  exact htr p st idx (trStateStoredAt_append_other rfl hps)

private theorem preserves_sendMessage (m : DY.Bytes) :
    Preserves AllStoredRecvNonEmpty (Network.sendMessage m) := by
  intro tr htr p st idx hps
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk] at hps
  exact htr p st idx (trStateStoredAt_append_other rfl hps)

private theorem preserves_logTR (ev : DY.Libsignal.TripleRatchet.TREvent) :
    Preserves AllStoredRecvNonEmpty (ProtocolEvent.logEvent ev) := by
  intro tr htr p st idx hps
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk,
    Traceful.run_pure] at hps
  exact htr p st idx (trStateStoredAt_append_other rfl hps)

private theorem preserves_logPQ (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    Preserves AllStoredRecvNonEmpty (ProtocolEvent.logEvent ev) := by
  intro tr htr p st idx hps
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk,
    Traceful.run_pure] at hps
  exact htr p st idx (trStateStoredAt_append_other rfl hps)

private theorem preserves_logC (ev : DY.Libsignal.Composed.ComposedEvent) :
    Preserves AllStoredRecvNonEmpty (ProtocolEvent.logEvent ev) := by
  intro tr htr p st idx hps
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk,
    Traceful.run_pure] at hps
  exact htr p st idx (trStateStoredAt_append_other rfl hps)

private theorem preserves_storePQ (p₀ : Participant) (st₀ : DY.Libsignal.PQXDH.PQXDHState) :
    Preserves AllStoredRecvNonEmpty (PersistentLocalState.storeLocalState p₀ st₀) := by
  intro tr htr p st idx hps
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk] at hps
  exact htr p st idx (trStateStoredAt_append_other rfl hps)

private theorem preserves_storeTR (p₀ : Participant) {st₀ : TRState} (hst₀ : PRecv st₀) :
    Preserves AllStoredRecvNonEmpty (PersistentLocalState.storeLocalState p₀ st₀) := by
  intro tr htr p st idx hps
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk] at hps
  rcases trStateStoredAt_append_same hps with ⟨_, hpre⟩ | ⟨_, _, rfl⟩
  · exact htr p st idx hpre
  · exact hst₀

private theorem tracefulPRecv_getLocalState (p : Participant) (stateIdx : Nat) :
    TracefulPRecv PRecv
      (PersistentLocalState.getLocalState p stateIdx : Traceful TRState) := by
  intro tr htr
  refine ⟨Preserves.getLocalState_tr p stateIdx tr htr, fun st hst => ?_⟩
  rw [getLocalState_tr_fst p stateIdx tr] at hst
  rcases hat : (tr.at? stateIdx : Option TRStEntry) with _ | ⟨⟨p', st'⟩⟩
  · rw [hat] at hst; cases hst
  · rw [hat] at hst; dsimp only at hst
    split_ifs at hst with hp
    · injection hst with hst_eq
      subst hp hst_eq
      exact htr p' st' stateIdx hat

private theorem setRecvChain_ne_nil {recv : List RecvChain} {c' : RecvChain}
    (h : recv ≠ []) : setRecvChain recv c' ≠ [] := by
  cases recv with
  | nil => exact False.elim (h rfl)
  | cons _ _ => intro hnil; cases hnil

private theorem drop_append_singleton_ne_nil (l : List RecvChain) (c : RecvChain) :
    List.drop (l.length + 1 - maxReceiverChains) (l ++ [c]) ≠ [] := by
  have hm : maxReceiverChains = 5 := rfl
  rw [List.ne_nil_iff_length_pos, List.length_drop, List.length_append, List.length_singleton, hm]
  omega

private theorem tracefulPRecv_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    TracefulPRecv (fun p : TRState × RecvChain => PRecv p.1) (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact tracefulPRecv_bind (tracefulPRecv_of_preserves (Preserves.guardP _)) fun _ _ =>
    tracefulPRecv_bind (tracefulPRecv_of_preserves (preserves_genRand 32)) fun _ _ =>
    tracefulPRecv_pure (drop_append_singleton_ne_nil st.recv _)

private theorem tracefulPRecv_ensureReceiverChain {st : TRState} (pk : DY.Bytes)
    (hst : PRecv st) :
    TracefulPRecv (fun p : TRState × RecvChain × Bool => PRecv p.1) (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact tracefulPRecv_pure hst
  · exact tracefulPRecv_bind (tracefulPRecv_dhRatchetStep st pk) fun x hx =>
      tracefulPRecv_pure hx
  · exact tracefulPRecv_failure

theorem tracefulPRecv_ensureReceiverChain_nil (st : TRState) (pk : DY.Bytes)
    (hnil : st.recv = []) :
    TracefulPRecv (fun p : TRState × RecvChain × Bool => PRecv p.1) (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · next c h =>
    unfold recvChainFor TRState.toDRState at h
    rw [hnil, findRecvChain] at h
    split_ifs at h <;> cases h
  · exact tracefulPRecv_bind (tracefulPRecv_dhRatchetStep st pk) fun x hx =>
      tracefulPRecv_pure hx
  · exact tracefulPRecv_failure

private theorem preserves_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat),
      Preserves AllStoredRecvNonEmpty (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact Preserves.pure ()
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact Preserves.bind (preserves_logTR _) fun _ =>
      preserves_logSkippedKeys s pk rIdx src (DY.Libsignal.TripleRatchet.kdfCk ck).1 (n + 1) k

private theorem preserves_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (rIdx prevStateIdx : Nat) (st : TRState) (hst : PRecv st) :
    Preserves AllStoredRecvNonEmpty
      (logMessageKeyAndStore me s dir seed pqSalt n rIdx prevStateIdx st) := by
  unfold logMessageKeyAndStore
  exact Preserves.bind (preserves_logTR _) fun _ =>
    preserves_storeTR me hst

private theorem preserves_registerIdentity (p : Participant) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (preserves_genRand 32) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    preserves_storePQ p _

private theorem preserves_getKey (p : Participant) (idx : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.getKey p idx kind) := by
  intro tr htr
  have h := bind_getKey_at (Inv := AllStoredRecvNonEmpty) p idx kind (f := Pure.pure) tr htr
    (fun _ _ => Preserves.pure _ tr htr)
  rw [run_bind_snd] at h
  rcases hrun : (DY.Libsignal.PQXDH.getKey p idx kind).run tr with ⟨o, t'⟩
  rw [hrun] at h
  cases o with
  | none => exact h
  | some _ => dsimp only at h; rwa [Traceful.run_pure] at h

private theorem preserves_genSignedPrekey (p : Participant) (idx : Nat) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.genSignedPrekey p idx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact Preserves.bind (preserves_getKey p idx _) fun _ =>
    Preserves.bind (preserves_genRand 32) fun _ =>
    Preserves.bind (preserves_genRand 64) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ =>
    Preserves.bind (preserves_storePQ p _) fun h =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.pure h

private theorem preserves_genPQPrekey (p : Participant) (idx : Nat) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.genPQPrekey p idx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact Preserves.bind (preserves_getKey p idx _) fun _ =>
    Preserves.bind (preserves_genRand 64) fun _ =>
    Preserves.bind (preserves_genRand 64) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ =>
    Preserves.bind (preserves_storePQ p _) fun h =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.pure h

private theorem preserves_genOneTimePrekey (p : Participant) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.genOneTimePrekey p) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact Preserves.bind (preserves_genRand 32) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ =>
    Preserves.bind (preserves_storePQ p _) fun h =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.pure h

private theorem preserves_setupAct (a b : Participant) (withOpk : Bool) :
    Preserves AllStoredRecvNonEmpty (setupAct a b withOpk) := by
  unfold setupAct
  refine Preserves.bind (preserves_registerIdentity a) fun _ =>
    Preserves.bind (preserves_registerIdentity b) fun _ =>
    Preserves.bind (preserves_genSignedPrekey b _) fun _ =>
    Preserves.bind (preserves_genPQPrekey b _) fun _ => ?_
  split
  · exact Preserves.bind (preserves_genOneTimePrekey b) fun _ => Preserves.pure _
  · exact Preserves.pure _

private theorem preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves AllStoredRecvNonEmpty (aliceStart a b idStateIdx regIdxB h) := by
  intro tr htr
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  have htr1 : AllStoredRecvNonEmpty (tr.append (RndE 32)) := by
    have h1 := preserves_genRand 32 tr htr
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure] at h1
    exact h1
  refine bind_aliceHandshake_at (Inv := AllStoredRecvNonEmpty) a b idStateIdx regIdxB h tr htr
    htr1 ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have htr2 : AllStoredRecvNonEmpty ((tr.append (RndE 32)).append (RndE 32)) := by
    have h2 := preserves_genRand 32 (tr.append (RndE 32)) htr1
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure] at h2
    exact h2
  refine (Preserves.bind (preserves_genRand 32) (fun dhsA => ?_)) _ htr2
  dsimp only
  exact Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.bind (preserves_sendMessage _) fun _ =>
    Preserves.bind Preserves.traceLength fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ =>
    Preserves.bind (preserves_logTR _) fun _ =>
    Preserves.bind (preserves_logC _) fun _ =>
    preserves_storeTR a (List.cons_ne_nil _ _)

private theorem preserves_bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves AllStoredRecvNonEmpty (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr htr
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at (Inv := AllStoredRecvNonEmpty) b a kh regIdxA mh.ek mh.ct tr htr ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ((tracefulPRecv_bind (Q₂ := fun _ => True)
    (tracefulPRecv_of_preserves (Preserves.receiveSignalMsg mh.msg)) fun msg _ => ?_) tr htr).1
  refine tracefulPRecv_bind (Q₂ := fun _ => True)
    (tracefulPRecv_ensureReceiverChain_nil _ msg.ratchetKey rfl) fun x hx => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hx ⊢
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      have hrecv' : PRecv { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        setRecvChain_ne_nil hx
      refine tracefulPRecv_of_preserves ?_
      refine Preserves.bind (preserves_sendMessage key) fun _ =>
        Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
        Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt seed) fun _ => ?_
      split
      · refine Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
          Preserves.bind (preserves_logPQ _) fun _ =>
          Preserves.bind Preserves.traceLength fun _ =>
          Preserves.bind (preserves_logPQ _) fun _ => ?_
        split
        · exact Preserves.bind (preserves_logTR _) fun _ =>
            Preserves.bind (preserves_logTR _) fun _ =>
            Preserves.bind (preserves_logC _) fun _ =>
            Preserves.bind Preserves.traceLength fun _ =>
            Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (preserves_logTR _) fun _ =>
            preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ hrecv'
        · exact Preserves.bind (preserves_logC _) fun _ =>
            Preserves.bind Preserves.traceLength fun _ =>
            Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (preserves_logTR _) fun _ =>
            preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ hrecv'
      · refine Preserves.bind Preserves.traceLength fun _ =>
          Preserves.bind (preserves_logPQ _) fun _ => ?_
        split
        · exact Preserves.bind (preserves_logTR _) fun _ =>
            Preserves.bind (preserves_logTR _) fun _ =>
            Preserves.bind (preserves_logC _) fun _ =>
            Preserves.bind Preserves.traceLength fun _ =>
            Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (preserves_logTR _) fun _ =>
            preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ hrecv'
        · exact Preserves.bind (preserves_logC _) fun _ =>
            Preserves.bind Preserves.traceLength fun _ =>
            Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (preserves_logTR _) fun _ =>
            preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ hrecv'
    · exact tracefulPRecv_failure
  · exact tracefulPRecv_failure

private theorem preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (messageEncrypt me stateIdx coinsLen pqIdx) := by
  intro tr htr
  unfold messageEncrypt
  refine ((tracefulPRecv_bind (Q₂ := fun _ => True)
    (tracefulPRecv_getLocalState me stateIdx) fun st hst => ?_) tr htr).1
  refine tracefulPRecv_of_preserves <|
    Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (preserves_genRand 32) fun m =>
    Preserves.bind (preserves_genRand coinsLen) fun coins => ?_
  rcases DY.Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩
  rcases DY.Libsignal.TripleRatchet.kdfCk st.cks with ⟨ck', seed⟩
  dsimp only
  exact Preserves.bind (preserves_sendMessage key) fun _ =>
    Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
    Preserves.bind (preserves_logTR _) fun _ =>
    Preserves.bind (preserves_logMessageKeyAndStore me _ .sender _ _ _ _ _ _ hst) fun _ =>
    preserves_sendMessage _

private theorem preserves_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun _ =>
    Preserves.bind (preserves_genRand 32) fun _ =>
    Preserves.failure

private theorem preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves AllStoredRecvNonEmpty (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  intro tr htr
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine ((tracefulPRecv_bind (Q₂ := fun _ => True)
    (tracefulPRecv_getLocalState me stateIdx) fun st₀ hst₀ =>
    tracefulPRecv_bind (Q₂ := fun _ => True)
      (tracefulPRecv_of_preserves (Preserves.receiveSignalMsg msgIdx)) fun msg _ =>
    tracefulPRecv_bind (Q₂ := fun _ => True)
      (tracefulPRecv_ensureReceiverChain msg.ratchetKey hst₀) fun x hx => ?_) tr htr).1
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hx ⊢
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      have hrecv' : PRecv { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
        setRecvChain_ne_nil hx
      refine tracefulPRecv_of_preserves <|
        Preserves.bind (preserves_sendMessage key) fun _ =>
        Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
        Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt seed) fun _ => ?_
      split
      · exact Preserves.bind (preserves_logTR _) fun _ =>
          Preserves.bind (preserves_logTR _) fun _ =>
          Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          Preserves.bind (preserves_logTR _) fun _ =>
          preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hrecv'
      · exact Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          Preserves.bind (preserves_logTR _) fun _ =>
          preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hrecv'
    · exact tracefulPRecv_failure
  · exact tracefulPRecv_failure

private theorem preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves AllStoredRecvNonEmpty
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  intro tr htr
  unfold messageDecryptSkipped
  refine ((tracefulPRecv_bind (Q₂ := fun _ => True)
    (tracefulPRecv_getLocalState me stateIdx) fun st hst =>
    tracefulPRecv_bind (Q₂ := fun _ => True)
      (tracefulPRecv_of_preserves (Preserves.receiveSignalMsg msgIdx)) fun msg _ =>
    tracefulPRecv_bind (Q₂ := fun _ => True)
      (tracefulPRecv_of_preserves (Preserves.getEntry skippedKeyEventIdx)) fun ev _ => ?_) tr htr).1
  split
  · refine tracefulPRecv_of_preserves <|
      Preserves.bind (Preserves.guardP _) fun _ =>
      Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    split
    · exact Preserves.bind (preserves_sendMessage _) fun _ =>
        Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
        Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt _) fun _ =>
        Preserves.bind (preserves_logTR _) fun _ =>
        Preserves.bind (preserves_logTR _) fun _ =>
        preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hst
    · exact Preserves.failure
  · exact tracefulPRecv_failure

private theorem preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    Preserves AllStoredRecvNonEmpty (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun _ => ?_
  cases k with
  | rk => exact Preserves.bind (preserves_logTR _) fun _ => preserves_sendMessage _
  | dhs => exact Preserves.bind (preserves_logTR _) fun _ => preserves_sendMessage _
  | cks => exact Preserves.bind (preserves_logTR _) fun _ => preserves_sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact Preserves.bind (preserves_logTR _) fun _ => preserves_sendMessage _
    · exact Preserves.failure

private theorem preserves_exposeSpqr (me : Participant) (stateIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun _ =>
    Preserves.bind (preserves_logTR _) fun _ => preserves_sendMessage _

private theorem preserves_exposeSkipped (skippedKeyEventIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine Preserves.bind (Preserves.getEntry skippedKeyEventIdx) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardTrace _) fun _ =>
      Preserves.bind (preserves_logTR _) fun _ => preserves_sendMessage _
  · exact Preserves.failure

private theorem preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact Preserves.bind (preserves_getKey p stateIdx _) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ => preserves_sendMessage _

private theorem preserves_compromiseSPK (p : Participant) (stateIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.compromiseSPK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact Preserves.bind (preserves_getKey p stateIdx _) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ => preserves_sendMessage _

private theorem preserves_compromisePQSPK (p : Participant) (stateIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.compromisePQSPK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact Preserves.bind (preserves_getKey p stateIdx _) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ => preserves_sendMessage _

private theorem preserves_compromiseOPK (p : Participant) (stateIdx : Nat) :
    Preserves AllStoredRecvNonEmpty (DY.Libsignal.PQXDH.compromiseOPK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact Preserves.bind (preserves_getKey p stateIdx _) fun _ =>
    Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (preserves_logPQ _) fun _ => preserves_sendMessage _

private theorem allStoredRecvNonEmpty_nil : AllStoredRecvNonEmpty Trace.nil := by
  intro p st idx h
  unfold TRStateStoredAt at h
  rw [Trace.at?_eq_some] at h
  obtain ⟨hlt, _⟩ := h
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt
  omega

private theorem allStoredRecvNonEmpty_setupTrace (r₀ : ProtocolSetup) :
    AllStoredRecvNonEmpty (setupTrace r₀) :=
  preserves_setupAct r₀.alice r₀.bob r₀.withOpk Trace.nil allStoredRecvNonEmpty_nil

private theorem preserves_void {α : Type} {f : Traceful α}
    (hf : Preserves AllStoredRecvNonEmpty f) :
    Preserves AllStoredRecvNonEmpty (do let _ ← f; pure ()) :=
  Preserves.bind hf fun _ => Preserves.pure ()

private theorem allStoredRecvNonEmpty_move_next (m : Move) (tr : ExecTrace)
    (htr : AllStoredRecvNonEmpty tr) :
    AllStoredRecvNonEmpty (m.next tr) := by
  unfold Move.next Move.act
  cases m with
  | setup a b withOpk => exact preserves_setupAct a b withOpk tr htr
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact preserves_void (preserves_aliceStart a b idStateIdx regIdxB h) tr htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact preserves_void (preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) tr htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact preserves_void (preserves_messageEncrypt me stateIdx coinsLen pqIdx) tr htr
  | encryptAbort me stateIdx =>
    exact preserves_void (preserves_messageEncryptAbort me stateIdx) tr htr
  | encryptFail me stateIdx coinsLen =>
    exact (Preserves.bind Preserves.traceLength fun n =>
      preserves_void (preserves_messageEncrypt me stateIdx coinsLen (n + 3))) tr htr
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact preserves_void (preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) tr htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact preserves_void
      (preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) tr htr
  | reject _ => exact Preserves.pure () tr htr
  | compromiseIK p stateIdx =>
    exact preserves_void (preserves_compromiseIK p stateIdx) tr htr
  | compromiseSPK p stateIdx =>
    exact preserves_void (preserves_compromiseSPK p stateIdx) tr htr
  | compromisePQSPK p stateIdx =>
    exact preserves_void (preserves_compromisePQSPK p stateIdx) tr htr
  | compromiseOPK p stateIdx =>
    exact preserves_void (preserves_compromiseOPK p stateIdx) tr htr
  | exposeKey me stateIdx k =>
    exact preserves_void (preserves_exposeKey me stateIdx k) tr htr
  | exposeSpqr me stateIdx =>
    exact preserves_void (preserves_exposeSpqr me stateIdx) tr htr
  | exposeSkipped skippedKeyEventIdx =>
    exact preserves_void (preserves_exposeSkipped skippedKeyEventIdx) tr htr
  | attackerSend msg => exact preserves_void (preserves_sendMessage msg) tr htr
  | brkDH =>
    exact preserves_logPQ .BrokenDH tr htr
  | brkKEM =>
    exact preserves_logPQ .BrokenKEM tr htr

private theorem allStoredRecvNonEmpty_runMoves (ms : List Move) (tr : ExecTrace)
    (htr : AllStoredRecvNonEmpty tr) :
    AllStoredRecvNonEmpty (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact htr
  | cons m ms ih => exact ih (m.next tr) (allStoredRecvNonEmpty_move_next m tr htr)

/-- Every stored `TRState` on `runTraceMoves r₀ ms` has `st.recv ≠ []`. -/
theorem allStoredRecvNonEmpty_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    AllStoredRecvNonEmpty (runTraceMoves r₀ ms) :=
  allStoredRecvNonEmpty_runMoves ms (setupTrace r₀) (allStoredRecvNonEmpty_setupTrace r₀)

theorem recv_ne_nil_of_getLocalState {r₀ : ProtocolSetup} {ms : List Move}
    {p : Participant} {stateIdx : Nat} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st) :
    st.recv ≠ [] :=
  (tracefulPRecv_getLocalState p stateIdx (runTraceMoves r₀ ms)
    (allStoredRecvNonEmpty_runTrace r₀ ms)).2 st hst

theorem receiverChains_ne_nil_of_length_eq {st : TRState} {rr : RecordRec}
    (hrecv : st.recv ≠ [])
    (hlen : rr.current.receiverChains.length = st.recv.length) :
    rr.current.receiverChains ≠ [] := by
  intro hnil
  rw [hnil, List.length_nil] at hlen
  exact hrecv (List.eq_nil_of_length_eq_zero hlen.symm)

theorem receiverChains_ne_nil_of_getLocalState_length {r₀ : ProtocolSetup} {ms : List Move}
    {p : Participant} {stateIdx : Nat} {st : TRState} {rr : RecordRec}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hlen : rr.current.receiverChains.length = st.recv.length) :
    rr.current.receiverChains ≠ [] :=
  receiverChains_ne_nil_of_length_eq (recv_ne_nil_of_getLocalState hst) hlen

end Symbolic.Swarm.CREF
