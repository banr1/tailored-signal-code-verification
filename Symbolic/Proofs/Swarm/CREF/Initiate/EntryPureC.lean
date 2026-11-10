/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.Random
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecordsBridgePure
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Swarm.CREF.Initiate.PostTrace
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# `session_initiate` Randomness Bounds and Setup Handle Pinning

Bounds visible entries of `bobStart`, `decrypt`, and `decryptSkipped` via `AtMost1Rand`, and
maintains `IniFrame` and `SetupIni` across non-setup moves to pin Alice's identity-key state at
index `4` and Bob's `IdentityRegistered` event at index `6`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.IniPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
cref_open
open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Symbolic.Swarm.CREF.TR (StE EvE)
open Symbolic.Swarm.CREF.TR.RecvDec
  (at?_append_of_lt at?_eq_none_of_le at?_append_non_entry logSkippedKeysTr getLocalState_snd)

private abbrev PQStEntry :=
  PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
private abbrev TREntryP := DY.ProtocolEvent.ExecEntryT TREvent
private abbrev StEntryP :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private abbrev PQEvEntryP :=
  DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent
private abbrev CEvEntryP :=
  DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent

private def NoRand (t t' : ExecTrace) : Prop :=
  ∀ i : Nat, (t'.at? i : Option Random.ExecEntryT) = (t.at? i : Option Random.ExecEntryT)

private def NoRandOp {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, NoRand tr (x.run tr).2.val

private theorem NoRandOp.of_id {α : Type} {x : Traceful α} (h : ∀ tr, (x.run tr).2.val = tr) :
    NoRandOp x := fun tr _ => by rw [h tr]

private theorem NoRandOp.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoRandOp x) (hf : ∀ a, NoRandOp (f a)) : NoRandOp (x >>= f) := by
  intro tr i; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx tr i
  · exact (hf a (x.run tr).2.val i).trans (hx tr i)

private theorem ini_xfix_pure {α : Type} (a : α) : XplSteps.XFix (pure a : Traceful α) :=
  fun _ => by rw [Traceful.run_pure]

private theorem ini_xfix_failure {α : Type} : XplSteps.XFix (failure : Traceful α) :=
  fun _ => by rw [Traceful.run_failure]

private theorem ini_xfix_traceLength : XplSteps.XFix TripleRatchet.traceLength :=
  fun _ => by unfold TripleRatchet.traceLength; rw [Traceful.run_mk]

private theorem ini_xfix_guardTrace (p : ExecTrace → Bool) :
    XplSteps.XFix (TripleRatchet.guardTrace p) :=
  fun _ => by unfold TripleRatchet.guardTrace; rw [Traceful.run_mk]

private theorem ini_xfix_requireTracePredicate (p : ExecTrace → Bool) :
    XplSteps.XFix (DY.Libsignal.PQXDH.guardTrace p) :=
  fun _ => by unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]

private theorem ini_xfix_monadLift {α : Type} (x : DY.Err α) :
    XplSteps.XFix (monadLift x : Traceful α) :=
  fun _ => by
    rw [show (monadLift x : Traceful α) = Traceful.mk (fun tr => (x, ⟨tr, Trace.le_refl tr⟩)) from rfl,
      Traceful.run_mk]

private theorem ini_xfix_getEntry {E : Type} [ExecTraceTypes.Has E] (i : Nat) :
    XplSteps.XFix (DY.getEntry i : Traceful E) :=
  fun _ => by rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]

private theorem NoRandOp.sendMessage (m : DY.Bytes) : NoRandOp (Network.sendMessage m) :=
  fun tr i => by
    rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    exact at?_append_non_entry tr (⟨m⟩ : Network.ExecEntryT) rfl i

private theorem NoRandOp.storeLocalState (p : Participant) (st : TRState) :
    NoRandOp (PersistentLocalState.storeLocalState p st) :=
  fun tr i => by
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    exact at?_append_non_entry tr (⟨⟨p, st⟩⟩ : StEntryP) rfl i

private theorem NoRandOp.logEventPQ (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    NoRandOp (DY.ProtocolEvent.logEvent ev) := fun tr i => by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact at?_append_non_entry tr (⟨ev⟩ : PQEvEntryP) rfl i

private theorem NoRandOp.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    NoRandOp (DY.ProtocolEvent.logEvent ev) := fun tr i => by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact at?_append_non_entry tr (⟨ev⟩ : CEvEntryP) rfl i

private theorem NoRandOp.logEventTR (ev : TREvent) :
    NoRandOp (DY.ProtocolEvent.logEvent ev) := fun tr i => by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact at?_append_non_entry tr (⟨ev⟩ : TREntryP) rfl i

private theorem NoRandOp.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    NoRandOp (TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  intro tr i; rw [(Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeys_run s pk rIdx src ck n k tr).2]
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih => unfold logSkippedKeysTr; exact (ih _ _ _).trans (at?_append_non_entry tr _ rfl i)

private theorem NoRandOp.logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (r par : Nat) (st : TRState) :
    NoRandOp (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact NoRandOp.bind (NoRandOp.logEventTR _) fun _ => NoRandOp.storeLocalState _ _

private def AtMost1Rand (tr t : ExecTrace) : Prop :=
  ∀ i : Nat, tr.length + 1 ≤ i → (t.at? i : Option Random.ExecEntryT) = none

private theorem atMost1Rand_refl (tr : ExecTrace) : AtMost1Rand tr tr :=
  fun _ hi => at?_eq_none_of_le tr (by omega)

private theorem atMost1Rand_of_noRand {tr t t' : ExecTrace} (h1 : AtMost1Rand tr t)
    (h2 : NoRand t t') : AtMost1Rand tr t' := fun i hi => (h2 i).trans (h1 i hi)

private theorem atMost1Rand_bind_noRandOp {α β : Type} {tr : ExecTrace}
    {x : Traceful α} {f : α → Traceful β}
    (hx : AtMost1Rand tr (x.run tr).2.val) (hf : ∀ a, NoRandOp (f a)) :
    AtMost1Rand tr ((x >>= f).run tr).2.val := by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx
  · exact atMost1Rand_of_noRand hx (hf a _)

private theorem atMost1Rand_ensureReceiverChain (st : TRState) (pk : DY.Bytes) (tr : ExecTrace) :
    AtMost1Rand tr ((TripleRatchet.ensureReceiverChain st pk).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · rw [Traceful.run_pure]; exact atMost1Rand_refl tr
  · refine atMost1Rand_bind_noRandOp ?_ (fun ⟨st', c'⟩ => NoRandOp.of_id (ini_xfix_pure (st', c', true)))
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    refine XplSteps.xbind_fix (AtMost1Rand tr) (XplSteps.xfix_guard _ tr) (atMost1Rand_refl tr) fun _ => ?_
    refine atMost1Rand_bind_noRandOp ?_ (fun _ => NoRandOp.of_id (ini_xfix_pure _))
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
    exact fun _ hi => at?_eq_none_of_le (tr.append (⟨32⟩ : Random.ExecEntryT))
      (by rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; exact hi)
  · rw [Traceful.run_failure]; exact atMost1Rand_refl tr

private theorem xfix_lookupIdentity (p : Participant) (h : Nat) :
    XplSteps.XFix (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine XplSteps.xfix_bind (ini_xfix_getEntry h) fun e => ?_
  cases e.ev <;> first
    | exact ini_xfix_failure
    | exact XplSteps.xfix_bind (XplSteps.xfix_guard _) fun _ => ini_xfix_pure _

private theorem xfix_bobOpk (b : Participant) (opk : Option Nat) :
    XplSteps.XFix (match opk with
      | some i => do
          let opkSk ← DY.Libsignal.PQXDH.getKey b i .oneTimePrekey
          pure (some opkSk)
      | none => pure none) := by
  cases opk with
  | none => exact ini_xfix_pure none
  | some i => exact XplSteps.xfix_bind (XplSteps.xfix_getKey _ _ _) fun x => ini_xfix_pure (some x)

private theorem xfix_bobHandshake (b a : Participant) (h : DY.Libsignal.PQXDH.BobKeyHandles)
    (r e c : Nat) : XplSteps.XFix (DY.Libsignal.PQXDH.bobHandshake b a h r e c) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine XplSteps.xfix_bind (XplSteps.xfix_getKey b h.ik .identity) fun ikB => ?_
  refine XplSteps.xfix_bind (XplSteps.xfix_getKey b h.spk .signedPrekey) fun spkSk => ?_
  refine XplSteps.xfix_bind (XplSteps.xfix_getKey b h.pqspk .pqPrekey) fun pqsk => ?_
  dsimp only
  cases h.opk with
  | none =>
    refine XplSteps.xfix_bind (ini_xfix_pure none) fun opkSk => ?_
    refine XplSteps.xfix_bind (xfix_lookupIdentity a r) fun ⟨ikA, _⟩ => ?_
    refine XplSteps.xfix_bind (XplSteps.xfix_receiveMessage e) fun ek => ?_
    refine XplSteps.xfix_bind (XplSteps.xfix_receiveMessage c) fun ct => ?_
    refine XplSteps.xfix_bind (XplSteps.xfix_guard _) fun _ => ?_
    cases DY.Libsignal.PQXDH.bobAgreement ikB spkSk pqsk opkSk ikA ek ct with
    | none => exact ini_xfix_failure
    | some _ => exact ini_xfix_pure _
  | some i =>
    refine XplSteps.xfix_bind (XplSteps.xfix_getKey b i .oneTimePrekey) fun lift => ?_
    refine XplSteps.xfix_bind (ini_xfix_pure (some lift)) fun opkSk => ?_
    refine XplSteps.xfix_bind (xfix_lookupIdentity a r) fun ⟨ikA, _⟩ => ?_
    refine XplSteps.xfix_bind (XplSteps.xfix_receiveMessage e) fun ek => ?_
    refine XplSteps.xfix_bind (XplSteps.xfix_receiveMessage c) fun ct => ?_
    refine XplSteps.xfix_bind (XplSteps.xfix_guard _) fun _ => ?_
    cases DY.Libsignal.PQXDH.bobAgreement ikB spkSk pqsk opkSk ikA ek ct with
    | none => exact ini_xfix_failure
    | some _ => exact ini_xfix_pure _

private theorem xfix_receiveSignalMsg (i : Nat) :
    XplSteps.XFix (TripleRatchet.receiveSignalMsg i) := by
  unfold TripleRatchet.receiveSignalMsg
  refine XplSteps.xfix_bind (XplSteps.xfix_receiveMessage i) fun raw => ?_
  cases TripleRatchet.parseTrSignalMsg raw with
  | none => exact ini_xfix_failure
  | some msg => exact XplSteps.xfix_bind (XplSteps.xfix_guard _) fun _ => ini_xfix_pure msg

private theorem xfix_verifyMacAndDecrypt (st : TRState) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (s seed : DY.Bytes) : XplSteps.XFix (TripleRatchet.verifyMacAndDecrypt st msg s seed) := by
  unfold TripleRatchet.verifyMacAndDecrypt
  refine XplSteps.xfix_bind (XplSteps.xfix_guard _) fun _ _ => ?_
  cases DY.SymEnc.symDec (TripleRatchet.trMsgKeys s seed).cipherKey
    (TripleRatchet.trMsgKeys s seed).iv msg.ciphertext <;>
    simp only [liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]

local macro "noRand_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply NoRandOp.bind
  | with_reducible apply NoRandOp.sendMessage | with_reducible apply NoRandOp.storeLocalState
  | with_reducible apply NoRandOp.logSkippedKeys | with_reducible apply NoRandOp.logMessageKeyAndStore
  | with_reducible apply NoRandOp.logEventPQ | with_reducible apply NoRandOp.logEventC
  | with_reducible apply NoRandOp.logEventTR
  | exact NoRandOp.of_id (XplSteps.xfix_getLocalState _ _)
  | exact NoRandOp.of_id (XplSteps.xfix_receiveMessage _)
  | exact NoRandOp.of_id (xfix_receiveSignalMsg _)
  | exact NoRandOp.of_id (xfix_verifyMacAndDecrypt _ _ _ _)
  | exact NoRandOp.of_id (XplSteps.xfix_guard _)
  | exact NoRandOp.of_id (ini_xfix_pure _)
  | exact NoRandOp.of_id ini_xfix_failure
  | exact NoRandOp.of_id ini_xfix_traceLength
  | exact NoRandOp.of_id (ini_xfix_guardTrace _)
  | exact NoRandOp.of_id (ini_xfix_requireTracePredicate _)
  | exact NoRandOp.of_id (ini_xfix_getEntry _)
  | exact NoRandOp.of_id (ini_xfix_monadLift _)
  | split | with_reducible intro))

private theorem atMost1Rand_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pq : Nat) (sp : UInt32)
    (shown : Nat) (tr : ExecTrace) :
    AtMost1Rand tr ((Move.bobStart b a kh regA mh pq sp shown).next tr) := by
  unfold Move.next Move.act
  refine atMost1Rand_bind_noRandOp ?_ (fun _ => NoRandOp.of_id (ini_xfix_pure ()))
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine XplSteps.xbind_fix (AtMost1Rand tr) (xfix_bobHandshake b a kh regA mh.ek mh.ct tr) (atMost1Rand_refl tr) fun o => ?_
  refine XplSteps.xbind_fix (AtMost1Rand tr) (xfix_receiveSignalMsg mh.msg tr) (atMost1Rand_refl tr) fun msg => ?_
  refine atMost1Rand_bind_noRandOp (atMost1Rand_ensureReceiverChain _ _ tr) fun x => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only; noRand_tac

private theorem atMost1Rand_decrypt (me : Participant) (si mi pq : Nat) (sp : UInt32)
    (w : Bool) (tr : ExecTrace) : AtMost1Rand tr ((Move.decrypt me si mi pq sp w).next tr) := by
  unfold Move.next Move.act
  refine atMost1Rand_bind_noRandOp ?_ (fun _ => NoRandOp.of_id (ini_xfix_pure ()))
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine XplSteps.xbind_fix (AtMost1Rand tr) (XplSteps.xfix_getLocalState me si tr) (atMost1Rand_refl tr) fun st => ?_
  refine XplSteps.xbind_fix (AtMost1Rand tr) (xfix_receiveSignalMsg mi tr) (atMost1Rand_refl tr) fun msg => ?_
  refine atMost1Rand_bind_noRandOp (atMost1Rand_ensureReceiverChain _ _ tr) fun x => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only; noRand_tac

private theorem atMost1Rand_decryptSkipped (me : Participant) (si mi k pq : Nat) (sp : UInt32)
    (w : Bool) (tr : ExecTrace) : AtMost1Rand tr ((Move.decryptSkipped me si mi k pq sp w).next tr) := by
  unfold Move.next Move.act
  refine atMost1Rand_bind_noRandOp ?_ (fun _ => NoRandOp.of_id (ini_xfix_pure ()))
  have h : NoRandOp (TripleRatchet.messageDecryptSkipped me si mi k pq sp) := by
    unfold TripleRatchet.messageDecryptSkipped; noRand_tac
  exact atMost1Rand_of_noRand (atMost1Rand_refl tr) (h tr)

private theorem newRandoms_length_le_one {tr t : ExecTrace} (hm : AtMost1Rand tr t) :
    (newRandoms tr t).length ≤ 1 := by
  unfold newRandoms newIndices
  rcases hdiff : t.length - tr.length with _ | k
  · simp
  · rw [List.range'_succ, List.filterMap_cons]
    have hnil : List.filterMap
        (fun i => (t.at? i : Option DY.Random.ExecEntryT).map fun e => (randTerm i e.length, e.length))
        (List.range' (tr.length + 1) k) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro idx hidx
      rw [hm idx (by rw [List.mem_range'] at hidx; obtain ⟨j, _, rfl⟩ := hidx; omega)]
      rfl
    rw [hnil]; cases (t.at? tr.length : Option DY.Random.ExecEntryT) <;> simp

private theorem option_map_toList_length_le_one {α β : Type} (o : Option α) (f : α → β) :
    (o.map f).toList.length ≤ 1 := by cases o <;> simp

theorem vis_length_le_three_of_bob_or_dec (tr : ExecTrace) (m : Move)
    (h : (∃ b a kh r mh pq sp sh, m = .bobStart b a kh r mh pq sp sh) ∨
         (∃ me si mi pq sp w, m = .decrypt me si mi pq sp w) ∨
         (∃ me si mi k pq sp w, m = .decryptSkipped me si mi k pq sp w)) :
    (m.vis tr).length ≤ 3 := by
  have hexp : exposures tr (m.next tr) = [] := by
    rcases h with ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, _, rfl⟩ <;> exact exposures_nil_of_not_leakKind rfl (fun hc => nomatch hc)
  rw [xpl_vis_eq, hexp, List.append_nil]
  rcases h with ⟨b, a, kh, r, mh, pq, sp, sh, rfl⟩ | ⟨me, si, mi, pq, sp, w, rfl⟩ |
    ⟨me, si, mi, k, pq, sp, w, rfl⟩
  · have h1 := newRandoms_length_le_one (atMost1Rand_bobStart b a kh r mh pq sp sh tr)
    have hpt := option_map_toList_length_le_one (receivedPlaintext tr ((Move.bobStart b a kh r mh pq sp sh).next tr))
      fun m => ({ kind := .accept, terms := [m], layout := .single, anchor := eventIdx isBobDone tr ((Move.bobStart b a kh r mh pq sp sh).next tr) } : VisEntry)
    dsimp only [xpl_ownVis, bobVis]; simp only [List.length_take, List.length_cons, List.length_append, List.length_map]; omega
  · have h1 := newRandoms_length_le_one (atMost1Rand_decrypt me si mi pq sp w tr)
    have hr := option_map_toList_length_le_one (tr.getMessageSentAt mi)
      fun b => ({ kind := .recv, terms := [b], layout := if w then .preKeyInner (sessionBaseKeys tr si) else .whisper, anchor := none } : VisEntry)
    have hpt := option_map_toList_length_le_one (receivedPlaintext tr ((Move.decrypt me si mi pq sp w).next tr))
      fun m => ({ kind := .accept, terms := [m], layout := .single, anchor := none } : VisEntry)
    dsimp only [xpl_ownVis, decVis]; simp only [List.length_append, List.length_map]; omega
  · have h1 := newRandoms_length_le_one (atMost1Rand_decryptSkipped me si mi k pq sp w tr)
    have hr := option_map_toList_length_le_one (tr.getMessageSentAt mi)
      fun b => ({ kind := .recv, terms := [b], layout := if w then .preKeyInner (sessionBaseKeys tr si) else .whisper, anchor := none } : VisEntry)
    have hpt := option_map_toList_length_le_one (receivedPlaintext tr ((Move.decryptSkipped me si mi k pq sp w).next tr))
      fun m => ({ kind := .accept, terms := [m], layout := .single, anchor := none } : VisEntry)
    dsimp only [xpl_ownVis, decVis]; simp only [List.length_append, List.length_map]; omega

/-! ## `IniFrame` and `SetupIni` handle pinning -/

private def isIdEv : DY.Libsignal.PQXDH.PQXDHEvent → Bool
  | .IdentityRegistered .. => true
  | _ => false

private def IniFrame (t t' : ExecTrace) : Prop :=
  (∀ i : Nat, (t'.at? i : Option PQStEntry) = (t.at? i : Option PQStEntry)) ∧
  (∀ (i : Nat) (p : Participant) (pk vk : DY.Bytes) (hh : Bool),
    (t'.at? i : Option PQEvEntryP) = some (EvE (.IdentityRegistered p pk vk hh)) →
    (t.at? i : Option PQEvEntryP) = some (EvE (.IdentityRegistered p pk vk hh)))

private theorem IniFrame.refl (t : ExecTrace) : IniFrame t t :=
  ⟨fun _ => rfl, fun _ _ _ _ _ h => h⟩

private theorem IniFrame.trans {t₁ t₂ t₃ : ExecTrace} (h₁ : IniFrame t₁ t₂) (h₂ : IniFrame t₂ t₃) :
    IniFrame t₁ t₃ :=
  ⟨fun i => (h₂.1 i).trans (h₁.1 i), fun i p pk vk hh h => h₁.2 i p pk vk hh (h₂.2 i p pk vk hh h)⟩

private theorem IniFrame.append_non_pq {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (h1 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQStEntry) = none)
    (h2 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQEvEntryP) = none) :
    IniFrame tr (tr.append e) :=
  ⟨fun i => at?_append_non_entry tr e h1 i,
   fun i _ _ _ _ h => by rwa [at?_append_non_entry tr e h2 i] at h⟩

private theorem IniFrame.append_pq (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hne : isIdEv ev = false) : IniFrame tr (tr.append (⟨ev⟩ : PQEvEntryP)) := by
  refine ⟨fun i => at?_append_non_entry tr (⟨ev⟩ : PQEvEntryP) rfl i, fun i p pk vk hh h => ?_⟩
  by_cases hlt : i < tr.length
  · rwa [at?_append_of_lt tr (⟨ev⟩ : PQEvEntryP) hlt] at h
  · by_cases heq : i = tr.length
    · rw [TR.at?_append_eq_of_proj tr (⟨ev⟩ : PQEvEntryP) heq _ rfl] at h
      injection h with h; injection h with h; subst h; cases hne
    · rw [at?_eq_none_of_le (tr.append (⟨ev⟩ : PQEvEntryP))
        (by rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at h
      cases h

private def NoIni {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, IniFrame tr (x.run tr).2.val

private theorem NoIni.of_id {α : Type} {x : Traceful α} (h : ∀ tr, (x.run tr).2.val = tr) :
    NoIni x := fun tr => by rw [h tr]; exact IniFrame.refl tr

private theorem NoIni.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoIni x) (hf : ∀ a, NoIni (f a)) : NoIni (x >>= f) := by
  intro tr; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx tr
  · exact IniFrame.trans (hx tr) (hf a (x.run tr).2.val)

private theorem NoIni.genRand (n : Nat) : NoIni (Random.genRand n : Traceful DY.Bytes) :=
  fun tr => by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
    exact IniFrame.append_non_pq tr (⟨n⟩ : Random.ExecEntryT) rfl rfl
private theorem NoIni.sendMessage (m : DY.Bytes) : NoIni (Network.sendMessage m) :=
  fun tr => by
    rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    exact IniFrame.append_non_pq tr (⟨m⟩ : Network.ExecEntryT) rfl rfl
private theorem NoIni.storeLocalState (p : Participant) (st : TRState) :
    NoIni (PersistentLocalState.storeLocalState p st) :=
  fun tr => by
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    exact IniFrame.append_non_pq tr (⟨⟨p, st⟩⟩ : StEntryP) rfl rfl
private theorem NoIni.logEventPQ (ev : DY.Libsignal.PQXDH.PQXDHEvent) (hne : isIdEv ev = false) :
    NoIni (DY.ProtocolEvent.logEvent ev) := fun tr => by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact IniFrame.append_pq tr ev hne
private theorem NoIni.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    NoIni (DY.ProtocolEvent.logEvent ev) := fun tr => by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact IniFrame.append_non_pq tr (⟨ev⟩ : CEvEntryP) rfl rfl
private theorem NoIni.logEventTR (ev : TREvent) : NoIni (DY.ProtocolEvent.logEvent ev) := fun tr => by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact IniFrame.append_non_pq tr (⟨ev⟩ : TREntryP) rfl rfl

private theorem NoIni.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    NoIni (TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  intro tr; rw [(Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeys_run s pk rIdx src ck n k tr).2]
  induction k generalizing ck n tr with
  | zero => exact IniFrame.refl tr
  | succ k ih =>
    unfold logSkippedKeysTr
    exact IniFrame.trans (IniFrame.append_non_pq tr _ rfl rfl) (ih _ _ _)

private theorem NoIni.logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (r par : Nat) (st : TRState) :
    NoIni (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact NoIni.bind (NoIni.logEventTR _) fun _ => NoIni.storeLocalState _ _

private theorem NoIni.ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    NoIni (TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact NoIni.of_id (ini_xfix_pure _)
  · refine NoIni.bind ?_ (fun ⟨st', c'⟩ => NoIni.of_id (ini_xfix_pure (st', c', true)))
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    exact NoIni.bind (NoIni.of_id (XplSteps.xfix_guard _)) fun _ =>
      NoIni.bind (NoIni.genRand 32) fun _ => NoIni.of_id (ini_xfix_pure _)
  · exact NoIni.of_id ini_xfix_failure

local macro "noIni_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply NoIni.bind
  | with_reducible apply NoIni.genRand | with_reducible apply NoIni.sendMessage
  | with_reducible apply NoIni.storeLocalState | with_reducible apply NoIni.ensureReceiverChain
  | with_reducible apply NoIni.logSkippedKeys | with_reducible apply NoIni.logMessageKeyAndStore
  | with_reducible apply NoIni.logEventPQ _ rfl
  | with_reducible apply NoIni.logEventC | with_reducible apply NoIni.logEventTR
  | exact NoIni.of_id (XplSteps.xfix_getLocalState _ _)
  | exact NoIni.of_id (XplSteps.xfix_receiveMessage _)
  | exact NoIni.of_id (xfix_receiveSignalMsg _)
  | exact NoIni.of_id (xfix_verifyMacAndDecrypt _ _ _ _)
  | exact NoIni.of_id (XplSteps.xfix_guard _)
  | exact NoIni.of_id (ini_xfix_pure _)
  | exact NoIni.of_id ini_xfix_failure
  | exact NoIni.of_id ini_xfix_traceLength
  | exact NoIni.of_id (ini_xfix_guardTrace _)
  | exact NoIni.of_id (ini_xfix_requireTracePredicate _)
  | exact NoIni.of_id (ini_xfix_getEntry _)
  | exact NoIni.of_id (ini_xfix_monadLift _)
  | split | with_reducible intro))

private theorem iniFrame_aliceStartTrOfOut (tr : ExecTrace) (a b : Participant)
    (o : PQXDH.AliceHandshakeOut) :
    IniFrame tr (aliceStartTrOfOut tr a b o) := by
  unfold aliceStartTrOfOut
  refine IniFrame.trans ?_ (IniFrame.append_non_pq _ _ rfl rfl)
  refine IniFrame.trans ?_ (IniFrame.append_non_pq _ _ rfl rfl)
  refine IniFrame.trans ?_ (IniFrame.append_non_pq _ _ rfl rfl)
  refine IniFrame.trans ?_ (IniFrame.append_pq _ _ rfl)
  refine IniFrame.trans ?_ (IniFrame.append_non_pq _ _ rfl rfl)
  refine IniFrame.trans ?_ (IniFrame.append_non_pq _ _ rfl rfl)
  refine IniFrame.trans ?_ (IniFrame.append_non_pq _ _ rfl rfl)
  refine IniFrame.trans ?_ (IniFrame.append_non_pq _ _ rfl rfl)
  exact IniFrame.append_non_pq tr _ rfl rfl

private theorem iniFrame_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pq : Nat) (sp : UInt32)
    (shown : Nat) (tr : ExecTrace) :
    IniFrame tr ((Move.bobStart b a kh regA mh pq sp shown).next tr) := by
  unfold Move.next Move.act
  refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine NoIni.bind (NoIni.of_id (xfix_bobHandshake b a kh regA mh.ek mh.ct)) fun o => ?_
  refine NoIni.bind (NoIni.of_id (xfix_receiveSignalMsg mh.msg)) fun msg => ?_
  refine NoIni.bind (NoIni.ensureReceiverChain _ _) fun x => ?_
  rcases x with ⟨st, c, ratcheted⟩; dsimp only; noIni_tac

private theorem iniFrame_decrypt (me : Participant) (si mi pq : Nat) (sp : UInt32)
    (w : Bool) (tr : ExecTrace) : IniFrame tr ((Move.decrypt me si mi pq sp w).next tr) := by
  unfold Move.next Move.act
  refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine NoIni.bind (NoIni.of_id (XplSteps.xfix_getLocalState me si)) fun st => ?_
  refine NoIni.bind (NoIni.of_id (xfix_receiveSignalMsg mi)) fun msg => ?_
  refine NoIni.bind (NoIni.ensureReceiverChain _ _) fun x => ?_
  rcases x with ⟨st, c, ratcheted⟩; dsimp only; noIni_tac

private theorem iniP_move_frame (tr : ExecTrace) (m : Move) (hm : m.isSetup = false) :
    IniFrame tr (m.next tr) := by
  cases m with
  | setup _ => cases hm
  | reject _ => unfold Move.next Move.act; rw [Traceful.run_pure]; exact IniFrame.refl tr
  | encryptFail me si cl =>
    unfold Move.next Move.act
    refine NoIni.bind (NoIni.of_id ini_xfix_traceLength) (fun n => ?_) tr
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ()))
    unfold TripleRatchet.messageEncrypt; noIni_tac
  | encryptAbort me si =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold TripleRatchet.messageEncryptAbort; noIni_tac
  | aliceStart a b idS regB bh shown =>
    rcases aliceStart_next_cases a b idS regB bh shown tr with h_id | h_rnd |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_ok⟩
    · rw [h_id]; exact IniFrame.refl tr
    · rw [h_rnd]; exact IniFrame.append_non_pq tr _ rfl rfl
    · rw [h_ok]; exact iniFrame_aliceStartTrOfOut tr a b _
  | bobStart b a kh regA mh pq sp shown =>
    exact iniFrame_bobStart b a kh regA mh pq sp shown tr
  | encrypt me si cl pq _ =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold TripleRatchet.messageEncrypt; noIni_tac
  | decrypt me si mi pq sp w =>
    exact iniFrame_decrypt me si mi pq sp w tr
  | decryptSkipped me si mi k pq sp _ =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold TripleRatchet.messageDecryptSkipped; noIni_tac
  | exposeKey me si k =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold TripleRatchet.exposeKey; noIni_tac
  | exposeSpqr me si =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold TripleRatchet.exposeSpqr; noIni_tac
  | exposeSkipped k =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold TripleRatchet.exposeSkipped; noIni_tac
  | compromiseIK p si =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold DY.Libsignal.PQXDH.compromiseIK
    refine NoIni.bind (NoIni.of_id (XplSteps.xfix_getKey p si .identity)) fun _ => ?_; noIni_tac
  | compromiseSPK b si =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold DY.Libsignal.PQXDH.compromiseSPK
    refine NoIni.bind (NoIni.of_id (XplSteps.xfix_getKey b si .signedPrekey)) fun _ => ?_; noIni_tac
  | compromisePQSPK b si =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold DY.Libsignal.PQXDH.compromisePQSPK
    refine NoIni.bind (NoIni.of_id (XplSteps.xfix_getKey b si .pqPrekey)) fun _ => ?_; noIni_tac
  | compromiseOPK b si =>
    unfold Move.next Move.act
    refine NoIni.bind ?_ (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
    unfold DY.Libsignal.PQXDH.compromiseOPK
    refine NoIni.bind (NoIni.of_id (XplSteps.xfix_getKey b si .oneTimePrekey)) fun _ => ?_; noIni_tac
  | attackerSend msg =>
    exact NoIni.bind (NoIni.sendMessage msg) (fun _ => NoIni.of_id (ini_xfix_pure ())) tr
  | brkDH =>
    exact NoIni.logEventPQ .BrokenDH rfl tr
  | brkKEM =>
    exact NoIni.logEventPQ .BrokenKEM rfl tr

private theorem iniP_runMoves_frame (tr : ExecTrace) :
    ∀ (ms : List Move), (∀ m ∈ ms, m.isSetup = false) → IniFrame tr (runMoves ms tr).1
  | [], _ => IniFrame.refl tr
  | m :: ms, hms =>
    IniFrame.trans (iniP_move_frame tr m (hms m (.head _)))
      (iniP_runMoves_frame (m.next tr) ms fun m' hm' => hms m' (.tail _ hm'))

private def SetupIni (a b : Participant) (tr : ExecTrace) : Prop :=
  (∀ i p st, (tr.at? i : Option PQStEntry) = some (StE p st) → (p = a ∧ i = 4) ∨ p = b) ∧
  (∀ i p pk vk hh, (tr.at? i : Option PQEvEntryP) = some (EvE (.IdentityRegistered p pk vk hh)) →
    p = a ∨ (p = b ∧ i = 6))

private theorem SetupIni.nil (a b : Participant) : SetupIni a b DY.Trace.nil :=
  ⟨fun i _ _ h => by simp [Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h,
   fun i _ _ _ _ h => by simp [Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h⟩

private theorem SetupIni.append {E : Type} [ExecTraceTypes.Has E] {a b : Participant}
    {tr : ExecTrace} {e : E} (h : SetupIni a b tr)
    (hst : ∀ p st, (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQStEntry) = some (StE p st) → (p = a ∧ tr.length = 4) ∨ p = b)
    (hev : ∀ p pk vk hh, (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQEvEntryP) = some (EvE (.IdentityRegistered p pk vk hh)) →
      p = a ∨ (p = b ∧ tr.length = 6)) :
    SetupIni a b (tr.append e) := by
  refine ⟨fun i p st hs => ?_, fun i p pk vk hh hr => ?_⟩
  · by_cases hlt : i < tr.length
    · rw [at?_append_of_lt tr e hlt] at hs; exact h.1 i p st hs
    · by_cases heq : i = tr.length
      · rw [TR.at?_append_eq_of_proj tr e heq _ rfl] at hs
        exact (hst p st hs).elim (fun ⟨hp, hl⟩ => Or.inl ⟨hp, heq.trans hl⟩) Or.inr
      · rw [at?_eq_none_of_le (tr.append e)
          (by rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hs
        cases hs
  · by_cases hlt : i < tr.length
    · rw [at?_append_of_lt tr e hlt] at hr; exact h.2 i p pk vk hh hr
    · by_cases heq : i = tr.length
      · rw [TR.at?_append_eq_of_proj tr e heq _ rfl] at hr
        exact (hev p pk vk hh hr).elim Or.inl (fun ⟨hp, hl⟩ => Or.inr ⟨hp, heq.trans hl⟩)
      · rw [at?_eq_none_of_le (tr.append e)
          (by rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hr
        cases hr

local macro "iniP_setup_step" : tactic => `(tactic|
  (repeat (first
     | (with_reducible assumption)
     | refine SetupIni.append ?_
         (fun p st h => by first
           | (cases h; done) | (cases h; exact Or.inr rfl)
           | (cases h; exact Or.inl ⟨rfl, by
               (try unfold TR.setupTr1)
               simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                 Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]⟩))
         (fun p pk vk hh h => by first
           | (cases h; done) | (cases h; exact Or.inl rfl)
           | (cases h; exact Or.inr ⟨rfl, by
               (try unfold TR.setupTr1)
               simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                 Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]⟩))
     | exact SetupIni.nil _ _)))

private theorem iniP_setupIni_tr1 (a b : Participant) : SetupIni a b (TR.setupTr1 a) := by
  simp only [TR.setupTr1]; iniP_setup_step
private theorem iniP_setupIni_tr2 (a b : Participant) : SetupIni a b (TR.setupTr2 a b) := by
  have := iniP_setupIni_tr1 a b; simp only [TR.setupTr2]; iniP_setup_step
private theorem iniP_setupIni_tr3 (a b : Participant) : SetupIni a b (TR.setupTr3 a b) := by
  have := iniP_setupIni_tr2 a b; simp only [TR.setupTr3]; iniP_setup_step
private theorem iniP_setupIni_tr4 (a b : Participant) : SetupIni a b (TR.setupTr4 a b) := by
  have := iniP_setupIni_tr3 a b; simp only [TR.setupTr4]; iniP_setup_step
private theorem iniP_setupIni_tr5 (a b : Participant) : SetupIni a b (TR.setupTr5 a b) := by
  have := iniP_setupIni_tr4 a b; simp only [TR.setupTr5]; iniP_setup_step

private theorem iniP_setupIni (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    SetupIni r.alice r.bob (setupTrace r) := by
  rw [TR.setupTrace_eq r hne]
  cases r.withOpk <;> [exact iniP_setupIni_tr4 _ _; exact iniP_setupIni_tr5 _ _]

section
local notation (priority := high) "PQStEntry" =>
  PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
local notation (priority := high) "PQEvEntryP" =>
  DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent

theorem iniP_alice_st_idx_eq_4 {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move}
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat} {st : DY.Libsignal.PQXDH.PQXDHState}
    (h : ((runTraceMoves r ms).at? i : Option PQStEntry) = some (StE r.alice st)) : i = 4 := by
  change ((runMoves ms (setupTrace r)).1.at? i : Option IniPure.PQStEntry) = some (StE r.alice st) at h
  rw [(iniP_runMoves_frame (setupTrace r) ms hms).1 i] at h
  rcases (iniP_setupIni r hne).1 i r.alice st h with ⟨_, hi⟩ | hab
  · exact hi
  · exact absurd hab hne

theorem iniP_bob_id_idx_eq_6 {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move}
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat} {pk vk : DY.Bytes} {hh : Bool}
    (h : ((runTraceMoves r ms).at? i : Option PQEvEntryP) =
      some (EvE (.IdentityRegistered r.bob pk vk hh))) : i = 6 := by
  change ((runMoves ms (setupTrace r)).1.at? i : Option IniPure.PQEvEntryP) =
    some (EvE (.IdentityRegistered r.bob pk vk hh)) at h
  have h0 := (iniP_runMoves_frame (setupTrace r) ms hms).2 i r.bob pk vk hh h
  rcases (iniP_setupIni r hne).2 i r.bob pk vk hh h0 with hba | ⟨_, hi⟩
  · exact absurd hba.symm hne
  · exact hi

end

theorem ini_getElem?_append_middle {α : Type} (l₁ l₂ l₃ : List α) (x : α) :
    (l₁ ++ (l₂ ++ x :: l₃))[l₁.length + l₂.length]? = some x := by
  rw [← List.append_assoc, ← List.length_append, List.getElem?_append_right (Nat.le_refl _)]; simp

theorem ini_take_append_middle {α : Type} (l₁ l₂ l₃ : List α) (x : α) :
    (l₁ ++ (l₂ ++ x :: l₃)).take (l₁.length + l₂.length) = l₁ ++ l₂ := by
  rw [← List.append_assoc, ← List.length_append, List.take_left]

end Symbolic.Swarm.CREF.CliPure.IniPure
