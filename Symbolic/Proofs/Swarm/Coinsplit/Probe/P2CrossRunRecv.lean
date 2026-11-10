/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
import all DY.Bytes.Basic
import all DY.ALaCarte.Basic
import all DY.ALaCarte.Ordering
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.BaseAttackerKnowledge
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.Xpl.Steps

/-!
# Accepted `recv` Coin-Cut Dichotomy

Characterizes the random draws of `decrypt` and `decryptSkipped` moves and proves that on a
32-byte `.rng` call block `[.recv w, .rng coins, .accept pt]` under 32-byte `.single` `.rng`
length faithfulness, an accepted `recv` cut equals either `[.recv w, .accept pt]` or
`[.recv w, .rng coins, .accept pt]`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.Coinsplit.P2

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful)
open _root_.DY.DiffieHellman _root_.DY.SymEnc _root_.DY.Concat
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.TR.RecvDec
  (run_bind_snd run_bind_pure_val at?_eq_none_of_le at?_append_non_entry
   logSkippedKeysTr logSkippedKeys_run)

private abbrev StEntryP :=
  _root_.DY.PersistentGlobalState.State.ExecEntryT (_root_.DY.PersistentLocalState.LocalState TRState)
private abbrev TREntryP := _root_.DY.ProtocolEvent.ExecEntryT TREvent
private abbrev PQEvEntryP := _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent
private abbrev CEvEntryP := _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.Composed.ComposedEvent

private def NoRand (t t' : ExecTrace) : Prop :=
  ∀ i : Nat, (t'.at? i : Option _root_.DY.Random.ExecEntryT) =
    (t.at? i : Option _root_.DY.Random.ExecEntryT)

private def NoRandOp {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, NoRand tr (x.run tr).2.val

private theorem NoRandOp.of_id {α : Type} {x : Traceful α} (h : ∀ tr, (x.run tr).2.val = tr) :
    NoRandOp x := fun tr _ => by rw [h tr]

private theorem NoRandOp.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoRandOp x) (hf : ∀ a, NoRandOp (f a)) : NoRandOp (x >>= f) := by
  intro tr i
  rw [run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx tr i
  · exact (hf a (x.run tr).2.val i).trans (hx tr i)

private theorem NoRandOp.sendMessage (m : _root_.DY.Bytes) :
    NoRandOp (_root_.DY.Network.sendMessage m) :=
  fun tr i => at?_append_non_entry tr (⟨m⟩ : _root_.DY.Network.ExecEntryT) rfl i

private theorem NoRandOp.storeLocalState (p : Participant) (st : TRState) :
    NoRandOp (_root_.DY.PersistentLocalState.storeLocalState p st) :=
  fun tr i => at?_append_non_entry tr (⟨⟨p, st⟩⟩ : StEntryP) rfl i

private theorem NoRandOp.logEventPQ (ev : _root_.DY.Libsignal.PQXDH.PQXDHEvent) :
    NoRandOp (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun tr i => at?_append_non_entry tr (⟨ev⟩ : PQEvEntryP) rfl i

private theorem NoRandOp.logEventC (ev : _root_.DY.Libsignal.Composed.ComposedEvent) :
    NoRandOp (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun tr i => at?_append_non_entry tr (⟨ev⟩ : CEvEntryP) rfl i

private theorem NoRandOp.logEventTR (ev : TREvent) :
    NoRandOp (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun tr i => at?_append_non_entry tr (⟨ev⟩ : TREntryP) rfl i

private theorem NoRandOp.logSkippedKeys (s : SessionInfo) (pk : _root_.DY.Bytes)
    (rIdx src : Nat) (ck : _root_.DY.Bytes) (n : UInt32) (k : Nat) :
    NoRandOp (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  intro tr i
  rw [(logSkippedKeys_run s pk rIdx src ck n k tr).2]
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold logSkippedKeysTr
    exact (ih _ _ _).trans (at?_append_non_entry tr _ rfl i)

private theorem NoRandOp.logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : _root_.DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : _root_.DY.Bytes)
    (n : UInt32) (r par : Nat) (st : TRState) :
    NoRandOp (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      me s dir seed pqSalt n r par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact NoRandOp.bind (NoRandOp.logEventTR _) fun _ => NoRandOp.storeLocalState _ _

private theorem xfix_receiveMessage (idx : Nat) :
    XplSteps.XFix (_root_.DY.Network.receiveMessage idx) := by
  unfold _root_.DY.Network.receiveMessage
  exact XplSteps.xfix_bind (XplSteps.xfix_getEntry idx)
    (fun (e : _root_.DY.Network.ExecEntryT) => XplSteps.xfix_pure e.msg)

private theorem xfix_lookupIdentity (p : Participant) (h : Nat) :
    XplSteps.XFix (_root_.DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold _root_.DY.Libsignal.PQXDH.lookupIdentity
  refine XplSteps.xfix_bind (fun _ => rfl) fun e => ?_
  cases e.ev <;> first
    | exact fun _ => rfl
    | exact XplSteps.xfix_bind (XplSteps.xfix_guard _) fun _ _ => rfl

private theorem xfix_bobOpk (b : Participant) (opk : Option Nat) :
    XplSteps.XFix (match opk with
      | some i => do
          let opkSk ← _root_.DY.Libsignal.PQXDH.getKey b i .oneTimePrekey
          pure (some opkSk)
      | none => pure none) := by
  cases opk with
  | none => exact fun _ => rfl
  | some i => exact XplSteps.xfix_bind (XplSteps.xfix_getKey _ _ _) fun _ _ => rfl

local macro "p2_xfix_step" : tactic => `(tactic|
  first
  | apply XplSteps.xfix_bind (XplSteps.xfix_getKey _ _ _) _ ; intro _
  | apply XplSteps.xfix_bind (xfix_bobOpk _ _) _ ; intro _
  | apply XplSteps.xfix_bind (xfix_lookupIdentity _ _) _ ; intro _
  | apply XplSteps.xfix_bind (xfix_receiveMessage _) _ ; intro _
  | apply XplSteps.xfix_bind (XplSteps.xfix_guard _) _ ; intro _
  | apply XplSteps.xfix_bind (fun _ => rfl) _ ; intro _
  | exact fun _ => rfl
  | (split <;> try exact fun _ => rfl))

private theorem xfix_bobHandshake (b a : Participant)
    (kh : _root_.DY.Libsignal.PQXDH.BobKeyHandles) (rIdx eIdx cIdx : Nat) :
    XplSteps.XFix (_root_.DY.Libsignal.PQXDH.bobHandshake b a kh rIdx eIdx cIdx) := by
  unfold _root_.DY.Libsignal.PQXDH.bobHandshake
  repeat' p2_xfix_step

private theorem xfix_receiveSignalMsg (i : Nat) :
    XplSteps.XFix (_root_.DY.Libsignal.TripleRatchet.receiveSignalMsg i) := by
  unfold _root_.DY.Libsignal.TripleRatchet.receiveSignalMsg
  repeat' p2_xfix_step

private theorem xfix_verifyMacAndDecrypt (st : TRState)
    (msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg) (s seed : _root_.DY.Bytes) :
    XplSteps.XFix (_root_.DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg s seed) := by
  unfold _root_.DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  repeat' p2_xfix_step

private def AtMost1Rand32 (tr t : ExecTrace) : Prop :=
  ((t.at? tr.length : Option _root_.DY.Random.ExecEntryT) = none ∨
    (t.at? tr.length : Option _root_.DY.Random.ExecEntryT) = some ⟨32⟩) ∧
  ∀ i : Nat, tr.length + 1 ≤ i → (t.at? i : Option _root_.DY.Random.ExecEntryT) = none

private theorem atMost1Rand32_refl (tr : ExecTrace) : AtMost1Rand32 tr tr :=
  ⟨Or.inl (at?_eq_none_of_le tr (Nat.le_refl _)), fun _ hi => at?_eq_none_of_le tr (by omega)⟩

private theorem atMost1Rand32_of_noRand {tr t t' : ExecTrace}
    (h1 : AtMost1Rand32 tr t) (h2 : NoRand t t') : AtMost1Rand32 tr t' :=
  ⟨by rw [h2 tr.length]; exact h1.1, fun i hi => (h2 i).trans (h1.2 i hi)⟩

private theorem atMost1Rand32_bind_noRandOp {α β : Type} {tr : ExecTrace}
    {x : Traceful α} {f : α → Traceful β}
    (hx : AtMost1Rand32 tr (x.run tr).2.val) (hf : ∀ a, NoRandOp (f a)) :
    AtMost1Rand32 tr ((x >>= f).run tr).2.val := by
  rw [run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx
  · exact atMost1Rand32_of_noRand hx (hf a _)

private theorem at?_append_rnd_length (tr : ExecTrace) (n : Nat) :
    ((tr.append (⟨n⟩ : _root_.DY.Random.ExecEntryT)).at? tr.length :
      Option _root_.DY.Random.ExecEntryT) = some ⟨n⟩ :=
  Trace.at?_append tr (⟨n⟩ : _root_.DY.Random.ExecEntryT)

private theorem atMost1Rand32_ensureReceiverChain (st : TRState) (pk : _root_.DY.Bytes)
    (tr : ExecTrace) :
    AtMost1Rand32 tr ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact atMost1Rand32_refl tr
  · refine atMost1Rand32_bind_noRandOp ?_ (fun _ => NoRandOp.of_id fun _ => rfl)
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    refine XplSteps.xbind_fix (AtMost1Rand32 tr) (XplSteps.xfix_guard _ tr) (atMost1Rand32_refl tr)
      fun _ => ?_
    refine atMost1Rand32_bind_noRandOp ?_ (fun _ => NoRandOp.of_id fun _ => rfl)
    exact ⟨Or.inr (at?_append_rnd_length tr 32),
      fun _ hi => at?_eq_none_of_le (tr.append (⟨32⟩ : _root_.DY.Random.ExecEntryT)) hi⟩
  · exact atMost1Rand32_refl tr

private theorem newRandoms_of_noRand {tr t : ExecTrace} (h : NoRand tr t) :
    newRandoms tr t = [] := by
  unfold newRandoms newIndices
  rw [List.filterMap_eq_nil_iff]
  intro i hi
  rw [List.mem_range'_1] at hi
  rw [h i, at?_eq_none_of_le tr hi.1]
  rfl

private theorem newRandoms_of_atMost1Rand32 {tr t : ExecTrace} (h : AtMost1Rand32 tr t) :
    newRandoms tr t = [] ∨ newRandoms tr t = [(randTerm tr.length 32, 32)] := by
  unfold newRandoms newIndices
  rcases hdiff : t.length - tr.length with _ | k
  · exact Or.inl rfl
  · rw [List.range'_succ, List.filterMap_cons]
    have hnil : List.filterMap
        (fun i => (t.at? i : Option _root_.DY.Random.ExecEntryT).map
          fun e => (randTerm i e.length, e.length))
        (List.range' (tr.length + 1) k) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro idx hidx
      rw [List.mem_range'_1] at hidx
      rw [h.2 idx hidx.1]
      rfl
    rw [hnil]
    rcases h.1 with h0 | h32
    · rw [h0]; exact Or.inl rfl
    · rw [h32]; exact Or.inr rfl

local macro "p2_noRand_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply NoRandOp.bind
  | with_reducible apply NoRandOp.sendMessage
  | with_reducible apply NoRandOp.storeLocalState
  | with_reducible apply NoRandOp.logSkippedKeys
  | with_reducible apply NoRandOp.logMessageKeyAndStore
  | with_reducible apply NoRandOp.logEventPQ
  | with_reducible apply NoRandOp.logEventC
  | with_reducible apply NoRandOp.logEventTR
  | exact NoRandOp.of_id (XplSteps.xfix_getLocalState _ _)
  | exact NoRandOp.of_id (XplSteps.xfix_getEntry _)
  | exact NoRandOp.of_id (xfix_receiveMessage _)
  | exact NoRandOp.of_id (xfix_receiveSignalMsg _)
  | exact NoRandOp.of_id (xfix_verifyMacAndDecrypt _ _ _ _)
  | exact NoRandOp.of_id (XplSteps.xfix_guard _)
  | exact NoRandOp.of_id fun _ => rfl
  | split
  | with_reducible intro))

private theorem noRand_decryptSkipped (me : Participant) (sIdx mIdx skIdx pqIdx : Nat)
    (spIdx : UInt32) (w : Bool) (tr : ExecTrace) :
    NoRand tr ((Move.decryptSkipped me sIdx mIdx skIdx pqIdx spIdx w).next tr) := by
  have hop : NoRandOp (Move.decryptSkipped me sIdx mIdx skIdx pqIdx spIdx w).act := by
    unfold Move.act _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
    p2_noRand_tac
  exact hop tr

private theorem atMost1Rand32_decrypt (me : Participant) (sIdx mIdx pqIdx : Nat)
    (spIdx : UInt32) (w : Bool) (tr : ExecTrace) :
    AtMost1Rand32 tr ((Move.decrypt me sIdx mIdx pqIdx spIdx w).next tr) := by
  unfold Move.next Move.act
  refine atMost1Rand32_bind_noRandOp ?_ (fun _ => NoRandOp.of_id fun _ => rfl)
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine XplSteps.xbind_fix (AtMost1Rand32 tr) (XplSteps.xfix_getLocalState me sIdx tr)
    (atMost1Rand32_refl tr) fun st => ?_
  refine XplSteps.xbind_fix (AtMost1Rand32 tr) (xfix_receiveSignalMsg mIdx tr)
    (atMost1Rand32_refl tr) fun msg => ?_
  refine atMost1Rand32_bind_noRandOp (atMost1Rand32_ensureReceiverChain _ _ tr) fun x => ?_
  rcases x with ⟨st', c, ratcheted⟩
  dsimp only
  p2_noRand_tac

private def Exact1Rand32 (tr t : ExecTrace) : Prop :=
  (t.at? tr.length : Option _root_.DY.Random.ExecEntryT) = some ⟨32⟩ ∧
    ∀ i : Nat, tr.length + 1 ≤ i → (t.at? i : Option _root_.DY.Random.ExecEntryT) = none

private theorem exact1Rand32_of_noRand {tr t t' : ExecTrace}
    (h1 : Exact1Rand32 tr t) (h2 : NoRand t t') : Exact1Rand32 tr t' :=
  ⟨by rw [h2 tr.length]; exact h1.1, fun i hi => (h2 i).trans (h1.2 i hi)⟩

private theorem exact1Rand32_bind_noRandOp {α β : Type} {tr : ExecTrace}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Exact1Rand32 tr (x.run tr).2.val) (hf : ∀ a, NoRandOp (f a)) :
    Exact1Rand32 tr ((x >>= f).run tr).2.val := by
  rw [run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx
  · exact exact1Rand32_of_noRand hx (hf a _)

private theorem newRandoms_of_exact1Rand32 {tr t : ExecTrace} (h : Exact1Rand32 tr t) :
    newRandoms tr t = [(randTerm tr.length 32, 32)] := by
  unfold newRandoms newIndices
  rcases hdiff : t.length - tr.length with _ | k
  · exfalso
    have hnone : (t.at? tr.length : Option _root_.DY.Random.ExecEntryT) = none :=
      at?_eq_none_of_le t (by omega)
    rw [h.1] at hnone
    cases hnone
  · rw [List.range'_succ, List.filterMap_cons]
    have hnil : List.filterMap
        (fun i => (t.at? i : Option _root_.DY.Random.ExecEntryT).map
          fun e => (randTerm i e.length, e.length))
        (List.range' (tr.length + 1) k) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro idx hidx
      rw [List.mem_range'_1] at hidx
      rw [h.2 idx hidx.1]
      rfl
    rw [hnil, h.1]
    rfl

private theorem ensureReceiverChain_empty_bind_lowOrder {α : Type} {st : TRState}
    {pk : _root_.DY.Bytes}
    {f : TRState × _root_.DY.Libsignal.TripleRatchet.RecvChain × Bool → Traceful α}
    (hrecv : st.recv = [])
    (hlow : _root_.DY.X25519.x25519LowOrder pk = true) (tr : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk >>= f).run tr).2.val = tr := by
  have h1 : ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk).run tr).1 = none := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold _root_.DY.Libsignal.TripleRatchet.recvChainFor
      _root_.DY.Libsignal.TripleRatchet.findRecvChain
    simp only [hrecv, List.find?_nil, hlow, ↓reduceIte]
    rfl
  have h2 : ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk).run tr).2.val = tr := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold _root_.DY.Libsignal.TripleRatchet.recvChainFor
      _root_.DY.Libsignal.TripleRatchet.findRecvChain
    simp only [hrecv, List.find?_nil, hlow, ↓reduceIte]
    rfl
  rw [run_bind_snd, h1, h2]

private theorem ensureReceiverChain_empty_exact1Rand32 {st : TRState} {pk : _root_.DY.Bytes}
    (hrecv : st.recv = [])
    (hlow : _root_.DY.X25519.x25519LowOrder pk = false) (tr : ExecTrace) :
    Exact1Rand32 tr ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold _root_.DY.Libsignal.TripleRatchet.recvChainFor
    _root_.DY.Libsignal.TripleRatchet.findRecvChain
  simp only [hrecv, List.find?_nil, hlow, Bool.false_eq_true, ↓reduceIte]
  refine exact1Rand32_bind_noRandOp ?_ (fun _ => NoRandOp.of_id fun _ => rfl)
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  simp only [hlow, Bool.not_false, _root_.guard, ↓reduceIte]
  rw [run_bind_snd]
  refine exact1Rand32_bind_noRandOp ?_ (fun _ => NoRandOp.of_id fun _ => rfl)
  exact ⟨at?_append_rnd_length tr 32,
    fun _ hi => at?_eq_none_of_le (tr.append (⟨32⟩ : _root_.DY.Random.ExecEntryT)) hi⟩

private theorem bobStart_next_eq_or_exact1Rand32 (b a : Participant)
    (kh : _root_.DY.Libsignal.PQXDH.BobKeyHandles) (regA : Nat)
    (mh : _root_.DY.Libsignal.PQXDH.PreKeyMsgHandles) (pq : Nat) (sp : UInt32)
    (sh : Nat) (tr : ExecTrace) :
    (Move.bobStart b a kh regA mh pq sp sh).next tr = tr ∨
      Exact1Rand32 tr ((Move.bobStart b a kh regA mh pq sp sh).next tr) := by
  unfold Move.next Move.act
  dsimp only
  rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_pure_val]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
  refine XplSteps.xbind_fix (fun t => t = tr ∨ Exact1Rand32 tr t)
    (xfix_bobHandshake b a kh regA mh.ek mh.ct tr) (Or.inl rfl) fun o => ?_
  refine XplSteps.xbind_fix (fun t => t = tr ∨ Exact1Rand32 tr t)
    (xfix_receiveSignalMsg mh.msg tr) (Or.inl rfl) fun msg => ?_
  dsimp only
  by_cases hlow : _root_.DY.X25519.x25519LowOrder msg.ratchetKey = true
  · left
    refine ensureReceiverChain_empty_bind_lowOrder ?_ hlow tr
    rfl
  · right
    have hlow_f : _root_.DY.X25519.x25519LowOrder msg.ratchetKey = false :=
      Bool.eq_false_iff.mpr hlow
    refine exact1Rand32_bind_noRandOp (ensureReceiverChain_empty_exact1Rand32 ?_ hlow_f tr) fun x => ?_
    · rfl
    · rcases x with ⟨st', c, ratcheted⟩
      dsimp only
      p2_noRand_tac

unseal _root_.DY.Bytes in
private instance subRandomP2 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    _root_.DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @_root_.DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩

private theorem gamma_randTerm32 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts : Nat) :
    gamma interpretation S g (randTerm ts 32) = g.σ ts 32 := by
  unfold gamma gamma' randTerm
  rw [_root_.DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  rfl

private theorem coinSplit_recv_rng_accept_inv {w coins pt : HwBytes}
    {blk_hw : List MachineEvent}
    (hcs : CoinSplit [.recv w, .rng coins, .accept pt] blk_hw) :
    ∃ pieces : List HwBytes,
      (∀ p ∈ pieces, p ≠ []) ∧
      pieces.flatten <+: coins ∧
      blk_hw = .recv w :: (pieces.map MachineEvent.rng ++ [.accept pt]) := by
  cases hcs with
  | keep _ hcs1 =>
    cases hcs1 with
    | keep hne _ => exact False.elim (hne coins rfl)
    | split hne_p hpref hcs2 =>
      cases hcs2 with
      | keep _ hcs3 =>
        cases hcs3 with
        | nil => exact ⟨_, hne_p, hpref, rfl⟩

private theorem prefix_eq_of_length_eq {α : Type} {p coins : List α}
    (hp : p <+: coins) (hlen : p.length = coins.length) : p = coins := by
  rcases hp with ⟨rest, rfl⟩
  have hlen' : p.length = p.length + rest.length := by simpa [List.length_append] using hlen
  have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hr
  exact (List.append_nil p).symm

private theorem receivedPlaintext_self_none (tr : ExecTrace) :
    receivedPlaintext tr tr = none := by
  simp [receivedPlaintext, newIndices]

private theorem match_3_elem_rng32 {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {w coins pt : HwBytes} {pieces : List HwBytes}
    {v_recv v_acc : VisEntry}
    (hcoins : coins.length = 32)
    (hσ : (g.σ ts 32).length = 32)
    (hpref : pieces.flatten <+: coins)
    (hmatch : List.Forall₂ (EventMatchesEntry interp r S g)
      (.recv w :: (pieces.map MachineEvent.rng ++ [.accept pt]))
      [v_recv, rngEntry (randTerm ts 32), v_acc]) :
    pieces = [coins] := by
  rcases pieces with _ | ⟨p, _ | ⟨p2, rest⟩⟩
  · have hlen := hmatch.length_eq
    simp at hlen
  · cases hmatch with
    | cons _ htail =>
      cases htail with
      | cons hm_rng _ =>
        have hp_eq : p = g.σ ts 32 := by
          have hs := hm_rng.2
          dsimp only [rngEntry, eventBytes, List.map] at hs
          rw [gamma_randTerm32] at hs
          injection hs with hs'
          exact hs'.symm
        have hp_pref : p <+: coins := by
          simpa using hpref
        rw [prefix_eq_of_length_eq hp_pref (by rw [hp_eq, hσ, hcoins])]
  · have hlen := hmatch.length_eq
    simp at hlen

private theorem match_2_elem_no_rng {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {w pt : HwBytes} {pieces : List HwBytes}
    {v_recv v_acc : VisEntry}
    (hmatch : List.Forall₂ (EventMatchesEntry interp r S g)
      (.recv w :: (pieces.map MachineEvent.rng ++ [.accept pt]))
      [v_recv, v_acc]) :
    pieces = [] := by
  cases hmatch with
  | cons _ htail =>
    rcases pieces with _ | ⟨p, _ | ⟨p2, rest⟩⟩
    · rfl
    · cases htail with
      | cons _ htail2 => cases htail2
    · cases htail with
      | cons _ htail2 => cases htail2

private theorem forall2_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hhd _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self .., hhd⟩
    · obtain ⟨y, hy, hry⟩ := ih hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

private theorem accepted_recv_blk_dichotomy_core {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {m : Move} {w coins pt : HwBytes}
    {blk_hw : List MachineEvent}
    (hcoins : coins.length = 32)
    (hσ : rngEntry (randTerm tr.length 32) ∈ m.vis tr → (g.σ tr.length 32).length = 32)
    (hread : Symbolic.Swarm.CREF.isReadMove m = true)
    (_hanc : m.LogsSessionCompletion tr)
    (hexp : exposures tr (m.next tr) = [])
    (hcs : CoinSplit [.recv w, .rng coins, .accept pt] blk_hw)
    (hmatch : List.Forall₂ (EventMatchesEntry interp r S g) blk_hw (m.vis tr)) :
    (blk_hw = [.recv w, .accept pt] ∨ blk_hw = [.recv w, .rng coins, .accept pt]) ∧
      ((∃ b a kh regA mh pq sp sh, m = .bobStart b a kh regA mh pq sp sh) →
        blk_hw = [.recv w, .rng coins, .accept pt]) := by
  obtain ⟨pieces, _, hpref, rfl⟩ := coinSplit_recv_rng_accept_inv hcs
  have hacc_mem : ∃ v ∈ m.vis tr, v.kind = .accept := by
    have hmem : MachineEvent.accept pt ∈
        (MachineEvent.recv w :: (pieces.map MachineEvent.rng ++ [MachineEvent.accept pt])) := by
      simp
    obtain ⟨v, hv, hrv⟩ := forall2_mem_left hmatch hmem
    exact ⟨v, hv, hrv.1.symm⟩
  cases m <;> simp only [Symbolic.Swarm.CREF.isReadMove, Bool.false_eq_true] at hread
  case bobStart b a kh regA mh pq sp sh =>
    have hvis_eq : (Move.bobStart b a kh regA mh pq sp sh).vis tr =
        (bobVis tr ((Move.bobStart b a kh regA mh pq sp sh).next tr) mh
          (bobOpkPk b kh tr)).take sh := by
      unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
    rw [hvis_eq] at hmatch hacc_mem
    have hpt_some : ∃ ptTerm, receivedPlaintext tr
        ((Move.bobStart b a kh regA mh pq sp sh).next tr) = some ptTerm := by
      rcases hpt : receivedPlaintext tr
          ((Move.bobStart b a kh regA mh pq sp sh).next tr) with _ | ptTerm
      · exfalso
        obtain ⟨v, hv, hvk⟩ := hacc_mem
        have hv' := List.mem_of_mem_take hv
        unfold bobVis at hv'
        rw [hpt] at hv'
        simp only [Option.map_none, Option.toList_none, List.append_nil, List.mem_cons,
          List.mem_map] at hv'
        rcases hv' with rfl | ⟨_, _, rfl⟩ <;> cases hvk
      · exact ⟨ptTerm, rfl⟩
    obtain ⟨ptTerm, hpt⟩ := hpt_some
    have hne_tr : (Move.bobStart b a kh regA mh pq sp sh).next tr ≠ tr := by
      intro heq
      rw [heq, receivedPlaintext_self_none] at hpt
      cases hpt
    have hnr : newRandoms tr ((Move.bobStart b a kh regA mh pq sp sh).next tr) =
        [(randTerm tr.length 32, 32)] := by
      rcases bobStart_next_eq_or_exact1Rand32 b a kh regA mh pq sp sh tr with heq | hex1
      · exact absurd heq hne_tr
      · exact newRandoms_of_exact1Rand32 hex1
    have hbvis : bobVis tr ((Move.bobStart b a kh regA mh pq sp sh).next tr) mh
        (bobOpkPk b kh tr) =
        [⟨.recv, received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList, .preKeyRecv, none⟩,
         rngEntry (randTerm tr.length 32),
         ⟨.accept, [ptTerm], .single,
           eventIdx isBobDone tr ((Move.bobStart b a kh regA mh pq sp sh).next tr)⟩] := by
      unfold bobVis
      rw [hnr, hpt]
      rfl
    rw [hbvis] at hmatch hacc_mem
    have hsh3 : 3 ≤ sh := by
      obtain ⟨v, hv, hvk⟩ := hacc_mem
      rcases sh with _ | _ | _ | sh'
      · simp at hv
      · simp at hv; subst hv; cases hvk
      · simp at hv; rcases hv with rfl | rfl <;> cases hvk
      · omega
    have htake3 : [⟨.recv, received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList,
          .preKeyRecv, none⟩,
        rngEntry (randTerm tr.length 32),
        ⟨.accept, [ptTerm], .single,
          eventIdx isBobDone tr ((Move.bobStart b a kh regA mh pq sp sh).next tr)⟩].take sh =
        [⟨.recv, received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList,
          .preKeyRecv, none⟩,
        rngEntry (randTerm tr.length 32),
        ⟨.accept, [ptTerm], .single,
          eventIdx isBobDone tr ((Move.bobStart b a kh regA mh pq sp sh).next tr)⟩] :=
      List.take_of_length_le hsh3
    rw [htake3] at hmatch
    have hσ32 : (g.σ tr.length 32).length = 32 :=
      hσ (by rw [hvis_eq, hbvis, htake3]; simp)
    have hp_eq := match_3_elem_rng32 hcoins hσ32 hpref hmatch
    subst hp_eq
    exact ⟨Or.inr rfl, fun _ => rfl⟩
  case decrypt me sIdx mIdx pqIdx spIdx wr =>
    have hvis_eq : (Move.decrypt me sIdx mIdx pqIdx spIdx wr).vis tr =
        decVis tr ((Move.decrypt me sIdx mIdx pqIdx spIdx wr).next tr) sIdx mIdx wr := by
      unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
    rw [hvis_eq] at hmatch hacc_mem
    have hpt_some : ∃ ptTerm, receivedPlaintext tr
        ((Move.decrypt me sIdx mIdx pqIdx spIdx wr).next tr) = some ptTerm := by
      rcases hpt : receivedPlaintext tr
          ((Move.decrypt me sIdx mIdx pqIdx spIdx wr).next tr) with _ | ptTerm
      · exfalso
        obtain ⟨v, hv, hvk⟩ := hacc_mem
        unfold decVis at hv
        rw [hpt] at hv
        simp only [Option.map_none, Option.toList_none, List.append_nil, List.mem_append,
          List.mem_map] at hv
        rcases hv with hv | ⟨_, _, rfl⟩
        · cases hmsg : tr.getMessageSentAt mIdx <;> simp [hmsg] at hv
          subst hv; cases hvk
        · cases hvk
      · exact ⟨ptTerm, rfl⟩
    obtain ⟨ptTerm, hpt⟩ := hpt_some
    have hmsg_some : ∃ msgTerm, tr.getMessageSentAt mIdx = some msgTerm := by
      rcases hmsg : tr.getMessageSentAt mIdx with _ | msgTerm
      · exfalso
        unfold decVis at hmatch
        rw [hmsg, hpt] at hmatch
        simp only [Option.map_none, Option.toList_none, List.nil_append, Option.map_some,
          Option.toList_some] at hmatch
        rcases hnr : newRandoms tr ((Move.decrypt me sIdx mIdx pqIdx spIdx wr).next tr) with
          _ | ⟨r0, rs⟩
        · rw [hnr] at hmatch
          cases hmatch with
          | cons hhd _ => cases hhd.1
        · rw [hnr] at hmatch
          cases hmatch with
          | cons hhd _ => cases hhd.1
      · exact ⟨msgTerm, rfl⟩
    obtain ⟨msgTerm, hmsg⟩ := hmsg_some
    rcases newRandoms_of_atMost1Rand32 (atMost1Rand32_decrypt me sIdx mIdx pqIdx spIdx wr tr) with
      hnr0 | hnr32
    · have hdvis : decVis tr ((Move.decrypt me sIdx mIdx pqIdx spIdx wr).next tr) sIdx mIdx wr =
          [⟨.recv, [msgTerm], if wr then .preKeyInner (sessionBaseKeys tr sIdx) else .whisper,
            none⟩,
           ⟨.accept, [ptTerm], .single, none⟩] := by
        unfold decVis; rw [hmsg, hnr0, hpt]; rfl
      rw [hdvis] at hmatch
      have hp_eq := match_2_elem_no_rng hmatch
      subst hp_eq
      exact ⟨Or.inl rfl, by rintro ⟨_, _, _, _, _, _, _, _, h⟩; cases h⟩
    · have hdvis : decVis tr ((Move.decrypt me sIdx mIdx pqIdx spIdx wr).next tr) sIdx mIdx wr =
          [⟨.recv, [msgTerm], if wr then .preKeyInner (sessionBaseKeys tr sIdx) else .whisper,
            none⟩,
           rngEntry (randTerm tr.length 32),
           ⟨.accept, [ptTerm], .single, none⟩] := by
        unfold decVis; rw [hmsg, hnr32, hpt]; rfl
      rw [hdvis] at hmatch
      have hσ32 : (g.σ tr.length 32).length = 32 :=
        hσ (by rw [hvis_eq, hdvis]; simp)
      have hp_eq := match_3_elem_rng32 hcoins hσ32 hpref hmatch
      subst hp_eq
      exact ⟨Or.inr rfl, by rintro ⟨_, _, _, _, _, _, _, _, h⟩; cases h⟩
  case decryptSkipped me sIdx mIdx skIdx pqIdx spIdx wr =>
    have hvis_eq : (Move.decryptSkipped me sIdx mIdx skIdx pqIdx spIdx wr).vis tr =
        decVis tr ((Move.decryptSkipped me sIdx mIdx skIdx pqIdx spIdx wr).next tr) sIdx mIdx wr := by
      unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
    rw [hvis_eq] at hmatch hacc_mem
    have hnr0 := newRandoms_of_noRand (noRand_decryptSkipped me sIdx mIdx skIdx pqIdx spIdx wr tr)
    have hpt_some : ∃ ptTerm, receivedPlaintext tr
        ((Move.decryptSkipped me sIdx mIdx skIdx pqIdx spIdx wr).next tr) = some ptTerm := by
      rcases hpt : receivedPlaintext tr
          ((Move.decryptSkipped me sIdx mIdx skIdx pqIdx spIdx wr).next tr) with _ | ptTerm
      · exfalso
        obtain ⟨v, hv, hvk⟩ := hacc_mem
        unfold decVis at hv
        rw [hpt, hnr0] at hv
        simp only [Option.map_none, Option.toList_none, List.map_nil, List.append_nil] at hv
        cases hmsg : tr.getMessageSentAt mIdx <;> simp [hmsg] at hv
        subst hv; cases hvk
      · exact ⟨ptTerm, rfl⟩
    obtain ⟨ptTerm, hpt⟩ := hpt_some
    have hmsg_some : ∃ msgTerm, tr.getMessageSentAt mIdx = some msgTerm := by
      rcases hmsg : tr.getMessageSentAt mIdx with _ | msgTerm
      · exfalso
        unfold decVis at hmatch
        rw [hmsg, hnr0, hpt] at hmatch
        cases hmatch with
        | cons hhd _ => cases hhd.1
      · exact ⟨msgTerm, rfl⟩
    obtain ⟨msgTerm, hmsg⟩ := hmsg_some
    have hdvis : decVis tr ((Move.decryptSkipped me sIdx mIdx skIdx pqIdx spIdx wr).next tr)
        sIdx mIdx wr =
        [⟨.recv, [msgTerm], if wr then .preKeyInner (sessionBaseKeys tr sIdx) else .whisper,
          none⟩,
         ⟨.accept, [ptTerm], .single, none⟩] := by
      unfold decVis; rw [hmsg, hnr0, hpt]; rfl
    rw [hdvis] at hmatch
    have hp_eq := match_2_elem_no_rng hmatch
    subst hp_eq
    exact ⟨Or.inl rfl, by rintro ⟨_, _, _, _, _, _, _, _, h⟩; cases h⟩

unseal _root_.DY.Bytes in
private theorem x25519LowOrder_dhPk_randTerm0 :
    _root_.DY.X25519.x25519LowOrder
      (dhPk (randTerm 0 32)) = false := by
  rfl

unseal _root_.DY.Bytes in
private theorem spqrRecv_randTerm0 :
    _root_.DY.Spqr.spqrRecv (randTerm 0 32) (randTerm 0 32) 0 =
      some (({ st := randTerm 0 32, msg := randTerm 0 32 } :
          _root_.DY.Spqr.RecvState.SubF _root_.DY.Bytes).pack,
        ({ st := randTerm 0 32, msg := randTerm 0 32 } :
          _root_.DY.Spqr.RecvKey.SubF _root_.DY.Bytes).pack) := by
  rfl

/-- Accepted-`recv` cut dichotomy under move-level `.single` `.rng` length faithfulness. -/
theorem accepted_recv_blk_dichotomy_of_rngLengths {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {m : Move} {w coins pt : HwBytes}
    {blk_hw : List MachineEvent}
    (hcoins : coins.length = 32)
    (hrng : ∀ (v : VisEntry) (t : _root_.DY.Bytes),
      v ∈ m.vis tr → v.kind = .rng → v.layout = .single → v.terms = [t] →
      (gamma interp S g t).length = 32)
    (hread : Symbolic.Swarm.CREF.isReadMove m = true)
    (hanc : m.LogsSessionCompletion tr)
    (hexp : exposures tr (m.next tr) = [])
    (hcs : CoinSplit [.recv w, .rng coins, .accept pt] blk_hw)
    (hmatch : List.Forall₂ (EventMatchesEntry interp r S g) blk_hw (m.vis tr)) :
    (blk_hw = [.recv w, .accept pt] ∨ blk_hw = [.recv w, .rng coins, .accept pt]) ∧
      ((∃ b a kh regA mh pq sp sh, m = .bobStart b a kh regA mh pq sp sh) →
        blk_hw = [.recv w, .rng coins, .accept pt]) := by
  refine accepted_recv_blk_dichotomy_core hcoins (fun hmem => ?_) hread hanc hexp hcs hmatch
  have h := hrng (rngEntry (randTerm tr.length 32)) (randTerm tr.length 32) hmem rfl rfl rfl
  rwa [gamma_randTerm32] at h

end Symbolic.Swarm.Coinsplit.P2
