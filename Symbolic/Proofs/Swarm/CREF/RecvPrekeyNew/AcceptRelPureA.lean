/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.QuietTransferPure
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRpk
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
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
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Block Shape, `TRNsBound`, and Frame Lemmas for Pre-Key Accept

Proves block-shape and quiet-extension helpers for `[.recv b, .rng d, .accept pt]`, `TRNsBound`
preservation across `bobStart` (`rpkA2_nsBound`), and `PureCRecRel` frame preservation for
participants other than Bob (`rpkA2_frame`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure.RpkCli
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)

/-! ## Block shape and `TRNsBound` preservation -/

theorem rpkA2_blockShape (b d pt : HwBytes) :
    RpkBlockShape [MachineEvent.recv b, .rng d, .accept pt] where
  head := ⟨b, rfl⟩
  tail := by
    intro e he
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  len := by simp

theorem rpkA2_blockHead (b d pt : HwBytes) :
    ∀ e ∈ ([MachineEvent.recv b, .rng d, .accept pt] : List MachineEvent).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
  intro e he
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
  subst he; exact Or.inl rfl

theorem rpkA2_blockAccept (b d pt : HwBytes) :
    ∃ e ∈ ([MachineEvent.recv b, .rng d, .accept pt] : List MachineEvent),
      eventKind e = .accept :=
  ⟨.accept pt, by simp, rfl⟩

theorem rpkA2_sentBodies (acc : List MachineEvent) (b d pt : HwBytes) :
    TR.sentBodies (acc ++ [MachineEvent.recv b, .rng d, .accept pt]) = TR.sentBodies acc := by
  simp [TR.sentBodies]

theorem rpk_callStarts_map_rng :
    ∀ (ds : List HwBytes), callStarts (ds.map MachineEvent.rng) = []
  | [] => rfl
  | _ :: ds => rpk_callStarts_map_rng ds

theorem b2_quietPost {r : ProtocolSetup} {ms₀ pre post : List Move} {m : Move}
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m])) (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) := by
  rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
    TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
  exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)

theorem b2_quietPre {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
section NsBound

open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir setRecvChain TRState TREvent
  TRSignalMsg ensureReceiverChain dhRatchetStep logSkippedKeys logMessageKeyAndStore traceLength)
open DY.Libsignal.PQXDH (BobKeyHandles PreKeyMsgHandles bobHandshake)

def b2NsInv (n : Nat) (tr : ExecTrace) : Prop :=
  ∀ (p : Participant) (stateIdx : Nat) (st : TRState),
    ((DY.PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st →
    st.ns.toNat ≤ n

theorem b2NsInv_iff (n : Nat) (tr : ExecTrace) :
    b2NsInv n tr ↔ ∀ (i : Nat) (e : CompTrace.TRStEntry),
      (tr.at? i : Option CompTrace.TRStEntry) = some e → e.st.state.ns.toNat ≤ n := by
  constructor
  · intro h i ⟨⟨p, st⟩⟩ he
    refine h p i st ?_
    rw [CompTrace.getLocalState_tr_fst, he]; simp
  · intro h p i st hget
    rw [CompTrace.getLocalState_tr_fst] at hget
    rcases he : (tr.at? i : Option CompTrace.TRStEntry) with _ | ⟨⟨q, st'⟩⟩
    · rw [he] at hget; cases hget
    · rw [he] at hget; dsimp only at hget; split_ifs at hget; cases hget; exact h i _ he

theorem b2NsInv_append {E : Type} [DY.ExecTraceTypes.Has E] {n : Nat} {tr : ExecTrace} {x : E}
    (hx : ∀ e : CompTrace.TRStEntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TRStEntry) = some e → e.st.state.ns.toNat ≤ n)
    (h : b2NsInv n tr) : b2NsInv n (tr.append x) := by
  rw [b2NsInv_iff] at h ⊢
  intro i e he
  rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
  · exact h i e he'
  · exact hx e hp

theorem b2NsInv_append_other {E : Type} [DY.ExecTraceTypes.Has E] {n : Nat} {tr : ExecTrace} {x : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = none)
    (h : b2NsInv n tr) : b2NsInv n (tr.append x) :=
  b2NsInv_append (fun _ hp => by rw [hnone] at hp; cases hp) h

theorem b2NsInv_quiet {n : Nat} {tr tr' : ExecTrace} (h : XplQuiet.QuietExt tr tr')
    (hI : b2NsInv n tr) : b2NsInv n tr' := by
  intro p i st hget; rw [XplQuiet.quiet_getLocalState h] at hget; exact hI p i st hget

theorem b2_store {n : Nat} (p : Participant) (st : TRState) (hst : st.ns.toNat ≤ n) :
    CompTrace.Preserves (b2NsInv n) (DY.PersistentLocalState.storeLocalState p st) := by
  intro _ h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact b2NsInv_append (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; exact hst) h

def b2BobEv (b : Participant) : TREvent → Prop
  | .SkippedKeyUsed _ _ => False
  | .MessageKey s _ _ _ _ _ _ => s.me = b
  | .SkippedKeyStored s _ _ _ _ _ => s.me = b
  | _ => True

structure b2BobFx (Inv : ExecTrace → Prop) (b : Participant) : Prop where
  send : ∀ m : DY.Bytes, CompTrace.Preserves Inv (DY.Network.sendMessage m)
  rand : ∀ k : Nat, CompTrace.Preserves Inv (DY.Random.genRand k)
  pq : ∀ ev : DY.Libsignal.PQXDH.PQXDHEvent, CompTrace.Preserves Inv (DY.ProtocolEvent.logEvent ev)
  c : ∀ ev : DY.Libsignal.Composed.ComposedEvent, CompTrace.Preserves Inv (DY.ProtocolEvent.logEvent ev)
  tr : ∀ ev : TREvent, b2BobEv b ev → CompTrace.Preserves Inv (DY.ProtocolEvent.logEvent ev)
  store : ∀ st : TRState, st.ns = 0 →
    CompTrace.Preserves Inv (DY.PersistentLocalState.storeLocalState b st)

theorem b2_logSkippedKeys {Inv : ExecTrace → Prop} {b : Participant} (fx : b2BobFx Inv b)
    (s : SessionInfo) (hs : s.me = b) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (idx : UInt32) (k : Nat),
      CompTrace.Preserves Inv (logSkippedKeys s pk rIdx src ck idx k)
  | _, _, 0 => CompTrace.Preserves.pure ()
  | ck, idx, k + 1 => by
    unfold logSkippedKeys
    exact CompTrace.Preserves.bind (fx.tr _ (by exact hs)) fun _ =>
      b2_logSkippedKeys fx s hs pk rIdx src _ _ k

theorem b2_logMKStore {Inv : ExecTrace → Prop} {b : Participant} (fx : b2BobFx Inv b)
    (s : SessionInfo) (hs : s.me = b) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (k : UInt32) (rIdx par : Nat) (st : TRState) (hst : st.ns = 0) :
    CompTrace.Preserves Inv (logMessageKeyAndStore b s dir seed pqSalt k rIdx par st) := by
  unfold logMessageKeyAndStore
  exact CompTrace.Preserves.bind (fx.tr _ (by exact hs)) fun _ => fx.store st hst

theorem b2_bobHandshake {Inv : ExecTrace → Prop} (b a : Participant) (kh : BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) :
    CompTrace.Preserves Inv (bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  intro tr h
  have hb := CompTrace.bind_bobHandshake_at (Inv := Inv) b a kh regIdxA ekIdx ctIdx
    (f := Pure.pure) tr h (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      simp only [DY.Traceful.run_pure]; exact h)
  have hp : ((bobHandshake b a kh regIdxA ekIdx ctIdx >>= Pure.pure).run tr).2.val =
      ((bobHandshake b a kh regIdxA ekIdx ctIdx).run tr).2.val := by
    rw [Traceful.run_bind]
    rcases (bobHandshake b a kh regIdxA ekIdx ctIdx).run tr with ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
  rwa [hp] at hb

def b2PP (Inv : ExecTrace → Prop) {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

theorem b2PP.pure {Inv : ExecTrace → Prop} {α : Type} {Q : α → Prop} {a : α} (h : Q a) :
    b2PP Inv Q (Pure.pure a : Traceful α) := by
  intro _ hI
  simp only [DY.Traceful.run_pure]
  exact ⟨hI, fun _ ha => Option.some.inj ha ▸ h⟩

theorem b2PP.failure {Inv : ExecTrace → Prop} {α : Type} {Q : α → Prop} :
    b2PP Inv Q (failure : Traceful α) := by
  intro _ hI
  simp only [DY.Traceful.run_failure]
  exact ⟨hI, fun _ ha => by cases ha⟩

theorem b2PP.ofPres {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (h : CompTrace.Preserves Inv x) : b2PP Inv (fun _ => True) x :=
  fun tr hI => ⟨h tr hI, fun _ _ => trivial⟩

theorem b2PP.bind {Inv : ExecTrace → Prop} {α β : Type} {R : α → Prop} {Q : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : b2PP Inv R x) (hf : ∀ a, R a → b2PP Inv Q (f a)) : b2PP Inv Q (x >>= f) := by
  intro tr hI
  obtain ⟨h1, h2⟩ := hx tr hI
  rw [CompTrace.run_bind_snd, CompTrace.run_bind_fst]
  rcases hr : (x.run tr).1 with _ | a
  · exact ⟨h1, fun _ ha => by cases ha⟩
  · exact hf a (h2 a hr) _ h1

theorem b2PP.bindPres {Inv : ExecTrace → Prop} {α β : Type} {R : α → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : b2PP Inv R x) (hf : ∀ a, R a → CompTrace.Preserves Inv (f a)) :
    CompTrace.Preserves Inv (x >>= f) :=
  fun tr hI => ((b2PP.bind hx fun a ha => b2PP.ofPres (hf a ha)) tr hI).1

theorem b2_dhRatchetStep {Inv : ExecTrace → Prop} {b : Participant} (fx : b2BobFx Inv b)
    (st : TRState) (pk : DY.Bytes) :
    b2PP Inv (fun p : TRState × RecvChain => p.1.ns = 0) (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact b2PP.bind (b2PP.ofPres (CompTrace.Preserves.guardP _)) fun _ _ =>
    b2PP.bind (b2PP.ofPres (fx.rand 32)) fun _ _ => b2PP.pure rfl

theorem b2_ensureReceiverChain {Inv : ExecTrace → Prop} {b : Participant} (fx : b2BobFx Inv b)
    (st₀ : TRState) (pk : DY.Bytes) (hns : st₀.ns = 0) :
    b2PP Inv (fun p : TRState × RecvChain × Bool => p.1.ns = 0) (ensureReceiverChain st₀ pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact b2PP.pure hns
  · exact b2PP.bind (b2_dhRatchetStep fx st₀ pk) fun ⟨_, _⟩ hp => b2PP.pure hp
  · exact b2PP.failure

theorem b2_bobStart_storeTail {Inv : ExecTrace → Prop} {b : Participant} (fx : b2BobFx Inv b)
    (st : TRState) (msg : TRSignalMsg) (c c' : RecvChain) (seed pqSalt spqr' m : DY.Bytes)
    (hst : st.ns = 0) :
    CompTrace.Preserves Inv (do
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← traceLength) + skipped + 2
      logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
  CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ =>
    CompTrace.Preserves.bind (b2_logSkippedKeys fx (st.sessionInfo b) rfl _ _ _ _ _ _) fun _ =>
    CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
    b2_logMKStore fx (st.sessionInfo b) rfl _ _ _ _ _ _ _ hst

theorem b2_bobStart {Inv : ExecTrace → Prop} {b : Participant} (fx : b2BobFx Inv b)
    (a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves Inv
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.Preserves.bind (b2_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o =>
    CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg mh.msg) fun msg =>
    b2PP.bindPres (b2_ensureReceiverChain fx _ msg.ratchetKey (by rfl)) fun r hr => ?_
  rcases r with ⟨st, c, ratcheted⟩
  dsimp only at hr ⊢
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine CompTrace.Preserves.bind (fx.send key) fun _ =>
        CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun pqSalt =>
        CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt st msg pqSalt seed)
          fun m => ?_
      have htail := b2_bobStart_storeTail fx st msg c c' seed pqSalt spqr' m hr
      cases o.opk <;> dsimp only
      · refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ =>
          CompTrace.Preserves.bind (fx.pq _) fun _ => ?_
        split
        · exact CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
            CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
            CompTrace.Preserves.bind (fx.c _) fun _ => htail
        · exact CompTrace.Preserves.bind (fx.c _) fun _ => htail
      · refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ =>
          CompTrace.Preserves.bind (fx.pq _) fun _ =>
          CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ =>
          CompTrace.Preserves.bind (fx.pq _) fun _ => ?_
        split
        · exact CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
            CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
            CompTrace.Preserves.bind (fx.c _) fun _ => htail
        · exact CompTrace.Preserves.bind (fx.c _) fun _ => htail
    · exact CompTrace.Preserves.failure
  · exact CompTrace.Preserves.failure

theorem b2_next_bobStart {Inv : ExecTrace → Prop} {p : Participant} (fx : b2BobFx Inv p)
    {tr : ExecTrace} {m : Move} (hbs : BobStartBy p m) (h : Inv tr) : Inv (m.next tr) := by
  cases m with
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    obtain rfl : b = p := hbs
    rw [b5_bobStart_next]; exact b2_bobStart fx a kh regIdxA mh pqIdx spqrMsgIdx tr h
  | _ => exact False.elim hbs

theorem b2NsFx (n : Nat) (b : Participant) : b2BobFx (b2NsInv n) b where
  send _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact b2NsInv_append_other rfl h
  rand _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2NsInv_append_other rfl h
  pq _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2NsInv_append_other rfl h
  c _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2NsInv_append_other rfl h
  tr _ _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2NsInv_append_other rfl h
  store st hst := b2_store b st (by simp [hst])

theorem b2NsInv_next_bobStart {n : Nat} {tr : ExecTrace} {p : Participant} {m : Move}
    (hbs : BobStartBy p m) (h : b2NsInv n tr) : b2NsInv n (m.next tr) :=
  b2_next_bobStart (b2NsFx n p) hbs h

end NsBound

theorem rpkA2_nsBound {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {acc : List MachineEvent} {b d pt : HwBytes} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {sent : List HwBytes}
    (_hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hbs : BobStartBy r.bob m) (hns : TR.TRNsBound r ms₀ sent) :
    TR.TRNsBound r (ms₀ ++ (pre ++ m :: post)) sent := by
  have hq1 := XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hq2 := XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)
  have h0 : b2NsInv sent.length (runTraceMoves r ms₀) := hns
  have h3 := b2NsInv_quiet hq2 (b2NsInv_next_bobStart hbs (b2NsInv_quiet hq1 h0))
  show b2NsInv sent.length (runTraceMoves r (ms₀ ++ (pre ++ m :: post)))
  rw [TR.runTrace_append, TR.runMoves_append]; exact h3

/-! ## Frame preservation for other participants -/

section Frame

open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir TRState TREvent)

def b2Frame (b : Participant) (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ i, tr₀.length ≤ i →
    (∀ e : CompTrace.TRStEntry, (tr.at? i : Option CompTrace.TRStEntry) = some e →
      e.st.participant = b) ∧
    (∀ e : CompTrace.TREntry, (tr.at? i : Option CompTrace.TREntry) = some e → b2BobEv b e.ev)

theorem b2Frame_refl (b : Participant) (tr : ExecTrace) : b2Frame b tr tr := by
  refine ⟨Trace.le_refl tr, fun _ hi => ⟨fun _ he => ?_, fun _ he => ?_⟩⟩ <;>
    (rw [XplQuiet.at?_none_of_ge hi] at he; cases he)

theorem b2Frame_append {E : Type} [DY.ExecTraceTypes.Has E] {b : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (hst : ∀ e : CompTrace.TRStEntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TRStEntry) = some e → e.st.participant = b)
    (hev : ∀ e : CompTrace.TREntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TREntry) = some e → b2BobEv b e.ev)
    (h : b2Frame b tr₀ tr) : b2Frame b tr₀ (tr.append x) := by
  refine ⟨Trace.le_trans _ _ _ h.1 (Trace.append_le tr x), fun i hi => ⟨fun e he => ?_, fun e he => ?_⟩⟩
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).1 e he'
    · exact hst e hp
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).2 e he'
    · exact hev e hp

theorem b2Frame_append_other {E : Type} [DY.ExecTraceTypes.Has E] {b : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (h1 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = none)
    (h2 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TREntry) = none)
    (h : b2Frame b tr₀ tr) : b2Frame b tr₀ (tr.append x) :=
  b2Frame_append (fun _ hp => by rw [h1] at hp; cases hp)
    (fun _ hp => by rw [h2] at hp; cases hp) h

theorem b2FrameFx (b : Participant) (tr₀ : ExecTrace) : b2BobFx (b2Frame b tr₀) b where
  send _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact b2Frame_append_other rfl rfl h
  rand _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2Frame_append_other rfl rfl h
  pq _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2Frame_append_other rfl rfl h
  c _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2Frame_append_other rfl rfl h
  tr _ hev := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact b2Frame_append (fun _ hp => by cases hp)
      (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; exact hev) h
  store _ _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact b2Frame_append
      (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; rfl) (fun _ hp => by cases hp) h

theorem b2_at?_lt {EntryT : Type} [DY.TraceEntryHas EntryT ExecTrace.Entry] {tr₀ tr : ExecTrace}
    (hle : tr₀ ≤ tr) {j : Nat} (hj : j < tr₀.length) :
    (tr.at? j : Option EntryT) = tr₀.at? j := by
  have hj' : j < tr.length := Nat.lt_of_lt_of_le hj (Trace.length_le tr₀ tr hle)
  simp only [Trace.at?, hj, hj', dite_true, Trace.at_le tr₀ tr j hj hle]

theorem b2Frame_getLocalState {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {p : Participant} {i : Nat} {st : TRState}
    (hget : ((DY.PersistentLocalState.getLocalState p i : Traceful TRState).run tr₀).1 = some st) :
    ((DY.PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st := by
  rw [CompTrace.getLocalState_tr_fst] at hget ⊢
  rcases he : (tr₀.at? i : Option CompTrace.TRStEntry) with _ | e
  · rw [he] at hget; cases hget
  · rw [he] at hget; rw [CompTrace.at?_le_some h.1 he]; exact hget

theorem b2Frame_isCurrentSnapshot {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {p : Participant} (hp : p ≠ b) {i : Nat} {st : TRState}
    (hget : ((DY.PersistentLocalState.getLocalState p i : Traceful TRState).run tr₀).1 = some st)
    (hcur : TripleRatchet.isCurrentSnapshot tr₀ i = true) :
    TripleRatchet.isCurrentSnapshot tr i = true := by
  rw [CompTrace.getLocalState_tr_fst] at hget
  rcases he : (tr₀.at? i : Option CompTrace.TRStEntry) with _ | ⟨⟨q, st'⟩⟩
  · rw [he] at hget; cases hget
  rw [he] at hget
  have hq : q = p := by dsimp only at hget; split_ifs at hget with hq; exact hq
  have hlt : i < tr₀.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.TRStEntry) tr₀ i
    rw [he] at this; exact this
  have hlen := Trace.length_le tr₀ tr h.1
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [CompTrace.at?_le_some h.1 he]; rw [he] at hcur; dsimp only at hcur ⊢
  rw [show tr.length - (i + 1) = (tr₀.length - (i + 1)) + (tr.length - tr₀.length) by omega,
    ← List.range'_append_1, List.all_append, Bool.and_eq_true]
  simp only [show i + 1 + (tr₀.length - (i + 1)) = tr₀.length by omega]
  refine ⟨Eq.trans (XplQuiet.q_all_congr_mem fun j hj => ?_) hcur, ?_⟩
  · rw [List.mem_range'_1] at hj; rw [b2_at?_lt h.1 (by omega : j < tr₀.length)]
  · rw [List.all_eq_true]; intro j hj; rw [List.mem_range'_1] at hj; try dsimp only
    rcases hj' : (tr.at? j : Option CompTrace.TRStEntry) with _ | e'
    · rfl
    · have hb := (h.2 j (by omega)).1 e' hj'
      simp only [hb, Bool.or_eq_true, bne_iff_ne, ne_eq]
      exact Or.inl fun h' => hp (h'.trans hq).symm

theorem b2Frame_eventLoggedAt {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {ev : TREvent} {i : Nat} (hl : tr₀.EventLoggedAt ev i) : tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hl ⊢
  exact CompTrace.at?_le_some h.1 hl

theorem b2Frame_someEventOnTraceB {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    (P : TREvent → Bool) (hP : ∀ ev, b2BobEv b ev → P ev = false)
    (h0 : (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr₀ P = false) :
    (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr P = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h0 ⊢
  rw [List.any_eq_false] at h0 ⊢
  intro j hj hfj; rw [List.mem_range] at hj; try dsimp only at hfj
  by_cases hlt : j < tr₀.length
  · rw [b2_at?_lt h.1 hlt] at hfj; exact h0 j (List.mem_range.mpr hlt) hfj
  · rcases he : (tr.at? j : Option CompTrace.TREntry) with _ | e
    · rw [he] at hfj; dsimp only at hfj; cases hfj
    · rw [he] at hfj; dsimp only at hfj; rw [hP e.ev ((h.2 j (by omega)).2 e he)] at hfj; cases hfj

theorem b2Frame_skippedKeyUsedB {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {k : Nat} (hsu : (!TripleRatchet.skippedKeyUsedB tr₀ k) = true) :
    (!TripleRatchet.skippedKeyUsedB tr k) = true := by
  have h0 : TripleRatchet.skippedKeyUsedB tr₀ k = false := by simpa using hsu
  have h1 : TripleRatchet.skippedKeyUsedB tr k = false :=
    b2Frame_someEventOnTraceB h _ (fun ev hev => by cases ev <;> first | rfl | exact False.elim hev) h0
  simp [h1]

theorem b2Frame_receiverKeyUsedB {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {p : Participant} (hp : p ≠ b) {st : TRState} {seed : DY.Bytes} {n : UInt32} {rIdx : Nat}
    (hru : (!TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo p) seed n rIdx) = true) :
    (!TripleRatchet.receiverKeyUsedB tr (st.sessionInfo p) seed n rIdx) = true := by
  have h0 : TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo p) seed n rIdx = false := by simpa using hru
  have h1 : TripleRatchet.receiverKeyUsedB tr (st.sessionInfo p) seed n rIdx = false := by
    refine b2Frame_someEventOnTraceB h _ (fun ev hev => ?_) h0
    cases ev
    case MessageKey s' dir _ _ _ _ _ =>
      cases dir
      · rfl
      · exact decide_eq_false fun hc => hp ((congrArg SessionInfo.me hc.1).symm.trans hev)
    all_goals rfl
  simp [h1]

theorem b2Frame_getMessageSentAt {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {i : Nat} {x : DY.Bytes} (hi : tr₀.getMessageSentAt i = some x) :
    tr.getMessageSentAt i = some x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hi ⊢
  have hlt : i < tr₀.length := by
    by_contra hge
    rw [XplQuiet.at?_none_of_ge (EntryT := DY.Network.ExecEntryT) (by omega : tr₀.length ≤ i)] at hi
    cases hi
  rw [b2_at?_lt (EntryT := DY.Network.ExecEntryT) h.1 hlt]; exact hi

theorem b2Frame_trRecordStateInv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {Z : TR.PureTRSlots} {g : Ghost} {ms ms' : List Move} {records : Participant → Option HwBytes}
    {b : Participant} (h : b2Frame b (runTraceMoves r ms) (runTraceMoves r ms'))
    (hrec : ∀ q bs, records q = some bs → q ≠ b)
    (hrsi : TR.PureTRRecordStateInv interpretation r S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r S Z g ms' records := by
  intro q bs hqb
  have hqb' := hrec q bs hqb
  obtain ⟨hq_mem, rec, st, stateIdx, hb, hget, hcur, hrel, hsk, hcanon, hks, hnd⟩ := hrsi q bs hqb
  refine ⟨hq_mem, rec, st, stateIdx, hb, b2Frame_getLocalState h hget,
    b2Frame_isCurrentSnapshot h hqb' hget hcur, hrel, ?_, hcanon, hks, hnd⟩
  intro c hc k hk
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam, hsrk, hfind⟩ := hsk c hc k hk
  exact ⟨pk, rIdx, srcIdx, skIdx, seed, b2Frame_eventLoggedAt h hlog,
    b2Frame_skippedKeyUsedB h hsu, b2Frame_receiverKeyUsedB h hqb' hru, hgam, hsrk, hfind⟩

theorem b2Frame_aliceInitPending {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {bs : HwBytes}
    (h : b2Frame r.bob (runTraceMoves r ms) (runTraceMoves r ms')) (hab : r.alice ≠ r.bob)
    (hp : PureAliceInitPending interpretation r S g ms bs) :
    PureAliceInitPending interpretation r S g ms' bs := by
  obtain ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, hget, hcur, h6, h7, hek, hct, rest⟩ := hp
  exact ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, b2Frame_getLocalState h hget, b2Frame_isCurrentSnapshot h hab hget hcur, h6, h7,
    b2Frame_getMessageSentAt h hek, b2Frame_getMessageSentAt h hct, rest⟩

theorem b2Frame_cRecRel {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {p : Participant} {bs : HwBytes}
    (h : b2Frame r.bob (runTraceMoves r ms) (runTraceMoves r ms')) (hp : p ≠ r.bob)
    (hc : PureCRecRel interpretation r S g ms p bs) : PureCRecRel interpretation r S g ms' p bs := by
  rcases hc with hc | ⟨hpa, hc⟩
  · refine Or.inl (b2Frame_trRecordStateInv h (fun q bs' hq => ?_) hc)
    by_cases hqp : q = p
    · subst hqp; exact hp
    · simp [hqp] at hq
  · exact Or.inr ⟨hpa, b2Frame_aliceInitPending h (fun h' => hp (hpa.trans h')) hc⟩

end Frame

theorem rpkA2_frame {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {acc : List MachineEvent} {b d pt : HwBytes} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {p : Participant} {bs : HwBytes}
    (_hwf : ProtocolSetupWF r)
    (_hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hbs : BobStartBy r.bob m) (hp : p ≠ r.bob)
    (hc : PureCRecRel interpretation r S g ms₀ p bs) :
    PureCRecRel interpretation r S g (ms₀ ++ (pre ++ m :: post)) p bs := by
  have c1 := XplQuiet.quiet_pureCRecRel (b2_quietPre hpre) hc
  have hf : b2Frame r.bob (runTraceMoves r (ms₀ ++ pre)) (runTraceMoves r (ms₀ ++ pre ++ [m])) := by
    rw [TR.runTrace_snoc]
    exact b2_next_bobStart (b2FrameFx r.bob _) hbs (b2Frame_refl r.bob _)
  exact XplQuiet.quiet_pureCRecRel (b2_quietPost hpost) (b2Frame_cRecRel hf hp c1)

end Symbolic.Swarm.CREF.CliPure
