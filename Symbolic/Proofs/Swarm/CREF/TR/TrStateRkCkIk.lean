/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Specifications.Refinement.TraceExplanation
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
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
# Identity-Key Provenance and 32-Byte Key Lengths on Stored States

Defines `TrStateRkCkIk` and proves `trStateRkCkIk_of_getLocalState`: on any `ModelRun r₀ ms`, every
stored `TRState` has `myIk` and `peerIk` equal to one of the two setup identity public keys and has
32-byte concretized root and receiver-chain keys.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.Libsignal
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
  (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain
   recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk createChain x25519LowOrder messageVersion)
open CryptoProofLib.Refinement (ExternInterpretation)

namespace RecvDecStep

/-! ## Key-Length and Identity-Key Trace Predicates -/

local notation "IkStEntry" =>
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
local notation "IkPQStEntry" =>
  PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
local notation "IkPQEvEntry" => DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent

private theorem proj_inj_ik {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

def IsKey32 (u : DY.Bytes) : Prop :=
  ∀ (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost),
    (gamma interpretation S g u).length = 32

private theorem isKey32_pqxdhKdf_rk (ikm : DY.Bytes) :
    IsKey32 (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk := by
  intro interpretation S g
  rw [(gamma_pqxdhKdf interpretation S g ikm).1]
  exact CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _

private theorem isKey32_pqxdhKdf_ck (ikm : DY.Bytes) :
    IsKey32 (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck := by
  intro interpretation S g
  rw [(gamma_pqxdhKdf interpretation S g ikm).2.1]
  exact CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _

private theorem isKey32_createChain_fst (rk pk sk : DY.Bytes) :
    IsKey32 (createChain rk pk sk).1 := by
  intro interpretation S g
  have hcc : (createChain rk pk sk).1 =
      DY.Libsignal.TripleRatchet.hkdfBlock1
        (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree pk sk))
        (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
  rw [hcc, gamma_hkdfBlock1]
  exact CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _

private theorem isKey32_createChain_snd (rk pk sk : DY.Bytes) :
    IsKey32 (createChain rk pk sk).2 := by
  intro interpretation S g
  have hcc : (createChain rk pk sk).2 =
      DY.Libsignal.TripleRatchet.hkdfBlock2
        (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree pk sk))
        (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
  rw [hcc, gamma_hkdfBlock2]
  exact CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _

private theorem isKey32_kdfCk_fst (ck : DY.Bytes) :
    IsKey32 (kdfCk ck).1 := by
  intro interpretation S g
  rw [gamma_kdfCk_fst]
  exact CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _

def IkPkIsInit (pk : DY.Bytes) : Prop :=
  pk = dhPk (randTerm 0 32) ∨ pk = dhPk (randTerm 5 32)

def TrStateIkInit (st : TRState) : Prop :=
  (st.myIk = DY.Libsignal.PQXDH.serializedIk (dhPk (randTerm 0 32)) ∨
   st.myIk = DY.Libsignal.PQXDH.serializedIk (dhPk (randTerm 5 32))) ∧
  (st.peerIk = DY.Libsignal.PQXDH.serializedIk (dhPk (randTerm 0 32)) ∨
   st.peerIk = DY.Libsignal.PQXDH.serializedIk (dhPk (randTerm 5 32))) ∧
  IsKey32 st.rk ∧
  (∀ c ∈ st.recv, IsKey32 c.chainKey)

def PQStateIkInit (st : DY.Libsignal.PQXDH.PQXDHState) : Prop :=
  st.kind = .identity → IkPkIsInit (dhPk st.sk)

def PQEventIkInit (ev : DY.Libsignal.PQXDH.PQXDHEvent) : Prop :=
  ∀ (p : Participant) (ikPk vkPk : DY.Bytes) (honest : Bool),
    ev = .IdentityRegistered p ikPk vkPk honest → IkPkIsInit ikPk

def IkInitEntryOk (ent : ExecTrace.Entry) : Prop :=
  (∀ e : IkStEntry, TraceEntryHas.proj ent = some e → TrStateIkInit e.st.state) ∧
  (∀ e : IkPQStEntry, TraceEntryHas.proj ent = some e → PQStateIkInit e.st.state) ∧
  (∀ e : IkPQEvEntry, TraceEntryHas.proj ent = some e → PQEventIkInit e.ev)

def TraceIkInit (tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), IkInitEntryOk (tr.at j hj)

theorem traceIkInit_nil : TraceIkInit (DY.Trace.nil : ExecTrace) :=
  fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj

theorem traceIkInit_append {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hent : IkInitEntryOk (TraceEntryHas.inj e)) (htr : TraceIkInit tr) :
    TraceIkInit (tr.append e) := by
  have hle : tr ≤ tr.append e := DY.Trace.append_le tr e
  intro j hj
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt hle]
    exact htr j hlt
  · have heq : j = tr.length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj
      omega
    subst heq
    simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

/-! ## `TracefulIkInit` Combinators -/

def TracefulIkInit {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, TraceIkInit tr →
    TraceIkInit (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

theorem TracefulIkInit.pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    TracefulIkInit Q (Pure.pure a) := by
  unfold TracefulIkInit
  intro tr htr
  simp only [Traceful.run_pure]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb
  exact ha

theorem TracefulIkInit.failure {α : Type} {Q : α → Prop} :
    TracefulIkInit Q (Alternative.failure : Traceful α) := by
  unfold TracefulIkInit
  intro _ htr
  simp only [Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

private theorem run_bind_fst_iki {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd_iki {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem TracefulIkInit.bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulIkInit Q₁ x) (hf : ∀ a : α, Q₁ a → TracefulIkInit Q₂ (f a)) :
    TracefulIkInit Q₂ (x >>= f) := by
  intro tr htr
  rw [run_bind_snd_iki, run_bind_fst_iki]
  have h1 := hx tr htr
  cases hres : (x.run tr).1 with
  | none => exact ⟨h1.1, fun _ hb => by cases hb⟩
  | some a => exact hf a (h1.2 a hres) _ h1.1

theorem tracefulIkInit_run_snd {α : Type} {Q : α → Prop} {x : Traceful α}
    (hx : TracefulIkInit Q x) {tr : ExecTrace} (htr : TraceIkInit tr) :
    TraceIkInit ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulIkInit.bind hx (fun _ _ => TracefulIkInit.pure (Q := fun _ => True) trivial) tr htr).1

theorem TracefulIkInit.guardP (p : Prop) [Decidable p] :
    TracefulIkInit (fun _ => True) (_root_.guard p) := by
  unfold _root_.guard
  split
  · exact TracefulIkInit.pure trivial
  · exact TracefulIkInit.failure

theorem tracefulIkInit_guardTrace (p : ExecTrace → Bool) :
    TracefulIkInit (fun _ => True) (guardTrace p) := by
  unfold TracefulIkInit guardTrace
  intro _ htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulIkInit_traceLength : TracefulIkInit (fun _ => True) traceLength := by
  unfold TracefulIkInit traceLength
  intro _ htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulIkInit.getEntry_any {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulIkInit (fun (_ : E) => True) (getEntry j : Traceful E) := by
  unfold TracefulIkInit
  intro _ htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulIkInit.getEntry_st (j : Nat) :
    TracefulIkInit (fun (e : IkStEntry) => TrStateIkInit e.st.state) (getEntry j) := by
  unfold TracefulIkInit
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).1 e he
  · cases he

theorem TracefulIkInit.getEntry_pq (j : Nat) :
    TracefulIkInit (fun (e : IkPQStEntry) => PQStateIkInit e.st.state) (getEntry j) := by
  unfold TracefulIkInit
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2.1 e he
  · cases he

theorem TracefulIkInit.getEntry_ev (j : Nat) :
    TracefulIkInit (fun (e : IkPQEvEntry) => PQEventIkInit e.ev) (getEntry j) := by
  unfold TracefulIkInit
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2.2 e he
  · cases he

theorem TracefulIkInit.receiveMessage (j : Nat) :
    TracefulIkInit (fun _ => True) (Network.receiveMessage j) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TracefulIkInit.bind (TracefulIkInit.getEntry_any j) fun _ _ => TracefulIkInit.pure trivial

theorem tracefulIkInit_receiveSignalMsg (msgIdx : Nat) :
    TracefulIkInit (fun _ => True) (receiveSignalMsg msgIdx) := by
  unfold receiveSignalMsg
  refine TracefulIkInit.bind (TracefulIkInit.receiveMessage msgIdx) fun _ _ => ?_
  split
  · exact TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ => TracefulIkInit.pure trivial
  · exact TracefulIkInit.failure

theorem TracefulIkInit.getLocalState (p : Participant) (j : Nat) :
    TracefulIkInit (fun (st : TRState) => TrStateIkInit st) (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulIkInit.bind
    (TracefulIkInit.bind (TracefulIkInit.getEntry_st j) fun _ he =>
      TracefulIkInit.pure
        (Q := fun (ls : PersistentLocalState.LocalState TRState) => TrStateIkInit ls.state) he)
    fun _ hst => ?_
  exact TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ => TracefulIkInit.pure hst

theorem TracefulIkInit.getLocalStatePQ (p : Participant) (j : Nat) :
    TracefulIkInit (fun (st : DY.Libsignal.PQXDH.PQXDHState) => PQStateIkInit st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulIkInit.bind
    (TracefulIkInit.bind (TracefulIkInit.getEntry_pq j) fun _ he =>
      TracefulIkInit.pure
        (Q := fun (ls : PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) =>
          PQStateIkInit ls.state) he)
    fun _ hst => ?_
  exact TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ => TracefulIkInit.pure hst

theorem TracefulIkInit.getKey (p : Participant) (j : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    TracefulIkInit (fun (sk : DY.Bytes) => kind = .identity → IkPkIsInit (dhPk sk))
      (DY.Libsignal.PQXDH.getKey p j kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine TracefulIkInit.bind (TracefulIkInit.getLocalStatePQ p j) fun st hst => ?_
  refine TracefulIkInit.bind (Q₁ := fun _ => st.kind = kind) ?_ fun _ hk =>
    TracefulIkInit.pure fun hkind => hst (hk.trans hkind)
  unfold _root_.guard
  split
  · next h => exact TracefulIkInit.pure h
  · exact TracefulIkInit.failure

theorem TracefulIkInit.lookupIdentity (p : Participant) (j : Nat) :
    TracefulIkInit (fun (kv : DY.Bytes × DY.Bytes) => IkPkIsInit kv.1)
      (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulIkInit.bind (TracefulIkInit.getEntry_ev j) fun e hev => ?_
  split
  · next p' ikPk vkPk honest heq =>
    exact TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ =>
      TracefulIkInit.pure (hev p' ikPk vkPk honest heq)
  · exact TracefulIkInit.failure

theorem TracefulIkInit.genRand (n : Nat) : TracefulIkInit (fun _ => True) (DY.Random.genRand n) := by
  unfold TracefulIkInit
  intro _ htr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceIkInit_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIkInit.sendMessage (msg : DY.Bytes) :
    TracefulIkInit (fun _ => True) (Network.sendMessage msg) := by
  unfold TracefulIkInit
  intro _ htr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  exact ⟨traceIkInit_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIkInit.logEvent (ev : TREvent) :
    TracefulIkInit (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulIkInit
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceIkInit_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIkInit.logEventPQ {ev : DY.Libsignal.PQXDH.PQXDHEvent} (hev : PQEventIkInit ev) :
    TracefulIkInit (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulIkInit
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨traceIkInit_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), ?_⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hev

theorem TracefulIkInit.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulIkInit (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulIkInit
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceIkInit_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIkInit.storeLocalState (p : Participant) {st : TRState} (hst : TrStateIkInit st) :
    TracefulIkInit (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulIkInit
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceIkInit_append ⟨?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst

theorem TracefulIkInit.storeLocalStatePQ (p : Participant) {st : DY.Libsignal.PQXDH.PQXDHState}
    (hst : PQStateIkInit st) :
    TracefulIkInit (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulIkInit
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceIkInit_append ⟨fun _ h => (by cases h), ?_, fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst

theorem tracefulIkInit_guardOnTrace (p : ExecTrace → Bool) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  unfold TracefulIkInit DY.Libsignal.PQXDH.guardTrace
  intro tr htr
  by_cases hp : p tr = true <;> simp only [Traceful.run_mk, hp, Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨htr, fun _ _ => trivial⟩

/-! ## Transition Preservation -/

theorem tracefulIkInit_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : TrStateIkInit st) :
    TracefulIkInit (fun _ => True) (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
    TracefulIkInit.storeLocalState me hst

theorem tracefulIkInit_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    TracefulIkInit (fun _ => True) (logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero =>
    unfold logSkippedKeys
    exact TracefulIkInit.pure trivial
  | succ k ih =>
    unfold logSkippedKeys
    exact TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => ih (kdfCk ck).1 (n + 1)

theorem tracefulIkInit_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    TracefulIkInit (fun _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ => ?_
  unfold TracefulIkInit
  intro _ htr
  dsimp [liftM, monadLift, MonadLift.monadLift]
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem trStateIkInit_setRecvChain {st : TRState} {c' : RecvChain}
    (spqr' : DY.Bytes) (hst : TrStateIkInit st) (hc' : IsKey32 c'.chainKey) :
    TrStateIkInit { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
  refine ⟨hst.1, hst.2.1, hst.2.2.1, fun c hc => ?_⟩
  unfold setRecvChain at hc
  obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc
  split at heq <;> subst heq
  · exact hc'
  · exact hst.2.2.2 c₀ hc₀

theorem isKey32_recvChainFor {st : TRState} {pk : DY.Bytes} {c : RecvChain} {b : Bool}
    (hst : TrStateIkInit st) (hrc : recvChainFor st.toDRState pk = some (c, b)) :
    IsKey32 c.chainKey := by
  unfold recvChainFor at hrc
  rcases hfind : findRecvChain st.toDRState.recv pk with _ | c₀
  · rw [hfind] at hrc; dsimp only at hrc
    split at hrc
    · cases hrc
    · injection hrc with hrc
      rcases Prod.mk.inj hrc with ⟨rfl, _⟩
      exact isKey32_createChain_snd _ _ _
  · rw [hfind] at hrc
    injection hrc with hrc
    rcases Prod.mk.inj hrc with ⟨rfl, _⟩
    unfold findRecvChain at hfind
    exact hst.2.2.2 c₀ (List.mem_of_find?_eq_some hfind)

theorem isKey32_consumeMessageKey {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hcm : consumeMessageKey c counter = some (seed, c')) :
    IsKey32 c'.chainKey := by
  unfold consumeMessageKey at hcm
  split at hcm
  · cases hcm
  · split at hcm
    · cases hcm
    · split at hcm
      · cases hcm
      · injection hcm with hcm
        rcases Prod.mk.inj hcm with ⟨_, rfl⟩
        exact isKey32_kdfCk_fst _

theorem tracefulIkInit_dhRatchetStep {st : TRState} (pk : DY.Bytes) (hst : TrStateIkInit st) :
    TracefulIkInit (fun (p : TRState × RecvChain) => TrStateIkInit p.1 ∧ IsKey32 p.2.chainKey)
      (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand 32) fun dhs' _ => ?_
  refine TracefulIkInit.pure ⟨⟨hst.1, hst.2.1, isKey32_createChain_fst _ _ _, fun c' hc' => ?_⟩,
    isKey32_createChain_snd _ _ _⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst.2.2.2 c' hmem
  · rcases List.mem_singleton.mp hmem with rfl
    exact isKey32_createChain_snd _ _ _

theorem tracefulIkInit_ensureReceiverChain {st : TRState} (pk : DY.Bytes) (hst : TrStateIkInit st) :
    TracefulIkInit (fun (p : TRState × RecvChain × Bool) => TrStateIkInit p.1 ∧ IsKey32 p.2.1.chainKey)
      (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · next c hr => exact TracefulIkInit.pure ⟨hst, isKey32_recvChainFor hst hr⟩
  · exact TracefulIkInit.bind (tracefulIkInit_dhRatchetStep pk hst) fun ⟨_, _⟩ h => TracefulIkInit.pure h
  · exact TracefulIkInit.failure

theorem tracefulIkInit_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulIkInit (fun _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  refine TracefulIkInit.bind (TracefulIkInit.getLocalState me stateIdx) fun st hst =>
    TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand 32) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand coinsLen) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.receiveMessage pqIdx) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
    TracefulIkInit.bind (tracefulIkInit_logMessageKeyAndStore me _ .sender _ _ _ _ _ hst) fun _ _ =>
      TracefulIkInit.sendMessage _

theorem tracefulIkInit_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    TracefulIkInit (fun _ => True) (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact TracefulIkInit.bind (TracefulIkInit.getLocalState me stateIdx) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand 32) fun _ _ => TracefulIkInit.failure

theorem tracefulIkInit_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulIkInit (fun _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulIkInit.bind (TracefulIkInit.getLocalState me stateIdx) fun st₀ hst₀ =>
    TracefulIkInit.bind (tracefulIkInit_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulIkInit.bind (tracefulIkInit_ensureReceiverChain msg.ratchetKey hst₀)
      fun ⟨st, c, ratcheted⟩ ⟨hst, _⟩ => ?_
  dsimp only
  split
  · next seed c' hcm =>
    have hc' : IsKey32 c'.chainKey := isKey32_consumeMessageKey hcm
    split
    · next spqr' key _ =>
      have hst' := trStateIkInit_setRecvChain spqr' hst hc'
      refine TracefulIkInit.bind (TracefulIkInit.sendMessage key) fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulIkInit.bind (tracefulIkInit_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      have hrest :
          TracefulIkInit (fun _ => True)
            (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                  (msg.counter.toNat - c.index.toNat)
                DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
                logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulIkInit.bind (tracefulIkInit_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
            tracefulIkInit_logMessageKeyAndStore me _ .receiver _ _ _ _ _ hst'
      split
      · exact TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
          TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => hrest
      · exact hrest
    · exact TracefulIkInit.failure
  · exact TracefulIkInit.failure

theorem tracefulIkInit_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulIkInit (fun _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulIkInit.bind (TracefulIkInit.getLocalState me stateIdx) fun st hst =>
    TracefulIkInit.bind (tracefulIkInit_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulIkInit.bind (TracefulIkInit.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TracefulIkInit.bind (TracefulIkInit.guardP _) fun _ _ =>
      TracefulIkInit.bind (tracefulIkInit_guardTrace _) fun _ _ => ?_
    split
    · next spqr' key _ =>
      exact TracefulIkInit.bind (TracefulIkInit.sendMessage key) fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulIkInit.bind (tracefulIkInit_verifyMacAndDecrypt st msg pqSalt _) fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
        tracefulIkInit_logMessageKeyAndStore me _ .receiver _ _ _ _ _ hst
    · exact TracefulIkInit.failure
  · exact TracefulIkInit.failure

theorem tracefulIkInit_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulIkInit (fun _ => True) (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine TracefulIkInit.bind (TracefulIkInit.getLocalState me stateIdx) fun _ _ => ?_
  cases k with
  | rk => exact TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => TracefulIkInit.sendMessage _
  | dhs => exact TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => TracefulIkInit.sendMessage _
  | cks => exact TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => TracefulIkInit.sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => TracefulIkInit.sendMessage _
    · exact TracefulIkInit.failure

theorem tracefulIkInit_exposeSpqr (me : Participant) (stateIdx : Nat) :
    TracefulIkInit (fun _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact TracefulIkInit.bind (TracefulIkInit.getLocalState me stateIdx) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => TracefulIkInit.sendMessage _

theorem tracefulIkInit_exposeSkipped (skippedKeyEventIdx : Nat) :
    TracefulIkInit (fun _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulIkInit.bind (TracefulIkInit.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · exact TracefulIkInit.bind (tracefulIkInit_guardTrace _) fun _ _ =>
      TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
      TracefulIkInit.sendMessage _
  · exact TracefulIkInit.failure

theorem tracefulIkInit_compromiseIK (p : Participant) (j : Nat) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact TracefulIkInit.bind (TracefulIkInit.getKey p j _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.sendMessage _

theorem tracefulIkInit_compromiseSPK (p : Participant) (j : Nat) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact TracefulIkInit.bind (TracefulIkInit.getKey p j _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.sendMessage _

theorem tracefulIkInit_compromisePQSPK (p : Participant) (j : Nat) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact TracefulIkInit.bind (TracefulIkInit.getKey p j _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.sendMessage _

theorem tracefulIkInit_compromiseOPK (p : Participant) (j : Nat) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact TracefulIkInit.bind (TracefulIkInit.getKey p j _) fun _ _ =>
    TracefulIkInit.bind (tracefulIkInit_guardOnTrace _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.sendMessage _

theorem tracefulIkInit_genSignedPrekey (b : Participant) (j : Nat) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact TracefulIkInit.bind (TracefulIkInit.getKey b j _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand 32) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand 64) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.storeLocalStatePQ b fun h => by cases h) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ => TracefulIkInit.pure trivial

theorem tracefulIkInit_genPQPrekey (b : Participant) (j : Nat) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact TracefulIkInit.bind (TracefulIkInit.getKey b j _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand 64) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.genRand 64) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.storeLocalStatePQ b fun h => by cases h) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ => TracefulIkInit.pure trivial

theorem tracefulIkInit_genOneTimePrekey (b : Participant) :
    TracefulIkInit (fun _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact TracefulIkInit.bind (TracefulIkInit.genRand 32) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.storeLocalStatePQ b fun h => by cases h) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ => TracefulIkInit.pure trivial

theorem tracefulIkInit_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulIkInit (fun (o : DY.Libsignal.PQXDH.AliceHandshakeOut) =>
        IkPkIsInit o.ikA ∧ IkPkIsInit o.ikB ∧ IsKey32 o.keys.ck)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulIkInit.bind (TracefulIkInit.getKey a idStateIdx _); intro ikA hikA
  apply TracefulIkInit.bind (TracefulIkInit.lookupIdentity b regIdxB); intro ikv hikB
  rcases ikv with ⟨ikB, vkB⟩
  dsimp only at hikB ⊢
  apply TracefulIkInit.bind (TracefulIkInit.receiveMessage h.spk); intro spk _
  apply TracefulIkInit.bind (TracefulIkInit.receiveMessage h.spkSig); intro _ _
  apply TracefulIkInit.bind (TracefulIkInit.receiveMessage h.pqpk); intro pqpk _
  apply TracefulIkInit.bind (TracefulIkInit.receiveMessage h.pqpkSig); intro _ _
  apply TracefulIkInit.bind (TracefulIkInit.guardP _); intro _ _
  apply TracefulIkInit.bind (TracefulIkInit.guardP _); intro _ _
  split
  all_goals first
    | (apply TracefulIkInit.bind (TracefulIkInit.receiveMessage _); intro _ _)
    | skip
  all_goals
    apply TracefulIkInit.bind (TracefulIkInit.pure (Q := fun _ => True) trivial)
    intro opk _
    apply TracefulIkInit.bind (TracefulIkInit.genRand 32); intro ek _
    apply TracefulIkInit.bind (TracefulIkInit.guardP _); intro _ _
    apply TracefulIkInit.bind (TracefulIkInit.guardP _); intro _ _
    apply TracefulIkInit.bind (TracefulIkInit.genRand 32); intro entropy _
    rcases hag : DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pqpk opk entropy with ⟨ct, keys⟩
    try dsimp only
    refine TracefulIkInit.pure ⟨hikA rfl, hikB, ?_⟩
    unfold DY.Libsignal.PQXDH.aliceAgreement at hag
    rcases hke : DY.PQKem.kemEncap pqpk entropy with ⟨ct', ss⟩
    simp only [hke, Prod.mk.injEq] at hag
    rw [← hag.2]
    exact isKey32_pqxdhKdf_ck _

private theorem serializedIk_mem_of_ikPkIsInit {pk : DY.Bytes} (h : IkPkIsInit pk) :
    DY.Libsignal.PQXDH.serializedIk pk = DY.Libsignal.PQXDH.serializedIk (dhPk (randTerm 0 32)) ∨
    DY.Libsignal.PQXDH.serializedIk pk = DY.Libsignal.PQXDH.serializedIk (dhPk (randTerm 5 32)) :=
  h.imp (congrArg DY.Libsignal.PQXDH.serializedIk) (congrArg DY.Libsignal.PQXDH.serializedIk)

theorem tracefulIkInit_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulIkInit (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulIkInit.bind (tracefulIkInit_aliceHandshake a b idStateIdx regIdxB h) fun o ho =>
    TracefulIkInit.bind (TracefulIkInit.genRand 32) fun dhsA _ => ?_
  have hrkA : IsKey32 (createChain o.keys.rk o.spk dhsA).1 := isKey32_createChain_fst _ _ _
  rcases hcc : createChain o.keys.rk o.spk dhsA with ⟨rkA, cksA⟩
  rw [hcc] at hrkA
  dsimp only
  refine TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ =>
    TracefulIkInit.bind tracefulIkInit_traceLength fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
    TracefulIkInit.bind (TracefulIkInit.logEventC _) fun _ _ =>
    TracefulIkInit.storeLocalState a
      ⟨serializedIk_mem_of_ikPkIsInit ho.1, serializedIk_mem_of_ikPkIsInit ho.2.1, hrkA, ?_⟩
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact ho.2.2

theorem tracefulIkInit_bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulIkInit (fun (o : DY.Libsignal.PQXDH.BobHandshakeOut) =>
        IkPkIsInit o.ikA ∧ IkPkIsInit o.ikB ∧ IsKey32 o.keys.rk)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TracefulIkInit.bind (TracefulIkInit.getKey b h.ik _); intro ikB hikB
  apply TracefulIkInit.bind (TracefulIkInit.getKey b h.spk _); intro spkSk _
  apply TracefulIkInit.bind (TracefulIkInit.getKey b h.pqspk _); intro pqsk _
  dsimp only
  split
  all_goals first
    | (apply TracefulIkInit.bind (TracefulIkInit.getKey b _ _); intro _ _)
    | skip
  all_goals
    apply TracefulIkInit.bind (TracefulIkInit.pure (Q := fun _ => True) trivial)
    intro opkSk _
    apply TracefulIkInit.bind (TracefulIkInit.lookupIdentity a regIdxA); intro ikv hikA
    rcases ikv with ⟨ikA, vkA⟩
    dsimp only at hikA ⊢
    apply TracefulIkInit.bind (TracefulIkInit.receiveMessage ekIdx); intro ek _
    apply TracefulIkInit.bind (TracefulIkInit.receiveMessage ctIdx); intro ct _
    apply TracefulIkInit.bind (TracefulIkInit.guardP _); intro _ _
    split
    · next keys hag =>
      refine TracefulIkInit.pure ⟨hikA, hikB rfl, ?_⟩
      unfold DY.Libsignal.PQXDH.bobAgreement at hag
      simp only [Pure.pure, Option.some.injEq] at hag
      rw [← hag]
      exact isKey32_pqxdhKdf_rk _
    · exact TracefulIkInit.failure

theorem tracefulIkInit_bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulIkInit (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulIkInit.bind (tracefulIkInit_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o ho =>
    TracefulIkInit.bind (tracefulIkInit_receiveSignalMsg mh.msg) fun msg _ => ?_
  refine TracefulIkInit.bind (tracefulIkInit_ensureReceiverChain msg.ratchetKey ?hst0)
    fun x hst => ?_
  case hst0 =>
    exact ⟨serializedIk_mem_of_ikPkIsInit ho.2.1, serializedIk_mem_of_ikPkIsInit ho.1,
      ho.2.2, fun c hc => by simp at hc⟩
  rcases x with ⟨st, c, ratcheted⟩
  rcases hst with ⟨hst, _⟩
  dsimp only at hst ⊢
  split
  · next seed c' hcm =>
    have hc' : IsKey32 c'.chainKey := isKey32_consumeMessageKey hcm
    split
    · next spqr' key _ =>
      have hst' := trStateIkInit_setRecvChain spqr' hst hc'
      refine TracefulIkInit.bind (TracefulIkInit.sendMessage key) fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulIkInit.bind (tracefulIkInit_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      split
      all_goals first
        | refine TracefulIkInit.bind (tracefulIkInit_guardOnTrace _) fun _ _ =>
            TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ => ?_
        | skip
      all_goals refine TracefulIkInit.bind tracefulIkInit_traceLength fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ => ?_
      all_goals split
      all_goals first
        | refine TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
            TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ => ?_
        | skip
      all_goals exact TracefulIkInit.bind (TracefulIkInit.logEventC _) fun _ _ =>
          TracefulIkInit.bind tracefulIkInit_traceLength fun _ _ =>
          TracefulIkInit.bind (tracefulIkInit_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulIkInit.bind (TracefulIkInit.logEvent _) fun _ _ =>
          tracefulIkInit_logMessageKeyAndStore b _ .receiver _ _ _ _ _ hst'
    · exact TracefulIkInit.failure
  · exact TracefulIkInit.failure

/-! ## Setup Base Case and Move Induction -/

private theorem traceIkInit_registerIdentity_at (p : Participant) {tr : ExecTrace}
    (htr : TraceIkInit tr) (hlen : tr.length = 0 ∨ tr.length = 5) :
    TraceIkInit ((DY.Libsignal.PQXDH.registerIdentity p).run tr).2.val := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  rw [run_bind_snd_iki]
  unfold DY.Libsignal.PQXDH.guardTrace
  rw [Traceful.run_mk]
  by_cases hp : (!DY.Libsignal.PQXDH.isRegisteredB tr p) = true
  · simp only [hp, ↓reduceIte]
    have hik : IkPkIsInit (dhPk (randTerm tr.length 32)) := by
      rcases hlen with h0 | h5
      · rw [h0]; exact Or.inl rfl
      · rw [h5]; exact Or.inr rfl
    let ik := randTerm tr.length 32
    have hstep : TracefulIkInit (fun _ => True)
        (do DY.ProtocolEvent.logEvent
              (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered p (dhPk ik) (DY.Signature.vk ik) true)
            let _ ← Network.sendMessage (dhPk ik)
            let _ ← Network.sendMessage (DY.Signature.vk ik)
            PersistentLocalState.storeLocalState p
              ({ kind := .identity, sk := ik } : DY.Libsignal.PQXDH.PQXDHState)) :=
      TracefulIkInit.bind (TracefulIkInit.logEventPQ
        (by intro _ _ _ _ hev; injection hev with _ hpk _ _; subst hpk; exact hik)) fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ =>
        TracefulIkInit.bind (TracefulIkInit.sendMessage _) fun _ _ =>
        TracefulIkInit.storeLocalStatePQ p (fun _ => hik)
    have hg1 : ((DY.Random.genRand 32).run tr).1 = some ik := by
      rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        run_bind_fst_iki, Traceful.run_mk]
      dsimp only
      rw [Traceful.run_pure]
      rfl
    have hg2 : ((DY.Random.genRand 32).run tr).2.val = tr.append (RndE 32) := by
      rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        run_bind_snd_iki, Traceful.run_mk]
      dsimp only
      rw [Traceful.run_pure]
    rw [run_bind_snd_iki, hg1, hg2]
    dsimp only
    have htr1 : TraceIkInit (tr.append (RndE 32)) :=
      traceIkInit_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr
    exact (hstep (tr.append (RndE 32)) htr1).1
  · simp only [hp]
    exact htr

private theorem traceIkInit_setupTr1 (a : Participant) : TraceIkInit (setupTr1 a) := by
  have h := traceIkInit_registerIdentity_at a traceIkInit_nil
    (Or.inl Symbolic.DYBridge.DY.Trace.length_eq_1)
  rwa [(runs_registerIdentity_a a).2] at h

private theorem traceIkInit_setupTr2 {a b : Participant} (hNe : a ≠ b) : TraceIkInit (setupTr2 a b) := by
  have h := traceIkInit_registerIdentity_at b (traceIkInit_setupTr1 a)
    (Or.inr (by simp [setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]))
  rwa [(runs_registerIdentity_b hNe).2] at h

private theorem traceIkInit_setupTrace (r₀ : ProtocolSetup) (hNe : r₀.alice ≠ r₀.bob) :
    TraceIkInit (setupTrace r₀) := by
  have htr3 : TraceIkInit (setupTr3 r₀.alice r₀.bob) := by
    have h := (tracefulIkInit_genSignedPrekey r₀.bob 9 (setupTr2 r₀.alice r₀.bob)
      (traceIkInit_setupTr2 hNe)).1
    rwa [(runs_genSignedPrekey r₀.alice r₀.bob).2] at h
  have htr4 : TraceIkInit (setupTr4 r₀.alice r₀.bob) := by
    have h := (tracefulIkInit_genPQPrekey r₀.bob 9 (setupTr3 r₀.alice r₀.bob) htr3).1
    rwa [(runs_genPQPrekey r₀.alice r₀.bob).2] at h
  have htr5 : TraceIkInit (setupTr5 r₀.alice r₀.bob) := by
    have h := (tracefulIkInit_genOneTimePrekey r₀.bob (setupTr4 r₀.alice r₀.bob) htr4).1
    rwa [(runs_genOneTimePrekey r₀.alice r₀.bob).2] at h
  rw [setupTrace_eq r₀ hNe]
  cases r₀.withOpk
  · exact htr4
  · exact htr5

theorem traceIkInit_move_next {tr : ExecTrace} {m : Move} (hm : m.isSetup = false)
    (htr : TraceIkInit tr) :
    TraceIkInit (m.next tr) := by
  unfold Move.next Move.act
  cases m with
  | setup a b withOpk => simp [Move.isSetup] at hm
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulIkInit_run_snd (tracefulIkInit_aliceStart a b idStateIdx regIdxB h) htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulIkInit_run_snd (tracefulIkInit_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulIkInit_run_snd (tracefulIkInit_messageEncrypt me stateIdx coinsLen pqIdx) htr
  | encryptAbort me stateIdx =>
    exact tracefulIkInit_run_snd (tracefulIkInit_messageEncryptAbort me stateIdx) htr
  | encryptFail me stateIdx coinsLen =>
    dsimp only
    have h_assoc :
        ((do let n ← traceLength; let _ ← messageEncrypt me stateIdx coinsLen (n + 3); Pure.pure ()).run tr).2.val =
        (((do let n ← traceLength; messageEncrypt me stateIdx coinsLen (n + 3)) >>= fun _ => Pure.pure ()).run tr).2.val := by
      rw [run_bind_snd_iki, run_bind_snd_iki, run_bind_fst_iki]
      rcases ht : (traceLength.run tr).1 with _ | n
      · dsimp only; rw [run_bind_snd_iki, ht]
      · dsimp only; rw [run_bind_snd_iki, run_bind_snd_iki, ht]
    rw [h_assoc]
    exact tracefulIkInit_run_snd
      (TracefulIkInit.bind tracefulIkInit_traceLength
        fun n _ => tracefulIkInit_messageEncrypt me stateIdx coinsLen (n + 3)) htr
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulIkInit_run_snd (tracefulIkInit_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulIkInit_run_snd
      (tracefulIkInit_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) htr
  | reject _ =>
    dsimp only
    rw [Traceful.run_pure]
    exact htr
  | compromiseIK p stateIdx =>
    exact tracefulIkInit_run_snd (tracefulIkInit_compromiseIK p stateIdx) htr
  | compromiseSPK p stateIdx =>
    exact tracefulIkInit_run_snd (tracefulIkInit_compromiseSPK p stateIdx) htr
  | compromisePQSPK p stateIdx =>
    exact tracefulIkInit_run_snd (tracefulIkInit_compromisePQSPK p stateIdx) htr
  | compromiseOPK p stateIdx =>
    exact tracefulIkInit_run_snd (tracefulIkInit_compromiseOPK p stateIdx) htr
  | exposeKey me stateIdx k =>
    exact tracefulIkInit_run_snd (tracefulIkInit_exposeKey me stateIdx k) htr
  | exposeSpqr me stateIdx =>
    exact tracefulIkInit_run_snd (tracefulIkInit_exposeSpqr me stateIdx) htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulIkInit_run_snd (tracefulIkInit_exposeSkipped skippedKeyEventIdx) htr
  | attackerSend msg =>
    exact tracefulIkInit_run_snd (TracefulIkInit.sendMessage msg) htr
  | brkDH =>
    exact (TracefulIkInit.logEventPQ (ev := .BrokenDH) (fun _ _ _ _ h => by cases h) tr htr).1
  | brkKEM =>
    exact (TracefulIkInit.logEventPQ (ev := .BrokenKEM) (fun _ _ _ _ h => by cases h) tr htr).1

theorem traceIkInit_runMoves :
    ∀ (L : List Move) (tr : ExecTrace),
      (∀ m ∈ L, m.isSetup = false) → TraceIkInit tr → TraceIkInit (runMoves L tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hL, htr =>
    traceIkInit_runMoves ms (m.next tr)
      (fun m' hm' => hL m' (List.mem_cons_of_mem m hm'))
      (traceIkInit_move_next (hL m List.mem_cons_self) htr)

private theorem isRegisteredB_setupTr1_self (a : DY.Participant) :
    (!DY.Libsignal.PQXDH.isRegisteredB (setupTr1 a) a) = false := by
  have hbeq : (a == a) = true := beq_self_eq_true a
  have hlen : (setupTr1 a).length = 5 := by
    simp [setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hrng : List.range 5 = [0, 1, 2, 3, 4] := rfl
  unfold DY.Libsignal.PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [hlen, hrng]
  simp only [List.any_cons, List.any_nil, Bool.or_false,
    setupTr1_at?_ev_0, setupTr1_at?_ev_1, setupTr1_at?_ev_2,
    setupTr1_at?_ev_3, setupTr1_at?_ev_4, hbeq]
  rfl

private theorem alice_ne_bob_of_modelRun {r₀ : ProtocolSetup} {ms : List Move} (hrun : ModelRun r₀ ms) :
    r₀.alice ≠ r₀.bob := by
  intro hEq
  have hlen := hrun.1
  have hreg1 : ((DY.Libsignal.PQXDH.registerIdentity r₀.alice).run (setupTr1 r₀.alice)).1 = none := by
    unfold DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.guardTrace
    rw [run_bind_fst_iki]
    simp only [Traceful.run_mk, isRegisteredB_setupTr1_self, Bool.false_eq_true, ↓reduceIte]
  have hreg2 : ((DY.Libsignal.PQXDH.registerIdentity r₀.alice).run (setupTr1 r₀.alice)).2.val =
      setupTr1 r₀.alice := by
    unfold DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.guardTrace
    rw [run_bind_snd_iki]
    simp only [Traceful.run_mk, isRegisteredB_setupTr1_self, Bool.false_eq_true, ↓reduceIte]
  have htr : setupTrace r₀ = setupTr1 r₀.alice := by
    unfold setupTrace setupAct
    rw [← hEq]
    rw [run_bind_snd_iki, (runs_registerIdentity_a r₀.alice).1, (runs_registerIdentity_a r₀.alice).2]
    dsimp only
    rw [run_bind_snd_iki, hreg1, hreg2]
  have hrnd : setupRandoms r₀ = [randTerm 0 32] := by
    unfold setupRandoms
    rw [htr, newRandoms_setupTr1]
    rfl
  rw [hrnd] at hlen
  rcases h : r₀.withOpk <;> simp [h] at hlen

/-! ## Stored-State Theorem -/

/-- Identity-key provenance and 32-byte root/receiver-chain key lengths for a stored `TRState`. -/
structure TrStateRkCkIk (r₀ : ProtocolSetup) (st : TRState) : Prop where
  myIk : st.myIk = DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 0) ∨
    st.myIk = DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 2)
  peerIk : st.peerIk = DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 0) ∨
    st.peerIk = DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 2)
  rk_len : ∀ (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost),
    ProtocolSetupWF r₀ → GhostAndSemMatchSetup interpretation r₀ S g → (gamma interpretation S g st.rk).length = 32
  recv_ck_len : ∀ (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost),
    ProtocolSetupWF r₀ → GhostAndSemMatchSetup interpretation r₀ S g → ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32

theorem trStateRkCkIk_of_getLocalState {r₀ : ProtocolSetup} {ms : List Move}
    {p : Participant} {stateIdx : Nat} {st : TRState} (hrun : ModelRun r₀ ms)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 = some st) :
    TrStateRkCkIk r₀ st := by
  have hNe : r₀.alice ≠ r₀.bob := alice_ne_bob_of_modelRun hrun
  have htr_ik : TraceIkInit (runTraceMoves r₀ ms) := by
    rw [runTraceMoves, runMoves, setupMove_next_nil]
    exact traceIkInit_runMoves ms (setupTrace r₀) hrun.2.1 (traceIkInit_setupTrace r₀ hNe)
  have hik : TrStateIkInit st :=
    (TracefulIkInit.getLocalState p stateIdx (runTraceMoves r₀ ms) htr_ik).2 st hst
  have hpub0 : setupPublic r₀ 0 = dhPk (randTerm 0 32) := by
    rw [(setupPublic_eq r₀ hNe).1, (setupSecret_eq r₀ hNe).1]
  have hpub2 : setupPublic r₀ 2 = dhPk (randTerm 5 32) := by
    rw [(setupPublic_eq r₀ hNe).2.1, (setupSecret_eq r₀ hNe).2.1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpub0, hpub2]; exact hik.1
  · rw [hpub0, hpub2]; exact hik.2.1
  · intro interpretation S g _ _
    exact hik.2.2.1 interpretation S g
  · intro interpretation S g _ _ c hc
    exact hik.2.2.2 c hc interpretation S g

end RecvDecStep

end Symbolic.Swarm.CREF.TR
