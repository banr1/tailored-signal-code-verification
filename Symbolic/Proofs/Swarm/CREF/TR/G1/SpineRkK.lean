/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkKDefs
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
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRkCore
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
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
# Known-Peer-Key Seed Spine Invariant

Proves that every entry and available `TRState` along `runTraceMoves r₀ ms` satisfies the
known-peer-key honest-spine invariant `SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T)`, recording
attacker knowledge of the peer public key at every PQXDH base DH hole (`IkmHolesK`) and every
`kdfRk` step (`DhHoleK`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent KeyDir RecvChain findRecvChain
  setRecvChain recvChainFor consumeMessageKey kdfCk createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf agree)
open Symbolic.Swarm.CREF.TR (attackerKnows_of_at?_network
  attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg)
open Symbolic.Swarm.CREF.TR.G1.Ik (IkStEntry IkPQStEntry IkPQEvEntry proj_inj_ik)

/-! ## Known-Key DH Hole Helpers -/

theorem attackerKnows_x25519Key {T : ExecTrace} {pk : DY.Bytes}
    (h : pk.AttackerKnows T) : (DY.X25519.normalizeX25519Key pk).AttackerKnows T := by
  unfold DY.X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
  rcases hv : pk.view? DY.X25519.Variant.SubF with _ | v; · exact h
  rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h
  exact DY.Bytes.AttackerKnows.prove DY.X25519.normalizeX25519Key.attackerKnowledge _ T ⟨v, h, rfl⟩

theorem dhHoleK_agree {T : ExecTrace} {pk : DY.Bytes} (t : Nat) (hpk : pk.AttackerKnows T) :
    DhHoleK (·.AttackerKnows T) (agree pk (randTerm t 32)) :=
  ⟨DY.X25519.normalizeX25519Key pk, t, rfl, attackerKnows_x25519Key hpk⟩

theorem dhHoleK_dh_x25519Key {T : ExecTrace} {pk : DY.Bytes} (t : Nat) (hpk : pk.AttackerKnows T) :
    DhHoleK (·.AttackerKnows T) (dh (DY.X25519.normalizeX25519Key pk) (randTerm t 32)) :=
  ⟨DY.X25519.normalizeX25519Key pk, t, rfl, attackerKnows_x25519Key hpk⟩

/-! ## Entry Invariants -/

/-- The known-peer-key honest-spine invariant of a session state stored at position `j`. -/
structure SpStateRkK (K : DY.Bytes → Prop) (B : Bool → DY.Bytes → Prop) (j : Nat)
    (st : TRState) : Prop where
  rk : SpineRkK K B true st.rk
  cks : SpineRkK K B true st.cks
  recv : ∀ c ∈ st.recv, SpineRkK K B false c.chainKey
  dhs : ∃ (t : Nat) (pk' : DY.Bytes), t < j ∧ st.dhs = randTerm t 32 ∧ TopDhSecret st.rk pk' t

theorem SpStateRkK.mono_idx {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop} {j j' : Nat}
    {st : TRState} (h : SpStateRkK K B j st) (hj : j ≤ j') : SpStateRkK K B j' st := by
  obtain ⟨t, pk', ht, h1, h2⟩ := h.dhs
  exact ⟨h.rk, h.cks, h.recv, ⟨t, pk', by omega, h1, h2⟩⟩

theorem SpStateRkK.mono {K K' : DY.Bytes → Prop} {B B' : Bool → DY.Bytes → Prop} {j : Nat}
    {st : TRState} (h : SpStateRkK K B j st) (hK : ∀ x, K x → K' x)
    (hB : ∀ c m, B c m → B' c m) : SpStateRkK K' B' j st :=
  ⟨h.rk.mono hK hB, h.cks.mono hK hB, fun c hc => (h.recv c hc).mono hK hB, h.dhs⟩

def PQEventKnown (T : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent) : Prop :=
  ∀ (p : Participant) (ikPk vkPk : DY.Bytes) (honest : Bool),
    ev = .IdentityRegistered p ikPk vkPk honest → ikPk.AttackerKnows T

/-- Per-entry invariant at position `j`, relative to the final trace `T`. -/
def SpEntryOkRK (T : ExecTrace) (j : Nat) (ent : ExecTrace.Entry) : Prop :=
  (∀ e : IkStEntry, TraceEntryHas.proj ent = some e →
    SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) j e.st.state) ∧
  (∀ e : IkPQStEntry, TraceEntryHas.proj ent = some e → PQSkAt T j e.st.state) ∧
  (∀ e : IkPQEvEntry, TraceEntryHas.proj ent = some e → PQEventKnown T e.ev)

def TraceOkRK (T tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), SpEntryOkRK T j (tr.at j hj)

theorem traceOkRK_nil (T : ExecTrace) : TraceOkRK T (DY.Trace.nil : ExecTrace) :=
  fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj

theorem traceOkRK_append {T : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hent : SpEntryOkRK T tr.length (TraceEntryHas.inj e)) (htr : TraceOkRK T tr) :
    TraceOkRK T (tr.append e) := by
  have hle : tr ≤ tr.append e := DY.Trace.append_le tr e
  intro j hj
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt hle]; exact htr j hlt
  · have heq : j = tr.length := by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj; omega
    subst heq; simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

/-! ## Exact-Length and Floor Combinators -/

def TracefulRK {α : Type} (T : ExecTrace) (n : Nat) (Q : α → Nat → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, tr.length = n → (x.run tr).2.val ≤ T → TraceOkRK T tr →
    TraceOkRK T (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a (x.run tr).2.val.length

def TracefulFK {α : Type} (T : ExecTrace) (k : Nat) (Q : α → Nat → Prop) (x : Traceful α) : Prop :=
  ∀ n, k ≤ n → TracefulRK T n Q x

section Combinators

variable {T : ExecTrace}

private theorem run_bind_fst_rkk {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩; · rfl
  rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd_rkk {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩; · rfl
  rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem TracefulRK.pure {α : Type} {n : Nat} {Q : α → Nat → Prop} {a : α} (ha : Q a n) :
    TracefulRK T n Q (Pure.pure a) := by
  unfold TracefulRK
  intro tr hn _ htr
  simp only [Traceful.run_pure]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb; subst hn; exact ha

theorem TracefulRK.failure {α : Type} {n : Nat} {Q : α → Nat → Prop} :
    TracefulRK T n Q (Alternative.failure : Traceful α) := by
  unfold TracefulRK
  intro _ _ _ htr
  simp only [Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

theorem TracefulRK.bind {α β : Type} {n : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulRK T n Q₁ x)
    (hf : ∀ (a : α) (m : Nat), n ≤ m → Q₁ a m → TracefulRK T m Q₂ (f a)) :
    TracefulRK T n Q₂ (x >>= f) := by
  intro tr hn hT htr
  rw [run_bind_snd_rkk] at hT; rw [run_bind_snd_rkk, run_bind_fst_rkk]; revert hT
  cases hres : (x.run tr).1 with
  | none => intro hT; exact ⟨(hx tr hn hT htr).1, fun _ hb => by cases hb⟩
  | some a =>
    intro hT
    have hT1 : (x.run tr).2.val ≤ T :=
      DY.Trace.le_trans _ _ _ ((f a).run (x.run tr).2.val).2.property hT
    have h1 := hx tr hn hT1 htr
    have hle : n ≤ (x.run tr).2.val.length := by
      rw [← hn]; exact traceLen_le_of_le_rk (x.run tr).2.property
    exact hf a _ hle (h1.2 a hres) _ rfl hT h1.1

theorem TracefulRK.mono {α : Type} {n : Nat} {Q Q' : α → Nat → Prop} {x : Traceful α}
    (hx : TracefulRK T n Q x) (h : ∀ a m, Q a m → Q' a m) : TracefulRK T n Q' x :=
  fun tr hn hT htr => ⟨(hx tr hn hT htr).1, fun a ha => h a _ ((hx tr hn hT htr).2 a ha)⟩

theorem TracefulRK.guardP {n : Nat} (p : Prop) [Decidable p] :
    TracefulRK T n (fun _ m => p ∧ m = n) (_root_.guard p) := by
  unfold _root_.guard; split
  · next h => exact TracefulRK.pure ⟨h, rfl⟩
  · exact TracefulRK.failure

theorem TracefulRK.bindF {α β : Type} {n : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulRK T n Q₁ x)
    (hf : ∀ (a : α) (m : Nat), n ≤ m → Q₁ a m → TracefulFK T m Q₂ (f a)) :
    TracefulRK T n Q₂ (x >>= f) :=
  TracefulRK.bind hx fun a m hm hq => (hf a m hm hq) m (Nat.le_refl m)

theorem TracefulFK.pure {α : Type} {k : Nat} {Q : α → Nat → Prop} {a : α}
    (ha : ∀ n, k ≤ n → Q a n) : TracefulFK T k Q (Pure.pure a) :=
  fun n hn => TracefulRK.pure (ha n hn)

theorem TracefulFK.failure {α : Type} {k : Nat} {Q : α → Nat → Prop} :
    TracefulFK T k Q (Alternative.failure : Traceful α) :=
  fun _ _ => TracefulRK.failure

theorem TracefulFK.bind {α β : Type} {k : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulFK T k Q₁ x)
    (hf : ∀ (a : α) (m : Nat), k ≤ m → Q₁ a m → TracefulFK T k Q₂ (f a)) :
    TracefulFK T k Q₂ (x >>= f) :=
  fun n hn => TracefulRK.bind (hx n hn) fun a m hm hq => hf a m (by omega) hq m (by omega)

theorem TracefulFK.bindD {α β : Type} {k : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulFK T k Q₁ x)
    (hf : ∀ (a : α) (m : Nat), k ≤ m → Q₁ a m → TracefulFK T m Q₂ (f a)) :
    TracefulFK T k Q₂ (x >>= f) :=
  fun n hn => TracefulRK.bind (hx n hn) fun a m hm hq => hf a m (by omega) hq m (Nat.le_refl m)

theorem TracefulFK.bindE {α β : Type} {k : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulFK T k Q₁ x)
    (hf : ∀ (a : α) (m : Nat), k ≤ m → Q₁ a m → TracefulRK T m Q₂ (f a)) :
    TracefulFK T k Q₂ (x >>= f) :=
  fun n hn => TracefulRK.bind (hx n hn) fun a m hm hq => hf a m (by omega) hq

theorem TracefulFK.guard {k : Nat} (p : Prop) [Decidable p] :
    TracefulFK T k (fun _ _ => p) (_root_.guard p) :=
  fun _ _ => (TracefulRK.guardP p).mono fun _ _ h => h.1

end Combinators

/-! ## Primitive Steps -/

section Steps

variable {T : ExecTrace} {k : Nat}

theorem tracefulFK_guardTrace (p : ExecTrace → Bool) :
    TracefulFK T k (fun _ _ => True) (guardTrace p) := by
  unfold TracefulFK TracefulRK guardTrace
  intro _ _ _ _ _ htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulFK_traceLength : TracefulFK T k (fun _ _ => True) traceLength := by
  unfold TracefulFK TracefulRK traceLength
  intro _ _ _ _ _ htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulFK_guardOnTrace (p : ExecTrace → Bool) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  unfold TracefulFK TracefulRK DY.Libsignal.PQXDH.guardTrace
  intro _ _ tr _ _ htr
  by_cases hp : p tr = true <;> simp only [Traceful.run_mk, hp, Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulFK.getEntry_any {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulFK T k (fun (_ : E) _ => True) (getEntry j : Traceful E) := by
  unfold TracefulFK TracefulRK
  intro _ _ _ _ _ htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulFK.getEntry_st (j : Nat) :
    TracefulFK T k
      (fun (e : IkStEntry) m => SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) m e.st.state)
      (getEntry j) := by
  unfold TracefulFK TracefulRK
  intro _ _ tr _ _ htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact ((htr j hj).1 e he).mono_idx (Nat.le_of_lt hj)
  · cases he

theorem TracefulFK.getEntry_pq (j : Nat) :
    TracefulFK T k (fun (e : IkPQStEntry) m => PQSkAt T m e.st.state) (getEntry j) := by
  unfold TracefulFK TracefulRK
  intro _ _ tr _ _ htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact ((htr j hj).2.1 e he).mono (Nat.le_of_lt hj)
  · cases he

theorem TracefulFK.getEntry_ev (j : Nat) :
    TracefulFK T k (fun (e : IkPQEvEntry) _ => PQEventKnown T e.ev) (getEntry j) := by
  unfold TracefulFK TracefulRK
  intro _ _ tr _ _ htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2.2 e he
  · cases he

theorem TracefulFK.getEntry_net (j : Nat) :
    TracefulFK T k (fun (e : Network.ExecEntryT) _ => e.msg.AttackerKnows T) (getEntry j) := by
  unfold TracefulFK TracefulRK
  intro _ _ tr _ hT htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk] at hT ⊢
  refine ⟨htr, fun e he => ?_⟩
  exact DY.Bytes.AttackerKnows_le e.msg tr T hT (attackerKnows_of_at?_network he)

theorem TracefulFK.receiveMessage (j : Nat) :
    TracefulFK T k (fun (msg : DY.Bytes) _ => msg.AttackerKnows T) (Network.receiveMessage j) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TracefulFK.bind (TracefulFK.getEntry_net j) fun _ _ _ he => TracefulFK.pure fun _ _ => he

theorem tracefulFK_receiveSignalMsg (j : Nat) :
    TracefulFK T k (fun (msg : TRSignalMsg) _ => msg.ratchetKey.AttackerKnows T)
      (receiveSignalMsg j) := by
  unfold receiveSignalMsg
  refine TracefulFK.bind (TracefulFK.receiveMessage j) fun b _ _ hb => ?_
  split
  · next msg hparse =>
    exact TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ =>
      TracefulFK.pure fun _ _ =>
        (attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg hb hparse).1
  · exact TracefulFK.failure

theorem TracefulFK.getLocalState (p : Participant) (j : Nat) :
    TracefulFK T k (fun (st : TRState) m => SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) m st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulFK.bindD
    (TracefulFK.bindD (TracefulFK.getEntry_st j) fun _ _ _ he =>
      TracefulFK.pure
        (Q := fun (ls : PersistentLocalState.LocalState TRState) n =>
          SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) n ls.state)
        fun _ hn => he.mono_idx hn)
    fun _ _ _ hst => ?_
  exact TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ =>
    TracefulFK.pure fun _ hn => hst.mono_idx hn

theorem TracefulFK.getLocalStatePQ (p : Participant) (j : Nat) :
    TracefulFK T k (fun (st : DY.Libsignal.PQXDH.PQXDHState) m => PQSkAt T m st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulFK.bindD
    (TracefulFK.bindD (TracefulFK.getEntry_pq j) fun _ _ _ he =>
      TracefulFK.pure
        (Q := fun (ls : PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) n =>
          PQSkAt T n ls.state)
        fun _ hn => he.mono hn)
    fun _ _ _ hst => ?_
  exact TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ =>
    TracefulFK.pure fun _ hn => hst.mono hn

theorem TracefulFK.getKey (p : Participant) (j : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    TracefulFK T k (fun (sk : DY.Bytes) m => PQSkAt T m { kind := kind, sk := sk })
      (DY.Libsignal.PQXDH.getKey p j kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine TracefulFK.bindD (TracefulFK.getLocalStatePQ p j) fun st _ _ hst => ?_
  refine TracefulFK.bind (TracefulFK.guard _) fun _ _ _ hk => TracefulFK.pure fun _ hn => ?_
  rcases st with ⟨kind', sk⟩
  obtain rfl : kind' = kind := hk
  exact hst.mono hn

theorem TracefulFK.lookupIdentity (p : Participant) (j : Nat) :
    TracefulFK T k (fun (ikv : DY.Bytes × DY.Bytes) _ => ikv.1.AttackerKnows T)
      (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulFK.bind (TracefulFK.getEntry_ev j) fun e _ _ he => ?_
  split
  · next p' ikPk vkPk honest hev =>
    exact TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ =>
      TracefulFK.pure fun _ _ => he p' ikPk vkPk honest hev
  · exact TracefulFK.failure

theorem TracefulRK.genRand {n : Nat} (size : Nat) :
    TracefulRK T n (fun b m => b = randTerm n size ∧ ¬ PQEvAt T n ∧ m = n + 1)
      (DY.Random.genRand size) := by
  unfold TracefulRK
  intro tr hn hT htr
  have hg1 : ((DY.Random.genRand size).run tr).1 = some (randTerm tr.length size) := by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      run_bind_fst_rkk, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]; rfl
  have hg2 : ((DY.Random.genRand size).run tr).2.val = tr.append (⟨size⟩ : DY.Random.ExecEntryT) := by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      run_bind_snd_rkk, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  rw [hg2] at hT ⊢; rw [hg1]
  refine ⟨traceOkRK_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun a ha => ?_⟩
  injection ha with ha
  subst ha hn
  exact ⟨rfl, not_pqEvAt_of_append (e := (⟨size⟩ : DY.Random.ExecEntryT)) rfl hT,
    append_length_rk tr _⟩

theorem TracefulFK.genRand (size : Nat) :
    TracefulFK T k (fun b m => ∃ L, k ≤ L ∧ m = L + 1 ∧ b = randTerm L size ∧ ¬ PQEvAt T L)
      (DY.Random.genRand size) :=
  fun n hn => (TracefulRK.genRand (n := n) size).mono fun _ _ h => ⟨n, hn, h.2.2, h.1, h.2.1⟩

theorem TracefulFK.sendMessage (msg : DY.Bytes) :
    TracefulFK T k (fun _ _ => True) (Network.sendMessage msg) := by
  unfold TracefulFK TracefulRK
  intro _ _ _ _ _ htr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  exact ⟨traceOkRK_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulFK.logEvent (ev : TREvent) :
    TracefulFK T k (fun _ _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulFK TracefulRK
  intro _ _ _ _ _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceOkRK_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulFK.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulFK T k (fun _ _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulFK TracefulRK
  intro _ _ _ _ _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceOkRK_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulRK.logEventPQ {n : Nat} (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hkn : PQEventKnown T ev) :
    TracefulRK T n (fun _ m => PQEvAt T n ∧ LoggedPQEv T ev ∧ m = n + 1)
      (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulRK
  intro tr hn hT htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1] at hT ⊢
  refine ⟨traceOkRK_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), ?_⟩ htr,
    fun _ _ => ?_⟩
  · intro e h
    rw [proj_inj_ik] at h
    injection h with h
    subst h
    exact hkn
  · subst hn
    have hat := at?_of_le hT (at?_append_self tr ({ ev := ev } : IkPQEvEntry))
    exact ⟨⟨_, hat⟩, ⟨tr.length, { ev := ev }, hat, rfl⟩, append_length_rk tr _⟩

theorem TracefulFK.logEventPQ (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hkn : PQEventKnown T ev) :
    TracefulFK T k (fun _ _ => LoggedPQEv T ev) (DY.ProtocolEvent.logEvent ev) :=
  fun n _ => (TracefulRK.logEventPQ (n := n) ev hkn).mono fun _ _ h => h.2.1

theorem TracefulRK.logIdentity_bind_send {α : Type} {n : Nat} {Q : α → Nat → Prop}
    (p : Participant) (ikPk vkPk : DY.Bytes) (rest : Traceful α)
    (hrest : PQEvAt T n → TracefulFK T (n + 2) Q rest) :
    TracefulRK T n Q
      (DY.ProtocolEvent.logEvent
        (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered p ikPk vkPk true) >>= fun _ =>
        Network.sendMessage ikPk >>= fun _ => rest) := by
  intro tr hn hT htr
  let ev := DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered p ikPk vkPk true
  let tr₁ := tr.append ({ ev := ev } : IkPQEvEntry)
  let tr₂ := tr₁.append ({ msg := ikPk } : Network.ExecEntryT)
  have hl1 : ((DY.ProtocolEvent.logEvent ev).run tr).1 = some () := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  have hl2 : ((DY.ProtocolEvent.logEvent ev).run tr).2.val = tr₁ := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  have hs1 : ((Network.sendMessage ikPk).run tr₁).1 = some tr₁.length := by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  have hs2 : ((Network.sendMessage ikPk).run tr₁).2.val = tr₂ := by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]; rfl
  have hrun_snd :
      (((DY.ProtocolEvent.logEvent ev >>= fun _ =>
        Network.sendMessage ikPk >>= fun _ => rest).run tr).2.val) =
        (rest.run tr₂).2.val := by
    rw [run_bind_snd_rkk, hl1, hl2]; dsimp only; rw [run_bind_snd_rkk, hs1, hs2]
  have hrun_fst :
      (((DY.ProtocolEvent.logEvent ev >>= fun _ =>
        Network.sendMessage ikPk >>= fun _ => rest).run tr).1) =
        (rest.run tr₂).1 := by
    rw [run_bind_fst_rkk, hl1, hl2]; dsimp only; rw [run_bind_fst_rkk, hs1, hs2]
  rw [hrun_snd] at hT ⊢; rw [hrun_fst]
  have htr₂_le : tr₂ ≤ T := DY.Trace.le_trans _ _ _ (rest.run tr₂).2.property hT
  have htr₁_le : tr₁ ≤ T :=
    DY.Trace.le_trans _ _ _ (DY.Trace.append_le tr₁ ({ msg := ikPk } : Network.ExecEntryT)) htr₂_le
  have hik_kn : ikPk.AttackerKnows T :=
    DY.Bytes.AttackerKnows_le ikPk tr₂ T htr₂_le
      (attackerKnows_of_at?_network (at?_append_self tr₁ ({ msg := ikPk } : Network.ExecEntryT)))
  have hkn : PQEventKnown T ev := fun _ _ _ _ heq => by
    injection heq with _ hik _ _; subst hik; exact hik_kn
  have htr₁_ok : TraceOkRK T tr₁ :=
    traceOkRK_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun e h => by
      rw [proj_inj_ik] at h; injection h with h; subst h; exact hkn⟩ htr
  have htr₂_ok : TraceOkRK T tr₂ :=
    traceOkRK_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
      fun _ h => (by cases h)⟩ htr₁_ok
  have hpq : PQEvAt T n := by
    subst hn; exact ⟨_, at?_of_le htr₁_le (at?_append_self tr ({ ev := ev } : IkPQEvEntry))⟩
  have hlen₂ : tr₂.length = n + 2 := by
    dsimp [tr₂, tr₁]; rw [append_length_rk, append_length_rk, hn]
  exact hrest hpq (n + 2) (Nat.le_refl _) tr₂ hlen₂ hT htr₂_ok

theorem TracefulFK.storeLocalState (p : Participant) {st : TRState}
    (hst : SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) k st) :
    TracefulFK T k (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulFK TracefulRK
  intro n hn tr hlen _ htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceOkRK_append ⟨?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩
  intro e h; rw [proj_inj_ik] at h; injection h with h; subst h; exact hst.mono_idx (by omega)

theorem TracefulFK.storeLocalStatePQ (p : Participant) {st : DY.Libsignal.PQXDH.PQXDHState}
    (hst : PQSkAt T k st) :
    TracefulFK T k (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulFK TracefulRK
  intro n hn tr hlen _ htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceOkRK_append ⟨fun _ h => (by cases h), ?_, fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩
  intro e h; rw [proj_inj_ik] at h; injection h with h; subst h; exact hst.mono (by omega)

end Steps

/-! ## Double Ratchet Key Schedule -/

section DR

variable {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop}

theorem spineRkK_recvChainFor {j : Nat} {st : TRState} {pk : DY.Bytes} {c : RecvChain} {b : Bool}
    (hst : SpStateRkK K B j st) (hpk : K (DY.X25519.normalizeX25519Key pk))
    (hrc : recvChainFor st.toDRState pk = some (c, b)) :
    SpineRkK K B false c.chainKey := by
  unfold recvChainFor at hrc
  rcases hfind : findRecvChain st.toDRState.recv pk with _ | c₀
  · rw [hfind] at hrc; dsimp only at hrc; split at hrc
    · cases hrc
    · injection hrc with hrc; rcases Prod.mk.inj hrc with ⟨rfl, _⟩
      obtain ⟨t, pk₀', _, hdhs, htop⟩ := hst.dhs
      have hh : RkHole true st.rk (dh (DY.X25519.normalizeX25519Key pk) st.dhs) := by
        rw [hdhs]; exact rkHole_true_intro htop
      have hdhk : DhHoleK K (dh (DY.X25519.normalizeX25519Key pk) st.dhs) := by
        rw [hdhs]; exact ⟨DY.X25519.normalizeX25519Key pk, t, rfl, hpk⟩
      exact SpineRkK.rkStep2 hst.rk hh hdhk
  · rw [hfind] at hrc; injection hrc with hrc; rcases Prod.mk.inj hrc with ⟨rfl, _⟩
    unfold findRecvChain at hfind; exact hst.recv _ (List.mem_of_find?_eq_some hfind)

theorem spineRkK_consumeMessageKey {b : Bool} {c c' : RecvChain} {counter : UInt32}
    {seed : DY.Bytes} (hc : SpineRkK K B b c.chainKey)
    (hcm : consumeMessageKey c counter = some (seed, c')) :
    SpineRkK K B b seed ∧ SpineRkK K B b c'.chainKey := by
  unfold consumeMessageKey at hcm
  split at hcm
  · cases hcm
  · split at hcm
    · cases hcm
    · split at hcm
      · cases hcm
      · injection hcm with hcm; rcases Prod.mk.inj hcm with ⟨rfl, rfl⟩
        have hck := spineRkK_chainKeyAt hc (counter.toNat - c.index.toNat)
        exact ⟨.ckStep2 hck, .ckStep1 hck⟩

theorem spStateRkK_setRecv {j : Nat} {st : TRState} {c' : RecvChain} (hst : SpStateRkK K B j st)
    (hc' : SpineRkK K B false c'.chainKey) (spqr : DY.Bytes) :
    SpStateRkK K B j { st with recv := setRecvChain st.recv c', spqr := spqr } := by
  refine ⟨hst.rk, hst.cks, fun c hc => ?_, hst.dhs⟩
  have hc2 : c ∈ setRecvChain st.recv c' := hc; unfold setRecvChain at hc2
  obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc2
  split at heq <;> subst heq
  · exact hc'
  · exact hst.recv c₀ hc₀

theorem spStateRkK_send {j : Nat} {st : TRState} (hst : SpStateRkK K B j st) (ns : UInt32)
    (spqr : DY.Bytes) :
    SpStateRkK K B j { st with cks := (kdfCk st.cks).1, ns := ns, spqr := spqr } :=
  ⟨hst.rk, .ckStep1 hst.cks, hst.recv, hst.dhs⟩

theorem spStateRkK_spqr {j : Nat} {st : TRState} (hst : SpStateRkK K B j st) (spqr : DY.Bytes) :
    SpStateRkK K B j { st with spqr := spqr } :=
  ⟨hst.rk, hst.cks, hst.recv, hst.dhs⟩

theorem spineRkK_of_recvSeed {j : Nat} {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes}
    (hst : SpStateRkK K B j st) (hpk : K (DY.X25519.normalizeX25519Key msg.ratchetKey))
    (hseed : recvSeed st msg = some seed) : SpineRkK K B false seed := by
  unfold recvSeed at hseed; split at hseed
  · rcases hrc : recvChainFor st.toDRState msg.ratchetKey with _ | ⟨c, b⟩
    · rw [hrc] at hseed; cases hseed
    · rw [hrc] at hseed; dsimp only at hseed
      rcases hcm : consumeMessageKey c msg.counter with _ | ⟨s, c'⟩
      · rw [hcm] at hseed; cases hseed
      · rw [hcm] at hseed; injection hseed with hseed; subst hseed
        exact (spineRkK_consumeMessageKey (spineRkK_recvChainFor hst hpk hrc) hcm).1
  · cases hseed

variable {T : ExecTrace}

theorem tracefulFK_dhRatchetStep {k : Nat} {st : TRState} {pk : DY.Bytes}
    (hst : SpStateRkK K B k st) (hpk : K (DY.X25519.normalizeX25519Key pk)) :
    TracefulFK T k (fun (p : TRState × RecvChain) m => SpStateRkK K B m p.1 ∧
      SpineRkK K B false p.2.chainKey) (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ => ?_
  refine TracefulFK.bindD (TracefulFK.genRand 32) fun dhs' m _ hg => ?_
  obtain ⟨L, hkL, hm, hdhs', _⟩ := hg
  obtain ⟨t, pk₀', htk, hdhs, htop⟩ := hst.dhs
  have hh1 : RkHole true st.rk (dh (DY.X25519.normalizeX25519Key pk) st.dhs) := by
    rw [hdhs]; exact rkHole_true_intro htop
  have hdhk1 : DhHoleK K (dh (DY.X25519.normalizeX25519Key pk) st.dhs) := by
    rw [hdhs]; exact ⟨DY.X25519.normalizeX25519Key pk, t, rfl, hpk⟩
  have hrk1 : SpineRkK K B false (createChain st.rk pk st.dhs).1 :=
    SpineRkK.rkStep1 hst.rk hh1 hdhk1
  have hckr : SpineRkK K B false (createChain st.rk pk st.dhs).2 :=
    SpineRkK.rkStep2 hst.rk hh1 hdhk1
  have htop1 : TopDhSecret (createChain st.rk pk st.dhs).1 (DY.X25519.normalizeX25519Key pk) t := by
    rw [hdhs]; exact topDhSecret_kdfRk
  have hh2 : RkHole false (createChain st.rk pk st.dhs).1 (dh (DY.X25519.normalizeX25519Key pk) dhs') := by
    rw [hdhs']; exact rkHole_false_intro htop1 (by omega)
  have hdhk2 : DhHoleK K (dh (DY.X25519.normalizeX25519Key pk) dhs') := by
    rw [hdhs']; exact ⟨DY.X25519.normalizeX25519Key pk, L, rfl, hpk⟩
  have htop2 : TopDhSecret (createChain (createChain st.rk pk st.dhs).1 pk dhs').1
      (DY.X25519.normalizeX25519Key pk) L := by
    rw [hdhs']; exact topDhSecret_kdfRk
  refine TracefulFK.pure fun n hn => ⟨⟨SpineRkK.rkStep1 hrk1 hh2 hdhk2,
    SpineRkK.rkStep2 hrk1 hh2 hdhk2, fun c' hc' => ?_, ⟨L, _, by omega, hdhs', htop2⟩⟩, hckr⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst.recv c' hmem
  · rcases List.mem_singleton.mp hmem with rfl; exact hckr

theorem tracefulFK_ensureReceiverChain {k : Nat} {st : TRState} {pk : DY.Bytes}
    (hst : SpStateRkK K B k st) (hpk : K (DY.X25519.normalizeX25519Key pk)) :
    TracefulFK T k
      (fun (p : TRState × RecvChain × Bool) m => SpStateRkK K B m p.1 ∧
        SpineRkK K B false p.2.1.chainKey)
      (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · next c hr => exact TracefulFK.pure fun _ hn => ⟨hst.mono_idx hn, spineRkK_recvChainFor hst hpk hr⟩
  · exact TracefulFK.bindD (tracefulFK_dhRatchetStep hst hpk) fun ⟨_, _⟩ _ _ h =>
      TracefulFK.pure fun _ hn => ⟨h.1.mono_idx hn, h.2⟩
  · exact TracefulFK.failure

end DR

/-! ## Triple Ratchet Transitions -/

section TR

variable {T : ExecTrace}

theorem tracefulFK_logMessageKeyAndStore {k : Nat} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) k st) :
    TracefulFK T k (fun _ _ => True)
      (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => TracefulFK.storeLocalState me hst

theorem tracefulFK_logSkippedKeys {k : Nat} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (cnt : Nat) :
    TracefulFK T k (fun _ _ => True) (logSkippedKeys s pk rIdx src ck n cnt) := by
  induction cnt generalizing ck n with
  | zero => unfold logSkippedKeys; exact TracefulFK.pure fun _ _ => trivial
  | succ cnt ih =>
    unfold logSkippedKeys
    exact TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => ih (kdfCk ck).1 (n + 1)

theorem tracefulFK_verifyMacAndDecrypt {k : Nat} (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    TracefulFK T k (fun _ _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ => ?_
  unfold TracefulFK TracefulRK
  intro _ _ _ _ _ htr
  dsimp [liftM, monadLift, MonadLift.monadLift]
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulFK_messageEncrypt {k : Nat} (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulFK T k (fun _ _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  refine TracefulFK.bindD (TracefulFK.getLocalState me stateIdx) fun st m _ hst =>
    TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.genRand 32) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.genRand coinsLen) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.receiveMessage pqIdx) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
    TracefulFK.bind (tracefulFK_logMessageKeyAndStore me _ .sender _ _ _ _ _
      (spStateRkK_send hst _ _)) fun _ _ _ _ => TracefulFK.sendMessage _

theorem tracefulFK_messageEncryptAbort {k : Nat} (me : Participant) (stateIdx : Nat) :
    TracefulFK T k (fun _ _ => True) (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact TracefulFK.bind (TracefulFK.getLocalState me stateIdx) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.genRand 32) fun _ _ _ _ => TracefulFK.failure

theorem tracefulFK_messageDecrypt {k : Nat} (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulFK T k (fun _ _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulFK.bindD (TracefulFK.getLocalState me stateIdx) fun st₀ m₀ _ hst₀ =>
    TracefulFK.bind (tracefulFK_receiveSignalMsg msgIdx) fun msg _ _ hrk_kn =>
    TracefulFK.bindD (tracefulFK_ensureReceiverChain (hst₀.mono_idx (Nat.le_refl m₀))
      (attackerKnows_x25519Key hrk_kn))
      fun ⟨st, c, ratcheted⟩ m₁ _ hst => ?_
  dsimp only; split
  · next seed c' hcm =>
    have hc' := (spineRkK_consumeMessageKey (c := c) hst.2 hcm).2
    split
    · next spqr' key _ =>
      refine TracefulFK.bind (TracefulFK.sendMessage key) fun _ _ _ _ =>
        TracefulFK.bind (TracefulFK.receiveMessage pqIdx) fun pqSalt _ _ _ =>
        TracefulFK.bind (tracefulFK_verifyMacAndDecrypt st msg pqSalt seed) fun mm _ _ _ => ?_
      have hrest :
          TracefulFK T m₁ (fun _ _ => True)
            (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                  (msg.counter.toNat - c.index.toNat)
                DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter mm)
                logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt
                  msg.counter c.rIdx stateIdx
                  { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulFK.bind (tracefulFK_logSkippedKeys _ _ _ _ _ _ _) fun _ _ _ _ =>
          TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
            tracefulFK_logMessageKeyAndStore me _ .receiver _ _ _ _ _
              (spStateRkK_setRecv hst.1 hc' spqr')
      split
      · exact TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
          TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => hrest
      · exact hrest
    · exact TracefulFK.failure
  · exact TracefulFK.failure

theorem tracefulFK_messageDecryptSkipped {k : Nat} (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulFK T k (fun _ _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulFK.bindD (TracefulFK.getLocalState me stateIdx) fun st _ _ hst =>
    TracefulFK.bind (tracefulFK_receiveSignalMsg msgIdx) fun msg _ _ _ =>
    TracefulFK.bind (TracefulFK.getEntry_any skippedKeyEventIdx) fun _ _ _ _ => ?_
  split
  · refine TracefulFK.bind (TracefulFK.guard _) fun _ _ _ _ =>
      TracefulFK.bind (tracefulFK_guardTrace _) fun _ _ _ _ => ?_
    split
    · next spqr' key _ =>
      exact TracefulFK.bind (TracefulFK.sendMessage key) fun _ _ _ _ =>
        TracefulFK.bind (TracefulFK.receiveMessage pqIdx) fun pqSalt _ _ _ =>
        TracefulFK.bind (tracefulFK_verifyMacAndDecrypt st msg pqSalt _) fun _ _ _ _ =>
        TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
        TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
        tracefulFK_logMessageKeyAndStore me _ .receiver _ _ _ _ _ (spStateRkK_spqr hst spqr')
    · exact TracefulFK.failure
  · exact TracefulFK.failure

theorem tracefulFK_exposeKey {k : Nat} (me : Participant) (stateIdx : Nat) (kc : KeyComponent) :
    TracefulFK T k (fun _ _ => True) (exposeKey me stateIdx kc) := by
  unfold exposeKey
  refine TracefulFK.bind (TracefulFK.getLocalState me stateIdx) fun _ _ _ _ => ?_
  cases kc with
  | rk => exact TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => TracefulFK.sendMessage _
  | dhs => exact TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => TracefulFK.sendMessage _
  | cks => exact TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => TracefulFK.sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => TracefulFK.sendMessage _
    · exact TracefulFK.failure

theorem tracefulFK_exposeSpqr {k : Nat} (me : Participant) (stateIdx : Nat) :
    TracefulFK T k (fun _ _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact TracefulFK.bind (TracefulFK.getLocalState me stateIdx) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => TracefulFK.sendMessage _

theorem tracefulFK_exposeSkipped {k : Nat} (skippedKeyEventIdx : Nat) :
    TracefulFK T k (fun _ _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulFK.bind (TracefulFK.getEntry_any skippedKeyEventIdx) fun _ _ _ _ => ?_
  split
  · exact TracefulFK.bind (tracefulFK_guardTrace _) fun _ _ _ _ =>
      TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => TracefulFK.sendMessage _
  · exact TracefulFK.failure

end TR

/-! ## PQXDH Key Management -/

section PQ

variable {T : ExecTrace} {k : Nat}

theorem tracefulFK_compromiseIK (p : Participant) (j : Nat) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact TracefulFK.bind (TracefulFK.getKey p j _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ _ =>
      TracefulFK.sendMessage _

theorem tracefulFK_compromiseSPK (p : Participant) (j : Nat) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact TracefulFK.bind (TracefulFK.getKey p j _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ _ =>
      TracefulFK.sendMessage _

theorem tracefulFK_compromisePQSPK (p : Participant) (j : Nat) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact TracefulFK.bind (TracefulFK.getKey p j _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ _ =>
      TracefulFK.sendMessage _

theorem tracefulFK_compromiseOPK (p : Participant) (j : Nat) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact TracefulFK.bind (TracefulFK.getKey p j _) fun _ _ _ _ =>
    TracefulFK.bind (tracefulFK_guardOnTrace _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ _ =>
      TracefulFK.sendMessage _

theorem tracefulFK_registerIdentity (p : Participant) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine TracefulFK.bind (tracefulFK_guardOnTrace _) fun _ _ _ _ => ?_
  refine TracefulFK.bindE (TracefulFK.genRand 32) fun ik m _ hg => ?_
  obtain ⟨L, _, rfl, rfl, _⟩ := hg
  refine TracefulRK.logIdentity_bind_send p _ _ _ fun hev => ?_
  refine TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ =>
    TracefulFK.storeLocalStatePQ p (st := { kind := .identity, sk := randTerm L 32 }) ?_
  exact ⟨L, by omega, rfl, hev⟩

theorem tracefulFK_genSignedPrekey (b : Participant) (j : Nat) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine TracefulFK.bind (TracefulFK.getKey b j _) fun _ _ _ _ => ?_
  refine TracefulFK.bindE (TracefulFK.genRand 32) fun spk m _ hg => ?_
  obtain ⟨L, _, rfl, rfl, _⟩ := hg
  refine TracefulRK.bind (TracefulRK.genRand 64) fun _ m₁ _ hn => ?_
  obtain ⟨_, hne, rfl⟩ := hn
  refine TracefulRK.bindF (TracefulRK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ m₂ _ hl => ?_
  obtain ⟨hev, _, rfl⟩ := hl
  refine TracefulFK.bind
    (TracefulFK.storeLocalStatePQ b (st := { kind := .signedPrekey, sk := randTerm L 32 }) ?_)
    fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ => TracefulFK.pure fun _ _ => trivial
  exact ⟨L, by omega, rfl, hne, hev⟩

theorem tracefulFK_genPQPrekey (b : Participant) (j : Nat) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact TracefulFK.bind (TracefulFK.getKey b j _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.genRand 64) fun pqsk _ _ _ =>
    TracefulFK.bind (TracefulFK.genRand 64) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ _ =>
    TracefulFK.bind
      (TracefulFK.storeLocalStatePQ b (st := { kind := .pqPrekey, sk := pqsk }) trivial)
      fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ => TracefulFK.pure fun _ _ => trivial

theorem tracefulFK_genOneTimePrekey (b : Participant) :
    TracefulFK T k (fun _ _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine TracefulFK.bindE (TracefulFK.genRand 32) fun opk m _ hg => ?_
  obtain ⟨L, _, rfl, rfl, _⟩ := hg
  refine TracefulRK.bindF (TracefulRK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ m₁ _ hl => ?_
  obtain ⟨hev, _, rfl⟩ := hl
  refine TracefulFK.bind
    (TracefulFK.storeLocalStatePQ b (st := { kind := .oneTimePrekey, sk := randTerm L 32 }) ?_)
    fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ => TracefulFK.pure fun _ _ => trivial
  exact ⟨L, by omega, rfl, hev⟩

theorem tracefulFK_setupAct (a b : Participant) (withOpk : Bool) :
    TracefulFK T k (fun _ _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  apply TracefulFK.bind (Q₁ := fun _ _ => True) (tracefulFK_registerIdentity a); intro _ _ _ _
  apply TracefulFK.bind (Q₁ := fun _ _ => True) (tracefulFK_registerIdentity b); intro hB _ _ _
  apply TracefulFK.bind (Q₁ := fun _ _ => True) (tracefulFK_genSignedPrekey b hB); intro _ _ _ _
  apply TracefulFK.bind (Q₁ := fun _ _ => True) (tracefulFK_genPQPrekey b hB); intro _ _ _ _
  split
  · apply TracefulFK.bind (Q₁ := fun _ _ => True) (tracefulFK_genOneTimePrekey b); intro _ _ _ _
    exact TracefulFK.pure fun _ _ => trivial
  · exact TracefulFK.pure fun _ _ => trivial

end PQ

/-! ## Handshakes -/

def AliceHsOkK (T : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (m : Nat) : Prop :=
  ∃ (tᵢ tₑ : Nat) (pk ent ikB : DY.Bytes) (opk' : Option DY.Bytes),
    tᵢ < tₑ ∧ IkAt T tᵢ ∧ ¬ PQEvAt T (tₑ + 1) ∧ m = tₑ + 2 ∧
    o.spk.AttackerKnows T ∧ ikB.AttackerKnows T ∧ (∀ v, opk' = some v → v.AttackerKnows T) ∧
    o.ct = (DY.PQKem.kemEncap pk ent).1 ∧
    o.keys = pqxdhKdf (pqxdhIkm (agree o.spk (randTerm tᵢ 32)) (agree ikB (randTerm tₑ 32))
      (agree o.spk (randTerm tₑ 32)) (opk'.map (agree · (randTerm tₑ 32)))
      (DY.PQKem.kemEncap pk ent).2)

theorem tracefulFK_aliceHandshake {T : ExecTrace} {k : Nat} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulFK T k (fun (o : DY.Libsignal.PQXDH.AliceHandshakeOut) m => AliceHsOkK T o m)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulFK.bindD (TracefulFK.getKey a idStateIdx _); intro ikA mₐ _ hikA
  simp only [PQSkAt] at hikA
  obtain ⟨tᵢ, htᵢ, rfl, hik⟩ := hikA
  apply TracefulFK.bind (TracefulFK.lookupIdentity b regIdxB); intro ikv _ _ hikB
  rcases ikv with ⟨ikB, vkB⟩
  dsimp only at hikB ⊢
  apply TracefulFK.bind (TracefulFK.receiveMessage h.spk); intro spk _ _ hspk
  apply TracefulFK.bind (TracefulFK.receiveMessage h.spkSig); intro _ _ _ _
  apply TracefulFK.bind (TracefulFK.receiveMessage h.pqpk); intro pqpk _ _ _
  apply TracefulFK.bind (TracefulFK.receiveMessage h.pqpkSig); intro _ _ _ _
  apply TracefulFK.bind (TracefulFK.guard _); intro _ _ _ _
  apply TracefulFK.bind (TracefulFK.guard _); intro _ _ _ _
  split
  case' h_1 i _ =>
    apply TracefulFK.bind (TracefulFK.receiveMessage i); intro o _ _ ho
    apply TracefulFK.bind (TracefulFK.pure
      (Q := fun (x : Option DY.Bytes) _ => ∀ v, x = some v → v.AttackerKnows T)
      fun _ _ v hv => by cases hv; exact ho)
  case' h_2 =>
    apply TracefulFK.bind (TracefulFK.pure
      (Q := fun (x : Option DY.Bytes) _ => ∀ v, x = some v → v.AttackerKnows T)
      fun _ _ v hv => by cases hv)
  all_goals
    intro opk _ _ hopk
    apply TracefulFK.bindE (TracefulFK.genRand 32); intro ek m _ hg
    obtain ⟨tₑ, hkt, rfl, rfl, _⟩ := hg
    apply TracefulRK.bind (TracefulRK.guardP _); intro _ m₁ _ hg₁
    obtain ⟨_, rfl⟩ := hg₁
    apply TracefulRK.bind (TracefulRK.guardP _); intro _ m₂ _ hg₂
    obtain ⟨_, rfl⟩ := hg₂
    apply TracefulRK.bind (TracefulRK.genRand 32); intro ent m₃ _ hr
    obtain ⟨rfl, hne1, rfl⟩ := hr
    exact TracefulRK.pure ⟨tᵢ, tₑ, pqpk, randTerm (tₑ + 1) 32, ikB, opk, by omega, hik, hne1, rfl,
      hspk, hikB, hopk, rfl, rfl⟩

def BobHsOkK (T : ExecTrace) (o : DY.Libsignal.PQXDH.BobHandshakeOut) (m : Nat) : Prop :=
  ∃ (ikm : DY.Bytes) (t : Nat) (pk' : DY.Bytes),
    CtKeysIkmR T true o.ct o.keys ikm ∧ IkmHolesK (·.AttackerKnows T) ikm ∧
    t < m ∧ o.spkSk = randTerm t 32 ∧ TopDhSecret o.keys.rk pk' t

theorem bobHsOkK_of_bobAgreement {T : ExecTrace} {tᵢ tₛ : Nat} {pqsk ikA ek ct : DY.Bytes}
    {opk : Option DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hik : IkAt T tᵢ) (hspk : SpkAt T tₛ)
    (hopk : ∀ o, opk = some o → ∃ t, o = randTerm t 32 ∧ OpkAt T t)
    (hikA : ikA.AttackerKnows T) (hek : ek.AttackerKnows T)
    (h : DY.Libsignal.PQXDH.bobAgreement (randTerm tᵢ 32) (randTerm tₛ 32) pqsk opk ikA ek ct =
      some keys) :
    ∃ ikm, CtKeysIkmR T true ct keys ikm ∧ IkmHolesK (·.AttackerKnows T) ikm ∧
      TopDhSecret keys.rk (DY.X25519.normalizeX25519Key ikA) tₛ := by
  dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at h
  injection h with hkeys
  subst hkeys
  refine ⟨_, ⟨_, _, _, _, _, ?_, rfl, rfl,
    ⟨DY.X25519.normalizeX25519Key ikA, tₛ, rfl, hspk⟩,
    ⟨DY.X25519.normalizeX25519Key ek, tᵢ, rfl, hik⟩,
    ⟨DY.X25519.normalizeX25519Key ek, tₛ, rfl, hspk⟩, fun v hv => ?_⟩,
    ⟨_, _, _, _, _, rfl, dhHoleK_agree tₛ hikA, dhHoleK_agree tᵢ hek,
      dhHoleK_agree tₛ hek, fun v hv => ?_⟩,
    topDhSecret_pqxdh⟩
  · rcases hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct) with _ | s
    · exact .inr ⟨pqsk, ct, rfl⟩
    · obtain ⟨e, _, rfl⟩ := Symbolic.Swarm.CREF.TR.kemDecap_eq_some_iff pqsk ct s hdec
      exact .inl ⟨_, e, rfl⟩
  · rcases opk with _ | o
    · cases hv
    · injection hv with hv
      subst hv
      obtain ⟨t, rfl, ho⟩ := hopk o rfl
      exact ⟨DY.X25519.normalizeX25519Key ek, t, rfl, ho⟩
  · rcases opk with _ | o
    · cases hv
    · injection hv with hv
      subst hv
      obtain ⟨t, rfl, _⟩ := hopk o rfl
      exact dhHoleK_agree t hek

theorem tracefulFK_bobHandshake {T : ExecTrace} {k : Nat} (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulFK T k (fun (o : DY.Libsignal.PQXDH.BobHandshakeOut) m => BobHsOkK T o m)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TracefulFK.bind (TracefulFK.getKey b h.ik _); intro ikB mᵢ _ hikB
  simp only [PQSkAt] at hikB
  obtain ⟨tᵢ, _, rfl, hik⟩ := hikB
  apply TracefulFK.bindD (TracefulFK.getKey b h.spk _); intro spkSk mₛ _ hspkSk
  simp only [PQSkAt] at hspkSk
  obtain ⟨tₛ, htₛ, rfl, hspk⟩ := hspkSk
  apply TracefulFK.bind (TracefulFK.getKey b h.pqspk _); intro pqsk _ _ _
  split
  case' h_1 i _ =>
    apply TracefulFK.bind (TracefulFK.getKey b i _); intro o _ _ ho
    apply TracefulFK.bind (TracefulFK.pure
      (Q := fun (x : Option DY.Bytes) _ => ∀ d, x = some d → ∃ t, d = randTerm t 32 ∧ OpkAt T t)
      fun _ _ d hd => by
        cases hd
        obtain ⟨t, _, hsk, hr⟩ := ho
        exact ⟨t, hsk, hr⟩)
  case' h_2 =>
    apply TracefulFK.bind (TracefulFK.pure
      (Q := fun (x : Option DY.Bytes) _ => ∀ d, x = some d → ∃ t, d = randTerm t 32 ∧ OpkAt T t)
      fun _ _ d hd => by cases hd)
  all_goals
    intro opkSk _ _ hopk
    apply TracefulFK.bind (TracefulFK.lookupIdentity a regIdxA); intro ikv _ _ hikA
    rcases ikv with ⟨ikA, vkA⟩
    dsimp only at hikA ⊢
    apply TracefulFK.bind (TracefulFK.receiveMessage ekIdx); intro ek _ _ hek
    apply TracefulFK.bind (TracefulFK.receiveMessage ctIdx); intro ct _ _ _
    apply TracefulFK.bind (TracefulFK.guard _); intro _ _ _ _
    split
    · next keys hkeys =>
      obtain ⟨ikm, hck, hholes, htop⟩ := bobHsOkK_of_bobAgreement hik hspk hopk hikA hek hkeys
      exact TracefulFK.pure fun n hn => ⟨ikm, tₛ, _, hck, hholes, by omega, rfl, htop⟩
    · exact TracefulFK.failure

/-! ## Session Starts -/

theorem spineRkK_of_ctKeys {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop} {c : Bool}
    {ikm : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} (hkeys : keys = pqxdhKdf ikm)
    (hB : B c ikm) (hI : IkmHolesK K ikm) :
    SpineRkK K B c keys.rk ∧ SpineRkK K B c keys.ck := by
  subst hkeys
  exact ⟨.hsRk hB hI, .hsCk hB hI⟩

theorem tracefulFK_aliceStart {T : ExecTrace} {k : Nat} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulFK T k (fun _ _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulFK.bindE (tracefulFK_aliceHandshake a b idStateIdx regIdxB h) fun o m _ ho => ?_
  obtain ⟨tᵢ, tₑ, pk, ent, ikB, opk', hlt, hik, hne1, rfl, hspk_kn, hikB_kn, hopk_kn,
    hct, hkeys⟩ := ho
  refine TracefulRK.bindF (TracefulRK.genRand 32) fun dhsA m₁ _ hg => ?_
  obtain ⟨rfl, hne2, rfl⟩ := hg
  rcases hcc : createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32) with ⟨rkA, cksA⟩
  dsimp only
  refine TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.sendMessage _) fun _ _ _ _ =>
    TracefulFK.bind tracefulFK_traceLength fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ hlog =>
    TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
    TracefulFK.bind (TracefulFK.logEventC _) fun _ _ _ _ =>
    TracefulFK.storeLocalState a ?_
  have hikm : CtKeysIkmR T false o.ct o.keys
      (pqxdhIkm (agree o.spk (randTerm tᵢ 32)) (agree ikB (randTerm tₑ 32))
        (agree o.spk (randTerm tₑ 32)) (opk'.map (agree · (randTerm tₑ 32)))
        (DY.PQKem.kemEncap pk ent).2) := by
    refine ⟨pk, ent, _, _, _, _, hct, rfl, hkeys, ?_⟩
    refine ⟨⟨DY.X25519.normalizeX25519Key o.spk, tᵢ, rfl, hik⟩,
      ⟨DY.X25519.normalizeX25519Key ikB, tₑ, rfl, hne1, hne2⟩,
      ⟨DY.X25519.normalizeX25519Key o.spk, tₑ, rfl, hne1, hne2⟩, fun v hv => ?_⟩
    rcases opk' with _ | o'
    · cases hv
    · injection hv with hv
      subst hv
      exact ⟨DY.X25519.normalizeX25519Key o', tₑ, rfl, hne1, hne2⟩
  have hB : LoggedIkmRk T false
      (pqxdhIkm (agree o.spk (randTerm tᵢ 32)) (agree ikB (randTerm tₑ 32))
        (agree o.spk (randTerm tₑ 32)) (opk'.map (agree · (randTerm tₑ 32)))
        (DY.PQKem.kemEncap pk ent).2) :=
    ⟨_, hlog, hikm⟩
  have hI : IkmHolesK (·.AttackerKnows T)
      (pqxdhIkm (agree o.spk (randTerm tᵢ 32)) (agree ikB (randTerm tₑ 32))
        (agree o.spk (randTerm tₑ 32)) (opk'.map (agree · (randTerm tₑ 32)))
        (DY.PQKem.kemEncap pk ent).2) := by
    refine ⟨_, _, _, _, _, rfl, dhHoleK_agree tᵢ hspk_kn, dhHoleK_agree tₑ hikB_kn,
      dhHoleK_agree tₑ hspk_kn, fun v hv => ?_⟩
    rcases opk' with _ | o'
    · cases hv
    · injection hv with hv
      subst hv
      exact dhHoleK_agree tₑ (hopk_kn o' rfl)
  obtain ⟨hrk0, hck0⟩ := spineRkK_of_ctKeys hkeys hB hI
  have htop0 : TopDhSecret o.keys.rk (DY.X25519.normalizeX25519Key o.spk) tᵢ := by
    rw [hkeys]; exact topDhSecret_pqxdh
  have hh : RkHole false o.keys.rk (dh (DY.X25519.normalizeX25519Key o.spk) (randTerm (tₑ + 2) 32)) :=
    rkHole_false_intro htop0 (by omega)
  have hdhk : DhHoleK (·.AttackerKnows T)
      (dh (DY.X25519.normalizeX25519Key o.spk) (randTerm (tₑ + 2) 32)) :=
    dhHoleK_dh_x25519Key (tₑ + 2) hspk_kn
  have hrkA : SpineRkK (·.AttackerKnows T) (LoggedIkmRk T) true rkA := by
    have h1 := SpineRkK.rkStep1 hrk0 hh hdhk
    have h2 : (createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32)).1 = rkA := by rw [hcc]
    rw [← h2]; exact h1
  have hcksA : SpineRkK (·.AttackerKnows T) (LoggedIkmRk T) true cksA := by
    have h1 := SpineRkK.rkStep2 hrk0 hh hdhk
    have h2 : (createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32)).2 = cksA := by rw [hcc]
    rw [← h2]; exact h1
  have htopA : TopDhSecret rkA (DY.X25519.normalizeX25519Key o.spk) (tₑ + 2) := by
    have h1 : TopDhSecret (createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32)).1
        (DY.X25519.normalizeX25519Key o.spk) (tₑ + 2) := topDhSecret_kdfRk
    rw [hcc] at h1; exact h1
  refine ⟨hrkA, hcksA, fun c hc => ?_, ⟨tₑ + 2, _, by omega, rfl, htopA⟩⟩
  rcases List.mem_singleton.mp hc with rfl
  exact hck0

theorem tracefulFK_bobStart {T : ExecTrace} {k : Nat} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulFK T k (fun _ _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulFK.bindD (tracefulFK_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o mₒ _ ho =>
    TracefulFK.bind (tracefulFK_receiveSignalMsg mh.msg) fun msg _ _ hrk_kn => ?_
  obtain ⟨ikm, t, pk', hck, hholes, ht, hspk, htop⟩ := ho
  have hkeys : o.keys = pqxdhKdf ikm := by
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hck
    exact hk
  obtain ⟨hrk0, hck0⟩ :=
    spineRkK_of_ctKeys (B := BobBase T o.ct o.keys) (c := true) hkeys ⟨rfl, hck⟩ hholes
  refine TracefulFK.bindD (tracefulFK_ensureReceiverChain (B := BobBase T o.ct o.keys)
    (SpStateRkK.mk hrk0 hck0 (fun _ h => (by simp at h)) ⟨t, pk', ht, hspk, htop⟩)
    (attackerKnows_x25519Key hrk_kn))
    fun x m₁ _ hst => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hst ⊢
  split
  · next seed c' hcm =>
    have hc' := (spineRkK_consumeMessageKey hst.2 hcm).2
    split
    · next spqr' key _ =>
      refine TracefulFK.bind (TracefulFK.sendMessage key) fun _ _ _ _ =>
        TracefulFK.bind (TracefulFK.receiveMessage pqIdx) fun pqSalt _ _ _ =>
        TracefulFK.bind (tracefulFK_verifyMacAndDecrypt st msg pqSalt seed) fun mm _ _ _ => ?_
      split
      all_goals first
        | refine TracefulFK.bind (tracefulFK_guardOnTrace _) fun _ _ _ _ =>
            TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ _ => ?_
        | skip
      all_goals refine TracefulFK.bind tracefulFK_traceLength fun _ _ _ _ =>
        TracefulFK.bind (TracefulFK.logEventPQ _ (by rintro _ _ _ _ ⟨⟩)) fun _ _ _ hlog => ?_
      all_goals
        have hfin : SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) m₁
            { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
          (spStateRkK_setRecv hst.1 hc' spqr').mono (fun _ h => h) fun c ss hss => by
            obtain ⟨rfl, hss⟩ := hss
            exact ⟨_, hlog, hss⟩
      all_goals split
      all_goals first
        | refine TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
            TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ => ?_
        | skip
      all_goals exact TracefulFK.bind (TracefulFK.logEventC _) fun _ _ _ _ =>
          TracefulFK.bind tracefulFK_traceLength fun _ _ _ _ =>
          TracefulFK.bind (tracefulFK_logSkippedKeys _ _ _ _ _ _ _) fun _ _ _ _ =>
          TracefulFK.bind (TracefulFK.logEvent _) fun _ _ _ _ =>
          tracefulFK_logMessageKeyAndStore b _ .receiver _ _ _ _ _ hfin
    · exact TracefulFK.failure
  · exact TracefulFK.failure

/-! ## Moves Induction and Exported Theorems -/

theorem tracefulFK_run_snd {T : ExecTrace} {α : Type} {Q : α → Nat → Prop} {x : Traceful α}
    (hx : TracefulFK T 0 Q x) {tr : ExecTrace}
    (hT : ((x >>= fun _ => Pure.pure ()).run tr).2.val ≤ T) (htr : TraceOkRK T tr) :
    TraceOkRK T ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulFK.bind hx (fun _ _ _ _ => TracefulFK.pure (Q := fun _ _ => True) fun _ _ => trivial)
    tr.length (Nat.zero_le _) tr rfl hT htr).1

theorem traceOkRK_move_next {T tr : ExecTrace} {m : Move} (hT : m.next tr ≤ T)
    (htr : TraceOkRK T tr) : TraceOkRK T (m.next tr) := by
  unfold Move.next Move.act at hT ⊢
  cases m with
  | setup a b withOpk =>
    exact (tracefulFK_setupAct (k := 0) a b withOpk tr.length (Nat.zero_le _) tr rfl hT htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulFK_run_snd (tracefulFK_aliceStart a b idStateIdx regIdxB h) hT htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulFK_run_snd (tracefulFK_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) hT htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulFK_run_snd (tracefulFK_messageEncrypt me stateIdx coinsLen pqIdx) hT htr
  | encryptAbort me stateIdx =>
    exact tracefulFK_run_snd (tracefulFK_messageEncryptAbort me stateIdx) hT htr
  | encryptFail me stateIdx coinsLen =>
    dsimp only at hT ⊢
    have h_assoc :
        ((do let n ← traceLength; let _ ← messageEncrypt me stateIdx coinsLen (n + 3); Pure.pure ()).run tr).2.val =
        (((do let n ← traceLength; messageEncrypt me stateIdx coinsLen (n + 3)) >>= fun _ => Pure.pure ()).run tr).2.val := by
      rw [run_bind_snd_rkk, run_bind_snd_rkk, run_bind_fst_rkk]
      rcases ht : (traceLength.run tr).1 with _ | n
      · dsimp only; rw [run_bind_snd_rkk, ht]
      · dsimp only; rw [run_bind_snd_rkk, run_bind_snd_rkk, ht]
    rw [h_assoc] at hT ⊢
    exact tracefulFK_run_snd
      (TracefulFK.bind tracefulFK_traceLength
        fun n _ _ _ => tracefulFK_messageEncrypt me stateIdx coinsLen (n + 3)) hT htr
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulFK_run_snd (tracefulFK_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx)
      hT htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulFK_run_snd
      (tracefulFK_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx)
      hT htr
  | reject _ =>
    dsimp only
    rw [Traceful.run_pure]
    exact htr
  | compromiseIK p stateIdx =>
    exact tracefulFK_run_snd (tracefulFK_compromiseIK p stateIdx) hT htr
  | compromiseSPK p stateIdx =>
    exact tracefulFK_run_snd (tracefulFK_compromiseSPK p stateIdx) hT htr
  | compromisePQSPK p stateIdx =>
    exact tracefulFK_run_snd (tracefulFK_compromisePQSPK p stateIdx) hT htr
  | compromiseOPK p stateIdx =>
    exact tracefulFK_run_snd (tracefulFK_compromiseOPK p stateIdx) hT htr
  | exposeKey me stateIdx kc =>
    exact tracefulFK_run_snd (tracefulFK_exposeKey me stateIdx kc) hT htr
  | exposeSpqr me stateIdx =>
    exact tracefulFK_run_snd (tracefulFK_exposeSpqr me stateIdx) hT htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulFK_run_snd (tracefulFK_exposeSkipped skippedKeyEventIdx) hT htr
  | attackerSend msg => exact tracefulFK_run_snd (TracefulFK.sendMessage msg) hT htr
  | brkDH =>
    exact (TracefulFK.logEventPQ (k := 0) .BrokenDH (fun _ _ _ _ h => by cases h) tr.length (Nat.zero_le _) tr rfl hT htr).1
  | brkKEM =>
    exact (TracefulFK.logEventPQ (k := 0) .BrokenKEM (fun _ _ _ _ h => by cases h) tr.length (Nat.zero_le _) tr rfl hT htr).1

theorem traceOkRK_runMoves {T : ExecTrace} :
    ∀ (L : List Move) (tr : ExecTrace), (runMoves L tr).1 ≤ T →
      TraceOkRK T tr → TraceOkRK T (runMoves L tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hT, htr => by
    have hT' : (runMoves ms (m.next tr)).1 ≤ T := hT
    have hle : m.next tr ≤ T :=
      DY.Trace.le_trans _ _ _ (Symbolic.Swarm.CREF.runMoves_le ms (m.next tr)) hT'
    exact traceOkRK_runMoves ms (m.next tr) hT' (traceOkRK_move_next hle htr)

/-- Every entry of the run's trace satisfies `SpEntryOkRK` relative to the run's own trace. -/
theorem traceOkRK_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    TraceOkRK (runTraceMoves r₀ ms) (runTraceMoves r₀ ms) :=
  traceOkRK_runMoves (r₀.setupMove :: ms) DY.Trace.nil (DY.Trace.le_refl _) (traceOkRK_nil _)

theorem spStateRkK_of_mem_availableStates {r₀ : ProtocolSetup} {T tr : ExecTrace} (htr : TraceOkRK T tr)
    {st : TRState} (hst : st ∈ availableStates r₀ tr) :
    SpStateRkK (·.AttackerKnows T) (LoggedIkmRk T) tr.length st := by
  unfold availableStates storedStates DY.ExecTrace.getLocalStateAt at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he
  obtain ⟨e, hat, rfl⟩ := he
  unfold DY.Trace.at? at hat
  split at hat
  · next hj => exact ((htr j hj).1 e hat).mono_idx (Nat.le_of_lt hj)
  · cases hat

/-- Every available state of a run satisfies the known-peer-key honest-spine invariant. -/
theorem spStateRkK_runTrace {r₀ : ProtocolSetup} {ms : List Move} {st : TRState}
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) :
    SpStateRkK (·.AttackerKnows (runTraceMoves r₀ ms)) (LoggedIkmRk (runTraceMoves r₀ ms))
      (runTraceMoves r₀ ms).length st :=
  spStateRkK_of_mem_availableStates (traceOkRK_runTrace r₀ ms) hst

/-- Every stored receiving chain key of an available state is a role-`false` `SpineRkK` term. -/
theorem spineRkK_recvChain_runTrace {r₀ : ProtocolSetup} {ms : List Move} {st : TRState}
    {c : RecvChain} (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) (hc : c ∈ st.recv) :
    SpineRkK (·.AttackerKnows (runTraceMoves r₀ ms)) (LoggedIkmRk (runTraceMoves r₀ ms)) false c.chainKey :=
  (spStateRkK_runTrace hst).recv c hc

/-- A receiving seed of an available state on a message with attacker-known `msg.ratchetKey` is a
role-`false` `SpineRkK` term. -/
theorem spineRkK_recvSeed_runTrace {r₀ : ProtocolSetup} {ms : List Move} {st : TRState}
    {msg : TRSignalMsg} {seed : DY.Bytes} (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hpk : msg.ratchetKey.AttackerKnows (runTraceMoves r₀ ms)) (hseed : recvSeed st msg = some seed) :
    SpineRkK (·.AttackerKnows (runTraceMoves r₀ ms)) (LoggedIkmRk (runTraceMoves r₀ ms)) false seed :=
  spineRkK_of_recvSeed (spStateRkK_runTrace hst) (attackerKnows_x25519Key hpk) hseed

end Symbolic.Swarm.CREF.TR.G1.Spine
