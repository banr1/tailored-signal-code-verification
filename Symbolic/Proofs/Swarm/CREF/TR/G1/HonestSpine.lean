/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.IkShapeId
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineIkm
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
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
# Role-Indexed Honest-Spine Invariant

Proves that every stored `TRState` along a composed run satisfies `SpState (LoggedIkmR T)`, placing
stored root and sending chain keys at parity `true` and receiving chain keys and seeds at parity
`false` over `LoggedIkmR T` with `ShapeId` DH secrets (`spState_runTrace`). Consequently, shape-equal
sending and receiving seeds of available states are equal under peel-local `DhHole` and
opposite-role base injectivity (`seed_eq_of_shape_eq_peel`).
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
open Symbolic.Swarm.CREF.TR.G1 (ShapeId)
open Symbolic.Swarm.CREF.TR.G1.ShapeModKem (KemLeaf)
open Symbolic.Swarm.CREF.TR.G1.SpineIkm (SpineR spineR_chainKeyAt DhHole dhHole_agree)
open Symbolic.Swarm.CREF.TR.G1.Ik (IkStEntry IkPQStEntry IkPQEvEntry proj_inj_ik)
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## Grammar helpers -/

/-- The honest spine with `DhHole` holes over a role-indexed base `B`. -/
abbrev Sp (B : Bool → DY.Bytes → Prop) : Bool → DY.Bytes → Prop := SpineR DhHole B

theorem sp_mono {B B' : Bool → DY.Bytes → Prop} (h : ∀ c m, B c m → B' c m) {b : Bool}
    {u : DY.Bytes} (hu : Sp B b u) : Sp B' b u :=
  SpineIkm.SpineR.mono (fun _ hm => hm) h hu

theorem dhHole_createChain {pk sk : DY.Bytes} (hsk : ShapeId sk) :
    DhHole (dh (DY.X25519.normalizeX25519Key pk) sk) :=
  ⟨pk, sk, rfl, hsk⟩

theorem sp_createChain_fst {B : Bool → DY.Bytes → Prop} {b : Bool} {rk pk sk : DY.Bytes}
    (hrk : Sp B b rk) (hsk : ShapeId sk) : Sp B (!b) (createChain rk pk sk).1 :=
  SpineR.rkStep1 hrk (dhHole_createChain hsk)

theorem sp_createChain_snd {B : Bool → DY.Bytes → Prop} {b : Bool} {rk pk sk : DY.Bytes}
    (hrk : Sp B b rk) (hsk : ShapeId sk) : Sp B (!b) (createChain rk pk sk).2 :=
  SpineR.rkStep2 hrk (dhHole_createChain hsk)

/-! ## Logged handshake IKMs -/

/-- Handshake keys derived from `DhHole` DH outputs and the KEM leaf paired with `ct`. -/
def HsKeysOk (ct : DY.Bytes) (keys : DY.Libsignal.PQXDH.HandshakeKeys) : Prop :=
  ∃ (ss d1 d2 d3 : DY.Bytes) (d4 : Option DY.Bytes),
    ((∃ pk e : DY.Bytes, ct = (DY.PQKem.kemEncap pk e).1 ∧ ss = (DY.PQKem.kemEncap pk e).2) ∨
      (∃ sk : DY.Bytes, ss = DY.PQKem.kemRejKey sk ct)) ∧
    keys = pqxdhKdf (pqxdhIkm d1 d2 d3 d4 ss) ∧
    DhHole d1 ∧ DhHole d2 ∧ DhHole d3 ∧ (∀ d, d4 = some d → DhHole d)

/-- `ikm` is a PQXDH input key material with `DhHole` DH outputs and the KEM leaf paired with `ct`,
and `keys` is derived from it. -/
def CtKeysIkm (ct : DY.Bytes) (keys : DY.Libsignal.PQXDH.HandshakeKeys) (ikm : DY.Bytes) :
    Prop :=
  ∃ (ss d1 d2 d3 : DY.Bytes) (d4 : Option DY.Bytes),
    ((∃ pk e : DY.Bytes, ct = (DY.PQKem.kemEncap pk e).1 ∧ ss = (DY.PQKem.kemEncap pk e).2) ∨
      (∃ sk : DY.Bytes, ss = DY.PQKem.kemRejKey sk ct)) ∧
    ikm = pqxdhIkm d1 d2 d3 d4 ss ∧
    keys = pqxdhKdf ikm ∧
    DhHole d1 ∧ DhHole d2 ∧ DhHole d3 ∧ (∀ d, d4 = some d → DhHole d)

/-- `ikm` is an input key material of a handshake-completion event of role `c`
(`false`: `AliceDone`, `true`: `BobDone`). -/
def DoneIkmR (c : Bool) (ev : DY.Libsignal.PQXDH.PQXDHEvent) (ikm : DY.Bytes) : Prop :=
  match c, ev with
  | false, .AliceDone _ _ _ _ _ _ _ _ ct keys => CtKeysIkm ct keys ikm
  | true, .BobDone _ _ _ _ _ _ _ _ ct keys => CtKeysIkm ct keys ikm
  | _, _ => False

/-- `ev` is logged in `T`. -/
def LoggedPQEv (T : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent) : Prop :=
  ∃ (j : Nat) (e : IkPQEvEntry), (T.at? j : Option IkPQEvEntry) = some e ∧ e.ev = ev

/-- Role-indexed input key materials of handshake-completion events logged in `T`. -/
def LoggedIkmR (T : ExecTrace) (c : Bool) (ikm : DY.Bytes) : Prop :=
  ∃ ev, LoggedPQEv T ev ∧ DoneIkmR c ev ikm

/-- PQXDH input key material with `DhHole` DH outputs and a KEM leaf. -/
def IkmH (ikm : DY.Bytes) : Prop :=
  ∃ (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (ss : DY.Bytes),
    ikm = pqxdhIkm dh1 dh2 dh3 dh4 ss ∧ DhHole dh1 ∧ DhHole dh2 ∧ DhHole dh3 ∧
    (∀ d, dh4 = some d → DhHole d) ∧ KemLeaf ss

theorem ikmH_of_ctKeysIkm {ct ikm : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (h : CtKeysIkm ct keys ikm) : IkmH ikm := by
  obtain ⟨ss, d1, d2, d3, d4, hkem, hikm, _, h1, h2, h3, h4⟩ := h
  refine ⟨d1, d2, d3, d4, ss, hikm, h1, h2, h3, h4, ?_⟩
  rcases hkem with ⟨pk, e, _, rfl⟩ | ⟨sk, rfl⟩
  · exact .inl ⟨pk, e, rfl⟩
  · exact .inr ⟨sk, ct, rfl⟩

theorem ikmH_of_doneIkmR {c : Bool} {ev : DY.Libsignal.PQXDH.PQXDHEvent} {ikm : DY.Bytes}
    (h : DoneIkmR c ev ikm) : IkmH ikm := by
  cases c <;> cases ev <;> simp only [DoneIkmR] at h <;>
    first | exact h.elim | exact ikmH_of_ctKeysIkm h

theorem ikmH_of_loggedIkmR {T : ExecTrace} {c : Bool} {ikm : DY.Bytes} (h : LoggedIkmR T c ikm) :
    IkmH ikm := by
  obtain ⟨_, _, hd⟩ := h
  exact ikmH_of_doneIkmR hd

/-- Handshake keys of a role-`c` base are spine terms at index `c`. -/
theorem sp_of_hsKeysOk {B : Bool → DY.Bytes → Prop} {c : Bool} {ct : DY.Bytes}
    {keys : DY.Libsignal.PQXDH.HandshakeKeys} (hk : HsKeysOk ct keys)
    (hB : ∀ ikm, CtKeysIkm ct keys ikm → B c ikm) :
    Sp B c keys.rk ∧ Sp B c keys.ck := by
  obtain ⟨ss, d1, d2, d3, d4, hkem, hkeys, h1, h2, h3, h4⟩ := hk
  have hikm : B c (pqxdhIkm d1 d2 d3 d4 ss) :=
    hB _ ⟨ss, d1, d2, d3, d4, hkem, rfl, hkeys, h1, h2, h3, h4⟩
  rw [hkeys]
  exact ⟨.hsRk hikm, .hsCk hikm⟩

/-! ## Entry predicate -/

/-- Role-indexed honest-spine invariant on a `TRState`: stored `rk` and `cks` have parity `true`,
`dhs` satisfies `ShapeId`, and receiving chain keys have parity `false`. -/
structure SpState (B : Bool → DY.Bytes → Prop) (st : TRState) : Prop where
  rk : Sp B true st.rk
  cks : Sp B true st.cks
  dhs : ShapeId st.dhs
  recv : ∀ c ∈ st.recv, Sp B false c.chainKey

theorem SpState.mono {B B' : Bool → DY.Bytes → Prop} {st : TRState} (hst : SpState B st)
    (h : ∀ c m, B c m → B' c m) : SpState B' st :=
  ⟨sp_mono h hst.rk, sp_mono h hst.cks, hst.dhs, fun c hc => sp_mono h (hst.recv c hc)⟩

/-- PQXDH key states hold `ShapeId` secrets. -/
def PQSkOk (st : DY.Libsignal.PQXDH.PQXDHState) : Prop := ShapeId st.sk

/-- `IdentityRegistered` events carry a `ShapeId` identity public key. -/
def PQEvOk (ev : DY.Libsignal.PQXDH.PQXDHEvent) : Prop :=
  ∀ (p : Participant) (ikPk vkPk : DY.Bytes) (honest : Bool),
    ev = .IdentityRegistered p ikPk vkPk honest → ShapeId ikPk

/-- Per-entry invariant relative to the final trace `T`. -/
def SpEntryOk (T : ExecTrace) (ent : ExecTrace.Entry) : Prop :=
  (∀ e : IkStEntry, TraceEntryHas.proj ent = some e → SpState (LoggedIkmR T) e.st.state) ∧
  (∀ e : IkPQStEntry, TraceEntryHas.proj ent = some e → PQSkOk e.st.state) ∧
  (∀ e : IkPQEvEntry, TraceEntryHas.proj ent = some e → PQEvOk e.ev)

def TraceSpOk (T tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), SpEntryOk T (tr.at j hj)

theorem traceSpOk_nil (T : ExecTrace) : TraceSpOk T (DY.Trace.nil : ExecTrace) :=
  fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj

theorem traceSpOk_append {T : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hent : SpEntryOk T (TraceEntryHas.inj e)) (htr : TraceSpOk T tr) :
    TraceSpOk T (tr.append e) := by
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

private theorem lt_len_of_at_eq {tr T : ExecTrace} {j : Nat} {hj : j < tr.length}
    {hT : j < T.length} (_ : tr.at j hj = T.at j hT) : j < T.length := hT

theorem at?_of_le {E : Type} [ExecTraceTypes.Has E] {tr T : ExecTrace} (hle : tr ≤ T) {j : Nat}
    {e : E} (h : (tr.at? j : Option E) = some e) : (T.at? j : Option E) = some e := by
  unfold DY.Trace.at? at h ⊢
  split at h
  · next hj =>
    have hT := lt_len_of_at_eq (DY.Trace.at_le tr T j hj hle)
    rw [DY.Trace.at_le tr T j hj hle] at h
    split
    · exact h
    · next hT' => exact absurd hT hT'
  · cases h

theorem at?_append_self {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e := by
  unfold DY.Trace.at?
  split
  · next h =>
    have : (tr.append e).at tr.length h = TraceEntryHas.inj e := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2]
    rw [this, proj_inj_ik]
  · next h => exact absurd (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]) h

/-! ## `TracefulSp` combinators -/

/-- Monad combinator for `TraceSpOk T`, on runs whose output trace is a prefix of `T`. -/
def TracefulSp {α : Type} (T : ExecTrace) (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).2.val ≤ T → TraceSpOk T tr →
    TraceSpOk T (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

section Combinators

variable {T : ExecTrace}

theorem TracefulSp.pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    TracefulSp T Q (Pure.pure a) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb
  exact ha

theorem TracefulSp.failure {α : Type} {Q : α → Prop} :
    TracefulSp T Q (Alternative.failure : Traceful α) := by
  intro tr _ htr
  rw [DY.Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

private theorem run_bind_fst_sp {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd_sp {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem TracefulSp.bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulSp T Q₁ x) (hf : ∀ a : α, Q₁ a → TracefulSp T Q₂ (f a)) :
    TracefulSp T Q₂ (x >>= f) := by
  intro tr hT htr
  rw [run_bind_snd_sp] at hT
  rw [run_bind_snd_sp, run_bind_fst_sp]
  revert hT
  cases hres : (x.run tr).1 with
  | none =>
    intro hT
    exact ⟨(hx tr hT htr).1, fun _ hb => by cases hb⟩
  | some a =>
    intro hT
    have hT1 : (x.run tr).2.val ≤ T :=
      DY.Trace.le_trans _ _ _ ((f a).run (x.run tr).2.val).2.property hT
    have h1 := hx tr hT1 htr
    exact hf a (h1.2 a hres) _ hT h1.1

theorem TracefulSp.guardP (p : Prop) [Decidable p] :
    TracefulSp T (fun _ => p) (_root_.guard p) := by
  unfold _root_.guard
  split
  · next h => exact TracefulSp.pure h
  · exact TracefulSp.failure

/-! ## Primitive steps -/

theorem tracefulSp_guardTrace (p : ExecTrace → Bool) :
    TracefulSp T (fun _ => True) (guardTrace p) := by
  intro _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulSp_traceLength : TracefulSp T (fun _ => True) traceLength := by
  intro _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulSp_guardOnTrace (p : ExecTrace → Bool) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulSp.getEntry_any {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulSp T (fun (_ : E) => True) (getEntry j : Traceful E) := by
  intro _ _ htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulSp.getEntry_st (j : Nat) :
    TracefulSp T (fun (e : IkStEntry) => SpState (LoggedIkmR T) e.st.state) (getEntry j) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  change (tr.at? j : Option IkStEntry) = some e at he
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).1 e he
  · cases he

theorem TracefulSp.getEntry_pq (j : Nat) :
    TracefulSp T (fun (e : IkPQStEntry) => PQSkOk e.st.state) (getEntry j) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  change (tr.at? j : Option IkPQStEntry) = some e at he
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2.1 e he
  · cases he

theorem TracefulSp.getEntry_ev (j : Nat) :
    TracefulSp T (fun (e : IkPQEvEntry) => PQEvOk e.ev) (getEntry j) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  change (tr.at? j : Option IkPQEvEntry) = some e at he
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2.2 e he
  · cases he

end Combinators

/-- The network message read at handle `j` of `T`. -/
def MsgAt (T : ExecTrace) (j : Nat) (b : DY.Bytes) : Prop :=
  ((Network.receiveMessage j).run T).1 = some b

/-- Every Signal message parsed at handle `j` of `T` has a `ShapeId` ratchet key. -/
def NetRkShapeId (T : ExecTrace) (j : Nat) : Prop :=
  ∀ b msg, MsgAt T j b → parseTrSignalMsg b = some msg → ShapeId msg.ratchetKey

theorem receiveMessage_mono {tr T : ExecTrace} (hle : tr ≤ T) {j : Nat} {b : DY.Bytes}
    (h : ((Network.receiveMessage j).run tr).1 = some b) : MsgAt T j b := by
  unfold MsgAt
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1] at h ⊢
  rw [run_bind_fst_sp] at h ⊢
  split at h
  · next e heq =>
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk] at heq ⊢
    rw [at?_of_le hle heq]
    simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1] at h ⊢
    exact h
  · cases h

section Steps

variable {T : ExecTrace}

theorem TracefulSp.receiveMessage (j : Nat) :
    TracefulSp T (fun b => MsgAt T j b) (Network.receiveMessage j) := by
  intro tr hT htr
  have h0 : TracefulSp T (fun _ => True) (Network.receiveMessage j) := by
    simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
    exact TracefulSp.bind (TracefulSp.getEntry_any j) fun _ _ => TracefulSp.pure trivial
  refine ⟨(h0 tr hT htr).1, fun b hb => receiveMessage_mono ?_ hb⟩
  exact DY.Trace.le_trans _ _ _ ((Network.receiveMessage j).run tr).2.property hT

theorem tracefulSp_receiveSignalMsg (j : Nat) :
    TracefulSp T (fun msg => NetRkShapeId T j → ShapeId msg.ratchetKey) (receiveSignalMsg j) := by
  unfold receiveSignalMsg
  refine TracefulSp.bind (TracefulSp.receiveMessage j) fun b hb => ?_
  split
  · next msg hp =>
    exact TracefulSp.bind (TracefulSp.guardP _) fun _ _ =>
      TracefulSp.pure fun hN => hN b msg hb hp
  · exact TracefulSp.failure

theorem TracefulSp.getLocalState (p : Participant) (j : Nat) :
    TracefulSp T (fun (st : TRState) => SpState (LoggedIkmR T) st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulSp.bind
    (TracefulSp.bind (TracefulSp.getEntry_st j) fun _ he =>
      TracefulSp.pure
        (Q := fun (ls : PersistentLocalState.LocalState TRState) => SpState (LoggedIkmR T) ls.state)
        he)
    fun _ hst => ?_
  exact TracefulSp.bind (TracefulSp.guardP _) fun _ _ => TracefulSp.pure hst

theorem TracefulSp.getLocalStatePQ (p : Participant) (j : Nat) :
    TracefulSp T (fun (st : DY.Libsignal.PQXDH.PQXDHState) => PQSkOk st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulSp.bind
    (TracefulSp.bind (TracefulSp.getEntry_pq j) fun _ he =>
      TracefulSp.pure
        (Q := fun (ls : PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) =>
          PQSkOk ls.state) he)
    fun _ hst => ?_
  exact TracefulSp.bind (TracefulSp.guardP _) fun _ _ => TracefulSp.pure hst

theorem TracefulSp.getKey (p : Participant) (j : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    TracefulSp T (fun (sk : DY.Bytes) => ShapeId sk) (DY.Libsignal.PQXDH.getKey p j kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine TracefulSp.bind (TracefulSp.getLocalStatePQ p j) fun st hst => ?_
  exact TracefulSp.bind (TracefulSp.guardP _) fun _ _ => TracefulSp.pure hst

theorem TracefulSp.lookupIdentity (p : Participant) (j : Nat) :
    TracefulSp T (fun (kv : DY.Bytes × DY.Bytes) => ShapeId kv.1)
      (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulSp.bind (TracefulSp.getEntry_ev j) fun e hev => ?_
  split
  · next p' ikPk vkPk honest heq =>
    exact TracefulSp.bind (TracefulSp.guardP _) fun _ _ =>
      TracefulSp.pure (hev p' ikPk vkPk honest heq)
  · exact TracefulSp.failure

theorem TracefulSp.genRand_shapeId (n : Nat) (hn : n ≠ 0) :
    TracefulSp T (fun (b : DY.Bytes) => ShapeId b) (DY.Random.genRand n) := by
  intro tr _ htr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨traceSpOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun a ha => ?_⟩
  injection ha with ha
  subst ha
  exact Symbolic.Swarm.CREF.TR.G1.termShapeId_randTerm_of_ne_zero tr.length n hn

theorem TracefulSp.sendMessage (msg : DY.Bytes) :
    TracefulSp T (fun _ => True) (Network.sendMessage msg) := by
  intro _ _ htr
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact ⟨traceSpOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulSp.logEvent (ev : TREvent) :
    TracefulSp T (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro _ _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceSpOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulSp.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulSp T (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro _ _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceSpOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulSp.logEventPQ {ev : DY.Libsignal.PQXDH.PQXDHEvent} (hev : PQEvOk ev) :
    TracefulSp T (fun _ => LoggedPQEv T ev) (DY.ProtocolEvent.logEvent ev) := by
  intro tr hT htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1] at hT ⊢
  refine ⟨traceSpOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), ?_⟩ htr,
    fun _ _ => ⟨tr.length, { ev := ev }, at?_of_le hT (at?_append_self tr ({ ev := ev } : IkPQEvEntry)), rfl⟩⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hev

theorem TracefulSp.storeLocalState (p : Participant) {st : TRState}
    (hst : SpState (LoggedIkmR T) st) :
    TracefulSp T (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨traceSpOk_append ⟨?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst

theorem TracefulSp.storeLocalStatePQ (p : Participant) {st : DY.Libsignal.PQXDH.PQXDHState}
    (hst : PQSkOk st) :
    TracefulSp T (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨traceSpOk_append ⟨fun _ h => (by cases h), ?_, fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst

end Steps

theorem TracefulSp.genRand {T : ExecTrace} (n : Nat) :
    TracefulSp T (fun _ => True) (DY.Random.genRand n) := by
  intro _ _ htr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceSpOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

/-! ## Double Ratchet key schedule -/

section DR

variable {B : Bool → DY.Bytes → Prop}

/-- Chains of `recvChainFor` are spine terms at the receiving index. No premise on the ratchet key:
a fresh chain is a `kdfRk` step whose DH hole has the state's own `ShapeId` secret. -/
theorem sp_recvChainFor {st : TRState} {pk : DY.Bytes} {c : RecvChain} {b : Bool}
    (hst : SpState B st) (hrc : recvChainFor st.toDRState pk = some (c, b)) :
    Sp B false c.chainKey := by
  unfold recvChainFor at hrc
  rcases hfind : findRecvChain st.toDRState.recv pk with _ | c₀
  · rw [hfind] at hrc; dsimp only at hrc
    split at hrc
    · cases hrc
    · injection hrc with hrc
      rcases Prod.mk.inj hrc with ⟨rfl, _⟩
      exact sp_createChain_snd (b := true) hst.rk hst.dhs
  · rw [hfind] at hrc
    injection hrc with hrc
    rcases Prod.mk.inj hrc with ⟨rfl, _⟩
    unfold findRecvChain at hfind
    exact hst.recv _ (List.mem_of_find?_eq_some hfind)

theorem sp_consumeMessageKey {b : Bool} {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hc : Sp B b c.chainKey) (hcm : consumeMessageKey c counter = some (seed, c')) :
    Sp B b seed ∧ Sp B b c'.chainKey := by
  unfold consumeMessageKey at hcm
  split at hcm
  · cases hcm
  · split at hcm
    · cases hcm
    · split at hcm
      · cases hcm
      · injection hcm with hcm
        rcases Prod.mk.inj hcm with ⟨rfl, rfl⟩
        have hck := spineR_chainKeyAt hc (counter.toNat - c.index.toNat)
        exact ⟨.ckStep2 hck, .ckStep1 hck⟩

theorem spState_setRecv {st : TRState} {c' : RecvChain} (hst : SpState B st)
    (hc' : Sp B false c'.chainKey) (spqr : DY.Bytes) :
    SpState B { st with recv := setRecvChain st.recv c', spqr := spqr } := by
  refine ⟨hst.rk, hst.cks, hst.dhs, fun c hc => ?_⟩
  have hc2 : c ∈ setRecvChain st.recv c' := hc
  unfold setRecvChain at hc2
  obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc2
  split at heq <;> subst heq
  · exact hc'
  · exact hst.recv c₀ hc₀

theorem spState_send {st : TRState} (hst : SpState B st) (ns : UInt32) (spqr : DY.Bytes) :
    SpState B { st with cks := (kdfCk st.cks).1, ns := ns, spqr := spqr } :=
  ⟨hst.rk, .ckStep1 hst.cks, hst.dhs, hst.recv⟩

theorem spState_spqr {st : TRState} (hst : SpState B st) (spqr : DY.Bytes) :
    SpState B { st with spqr := spqr } :=
  ⟨hst.rk, hst.cks, hst.dhs, hst.recv⟩

/-- Seeds of `recvSeed` are spine terms at the receiving index (no premise on the ratchet key). -/
theorem sp_of_recvSeed {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes}
    (hst : SpState B st) (hseed : recvSeed st msg = some seed) : Sp B false seed := by
  unfold recvSeed at hseed
  split at hseed
  · rcases hrc : recvChainFor st.toDRState msg.ratchetKey with _ | ⟨c, b⟩
    · rw [hrc] at hseed; cases hseed
    · rw [hrc] at hseed; dsimp only at hseed
      rcases hcm : consumeMessageKey c msg.counter with _ | ⟨s, c'⟩
      · rw [hcm] at hseed; cases hseed
      · rw [hcm] at hseed
        injection hseed with hseed; subst hseed
        exact (sp_consumeMessageKey (sp_recvChainFor hst hrc) hcm).1
  · cases hseed

variable {T : ExecTrace}

theorem tracefulSp_dhRatchetStep {st : TRState} {pk : DY.Bytes} (hst : SpState B st) :
    TracefulSp T (fun (p : TRState × RecvChain) => SpState B p.1 ∧ Sp B false p.2.chainKey)
      (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulSp.bind (TracefulSp.guardP _) fun _ _ => ?_
  refine TracefulSp.bind (TracefulSp.genRand_shapeId 32 (by decide)) fun dhs' hdhs' => ?_
  have hrk1 : Sp B false (createChain st.rk pk st.dhs).1 := sp_createChain_fst (b := true) hst.rk hst.dhs
  have hckr : Sp B false (createChain st.rk pk st.dhs).2 := sp_createChain_snd (b := true) hst.rk hst.dhs
  refine TracefulSp.pure ⟨⟨sp_createChain_fst (b := false) hrk1 hdhs',
    sp_createChain_snd (b := false) hrk1 hdhs', hdhs', fun c' hc' => ?_⟩, hckr⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst.recv c' hmem
  · rcases List.mem_singleton.mp hmem with rfl
    exact hckr

theorem tracefulSp_ensureReceiverChain {st : TRState} {pk : DY.Bytes} (hst : SpState B st) :
    TracefulSp T
      (fun (p : TRState × RecvChain × Bool) => SpState B p.1 ∧ Sp B false p.2.1.chainKey)
      (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · next c hr => exact TracefulSp.pure ⟨hst, sp_recvChainFor hst hr⟩
  · exact TracefulSp.bind (tracefulSp_dhRatchetStep hst) fun ⟨_, _⟩ h => TracefulSp.pure h
  · exact TracefulSp.failure

end DR

/-! ## Triple Ratchet transitions -/

section TR

variable {T : ExecTrace}

theorem tracefulSp_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : SpState (LoggedIkmR T) st) :
    TracefulSp T (fun _ => True)
      (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
    TracefulSp.storeLocalState me hst

theorem tracefulSp_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    TracefulSp T (fun _ => True) (logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero =>
    unfold logSkippedKeys
    exact TracefulSp.pure trivial
  | succ k ih =>
    unfold logSkippedKeys
    exact TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => ih (kdfCk ck).1 (n + 1)

theorem tracefulSp_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    TracefulSp T (fun _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulSp.bind (TracefulSp.guardP _) fun _ _ => ?_
  intro _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulSp_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulSp T (fun _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  refine TracefulSp.bind (TracefulSp.getLocalState me stateIdx) fun st hst =>
    TracefulSp.bind (TracefulSp.guardP _) fun _ _ =>
    TracefulSp.bind (TracefulSp.genRand 32) fun _ _ =>
    TracefulSp.bind (TracefulSp.genRand coinsLen) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ =>
    TracefulSp.bind (TracefulSp.receiveMessage pqIdx) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
    TracefulSp.bind (tracefulSp_logMessageKeyAndStore me _ .sender _ _ _ _ _
      (spState_send hst _ _)) fun _ _ =>
      TracefulSp.sendMessage _

theorem tracefulSp_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    TracefulSp T (fun _ => True) (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact TracefulSp.bind (TracefulSp.getLocalState me stateIdx) fun _ _ =>
    TracefulSp.bind (TracefulSp.genRand 32) fun _ _ => TracefulSp.failure

theorem tracefulSp_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulSp T (fun _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulSp.bind (TracefulSp.getLocalState me stateIdx) fun st₀ hst₀ =>
    TracefulSp.bind (tracefulSp_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulSp.bind (tracefulSp_ensureReceiverChain hst₀)
      fun ⟨st, c, ratcheted⟩ hst => ?_
  dsimp only
  split
  · next seed c' hcm =>
    have hc' := (sp_consumeMessageKey (c := c) hst.2 hcm).2
    split
    · next spqr' key _ =>
      refine TracefulSp.bind (TracefulSp.sendMessage key) fun _ _ =>
        TracefulSp.bind (TracefulSp.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulSp.bind (tracefulSp_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      have hrest :
          TracefulSp T (fun _ => True)
            (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                  (msg.counter.toNat - c.index.toNat)
                DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
                logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt
                  msg.counter c.rIdx stateIdx
                  { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulSp.bind (tracefulSp_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
            tracefulSp_logMessageKeyAndStore me _ .receiver _ _ _ _ _
              (spState_setRecv hst.1 hc' spqr')
      split
      · exact TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
          TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => hrest
      · exact hrest
    · exact TracefulSp.failure
  · exact TracefulSp.failure

theorem tracefulSp_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulSp T (fun _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulSp.bind (TracefulSp.getLocalState me stateIdx) fun st hst =>
    TracefulSp.bind (tracefulSp_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulSp.bind (TracefulSp.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TracefulSp.bind (TracefulSp.guardP _) fun _ _ =>
      TracefulSp.bind (tracefulSp_guardTrace _) fun _ _ => ?_
    split
    · next spqr' key _ =>
      exact TracefulSp.bind (TracefulSp.sendMessage key) fun _ _ =>
        TracefulSp.bind (TracefulSp.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulSp.bind (tracefulSp_verifyMacAndDecrypt st msg pqSalt _) fun _ _ =>
        TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
        TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
        tracefulSp_logMessageKeyAndStore me _ .receiver _ _ _ _ _ (spState_spqr hst spqr')
    · exact TracefulSp.failure
  · exact TracefulSp.failure

theorem tracefulSp_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulSp T (fun _ => True) (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine TracefulSp.bind (TracefulSp.getLocalState me stateIdx) fun _ _ => ?_
  cases k with
  | rk => exact TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => TracefulSp.sendMessage _
  | dhs => exact TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => TracefulSp.sendMessage _
  | cks => exact TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => TracefulSp.sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => TracefulSp.sendMessage _
    · exact TracefulSp.failure

theorem tracefulSp_exposeSpqr (me : Participant) (stateIdx : Nat) :
    TracefulSp T (fun _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact TracefulSp.bind (TracefulSp.getLocalState me stateIdx) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => TracefulSp.sendMessage _

theorem tracefulSp_exposeSkipped (skippedKeyEventIdx : Nat) :
    TracefulSp T (fun _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulSp.bind (TracefulSp.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · exact TracefulSp.bind (tracefulSp_guardTrace _) fun _ _ =>
      TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
      TracefulSp.sendMessage _
  · exact TracefulSp.failure

end TR

/-! ## PQXDH key management -/

section PQ

variable {T : ExecTrace}

theorem tracefulSp_compromiseIK (p : Participant) (j : Nat) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact TracefulSp.bind (TracefulSp.getKey p j _) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulSp.sendMessage _

theorem tracefulSp_compromiseSPK (p : Participant) (j : Nat) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact TracefulSp.bind (TracefulSp.getKey p j _) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulSp.sendMessage _

theorem tracefulSp_compromisePQSPK (p : Participant) (j : Nat) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact TracefulSp.bind (TracefulSp.getKey p j _) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulSp.sendMessage _

theorem tracefulSp_compromiseOPK (p : Participant) (j : Nat) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact TracefulSp.bind (TracefulSp.getKey p j _) fun _ _ =>
    TracefulSp.bind (tracefulSp_guardOnTrace _) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulSp.sendMessage _

theorem tracefulSp_registerIdentity (p : Participant) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine TracefulSp.bind (tracefulSp_guardOnTrace _) fun _ _ =>
    TracefulSp.bind (TracefulSp.genRand_shapeId 32 (by decide)) fun ik hik =>
    TracefulSp.bind (TracefulSp.logEventPQ ?_) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ =>
    TracefulSp.storeLocalStatePQ p (st := { kind := .identity, sk := ik }) hik
  intro _ _ _ _ h
  cases h
  exact Symbolic.Swarm.CREF.TR.G1.shapeId_dhPk hik

theorem tracefulSp_genSignedPrekey (b : Participant) (j : Nat) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact TracefulSp.bind (TracefulSp.getKey b j _) fun _ _ =>
    TracefulSp.bind (TracefulSp.genRand_shapeId 32 (by decide)) fun _ hk =>
    TracefulSp.bind (TracefulSp.genRand 64) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulSp.bind (TracefulSp.storeLocalStatePQ b hk) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ => TracefulSp.pure trivial

theorem tracefulSp_genPQPrekey (b : Participant) (j : Nat) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact TracefulSp.bind (TracefulSp.getKey b j _) fun _ _ =>
    TracefulSp.bind (TracefulSp.genRand_shapeId 64 (by decide)) fun _ hk =>
    TracefulSp.bind (TracefulSp.genRand 64) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulSp.bind (TracefulSp.storeLocalStatePQ b hk) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ => TracefulSp.pure trivial

theorem tracefulSp_genOneTimePrekey (b : Participant) :
    TracefulSp T (fun _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact TracefulSp.bind (TracefulSp.genRand_shapeId 32 (by decide)) fun _ hk =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulSp.bind (TracefulSp.storeLocalStatePQ b hk) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ => TracefulSp.pure trivial

theorem tracefulSp_setupAct (a b : Participant) (withOpk : Bool) :
    TracefulSp T (fun _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  apply TracefulSp.bind (Q₁ := fun _ => True) (tracefulSp_registerIdentity a)
  intro _ _
  apply TracefulSp.bind (Q₁ := fun _ => True) (tracefulSp_registerIdentity b)
  intro hB _
  apply TracefulSp.bind (Q₁ := fun _ => True) (tracefulSp_genSignedPrekey b hB)
  intro _ _
  apply TracefulSp.bind (Q₁ := fun _ => True) (tracefulSp_genPQPrekey b hB)
  intro _ _
  split
  · apply TracefulSp.bind (Q₁ := fun _ => True) (tracefulSp_genOneTimePrekey b)
    intro _ _
    exact TracefulSp.pure trivial
  · exact TracefulSp.pure trivial

end PQ

/-! ## Agreements -/

theorem hsKeysOk_aliceAgreement {ikA ek ikB spk pqpk entropy : DY.Bytes} {opk : Option DY.Bytes}
    (hikA : ShapeId ikA) (hek : ShapeId ek) :
    HsKeysOk (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pqpk opk entropy).1
      (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pqpk opk entropy).2 := by
  unfold DY.Libsignal.PQXDH.aliceAgreement
  refine ⟨_, _, _, _, opk.map (agree · ek), .inl ⟨pqpk, entropy, rfl, rfl⟩, rfl, dhHole_agree hikA,
    dhHole_agree hek, dhHole_agree hek, fun d hd => ?_⟩
  rcases opk with _ | o
  · cases hd
  · injection hd with hd
    subst hd
    exact dhHole_agree hek

theorem hsKeysOk_of_bobAgreement {ikB spk pqsk ikA ek ct : DY.Bytes} {opk : Option DY.Bytes}
    {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hikB : ShapeId ikB) (hspk : ShapeId spk) (hopk : ∀ o, opk = some o → ShapeId o)
    (h : DY.Libsignal.PQXDH.bobAgreement ikB spk pqsk opk ikA ek ct = some keys) :
    HsKeysOk ct keys := by
  dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at h
  injection h with hkeys
  subst hkeys
  refine ⟨_, _, _, _, opk.map (agree ek ·), ?_, rfl, dhHole_agree hspk,
    dhHole_agree hikB, dhHole_agree hspk, fun d hd => ?_⟩
  · rcases hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct) with _ | ss
    · exact .inr ⟨pqsk, rfl⟩
    · obtain ⟨e, hct, rfl⟩ := Symbolic.Swarm.CREF.TR.kemDecap_eq_some_iff pqsk ct ss hdec
      exact .inl ⟨_, e, hct, rfl⟩
  · rcases opk with _ | o
    · cases hd
    · injection hd with hd
      subst hd
      exact dhHole_agree (hopk o rfl)

/-! ## Handshakes -/

theorem tracefulSp_aliceHandshake {T : ExecTrace} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulSp T (fun (o : DY.Libsignal.PQXDH.AliceHandshakeOut) => HsKeysOk o.ct o.keys)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulSp.bind (TracefulSp.getKey a idStateIdx _); intro ikA hikA
  apply TracefulSp.bind (TracefulSp.lookupIdentity b regIdxB); intro ikv _
  rcases ikv with ⟨ikB, vkB⟩
  dsimp only
  apply TracefulSp.bind (TracefulSp.receiveMessage h.spk); intro spk _
  apply TracefulSp.bind (TracefulSp.receiveMessage h.spkSig); intro _ _
  apply TracefulSp.bind (TracefulSp.receiveMessage h.pqpk); intro pqpk _
  apply TracefulSp.bind (TracefulSp.receiveMessage h.pqpkSig); intro _ _
  apply TracefulSp.bind (TracefulSp.guardP _); intro _ _
  apply TracefulSp.bind (TracefulSp.guardP _); intro _ _
  split
  · next i hi =>
    apply TracefulSp.bind (TracefulSp.receiveMessage i); intro o _
    apply TracefulSp.bind (TracefulSp.pure (Q := fun (_ : Option DY.Bytes) => True) trivial)
    intro opk _
    apply TracefulSp.bind (TracefulSp.genRand_shapeId 32 (by decide)); intro ek hek
    apply TracefulSp.bind (TracefulSp.guardP _); intro _ _
    apply TracefulSp.bind (TracefulSp.guardP _); intro _ _
    apply TracefulSp.bind (TracefulSp.genRand 32); intro entropy _
    exact TracefulSp.pure (hsKeysOk_aliceAgreement hikA hek)
  · apply TracefulSp.bind (TracefulSp.pure (Q := fun (_ : Option DY.Bytes) => True) trivial)
    intro opk _
    apply TracefulSp.bind (TracefulSp.genRand_shapeId 32 (by decide)); intro ek hek
    apply TracefulSp.bind (TracefulSp.guardP _); intro _ _
    apply TracefulSp.bind (TracefulSp.guardP _); intro _ _
    apply TracefulSp.bind (TracefulSp.genRand 32); intro entropy _
    exact TracefulSp.pure (hsKeysOk_aliceAgreement hikA hek)

theorem tracefulSp_bobHandshake {T : ExecTrace} (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulSp T (fun (o : DY.Libsignal.PQXDH.BobHandshakeOut) =>
        HsKeysOk o.ct o.keys ∧ ShapeId o.spkSk)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TracefulSp.bind (TracefulSp.getKey b h.ik _); intro ikB hikB
  apply TracefulSp.bind (TracefulSp.getKey b h.spk _); intro spkSk hspk
  apply TracefulSp.bind (TracefulSp.getKey b h.pqspk _); intro pqsk _
  split
  case' h_1 i _ =>
    apply TracefulSp.bind (TracefulSp.getKey b i _); intro o ho
    apply TracefulSp.bind (TracefulSp.pure
      (Q := fun (x : Option DY.Bytes) => ∀ d, x = some d → ShapeId d)
      (fun d hd => by cases hd; exact ho))
  case' h_2 =>
    apply TracefulSp.bind (TracefulSp.pure
      (Q := fun (x : Option DY.Bytes) => ∀ d, x = some d → ShapeId d)
      (fun d hd => by cases hd))
  all_goals
    intro opkSk hopk
    apply TracefulSp.bind (TracefulSp.lookupIdentity a regIdxA); intro ikv _
    rcases ikv with ⟨ikA, vkA⟩
    dsimp only
    apply TracefulSp.bind (TracefulSp.receiveMessage ekIdx); intro ek _
    apply TracefulSp.bind (TracefulSp.receiveMessage ctIdx); intro ct _
    apply TracefulSp.bind (TracefulSp.guardP _); intro _ _
    split
    · next keys hkeys =>
      exact TracefulSp.pure ⟨hsKeysOk_of_bobAgreement hikB hspk hopk hkeys, hspk⟩
    · exact TracefulSp.failure

/-! ## Session starts -/

theorem tracefulSp_aliceStart {T : ExecTrace} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulSp T (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulSp.bind (tracefulSp_aliceHandshake a b idStateIdx regIdxB h)
    fun o ho => TracefulSp.bind (TracefulSp.genRand_shapeId 32 (by decide)) fun dhsA hdhs => ?_
  rcases hcc : createChain o.keys.rk o.spk dhsA with ⟨rkA, cksA⟩
  dsimp only
  refine TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ =>
    TracefulSp.bind (TracefulSp.sendMessage _) fun _ _ =>
    TracefulSp.bind tracefulSp_traceLength fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ hlog =>
    TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
    TracefulSp.bind (TracefulSp.logEventC _) fun _ _ =>
    TracefulSp.storeLocalState a ?_
  have hsp := sp_of_hsKeysOk (B := LoggedIkmR T) (c := false) ho fun ss hss => ⟨_, hlog, hss⟩
  refine ⟨?_, ?_, hdhs, fun c hc => ?_⟩
  · have := sp_createChain_fst (pk := o.spk) hsp.1 hdhs
    rw [hcc] at this
    exact this
  · have := sp_createChain_snd (pk := o.spk) hsp.1 hdhs
    rw [hcc] at this
    exact this
  · rcases List.mem_singleton.mp hc with rfl
    exact hsp.2

theorem tracefulSp_bobStart {T : ExecTrace} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulSp T (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulSp.bind (tracefulSp_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o ho =>
    TracefulSp.bind (tracefulSp_receiveSignalMsg mh.msg) fun msg _ => ?_
  have hsp := sp_of_hsKeysOk (B := fun c ikm => c = true ∧ CtKeysIkm o.ct o.keys ikm) (c := true)
    ho.1 fun _ h => ⟨rfl, h⟩
  refine TracefulSp.bind (tracefulSp_ensureReceiverChain
    (B := fun c ikm => c = true ∧ CtKeysIkm o.ct o.keys ikm)
    ⟨hsp.1, hsp.2, ho.2, fun _ h => by cases h⟩) fun x hst => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hst ⊢
  split
  · next seed c' hcm =>
    have hc' := (sp_consumeMessageKey hst.2 hcm).2
    split
    · next spqr' key _ =>
      refine TracefulSp.bind (TracefulSp.sendMessage key) fun _ _ =>
        TracefulSp.bind (TracefulSp.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulSp.bind (tracefulSp_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      split
      all_goals first
        | refine TracefulSp.bind (tracefulSp_guardOnTrace _) fun _ _ =>
            TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ => ?_
        | skip
      all_goals refine TracefulSp.bind tracefulSp_traceLength fun _ _ =>
        TracefulSp.bind (TracefulSp.logEventPQ fun _ _ _ _ h => by cases h) fun _ hlog => ?_
      all_goals
        have hfin : SpState (LoggedIkmR T)
            { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
          (spState_setRecv hst.1 hc' spqr').mono fun c ss hss => by
            obtain ⟨rfl, hss⟩ := hss
            exact ⟨_, hlog, hss⟩
      all_goals split
      all_goals first
        | refine TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
            TracefulSp.bind (TracefulSp.logEvent _) fun _ _ => ?_
        | skip
      all_goals exact TracefulSp.bind (TracefulSp.logEventC _) fun _ _ =>
          TracefulSp.bind tracefulSp_traceLength fun _ _ =>
          TracefulSp.bind (tracefulSp_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulSp.bind (TracefulSp.logEvent _) fun _ _ =>
          tracefulSp_logMessageKeyAndStore b _ .receiver _ _ _ _ _ hfin
    · exact TracefulSp.failure
  · exact TracefulSp.failure

/-! ## Moves induction -/

theorem tracefulSp_run_snd {T : ExecTrace} {α : Type} {Q : α → Prop} {x : Traceful α}
    (hx : TracefulSp T Q x) {tr : ExecTrace}
    (hT : ((x >>= fun _ => Pure.pure ()).run tr).2.val ≤ T) (htr : TraceSpOk T tr) :
    TraceSpOk T ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulSp.bind hx (fun _ _ => TracefulSp.pure (Q := fun _ => True) trivial) tr hT htr).1

theorem traceSpOk_move_next {T tr : ExecTrace} {m : Move} (hT : m.next tr ≤ T)
    (htr : TraceSpOk T tr) : TraceSpOk T (m.next tr) := by
  unfold Move.next Move.act at hT ⊢
  cases m with
  | setup a b withOpk => exact (tracefulSp_setupAct a b withOpk tr hT htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulSp_run_snd (tracefulSp_aliceStart a b idStateIdx regIdxB h) hT htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulSp_run_snd (tracefulSp_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) hT htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulSp_run_snd (tracefulSp_messageEncrypt me stateIdx coinsLen pqIdx) hT htr
  | encryptAbort me stateIdx =>
    exact tracefulSp_run_snd (tracefulSp_messageEncryptAbort me stateIdx) hT htr
  | encryptFail me stateIdx coinsLen =>
    dsimp only at hT ⊢
    exact (TracefulSp.bind tracefulSp_traceLength
      (fun n _ => TracefulSp.bind (tracefulSp_messageEncrypt me stateIdx coinsLen (n + 3))
        (fun _ _ => TracefulSp.pure (Q := fun _ => True) trivial)) tr hT htr).1
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulSp_run_snd (tracefulSp_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx)
      hT htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulSp_run_snd
      (tracefulSp_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx)
      hT htr
  | reject _ =>
    dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact htr
  | compromiseIK p stateIdx => exact tracefulSp_run_snd (tracefulSp_compromiseIK p stateIdx) hT htr
  | compromiseSPK p stateIdx =>
    exact tracefulSp_run_snd (tracefulSp_compromiseSPK p stateIdx) hT htr
  | compromisePQSPK p stateIdx =>
    exact tracefulSp_run_snd (tracefulSp_compromisePQSPK p stateIdx) hT htr
  | compromiseOPK p stateIdx =>
    exact tracefulSp_run_snd (tracefulSp_compromiseOPK p stateIdx) hT htr
  | exposeKey me stateIdx k => exact tracefulSp_run_snd (tracefulSp_exposeKey me stateIdx k) hT htr
  | exposeSpqr me stateIdx => exact tracefulSp_run_snd (tracefulSp_exposeSpqr me stateIdx) hT htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulSp_run_snd (tracefulSp_exposeSkipped skippedKeyEventIdx) hT htr
  | attackerSend msg => exact tracefulSp_run_snd (TracefulSp.sendMessage msg) hT htr
  | brkDH =>
    exact (TracefulSp.logEventPQ (ev := .BrokenDH) (fun _ _ _ _ h => by cases h) tr hT htr).1
  | brkKEM =>
    exact (TracefulSp.logEventPQ (ev := .BrokenKEM) (fun _ _ _ _ h => by cases h) tr hT htr).1

theorem traceSpOk_runMoves {T : ExecTrace} :
    ∀ (L : List Move) (tr : ExecTrace), (runMoves L tr).1 ≤ T →
      TraceSpOk T tr → TraceSpOk T (runMoves L tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hT, htr => by
    have hT' : (runMoves ms (m.next tr)).1 ≤ T := hT
    have hle : m.next tr ≤ T :=
      DY.Trace.le_trans _ _ _ (Symbolic.Swarm.CREF.runMoves_le ms (m.next tr)) hT'
    exact traceSpOk_runMoves ms (m.next tr) hT' (traceSpOk_move_next hle htr)

/-- Every entry of the run's trace satisfies `SpEntryOk` relative to the run's own trace. -/
theorem traceSpOk_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    TraceSpOk (runTraceMoves r₀ ms) (runTraceMoves r₀ ms) :=
  traceSpOk_runMoves (r₀.setupMove :: ms) DY.Trace.nil (DY.Trace.le_refl _) (traceSpOk_nil _)

theorem spState_of_mem_availableStates {r₀ : ProtocolSetup} {T tr : ExecTrace} (htr : TraceSpOk T tr)
    {st : TRState} (hst : st ∈ availableStates r₀ tr) : SpState (LoggedIkmR T) st := by
  unfold availableStates storedStates DY.ExecTrace.getLocalStateAt at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he
  obtain ⟨e, hat, rfl⟩ := he
  unfold DY.Trace.at? at hat
  split at hat
  · next hj => exact (htr j hj).1 e hat
  · cases hat

/-- Every available state of a run satisfies `SpState (LoggedIkmR (runTraceMoves r₀ ms))`. -/
theorem spState_runTrace {r₀ : ProtocolSetup} {ms : List Move} {st : TRState}
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) : SpState (LoggedIkmR (runTraceMoves r₀ ms)) st :=
  spState_of_mem_availableStates (traceSpOk_runTrace r₀ ms) hst

/-! ## Seed uniqueness from peel-local injectivity -/

/-- Shape-equal sending and receiving seeds of available states are equal whenever a received
ratchet key opening a fresh chain satisfies `ShapeId`. -/
def HonestSkelUniqRk (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) : Prop :=
  ∀ st_s ∈ availableStates r₀ (runTraceMoves r₀ ms), ∀ st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms),
    ∀ (msg₀ : TRSignalMsg) (mkSeed : DY.Bytes),
      (findRecvChain st₀.recv msg₀.ratchetKey = none → ShapeId msg₀.ratchetKey) →
      recvSeed st₀ msg₀ = some mkSeed →
      (gamma' interpretation S g (kdfCk st_s.cks).2).shape =
        (gamma' interpretation S g mkSeed).shape →
      (kdfCk st_s.cks).2 = mkSeed

open SpineIkm (Peel eq_of_shape_eq_of_spineR_peel) in
/-- For available states `st_s` and `st₀` of a run, a shape-equal sending seed `(kdfCk st_s.cks).2`
and receiving seed `mkSeed` of `st₀` are equal, given injectivity on the `DhHole` pairs and
opposite-role logged base pairs reached by the peel from `((kdfCk st_s.cks).2, mkSeed)`. -/
theorem seed_eq_of_shape_eq_peel (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) {st_s st₀ : TRState}
    (hst_s : st_s ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms)) {msg₀ : TRSignalMsg} {mkSeed : DY.Bytes}
    (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (hhole : ∀ d₁ d₂ : DY.Bytes, Peel (kdfCk st_s.cks).2 mkSeed d₁ d₂ → DhHole d₁ → DhHole d₂ →
      (gamma' interpretation S g d₁).shape = (gamma' interpretation S g d₂).shape → d₁ = d₂)
    (hbase : ∀ (c c' : Bool) (m₁ m₂ : DY.Bytes),
      SpineIkm.PeelKdf (kdfCk st_s.cks).2 mkSeed m₁ m₂ →
      LoggedIkmR (runTraceMoves r₀ ms) c m₁ → LoggedIkmR (runTraceMoves r₀ ms) c' m₂ → (c ^^ c') = true →
      (gamma' interpretation S g m₁).shape = (gamma' interpretation S g m₂).shape → m₁ = m₂)
    (hshape : (gamma' interpretation S g (kdfCk st_s.cks).2).shape =
      (gamma' interpretation S g mkSeed).shape) :
    (kdfCk st_s.cks).2 = mkSeed :=
  eq_of_shape_eq_of_spineR_peel hhole hbase (.ckStep2 (spState_runTrace hst_s).cks)
    (sp_of_recvSeed (spState_runTrace hst₀) hseed) .refl hshape rfl

end Symbolic.Swarm.CREF.TR.G1.Spine
