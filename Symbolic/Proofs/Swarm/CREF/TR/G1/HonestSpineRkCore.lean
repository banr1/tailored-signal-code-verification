/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpine
public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkHole
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
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
# Position-Indexed Honest Spine Core

Defines the position-indexed honest-spine invariant `SpStateRk` over the role- and parity-indexed
hole predicates of `RkHole`, together with positional PQXDH draw-role tags (`IkAt`, `SpkAt`,
`OpkAt`, `EkAt`) and the trace-length monad combinators `TracefulR` and `TracefulF`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent KeyDir RecvChain findRecvChain
  setRecvChain recvChainFor consumeMessageKey kdfCk kdfRk createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf)
open Symbolic.Swarm.CREF.TR.G1.ShapeModKem (KemLeaf)
open Symbolic.Swarm.CREF.TR.G1.Ik (IkStEntry IkPQStEntry IkPQEvEntry proj_inj_ik)

/-! ## Positional role tags -/

/-- A PQXDH event is logged at position `j` of `T`. -/
def PQEvAt (T : ExecTrace) (j : Nat) : Prop :=
  ∃ e : IkPQEvEntry, (T.at? j : Option IkPQEvEntry) = some e

/-- Identity secret drawn at `t` (`registerIdentity`: the next entry is a PQXDH event). -/
def IkAt (T : ExecTrace) (t : Nat) : Prop := PQEvAt T (t + 1)

/-- Signed-prekey secret drawn at `t` (`genSignedPrekey`: a nonce draw, then a PQXDH event). -/
def SpkAt (T : ExecTrace) (t : Nat) : Prop := ¬ PQEvAt T (t + 1) ∧ PQEvAt T (t + 2)

/-- One-time-prekey secret drawn at `t` (`genOneTimePrekey`: the next entry is a PQXDH event). -/
def OpkAt (T : ExecTrace) (t : Nat) : Prop := PQEvAt T (t + 1)

/-- Alice's base secret drawn at `t` (`aliceHandshake`/`aliceStart`: two more draws). -/
def EkAt (T : ExecTrace) (t : Nat) : Prop := ¬ PQEvAt T (t + 1) ∧ ¬ PQEvAt T (t + 2)

theorem ikAt_spkAt_false (T : ExecTrace) : ∀ t, IkAt T t → SpkAt T t → False :=
  fun _ hi hs => hs.1 hi

theorem ekAt_ikAt_false (T : ExecTrace) : ∀ t, EkAt T t → IkAt T t → False :=
  fun _ he hi => he.1 hi

theorem ekAt_spkAt_false (T : ExecTrace) : ∀ t, EkAt T t → SpkAt T t → False :=
  fun _ he hs => he.2 hs.2

theorem ekAt_opkAt_false (T : ExecTrace) : ∀ t, EkAt T t → OpkAt T t → False :=
  fun _ he ho => he.1 ho

/-! ## Hole helpers -/

theorem rkHole_true_intro {rk pk' pk₀' : DY.Bytes} {t : Nat} (h : TopDhSecret rk pk₀' t) :
    RkHole true rk (dh pk' (randTerm t 32)) := by
  simp only [RkHole]
  exact ⟨pk', pk₀', t, rfl, h⟩

theorem rkHole_false_intro {rk pk' : DY.Bytes} {t₀ t₁ : Nat} (h : TopDhSecret rk pk' t₀)
    (hne : t₀ ≠ t₁) : RkHole false rk (dh pk' (randTerm t₁ 32)) := by
  simp only [RkHole]
  exact ⟨pk', t₀, t₁, rfl, h, hne⟩

theorem topDhSecret_kdfRk {r₀ pk' : DY.Bytes} {t : Nat} :
    TopDhSecret (kdfRk r₀ (dh pk' (randTerm t 32))).1 pk' t := by
  unfold TopDhSecret
  exact Or.inl ⟨r₀, rfl⟩

theorem topDhSecret_pqxdh {pk' dh2 dh3 ss : DY.Bytes} {dh4 : Option DY.Bytes} {t : Nat} :
    TopDhSecret (pqxdhKdf (pqxdhIkm (dh pk' (randTerm t 32)) dh2 dh3 dh4 ss)).rk pk' t := by
  unfold TopDhSecret
  exact Or.inr ⟨dh2, dh3, dh4, ss, rfl⟩

/-! ## Logged handshake IKMs -/

/-- `ikm` is the PQXDH input key material of `keys`, paired with `ct`, with role-`c` DH holes. -/
def CtKeysIkmR (T : ExecTrace) (c : Bool) (ct : DY.Bytes)
    (keys : DY.Libsignal.PQXDH.HandshakeKeys) (ikm : DY.Bytes) : Prop :=
  match c with
  | false =>
    ∃ (pk e a b e' : DY.Bytes) (d : Option DY.Bytes),
      ct = (DY.PQKem.kemEncap pk e).1 ∧ ikm = pqxdhIkm a b e' d (DY.PQKem.kemEncap pk e).2 ∧
      keys = pqxdhKdf ikm ∧ IkmRoleHoles (IkAt T) (SpkAt T) (OpkAt T) (EkAt T) false a b e' d
  | true =>
    ∃ (ss a b e' : DY.Bytes) (d : Option DY.Bytes),
      KemLeaf ss ∧ ikm = pqxdhIkm a b e' d ss ∧
      keys = pqxdhKdf ikm ∧ IkmRoleHoles (IkAt T) (SpkAt T) (OpkAt T) (EkAt T) true a b e' d

/-- `ikm` is an input key material of a role-`c` handshake-completion event. -/
def DoneIkmRk (T : ExecTrace) (c : Bool) (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (ikm : DY.Bytes) : Prop :=
  match c, ev with
  | false, .AliceDone _ _ _ _ _ _ _ _ ct keys => CtKeysIkmR T false ct keys ikm
  | true, .BobDone _ _ _ _ _ _ _ _ ct keys => CtKeysIkmR T true ct keys ikm
  | _, _ => False

/-- Role-indexed input key materials of handshake-completion events logged in `T`. -/
def LoggedIkmRk (T : ExecTrace) (c : Bool) (ikm : DY.Bytes) : Prop :=
  ∃ ev, LoggedPQEv T ev ∧ DoneIkmRk T c ev ikm

theorem roleHoles_of_ctKeysIkmR {T : ExecTrace} {c : Bool} {ct m : DY.Bytes}
    {keys : DY.Libsignal.PQXDH.HandshakeKeys} (h : CtKeysIkmR T c ct keys m) :
    ∃ (a b e : DY.Bytes) (d : Option DY.Bytes) (ss : DY.Bytes),
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles (IkAt T) (SpkAt T) (OpkAt T) (EkAt T) c a b e d ∧
      KemLeaf ss := by
  cases c
  · obtain ⟨pk, e, a, b, e', d, _, hm, _, hr⟩ := h
    exact ⟨a, b, e', d, _, hm, hr, .inl ⟨pk, e, rfl⟩⟩
  · obtain ⟨ss, a, b, e', d, hss, hm, _, hr⟩ := h
    exact ⟨a, b, e', d, ss, hm, hr, hss⟩

theorem loggedIkmRk_roleHoles {T : ExecTrace} {c : Bool} {m : DY.Bytes} (h : LoggedIkmRk T c m) :
    ∃ (a b e : DY.Bytes) (d : Option DY.Bytes) (ss : DY.Bytes),
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles (IkAt T) (SpkAt T) (OpkAt T) (EkAt T) c a b e d ∧
      KemLeaf ss := by
  obtain ⟨ev, _, hd⟩ := h
  cases c <;> cases ev <;> simp only [DoneIkmRk] at hd <;>
    first | exact hd.elim | exact roleHoles_of_ctKeysIkmR hd

/-! ## Entry invariants -/

/-- Honest-spine invariant of a session state stored at trace position `j`. -/
structure SpStateRk (B : Bool → DY.Bytes → Prop) (j : Nat) (st : TRState) : Prop where
  rk : SpineRk B true st.rk
  cks : SpineRk B true st.cks
  recv : ∀ c ∈ st.recv, SpineRk B false c.chainKey
  dhs : ∃ (t : Nat) (pk' : DY.Bytes), t < j ∧ st.dhs = randTerm t 32 ∧ TopDhSecret st.rk pk' t

theorem SpStateRk.mono_idx {B : Bool → DY.Bytes → Prop} {j j' : Nat} {st : TRState}
    (h : SpStateRk B j st) (hj : j ≤ j') : SpStateRk B j' st := by
  obtain ⟨t, pk', ht, h1, h2⟩ := h.dhs
  exact ⟨h.rk, h.cks, h.recv, ⟨t, pk', by omega, h1, h2⟩⟩

theorem SpStateRk.mono {B B' : Bool → DY.Bytes → Prop} {j : Nat} {st : TRState}
    (h : SpStateRk B j st) (hB : ∀ c m, B c m → B' c m) : SpStateRk B' j st :=
  ⟨SpineRk.mono hB h.rk, SpineRk.mono hB h.cks, fun c hc => SpineRk.mono hB (h.recv c hc), h.dhs⟩

/-- Stored PQXDH secrets (stored at position `j`): DH secrets are 32-byte draws at a position
`t < j` carrying the role tag of their kind. -/
def PQSkAt (T : ExecTrace) (j : Nat) (st : DY.Libsignal.PQXDH.PQXDHState) : Prop :=
  match st.kind with
  | .identity => ∃ t, t < j ∧ st.sk = randTerm t 32 ∧ IkAt T t
  | .signedPrekey => ∃ t, t < j ∧ st.sk = randTerm t 32 ∧ SpkAt T t
  | .oneTimePrekey => ∃ t, t < j ∧ st.sk = randTerm t 32 ∧ OpkAt T t
  | .pqPrekey => True

theorem PQSkAt.mono {T : ExecTrace} {j j' : Nat} {st : DY.Libsignal.PQXDH.PQXDHState}
    (h : PQSkAt T j st) (hj : j ≤ j') : PQSkAt T j' st := by
  rcases st with ⟨kind, sk⟩
  cases kind <;> simp only [PQSkAt] at h ⊢
  all_goals first
    | trivial
    | (obtain ⟨t, ht, hsk, hr⟩ := h; exact ⟨t, by omega, hsk, hr⟩)

/-- Per-entry invariant at position `j`, relative to the final trace `T`. -/
def SpEntryOkR (T : ExecTrace) (j : Nat) (ent : ExecTrace.Entry) : Prop :=
  (∀ e : IkStEntry, TraceEntryHas.proj ent = some e → SpStateRk (LoggedIkmRk T) j e.st.state) ∧
  (∀ e : IkPQStEntry, TraceEntryHas.proj ent = some e → PQSkAt T j e.st.state)

def TraceOkR (T tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), SpEntryOkR T j (tr.at j hj)

theorem traceOkR_nil (T : ExecTrace) : TraceOkR T (DY.Trace.nil : ExecTrace) :=
  fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj

theorem traceOkR_append {T : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hent : SpEntryOkR T tr.length (TraceEntryHas.inj e)) (htr : TraceOkR T tr) :
    TraceOkR T (tr.append e) := by
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

private theorem lt_len_of_at_eq_rk {tr T : ExecTrace} {j : Nat} {hj : j < tr.length}
    {hT : j < T.length} (_ : tr.at j hj = T.at j hT) : j < T.length := hT

theorem traceLen_le_of_le_rk {tr T : ExecTrace} (h : tr ≤ T) : tr.length ≤ T.length := by
  rcases Nat.eq_zero_or_pos tr.length with h0 | hpos
  · omega
  · have hj : tr.length - 1 < tr.length := by omega
    have := lt_len_of_at_eq_rk (DY.Trace.at_le tr T (tr.length - 1) hj h)
    omega

theorem append_length_rk {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem not_pqEvAt_of_append {E : Type} [ExecTraceTypes.Has E] {tr T : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option IkPQEvEntry) =
      none)
    (hT : tr.append e ≤ T) : ¬ PQEvAt T tr.length := by
  rintro ⟨ev, hev⟩
  have hlt : tr.length < (tr.append e).length := by rw [append_length_rk]; omega
  unfold DY.Trace.at? at hev
  split at hev
  · rw [← DY.Trace.at_le (tr.append e) T tr.length hlt hT] at hev
    have hat : (tr.append e).at tr.length hlt = TraceEntryHas.inj e := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2]
    rw [hat, hnone] at hev
    cases hev
  · cases hev

/-! ## Exact-length and floor combinators -/

/-- Monad combinator for `TraceOkR T`, on runs from a trace of length `n` whose output trace is a
prefix of `T`; `Q` sees the result and the output trace length. -/
def TracefulR {α : Type} (T : ExecTrace) (n : Nat) (Q : α → Nat → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, tr.length = n → (x.run tr).2.val ≤ T → TraceOkR T tr →
    TraceOkR T (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a (x.run tr).2.val.length

/-- Floor form: `TracefulR T n Q x` for every input length `n ≥ k`. -/
def TracefulF {α : Type} (T : ExecTrace) (k : Nat) (Q : α → Nat → Prop) (x : Traceful α) : Prop :=
  ∀ n, k ≤ n → TracefulR T n Q x

section Combinators

variable {T : ExecTrace}

private theorem run_bind_fst_rk {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd_rk {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem TracefulR.pure {α : Type} {n : Nat} {Q : α → Nat → Prop} {a : α} (ha : Q a n) :
    TracefulR T n Q (Pure.pure a) := by
  intro tr hn _ htr
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb
  subst hn
  exact ha

theorem TracefulR.failure {α : Type} {n : Nat} {Q : α → Nat → Prop} :
    TracefulR T n Q (Alternative.failure : Traceful α) := by
  intro tr _ _ htr
  rw [DY.Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

theorem TracefulR.bind {α β : Type} {n : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulR T n Q₁ x) (hf : ∀ (a : α) (m : Nat), n ≤ m → Q₁ a m → TracefulR T m Q₂ (f a)) :
    TracefulR T n Q₂ (x >>= f) := by
  intro tr hn hT htr
  rw [run_bind_snd_rk] at hT
  rw [run_bind_snd_rk, run_bind_fst_rk]
  revert hT
  cases hres : (x.run tr).1 with
  | none =>
    intro hT
    exact ⟨(hx tr hn hT htr).1, fun _ hb => by cases hb⟩
  | some a =>
    intro hT
    have hT1 : (x.run tr).2.val ≤ T :=
      DY.Trace.le_trans _ _ _ ((f a).run (x.run tr).2.val).2.property hT
    have h1 := hx tr hn hT1 htr
    have hle : n ≤ (x.run tr).2.val.length := by
      rw [← hn]; exact traceLen_le_of_le_rk (x.run tr).2.property
    exact hf a _ hle (h1.2 a hres) _ rfl hT h1.1

theorem TracefulR.mono {α : Type} {n : Nat} {Q Q' : α → Nat → Prop} {x : Traceful α}
    (hx : TracefulR T n Q x) (h : ∀ a m, Q a m → Q' a m) : TracefulR T n Q' x :=
  fun tr hn hT htr => ⟨(hx tr hn hT htr).1, fun a ha => h a _ ((hx tr hn hT htr).2 a ha)⟩

theorem TracefulR.guardP {n : Nat} (p : Prop) [Decidable p] :
    TracefulR T n (fun _ m => p ∧ m = n) (_root_.guard p) := by
  unfold _root_.guard
  split
  · next h => exact TracefulR.pure ⟨h, rfl⟩
  · exact TracefulR.failure

theorem TracefulR.bindF {α β : Type} {n : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulR T n Q₁ x) (hf : ∀ (a : α) (m : Nat), n ≤ m → Q₁ a m → TracefulF T m Q₂ (f a)) :
    TracefulR T n Q₂ (x >>= f) :=
  TracefulR.bind hx fun a m hm hq => (hf a m hm hq) m (Nat.le_refl m)

theorem TracefulF.pure {α : Type} {k : Nat} {Q : α → Nat → Prop} {a : α}
    (ha : ∀ n, k ≤ n → Q a n) : TracefulF T k Q (Pure.pure a) :=
  fun n hn => TracefulR.pure (ha n hn)

theorem TracefulF.failure {α : Type} {k : Nat} {Q : α → Nat → Prop} :
    TracefulF T k Q (Alternative.failure : Traceful α) :=
  fun _ _ => TracefulR.failure

theorem TracefulF.bind {α β : Type} {k : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulF T k Q₁ x) (hf : ∀ (a : α) (m : Nat), k ≤ m → Q₁ a m → TracefulF T k Q₂ (f a)) :
    TracefulF T k Q₂ (x >>= f) :=
  fun n hn => TracefulR.bind (hx n hn) fun a m hm hq => hf a m (by omega) hq m (by omega)

theorem TracefulF.bindD {α β : Type} {k : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulF T k Q₁ x) (hf : ∀ (a : α) (m : Nat), k ≤ m → Q₁ a m → TracefulF T m Q₂ (f a)) :
    TracefulF T k Q₂ (x >>= f) :=
  fun n hn => TracefulR.bind (hx n hn) fun a m hm hq => hf a m (by omega) hq m (Nat.le_refl m)

theorem TracefulF.bindE {α β : Type} {k : Nat} {Q₁ : α → Nat → Prop} {Q₂ : β → Nat → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulF T k Q₁ x) (hf : ∀ (a : α) (m : Nat), k ≤ m → Q₁ a m → TracefulR T m Q₂ (f a)) :
    TracefulF T k Q₂ (x >>= f) :=
  fun n hn => TracefulR.bind (hx n hn) fun a m hm hq => hf a m (by omega) hq

theorem TracefulF.guard {k : Nat} (p : Prop) [Decidable p] :
    TracefulF T k (fun _ _ => p) (_root_.guard p) :=
  fun _ _ => (TracefulR.guardP p).mono fun _ _ h => h.1

end Combinators

/-! ## Primitive steps -/

section Steps

variable {T : ExecTrace} {k : Nat}

theorem tracefulF_guardTrace (p : ExecTrace → Bool) :
    TracefulF T k (fun _ _ => True) (guardTrace p) := by
  intro _ _ tr _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulF_traceLength : TracefulF T k (fun _ _ => True) traceLength := by
  intro _ _ tr _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulF_guardOnTrace (p : ExecTrace → Bool) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ _ tr _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulF.getEntry_any {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulF T k (fun (_ : E) _ => True) (getEntry j : Traceful E) := by
  intro _ _ tr _ _ htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulF.getEntry_st (j : Nat) :
    TracefulF T k (fun (e : IkStEntry) m => SpStateRk (LoggedIkmRk T) m e.st.state)
      (getEntry j) := by
  intro _ _ tr _ _ htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  change (tr.at? j : Option IkStEntry) = some e at he
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact ((htr j hj).1 e he).mono_idx (Nat.le_of_lt hj)
  · cases he

theorem TracefulF.getEntry_pq (j : Nat) :
    TracefulF T k (fun (e : IkPQStEntry) m => PQSkAt T m e.st.state) (getEntry j) := by
  intro _ _ tr _ _ htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  change (tr.at? j : Option IkPQStEntry) = some e at he
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact ((htr j hj).2 e he).mono (Nat.le_of_lt hj)
  · cases he

theorem TracefulF.receiveMessage (j : Nat) :
    TracefulF T k (fun _ _ => True) (Network.receiveMessage j) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TracefulF.bind (TracefulF.getEntry_any j) fun _ _ _ _ => TracefulF.pure fun _ _ => trivial

theorem tracefulF_receiveSignalMsg (j : Nat) :
    TracefulF T k (fun _ _ => True) (receiveSignalMsg j) := by
  unfold receiveSignalMsg
  refine TracefulF.bind (TracefulF.receiveMessage j) fun b _ _ _ => ?_
  split
  · exact TracefulF.bind (TracefulF.guard _) fun _ _ _ _ => TracefulF.pure fun _ _ => trivial
  · exact TracefulF.failure

theorem TracefulF.getLocalState (p : Participant) (j : Nat) :
    TracefulF T k (fun (st : TRState) m => SpStateRk (LoggedIkmRk T) m st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulF.bindD
    (TracefulF.bindD (TracefulF.getEntry_st j) fun _ _ _ he =>
      TracefulF.pure
        (Q := fun (ls : PersistentLocalState.LocalState TRState) n =>
          SpStateRk (LoggedIkmRk T) n ls.state)
        fun _ hn => he.mono_idx hn)
    fun _ _ _ hst => ?_
  exact TracefulF.bind (TracefulF.guard _) fun _ _ _ _ =>
    TracefulF.pure fun _ hn => hst.mono_idx hn

theorem TracefulF.getLocalStatePQ (p : Participant) (j : Nat) :
    TracefulF T k (fun (st : DY.Libsignal.PQXDH.PQXDHState) m => PQSkAt T m st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulF.bindD
    (TracefulF.bindD (TracefulF.getEntry_pq j) fun _ _ _ he =>
      TracefulF.pure
        (Q := fun (ls : PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) n =>
          PQSkAt T n ls.state)
        fun _ hn => he.mono hn)
    fun _ _ _ hst => ?_
  exact TracefulF.bind (TracefulF.guard _) fun _ _ _ _ =>
    TracefulF.pure fun _ hn => hst.mono hn

theorem TracefulF.getKey (p : Participant) (j : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    TracefulF T k (fun (sk : DY.Bytes) m => PQSkAt T m { kind := kind, sk := sk })
      (DY.Libsignal.PQXDH.getKey p j kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine TracefulF.bindD (TracefulF.getLocalStatePQ p j) fun st _ _ hst => ?_
  refine TracefulF.bind (TracefulF.guard _) fun _ _ _ hk => TracefulF.pure fun _ hn => ?_
  rcases st with ⟨kind', sk⟩
  obtain rfl : kind' = kind := hk
  exact hst.mono hn

theorem TracefulF.lookupIdentity (p : Participant) (j : Nat) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulF.bind (TracefulF.getEntry_any j) fun e _ _ _ => ?_
  split
  · exact TracefulF.bind (TracefulF.guard _) fun _ _ _ _ => TracefulF.pure fun _ _ => trivial
  · exact TracefulF.failure

theorem TracefulR.genRand {n : Nat} (size : Nat) :
    TracefulR T n (fun b m => b = randTerm n size ∧ ¬ PQEvAt T n ∧ m = n + 1)
      (DY.Random.genRand size) := by
  intro tr hn hT htr
  have hrun : (DY.Random.genRand size).run tr =
      (some (randTerm tr.length size),
       ⟨tr.append (⟨size⟩ : DY.Random.ExecEntryT), DY.Trace.append_le _ _⟩) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
    rfl
  rw [hrun] at hT ⊢
  refine ⟨traceOkR_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun a ha => ?_⟩
  injection ha with ha
  subst ha hn
  exact ⟨rfl, not_pqEvAt_of_append (e := (⟨size⟩ : DY.Random.ExecEntryT)) rfl hT,
    append_length_rk tr _⟩

theorem TracefulF.genRand (size : Nat) :
    TracefulF T k (fun b m => ∃ L, k ≤ L ∧ m = L + 1 ∧ b = randTerm L size ∧ ¬ PQEvAt T L)
      (DY.Random.genRand size) :=
  fun n hn => (TracefulR.genRand (n := n) size).mono fun _ _ h => ⟨n, hn, h.2.2, h.1, h.2.1⟩

theorem TracefulF.sendMessage (msg : DY.Bytes) :
    TracefulF T k (fun _ _ => True) (Network.sendMessage msg) := by
  intro _ _ tr _ _ htr
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact ⟨traceOkR_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulF.logEvent (ev : TREvent) :
    TracefulF T k (fun _ _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro _ _ tr _ _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceOkR_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulF.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulF T k (fun _ _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro _ _ tr _ _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceOkR_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulR.logEventPQ {n : Nat} (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    TracefulR T n (fun _ m => PQEvAt T n ∧ LoggedPQEv T ev ∧ m = n + 1)
      (DY.ProtocolEvent.logEvent ev) := by
  intro tr hn hT htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1] at hT ⊢
  refine ⟨traceOkR_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => ?_⟩
  subst hn
  have hat := at?_of_le hT (at?_append_self tr ({ ev := ev } : IkPQEvEntry))
  exact ⟨⟨_, hat⟩, ⟨tr.length, { ev := ev }, hat, rfl⟩, append_length_rk tr _⟩

theorem TracefulF.logEventPQ (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    TracefulF T k (fun _ _ => LoggedPQEv T ev) (DY.ProtocolEvent.logEvent ev) :=
  fun n _ => (TracefulR.logEventPQ (n := n) ev).mono fun _ _ h => h.2.1

theorem TracefulF.storeLocalState (p : Participant) {st : TRState}
    (hst : SpStateRk (LoggedIkmRk T) k st) :
    TracefulF T k (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro n hn tr hlen _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨traceOkR_append ⟨?_, fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst.mono_idx (by omega)

theorem TracefulF.storeLocalStatePQ (p : Participant) {st : DY.Libsignal.PQXDH.PQXDHState}
    (hst : PQSkAt T k st) :
    TracefulF T k (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro n hn tr hlen _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨traceOkR_append ⟨fun _ h => (by cases h), ?_⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst.mono (by omega)

end Steps

/-! ## Double Ratchet key schedule -/

section DR

variable {B : Bool → DY.Bytes → Prop}

/-- Chains of `recvChainFor` are spine terms at the receiving index: a fresh chain is a
`kdfRk st.rk (dh pk st.dhs)` step whose hole secret is the state's own `dhs` draw. -/
theorem spineRk_recvChainFor {j : Nat} {st : TRState} {pk : DY.Bytes} {c : RecvChain} {b : Bool}
    (hst : SpStateRk B j st) (hrc : recvChainFor st.toDRState pk = some (c, b)) :
    SpineRk B false c.chainKey := by
  unfold recvChainFor at hrc
  rcases hfind : findRecvChain st.toDRState.recv pk with _ | c₀
  · rw [hfind] at hrc; dsimp only at hrc
    split at hrc
    · cases hrc
    · injection hrc with hrc
      rcases Prod.mk.inj hrc with ⟨rfl, _⟩
      obtain ⟨t, pk₀', _, hdhs, htop⟩ := hst.dhs
      have hh : RkHole true st.rk (dh (DY.X25519.normalizeX25519Key pk) st.dhs) := by
        rw [hdhs]; exact rkHole_true_intro htop
      exact SpineRk.rkStep2 hst.rk hh
  · rw [hfind] at hrc
    injection hrc with hrc
    rcases Prod.mk.inj hrc with ⟨rfl, _⟩
    unfold findRecvChain at hfind
    exact hst.recv _ (List.mem_of_find?_eq_some hfind)

theorem spineRk_consumeMessageKey {b : Bool} {c c' : RecvChain} {counter : UInt32}
    {seed : DY.Bytes} (hc : SpineRk B b c.chainKey)
    (hcm : consumeMessageKey c counter = some (seed, c')) :
    SpineRk B b seed ∧ SpineRk B b c'.chainKey := by
  unfold consumeMessageKey at hcm
  split at hcm
  · cases hcm
  · split at hcm
    · cases hcm
    · split at hcm
      · cases hcm
      · injection hcm with hcm
        rcases Prod.mk.inj hcm with ⟨rfl, rfl⟩
        have hck := spineRk_chainKeyAt hc (counter.toNat - c.index.toNat)
        exact ⟨.ckStep2 hck, .ckStep1 hck⟩

theorem spStateRk_setRecv {j : Nat} {st : TRState} {c' : RecvChain} (hst : SpStateRk B j st)
    (hc' : SpineRk B false c'.chainKey) (spqr : DY.Bytes) :
    SpStateRk B j { st with recv := setRecvChain st.recv c', spqr := spqr } := by
  refine ⟨hst.rk, hst.cks, fun c hc => ?_, hst.dhs⟩
  have hc2 : c ∈ setRecvChain st.recv c' := hc
  unfold setRecvChain at hc2
  obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc2
  split at heq <;> subst heq
  · exact hc'
  · exact hst.recv c₀ hc₀

theorem spStateRk_send {j : Nat} {st : TRState} (hst : SpStateRk B j st) (ns : UInt32)
    (spqr : DY.Bytes) :
    SpStateRk B j { st with cks := (kdfCk st.cks).1, ns := ns, spqr := spqr } :=
  ⟨hst.rk, .ckStep1 hst.cks, hst.recv, hst.dhs⟩

theorem spStateRk_spqr {j : Nat} {st : TRState} (hst : SpStateRk B j st) (spqr : DY.Bytes) :
    SpStateRk B j { st with spqr := spqr } :=
  ⟨hst.rk, hst.cks, hst.recv, hst.dhs⟩

theorem spineRk_of_recvSeed {j : Nat} {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes}
    (hst : SpStateRk B j st) (hseed : recvSeed st msg = some seed) : SpineRk B false seed := by
  unfold recvSeed at hseed
  split at hseed
  · rcases hrc : recvChainFor st.toDRState msg.ratchetKey with _ | ⟨c, b⟩
    · rw [hrc] at hseed; cases hseed
    · rw [hrc] at hseed; dsimp only at hseed
      rcases hcm : consumeMessageKey c msg.counter with _ | ⟨s, c'⟩
      · rw [hcm] at hseed; cases hseed
      · rw [hcm] at hseed
        injection hseed with hseed; subst hseed
        exact (spineRk_consumeMessageKey (spineRk_recvChainFor hst hrc) hcm).1
  · cases hseed

variable {T : ExecTrace}

/-- `dhRatchetStep` from a state stored before the floor `k`: the fresh `dhs` draw sits at a
position `L ≥ k`, so it differs from the state's old `dhs` position `t < k` (`RkHole false`). -/
theorem tracefulF_dhRatchetStep {k : Nat} {st : TRState} {pk : DY.Bytes}
    (hst : SpStateRk B k st) :
    TracefulF T k (fun (p : TRState × RecvChain) m => SpStateRk B m p.1 ∧
      SpineRk B false p.2.chainKey) (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulF.bind (TracefulF.guard _) fun _ _ _ _ => ?_
  refine TracefulF.bindD (TracefulF.genRand 32) fun dhs' m _ hg => ?_
  obtain ⟨L, hkL, hm, hdhs', _⟩ := hg
  obtain ⟨t, pk₀', htk, hdhs, htop⟩ := hst.dhs
  have hh1 : RkHole true st.rk (dh (DY.X25519.normalizeX25519Key pk) st.dhs) := by
    rw [hdhs]; exact rkHole_true_intro htop
  have hrk1 : SpineRk B false (createChain st.rk pk st.dhs).1 := SpineRk.rkStep1 hst.rk hh1
  have hckr : SpineRk B false (createChain st.rk pk st.dhs).2 := SpineRk.rkStep2 hst.rk hh1
  have htop1 : TopDhSecret (createChain st.rk pk st.dhs).1 (DY.X25519.normalizeX25519Key pk) t := by
    rw [hdhs]; exact topDhSecret_kdfRk
  have hh2 : RkHole false (createChain st.rk pk st.dhs).1 (dh (DY.X25519.normalizeX25519Key pk) dhs') := by
    rw [hdhs']; exact rkHole_false_intro htop1 (by omega)
  have htop2 : TopDhSecret (createChain (createChain st.rk pk st.dhs).1 pk dhs').1
      (DY.X25519.normalizeX25519Key pk) L := by
    rw [hdhs']; exact topDhSecret_kdfRk
  refine TracefulF.pure fun n hn => ⟨⟨SpineRk.rkStep1 hrk1 hh2, SpineRk.rkStep2 hrk1 hh2,
    fun c' hc' => ?_, ⟨L, _, by omega, hdhs', htop2⟩⟩, hckr⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst.recv c' hmem
  · rcases List.mem_singleton.mp hmem with rfl
    exact hckr

theorem tracefulF_ensureReceiverChain {k : Nat} {st : TRState} {pk : DY.Bytes}
    (hst : SpStateRk B k st) :
    TracefulF T k
      (fun (p : TRState × RecvChain × Bool) m => SpStateRk B m p.1 ∧
        SpineRk B false p.2.1.chainKey)
      (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · next c hr => exact TracefulF.pure fun _ hn => ⟨hst.mono_idx hn, spineRk_recvChainFor hst hr⟩
  · exact TracefulF.bindD (tracefulF_dhRatchetStep hst) fun ⟨_, _⟩ _ _ h =>
      TracefulF.pure fun _ hn => ⟨h.1.mono_idx hn, h.2⟩
  · exact TracefulF.failure

end DR

/-! ## Triple Ratchet transitions -/

section TR

variable {T : ExecTrace}

theorem tracefulF_logMessageKeyAndStore {k : Nat} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : SpStateRk (LoggedIkmRk T) k st) :
    TracefulF T k (fun _ _ => True)
      (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
    TracefulF.storeLocalState me hst

theorem tracefulF_logSkippedKeys {k : Nat} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (cnt : Nat) :
    TracefulF T k (fun _ _ => True) (logSkippedKeys s pk rIdx src ck n cnt) := by
  induction cnt generalizing ck n with
  | zero =>
    unfold logSkippedKeys
    exact TracefulF.pure fun _ _ => trivial
  | succ cnt ih =>
    unfold logSkippedKeys
    exact TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => ih (kdfCk ck).1 (n + 1)

theorem tracefulF_verifyMacAndDecrypt {k : Nat} (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    TracefulF T k (fun _ _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulF.bind (TracefulF.guard _) fun _ _ _ _ => ?_
  intro _ _ _ _ _ htr
  erw [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulF_messageEncrypt {k : Nat} (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulF T k (fun _ _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  refine TracefulF.bindD (TracefulF.getLocalState me stateIdx) fun st m _ hst =>
    TracefulF.bind (TracefulF.guard _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.genRand 32) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.genRand coinsLen) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.receiveMessage pqIdx) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
    TracefulF.bind (tracefulF_logMessageKeyAndStore me _ .sender _ _ _ _ _
      (spStateRk_send hst _ _)) fun _ _ _ _ =>
      TracefulF.sendMessage _

theorem tracefulF_messageEncryptAbort {k : Nat} (me : Participant) (stateIdx : Nat) :
    TracefulF T k (fun _ _ => True) (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact TracefulF.bind (TracefulF.getLocalState me stateIdx) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.genRand 32) fun _ _ _ _ => TracefulF.failure

theorem tracefulF_messageDecrypt {k : Nat} (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulF T k (fun _ _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulF.bindD (TracefulF.getLocalState me stateIdx) fun st₀ m₀ _ hst₀ =>
    TracefulF.bind (tracefulF_receiveSignalMsg msgIdx) fun msg _ _ _ =>
    TracefulF.bindD (tracefulF_ensureReceiverChain (hst₀.mono_idx (Nat.le_refl m₀)))
      fun ⟨st, c, ratcheted⟩ m₁ _ hst => ?_
  dsimp only
  split
  · next seed c' hcm =>
    have hc' := (spineRk_consumeMessageKey (c := c) hst.2 hcm).2
    split
    · next spqr' key _ =>
      refine TracefulF.bind (TracefulF.sendMessage key) fun _ _ _ _ =>
        TracefulF.bind (TracefulF.receiveMessage pqIdx) fun pqSalt _ _ _ =>
        TracefulF.bind (tracefulF_verifyMacAndDecrypt st msg pqSalt seed) fun mm _ _ _ => ?_
      have hrest :
          TracefulF T m₁ (fun _ _ => True)
            (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                  (msg.counter.toNat - c.index.toNat)
                DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter mm)
                logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt
                  msg.counter c.rIdx stateIdx
                  { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulF.bind (tracefulF_logSkippedKeys _ _ _ _ _ _ _) fun _ _ _ _ =>
          TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
            tracefulF_logMessageKeyAndStore me _ .receiver _ _ _ _ _
              (spStateRk_setRecv hst.1 hc' spqr')
      split
      · exact TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
          TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => hrest
      · exact hrest
    · exact TracefulF.failure
  · exact TracefulF.failure

theorem tracefulF_messageDecryptSkipped {k : Nat} (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulF T k (fun _ _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulF.bindD (TracefulF.getLocalState me stateIdx) fun st _ _ hst =>
    TracefulF.bind (tracefulF_receiveSignalMsg msgIdx) fun msg _ _ _ =>
    TracefulF.bind (TracefulF.getEntry_any skippedKeyEventIdx) fun _ _ _ _ => ?_
  split
  · refine TracefulF.bind (TracefulF.guard _) fun _ _ _ _ =>
      TracefulF.bind (tracefulF_guardTrace _) fun _ _ _ _ => ?_
    split
    · next spqr' key _ =>
      exact TracefulF.bind (TracefulF.sendMessage key) fun _ _ _ _ =>
        TracefulF.bind (TracefulF.receiveMessage pqIdx) fun pqSalt _ _ _ =>
        TracefulF.bind (tracefulF_verifyMacAndDecrypt st msg pqSalt _) fun _ _ _ _ =>
        TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
        TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
        tracefulF_logMessageKeyAndStore me _ .receiver _ _ _ _ _ (spStateRk_spqr hst spqr')
    · exact TracefulF.failure
  · exact TracefulF.failure

theorem tracefulF_exposeKey {k : Nat} (me : Participant) (stateIdx : Nat) (kc : KeyComponent) :
    TracefulF T k (fun _ _ => True) (exposeKey me stateIdx kc) := by
  unfold exposeKey
  refine TracefulF.bind (TracefulF.getLocalState me stateIdx) fun _ _ _ _ => ?_
  cases kc with
  | rk => exact TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => TracefulF.sendMessage _
  | dhs => exact TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => TracefulF.sendMessage _
  | cks => exact TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => TracefulF.sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => TracefulF.sendMessage _
    · exact TracefulF.failure

theorem tracefulF_exposeSpqr {k : Nat} (me : Participant) (stateIdx : Nat) :
    TracefulF T k (fun _ _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact TracefulF.bind (TracefulF.getLocalState me stateIdx) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => TracefulF.sendMessage _

theorem tracefulF_exposeSkipped {k : Nat} (skippedKeyEventIdx : Nat) :
    TracefulF T k (fun _ _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulF.bind (TracefulF.getEntry_any skippedKeyEventIdx) fun _ _ _ _ => ?_
  split
  · exact TracefulF.bind (tracefulF_guardTrace _) fun _ _ _ _ =>
      TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
      TracefulF.sendMessage _
  · exact TracefulF.failure

end TR

end Symbolic.Swarm.CREF.TR.G1.Spine
