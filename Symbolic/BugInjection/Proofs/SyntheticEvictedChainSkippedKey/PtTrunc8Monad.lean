/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Prim
public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import DY.Bytes.AttackerKnowledge
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
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
# Trace-Entry Invariant and Triple-Ratchet Transitions for `Trunc8RowOK`

Defines the trace invariant `TraceEntriesTrunc8` and monadic Hoare predicate `TTrunc`, proves
preservation combinators across trace primitives, and establishes `TTrunc` for all Triple-Ratchet
protocol operations.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Monad

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet
  (SessionInfo KeyDir KeyComponent RecvChain TRState TREvent TRSignalMsg parseTrSignalMsg
   createChain kdfCk chainKeyAt computeMac trHonestWireMsg
   findRecvChain setRecvChain recvChainFor consumeMessageKey)
open DY.Libsignal.PQXDH (KeyKind PQXDHState PQXDHEvent)
open DY.Libsignal.Composed (ComposedEvent)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost assumedInjective)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
  (memoOK_concat_elim memoOK_trWire_elim memoOK_of_attackerKnows)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (StEntry TREntry PQStEntry PQEvEntry CEvEntry)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Prim
  (TermTrunc8OK StateTrunc8 EventTrunc8 PQEventTrunc8
   termTrunc8OK_rand termTrunc8OK_concat termTrunc8OK_dhPk termTrunc8OK_symEnc
   termTrunc8OK_symDec termTrunc8OK_spqrSend termTrunc8OK_spqrRecv
   termTrunc8OK_createChain termTrunc8OK_kdfCk termTrunc8OK_chainKeyAt
   termTrunc8OK_trMsgKeys termTrunc8OK_computeMac termTrunc8OK_trHonestWireMsg)

section MonadAndTR
variable {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {T : ExecTrace}

def EntryTrunc8 (ent : ExecTrace.Entry) : Prop :=
  (∀ e : Network.ExecEntryT, TraceEntryHas.proj ent = some e → TermTrunc8OK i S g T e.msg) ∧
  (∀ e : StEntry, TraceEntryHas.proj ent = some e → StateTrunc8 (i := i) (S := S) (g := g) (T := T) e.st.state) ∧
  (∀ e : TREntry, TraceEntryHas.proj ent = some e → EventTrunc8 (i := i) (S := S) (g := g) (T := T) e.ev) ∧
  (∀ e : PQStEntry, TraceEntryHas.proj ent = some e → TermTrunc8OK i S g T e.st.state.sk) ∧
  (∀ e : PQEvEntry, TraceEntryHas.proj ent = some e → PQEventTrunc8 (i := i) (S := S) (g := g) (T := T) e.ev)

def TraceEntriesTrunc8 (tr : ExecTrace) : Prop :=
  (∀ b, tr.BaseAttackerKnows b → TermTrunc8OK i S g T b) ∧
  (∀ j (hj : j < tr.length), EntryTrunc8 (i := i) (S := S) (g := g) (T := T) (tr.at j hj))

theorem traceEntriesTrunc8_nil :
    TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) (DY.Trace.nil : ExecTrace) :=
  ⟨fun _ h => by rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1] at h; exact h.elim,
   fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj⟩

theorem traceEntriesTrunc8_knows {tr : ExecTrace} (hle : tr ≤ T)
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr)
    {b : DY.Bytes} (hkn : b.AttackerKnows tr) :
    TermTrunc8OK i S g T b :=
  memoOK_of_attackerKnows
    (fun x hak _ _ => Or.inl (DY.Bytes.AttackerKnows_le x.1 _ _ hle hak))
    (fun x hni t ht => by
      have hinj : assumedInjective t.pack = true := by
        unfold assumedInjective
        simp [DY.BytesView.view_pack]
      rw [← ht, hni] at hinj
      cases hinj)
    htr.1 hkn

private theorem traceEntriesTrunc8_append {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (hbase : ∀ b, (tr.append e).BaseAttackerKnows b → TermTrunc8OK i S g T b)
    (hent : EntryTrunc8 (i := i) (S := S) (g := g) (T := T) (TraceEntryHas.inj e))
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr) :
    TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) (tr.append e) := by
  refine ⟨hbase, fun j hj => ?_⟩
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt (DY.Trace.append_le tr e)]
    exact htr.2 j hlt
  · have heq : j = tr.length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj
      omega
    subst heq
    simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

private theorem traceEntriesTrunc8_at?_net {tr : ExecTrace}
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr)
    {j : Nat} {e : Network.ExecEntryT} (h : (tr.at? j : Option Network.ExecEntryT) = some e) :
    TermTrunc8OK i S g T e.msg := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).1 e h
  · cases h

theorem traceEntriesTrunc8_at?_st {tr : ExecTrace}
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr)
    {j : Nat} {e : StEntry} (h : (tr.at? j : Option StEntry) = some e) :
    StateTrunc8 (i := i) (S := S) (g := g) (T := T) e.st.state := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.1 e h
  · cases h

private theorem traceEntriesTrunc8_at?_tr {tr : ExecTrace}
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr)
    {j : Nat} {e : TREntry} (h : (tr.at? j : Option TREntry) = some e) :
    EventTrunc8 (i := i) (S := S) (g := g) (T := T) e.ev := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.1 e h
  · cases h

theorem traceEntriesTrunc8_at?_pqst {tr : ExecTrace}
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr)
    {j : Nat} {e : PQStEntry} (h : (tr.at? j : Option PQStEntry) = some e) :
    TermTrunc8OK i S g T e.st.state.sk := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.2.1 e h
  · cases h

private theorem traceEntriesTrunc8_at?_pqev {tr : ExecTrace}
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr)
    {j : Nat} {e : PQEvEntry} (h : (tr.at? j : Option PQEvEntry) = some e) :
    PQEventTrunc8 (i := i) (S := S) (g := g) (T := T) e.ev := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.2.2 e h
  · cases h

private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 = match (x.run tr).1 with | some a => ((f a).run (x.run tr).2.val).1 | none => none := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val = match (x.run tr).1 with | some a => ((f a).run (x.run tr).2.val).2.val | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

/-- Hoare-style preservation of `TraceEntriesTrunc8` (relative to ambient upper-bound trace `T`)
and postcondition `Q` across a `Traceful` computation `x`. -/
def TTrunc {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).2.val ≤ T → TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr →
    TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) (x.run tr).2.val ∧
    ∀ a, (x.run tr).1 = some a → Q a

theorem TTrunc.pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    TTrunc (i := i) (S := S) (g := g) (T := T) Q (Pure.pure a) := by
  intro tr _ htr; rw [Traceful.run_pure]; exact ⟨htr, fun _ hb => Option.some.inj hb ▸ ha⟩

theorem TTrunc.failure {α : Type} {Q : α → Prop} :
    TTrunc (i := i) (S := S) (g := g) (T := T) Q (Alternative.failure : Traceful α) := by
  intro tr _ htr; rw [Traceful.run_failure]; exact ⟨htr, fun _ hb => by cases hb⟩

theorem TTrunc.bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TTrunc (i := i) (S := S) (g := g) (T := T) Q₁ x)
    (hf : ∀ a, Q₁ a → TTrunc (i := i) (S := S) (g := g) (T := T) Q₂ (f a)) :
    TTrunc (i := i) (S := S) (g := g) (T := T) Q₂ (x >>= f) := by
  intro tr hle htr; rw [run_bind_snd] at hle ⊢; rw [run_bind_fst]; revert hle
  cases h1 : (x.run tr).1 with
  | none => intro hle; exact ⟨(hx tr hle htr).1, fun _ hb => by cases hb⟩
  | some a =>
    intro hle
    have h1' := hx tr (DY.Trace.le_trans _ _ _ ((f a).run (x.run tr).2.val).2.property hle) htr
    exact hf a (h1'.2 a h1) (x.run tr).2.val hle h1'.1

theorem TTrunc.guardP (p : Prop) {_ : Decidable p} :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (@_root_.guard Traceful _ p _) := by
  unfold _root_.guard; split
  · exact TTrunc.pure trivial
  · exact TTrunc.failure

theorem TTrunc.guardTrace (p : ExecTrace → Bool) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.guardTrace p) := by
  intro tr _ htr; unfold DY.Libsignal.TripleRatchet.guardTrace; erw [Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

theorem TTrunc.requireTracePredicate (p : ExecTrace → Bool) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  intro tr _ htr; unfold DY.Libsignal.PQXDH.guardTrace; simp only [Traceful.run_mk]; split <;> exact ⟨htr, fun _ _ => trivial⟩

theorem TTrunc.traceLength :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) DY.Libsignal.TripleRatchet.traceLength := by
  intro tr _ htr; unfold DY.Libsignal.TripleRatchet.traceLength; erw [Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

private theorem TTrunc.getEntry_net (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun e : Network.ExecEntryT => TermTrunc8OK i S g T e.msg) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesTrunc8_at?_net htr he⟩

private theorem TTrunc.getEntry_st (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun e : StEntry => StateTrunc8 (i := i) (S := S) (g := g) (T := T) e.st.state) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesTrunc8_at?_st htr he⟩

theorem TTrunc.getEntry_tr (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun e : TREntry => EventTrunc8 (i := i) (S := S) (g := g) (T := T) e.ev) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesTrunc8_at?_tr htr he⟩

private theorem TTrunc.getEntry_pqst (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun e : PQStEntry => TermTrunc8OK i S g T e.st.state.sk) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesTrunc8_at?_pqst htr he⟩

private theorem TTrunc.getEntry_pqev (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun e : PQEvEntry => PQEventTrunc8 (i := i) (S := S) (g := g) (T := T) e.ev) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesTrunc8_at?_pqev htr he⟩

theorem TTrunc.receiveMessage (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (TermTrunc8OK i S g T) (Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TTrunc.bind (TTrunc.getEntry_net j) fun _ he => TTrunc.pure he

theorem TTrunc.getLocalState (p : Participant) (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (StateTrunc8 (i := i) (S := S) (g := g) (T := T)) (PersistentLocalState.getLocalState p j) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact TTrunc.bind (TTrunc.bind (TTrunc.getEntry_st j) fun _ he =>
    TTrunc.pure (Q := fun ls : PersistentLocalState.LocalState TRState => StateTrunc8 (i := i) (S := S) (g := g) (T := T) ls.state) he)
    fun _ hst => TTrunc.bind (TTrunc.guardP _) fun _ _ => TTrunc.pure hst

private theorem TTrunc.getPQLocalState (p : Participant) (j : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun s : PQXDHState => TermTrunc8OK i S g T s.sk) (PersistentLocalState.getLocalState p j) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact TTrunc.bind (TTrunc.bind (TTrunc.getEntry_pqst j) fun _ he =>
    TTrunc.pure (Q := fun ls : PersistentLocalState.LocalState PQXDHState => TermTrunc8OK i S g T ls.state.sk) he)
    fun _ hst => TTrunc.bind (TTrunc.guardP _) fun _ _ => TTrunc.pure hst

theorem TTrunc.getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (TermTrunc8OK i S g T) (DY.Libsignal.PQXDH.getKey p stateIdx kind) :=
  TTrunc.bind (TTrunc.getPQLocalState p stateIdx) fun _ hst => TTrunc.bind (TTrunc.guardP _) fun _ _ => TTrunc.pure hst

theorem TTrunc.lookupIdentity (p : Participant) (regIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T)
      (fun kv : DY.Bytes × DY.Bytes => TermTrunc8OK i S g T kv.1 ∧ TermTrunc8OK i S g T kv.2)
      (DY.Libsignal.PQXDH.lookupIdentity p regIdx) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TTrunc.bind (TTrunc.getEntry_pqev regIdx) fun e he => ?_
  cases hev : e.ev with
  | IdentityRegistered p' _ _ _ => rw [hev] at he; exact TTrunc.bind (TTrunc.guardP (p' = p)) fun _ _ => TTrunc.pure he
  | _ => exact TTrunc.failure

private theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem TTrunc.genRand (n : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (TermTrunc8OK i S g T) (DY.Random.genRand n) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  refine ⟨traceEntriesTrunc8_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, ?_⟩
  · rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
    rcases hb with h0 | hb'
    · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (DY.Random.ExecEntryT.mk n) : ExecTrace.Entry) b).trans
        (Symbolic.DYBridge.DY.Random.baseAttackerKnowledge_attackerKnows tr (DY.Random.ExecEntryT.mk n) b)
      exact False.elim (Eq.mp h1 h0)
    · exact htr.1 b hb'
  · intro a ha; injection ha with ha; subst ha; exact termTrunc8OK_rand i S g T tr.length n

theorem TTrunc.sendMessage {msg : DY.Bytes} (hm : TermTrunc8OK i S g T msg) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (Network.sendMessage msg) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesTrunc8_append (fun b hb => ?_)
    ⟨(fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hm),
     (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (Network.ExecEntryT.mk msg) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows tr (Network.ExecEntryT.mk msg) b)
    exact (Eq.mp h1 h0) ▸ hm
  · exact htr.1 b hb'

theorem TTrunc.storeLocalState (p : Participant) {st : TRState}
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) st) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesTrunc8_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hst),
     (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · let e : ExecTrace.Entry := TraceEntryHas.inj (⟨⟨p, st⟩⟩ : StEntry)
    have h1 := (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal TRState) tr e.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal TRState) tr e.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState TRState) tr ⟨⟨p, st⟩⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'

theorem TTrunc.storePQLocalState (p : Participant) {st : PQXDHState}
    (hsk : TermTrunc8OK i S g T st.sk) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesTrunc8_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hsk),
     (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · let e : ExecTrace.Entry := TraceEntryHas.inj (⟨⟨p, st⟩⟩ : PQStEntry)
    have h1 := (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal PQXDHState) tr e.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal PQXDHState) tr e.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState PQXDHState) tr ⟨⟨p, st⟩⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'

theorem TTrunc.logEvent {ev : TREvent}
    (hev : EventTrunc8 (i := i) (S := S) (g := g) (T := T) ev) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  refine ⟨traceEntriesTrunc8_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hev),
     (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (⟨ev⟩ : TREntry) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows TREvent tr ⟨ev⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'

theorem TTrunc.logPQEvent {ev : PQXDHEvent}
    (hev : PQEventTrunc8 (i := i) (S := S) (g := g) (T := T) ev) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  refine ⟨traceEntriesTrunc8_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hev)⟩ htr,
    fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (⟨ev⟩ : PQEvEntry) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows PQXDHEvent tr ⟨ev⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'

theorem TTrunc.logCEvent (ev : ComposedEvent) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  refine ⟨traceEntriesTrunc8_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
     (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (⟨ev⟩ : CEvEntry) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows ComposedEvent tr ⟨ev⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'

def TRSignalMsgTrunc8 (msg : TRSignalMsg) : Prop :=
  TermTrunc8OK i S g T msg.wire ∧ TermTrunc8OK i S g T msg.mac ∧
  TermTrunc8OK i S g T msg.ratchetKey ∧ TermTrunc8OK i S g T msg.ciphertext ∧
  TermTrunc8OK i S g T msg.pqRatchet

private theorem termTrunc8OK_parseTrSignalMsg {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : TermTrunc8OK i S g T t) (hp : parseTrSignalMsg t = some msg) :
    TRSignalMsgTrunc8 (i := i) (S := S) (g := g) (T := T) msg := by
  unfold parseTrSignalMsg at hp
  simp only [bind, Option.bind] at hp
  split at hp <;> try cases hp
  next p hsp =>
    rcases p with ⟨wire, mac⟩
    rw [← DY.Concat.concat_split t (t.length - DY.Trunc.trunc8Length) wire mac hsp] at ht
    obtain ⟨hw, hm⟩ := memoOK_concat_elim ht
    dsimp only at hp
    split at hp <;> try cases hp
    next x hx =>
      have hpv := DY.Bytes.pack_view? DY.TrWire.TrWireMsg.SubF wire
      change wire.view? DY.TrWire.TrWireMsg.SubF = some x at hx
      rw [hx] at hpv
      have hwf := hw
      rw [← hpv] at hwf
      have h3 := memoOK_trWire_elim (w := x) hwf
      exact ⟨hw, hm, h3.1, h3.2.1, h3.2.2⟩

theorem TTrunc.receiveSignalMsg (msgIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T)
      (TRSignalMsgTrunc8 (i := i) (S := S) (g := g) (T := T))
      (DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine TTrunc.bind (TTrunc.receiveMessage msgIdx) fun t ht => ?_
  split
  · next msg hp =>
    exact TTrunc.bind (TTrunc.guardP _) fun _ _ =>
      TTrunc.pure (termTrunc8OK_parseTrSignalMsg ht hp)
  · exact TTrunc.failure

def ChainTrunc8 (c : RecvChain) : Prop :=
  TermTrunc8OK i S g T c.ratchetKey ∧ TermTrunc8OK i S g T c.chainKey

private theorem termTrunc8OK_findRecvChain {st : TRState} {pk : DY.Bytes} {c : RecvChain}
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) st)
    (hf : findRecvChain st.recv pk = some c) :
    ChainTrunc8 (i := i) (S := S) (g := g) (T := T) c :=
  hst.2.2.2.2.2.2.2 c (List.mem_of_find?_eq_some hf)

private theorem termTrunc8OK_recvChainFor {st : TRState} {pk : DY.Bytes} {c : RecvChain} {b : Bool}
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) st) (hpk : TermTrunc8OK i S g T pk)
    (hr : recvChainFor st.toDRState pk = some (c, b)) :
    ChainTrunc8 (i := i) (S := S) (g := g) (T := T) c := by
  unfold recvChainFor at hr; split at hr
  · next c' hf =>
    injection hr with hr; injection hr with hc _; subst hc
    exact termTrunc8OK_findRecvChain hst hf
  · split at hr
    · cases hr
    · injection hr with hr; injection hr with hc _; subst hc
      exact ⟨hpk, (termTrunc8OK_createChain hst.2.2.1 hpk hst.2.2.2.1).2⟩

private theorem TTrunc.dhRatchetStep {st : TRState} {pk : DY.Bytes}
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) st) (hpk : TermTrunc8OK i S g T pk) :
    TTrunc (i := i) (S := S) (g := g) (T := T)
      (fun p : TRState × RecvChain =>
        StateTrunc8 (i := i) (S := S) (g := g) (T := T) p.1 ∧
        ChainTrunc8 (i := i) (S := S) (g := g) (T := T) p.2)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TTrunc.bind (TTrunc.guardP _) fun _ _ => TTrunc.bind (TTrunc.genRand 32) fun dhs hdhs => ?_
  have hc1 := termTrunc8OK_createChain hst.2.2.1 hpk hst.2.2.2.1
  have hc2 := termTrunc8OK_createChain hc1.1 hpk hdhs
  have hc_new : ChainTrunc8 (i := i) (S := S) (g := g) (T := T)
      { ratchetKey := pk, chainKey := (createChain st.rk pk st.dhs).2, index := 0, rIdx := st.rIdx + 2 } :=
    ⟨hpk, hc1.2⟩
  refine TTrunc.pure ⟨⟨hst.1, hst.2.1, hc2.1, hdhs, hc2.2, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1,
    fun c' hc' => ?_⟩, hc_new⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst.2.2.2.2.2.2.2 c' hmem
  · rcases List.mem_singleton.mp hmem with rfl; exact hc_new

theorem TTrunc.ensureReceiverChain {st : TRState} {pk : DY.Bytes}
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) st) (hpk : TermTrunc8OK i S g T pk) :
    TTrunc (i := i) (S := S) (g := g) (T := T)
      (fun p : TRState × RecvChain × Bool =>
        StateTrunc8 (i := i) (S := S) (g := g) (T := T) p.1 ∧
        ChainTrunc8 (i := i) (S := S) (g := g) (T := T) p.2.1)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · next c hr => exact TTrunc.pure ⟨hst, termTrunc8OK_recvChainFor hst hpk hr⟩
  · exact TTrunc.bind (TTrunc.dhRatchetStep hst hpk) fun ⟨_, _⟩ h => TTrunc.pure h
  · exact TTrunc.failure

theorem termTrunc8OK_consumeMessageKey {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hc : ChainTrunc8 (i := i) (S := S) (g := g) (T := T) c)
    (hcm : consumeMessageKey c counter = some (seed, c')) :
    TermTrunc8OK i S g T seed ∧ ChainTrunc8 (i := i) (S := S) (g := g) (T := T) c' := by
  unfold consumeMessageKey at hcm
  split at hcm <;> try cases hcm
  split at hcm <;> try cases hcm
  split at hcm <;> try cases hcm
  have hck := termTrunc8OK_kdfCk (termTrunc8OK_chainKeyAt (counter.toNat - c.index.toNat) hc.2)
  exact ⟨hck.2, hc.1, hck.1⟩

theorem stateTrunc8_setRecvChain {st : TRState} {c' : RecvChain} {spqr' : DY.Bytes}
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) st)
    (hc' : ChainTrunc8 (i := i) (S := S) (g := g) (T := T) c')
    (hspqr' : TermTrunc8OK i S g T spqr') :
    StateTrunc8 (i := i) (S := S) (g := g) (T := T)
      { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
  refine ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hspqr', fun c hc => ?_⟩
  unfold setRecvChain at hc
  obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc
  split at heq <;> subst heq
  · exact hc'
  · exact hst.2.2.2.2.2.2.2 c₀ hc₀

theorem TTrunc.verifyMacAndDecrypt {st : TRState} {msg : TRSignalMsg} {pqSalt seed : DY.Bytes}
    (hmsg : TRSignalMsgTrunc8 (i := i) (S := S) (g := g) (T := T) msg) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (TermTrunc8OK i S g T)
      (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine TTrunc.bind (TTrunc.guardP _) fun _ _ tr _ htr => by
    erw [Traceful.run_mk]
    exact ⟨htr, fun _ hm => termTrunc8OK_symDec hm hmsg.2.2.2.1⟩

theorem TTrunc.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (hpk : TermTrunc8OK i S g T pk) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), TermTrunc8OK i S g T ck →
      TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
        (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0, _ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact TTrunc.pure trivial
  | ck, n, k + 1, hck => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    have hkdf := termTrunc8OK_kdfCk hck
    exact TTrunc.bind (TTrunc.logEvent ⟨hkdf.2, hpk⟩) fun _ _ =>
      TTrunc.logSkippedKeys s pk rIdx src hpk (kdfCk ck).1 (n + 1) k hkdf.1

theorem TTrunc.logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : StateTrunc8 (i := i) (S := S) (g := g) (T := T) st) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) :=
  TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => TTrunc.storeLocalState me hst

theorem TTrunc.messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine TTrunc.bind (TTrunc.getLocalState me stateIdx) fun st hst =>
    TTrunc.bind (TTrunc.guardP _) fun _ _ =>
    TTrunc.bind (TTrunc.genRand 32) fun m hm =>
    TTrunc.bind (TTrunc.genRand coinsLen) fun coins hcoins => ?_
  have hspqr := termTrunc8OK_spqrSend hst.2.2.2.2.2.2.1 hcoins
  refine TTrunc.bind (TTrunc.sendMessage hspqr.2.1) fun _ _ =>
    TTrunc.bind (TTrunc.receiveMessage pqIdx) fun pqSalt hpqSalt =>
    TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => ?_
  have hck := termTrunc8OK_kdfCk hst.2.2.2.2.1
  have hkeys := termTrunc8OK_trMsgKeys hpqSalt hck.2
  have hwire := termTrunc8OK_trHonestWireMsg (termTrunc8OK_dhPk hst.2.2.2.1) st.ns st.pn
    (termTrunc8OK_symEnc hkeys.1 hkeys.2.2 hm) hspqr.2.2
  exact TTrunc.bind (TTrunc.logMessageKeyAndStore me _ .sender _ _ _ _ _
    ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hck.1, hst.2.2.2.2.2.1, hspqr.1, hst.2.2.2.2.2.2.2⟩)
    fun _ _ => TTrunc.sendMessage
      (termTrunc8OK_concat hwire (termTrunc8OK_computeMac hkeys.2.1 hst.1 hst.2.1 hwire))

theorem TTrunc.messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) :=
  TTrunc.bind (TTrunc.getLocalState me stateIdx) fun _ _ =>
    TTrunc.bind (TTrunc.genRand 32) fun _ _ => TTrunc.failure

theorem TTrunc.messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TTrunc.bind (TTrunc.getLocalState me stateIdx) fun st₀ hst₀ =>
    TTrunc.bind (TTrunc.receiveSignalMsg msgIdx) fun msg hmsg =>
    TTrunc.bind (TTrunc.ensureReceiverChain hst₀ hmsg.2.2.1) fun ⟨st, c, _⟩ ⟨hst, hc⟩ => ?_
  dsimp only; split
  · next seed c' hcm =>
    obtain ⟨_, hc'⟩ := termTrunc8OK_consumeMessageKey hc hcm; split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := termTrunc8OK_spqrRecv hst.2.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      refine TTrunc.bind (TTrunc.sendMessage hkey) fun _ _ =>
        TTrunc.bind (TTrunc.receiveMessage pqIdx) fun pqSalt _ =>
        TTrunc.bind (TTrunc.verifyMacAndDecrypt hmsg) fun m hm => ?_
      have hrest : TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
          (do DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index (msg.counter.toNat - c.index.toNat)
              DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx
                { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TTrunc.bind (TTrunc.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
          TTrunc.bind (TTrunc.logEvent (ev := TREvent.Received me st.peer msg.ratchetKey msg.counter m) hm) fun _ _ =>
          TTrunc.logMessageKeyAndStore me _ .receiver _ _ _ _ _ (stateTrunc8_setRecvChain hst hc' hspqr')
      split
      · exact TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => hrest
      · exact hrest
    · exact TTrunc.failure
  · exact TTrunc.failure

theorem TTrunc.messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine TTrunc.bind (TTrunc.getLocalState me stateIdx) fun st hst =>
    TTrunc.bind (TTrunc.receiveSignalMsg msgIdx) fun msg hmsg =>
    TTrunc.bind (TTrunc.getEntry_tr skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TTrunc.bind (TTrunc.guardP _) fun _ _ =>
      TTrunc.bind (TTrunc.guardTrace _) fun _ _ => ?_
    split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := termTrunc8OK_spqrRecv hst.2.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      exact TTrunc.bind (TTrunc.sendMessage hkey) fun _ _ =>
        TTrunc.bind (TTrunc.receiveMessage pqIdx) fun _ _ =>
        TTrunc.bind (TTrunc.verifyMacAndDecrypt hmsg) fun m hm =>
        TTrunc.bind (TTrunc.logEvent trivial) fun _ _ =>
        TTrunc.bind (TTrunc.logEvent (ev := TREvent.Received me st.peer _ _ m) hm) fun _ _ =>
        TTrunc.logMessageKeyAndStore me _ .receiver _ _ _ _ _
          ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hspqr', hst.2.2.2.2.2.2.2⟩
    · exact TTrunc.failure
  · exact TTrunc.failure

theorem TTrunc.exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine TTrunc.bind (TTrunc.getLocalState me stateIdx) fun st hst => ?_
  cases k with
  | rk => exact TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => TTrunc.sendMessage hst.2.2.1
  | dhs => exact TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => TTrunc.sendMessage hst.2.2.2.1
  | cks => exact TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => TTrunc.sendMessage hst.2.2.2.2.1
  | ckr _ =>
    dsimp only; split
    · next c hf =>
      exact TTrunc.bind (TTrunc.logEvent trivial) fun _ _ =>
        TTrunc.sendMessage (termTrunc8OK_findRecvChain hst hf).2
    · exact TTrunc.failure

theorem TTrunc.exposeSpqr (me : Participant) (stateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) :=
  TTrunc.bind (TTrunc.getLocalState me stateIdx) fun st hst =>
    TTrunc.bind (TTrunc.logEvent (ev := TREvent.ExposedSpqr (st.sessionInfo me) st.spqr _) hst.2.2.2.2.2.2.1)
      fun _ _ => TTrunc.sendMessage hst.2.2.2.2.2.2.1

theorem TTrunc.exposeSkipped (skippedKeyEventIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine TTrunc.bind (TTrunc.getEntry_tr skippedKeyEventIdx) fun e he => ?_
  split
  · next s pk n seed rIdx src heq =>
    rw [heq] at he
    have he' : TermTrunc8OK i S g T seed ∧ TermTrunc8OK i S g T pk := he
    exact TTrunc.bind (TTrunc.guardTrace _) fun _ _ =>
      TTrunc.bind (TTrunc.logEvent (ev := TREvent.ExposedMK s seed n rIdx) he'.1)
        fun _ _ => TTrunc.sendMessage he'.1
  · exact TTrunc.failure

end MonadAndTR

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Monad
