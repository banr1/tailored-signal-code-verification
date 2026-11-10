/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Specifications.Refinement.TraceExplanation
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Stored Ratchet-Key Knowledge and Double-Ratchet Key Spine

Defines `DRKeySpine`, `TrStateStoredRkKnown`, and `StoredRkKnown`, and proves by induction over
all protocol moves that every stored `TRState` on `runTraceMoves r₀ ms` derives its root and chain
keys along `DRKeySpine` from PQXDH handshake outputs and known or initial ratchet public keys.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent KeyDir RecvChain findRecvChain
  setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk createChain)
open DY.Libsignal.TripleRatchet

abbrev StEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private theorem proj_inj_rk {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

abbrev PQStEntry :=
  PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)

/-- A stored PQXDH signed-prekey secret is a 32-byte random draw `randTerm t 32`. -/
def PQStateSpkRand (st : DY.Libsignal.PQXDH.PQXDHState) : Prop :=
  st.kind = .signedPrekey → ∃ t : Nat, st.sk = randTerm t 32

/-- A KEM shared secret from a PQXDH handshake: an encapsulation output, a successful
decapsulation output, or an implicit-rejection key. -/
def IsKemSS (ss : DY.Bytes) : Prop :=
  (∃ pk e : DY.Bytes, ss = (DY.PQKem.kemEncap pk e).2) ∨
  (∃ sk ct : DY.Bytes, DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap sk ct) = some ss) ∨
  (∃ sk ct : DY.Bytes, ss = DY.PQKem.kemRejKey sk ct)

/-- Handshake keys derived by `pqxdhKdf` from a `pqxdhIkm` input whose KEM component satisfies
`IsKemSS`. -/
def HsKeysOk (k : DY.Libsignal.PQXDH.HandshakeKeys) : Prop :=
  ∃ (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (ss : DY.Bytes),
    k = DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 ss) ∧
    IsKemSS ss

/-! ## Parse Projection on Network Entries -/

/-- Any network entry `(tr.at? msgIdx : Option Network.ExecEntryT) = some e` on `tr` has
`e.msg.AttackerKnows tr`. -/
theorem attackerKnows_of_at?_network
    {tr : ExecTrace} {msgIdx : Nat} {e : Network.ExecEntryT}
    (hat : (tr.at? msgIdx : Option Network.ExecEntryT) = some e) :
    e.msg.AttackerKnows tr := by
  apply getMessageSentAt_attackerKnows (i := msgIdx)
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  rw [hat]

/-- Any `TRSignalMsg` parsed from an attacker-known wire term `t` has attacker-known `ratchetKey`
and `wire`. -/
theorem attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg
    {tr : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg) :
    msg.ratchetKey.AttackerKnows tr ∧ msg.wire.AttackerKnows tr := by
  unfold parseTrSignalMsg at hparse
  dsimp only [bind, Option.bind] at hparse
  rcases hsp : Concat.split t (t.length - Trunc.trunc8Length) with _ | ⟨wire, mac⟩
  · rw [hsp] at hparse; cases hparse
  · rw [hsp] at hparse; dsimp only at hparse
    rcases hfw : DY.TrWire.trWireMsgFields? wire with _ | x
    · rw [hfw] at hparse; cases hparse
    · rw [hfw] at hparse; injection hparse with hmsg
      subst hmsg
      have hsp_ak := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht
      rw [hsp] at hsp_ak
      have hwire_ak : wire.AttackerKnows tr := hsp_ak.1
      have hwire_eq := DY.TrWire.trWireMsg_of_fields? hfw
      rw [hwire_eq] at hsp_ak
      exact ⟨(DY.TrWire.attacker_knows_trWireMsg_args
        x.version x.senderRatchetKey x.counter x.previousCounter
        x.ciphertext x.pqRatchet x.encodingVariation tr hsp_ak.1).1, hwire_ak⟩

/-- Any `TRSignalMsg` parsed from the network entry at `msgIdx` on `tr` has
`msg.ratchetKey.AttackerKnows tr`. -/
theorem attackerKnows_ratchetKey_of_at?_network
    {tr : ExecTrace} {msgIdx : Nat} {e : Network.ExecEntryT} {msg : TRSignalMsg}
    (hat : (tr.at? msgIdx : Option Network.ExecEntryT) = some e)
    (hparse : parseTrSignalMsg e.msg = some msg) :
    msg.ratchetKey.AttackerKnows tr :=
  (attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg (attackerKnows_of_at?_network hat) hparse).1

/-! ## Key-Spine and Stored Ratchet-Key Predicates -/

/-- A ratchet public key `pk` is either attacker-known on `tr` or equal to `dhPk (randTerm 2 32)`. -/
def RkKnownOrInit (tr : ExecTrace) (pk : DY.Bytes) : Prop :=
  pk.AttackerKnows tr ∨ pk = dhPk (randTerm 2 32)

theorem RkKnownOrInit.mono {tr₁ tr₂ : ExecTrace} {pk : DY.Bytes}
    (hle : tr₁ ≤ tr₂) (h : RkKnownOrInit tr₁ pk) : RkKnownOrInit tr₂ pk :=
  h.imp (fun hak => DY.Bytes.AttackerKnows_le pk tr₁ tr₂ hle hak) id

/-- Inductive characterization of Double Ratchet root, chain, and message-seed terms whose
`createChain` public-key inputs satisfy `RkKnownOrInit tr`. -/
inductive DRKeySpine (tr : ExecTrace) : DY.Bytes → Prop
  | rand (t : Nat) : DRKeySpine tr (randTerm t 32)
  /-- The PQXDH root key `k.rk`. -/
  | hsRk {k : DY.Libsignal.PQXDH.HandshakeKeys} : HsKeysOk k → DRKeySpine tr k.rk
  /-- The PQXDH chain key `k.ck`. -/
  | hsCk {k : DY.Libsignal.PQXDH.HandshakeKeys} : HsKeysOk k → DRKeySpine tr k.ck
  | kdfCk_fst {ck : DY.Bytes} : DRKeySpine tr ck → DRKeySpine tr (kdfCk ck).1
  | kdfCk_snd {ck : DY.Bytes} : DRKeySpine tr ck → DRKeySpine tr (kdfCk ck).2
  | createChain_fst {rk pk : DY.Bytes} (t : Nat) :
      DRKeySpine tr rk → RkKnownOrInit tr pk →
      DRKeySpine tr (createChain rk pk (randTerm t 32)).1
  | createChain_snd {rk pk : DY.Bytes} (t : Nat) :
      DRKeySpine tr rk → RkKnownOrInit tr pk →
      DRKeySpine tr (createChain rk pk (randTerm t 32)).2

theorem DRKeySpine.mono {tr₁ tr₂ : ExecTrace} {u : DY.Bytes}
    (hle : tr₁ ≤ tr₂) (h : DRKeySpine tr₁ u) : DRKeySpine tr₂ u := by
  induction h with
  | rand t => exact .rand t
  | hsRk hk => exact .hsRk hk
  | hsCk hk => exact .hsCk hk
  | kdfCk_fst _ ih => exact .kdfCk_fst ih
  | kdfCk_snd _ ih => exact .kdfCk_snd ih
  | createChain_fst t _ hpk ih => exact .createChain_fst t ih (hpk.mono hle)
  | createChain_snd t _ hpk ih => exact .createChain_snd t ih (hpk.mono hle)

theorem DRKeySpine.chainKeyAt {tr : ExecTrace} {ck : DY.Bytes}
    (hck : DRKeySpine tr ck) : ∀ n : Nat, DRKeySpine tr (chainKeyAt ck n)
  | 0 => hck
  | n + 1 => (DRKeySpine.kdfCk_fst hck).chainKeyAt n

/-- Full DR key-spine and stored ratchet-key invariant on a `TRState` at trace `tr`:
`st.rk` and `st.cks` satisfy `DRKeySpine tr`, `st.dhs` is a 32-byte `randTerm`, and every receiver
chain `c ∈ st.recv` has `RkKnownOrInit tr c.ratchetKey ∧ DRKeySpine tr c.chainKey`. -/
structure TrStateStoredRkKnown (tr : ExecTrace) (st : TRState) : Prop where
  rk : DRKeySpine tr st.rk
  cks : DRKeySpine tr st.cks
  dhs : ∃ t : Nat, st.dhs = randTerm t 32
  recv : ∀ c ∈ st.recv, RkKnownOrInit tr c.ratchetKey ∧ DRKeySpine tr c.chainKey

theorem TrStateStoredRkKnown.ratchetKey {tr : ExecTrace} {st : TRState}
    (hst : TrStateStoredRkKnown tr st) {c : RecvChain} (hc : c ∈ st.recv) :
    RkKnownOrInit tr c.ratchetKey :=
  (hst.recv c hc).1

theorem TrStateStoredRkKnown.chainKey {tr : ExecTrace} {st : TRState}
    (hst : TrStateStoredRkKnown tr st) {c : RecvChain} (hc : c ∈ st.recv) :
    DRKeySpine tr c.chainKey :=
  (hst.recv c hc).2

theorem TrStateStoredRkKnown.mono {tr₁ tr₂ : ExecTrace} {st : TRState}
    (hle : tr₁ ≤ tr₂) (hst : TrStateStoredRkKnown tr₁ st) :
    TrStateStoredRkKnown tr₂ st where
  rk := hst.rk.mono hle
  cks := hst.cks.mono hle
  dhs := hst.dhs
  recv := fun c hc => ⟨((hst.recv c hc).1).mono hle, ((hst.recv c hc).2).mono hle⟩

/-- Every state `st ∈ availableStates r₀ (runTraceMoves r₀ ms)` satisfies
`TrStateStoredRkKnown (runTraceMoves r₀ ms) st`. -/
def StoredRkKnown (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms),
    TrStateStoredRkKnown (runTraceMoves r₀ ms) st

/-! ## Trace-Level Invariant and Monad Combinators -/

def EntryStatesStoredRkKnown (tr : ExecTrace) (ent : ExecTrace.Entry) : Prop :=
  (∀ e : StEntry, TraceEntryHas.proj ent = some e → TrStateStoredRkKnown tr e.st.state) ∧
  (∀ e : PQStEntry, TraceEntryHas.proj ent = some e → PQStateSpkRand e.st.state)

/-- Every stored state entry on `tr` satisfies `EntryStatesStoredRkKnown tr`. -/
def TraceStatesStoredRkKnown (tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), EntryStatesStoredRkKnown tr (tr.at j hj)

theorem traceStatesStoredRkKnown_nil : TraceStatesStoredRkKnown (DY.Trace.nil : ExecTrace) :=
  fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj

theorem traceStatesStoredRkKnown_append {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hent : EntryStatesStoredRkKnown (tr.append e) (TraceEntryHas.inj e))
    (htr : TraceStatesStoredRkKnown tr) :
    TraceStatesStoredRkKnown (tr.append e) := by
  have hle : tr ≤ tr.append e := DY.Trace.append_le tr e
  intro j hj
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt hle]
    exact ⟨fun stEnt hproj => ((htr j hlt).1 stEnt hproj).mono hle, (htr j hlt).2⟩
  · have heq : j = tr.length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj
      omega
    subst heq
    simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

theorem traceStatesStoredRkKnown_at?_st {tr : ExecTrace} (htr : TraceStatesStoredRkKnown tr)
    {j : Nat} {e : StEntry} (h : (tr.at? j : Option StEntry) = some e) :
    TrStateStoredRkKnown tr e.st.state := by
  unfold DY.Trace.at? at h
  split at h
  · next hj => exact (htr j hj).1 e h
  · cases h

/-- Pointwise monad combinator at trace `tr` for `TraceStatesStoredRkKnown`. -/
def TracefulRkAt (tr : ExecTrace) {α : Type} (Q : ExecTrace → α → Prop) (x : Traceful α) : Prop :=
  TraceStatesStoredRkKnown tr →
    TraceStatesStoredRkKnown (x.run tr).2.val ∧
    ∀ a, (x.run tr).1 = some a → Q (x.run tr).2.val a

theorem TracefulRkAt.pure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} {a : α}
    (ha : Q tr a) :
    TracefulRkAt tr Q (pure a) := by
  unfold TracefulRkAt
  intro htr
  simp only [Traceful.run_pure]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb
  exact ha

theorem TracefulRkAt.failure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} :
    TracefulRkAt tr Q (failure : Traceful α) := by
  unfold TracefulRkAt
  intro htr
  simp only [Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

private theorem run_bind_fst_rkat {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd_rkat {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem TracefulRkAt.bind {tr : ExecTrace} {α β : Type}
    {Q₁ : ExecTrace → α → Prop} {Q₂ : ExecTrace → β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulRkAt tr Q₁ x)
    (hf : ∀ (tr₁ : ExecTrace) (a : α), tr ≤ tr₁ → Q₁ tr₁ a → TracefulRkAt tr₁ Q₂ (f a)) :
    TracefulRkAt tr Q₂ (x >>= f) := by
  intro htr
  rw [run_bind_snd_rkat, run_bind_fst_rkat]
  have h1 := hx htr
  have hle : tr ≤ (x.run tr).2.val := (x.run tr).2.property
  cases hres : (x.run tr).1 with
  | none => exact ⟨h1.1, fun _ hb => by cases hb⟩
  | some a => exact hf (x.run tr).2.val a hle (h1.2 a hres) h1.1

theorem tracefulRkAt_run_snd {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} {x : Traceful α}
    (hx : TracefulRkAt tr Q x) (htr : TraceStatesStoredRkKnown tr) :
    TraceStatesStoredRkKnown ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulRkAt.bind hx (fun _ _ _ _ => TracefulRkAt.pure (Q := fun _ _ => True) trivial) htr).1

theorem TracefulRkAt.guardP {tr : ExecTrace} (p : Prop) [Decidable p] :
    TracefulRkAt tr (fun _ _ => True) (_root_.guard p) := by
  unfold _root_.guard
  split
  · exact TracefulRkAt.pure trivial
  · exact TracefulRkAt.failure

theorem tracefulRkAt_guardTrace {tr : ExecTrace} (p : ExecTrace → Bool) :
    TracefulRkAt tr (fun _ _ => True) (guardTrace p) := by
  unfold TracefulRkAt guardTrace
  intro htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulRkAt_traceLength {tr : ExecTrace} :
    TracefulRkAt tr (fun _ _ => True) traceLength := by
  unfold TracefulRkAt traceLength
  intro htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulRkAt.getEntry_any {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulRkAt tr (fun _ (_ : E) => True) (getEntry j : Traceful E) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulRkAt.getEntry_st {tr : ExecTrace} (j : Nat) :
    TracefulRkAt tr (fun tr₁ (e : StEntry) => TrStateStoredRkKnown tr₁ e.st.state) (getEntry j) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  exact ⟨htr, fun _ he => traceStatesStoredRkKnown_at?_st htr he⟩

theorem TracefulRkAt.receiveMessage {tr : ExecTrace} (j : Nat) :
    TracefulRkAt tr (fun tr₁ (b : DY.Bytes) => b.AttackerKnows tr₁) (Network.receiveMessage j) := by
  intro htr
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_fst_rkat, run_bind_snd_rkat, Traceful.run_mk]
  rcases hat : (tr.at? j : Option Network.ExecEntryT) with _ | e
  · dsimp only; exact ⟨htr, fun _ h => by cases h⟩
  · dsimp only; rw [Traceful.run_pure]; dsimp only
    refine ⟨htr, fun b hb => ?_⟩
    injection hb with hb; subst hb
    exact attackerKnows_of_at?_network hat

theorem tracefulRkAt_receiveSignalMsg {tr : ExecTrace} (msgIdx : Nat) :
    TracefulRkAt tr (fun tr₁ (msg : TRSignalMsg) => msg.ratchetKey.AttackerKnows tr₁)
      (receiveSignalMsg msgIdx) := by
  unfold receiveSignalMsg
  refine TracefulRkAt.bind (TracefulRkAt.receiveMessage msgIdx) fun tr₁ b _ hb => ?_
  split
  · next msg hparse =>
    have hrk : msg.ratchetKey.AttackerKnows tr₁ :=
      (attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg hb hparse).1
    exact TracefulRkAt.bind (TracefulRkAt.guardP _) fun tr₂ _ hle _ =>
      TracefulRkAt.pure (DY.Bytes.AttackerKnows_le _ _ _ hle hrk)
  · exact TracefulRkAt.failure

theorem TracefulRkAt.getLocalState {tr : ExecTrace} (p : Participant) (j : Nat) :
    TracefulRkAt tr (fun tr₁ (st : TRState) => TrStateStoredRkKnown tr₁ st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulRkAt.bind
    (TracefulRkAt.bind (TracefulRkAt.getEntry_st j) fun tr₁ _ _ he =>
      TracefulRkAt.pure
        (Q := fun tr' (ls : PersistentLocalState.LocalState TRState) => TrStateStoredRkKnown tr' ls.state) he)
    fun tr₁ _ _ hst => ?_
  exact TracefulRkAt.bind (TracefulRkAt.guardP _) fun tr₂ _ hle _ =>
    TracefulRkAt.pure (hst.mono hle)

theorem TracefulRkAt.genRand_eq {tr : ExecTrace} (n : Nat) :
    TracefulRkAt tr
      (fun tr₁ (b : DY.Bytes) => b = randTerm tr.length n ∧ tr₁.length = tr.length + 1)
      (DY.Random.genRand n) := by
  unfold TracefulRkAt
  intro htr
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    run_bind_fst_rkat, run_bind_snd_rkat, Traceful.run_mk]
  dsimp only
  rw [Traceful.run_pure]
  dsimp only
  refine ⟨traceStatesStoredRkKnown_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun a ha => ?_⟩
  injection ha with ha
  exact ⟨ha.symm, by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]⟩

theorem TracefulRkAt.genRand {tr : ExecTrace} (n : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Random.genRand n) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceStatesStoredRkKnown_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulRkAt.sendMessage {tr : ExecTrace} (msg : DY.Bytes) :
    TracefulRkAt tr (fun _ _ => True) (Network.sendMessage msg) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  exact ⟨traceStatesStoredRkKnown_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulRkAt.logEvent {tr : ExecTrace} (ev : TREvent) :
    TracefulRkAt tr (fun _ _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceStatesStoredRkKnown_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulRkAt.storeLocalState {tr : ExecTrace} (p : Participant) {st : TRState}
    (hst : TrStateStoredRkKnown tr st) :
    TracefulRkAt tr (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceStatesStoredRkKnown_append ⟨?_, fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_rk] at h
  injection h with h
  subst h
  exact hst.mono (DY.Trace.append_le tr _)

theorem tracefulRkAt_logMessageKeyAndStore {tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : TrStateStoredRkKnown tr st) :
    TracefulRkAt tr (fun _ _ => True)
      (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ hle _ =>
    TracefulRkAt.storeLocalState me (hst.mono hle)

theorem tracefulRkAt_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      TracefulRkAt tr (fun _ _ => True) (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0, _ => by unfold logSkippedKeys; exact TracefulRkAt.pure trivial
  | ck, n, k + 1, _ => by
    unfold logSkippedKeys
    exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun tr₁ _ _ _ =>
      tracefulRkAt_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k tr₁

theorem tracefulRkAt_verifyMacAndDecrypt {tr : ExecTrace} (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    TracefulRkAt tr (fun _ _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulRkAt.bind (TracefulRkAt.guardP _) fun _ _ _ _ => ?_
  unfold TracefulRkAt
  intro htr
  dsimp [liftM, monadLift, MonadLift.monadLift]
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem trStateStoredRkKnown_setRecvChain {tr : ExecTrace} {st : TRState} {c' : RecvChain}
    (spqr' : DY.Bytes) (hst : TrStateStoredRkKnown tr st)
    (hc' : RkKnownOrInit tr c'.ratchetKey ∧ DRKeySpine tr c'.chainKey) :
    TrStateStoredRkKnown tr { st with recv := setRecvChain st.recv c', spqr := spqr' } where
  rk := hst.rk
  cks := hst.cks
  dhs := hst.dhs
  recv := by
    intro c hc
    unfold setRecvChain at hc
    obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc
    split at heq <;> subst heq
    · exact hc'
    · exact hst.recv c₀ hc₀

theorem rkKnownOrInit_recvChainFor {tr : ExecTrace} {st : TRState} {pk : DY.Bytes}
    {c : RecvChain} {b : Bool}
    (hst : TrStateStoredRkKnown tr st) (hpk : RkKnownOrInit tr pk)
    (hrc : recvChainFor st.toDRState pk = some (c, b)) :
    RkKnownOrInit tr c.ratchetKey ∧ DRKeySpine tr c.chainKey := by
  unfold recvChainFor at hrc
  rcases hfind : findRecvChain st.toDRState.recv pk with _ | c₀
  · rw [hfind] at hrc; dsimp only at hrc
    split at hrc
    · cases hrc
    · injection hrc with hrc
      rcases Prod.mk.inj hrc with ⟨rfl, _⟩
      obtain ⟨t_dhs, hdhs⟩ := hst.dhs
      refine ⟨hpk, ?_⟩
      dsimp only [TRState.toDRState]
      rw [hdhs]
      exact DRKeySpine.createChain_snd t_dhs hst.rk hpk
  · rw [hfind] at hrc
    injection hrc with hrc
    rcases Prod.mk.inj hrc with ⟨rfl, _⟩
    unfold findRecvChain at hfind
    exact hst.recv c₀ (List.mem_of_find?_eq_some hfind)

theorem tracefulRkAt_dhRatchetStep {tr : ExecTrace} {st : TRState} {pk : DY.Bytes}
    (hst : TrStateStoredRkKnown tr st) (hpk : RkKnownOrInit tr pk) :
    TracefulRkAt tr
      (fun tr₁ (p : TRState × RecvChain) =>
        TrStateStoredRkKnown tr₁ p.1 ∧
        (RkKnownOrInit tr₁ p.2.ratchetKey ∧ DRKeySpine tr₁ p.2.chainKey))
      (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulRkAt.bind (TracefulRkAt.guardP _) fun tr₁ _ hle₁ _ => ?_
  refine TracefulRkAt.bind (TracefulRkAt.genRand_eq 32) fun tr₂ dhs' hle₂ ⟨hdhs', _⟩ => ?_
  have hle := DY.Trace.le_trans _ _ _ hle₁ hle₂
  have hpk₂ : RkKnownOrInit tr₂ pk := hpk.mono hle
  have hst₂ : TrStateStoredRkKnown tr₂ st := hst.mono hle
  obtain ⟨t_dhs, hdhs⟩ := hst₂.dhs
  have hrk1 : DRKeySpine tr₂ (createChain st.rk pk st.dhs).1 := by
    rw [hdhs]; exact DRKeySpine.createChain_fst t_dhs hst₂.rk hpk₂
  have hckr : DRKeySpine tr₂ (createChain st.rk pk st.dhs).2 := by
    rw [hdhs]; exact DRKeySpine.createChain_snd t_dhs hst₂.rk hpk₂
  have hrk2 : DRKeySpine tr₂ (createChain (createChain st.rk pk st.dhs).1 pk dhs').1 := by
    rw [hdhs']; exact DRKeySpine.createChain_fst tr₁.length hrk1 hpk₂
  have hcks' : DRKeySpine tr₂ (createChain (createChain st.rk pk st.dhs).1 pk dhs').2 := by
    rw [hdhs']; exact DRKeySpine.createChain_snd tr₁.length hrk1 hpk₂
  refine TracefulRkAt.pure ⟨⟨hrk2, hcks', ⟨tr₁.length, hdhs'⟩, fun c' hc' => ?_⟩, ⟨hpk₂, hckr⟩⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst₂.recv c' hmem
  · rcases List.mem_singleton.mp hmem with rfl
    exact ⟨hpk₂, hckr⟩

theorem tracefulRkAt_ensureReceiverChain {tr : ExecTrace} {st : TRState} {pk : DY.Bytes}
    (hst : TrStateStoredRkKnown tr st) (hpk : RkKnownOrInit tr pk) :
    TracefulRkAt tr
      (fun tr₁ (p : TRState × RecvChain × Bool) =>
        TrStateStoredRkKnown tr₁ p.1 ∧
        (RkKnownOrInit tr₁ p.2.1.ratchetKey ∧ DRKeySpine tr₁ p.2.1.chainKey))
      (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · next c hr =>
    exact TracefulRkAt.pure ⟨hst, rkKnownOrInit_recvChainFor hst hpk hr⟩
  · exact TracefulRkAt.bind (tracefulRkAt_dhRatchetStep hst hpk) fun _ ⟨_, _⟩ _ h =>
      TracefulRkAt.pure h
  · exact TracefulRkAt.failure

theorem tracefulRkAt_consumeMessageKey {tr : ExecTrace} {c c' : RecvChain} {counter : UInt32}
    {seed : DY.Bytes} (hc : RkKnownOrInit tr c.ratchetKey ∧ DRKeySpine tr c.chainKey)
    (hcm : consumeMessageKey c counter = some (seed, c')) :
    DRKeySpine tr seed ∧ (RkKnownOrInit tr c'.ratchetKey ∧ DRKeySpine tr c'.chainKey) := by
  unfold consumeMessageKey at hcm
  split at hcm
  · cases hcm
  · split at hcm
    · cases hcm
    · split at hcm
      · cases hcm
      · injection hcm with hcm
        rcases Prod.mk.inj hcm with ⟨rfl, rfl⟩
        have hck := hc.2.chainKeyAt (counter.toNat - c.index.toNat)
        exact ⟨.kdfCk_snd hck, ⟨hc.1, .kdfCk_fst hck⟩⟩

/-! ## Triple Ratchet Transition Preservation -/

theorem tracefulRkAt_messageEncrypt {tr : ExecTrace} (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulRkAt tr (fun _ _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  refine TracefulRkAt.bind (TracefulRkAt.getLocalState me stateIdx) fun _ st _ hst =>
    TracefulRkAt.bind (TracefulRkAt.guardP _) fun _ _ hle₁ _ =>
    TracefulRkAt.bind (TracefulRkAt.genRand 32) fun _ _ hle₂ _ =>
    TracefulRkAt.bind (TracefulRkAt.genRand coinsLen) fun _ _ hle₃ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ hle₄ _ =>
    TracefulRkAt.bind (TracefulRkAt.receiveMessage pqIdx) fun _ _ hle₅ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ hle₆ _ => ?_
  have hst' := (((((hst.mono hle₁).mono hle₂).mono hle₃).mono hle₄).mono hle₅).mono hle₆
  exact TracefulRkAt.bind
    (tracefulRkAt_logMessageKeyAndStore me _ .sender _ _ _ _ _
      ⟨hst'.rk, .kdfCk_fst hst'.cks, hst'.dhs, hst'.recv⟩)
    fun _ _ _ _ => TracefulRkAt.sendMessage _

theorem tracefulRkAt_messageEncryptAbort {tr : ExecTrace} (me : Participant) (stateIdx : Nat) :
    TracefulRkAt tr (fun _ _ => True) (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact TracefulRkAt.bind (TracefulRkAt.getLocalState me stateIdx) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.genRand 32) fun _ _ _ _ => TracefulRkAt.failure

theorem tracefulRkAt_messageDecrypt {tr : ExecTrace}
    (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulRkAt tr (fun _ _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulRkAt.bind (TracefulRkAt.getLocalState me stateIdx) fun _ st₀ _ hst₀ =>
    TracefulRkAt.bind (tracefulRkAt_receiveSignalMsg msgIdx) fun _ msg hle₁ hrk => ?_
  refine TracefulRkAt.bind
    (tracefulRkAt_ensureReceiverChain (hst₀.mono hle₁) (.inl hrk))
    fun tr₂ x _ ⟨hst, hc⟩ => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only
  split
  · next seed c' hcm =>
    have ⟨_, hc'⟩ := tracefulRkAt_consumeMessageKey hc hcm
    split
    · next spqr' key _ =>
      refine TracefulRkAt.bind (TracefulRkAt.sendMessage key) fun _ _ hle₂ _ =>
        TracefulRkAt.bind (TracefulRkAt.receiveMessage pqIdx) fun _ pqSalt hle₃ _ =>
        TracefulRkAt.bind (tracefulRkAt_verifyMacAndDecrypt st msg pqSalt seed) fun tr₅ m hle₄ _ => ?_
      have hle₂₅ := DY.Trace.le_trans _ _ _ hle₂ (DY.Trace.le_trans _ _ _ hle₃ hle₄)
      have hst₅ := trStateStoredRkKnown_setRecvChain spqr' (hst.mono hle₂₅)
        ⟨hc'.1.mono hle₂₅, hc'.2.mono hle₂₅⟩
      have hrest : ∀ tr_in, tr₅ ≤ tr_in →
          TracefulRkAt tr_in (fun _ _ => True)
            (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                  (msg.counter.toNat - c.index.toNat)
                DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
                logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        fun tr_in hle_in =>
          TracefulRkAt.bind (tracefulRkAt_logSkippedKeys _ _ _ _ _ _ _ tr_in) fun _ _ hle_sk _ =>
            TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ hle_ev _ =>
              tracefulRkAt_logMessageKeyAndStore me _ .receiver _ _ _ _ _
                (((hst₅.mono hle_in).mono hle_sk).mono hle_ev)
      split
      · exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ hle_a _ =>
          TracefulRkAt.bind (TracefulRkAt.logEvent _) fun tr_b _ hle_b _ =>
            hrest tr_b (DY.Trace.le_trans _ _ _ hle_a hle_b)
      · exact hrest tr₅ (DY.Trace.le_refl tr₅)
    · exact TracefulRkAt.failure
  · exact TracefulRkAt.failure

theorem tracefulRkAt_messageDecryptSkipped {tr : ExecTrace}
    (me : Participant) (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulRkAt tr (fun _ _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulRkAt.bind (TracefulRkAt.getLocalState me stateIdx) fun _ st _ hst =>
    TracefulRkAt.bind (tracefulRkAt_receiveSignalMsg msgIdx) fun _ msg hle₁ _ =>
    TracefulRkAt.bind (TracefulRkAt.getEntry_any skippedKeyEventIdx) fun _ _ hle₂ _ => ?_
  split
  · refine TracefulRkAt.bind (TracefulRkAt.guardP _) fun _ _ hle₃ _ =>
      TracefulRkAt.bind (tracefulRkAt_guardTrace _) fun _ _ hle₄ _ => ?_
    split
    · next spqr' key _ =>
      refine TracefulRkAt.bind (TracefulRkAt.sendMessage key) fun _ _ hle₅ _ =>
        TracefulRkAt.bind (TracefulRkAt.receiveMessage pqIdx) fun _ pqSalt hle₆ _ =>
        TracefulRkAt.bind (tracefulRkAt_verifyMacAndDecrypt st msg pqSalt _) fun _ _ hle₇ _ =>
        TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ hle₈ _ =>
        TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ hle₉ _ => ?_
      have hst' := (((((((((hst.mono hle₁).mono hle₂).mono hle₃).mono hle₄).mono hle₅).mono hle₆).mono hle₇).mono hle₈).mono hle₉)
      exact tracefulRkAt_logMessageKeyAndStore me _ .receiver _ _ _ _ _
        ⟨hst'.rk, hst'.cks, hst'.dhs, hst'.recv⟩
    · exact TracefulRkAt.failure
  · exact TracefulRkAt.failure

theorem tracefulRkAt_exposeKey {tr : ExecTrace} (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulRkAt tr (fun _ _ => True) (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine TracefulRkAt.bind (TracefulRkAt.getLocalState me stateIdx) fun _ _ _ _ => ?_
  cases k with
  | rk => exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ => TracefulRkAt.sendMessage _
  | dhs => exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ => TracefulRkAt.sendMessage _
  | cks => exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ => TracefulRkAt.sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ => TracefulRkAt.sendMessage _
    · exact TracefulRkAt.failure

theorem tracefulRkAt_exposeSpqr {tr : ExecTrace} (me : Participant) (stateIdx : Nat) :
    TracefulRkAt tr (fun _ _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  refine TracefulRkAt.bind (TracefulRkAt.getLocalState me stateIdx) fun _ _ _ _ => ?_
  exact TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ => TracefulRkAt.sendMessage _

theorem tracefulRkAt_exposeSkipped {tr : ExecTrace} (skippedKeyEventIdx : Nat) :
    TracefulRkAt tr (fun _ _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulRkAt.bind (TracefulRkAt.getEntry_any skippedKeyEventIdx) fun _ _ _ _ => ?_
  split
  · exact TracefulRkAt.bind (tracefulRkAt_guardTrace _) fun _ _ _ _ =>
      TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ =>
      TracefulRkAt.sendMessage _
  · exact TracefulRkAt.failure

/-! ## PQXDH and Handshake Transition Preservation -/

theorem TracefulRkAt.logEventPQ {tr : ExecTrace} (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    TracefulRkAt tr (fun _ _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceStatesStoredRkKnown_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulRkAt.logEventC {tr : ExecTrace} (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulRkAt tr (fun _ _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceStatesStoredRkKnown_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulRkAt.getEntry_pq {tr : ExecTrace} (j : Nat) :
    TracefulRkAt tr (fun _ (e : PQStEntry) => PQStateSpkRand e.st.state) (getEntry j) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2 e he
  · cases he

theorem TracefulRkAt.getLocalStatePQ {tr : ExecTrace} (p : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ (st : DY.Libsignal.PQXDH.PQXDHState) => PQStateSpkRand st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulRkAt.bind
    (TracefulRkAt.bind (TracefulRkAt.getEntry_pq j) fun tr₁ _ _ he =>
      TracefulRkAt.pure
        (Q := fun _ (ls : PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) =>
          PQStateSpkRand ls.state) he)
    fun tr₁ _ _ hst => ?_
  exact TracefulRkAt.bind (TracefulRkAt.guardP _) fun _ _ _ _ => TracefulRkAt.pure hst

theorem TracefulRkAt.getKey {tr : ExecTrace} (p : Participant) (j : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    TracefulRkAt tr (fun _ (sk : DY.Bytes) =>
        kind = .signedPrekey → ∃ t : Nat, sk = randTerm t 32)
      (DY.Libsignal.PQXDH.getKey p j kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine TracefulRkAt.bind (TracefulRkAt.getLocalStatePQ p j) fun _ st _ hst => ?_
  refine TracefulRkAt.bind (Q₁ := fun _ _ => st.kind = kind) ?_ fun _ _ _ hk =>
    TracefulRkAt.pure fun hkind => hst (hk.trans hkind)
  unfold _root_.guard
  split
  · next h => exact TracefulRkAt.pure h
  · exact TracefulRkAt.failure

theorem tracefulRkAt_compromiseIK {tr : ExecTrace} (p : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact TracefulRkAt.bind (TracefulRkAt.getKey p j _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ => TracefulRkAt.sendMessage _

theorem tracefulRkAt_compromiseSPK {tr : ExecTrace} (p : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact TracefulRkAt.bind (TracefulRkAt.getKey p j _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ => TracefulRkAt.sendMessage _

theorem tracefulRkAt_compromisePQSPK {tr : ExecTrace} (p : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact TracefulRkAt.bind (TracefulRkAt.getKey p j _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ => TracefulRkAt.sendMessage _

theorem tracefulRkAt_guardOnTrace {tr : ExecTrace} (p : ExecTrace → Bool) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  unfold TracefulRkAt DY.Libsignal.PQXDH.guardTrace
  intro htr
  by_cases hp : p tr = true <;>
    simp only [Traceful.run_mk, hp, Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulRkAt_compromiseOPK {tr : ExecTrace} (p : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact TracefulRkAt.bind (TracefulRkAt.getKey p j _) fun _ _ _ _ =>
    TracefulRkAt.bind (tracefulRkAt_guardOnTrace _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ => TracefulRkAt.sendMessage _

local macro "cref_k8a_rk_le" : tactic =>
  `(tactic| (repeat (first
    | exact DY.Trace.le_refl _
    | assumption
    | refine DY.Trace.le_trans _ _ _ ?_ ‹_ ≤ _›)))

theorem TracefulRkAt.storeLocalStatePQ {tr : ExecTrace} (p : Participant)
    {st : DY.Libsignal.PQXDH.PQXDHState} (hst : PQStateSpkRand st) :
    TracefulRkAt tr (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulRkAt
  intro htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceStatesStoredRkKnown_append ⟨fun _ h => (by cases h), ?_⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_rk] at h
  injection h with h
  subst h
  exact hst

theorem TracefulRkAt.lookupIdentity {tr : ExecTrace} (p : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulRkAt.bind (TracefulRkAt.getEntry_any j) fun _ _ _ _ => ?_
  split
  · exact TracefulRkAt.bind (TracefulRkAt.guardP _) fun _ _ _ _ => TracefulRkAt.pure trivial
  · exact TracefulRkAt.failure

theorem tracefulRkAt_registerIdentity {tr : ExecTrace} (p : Participant) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact TracefulRkAt.bind (tracefulRkAt_guardOnTrace _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.genRand 32) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ =>
    TracefulRkAt.storeLocalStatePQ p (fun h => by cases h)

theorem tracefulRkAt_genSignedPrekey {tr : ExecTrace} (b : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact TracefulRkAt.bind (TracefulRkAt.getKey b j _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.genRand_eq 32) fun _ _ _ hspk =>
    TracefulRkAt.bind (TracefulRkAt.genRand 64) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.storeLocalStatePQ b (fun _ => ⟨_, hspk.1⟩)) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ => TracefulRkAt.pure trivial

theorem tracefulRkAt_genPQPrekey {tr : ExecTrace} (b : Participant) (j : Nat) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact TracefulRkAt.bind (TracefulRkAt.getKey b j _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.genRand 64) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.genRand 64) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.storeLocalStatePQ b (fun h => by cases h)) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ => TracefulRkAt.pure trivial

theorem tracefulRkAt_genOneTimePrekey {tr : ExecTrace} (b : Participant) :
    TracefulRkAt tr (fun _ _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact TracefulRkAt.bind (TracefulRkAt.genRand 32) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.storeLocalStatePQ b (fun h => by cases h)) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ => TracefulRkAt.pure trivial

theorem tracefulRkAt_setupAct {tr : ExecTrace} (a b : Participant) (withOpk : Bool) :
    TracefulRkAt tr (fun _ _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  apply TracefulRkAt.bind (Q₁ := fun _ _ => True) (tracefulRkAt_registerIdentity a)
  intro _ _ _ _
  apply TracefulRkAt.bind (Q₁ := fun _ _ => True) (tracefulRkAt_registerIdentity b)
  intro _ hB _ _
  apply TracefulRkAt.bind (Q₁ := fun _ _ => True) (tracefulRkAt_genSignedPrekey b hB)
  intro _ _ _ _
  apply TracefulRkAt.bind (Q₁ := fun _ _ => True) (tracefulRkAt_genPQPrekey b hB)
  intro _ _ _ _
  split
  · apply TracefulRkAt.bind (Q₁ := fun _ _ => True) (tracefulRkAt_genOneTimePrekey b)
    intro _ _ _ _
    exact TracefulRkAt.pure trivial
  · exact TracefulRkAt.pure trivial

theorem tracefulRkAt_aliceHandshake {tr : ExecTrace} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulRkAt tr (fun tr₁ (o : DY.Libsignal.PQXDH.AliceHandshakeOut) =>
        o.spk.AttackerKnows tr₁ ∧ HsKeysOk o.keys)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulRkAt.bind (TracefulRkAt.getKey a idStateIdx _); intro _ ikA _ _
  apply TracefulRkAt.bind (TracefulRkAt.lookupIdentity b regIdxB); intro _ ikv _ _
  rcases ikv with ⟨ikB, vkB⟩
  dsimp only
  apply TracefulRkAt.bind (TracefulRkAt.receiveMessage h.spk); intro _ spk _ hspk
  apply TracefulRkAt.bind (TracefulRkAt.receiveMessage h.spkSig); intro _ _ _ _
  apply TracefulRkAt.bind (TracefulRkAt.receiveMessage h.pqpk); intro _ pqpk _ _
  apply TracefulRkAt.bind (TracefulRkAt.receiveMessage h.pqpkSig); intro _ _ _ _
  apply TracefulRkAt.bind (TracefulRkAt.guardP _); intro _ _ _ _
  apply TracefulRkAt.bind (TracefulRkAt.guardP _); intro _ _ _ _
  split
  all_goals first
    | (apply TracefulRkAt.bind (TracefulRkAt.receiveMessage _); intro _ _ _ _)
    | skip
  all_goals
    apply TracefulRkAt.bind (TracefulRkAt.pure (Q := fun _ _ => True) trivial)
    intro _ opk _ _
    apply TracefulRkAt.bind (TracefulRkAt.genRand 32); intro _ ek _ _
    apply TracefulRkAt.bind (TracefulRkAt.guardP _); intro _ _ _ _
    apply TracefulRkAt.bind (TracefulRkAt.guardP _); intro _ _ _ _
    apply TracefulRkAt.bind (TracefulRkAt.genRand 32); intro _ entropy _ _
    rcases hag : DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pqpk opk entropy with
      ⟨ct, keys⟩
    try dsimp only
    refine TracefulRkAt.pure ⟨DY.Bytes.AttackerKnows_le _ _ _ (by cref_k8a_rk_le) hspk, ?_⟩
    unfold DY.Libsignal.PQXDH.aliceAgreement at hag
    rcases hke : DY.PQKem.kemEncap pqpk entropy with ⟨ct', ss⟩
    simp only [hke, Prod.mk.injEq] at hag
    exact ⟨_, _, _, _, ss, hag.2.symm, .inl ⟨pqpk, entropy, by rw [hke]⟩⟩

theorem tracefulRkAt_aliceStart {tr : ExecTrace} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulRkAt tr (fun _ _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulRkAt.bind (tracefulRkAt_aliceHandshake a b idStateIdx regIdxB h)
    fun tr₁ o _ ho => TracefulRkAt.bind (TracefulRkAt.genRand_eq 32) fun tr₂ dhsA hle₂ hdhs => ?_
  obtain ⟨hdhsA, -⟩ := hdhs
  subst hdhsA
  have hspk : RkKnownOrInit tr₂ o.spk := .inl (DY.Bytes.AttackerKnows_le _ _ _ hle₂ ho.1)
  rcases hcc : createChain o.keys.rk o.spk (randTerm tr₁.length 32) with ⟨rkA, cksA⟩
  have hrk : DRKeySpine tr₂ rkA := by
    have := DRKeySpine.createChain_fst tr₁.length (.hsRk ho.2) hspk
    rwa [hcc] at this
  have hcks : DRKeySpine tr₂ cksA := by
    have := DRKeySpine.createChain_snd tr₁.length (.hsRk ho.2) hspk
    rwa [hcc] at this
  refine TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.sendMessage _) fun _ _ _ _ =>
    TracefulRkAt.bind tracefulRkAt_traceLength fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ =>
    TracefulRkAt.bind (TracefulRkAt.logEventC _) fun tr₈ _ _ _ =>
    TracefulRkAt.storeLocalState a ?_
  have hle : tr₂ ≤ tr₈ := by cref_k8a_rk_le
  refine ⟨hrk.mono hle, hcks.mono hle, ⟨_, rfl⟩, fun c hc => ?_⟩
  simp only [List.mem_singleton] at hc
  subst hc
  exact ⟨hspk.mono hle, .hsCk ho.2⟩

theorem tracefulRkAt_bobHandshake {tr : ExecTrace} (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulRkAt tr (fun _ (o : DY.Libsignal.PQXDH.BobHandshakeOut) =>
        (∃ t : Nat, o.spkSk = randTerm t 32) ∧ HsKeysOk o.keys)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TracefulRkAt.bind (TracefulRkAt.getKey b h.ik _); intro _ ikB _ _
  apply TracefulRkAt.bind (TracefulRkAt.getKey b h.spk _); intro _ spkSk _ hspk
  apply TracefulRkAt.bind (TracefulRkAt.getKey b h.pqspk _); intro _ pqsk _ _
  dsimp only
  split
  all_goals first
    | (apply TracefulRkAt.bind (TracefulRkAt.getKey b _ _); intro _ _ _ _)
    | skip
  all_goals
    apply TracefulRkAt.bind (TracefulRkAt.pure (Q := fun _ _ => True) trivial)
    intro _ opkSk _ _
    apply TracefulRkAt.bind (TracefulRkAt.lookupIdentity a regIdxA); intro _ ikv _ _
    rcases ikv with ⟨ikA, vkA⟩
    dsimp only
    apply TracefulRkAt.bind (TracefulRkAt.receiveMessage ekIdx); intro _ ek _ _
    apply TracefulRkAt.bind (TracefulRkAt.receiveMessage ctIdx); intro _ ct _ _
    apply TracefulRkAt.bind (TracefulRkAt.guardP _); intro _ _ _ _
    split
    · next keys hag =>
      refine TracefulRkAt.pure ⟨hspk rfl, ?_⟩
      unfold DY.Libsignal.PQXDH.bobAgreement at hag
      rcases hss : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct) with _ | ss
      · simp only [hss, Option.getD_none, Option.pure_def, Option.some.injEq] at hag
        exact ⟨_, _, _, _, DY.PQKem.kemRejKey pqsk ct, hag.symm, .inr (.inr ⟨pqsk, ct, rfl⟩)⟩
      · simp only [hss, Option.getD_some, Option.pure_def, Option.some.injEq] at hag
        exact ⟨_, _, _, _, ss, hag.symm, .inr (.inl ⟨pqsk, ct, hss⟩)⟩
    · exact TracefulRkAt.failure

theorem tracefulRkAt_bobStart {tr : ExecTrace} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulRkAt tr (fun _ _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulRkAt.bind (tracefulRkAt_bobHandshake b a kh regIdxA mh.ek mh.ct)
    fun tr₁ o _ ho => TracefulRkAt.bind (tracefulRkAt_receiveSignalMsg mh.msg)
    fun tr₂ msg hle₁ hrk => ?_
  refine TracefulRkAt.bind (tracefulRkAt_ensureReceiverChain ?hst0 (.inl hrk))
    fun tr₃ x _ ⟨hst, hc⟩ => ?_
  case hst0 =>
    exact ⟨.hsRk ho.2, .hsCk ho.2, ho.1, fun c hc => by simp at hc⟩
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only
  split
  · next seed c' hcm =>
    have ⟨_, hc'⟩ := tracefulRkAt_consumeMessageKey hc hcm
    split
    · next spqr' key _ =>
      refine TracefulRkAt.bind (TracefulRkAt.sendMessage key) fun _ _ hle₂ _ =>
        TracefulRkAt.bind (TracefulRkAt.receiveMessage pqIdx) fun _ pqSalt hle₃ _ =>
        TracefulRkAt.bind (tracefulRkAt_verifyMacAndDecrypt st msg pqSalt seed)
          fun tr₅ m hle₄ _ => ?_
      have hle₂₅ := DY.Trace.le_trans _ _ _ hle₂ (DY.Trace.le_trans _ _ _ hle₃ hle₄)
      have hst₅ := trStateStoredRkKnown_setRecvChain spqr' (hst.mono hle₂₅)
        ⟨hc'.1.mono hle₂₅, hc'.2.mono hle₂₅⟩
      clear hle₂₅
      split
      all_goals first
        | refine TracefulRkAt.bind (tracefulRkAt_guardOnTrace _) fun _ _ _ _ =>
            TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ => ?_
        | skip
      all_goals refine TracefulRkAt.bind tracefulRkAt_traceLength fun _ _ _ _ =>
        TracefulRkAt.bind (TracefulRkAt.logEventPQ _) fun _ _ _ _ => ?_
      all_goals split
      all_goals first
        | refine TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ =>
            TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ => ?_
        | skip
      all_goals refine TracefulRkAt.bind (TracefulRkAt.logEventC _) fun _ _ _ _ =>
          TracefulRkAt.bind tracefulRkAt_traceLength fun _ _ _ _ =>
          TracefulRkAt.bind (tracefulRkAt_logSkippedKeys _ _ _ _ _ _ _ _) fun _ _ _ _ =>
          TracefulRkAt.bind (TracefulRkAt.logEvent _) fun _ _ _ _ =>
          tracefulRkAt_logMessageKeyAndStore b _ .receiver _ _ _ _ _ (hst₅.mono ?_)
      all_goals cref_k8a_rk_le
    · exact TracefulRkAt.failure
  · exact TracefulRkAt.failure

/-- Every move `m` unconditionally preserves `TraceStatesStoredRkKnown`. -/
theorem traceStatesStoredRkKnown_move_next {tr : ExecTrace} {m : Move}
    (htr : TraceStatesStoredRkKnown tr) :
    TraceStatesStoredRkKnown (m.next tr) := by
  unfold Move.next Move.act
  cases m with
  | setup a b withOpk => exact (tracefulRkAt_setupAct a b withOpk htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulRkAt_run_snd (tracefulRkAt_aliceStart a b idStateIdx regIdxB h) htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulRkAt_run_snd (tracefulRkAt_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulRkAt_run_snd (tracefulRkAt_messageEncrypt me stateIdx coinsLen pqIdx) htr
  | encryptAbort me stateIdx =>
    exact tracefulRkAt_run_snd (tracefulRkAt_messageEncryptAbort me stateIdx) htr
  | encryptFail me stateIdx coinsLen =>
    dsimp only
    have h_assoc :
        ((do let n ← traceLength; let _ ← messageEncrypt me stateIdx coinsLen (n + 3); Pure.pure ()).run tr).2.val =
        (((do let n ← traceLength; messageEncrypt me stateIdx coinsLen (n + 3)) >>= fun _ => Pure.pure ()).run tr).2.val := by
      rw [run_bind_snd_rkat, run_bind_snd_rkat, run_bind_fst_rkat]
      rcases ht : (traceLength.run tr).1 with _ | n
      · dsimp only; rw [run_bind_snd_rkat, ht]
      · dsimp only; rw [run_bind_snd_rkat, run_bind_snd_rkat, ht]
    rw [h_assoc]
    exact tracefulRkAt_run_snd
      (TracefulRkAt.bind tracefulRkAt_traceLength
        fun _ n _ _ => tracefulRkAt_messageEncrypt me stateIdx coinsLen (n + 3)) htr
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulRkAt_run_snd (tracefulRkAt_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulRkAt_run_snd
      (tracefulRkAt_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) htr
  | reject _ =>
    dsimp only
    rw [Traceful.run_pure]
    exact htr
  | compromiseIK p stateIdx =>
    exact tracefulRkAt_run_snd (tracefulRkAt_compromiseIK p stateIdx) htr
  | compromiseSPK p stateIdx =>
    exact tracefulRkAt_run_snd (tracefulRkAt_compromiseSPK p stateIdx) htr
  | compromisePQSPK p stateIdx =>
    exact tracefulRkAt_run_snd (tracefulRkAt_compromisePQSPK p stateIdx) htr
  | compromiseOPK p stateIdx =>
    exact tracefulRkAt_run_snd (tracefulRkAt_compromiseOPK p stateIdx) htr
  | exposeKey me stateIdx k =>
    exact tracefulRkAt_run_snd (tracefulRkAt_exposeKey me stateIdx k) htr
  | exposeSpqr me stateIdx =>
    exact tracefulRkAt_run_snd (tracefulRkAt_exposeSpqr me stateIdx) htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulRkAt_run_snd (tracefulRkAt_exposeSkipped skippedKeyEventIdx) htr
  | attackerSend msg =>
    exact tracefulRkAt_run_snd (TracefulRkAt.sendMessage msg) htr
  | brkDH =>
    exact (TracefulRkAt.logEventPQ .BrokenDH htr).1
  | brkKEM =>
    exact (TracefulRkAt.logEventPQ .BrokenKEM htr).1

theorem traceStatesStoredRkKnown_runMoves :
    ∀ (L : List Move) (tr : ExecTrace),
      TraceStatesStoredRkKnown tr → TraceStatesStoredRkKnown (runMoves L tr).1
  | [], _, htr => htr
  | m :: ms, tr, htr =>
    traceStatesStoredRkKnown_runMoves ms (m.next tr) (traceStatesStoredRkKnown_move_next htr)

theorem traceStatesStoredRkKnown_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    TraceStatesStoredRkKnown (runTraceMoves r₀ ms) :=
  traceStatesStoredRkKnown_runMoves (r₀.setupMove :: ms) DY.Trace.nil traceStatesStoredRkKnown_nil

theorem trStateStoredRkKnown_of_mem_storedStates {r₀ : ProtocolSetup} {tr : ExecTrace}
    (htr : TraceStatesStoredRkKnown tr)
    {ls : PersistentLocalState.LocalState TRState} (hls : ls ∈ storedStates r₀ tr) :
    TrStateStoredRkKnown tr ls.state := by
  unfold storedStates DY.ExecTrace.getLocalStateAt at hls
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he
  obtain ⟨e, hat, rfl⟩ := he
  exact traceStatesStoredRkKnown_at?_st htr hat

/-- `TraceStatesStoredRkKnown (runTraceMoves r₀ ms)` implies `StoredRkKnown r₀ ms`. -/
theorem storedRkKnown_of_traceStatesStoredRkKnown {r₀ : ProtocolSetup} {ms : List Move}
    (htr : TraceStatesStoredRkKnown (runTraceMoves r₀ ms)) :
    StoredRkKnown r₀ ms := by
  intro st hst
  unfold availableStates at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  exact trStateStoredRkKnown_of_mem_storedStates htr hls

/-- `StoredRkKnown r₀ ms` holds for every move list `ms`. -/
theorem storedRkKnown_all (r₀ : ProtocolSetup) (ms : List Move) : StoredRkKnown r₀ ms :=
  storedRkKnown_of_traceStatesStoredRkKnown (traceStatesStoredRkKnown_runTrace r₀ ms)

/-- For any `ModelRun r₀ ms`, `StoredRkKnown r₀ ms` holds. -/
theorem storedRkKnown_of_modelRun {r₀ : ProtocolSetup} {ms : List Move}
    (_hRun : ModelRun r₀ ms) : StoredRkKnown r₀ ms :=
  storedRkKnown_all r₀ ms

end Symbolic.Swarm.CREF.TR
