/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
import DY.EquationalTheory.Concat
import Symbolic.Specifications.Model.EquationalTheory.Trunc
public import Symbolic.Specifications.Refinement.TraceExplanation
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

/-!
# Disjointness of Parsed MACs from Plaintext Atoms

Every `.pt` visible entry emitted along a composed run comes from the initial 32-byte random draw
`randTerm i 32` of an encrypt transition, whereas `parseTrSignalMsg` bounds `msg₀.mac.length ≤ 8`.
Hence `msg₀.mac ∉ plaintextTerms (runVis r₀ ms ++ extra)` (`g1_rep_ptAtoms_tr`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg)

open DY DY.Comparse DY.Literal DY.Libsignal

/-! ## Plaintext atoms are 32-byte random draws -/

private theorem run_bind_fst_smc_tr32 {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd_smc_tr32 {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem preservesTrace_getLocalState_tr32 (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  unfold _root_.guard
  rw [run_bind_snd_smc_tr32, run_bind_fst_smc_tr32, run_bind_snd_smc_tr32, Traceful.run_mk]
  rcases (tr.at? stH : Option (PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · simp only [Traceful.run_pure, Traceful.run_bind]
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; simp only [Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp]
      simp only [Traceful.run_failure]
      simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl

private theorem preservesTrace_guard_tr32 (p : Prop) [Decidable p] (tr : ExecTrace) :
    ((_root_.guard p : Traceful Unit).run tr).2.val = tr := by
  unfold _root_.guard
  split <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem run_bind_pure_unit_val_tr32 {α : Type} (x : Traceful α) (tr : ExecTrace) :
    (((x >>= fun _ => pure ()) : Traceful Unit).run tr).2.val = (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨o, trMid, _⟩
  cases o <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private def Draws32First (tr tr' : ExecTrace) : Prop :=
  tr' = tr ∨ ∃ e : DY.Random.ExecEntryT, (tr'.at? tr.length : Option DY.Random.ExecEntryT) = some e ∧
    e.length = 32

private theorem genRand_bind_draws32_tr32 {α : Type} (f : DY.Bytes → Traceful α) (tr : ExecTrace) :
    Draws32First tr ((Random.genRand 32 >>= f).run tr).2.val := by
  refine .inr ?_
  rw [run_bind_snd_smc_tr32]
  have h1 : ((Random.genRand 32 : Traceful DY.Bytes).run tr).1 = some (randTerm tr.length 32) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  have h2 : ((Random.genRand 32 : Traceful DY.Bytes).run tr).2.val =
      tr.append ({ length := 32 } : DY.Random.ExecEntryT) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  rw [h1, h2]
  dsimp only
  let tr₁ := tr.append ({ length := 32 } : DY.Random.ExecEntryT)
  have hle : tr₁ ≤ ((f (randTerm tr.length 32)).run tr₁).2.val :=
    ((f (randTerm tr.length 32)).run tr₁).2.property
  have hlt1 : tr.length < tr₁.length := by
    simp [tr₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt2 : tr.length < ((f (randTerm tr.length 32)).run tr₁).2.val.length :=
    Nat.lt_of_lt_of_le hlt1 (Trace.length_le tr₁ _ hle)
  refine ⟨{ length := 32 }, ?_, rfl⟩
  change (((f (randTerm tr.length 32)).run tr₁).2.val.at? tr.length : Option DY.Random.ExecEntryT) = _
  unfold Trace.at?
  rw [dite_eq_left hlt2, ← Trace.at_le tr₁ _ tr.length hlt1 hle]
  have hat1 : tr₁.at tr.length hlt1 = TraceEntryHas.inj ({ length := 32 } : DY.Random.ExecEntryT) := by
    simp [tr₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2]
  rw [hat1, TraceEntryHas.inj_proj_eq]

private theorem preservesTrace_bind_draws32_tr32 {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr : ExecTrace} (hx : (x.run tr).2.val = tr)
    (hf : ∀ a, Draws32First tr ((f a).run tr).2.val) :
    Draws32First tr ((x >>= f).run tr).2.val := by
  rw [run_bind_snd_smc_tr32, hx]
  split
  · exact hf _
  · exact .inl rfl

private theorem messageEncrypt_draws32_tr32 (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) :
    Draws32First tr ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold TripleRatchet.messageEncrypt
  refine preservesTrace_bind_draws32_tr32 (preservesTrace_getLocalState_tr32 me stateIdx tr)
    fun st => ?_
  refine preservesTrace_bind_draws32_tr32
    (preservesTrace_guard_tr32 (st.ns ≠ TripleRatchet.u32Max) tr) fun _ => ?_
  exact genRand_bind_draws32_tr32 _ tr

private theorem messageEncryptAbort_draws32_tr32 (me : Participant) (stateIdx : Nat)
    (tr : ExecTrace) :
    Draws32First tr ((TripleRatchet.messageEncryptAbort me stateIdx).run tr).2.val := by
  unfold TripleRatchet.messageEncryptAbort
  refine preservesTrace_bind_draws32_tr32 (preservesTrace_getLocalState_tr32 me stateIdx tr)
    fun _ => ?_
  exact genRand_bind_draws32_tr32 _ tr

private theorem newRandoms_head_tr32 {tr tr' : ExecTrace} (hd : Draws32First tr tr')
    {m : DY.Bytes} {k : Nat} {rest : List (DY.Bytes × Nat)}
    (h : newRandoms tr tr' = (m, k) :: rest) : m = randTerm tr.length 32 := by
  rcases hd with rfl | ⟨e, he, h32⟩
  · simp [newRandoms, newIndices] at h
  · have hlt : tr.length < tr'.length := by
      by_contra hn
      unfold Trace.at? at he
      simp [hn] at he
    unfold newRandoms newIndices at h
    rw [show tr'.length - tr.length = (tr'.length - tr.length - 1) + 1 by omega,
      List.range'_succ, List.filterMap_cons, he] at h
    simp only [Option.map_some, List.cons.injEq, Prod.mk.injEq] at h
    rw [← h.1.1, h32]

private theorem encDraws_pt_tr32 {L : List (DY.Bytes × Nat)} {v : VisEntry}
    (hv : v ∈ encDraws L) (hk : v.kind = .pt) :
    ∃ m k rest, L = (m, k) :: rest ∧ v.terms = [m] := by
  cases L with
  | nil => cases hv
  | cons hd rest =>
    obtain ⟨m, k⟩ := hd
    simp only [encDraws, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨r, _, rfl⟩
    · exact ⟨m, k, rest, rfl, rfl⟩
    · cases hk

private theorem encVis_pt_tr32 {tr tr' : ExecTrace} {wrap : Option (Nat × Nat)} {ws : Bool}
    {v : VisEntry} (hv : v ∈ encVis tr tr' wrap ws) (hk : v.kind = .pt) :
    ∃ m k rest, newRandoms tr tr' = (m, k) :: rest ∧ v.terms = [m] := by
  unfold encVis at hv
  rcases List.mem_append.mp hv with h | h
  · exact encDraws_pt_tr32 h hk
  · exfalso
    cases ws with
    | false => cases h
    | true =>
      simp only [ite_true] at h
      unfold encSend at h
      split at h
      · split at h <;> simp only [List.mem_singleton] at h <;> (subst h; cases hk)
      · cases h

private theorem aliceDraws_not_pt_tr32 (done : Option Nat) (L : List DY.Bytes) {v : VisEntry}
    (hv : v ∈ aliceDraws done L) : v.kind ≠ .pt := by
  match L, hv with
  | [_], hv => simp only [aliceDraws, List.mem_singleton] at hv; subst hv; intro hk; cases hk
  | _ :: _ :: _, hv =>
    simp only [aliceDraws, kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map] at hv
    rcases hv with (rfl | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> (intro hk; cases hk)

private theorem decVis_not_pt_tr32 (tr tr' : ExecTrace) (stateIdx msgIdx : Nat) (wrapped : Bool)
    {v : VisEntry} (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped) : v.kind ≠ .pt := by
  unfold decVis at hv
  rcases List.mem_append.mp hv with h | h
  · rcases List.mem_append.mp h with h | h
    · cases hm : tr.getMessageSentAt msgIdx <;> simp only [hm, Option.map_none, Option.map_some,
        Option.toList_none, Option.toList_some, List.not_mem_nil, List.mem_singleton] at h
      subst h; intro hk; cases hk
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h; intro hk; cases hk
  · cases hm : receivedPlaintext tr tr' <;> simp only [hm, Option.map_none, Option.map_some,
      Option.toList_none, Option.toList_some, List.not_mem_nil, List.mem_singleton] at h
    subst h; intro hk; cases hk

private theorem exposures_not_pt_tr32 (tr tr' : ExecTrace) {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind ≠ .pt := by
  unfold exposures at hv
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold pqExposureAt at hj
    dsimp only at hj
    split at hj <;> cases hj <;> (intro hk; cases hk)
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold trExposureAt at hj
    dsimp only at hj
    split at hj <;> cases hj <;> (intro hk; cases hk)

private theorem moveNext_encryptFail_tr32 (me : Participant) (stateIdx coinsLen : Nat)
    (tr : ExecTrace) : Draws32First tr ((Move.encryptFail me stateIdx coinsLen).next tr) := by
  dsimp only [Move.next, Move.act]
  refine preservesTrace_bind_draws32_tr32
    (by unfold TripleRatchet.traceLength; rw [Traceful.run_mk])
    fun n => ?_
  rw [run_bind_pure_unit_val_tr32]
  exact messageEncrypt_draws32_tr32 me stateIdx coinsLen (n + 3) tr

private theorem moveVis_pt_tr32 (m : Move) (tr : ExecTrace) {v : VisEntry}
    (hv : v ∈ m.vis tr) (hk : v.kind = .pt) : ∃ i, v.terms = [randTerm i 32] := by
  unfold Move.vis at hv
  rcases List.mem_append.mp hv with h | h
  · have henc : ∀ {wrap : Option (Nat × Nat)} {ws : Bool},
        Draws32First tr (m.next tr) → v ∈ encVis tr (m.next tr) wrap ws →
          ∃ i, v.terms = [randTerm i 32] := by
      intro wrap ws hd h
      obtain ⟨m', k, rest, hnr, hterms⟩ := encVis_pt_tr32 h hk
      exact ⟨tr.length, by rw [hterms, newRandoms_head_tr32 hd hnr]⟩
    cases m with
    | encrypt me stateIdx coinsLen pqIdx wrap =>
      refine henc ?_ h
      dsimp only [Move.next, Move.act]
      rw [run_bind_pure_unit_val_tr32]
      exact messageEncrypt_draws32_tr32 me stateIdx coinsLen pqIdx tr
    | encryptAbort me stateIdx =>
      refine henc ?_ h
      dsimp only [Move.next, Move.act]
      rw [run_bind_pure_unit_val_tr32]
      exact messageEncryptAbort_draws32_tr32 me stateIdx tr
    | encryptFail me stateIdx coinsLen => exact henc (moveNext_encryptFail_tr32 me stateIdx coinsLen tr) h
    | aliceStart _ _ _ _ hh shown =>
      exfalso
      have h' := List.mem_of_mem_take h
      unfold aliceVis at h'
      rcases List.mem_cons.mp h' with rfl | h''
      · cases hk
      · exact aliceDraws_not_pt_tr32 _ _ h'' hk
    | bobStart b _ kh _ mh _ _ shown =>
      exfalso
      have h' := List.mem_of_mem_take h
      unfold bobVis at h'
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at h'
      rcases h' with rfl | (⟨_, _, rfl⟩ | h'')
      · cases hk
      · cases hk
      · revert h''
        generalize receivedPlaintext _ _ = o
        cases o <;> simp only [Option.map_none, Option.map_some, Option.toList_none,
          Option.toList_some, List.not_mem_nil, List.mem_singleton, IsEmpty.forall_iff]
        intro h''; subst h''; cases hk
    | decrypt _ stateIdx msgIdx _ _ wrapped =>
      exact absurd hk (decVis_not_pt_tr32 _ _ stateIdx msgIdx wrapped h)
    | decryptSkipped _ _ msgIdx _ _ _ wrapped =>
      exact absurd hk (decVis_not_pt_tr32 _ _ _ msgIdx wrapped h)
    | reject draws =>
      exfalso
      simp only [List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨_, _, rfl⟩ <;> cases hk
    | _ => cases h
  · exact absurd hk (exposures_not_pt_tr32 _ _ h)

private theorem runMoves_pt_tr32 : ∀ (L : List Move) (tr : ExecTrace) {v : VisEntry},
    v ∈ (runMoves L tr).2 → v.kind = .pt → ∃ i, v.terms = [randTerm i 32]
  | [], _, _, hv, _ => by cases hv
  | m :: ms, tr, _, hv, hk => by
    simp only [runMoves] at hv
    rcases List.mem_append.mp hv with hm | hms
    · exact moveVis_pt_tr32 m tr hm hk
    · exact runMoves_pt_tr32 ms (m.next tr) hms hk

/-- Every plaintext atom `p ∈ plaintextTerms (runVis r₀ ms ++ extra)` is `randTerm i 32` when
`extra` contains no `.pt` entries. -/
theorem ptAtoms_runVis_mem_inv_tr32 (r₀ : ProtocolSetup) (ms : List Move) (extra : List VisEntry)
    (hextra : ∀ v ∈ extra, v.kind ≠ .pt) {p : DY.Bytes}
    (hp : p ∈ plaintextTerms (runVis r₀ ms ++ extra)) :
    ∃ i, p = randTerm i 32 := by
  unfold plaintextTerms at hp
  obtain ⟨v, hv_filt, hpv⟩ := List.mem_flatMap.mp hp
  rw [List.mem_filter] at hv_filt
  obtain ⟨hv_mem, hk_beq⟩ := hv_filt
  have hk : v.kind = .pt := by simpa using hk_beq
  rcases List.mem_append.mp hv_mem with hvis | hx
  · obtain ⟨i, hterms⟩ := runMoves_pt_tr32 _ _ hvis hk
    rw [hterms, List.mem_singleton] at hpv
    exact ⟨i, hpv⟩
  · exact absurd hk (hextra v hx)

theorem length_randTerm32_tr32 (i : Nat) : (randTerm i 32 : DY.Bytes).length = 32 := by
  unfold randTerm
  rw [DY.Bytes.length.eq]
  exact Symbolic.DYBridge.DY.Random.Random.length_eq_1 i 32 _

theorem not_mem_ptAtoms_of_length_lt_32_tr32 (r₀ : ProtocolSetup) (ms : List Move)
    (extra : List VisEntry) (hextra : ∀ v ∈ extra, v.kind ≠ .pt)
    {u : DY.Bytes} (hlt : u.length < 32) :
    u ∉ plaintextTerms (runVis r₀ ms ++ extra) := by
  intro hp
  obtain ⟨i, rfl⟩ := ptAtoms_runVis_mem_inv_tr32 r₀ ms extra hextra hp
  rw [length_randTerm32_tr32] at hlt
  omega

theorem split_eq_some_concat_and_length_tr32 {t : DY.Bytes} {n : Nat} {l r : DY.Bytes}
    (hsp : Concat.split t n = some (l, r)) :
    t = Concat.concat l r ∧ l.length = n := by
  dsimp only [Concat.split, Concat.CanConcat.split] at hsp
  have hv := DY.Bytes.pack_view? DY.Concat.Concat.SubF t
  cases hview : t.view? DY.Concat.Concat.SubF with
  | none => rw [hview] at hsp; cases hsp
  | some c =>
    rw [hview] at hsp hv
    dsimp only at hsp hv
    split at hsp
    · next hlen =>
      injection hsp with hpair
      injection hpair with hl hr
      subst hl hr
      exact ⟨hv.symm, hlen⟩
    · cases hsp

theorem parseTrSignalMsg_eq_some_concat_and_mac_length_le_8_tr32
    {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (hparse : parseTrSignalMsg t₀ = some msg₀) :
    t₀ = Concat.concat msg₀.wire msg₀.mac ∧ msg₀.mac.length ≤ 8 := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  obtain ⟨⟨wire, mac⟩, hsp, f, _hwf, rfl⟩ := hparse
  dsimp only
  obtain ⟨hcat, hlen⟩ := split_eq_some_concat_and_length_tr32 hsp
  have hcat_len : t₀.length = wire.length + mac.length := by
    rw [hcat, Concat.length_concat]
  have htr8 : Trunc.trunc8Length = 8 := rfl
  rw [hcat_len, htr8] at hlen
  exact ⟨hcat, by omega⟩

/-! ## Disjointness of parsed MACs from `plaintextTerms` -/

/-- The MAC of a parsed Triple Ratchet message has symbolic length at most 8, hence is never in
`plaintextTerms (runVis r₀ ms ++ extra)`. -/
theorem g1_rep_ptAtoms_tr (r₀ : ProtocolSetup) (ms : List Move) {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (extra : List VisEntry) (hextra : ∀ v ∈ extra, v.kind ≠ .pt)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) :
    msg₀.mac ∉ plaintextTerms (runVis r₀ ms ++ extra) :=
  not_mem_ptAtoms_of_length_lt_32_tr32 r₀ ms extra hextra
    (Nat.lt_of_le_of_lt (parseTrSignalMsg_eq_some_concat_and_mac_length_le_8_tr32 hparse₀).2
      (by decide))

end Symbolic.Swarm.CREF.TR.G1
