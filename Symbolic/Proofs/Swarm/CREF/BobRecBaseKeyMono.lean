/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKey
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Monotonicity and Trace Transport of Bob's Session Base-Key Invariant

Proves monotonicity of `sessionBaseKeys` and `isCurrentSnapshot` along trace extensions, together
with the abstract transport lemmas `bobBaseKeyOn_ext` and `bobBaseKeyOn_start` for `BobBaseKeyOn`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry getLocalState_tr_fst at?_le_some)
open DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot SessionInfo)

private theorem bks_at?_of_le {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (Trace.length_le tr tr' hle)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr tr' i hi hle]

theorem bks_lt_length_of_at? {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {x : E}
    (h : (tr.at? i : Option E) = some x) : i < tr.length := by
  by_contra hi
  simp only [Trace.at?, hi, ↓reduceDIte] at h
  cases h

theorem bks_getEventAt_of_le (Ev : Type) [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT Ev)]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    tr'.getEventAt Ev i = tr.getEventAt Ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [bks_at?_of_le hle hi]

theorem bks_lt_length_of_getEventAt (Ev : Type) [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {i : Nat} {ev : Ev} (h : tr.getEventAt Ev i = some ev) : i < tr.length := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
  rcases he : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT Ev)) with _ | e
  · rw [he] at h; cases h
  · exact bks_lt_length_of_at? he

theorem bks_getLocalState_of_stored {p : Participant} {st : TRState} {i : Nat} {tr : ExecTrace}
    (h : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩) :
    ((PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st := by
  rw [getLocalState_tr_fst, h]; simp

theorem bks_stored_of_getLocalState {p : Participant} {st : TRState} {i : Nat} {tr : ExecTrace}
    (h : ((PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st) :
    (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩ := by
  rw [getLocalState_tr_fst] at h
  rcases hat : (tr.at? i : Option TRStEntry) with _ | ⟨⟨q, st'⟩⟩ <;> rw [hat] at h
  · cases h
  · dsimp only at h
    split at h
    · next hq => subst hq; injection h with h; subst h; rfl
    · cases h

/-- Base keys collected by `sessionBaseKeys` for a given `SessionInfo`. -/
def sbkOf (tr : ExecTrace) (s : SessionInfo) : List DY.Bytes :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt ComposedEvent i with
    | some (.HandshakeSession s' d) =>
      if s' = s then
        match tr.getEventAt PQXDH.PQXDHEvent d with
        | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek
        | _ => none
      else none
    | none => none

theorem sessionBaseKeys_eq_sbkOf {tr : ExecTrace} {i : Nat} {p : Participant} {st : TRState}
    (h : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩) :
    sessionBaseKeys tr i = sbkOf tr (st.sessionInfo p) := by
  unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents sbkOf
  rw [h, Option.map_some]
  dsimp only
  rw [List.filterMap_filterMap]
  have hcongr : ∀ (l : List Nat) (f g : Nat → Option DY.Bytes),
      (∀ j ∈ l, f j = g j) → l.filterMap f = l.filterMap g := by
    intro l f g hfg
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filterMap_cons, hfg x (.head _), ih (fun j hj => hfg j (.tail _ hj))]
  refine hcongr _ _ _ fun j _ => ?_
  cases tr.getEventAt ComposedEvent j with
  | none => rfl
  | some ev =>
    cases ev with
    | HandshakeSession s' d =>
      by_cases hs : s' = st.sessionInfo p
      · simp only [hs, ↓reduceIte]
        cases tr.getEventAt PQXDH.PQXDHEvent d with
        | none => rfl
        | some ev' => cases ev' <;> rfl
      · simp only [hs, ↓reduceIte]; rfl

theorem sbkOf_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') (s : SessionInfo) :
    sbkOf tr s ⊆ sbkOf tr' s := by
  intro ek hek
  unfold sbkOf at hek ⊢
  obtain ⟨i, hi, hfind⟩ := List.mem_filterMap.mp hek
  have hi' : i < tr.length := List.mem_range.mp hi
  refine List.mem_filterMap.mpr
    ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le hi' (Trace.length_le tr tr' hle)), ?_⟩
  rw [bks_getEventAt_of_le ComposedEvent hle hi']
  rcases hev : tr.getEventAt ComposedEvent i with _ | ⟨s', d⟩ <;> rw [hev] at hfind
  · cases hfind
  · dsimp only at hfind ⊢
    by_cases hs : s' = s
    · simp only [hs, ↓reduceIte] at hfind ⊢
      rcases hpq : tr.getEventAt PQXDH.PQXDHEvent d with _ | ev <;> rw [hpq] at hfind
      · cases hfind
      · rw [bks_getEventAt_of_le PQXDH.PQXDHEvent hle
          (bks_lt_length_of_getEventAt PQXDH.PQXDHEvent hpq), hpq]
        exact hfind
    · simp only [hs, ↓reduceIte] at hfind
      cases hfind

theorem sessionBaseKeys_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') (i : Nat) :
    sessionBaseKeys tr i ⊆ sessionBaseKeys tr' i := by
  rcases hat : (tr.at? i : Option TRStEntry) with _ | ⟨⟨p, st⟩⟩
  · unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt; rw [hat]; exact List.nil_subset _
  · rw [sessionBaseKeys_eq_sbkOf hat, sessionBaseKeys_eq_sbkOf (at?_le_some hle hat)]
    exact sbkOf_mono hle _

theorem sessionBaseKeys_subset_of_sinfo {tr tr' : ExecTrace} (hle : tr ≤ tr') {i j : Nat}
    {p q : Participant} {st st' : TRState} (hi : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩)
    (hj : (tr'.at? j : Option TRStEntry) = some ⟨⟨q, st'⟩⟩) (hs : st.sessionInfo p = st'.sessionInfo q) :
    sessionBaseKeys tr i ⊆ sessionBaseKeys tr' j := by
  rw [sessionBaseKeys_eq_sbkOf hi, sessionBaseKeys_eq_sbkOf hj, ← hs]
  exact sbkOf_mono hle _

theorem isCurrentSnapshot_of_le_of_lt {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat}
    (hi : i < tr.length) (h : isCurrentSnapshot tr' i = true) : isCurrentSnapshot tr i = true := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at h ⊢
  rw [bks_at?_of_le hle hi] at h
  rcases hat : (tr.at? i : Option TRStEntry) with _ | e <;> rw [hat] at h
  · cases h
  · dsimp only at h ⊢
    rw [List.all_eq_true] at h ⊢
    intro j hj
    have hj' := List.mem_range'_1.mp hj
    have hjlt : j < tr.length := by omega
    have := h j (List.mem_range'_1.mpr
      ⟨hj'.1, by have := Trace.length_le tr tr' hle; omega⟩)
    rw [bks_at?_of_le hle hjlt] at this
    exact this

theorem isCurrentSnapshot_false_of_later {tr : ExecTrace} {i j : Nat} {p : Participant}
    {st st' : TRState} (hi : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩)
    (hj : (tr.at? j : Option TRStEntry) = some ⟨⟨p, st'⟩⟩) (hij : i < j)
    (hrole : st'.initiator = st.initiator) : isCurrentSnapshot tr i = false := by
  have hjlt := bks_lt_length_of_at? hj
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [hi]
  dsimp only
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have := h j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rw [hj] at this
  simp [hrole] at this

/-- Every Bob snapshot stored at index `≥ tr.length` in `tr'` shares `sessionInfo` with some
current Bob snapshot in `tr`. -/
def NewBobSinfo (bob : Participant) (tr tr' : ExecTrace) : Prop :=
  ∀ (j : Nat) (st : TRState), tr.length ≤ j →
    (tr'.at? j : Option TRStEntry) = some ⟨⟨bob, st⟩⟩ →
    ∃ (k₀ : Nat) (st₀ : TRState), (tr.at? k₀ : Option TRStEntry) = some ⟨⟨bob, st₀⟩⟩ ∧
      isCurrentSnapshot tr k₀ = true ∧ st₀.sessionInfo bob = st.sessionInfo bob

theorem newBobSinfo_of_noNewSt {bob : Participant} {tr tr' : ExecTrace}
    (h : ∀ j, tr.length ≤ j → (tr'.at? j : Option TRStEntry) = none) : NewBobSinfo bob tr tr' := by
  intro j st hj hat
  rw [h j hj] at hat
  cases hat

/-- Transports `BobBaseKeyOn` along `tr ≤ tr'` under `NewBobSinfo`. -/
theorem bobBaseKeyOn_ext {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {bob : Participant} {tr tr' : ExecTrace} {abk : HwBytes} (hle : tr ≤ tr')
    (hnew : NewBobSinfo bob tr tr') (h : BobBaseKeyOn interpretation S g bob tr abk) :
    BobBaseKeyOn interpretation S g bob tr' abk := by
  intro k st hst hcur
  have hat := bks_stored_of_getLocalState hst
  by_cases hk : k < tr.length
  · rw [bks_at?_of_le hle hk] at hat
    obtain ⟨ek, hek, heq⟩ := h k st (bks_getLocalState_of_stored hat)
      (isCurrentSnapshot_of_le_of_lt hle hk hcur)
    exact ⟨ek, sessionBaseKeys_mono hle k hek, heq⟩
  · obtain ⟨k₀, st₀, hat₀, hcur₀, hs⟩ := hnew k st (Nat.le_of_not_lt hk) hat
    obtain ⟨ek, hek, heq⟩ := h k₀ st₀ (bks_getLocalState_of_stored hat₀) hcur₀
    exact ⟨ek, sessionBaseKeys_subset_of_sinfo hle hat₀ hat hs hek, heq⟩

/-- Establishes `BobBaseKeyOn` for `ecKey (gamma interpretation S g ek)` on `tr'` when every Bob
snapshot is a responder snapshot, at least one new Bob snapshot is stored at index `≥ tr.length`,
and every new Bob snapshot contains `ek` in `sessionBaseKeys`. -/
theorem bobBaseKeyOn_start {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {bob : Participant} {tr tr' : ExecTrace} {ek : DY.Bytes}
    (hrole : ∀ (i : Nat) (st : TRState), (tr'.at? i : Option TRStEntry) = some ⟨⟨bob, st⟩⟩ →
      st.initiator = false)
    (hex : ∃ (j : Nat) (st : TRState), tr.length ≤ j ∧
      (tr'.at? j : Option TRStEntry) = some ⟨⟨bob, st⟩⟩)
    (hnew : ∀ (j : Nat) (st : TRState), tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨bob, st⟩⟩ → ek ∈ sessionBaseKeys tr' j) :
    BobBaseKeyOn interpretation S g bob tr' (ecKey (gamma interpretation S g ek)) := by
  intro k st hst hcur
  have hat := bks_stored_of_getLocalState hst
  by_cases hk : k < tr.length
  · exfalso
    obtain ⟨j, st', hj, hatj⟩ := hex
    rw [isCurrentSnapshot_false_of_later hat hatj (by omega)
      (by rw [hrole _ _ hatj, hrole _ _ hat])] at hcur
    cases hcur
  · exact ⟨ek, hnew k st (Nat.le_of_not_lt hk) hat, rfl⟩

end Symbolic.Swarm.CREF
