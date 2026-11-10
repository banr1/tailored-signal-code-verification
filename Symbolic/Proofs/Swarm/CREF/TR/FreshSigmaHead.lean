/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Prefix Faithfulness Under Fresh Ghost Updates

Proves `matchedPrefix_updateFreshAt`: updating the ghost randomness table `g.σ` at any timestamp
at least `(runTraceMoves r₀ ms).length` preserves `MatchedPrefix`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.FreshSigma

cref_open
open Symbolic.Swarm.CREF.TR
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)

theorem stampsLt_of_mem_newRandoms {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr tr' : ExecTrace} (hlen : tr'.length ≤ ts) {p : DY.Bytes × Nat}
    (hp : p ∈ newRandoms tr tr') : StampsLt i S g ts p.1 := by
  unfold newRandoms at hp
  obtain ⟨idx, hidx, hmap⟩ := List.mem_filterMap.mp hp
  simp only [newIndices, List.mem_range'_1] at hidx
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
  exact stampsLt_rand_of_lt i S g e.length (by omega)

theorem visStampsLt_of_mem_kyberCoinEntries {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {entropy : DY.Bytes} (he : StampsLt i S g ts entropy) {v : VisEntry}
    (hv : v ∈ kyberCoinEntries entropy) : VisStampsLt i S g ts v := by
  unfold kyberCoinEntries at hv
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]; exact he

theorem visStampsLt_of_mem_aliceDraws {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} (done : Option Nat) :
    ∀ (L : List DY.Bytes), (∀ t ∈ L, StampsLt i S g ts t) →
      ∀ {v : VisEntry}, v ∈ aliceDraws done L → VisStampsLt i S g ts v
  | [], _, _, hv => by simp [aliceDraws] at hv
  | [ek], hL, v, hv => by
    rcases List.mem_singleton.mp hv with rfl
    refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]; exact hL ek (by simp)
  | ek :: entropy :: rest, hL, v, hv => by
    simp only [aliceDraws, List.cons_append, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]; exact hL ek (by simp)
    · exact visStampsLt_of_mem_kyberCoinEntries (hL entropy (by simp)) hv
    · obtain ⟨dhsA, hdhsA, rfl⟩ := List.mem_map.mp hv
      refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
      exact hL dhsA (List.mem_cons_of_mem ek (List.mem_cons_of_mem entropy (List.mem_of_mem_take hdhsA)))

theorem visStampsLt_of_mem_encDraws {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} :
    ∀ (L : List (DY.Bytes × Nat)), (∀ p ∈ L, StampsLt i S g ts p.1) →
      ∀ {v : VisEntry}, v ∈ encDraws L → VisStampsLt i S g ts v
  | [], _, _, hv => by simp [encDraws] at hv
  | (m, sz) :: rest, hL, v, hv => by
    simp only [encDraws, List.mem_cons] at hv
    rcases hv with rfl | hv
    · refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]; exact hL (m, sz) (by simp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
      exact hL r (List.mem_cons_of_mem _ (List.mem_of_mem_filter hr))

theorem stampsLt_of_receivedPlaintext {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr tr' T : ExecTrace} (hle : tr' ≤ T) (htr : TraceEntriesLt i S g ts T) {m : DY.Bytes}
    (h : receivedPlaintext tr tr' = some m) : StampsLt i S g ts m := by
  unfold receivedPlaintext at h
  obtain ⟨idx, _, hfind⟩ := List.exists_of_findSome?_eq_some h
  split at hfind
  · next me peer rk n msg hev =>
    cases hfind
    have hat' : (tr'.at? idx : Option TREntry) = some ⟨.Received me peer rk n m⟩ := by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
      rcases he : (tr'.at? idx : Option TREntry) with _ | e
      · rw [he] at hev; cases hev
      · rw [he] at hev; injection hev with hev; cases e; subst hev; rfl
    have hatT := DY.Trace.at?_le (EntryT := TREntry) tr' T idx hle
    rw [hat'] at hatT
    exact traceEntriesLt_at?_tr htr hatT
  · cases hfind

theorem pqEventStampsLt_of_at?_le {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr T : ExecTrace} (hle : tr ≤ T) (htr : TraceEntriesLt i S g ts T) {j : Nat} {e : PQEvEntry}
    (he : (tr.at? j : Option PQEvEntry) = some e) : PQEventStampsLt i S g ts e.ev := by
  have hatT := DY.Trace.at?_le (EntryT := PQEvEntry) tr T j hle
  rw [he] at hatT
  exact traceEntriesLt_at?_pqev htr hatT

theorem stampsLt_of_mem_sessionBaseKeys {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr T : ExecTrace} (hle : tr ≤ T) (htr : TraceEntriesLt i S g ts T) {stateIdx : Nat}
    {ek : DY.Bytes} (hek : ek ∈ sessionBaseKeys tr stateIdx) : StampsLt i S g ts ek := by
  unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt sessionHandshakeEvents at hek
  split at hek
  · obtain ⟨ev, hev_mem, hfind⟩ := List.mem_filterMap.mp hek
    obtain ⟨idx, _, hget⟩ := List.mem_filterMap.mp hev_mem
    split at hfind
    · cases hfind
      split at hget
      · split at hget
        · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
          rcases he : (tr.at? _ : Option PQEvEntry) with _ | e
          · rw [he] at hget; cases hget
          · rw [he] at hget; injection hget with hget; cases e; subst hget
            exact pqEventStampsLt_of_at?_le hle htr he
        · cases hget
      · cases hget
    · cases hfind
  · cases hek

theorem stampsLt_of_mem_bobDoneBaseKeys {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr T : ExecTrace} (hle : tr ≤ T) (htr : TraceEntriesLt i S g ts T)
    {ek : DY.Bytes} (hek : ek ∈ bobDoneBaseKeys tr) : StampsLt i S g ts ek := by
  unfold bobDoneBaseKeys at hek
  obtain ⟨idx, _, hfind⟩ := List.mem_filterMap.mp hek
  split at hfind
  · next hev =>
    cases hfind
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
    rcases he : (tr.at? idx : Option PQEvEntry) with _ | e
    · rw [he] at hev; cases hev
    · rw [he] at hev; injection hev with hev; cases e; subst hev
      exact pqEventStampsLt_of_at?_le hle htr he
  · cases hfind

theorem visOf_visStampsLt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (m : Move) (tr : ExecTrace) (hs : OpkNetOK tr) {T : ExecTrace} (hle : m.next tr ≤ T)
    (hlen : T.length ≤ ts) (htr : TraceEntriesLt i S g ts T)
    {v : VisEntry} (hv : v ∈ m.vis tr) :
    VisStampsLt i S g ts v := by
  have hlen' : (m.next tr).length ≤ ts := Nat.le_trans (DY.Trace.length_le _ _ hle) hlen
  have hvk : VisKnown T v := (move_known m hs hv).mono hle
  have hobsT : (v.kind = .send ∨ v.kind = .recv ∨ v.kind = .leak) →
      ∀ t ∈ v.terms, StampsLt i S g ts t :=
    fun hk t ht => traceEntriesLt_knows htr (hvk hk t ht)
  have hobs : (v.kind = .send ∨ v.kind = .recv ∨ v.kind = .leak) → layoutKeys v.layout = [] →
      VisStampsLt i S g ts v :=
    fun hk hl => visStampsLt_of_terms hl (hobsT hk)
  unfold Move.vis at hv
  rcases List.mem_append.mp hv with hv | hv
  · cases m with
    | aliceStart _ _ _ _ h _ =>
      have hv' := List.mem_of_mem_take hv
      unfold aliceVis at hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hobs (.inr (.inl rfl)) rfl
      · refine visStampsLt_of_mem_aliceDraws _ _ (fun t ht => ?_) hv'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
        exact stampsLt_of_mem_newRandoms hlen' hp
    | bobStart _ _ _ _ mh _ _ _ =>
      have hv' := List.mem_of_mem_take hv
      unfold bobVis at hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hobs (.inr (.inl rfl)) rfl
      · rcases List.mem_append.mp hv' with hv' | hv'
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv'
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact stampsLt_of_mem_newRandoms hlen' hr
        · rcases hp : receivedPlaintext tr _ with _ | pt
          · rw [hp] at hv'; cases hv'
          · rw [hp] at hv'
            rcases List.mem_singleton.mp hv' with rfl
            refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
            exact stampsLt_of_receivedPlaintext hle htr hp
    | encrypt _ _ _ _ wrap =>
      unfold encVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact visStampsLt_of_mem_encDraws _ (fun _ hp => stampsLt_of_mem_newRandoms hlen' hp) hv
      · simp only [↓reduceIte] at hv; unfold encSend at hv
        split at hv
        · split at hv <;> (rcases List.mem_singleton.mp hv with rfl; exact hobs (.inl rfl) rfl)
        · cases hv
    | encryptAbort _ _ =>
      unfold encVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact visStampsLt_of_mem_encDraws _ (fun _ hp => stampsLt_of_mem_newRandoms hlen' hp) hv
      · simp at hv
    | encryptFail _ _ _ =>
      unfold encVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact visStampsLt_of_mem_encDraws _ (fun _ hp => stampsLt_of_mem_newRandoms hlen' hp) hv
      · simp at hv
    | decrypt _ _ msgIdx _ _ wrapped =>
      unfold decVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · rcases hm : tr.getMessageSentAt msgIdx with _ | b
          · rw [hm] at hv; cases hv
          · rw [hm] at hv; rcases List.mem_singleton.mp hv with rfl
            refine ⟨hobsT (.inr (.inl rfl)), ?_⟩
            cases wrapped
            · intro _ ht; cases ht
            · exact fun ek hek => stampsLt_of_mem_sessionBaseKeys (DY.Trace.le_trans _ _ _ (Move.le_next _ tr) hle) htr hek
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact stampsLt_of_mem_newRandoms hlen' hr
      · rcases hp : receivedPlaintext tr _ with _ | pt
        · rw [hp] at hv; cases hv
        · rw [hp] at hv; rcases List.mem_singleton.mp hv with rfl
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact stampsLt_of_receivedPlaintext hle htr hp
    | decryptSkipped _ _ msgIdx _ _ _ wrapped =>
      unfold decVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · rcases hm : tr.getMessageSentAt msgIdx with _ | b
          · rw [hm] at hv; cases hv
          · rw [hm] at hv; rcases List.mem_singleton.mp hv with rfl
            refine ⟨hobsT (.inr (.inl rfl)), ?_⟩
            cases wrapped
            · intro _ ht; cases ht
            · exact fun ek hek => stampsLt_of_mem_sessionBaseKeys (DY.Trace.le_trans _ _ _ (Move.le_next _ tr) hle) htr hek
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact stampsLt_of_mem_newRandoms hlen' hr
      · rcases hp : receivedPlaintext tr _ with _ | pt
        · rw [hp] at hv; cases hv
        · rw [hp] at hv; rcases List.mem_singleton.mp hv with rfl
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact stampsLt_of_receivedPlaintext hle htr hp
    | reject draws =>
      rcases List.mem_cons.mp hv with rfl | hv
      · exact visStampsLt_of_terms rfl fun _ ht => by cases ht
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; exact visStampsLt_of_terms rfl fun _ ht => by cases ht
    | setup _ _ _ | compromiseIK _ _ | compromiseSPK _ _ | compromisePQSPK _ _
    | compromiseOPK _ _ | exposeKey _ _ _ | exposeSpqr _ _ | exposeSkipped _
    | attackerSend _ => cases hv
    | brkDH =>
      cases hv
    | brkKEM =>
      cases hv
  · unfold exposures at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hv
      unfold pqExposureAt at hj
      split at hj <;> (try cases hj) <;> exact hobs (.inr (.inr rfl)) rfl
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hv
      unfold trExposureAt at hj
      split at hj <;> (try cases hj) <;> exact hobs (.inr (.inr rfl)) rfl

theorem runMoves_visStampsLt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} :
    ∀ (L : List Move) (tr : ExecTrace),
      OpkNetOK tr →
      (runMoves L tr).1.length ≤ ts →
      TraceEntriesLt i S g ts (runMoves L tr).1 →
      ∀ v ∈ (runMoves L tr).2, VisStampsLt i S g ts v
  | [], _, _, _, _, _, hv => by cases hv
  | m :: ms, tr, hs, hlen, htr, v, hv => by
    simp only [runMoves] at hv hlen htr
    rcases List.mem_append.mp hv with hm | hms
    · exact visOf_visStampsLt m tr hs (runMoves_le ms (m.next tr)) hlen htr hm
    · exact runMoves_visStampsLt ms (m.next tr) (hs.next m) hlen htr v hms

theorem fst_lt_of_mem_setupRandomsAt {r : ProtocolSetup} (_hNe : r.alice ≠ r.bob) {p : Nat × Nat}
    (hp : p ∈ setupRandomsAt r) : p.1 < (setupTrace r).length := by
  unfold setupRandomsAt newIndices at hp
  obtain ⟨i, hi, hp_eq⟩ := List.mem_filterMap.mp hp
  simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero, List.mem_range'_1,
    Nat.zero_add, Option.map_eq_some_iff] at hi hp_eq
  obtain ⟨_, _, rfl⟩ := hp_eq
  exact hi.2

theorem setupTrace_length_pos (r : ProtocolSetup) : 0 < (setupTrace r).length := by
  change 0 < ((setupAct r.alice r.bob r.withOpk).run DY.Trace.nil).2.val.length
  unfold setupAct; rw [Traceful.run_bind]
  have hrun_a := Symbolic.Swarm.CREF.TR.runs_registerIdentity_a r.alice
  have h1 : ((DY.Libsignal.PQXDH.registerIdentity r.alice).run DY.Trace.nil).1 = some 4 ∧
      ((DY.Libsignal.PQXDH.registerIdentity r.alice).run DY.Trace.nil).2.val.length = 5 := by
    refine ⟨hrun_a.1, ?_⟩
    rw [hrun_a.2]
    simp only [Symbolic.Swarm.CREF.TR.setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases hrun1 : (DY.Libsignal.PQXDH.registerIdentity r.alice).run DY.Trace.nil with ⟨o1, tr1, _⟩
  rw [hrun1] at h1; dsimp only at h1; rcases h1 with ⟨rfl, hlen1⟩; dsimp only
  have hle := DY.Trace.length_le _ _ ((do
    let hB ← DY.Libsignal.PQXDH.registerIdentity r.bob
    let _ ← DY.Libsignal.PQXDH.genSignedPrekey r.bob hB
    let _ ← DY.Libsignal.PQXDH.genPQPrekey r.bob hB
    if r.withOpk then do let _ ← DY.Libsignal.PQXDH.genOneTimePrekey r.bob; pure ()
    else pure ()).run tr1).2.property
  exact Nat.lt_of_lt_of_le (by omega) hle

theorem stampsLt_setupPublic {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {r₀ : ProtocolSetup} {ms : List Move} {ts : Nat}
    (hts : (runTraceMoves r₀ ms).length ≤ ts)
    (htr : TraceEntriesLt i S g ts (runTraceMoves r₀ ms)) (k : Nat) :
    StampsLt i S g ts (setupPublic r₀ k) := by
  have hsetup_le : (setupTrace r₀).length ≤ ts :=
    Nat.le_trans (DY.Trace.length_le _ _ (setupTrace_le_runTrace r₀ ms)) hts
  have hpos := setupTrace_length_pos r₀
  unfold setupPublic
  rcases hget : (setupSent r₀)[k]? with _ | t
  · exact stampsLt_rand_of_lt i S g 0 (by omega)
  · exact traceEntriesLt_knows htr (setupSent_known (List.mem_of_getElem? hget))

theorem compat_updateFreshAt {interpretation : ExternInterpretation}
    (r₀ : ProtocolSetup) (hNe : r₀.alice ≠ r₀.bob) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) {ts : Nat}
    (hts : (runTraceMoves r₀ ms).length ≤ ts)
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms))
    (n : Nat) (m : DY.Libsignal.HwBytes)
    (hc : GhostAndSemMatchSetup interpretation r₀ S g) :
    GhostAndSemMatchSetup interpretation r₀ S { g with σ := updateFreshAt g.σ ts n m } := by
  have hsetup_le : (setupTrace r₀).length ≤ ts :=
    Nat.le_trans (DY.Trace.length_le _ _ (setupTrace_le_runTrace r₀ ms)) hts
  refine ⟨fun p hp => ?_, fun t ht => ?_, hc.2.2⟩
  · have hlt : p.1 < (setupTrace r₀).length := fst_lt_of_mem_setupRandomsAt hNe hp
    have hne : ¬(p.1 = ts ∧ p.2 = n) := by omega
    simp only [updateFreshAt, hne, ↓reduceIte]
    exact hc.1 p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · unfold ProtocolSetup.spkSigTerm
      rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m (setupPublic r₀ 5)
          (stampsLt_setupPublic hts htr 5)]
      exact hc.2.1 r₀.spkSigTerm (by simp)
    · unfold ProtocolSetup.pqpkPubTerm
      rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m (setupPublic r₀ 6)
          (stampsLt_setupPublic hts htr 6)]
      exact hc.2.1 r₀.pqpkPubTerm (by simp)
    · unfold ProtocolSetup.pqpkSigTerm
      rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m (setupPublic r₀ 7)
          (stampsLt_setupPublic hts htr 7)]
      exact hc.2.1 r₀.pqpkSigTerm (by simp)

private theorem isRegisteredB_setupTr1_self (a : Participant) :
    (!DY.Libsignal.PQXDH.isRegisteredB (setupTr1 a) a) = false := by
  have hbeq : (a == a) = true := beq_self_eq_true a
  have hlen : (setupTr1 a).length = 5 := by
    simp only [Symbolic.Swarm.CREF.TR.setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hrng : List.range 5 = [0, 1, 2, 3, 4] := rfl
  unfold DY.Libsignal.PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [hlen, hrng]
  simp only [List.any_cons, List.any_nil, Bool.or_false,
    setupTr1_at?_ev_0, setupTr1_at?_ev_1, setupTr1_at?_ev_2,
    setupTr1_at?_ev_3, setupTr1_at?_ev_4, hbeq]
  rfl

private theorem setupTrace_eq_self (r : ProtocolSetup) (hEq : r.alice = r.bob) :
    setupTrace r = setupTr1 r.alice := by
  change ((setupAct r.alice r.bob r.withOpk).run DY.Trace.nil).2.val = setupTr1 r.alice
  rw [← hEq]
  unfold setupAct
  rw [run_bind_snd]
  have ha := runs_registerIdentity_a r.alice
  rw [ha.1, ha.2]
  dsimp only
  rw [run_bind_snd]
  have hb : ((DY.Libsignal.PQXDH.registerIdentity r.alice).run (setupTr1 r.alice)).1 = none ∧
      ((DY.Libsignal.PQXDH.registerIdentity r.alice).run (setupTr1 r.alice)).2.val =
        setupTr1 r.alice := by
    unfold DY.Libsignal.PQXDH.registerIdentity
    rw [run_bind_fst, run_bind_snd]
    have hg : ((DY.Libsignal.PQXDH.guardTrace fun tr =>
        !DY.Libsignal.PQXDH.isRegisteredB tr r.alice).run (setupTr1 r.alice)).1 = none ∧
      ((DY.Libsignal.PQXDH.guardTrace fun tr =>
        !DY.Libsignal.PQXDH.isRegisteredB tr r.alice).run (setupTr1 r.alice)).2.val =
        setupTr1 r.alice := by
      unfold DY.Libsignal.PQXDH.guardTrace
      simp only [Traceful.run_mk, isRegisteredB_setupTr1_self, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, trivial⟩
    rw [hg.1, hg.2]
    exact ⟨rfl, rfl⟩
  rw [hb.1, hb.2]

private theorem alice_ne_bob_of_modelRun {r : ProtocolSetup} {ms : List Move}
    (hmr : ModelRun r ms) : r.alice ≠ r.bob := by
  intro hEq
  have hlen := hmr.1
  have h1 : (setupRandoms r).length = 1 := by
    unfold setupRandoms
    rw [setupTrace_eq_self r hEq, newRandoms_setupTr1]
    rfl
  rw [h1] at hlen
  cases hOpk : r.withOpk <;> rw [hOpk] at hlen <;> exact absurd hlen (by decide)

private theorem runMoves_append_fst :
    ∀ (L₁ L₂ : List Move) (tr : ExecTrace),
      (runMoves (L₁ ++ L₂) tr).1 = (runMoves L₂ (runMoves L₁ tr).1).1
  | [], L₂, tr => rfl
  | m :: L₁, L₂, tr => by
    simp only [List.cons_append, runMoves]
    exact runMoves_append_fst L₁ L₂ (m.next tr)

private theorem runTrace_take_le (r₀ : ProtocolSetup) (ms : List Move) (idx : Nat) :
    runTraceMoves r₀ (ms.take idx) ≤ runTraceMoves r₀ ms := by
  have hsplit : ms = ms.take idx ++ ms.drop idx := (List.take_append_drop idx ms).symm
  conv => rhs; rw [hsplit]
  unfold runTraceMoves
  simp only [runMoves]
  rw [runMoves_append_fst]
  exact runMoves_le (ms.drop idx) _

theorem pathFaithful_updateFreshAt_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hpf : PathFaithful interpretation r₀ S g ms τ) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms))
    (n : Nat) (m : DY.Libsignal.HwBytes) :
    PathFaithful interpretation r₀ S { g with σ := updateFreshAt g.σ ts n m } ms τ := by
  intro idx mv promote b p hmi hpp hcs hpw
  rw [hpf idx mv promote b p hmi hpp hcs hpw]
  refine exists_congr fun ek => and_congr_right fun hek => ?_
  have hek_lt : StampsLt interpretation S g ts ek :=
    stampsLt_of_mem_bobDoneBaseKeys (runTrace_take_le r₀ ms idx) htr hek
  rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m ek hek_lt]

theorem recvRepresentations_updateFreshAt_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b : DY.Libsignal.HwBytes} {t : DY.Bytes}
    (ht : t ∈ recvRepresentations interpretation r₀ S g ms b) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms))
    (n : Nat) (m : DY.Libsignal.HwBytes) :
    t ∈ recvRepresentations interpretation r₀ S { g with σ := updateFreshAt g.σ ts n m } ms b := by
  have ht_lt : StampsLt interpretation S g ts t := traceEntriesLt_knows htr ht.1
  refine ⟨ht.1, ?_, ht.2.2.1, fun msg hparse => ?_⟩
  · rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m t ht_lt]
    exact ht.2.1
  · obtain ⟨hw_lt, hm_lt, hrk_lt, hct_lt, hpq_lt⟩ := stampsLt_parseTrSignalMsg ht_lt hparse
    have hmsg := ht.2.2.2 msg hparse
    refine ⟨?_, ?_, hmsg.2.2.1, fun sm hsm => ?_⟩
    · rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.wire hw_lt]
      exact hmsg.1
    · rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.mac hm_lt]
      exact hmsg.2.1
    · have hsm' := hmsg.2.2.2 sm hsm
      refine ⟨?_, ?_, ?_, hsm'.2.2.2⟩
      · rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.ciphertext hct_lt]
        exact hsm'.1
      · rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.ratchetKey hrk_lt]
        exact hsm'.2.1
      · rw [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.pqRatchet hpq_lt]
        exact hsm'.2.2.1

theorem preKeyRepresentations_updateFreshAt_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b : DY.Libsignal.HwBytes} {x : PreKeyRep}
    (hx : x ∈ preKeyRepresentations interpretation r₀ S g ms b) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms))
    (n : Nat) (m : DY.Libsignal.HwBytes) :
    x ∈ preKeyRepresentations interpretation r₀ S { g with σ := updateFreshAt g.σ ts n m } ms b := by
  have hek_lt : StampsLt interpretation S g ts x.ek := traceEntriesLt_knows htr hx.1
  have hct_lt : StampsLt interpretation S g ts x.ct := traceEntriesLt_knows htr hx.2.1
  have hmsg_lt : StampsLt interpretation S g ts x.msg := traceEntriesLt_knows htr hx.2.2.1
  have hv_list : ∀ u ∈ [x.ek, x.ct, x.msg], StampsLt interpretation S g ts u := by
    intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
  refine ⟨hx.1, hx.2.1, hx.2.2.1,
    (preKeyRecvMatches_updateFreshAt_of_visStampsLt interpretation r₀ S g ts n m b
      [x.ek, x.ct, x.msg] hv_list).mpr hx.2.2.2.1, ?_⟩
  obtain ⟨p, hpw, msg, hparse, hw, hmac, hspqr, hct, hrk, hpq, hcnt, hver⟩ := hx.2.2.2.2
  obtain ⟨hw_lt, hm_lt, hrk_lt, hct_lt', hpq_lt⟩ := stampsLt_parseTrSignalMsg hmsg_lt hparse
  refine ⟨p, hpw, msg, hparse, ?_, ?_, hspqr, ?_, ?_, ?_, hcnt, hver⟩
  · rwa [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.wire hw_lt]
  · rwa [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.mac hm_lt]
  · rwa [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.ciphertext hct_lt']
  · rwa [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.ratchetKey hrk_lt]
  · rwa [gamma_updateFreshAt_of_stampsLt interpretation S g ts n m msg.pqRatchet hpq_lt]

theorem readFaithful_updateFreshAt_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hrf : ReadFaithful interpretation r₀ S g ms τ) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms))
    (n : Nat) (m : DY.Libsignal.HwBytes) :
    ReadFaithful interpretation r₀ S { g with σ := updateFreshAt g.σ ts n m } ms τ := by
  intro ev hev hkind
  have h := hrf ev hev hkind
  revert h
  split <;> intro h
  · exact recvRepresentations_updateFreshAt_of_traceEntriesLt h htr n m
  · intro p hp
    exact recvRepresentations_updateFreshAt_of_traceEntriesLt (h p hp) htr n m
  · exact preKeyRepresentations_updateFreshAt_of_traceEntriesLt h htr n m
  · trivial

theorem matchedPrefix_updateFreshAt_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ) {ts : Nat}
    (hts : (runTraceMoves r₀ ms).length ≤ ts)
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms))
    (n : Nat) (m : DY.Libsignal.HwBytes) :
    MatchedPrefix interpretation r₀ S who { g with σ := updateFreshAt g.σ ts n m } ms τ := by
  refine ⟨compat_updateFreshAt r₀ (alice_ne_bob_of_modelRun hmp.2.1) S g ms hts htr n m hmp.1,
    hmp.2.1, hmp.2.2.1,
    pathFaithful_updateFreshAt_of_traceEntriesLt hmp.2.2.2.1 htr n m,
    readFaithful_updateFreshAt_of_traceEntriesLt hmp.2.2.2.2.1 htr n m, ?_⟩
  have hfor := hmp.2.2.2.2.2
  rw [List.forall₂_iff_zip] at hfor ⊢
  refine ⟨hfor.1, fun {e v} hx => ?_⟩
  have hmem_v : v ∈ runVis r₀ ms := List.of_mem_zip hx |>.2
  have hvs : VisStampsLt interpretation S g ts v :=
    runMoves_visStampsLt (r₀.setupMove :: ms) DY.Trace.nil opkNetOK_nil hts htr v hmem_v
  exact (eventMatchesEntry_updateFreshAt_of_visStampsLt interpretation r₀ S g ts n m e v hvs).mpr (hfor.2 hx)

/-- Updating `g.σ` at a timestamp `ts ≥ (runTraceMoves r₀ ms).length` preserves `MatchedPrefix`. -/
theorem matchedPrefix_updateFreshAt {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ) {ts : Nat}
    (hts : (runTraceMoves r₀ ms).length ≤ ts) (n : Nat) (m : DY.Libsignal.HwBytes) :
    MatchedPrefix interpretation r₀ S who { g with σ := updateFreshAt g.σ ts n m } ms τ :=
  matchedPrefix_updateFreshAt_of_traceEntriesLt hmp hts
    (traceEntriesLt_of_reachable interpretation S g ts hmp.2.1.2.2.1.1 hts) n m

end Symbolic.Swarm.CREF.TR.FreshSigma
