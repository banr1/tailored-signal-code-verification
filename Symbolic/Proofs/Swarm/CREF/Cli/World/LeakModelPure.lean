/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RoleSnapshots
public import Symbolic.Proofs.Swarm.CREF.TR.PQLeak
public import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import DY.Trace.Basic
import DY.Trace.Monad
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Exposure-Only Trace Lemmas for Leak Moves

Classifies trace updates of `LeakKind` moves, splits `MatchedPrefix` runs at `.leak` block
boundaries, and proves that `TR.AppendsOnlyExposure` extensions preserve stored states,
`RoleSnapshots`, and `bobDoneBaseKeys`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent TRState)

abbrev LeakStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev LeakTREntry := DY.ProtocolEvent.ExecEntryT TREvent

/-! ## Trace-shape classification for `LeakKind` moves -/

private theorem compromise_next_cases {m : Move} {p : Participant} {i : Nat}
    {kind : DY.Libsignal.PQXDH.KeyKind} {mk : DY.Bytes → PQXDHEvent} (tr : ExecTrace)
    (hm : TR.compromiseShape m = some (p, i, kind, mk)) :
    m.next tr = tr ∨
      ∃ sk, m.next tr = (tr.append (TR.EvE (mk sk))).append (TR.NetE sk) := by
  cases m <;> simp only [TR.compromiseShape, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hm <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm <;>
    (unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit])
  · unfold DY.Libsignal.PQXDH.compromiseIK
    rw [TR.run_bind_snd, XplSteps.xfix_getKey _ _ .identity tr]
    rcases ((DY.Libsignal.PQXDH.getKey _ _ .identity).run tr).1 with _ | sk
    · exact Or.inl rfl
    · refine Or.inr ⟨sk, ?_⟩
      simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  · unfold DY.Libsignal.PQXDH.compromiseSPK
    rw [TR.run_bind_snd, XplSteps.xfix_getKey _ _ .signedPrekey tr]
    rcases ((DY.Libsignal.PQXDH.getKey _ _ .signedPrekey).run tr).1 with _ | sk
    · exact Or.inl rfl
    · refine Or.inr ⟨sk, ?_⟩
      simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  · unfold DY.Libsignal.PQXDH.compromisePQSPK
    rw [TR.run_bind_snd, XplSteps.xfix_getKey _ _ .pqPrekey tr]
    rcases ((DY.Libsignal.PQXDH.getKey _ _ .pqPrekey).run tr).1 with _ | sk
    · exact Or.inl rfl
    · refine Or.inr ⟨sk, ?_⟩
      simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  · unfold DY.Libsignal.PQXDH.compromiseOPK
    rw [TR.run_bind_snd, XplSteps.xfix_getKey _ _ .oneTimePrekey tr]
    rcases ((DY.Libsignal.PQXDH.getKey _ _ .oneTimePrekey).run tr).1 with _ | sk
    · exact Or.inl rfl
    · dsimp only
      rw [TR.run_bind_snd]
      unfold DY.Libsignal.PQXDH.guardTrace
      rw [Traceful.run_mk]
      dsimp only
      split
      · refine Or.inr ⟨sk, ?_⟩
        simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
          Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      · exact Or.inl rfl

/-- Every `LeakKind` move either leaves `tr` unchanged (with `m.vis tr = []`), appends one TR
exposure pair `(ev, msg)` (with `m.vis tr = [v]`), or appends one PQXDH compromise pair `(ev, msg)`
(with `m.vis tr = [v]`). -/
theorem leakKind_next_cases {m : Move} (tr : ExecTrace) (hk : LeakKind m) :
    (m.next tr = tr ∧ m.vis tr = []) ∨
    (∃ ev msg, TR.IsAnyExposureEv ev ∧
      m.next tr = (tr.append (⟨ev⟩ : LeakTREntry)).append (⟨msg⟩ : Network.ExecEntryT) ∧
      m.vis tr = [⟨.leak, [msg], .leakRecord, some tr.length⟩]) ∨
    (∃ ev msg pq, TR.pqLeakKind ev = some pq ∧
      m.next tr = (tr.append (TR.EvE ev)).append (TR.NetE msg) ∧
      m.vis tr = [⟨.leak, [msg], .leakPq pq, some tr.length⟩]) := by
  cases m <;> try exact False.elim hk
  case compromiseIK p i =>
    rcases compromise_next_cases tr (m := .compromiseIK p i) rfl with hnext | ⟨sk, hnext⟩
    · exact Or.inl ⟨hnext, by unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
    · refine Or.inr (Or.inr ⟨_, sk, false, rfl, hnext, ?_⟩)
      unfold Move.vis; rw [List.nil_append, hnext]
      exact TR.exposures_append_pq_pair tr _ sk false rfl
  case compromiseSPK b i =>
    rcases compromise_next_cases tr (m := .compromiseSPK b i) rfl with hnext | ⟨sk, hnext⟩
    · exact Or.inl ⟨hnext, by unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
    · refine Or.inr (Or.inr ⟨_, sk, false, rfl, hnext, ?_⟩)
      unfold Move.vis; rw [List.nil_append, hnext]
      exact TR.exposures_append_pq_pair tr _ sk false rfl
  case compromisePQSPK b i =>
    rcases compromise_next_cases tr (m := .compromisePQSPK b i) rfl with hnext | ⟨sk, hnext⟩
    · exact Or.inl ⟨hnext, by unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
    · refine Or.inr (Or.inr ⟨_, sk, true, rfl, hnext, ?_⟩)
      unfold Move.vis; rw [List.nil_append, hnext]
      exact TR.exposures_append_pq_pair tr _ sk true rfl
  case compromiseOPK b i =>
    rcases compromise_next_cases tr (m := .compromiseOPK b i) rfl with hnext | ⟨sk, hnext⟩
    · exact Or.inl ⟨hnext, by unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
    · refine Or.inr (Or.inr ⟨_, sk, false, rfl, hnext, ?_⟩)
      unfold Move.vis; rw [List.nil_append, hnext]
      exact TR.exposures_append_pq_pair tr _ sk false rfl
  case exposeKey p stateIdx k =>
    rcases hget :
        ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 with _ | st
    · have hnext : (Move.exposeKey p stateIdx k).next tr = tr := by
        rw [TR.exposeKey_next_eq]; unfold TripleRatchet.exposeKey
        rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
      exact Or.inl ⟨hnext, by unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
    · cases k with
      | rk =>
        refine Or.inr (Or.inl ⟨.ExposedRK (st.sessionInfo p) st.rk st.rIdx, st.rk, trivial, ?_,
          TR.visOf_exposeKey_rk hget⟩)
        rw [TR.exposeKey_next_eq]; unfold TripleRatchet.exposeKey
        rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
        simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
          Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      | dhs =>
        refine Or.inr (Or.inl ⟨.ExposedDHs (st.sessionInfo p) st.dhs st.rIdx, st.dhs, trivial, ?_,
          TR.visOf_exposeKey_dhs hget⟩)
        rw [TR.exposeKey_next_eq]; unfold TripleRatchet.exposeKey
        rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
        simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
          Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      | cks =>
        refine Or.inr (Or.inl ⟨.ExposedCKs (st.sessionInfo p) st.cks st.ns st.rIdx, st.cks, trivial, ?_,
          TR.visOf_exposeKey_cks hget⟩)
        rw [TR.exposeKey_next_eq]; unfold TripleRatchet.exposeKey
        rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
        simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
          Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      | ckr pk =>
        rcases hf : TripleRatchet.findRecvChain st.recv pk with _ | c
        · have hnext : (Move.exposeKey p stateIdx (.ckr pk)).next tr = tr := by
            rw [TR.exposeKey_next_eq]; unfold TripleRatchet.exposeKey
            rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
            simp [hf]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
          exact Or.inl ⟨hnext, by
            unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
        · refine Or.inr (Or.inl ⟨.ExposedCKr (st.sessionInfo p) c.chainKey c.index c.rIdx, c.chainKey,
            trivial, ?_, TR.visOf_exposeKey_ckr hget hf⟩)
          rw [TR.exposeKey_next_eq]; unfold TripleRatchet.exposeKey
          rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
          simp [hf, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
            Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  case exposeSpqr p stateIdx =>
    rcases hget :
        ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 with _ | st
    · have hnext : (Move.exposeSpqr p stateIdx).next tr = tr := by
        rw [TR.exposeSpqr_next_eq]; unfold TripleRatchet.exposeSpqr
        rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
      exact Or.inl ⟨hnext, by unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
    · refine Or.inr (Or.inl ⟨.ExposedSpqr (st.sessionInfo p) st.spqr st.rIdx, st.spqr, trivial, ?_,
        TR.visOf_exposeSpqr hget⟩)
      rw [TR.exposeSpqr_next_eq]; unfold TripleRatchet.exposeSpqr
      rw [TR.run_bind_snd, hget, TR.getLocalState_snd]
      simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  case exposeSkipped evH =>
    rcases TR.exposeSkipped_trace evH tr with heq | ⟨s, seed, n, r, heq⟩
    · have hnext : (Move.exposeSkipped evH).next tr = tr :=
        (TR.exposeSkipped_next_eq evH tr).trans heq
      exact Or.inl ⟨hnext, by unfold Move.vis; rw [List.nil_append, hnext, XplSteps.xpl_exposures_self]⟩
    · have hnext : (Move.exposeSkipped evH).next tr =
          (tr.append (⟨.ExposedMK s seed n r⟩ : LeakTREntry)).append (⟨seed⟩ : Network.ExecEntryT) :=
        (TR.exposeSkipped_next_eq evH tr).trans heq
      refine Or.inr (Or.inl ⟨.ExposedMK s seed n r, seed, trivial, hnext, ?_⟩)
      unfold Move.vis; rw [List.nil_append, hnext]
      exact TR.exposures_append_tr_pair tr _ _ trivial

/-! ## Leak-block explanation splitting -/

private theorem setupMove_vis_nil (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    r.setupMove.vis Trace.nil = [] := by
  unfold Move.vis
  change [] ++ exposures Trace.nil (setupTrace r) = []
  rw [List.nil_append, b1_setupTrace_eq r hne]
  let P : ExecTrace → Prop := fun tr =>
    (∀ j ev, tr.getEventAt PQXDHEvent j = some ev → TR.pqLeakKind ev = none) ∧
    (∀ j, tr.getEventAt TREvent j = none)
  have hnil : P Trace.nil := by
    refine ⟨fun j ev h => ?_, fun j => ?_⟩
    · have hge : ¬ j < (Trace.nil : ExecTrace).length := by
        simp only [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?, hge, ↓reduceDIte] at h
      cases h
    · have hge : ¬ j < (Trace.nil : ExecTrace).length := by
        simp only [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?, hge, ↓reduceDIte]
  have hstep : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (e : E),
      P tr →
      (match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with
       | none => none
       | some x => TR.pqLeakKind x.ev) = none →
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option LeakTREntry) = none →
      P (tr.append e) := by
    intro E _ tr e h hpq htr
    refine ⟨fun j ev hj => ?_, fun j => ?_⟩
    · rcases Nat.lt_trichotomy j tr.length with hlt | rfl | hgt
      · rw [XplSteps.xgetEventAt_le_eq (Trace.append_le tr e) hlt] at hj
        exact h.1 j ev hj
      · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?,
          Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
          Nat.lt_succ_self, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2] at hj
        rcases hx : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
            Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with _ | ⟨ev'⟩
        · rw [hx] at hj; cases hj
        · rw [hx] at hj hpq
          injection hj with hj'
          subst hj'
          exact hpq
      · have hge : ¬ j < (tr.append e).length := by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
          omega
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?, hge, ↓reduceDIte] at hj
        cases hj
    · rcases Nat.lt_trichotomy j tr.length with hlt | rfl | hgt
      · rw [XplSteps.xgetEventAt_le_eq (Trace.append_le tr e) hlt]
        exact h.2 j
      · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?,
          Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
          Nat.lt_succ_self, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, htr]
      · have hge : ¬ j < (tr.append e).length := by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
          omega
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?, hge, ↓reduceDIte]
  have hexp : ∀ {tr' : ExecTrace}, P tr' → exposures Trace.nil tr' = [] := by
    intro tr' h
    unfold exposures
    rw [List.filterMap_eq_nil_iff.mpr fun j _ => by
          unfold pqExposureAt
          rcases hev : tr'.getEventAt PQXDHEvent j with _ | ev
          · rfl
          · have hk := h.1 j ev hev
            cases ev <;> simp_all [TR.pqLeakKind],
        List.filterMap_eq_nil_iff.mpr fun j _ => by
          simp only [trExposureAt, h.2 j],
        List.nil_append]
  have h1 : P (b1_setupTr1 r.alice) := by
    unfold b1_setupTr1
    exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ hnil rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl
  have h2 : P (b1_setupTr2 r.alice r.bob) := by
    unfold b1_setupTr2
    exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ h1 rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl
  have h3 : P (b1_setupTr3 r.alice r.bob) := by
    unfold b1_setupTr3
    exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ (hstep _ h2 rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl
  have h4 : P (b1_setupTr4 r.alice r.bob) := by
    unfold b1_setupTr4
    exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ (hstep _ h3 rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl
  have h5 : P (b1_setupTr5 r.alice r.bob) := by
    unfold b1_setupTr5
    exact hstep _ (hstep _ (hstep _ (hstep _ h4 rfl rfl) rfl rfl) rfl rfl) rfl rfl
  cases r.withOpk
  · exact hexp h4
  · exact hexp h5

private theorem leak_runVis_nil (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    runVis r [] = [] := by
  change (r.setupMove.vis Trace.nil) ++ [] = []
  rw [setupMove_vis_nil r hne, List.append_nil]

private theorem xpl_ownVis_not_leak (m : Move) (tr : ExecTrace) {v : VisEntry}
    (hv : v ∈ xpl_ownVis m tr) : v.kind ≠ .leak := by
  intro hk
  cases m <;> dsimp only [xpl_ownVis] at hv
  case aliceStart =>
    rcases xpl_aliceVis_kind (List.mem_of_mem_take hv) with h | h <;> rw [hk] at h <;> cases h
  case bobStart =>
    rcases xpl_bobVis_kind (List.mem_of_mem_take hv) with h | h | h <;> rw [hk] at h <;> cases h
  case encrypt => rcases xpl_encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
  case encryptAbort => rcases xpl_encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
  case encryptFail => rcases xpl_encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
  case decrypt => rcases xpl_decVis_kind hv with h | h | h <;> rw [hk] at h <;> cases h
  case decryptSkipped => rcases xpl_decVis_kind hv with h | h | h <;> rw [hk] at h <;> cases h
  case reject =>
    simp only [List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨_, _, rfl⟩ <;> cases hk
  all_goals simp at hv

private theorem xpl_not_leakKind_entry {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (hk : ¬ LeakKind m) {v : VisEntry} (hv : v ∈ m.vis tr) : v.kind ≠ .leak := by
  rw [xpl_vis_eq, exposures_nil_of_not_leakKind hs hk, List.append_nil] at hv
  exact xpl_ownVis_not_leak m tr hv

private theorem noCutMove_leak {m : Move} (hs : m.isSetup = false) (tr : ExecTrace) :
    b5_NoCutMove (fun _ b => b.kind = .leak) (m.vis tr) := by
  intro k a b hk _ hb hB
  by_cases hlk : LeakKind m
  · have hmem := b5_mem_tail_of_getElem? hk hb
    rcases leakKind_next_cases tr hlk with ⟨_, hvis⟩ | ⟨_, _, _, _, hvis⟩ | ⟨_, _, _, _, _, hvis⟩ <;>
      (rw [hvis] at hmem; cases hmem)
  · exact xpl_not_leakKind_entry hs hlk (List.mem_of_getElem? hb) hB

/-- Any matched run explaining `acc ++ blk` where `blk` starts with a `.leak` event (or is empty)
splits at a move boundary into `ms₀` (explaining `acc`) and `δ` (explaining `blk`). -/
theorem matchedPrefix_split_all_leak {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {acc blk : List MachineEvent}
    (hne : r.alice ≠ r.bob)
    (h : MatchedPrefix interpretation r S who g ms (acc ++ blk))
    (hblk : ∀ e ∈ blk.head?, eventKind e = .leak)
    (hreach : ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability :=
      matchedPrefix_prefix_reachable h) :
    ∃ ms₀ δ, ms = ms₀ ++ δ ∧ MatchedPrefix interpretation r S who g ms₀ acc ∧
      List.Forall₂ (EventMatchesEntry interpretation r S g) blk
        (runMoves δ (runTraceMoves r ms₀)).2 := by
  refine matchedPrefix_split_of_noCut (fun _ b => b.kind = .leak) h
    ⟨?_, b5_noCutFrom_of_mem _ ms (fun m hm tr =>
      noCutMove_leak (h.2.1.2.1 m hm) tr) _⟩
    ?_ (fun _ => leak_runVis_nil r hne) hreach
  · rw [setupMove_vis_nil r hne]
    intro _ _ _ _ ha; cases ha
  · intro a b _ _ hb
    obtain ⟨e, he, hR⟩ := b5_forall₂_getElem? h.2.2.2.2.2 hb
    rw [b5_getElem?_append_length] at he
    exact hR.1.symm.trans (hblk e (Option.mem_def.2 he))

/-! ## Exposure-only trace effects -/

private theorem appendsOnlyExposure_of_noSessionEffect {tr : ExecTrace} {m : Move}
    (h : NoSessionEffect tr m) : TR.AppendsOnlyExposure tr (m.next tr) := by
  refine ⟨(m.act.run tr).2.property, fun i hi hge => ?_⟩
  have hmem : i ∈ newIndices tr (m.next tr) := by
    unfold newIndices
    exact List.mem_range'.mpr ⟨i - tr.length, by omega, by omega⟩
  obtain ⟨hst, _, htr, _⟩ := h i hmem
  simp only [Trace.at?, hi, ↓reduceDIte] at hst htr
  exact ⟨hst, fun ev hev => by rw [htr] at hev; cases hev⟩

private theorem bobDoneBaseKeys_of_noSessionEffect {tr : ExecTrace} {m : Move}
    (h : NoSessionEffect tr m) : bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr := by
  have hle : tr ≤ m.next tr := (m.act.run tr).2.property
  exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.bobDoneBaseKeys_eq_of_nonSessionPQExt hle fun i h1 h2 =>
    (h i (by simp only [newIndices, List.mem_range'_1]; omega)).2.1

private theorem appendsOnlyExposure_of_leakKind {tr : ExecTrace} {m : Move}
    (hk : LeakKind m) : TR.AppendsOnlyExposure tr (m.next tr) := by
  rcases leakKind_next_cases tr hk with ⟨hnext, _⟩ | ⟨ev, msg, hev, hnext, _⟩ |
      ⟨ev, msg, _, _, hnext, _⟩
  · rw [hnext]; exact TR.AppendsOnlyExposure.refl tr
  · rw [hnext]; exact TR.AppendsOnlyExposure.pair tr ev msg hev
  · rw [hnext]; exact TR.appendsOnlyExposure_pq_pair tr ev msg

private theorem bobDoneBaseKeys_append_nonBobDone {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hno : ∀ b a ikB ikA spk pqpk opk ek ct keys,
      (tr.append e).getEventAt PQXDHEvent tr.length ≠
        some (.BobDone b a ikB ikA spk pqpk opk ek ct keys)) :
    bobDoneBaseKeys (tr.append e) = bobDoneBaseKeys tr := by
  unfold bobDoneBaseKeys
  have hlen : (tr.append e).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen, List.range_succ, List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rcases hev : (tr.append e).getEventAt PQXDHEvent tr.length with _ | ev
  · rw [List.append_nil]
    refine List.filterMap_congr fun i hi => ?_
    rw [XplSteps.xgetEventAt_le_eq (Trace.append_le tr e) (List.mem_range.1 hi)]
  · cases ev with
    | BobDone b a ikB ikA spk pqpk opk ek ct keys =>
      exact absurd hev (hno b a ikB ikA spk pqpk opk ek ct keys)
    | _ =>
      rw [List.append_nil]
      refine List.filterMap_congr fun i hi => ?_
      rw [XplSteps.xgetEventAt_le_eq (Trace.append_le tr e) (List.mem_range.1 hi)]

private theorem bobDoneBaseKeys_of_leakKind {tr : ExecTrace} {m : Move}
    (hk : LeakKind m) : bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr := by
  rcases leakKind_next_cases tr hk with ⟨hnext, _⟩ | ⟨ev, msg, _, hnext, _⟩ |
      ⟨ev, msg, pq, hpq, hnext, _⟩
  · rw [hnext]
  · rw [hnext,
      bobDoneBaseKeys_append_nonBobDone _ _ (fun _ _ _ _ _ _ _ _ _ _ h => by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
        rw [TR.at?_append_eq_of_proj _ _ rfl none rfl] at h; cases h),
      bobDoneBaseKeys_append_nonBobDone _ _ (fun _ _ _ _ _ _ _ _ _ _ h => by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
        rw [TR.at?_append_eq_of_proj _ _ rfl none rfl] at h; cases h)]
  · rw [hnext,
      bobDoneBaseKeys_append_nonBobDone _ _ (fun _ _ _ _ _ _ _ _ _ _ h => by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
        rw [TR.at?_append_eq_of_proj _ _ rfl none rfl] at h; cases h),
      bobDoneBaseKeys_append_nonBobDone _ _ (fun _ _ _ _ _ _ _ _ _ _ h => by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
        rw [TR.at?_append_self] at h
        simp only [Option.some.injEq] at h
        subst h; cases hpq)]

theorem leak_moves_effect {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ (δ : List Move) (tr : ExecTrace) (blk : List MachineEvent),
      MovesFrom (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr) tr δ →
      List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves δ tr).2 →
      (∀ e ∈ blk, eventKind e = .leak) →
      TR.AppendsOnlyExposure tr (runMoves δ tr).1 ∧
        bobDoneBaseKeys (runMoves δ tr).1 = bobDoneBaseKeys tr
  | [], tr, _, _, _, _ => ⟨TR.AppendsOnlyExposure.refl tr, rfl⟩
  | m :: δ, tr, blk, ⟨⟨hs, ha⟩, hδ⟩, hm, hleak => by
    rw [runMoves_cons_snd] at hm
    have hlen : (m.vis tr).length ≤ blk.length := by
      rw [xpl_forall₂_length hm, List.length_append]; omega
    have hsplit : blk = blk.take (m.vis tr).length ++ blk.drop (m.vis tr).length :=
      (List.take_append_drop _ _).symm
    rw [hsplit] at hm
    obtain ⟨hm₁, hm₂⟩ := xpl_forall₂_append_split (by simp; omega) hm
    obtain ⟨hexp₂, hbd₂⟩ := leak_moves_effect δ (m.next tr) _ hδ hm₂
      (fun e he => hleak e (List.mem_of_mem_drop he))
    have hm_eff : NoSessionEffect tr m ∨ LeakKind m := by
      by_cases hv0 : m.vis tr = []
      · exact Or.inl (noSessionEffect_of_vis_nil hs ha hv0)
      · refine Or.inr ?_
        by_contra hk
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hv0
        obtain ⟨e, he, hev⟩ := xpl_forall₂_mem_right hm₁ v hv
        exact xpl_not_leakKind_entry hs hk hv
          ((xpl_kind_of_matches hev).trans (hleak e (List.mem_of_mem_take he)))
    have hexp₁ : TR.AppendsOnlyExposure tr (m.next tr) :=
      hm_eff.elim appendsOnlyExposure_of_noSessionEffect appendsOnlyExposure_of_leakKind
    have hbd₁ : bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr :=
      hm_eff.elim bobDoneBaseKeys_of_noSessionEffect bobDoneBaseKeys_of_leakKind
    rw [runMoves_cons_fst]
    exact ⟨TR.AppendsOnlyExposure.trans hexp₁ hexp₂, hbd₂.trans hbd₁⟩

theorem at?_stEntry_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : TR.AppendsOnlyExposure t t') (i : Nat) :
    (t'.at? i : Option LeakStEntry) = (t.at? i : Option LeakStEntry) := by
  by_cases hi : i < t.length
  · have hi' : i < t'.length := Nat.lt_of_lt_of_le hi (Trace.length_le t t' h.1)
    simp only [Trace.at?, hi, hi', ↓reduceDIte, Trace.at_le t t' i hi h.1]
  · by_cases hi' : i < t'.length
    · simp only [Trace.at?, hi, hi', ↓reduceDIte, (h.2 i hi' (Nat.le_of_not_lt hi)).1]
    · simp only [Trace.at?, hi, hi', ↓reduceDIte]

theorem appendsOnlyExposure_of_leakBlock {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost}
    {ms₀ δ : List Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hleak : ∀ e ∈ blk, eventKind e = .leak) :
    TR.AppendsOnlyExposure (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ δ)) := by
  have hs := hB.run.2.1
  have hanc := hB.run.2.2.1.2.1
  have hanc' := xpl_movesAnchored_append_right ms₀ δ (setupTrace r) hanc
  rw [← xpl_runTrace_eq] at hanc'
  obtain ⟨hexp, _⟩ := leak_moves_effect δ (runTraceMoves r ms₀) blk
    (xpl_movesFrom_of δ _ (fun m hm => hs m (List.mem_append_right _ hm)) hanc')
    hB.matched hleak
  rwa [← TR.runTrace_append] at hexp

theorem roleSnapshots_of_appendsOnlyExposure {r : ProtocolSetup} {t t' : ExecTrace}
    (hexp : TR.AppendsOnlyExposure t t') (h : RoleSnapshots r t) : RoleSnapshots r t' := by
  intro p st i hst
  exact h p st i ((at?_stEntry_of_appendsOnlyExposure hexp i).symm.trans hst)

theorem getMessageSentAt_of_le {t t' : ExecTrace} (hle : t ≤ t') {i : Nat} {x : DY.Bytes}
    (hi : t.getMessageSentAt i = some x) : t'.getMessageSentAt i = some x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hi ⊢
  rcases hat : (t.at? i : Option Network.ExecEntryT) with _ | e
  · rw [hat] at hi; cases hi
  · rw [XplSteps.xat?_le_some hle hat, ← hat]; exact hi

theorem availableStates_of_appendsOnlyExposure {r : ProtocolSetup} {t t' : ExecTrace}
    (h : TR.AppendsOnlyExposure t t') {st : TRState}
    (hst : st ∈ DY.Libsignal.Composed.Refinement.availableStates r t') :
    st ∈ DY.Libsignal.Composed.Refinement.availableStates r t := by
  unfold DY.Libsignal.Composed.Refinement.availableStates
    DY.Libsignal.Composed.Refinement.storedStates
    DY.Libsignal.Composed.Refinement.newIndices
    DY.ExecTrace.getLocalStateAt at hst ⊢
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  obtain ⟨i, hi, hget⟩ := List.mem_filterMap.mp hls
  rw [List.mem_range'_1] at hi
  rw [at?_stEntry_of_appendsOnlyExposure h i] at hget
  have hlt : i < t.length := by
    by_contra hge
    rw [(XplSteps.xnone_of_ge (by omega : t.length ≤ i)).1] at hget
    simp at hget
  exact List.mem_map.mpr ⟨ls, List.mem_filterMap.mpr
    ⟨i, List.mem_range'_1.mpr ⟨hi.1, by omega⟩, hget⟩, rfl⟩

theorem skippedKeyStored_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : TR.AppendsOnlyExposure t t') {s : DY.Libsignal.TripleRatchet.SessionInfo}
    {pk : DY.Bytes} {n : UInt32} {seed : DY.Bytes} {rIdx src i : Nat}
    (hlog : t'.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i) :
    t.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog ⊢
  by_cases hi : i < t.length
  · have hi' : i < t'.length := Nat.lt_of_lt_of_le hi (Trace.length_le t t' h.1)
    simp only [Trace.at?, hi, hi', ↓reduceDIte, Trace.at_le t t' i hi h.1] at hlog ⊢
    exact hlog
  · by_cases hi' : i < t'.length
    · simp only [Trace.at?, hi', ↓reduceDIte] at hlog
      exact False.elim ((h.2 i hi' (Nat.le_of_not_lt hi)).2 _ hlog)
    · rw [(XplSteps.xnone_of_ge (by omega : t'.length ≤ i)).2.2.1] at hlog; cases hlog

end Symbolic.Swarm.CREF.CliPure
