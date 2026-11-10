/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Sem
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
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
# Initial Empty-Trace Model Invariants

Proves `MatchedPrefix`, `Clean`, and `PureCRel` on the empty hardware trace `[]` with empty session
records, `sent = []`, and `accepted = []`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent TRState)

private abbrev InitTRStateEntry :=
  DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState TRState)
private abbrev InitTREventEntry := DY.ProtocolEvent.ExecEntryT TREvent
private abbrev InitPQEventEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent

private def init_badPQEvent : PQXDHEvent → Bool
  | .BobDone .. => true
  | .OPKUsed .. => true
  | _ => false

private def init_TraceInv (tr : ExecTrace) : Prop :=
  (∀ i, (tr.at? i : Option InitTRStateEntry) = none) ∧
  (∀ i, (tr.at? i : Option InitTREventEntry) = none) ∧
  (∀ i (e : InitPQEventEntry), tr.at? i = some e → init_badPQEvent e.ev = false)

private theorem init_at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1} {i : Nat} {res : E2}
    (h : ((tr.append e).at? i : Option E2) = some res) :
    (tr.at? i : Option E2) = some res ∨
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some res := by
  by_cases hlt : i < tr.length
  · left
    rw [← TR.at?_append_of_lt tr e hlt]
    exact h
  · by_cases heq : i = tr.length
    · right
      rw [← TR.at?_append_eq_of_proj tr e heq _ rfl]
      exact h
    · have hlen : ¬ i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      simp [Trace.at?, hlen] at h

private theorem init_at?_none_append {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1}
    (htr : ∀ i, (tr.at? i : Option E2) = none)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none) :
    ∀ i, ((tr.append e).at? i : Option E2) = none := by
  intro i
  cases h : ((tr.append e).at? i : Option E2) with
  | none => rfl
  | some res =>
    rcases init_at?_append_cases h with h1 | h2
    · rw [htr i] at h1; cases h1
    · rw [hproj] at h2; cases h2

private theorem init_traceInv_nil : init_TraceInv Trace.nil := by
  have hge : ∀ i, ¬ i < (Trace.nil : ExecTrace).length := fun i => by
    simp only [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega
  exact ⟨fun i => by simp only [Trace.at?, hge i, ↓reduceDIte],
    fun i => by simp only [Trace.at?, hge i, ↓reduceDIte],
    fun i _ h => by simp only [Trace.at?, hge i, ↓reduceDIte] at h; cases h⟩

private theorem init_traceInv_append_nonPQ {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E} (htr : init_TraceInv tr)
    (h1 : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option InitTRStateEntry) = none)
    (h2 : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option InitTREventEntry) = none)
    (h3 : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option InitPQEventEntry) = none) :
    init_TraceInv (tr.append e) := by
  refine ⟨init_at?_none_append htr.1 h1, init_at?_none_append htr.2.1 h2, fun i ev h => ?_⟩
  rcases init_at?_append_cases h with h' | h'
  · exact htr.2.2 i ev h'
  · rw [h3] at h'; cases h'

private theorem init_traceInv_append_pqEv {tr : ExecTrace} {ev : PQXDHEvent}
    (htr : init_TraceInv tr) (hbad : init_badPQEvent ev = false) :
    init_TraceInv (tr.append (TR.EvE ev)) := by
  refine ⟨init_at?_none_append htr.1 rfl, init_at?_none_append htr.2.1 rfl, fun i e h => ?_⟩
  rcases init_at?_append_cases h with h' | h'
  · exact htr.2.2 i e h'
  · rw [TR.proj_inj_eq] at h'
    cases h'
    exact hbad

private theorem init_traceInv_setupTrace (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    init_TraceInv (setupTrace r) := by
  have h1 : init_TraceInv (TR.setupTr1 r.alice) := by
    unfold TR.setupTr1
    exact init_traceInv_append_nonPQ
      (init_traceInv_append_nonPQ
        (init_traceInv_append_nonPQ
          (init_traceInv_append_pqEv
            (init_traceInv_append_nonPQ init_traceInv_nil rfl rfl rfl) rfl)
          rfl rfl rfl)
        rfl rfl rfl)
      rfl rfl rfl
  have h2 : init_TraceInv (TR.setupTr2 r.alice r.bob) := by
    unfold TR.setupTr2
    exact init_traceInv_append_nonPQ
      (init_traceInv_append_nonPQ
        (init_traceInv_append_nonPQ
          (init_traceInv_append_pqEv
            (init_traceInv_append_nonPQ h1 rfl rfl rfl) rfl)
          rfl rfl rfl)
        rfl rfl rfl)
      rfl rfl rfl
  have h3 : init_TraceInv (TR.setupTr3 r.alice r.bob) := by
    unfold TR.setupTr3
    exact init_traceInv_append_nonPQ
      (init_traceInv_append_nonPQ
        (init_traceInv_append_nonPQ
          (init_traceInv_append_pqEv
            (init_traceInv_append_nonPQ
              (init_traceInv_append_nonPQ h2 rfl rfl rfl) rfl rfl rfl) rfl)
          rfl rfl rfl)
        rfl rfl rfl)
      rfl rfl rfl
  have h4 : init_TraceInv (TR.setupTr4 r.alice r.bob) := by
    unfold TR.setupTr4
    exact init_traceInv_append_nonPQ
      (init_traceInv_append_nonPQ
        (init_traceInv_append_nonPQ
          (init_traceInv_append_pqEv
            (init_traceInv_append_nonPQ
              (init_traceInv_append_nonPQ h3 rfl rfl rfl) rfl rfl rfl) rfl)
          rfl rfl rfl)
        rfl rfl rfl)
      rfl rfl rfl
  have h5 : init_TraceInv (TR.setupTr5 r.alice r.bob) := by
    unfold TR.setupTr5
    exact init_traceInv_append_nonPQ
      (init_traceInv_append_nonPQ
        (init_traceInv_append_pqEv
          (init_traceInv_append_nonPQ h4 rfl rfl rfl) rfl)
        rfl rfl rfl)
      rfl rfl rfl
  rw [TR.setupTrace_eq r hNe]
  cases r.withOpk
  · exact h4
  · exact h5

private theorem init_runVis_nil (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    runVis r [] = [] := by
  change (r.setupMove.vis Trace.nil) ++ [] = []
  rw [List.append_nil]
  unfold Move.vis
  change [] ++ exposures Trace.nil (setupTrace r) = []
  rw [List.nil_append, b1_setupTrace_eq r hNe]
  let isComp : PQXDHEvent → Bool := fun ev =>
    match ev with
    | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedOPK .. | .CompromisedPQSPK .. => true
    | _ => false
  let P : ExecTrace → Prop := fun tr =>
    (∀ j ev, tr.getEventAt PQXDHEvent j = some ev → isComp ev = false) ∧
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
          Option InitPQEventEntry) with
       | none => false
       | some x => isComp x.ev) = false →
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option InitTREventEntry) = none →
      P (tr.append e) := by
    intro E _ tr e h hpq htr
    refine ⟨fun j ev hj => ?_, fun j => ?_⟩
    · rcases Nat.lt_trichotomy j tr.length with hlt | rfl | hgt
      · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hj
        rw [TR.at?_append_of_lt tr e hlt] at hj
        exact h.1 j ev (by simpa only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] using hj)
      · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?,
          Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
          Nat.lt_succ_self, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2] at hj
        rcases hx : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
            Option InitPQEventEntry) with _ | ⟨ev'⟩
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
      · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [TR.at?_append_of_lt tr e hlt]
        simpa only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] using h.2 j
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
            cases ev <;> simp_all [isComp],
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

private theorem init_run_discard_snd {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, t, ht⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem init_run_bind_snd_of_none {α β : Type} {x : Traceful α} (f : α → Traceful β)
    {tr : ExecTrace} (hnone : (x.run tr).1 = none) (hro : (x.run tr).2.val = tr) :
    ((x >>= f).run tr).2.val = tr := by
  rw [Traceful.run_bind]
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at hnone hro
  cases hnone
  exact hro

private theorem init_run_bind_ro {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr : ExecTrace} (hx : (x.run tr).2.val = tr) (hf : ∀ a, ((f a).run tr).2.val = tr) :
    ((x >>= f).run tr).2.val = tr := by
  rw [Traceful.run_bind]
  rcases h : x.run tr with ⟨_ | a, t, ht⟩
  · rw [h] at hx; exact hx
  · rw [h] at hx; dsimp only at hx ⊢; rw [hx]; exact hf a

private theorem init_guard_ro (p : Prop) [Decidable p] (tr : ExecTrace) :
    ((_root_.guard p : Traceful Unit).run tr).2.val = tr := by
  unfold _root_.guard
  split <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem init_getLocalState_tr_none {tr : ExecTrace} (htr : init_TraceInv tr)
    (me : Participant) (stateIdx : Nat) :
    ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful DY.Libsignal.TripleRatchet.TRState).run tr).1 = none ∧
    ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful DY.Libsignal.TripleRatchet.TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  have h0 : ((DY.getEntry stateIdx : Traceful InitTRStateEntry).run tr).1 = none := by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
    exact htr.1 stateIdx
  have h1 : ((DY.getEntry stateIdx : Traceful InitTRStateEntry).run tr).2.val = tr := by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  rw [Traceful.run_bind, Traceful.run_bind]
  rcases hx : (DY.getEntry stateIdx : Traceful InitTRStateEntry).run tr with ⟨o, t, ht⟩
  rw [hx] at h0 h1
  cases h0
  exact ⟨rfl, h1⟩

private theorem init_getKey_pq_run {tr : ExecTrace} (me : Participant) (stateIdx : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    ((DY.Libsignal.PQXDH.getKey me stateIdx kind).run tr).2.val = tr := by
  unfold DY.Libsignal.PQXDH.getKey
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact init_run_bind_ro (init_run_bind_ro
    (init_run_bind_ro (by simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk])
      (fun _ => by simp only [Traceful.run_pure]))
    (fun _ => init_run_bind_ro (init_guard_ro _ _) (fun _ => by simp only [Traceful.run_pure])))
    (fun _ => init_run_bind_ro (init_guard_ro _ _) (fun _ => by simp only [Traceful.run_pure]))

private theorem init_compromise_step {tr : ExecTrace} (htr : init_TraceInv tr)
    (me : Participant) (stateIdx : Nat) (kind : DY.Libsignal.PQXDH.KeyKind)
    (mkEv : DY.Bytes → DY.Libsignal.PQXDH.PQXDHEvent) (hbad : ∀ sk, init_badPQEvent (mkEv sk) = false) :
    init_TraceInv
      (((DY.Libsignal.PQXDH.getKey me stateIdx kind >>= fun sk =>
          DY.ProtocolEvent.logEvent (mkEv sk) >>= fun _ =>
          DY.Network.sendMessage sk) >>= fun _ => pure ()).run tr).2.val := by
  have hro := init_getKey_pq_run (tr := tr) me stateIdx kind
  rw [init_run_discard_snd, Traceful.run_bind]
  rcases hx : (DY.Libsignal.PQXDH.getKey me stateIdx kind).run tr with ⟨_ | sk, t, ht⟩
  · rw [hx] at hro; dsimp only at hro ⊢; rw [hro]; exact htr
  · rw [hx] at hro; dsimp only at hro ⊢
    have heq :
        ((DY.ProtocolEvent.logEvent (mkEv sk) >>= fun _ =>
            DY.Network.sendMessage sk).run t).2.val =
          (t.append (TR.EvE (mkEv sk))).append (TR.NetE sk) :=
      (TR.Runs.bind (TR.Runs.logEvent t (mkEv sk)) (TR.Runs.sendMessage _ sk)).2
    rw [heq, hro]
    exact init_traceInv_append_nonPQ (init_traceInv_append_pqEv htr (hbad sk)) rfl rfl rfl

private theorem init_take_cons_ne_nil {α : Type} (x : α) (xs ys : List α) {n : Nat}
    (hn : 1 ≤ n) : (x :: xs).take n ++ ys ≠ [] := by
  cases n with
  | zero => omega
  | succ n => simp

private theorem init_traceInv_move {tr : ExecTrace} {m : Move}
    (htr : init_TraceInv tr) (hs : m.isSetup = false) (ha : m.LogsSessionCompletion tr)
    (hv : m.vis tr = []) :
    init_TraceInv (m.next tr) := by
  cases m with
  | setup a b withOpk => cases hs
  | aliceStart a b idStateIdx regIdxB h shown =>
    exfalso
    exact init_take_cons_ne_nil _ _ _ ha.1 hv
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    exfalso
    exact init_take_cons_ne_nil _ _ _ ha.1 hv
  | reject draws =>
    dsimp only [Move.next, Move.act]
    rw [Traceful.run_pure]
    exact htr
  | attackerSend msg =>
    dsimp only [Move.next, Move.act]
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
    exact init_traceInv_append_nonPQ htr rfl rfl rfl
  | brkDH =>
    dsimp only [Move.next, Move.act]
    unfold DY.Libsignal.PQXDH.breakDH
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
    exact init_traceInv_append_pqEv htr rfl
  | brkKEM =>
    dsimp only [Move.next, Move.act]
    unfold DY.Libsignal.PQXDH.breakKEM
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
    exact init_traceInv_append_pqEv htr rfl
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    have ⟨hn, hr⟩ := init_getLocalState_tr_none htr me stateIdx
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]
    unfold DY.Libsignal.TripleRatchet.messageEncrypt
    rw [init_run_bind_snd_of_none _ hn hr]
    exact htr
  | encryptAbort me stateIdx =>
    have ⟨hn, hr⟩ := init_getLocalState_tr_none htr me stateIdx
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]
    unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
    rw [init_run_bind_snd_of_none _ hn hr]
    exact htr
  | encryptFail me stateIdx coinsLen =>
    have ⟨hn, hr⟩ := init_getLocalState_tr_none htr me stateIdx
    dsimp only [Move.next, Move.act]
    rw [init_run_bind_ro (by unfold DY.Libsignal.TripleRatchet.traceLength; simp only [Traceful.run_mk]) (fun _ => by
      rw [init_run_discard_snd]
      unfold DY.Libsignal.TripleRatchet.messageEncrypt
      exact init_run_bind_snd_of_none _ hn hr)]
    exact htr
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    have ⟨hn, hr⟩ := init_getLocalState_tr_none htr me stateIdx
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    rw [init_run_bind_snd_of_none _ hn hr]
    exact htr
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    have ⟨hn, hr⟩ := init_getLocalState_tr_none htr me stateIdx
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]
    unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
    rw [init_run_bind_snd_of_none _ hn hr]
    exact htr
  | exposeKey me stateIdx k =>
    have ⟨hn, hr⟩ := init_getLocalState_tr_none htr me stateIdx
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]
    unfold DY.Libsignal.TripleRatchet.exposeKey
    rw [init_run_bind_snd_of_none _ hn hr]
    exact htr
  | exposeSpqr me stateIdx =>
    have ⟨hn, hr⟩ := init_getLocalState_tr_none htr me stateIdx
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]
    unfold DY.Libsignal.TripleRatchet.exposeSpqr
    rw [init_run_bind_snd_of_none _ hn hr]
    exact htr
  | exposeSkipped skIdx =>
    have hn : ((DY.getEntry skIdx : Traceful InitTREventEntry).run tr).1 = none := by
      simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
      exact htr.2.1 skIdx
    have hr : ((DY.getEntry skIdx : Traceful InitTREventEntry).run tr).2.val = tr := by
      simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]
    unfold DY.Libsignal.TripleRatchet.exposeSkipped
    rw [init_run_bind_snd_of_none _ hn hr]
    exact htr
  | compromiseIK p stateIdx =>
    exact init_compromise_step htr p stateIdx .identity
      (fun sk => .CompromisedIK p (DY.DiffieHellman.dhPk sk)) (fun _ => rfl)
  | compromiseSPK b stateIdx =>
    exact init_compromise_step htr b stateIdx .signedPrekey
      (fun sk => .CompromisedSPK b (DY.DiffieHellman.dhPk sk)) (fun _ => rfl)
  | compromisePQSPK b stateIdx =>
    exact init_compromise_step htr b stateIdx .pqPrekey
      (fun sk => .CompromisedPQSPK b (DY.PQKem.kemPk sk)) (fun _ => rfl)
  | compromiseOPK b stateIdx =>
    have hro := init_getKey_pq_run (tr := tr) b stateIdx .oneTimePrekey
    dsimp only [Move.next, Move.act]
    rw [init_run_discard_snd]; unfold DY.Libsignal.PQXDH.compromiseOPK; rw [Traceful.run_bind]
    rcases hx : (DY.Libsignal.PQXDH.getKey b stateIdx .oneTimePrekey).run tr with ⟨_ | sk, t, ht⟩
    · rw [hx] at hro; dsimp only at hro ⊢; rw [hro]; exact htr
    · rw [hx] at hro; dsimp only at hro ⊢; rw [hro]
      unfold DY.Libsignal.PQXDH.guardTrace
      rw [Traceful.run_bind]
      erw [DY.Traceful.run_mk]
      by_cases hg : (!DY.Libsignal.PQXDH.opkUsedB tr b (DY.DiffieHellman.dhPk sk)) = true
      · simp only [hg, ↓reduceIte]
        rw [(TR.Runs.bind (TR.Runs.logEvent tr _) (TR.Runs.sendMessage _ sk)).2]
        exact init_traceInv_append_nonPQ (init_traceInv_append_pqEv htr rfl) rfl rfl rfl
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]; exact htr

private theorem init_traceInv_runMoves :
    ∀ (ms : List Move) (tr : ExecTrace),
      init_TraceInv tr →
      (∀ m ∈ ms, m.isSetup = false) →
      MovesAnchored ms tr →
      (runMoves ms tr).2 = [] →
      init_TraceInv (runMoves ms tr).1
  | [], _, htr, _, _, _ => htr
  | m :: ms, tr, htr, hns, ⟨ha, hanc⟩, hvis => by
    rw [runMoves_cons_snd, List.append_eq_nil_iff] at hvis
    rw [runMoves_cons_fst]
    exact init_traceInv_runMoves ms (m.next tr)
      (init_traceInv_move htr (hns m (List.mem_cons_self ..)) ha hvis.1)
      (fun m' hm' => hns m' (List.mem_cons_of_mem _ hm'))
      hanc hvis.2

private theorem init_traceInv_of_matchedPrefix_nil
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move}
    (hwf : ProtocolSetupWF r) (hmp : MatchedPrefix interpretation r S who g ms []) :
    init_TraceInv (runTraceMoves r ms) := by
  have hns : ∀ m ∈ ms, m.isSetup = false := hmp.2.1.2.1
  have hanc : MovesAnchored ms (setupTrace r) := hmp.2.1.2.2.1.2.1
  have hfor := hmp.2.2.2.2.2
  have hvis : runVis r ms = [] := List.forall₂_nil_left_iff.mp hfor
  have hvis' : r.setupMove.vis Trace.nil ++ (runMoves ms (setupTrace r)).2 = [] := hvis
  rw [List.append_eq_nil_iff] at hvis'
  exact init_traceInv_runMoves ms (setupTrace r) (init_traceInv_setupTrace r hwf.1) hns hanc hvis'.2

private theorem init_trNsBound_of_traceInv {r : ProtocolSetup} {ms : List Move}
    (htr : init_TraceInv (runTraceMoves r ms)) :
    TR.TRNsBound r ms [] := by
  intro p stateIdx st hget
  rw [(init_getLocalState_tr_none htr p stateIdx).1] at hget
  cases hget

private theorem init_bobDoneBaseKeys_eq_nil_of_traceInv {tr : ExecTrace} (htr : init_TraceInv tr) :
    bobDoneBaseKeys tr = [] := by
  unfold bobDoneBaseKeys
  rw [List.filterMap_eq_nil_iff]
  intro i _
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  cases h : (tr.at? i : Option InitPQEventEntry) with
  | none => rfl
  | some e =>
    have hbad := htr.2.2 i e h
    rcases e with ⟨ev⟩
    cases ev <;> simp [init_badPQEvent] at hbad ⊢

private theorem init_availableStates_nil {r : ProtocolSetup} {tr : ExecTrace} (htr : init_TraceInv tr)
    {st : DY.Libsignal.TripleRatchet.TRState}
    (hst : st ∈ DY.Libsignal.Composed.Refinement.availableStates r tr) : False := by
  unfold DY.Libsignal.Composed.Refinement.availableStates
    DY.Libsignal.Composed.Refinement.storedStates
    DY.ExecTrace.getLocalStateAt at hst
  obtain ⟨ls, hls, -⟩ := List.mem_map.mp hst
  obtain ⟨i, -, hget⟩ := List.mem_filterMap.mp hls
  rw [htr.1 i] at hget
  simp at hget

private theorem init_roleSnapshots_of_traceInv {r : ProtocolSetup} {tr : ExecTrace}
    (htr : init_TraceInv tr) : RoleSnapshots r tr := by
  intro p st i hat
  rw [htr.1 i] at hat
  cases hat

theorem init_matchedPrefix_nil {interpretation : ExternInterpretation} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} (hS : SemReady interpretation r S) (who : List Participant) :
    MatchedPrefix interpretation r S who ⟨r.fresh, fun _ => []⟩ [] [] := by
  refine ⟨hS ⟨r.fresh, fun _ => []⟩ (fun _ _ => rfl), TR.modelRun_nil r hwf,
    by simp [RoleFaithful], by simp [PathFaithful], by simp [ReadFaithful], ?_⟩
  rw [init_runVis_nil r hwf.1]
  exact List.Forall₂.nil

theorem init_clean_nil {interpretation : ExternInterpretation} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} (hS : SemReady interpretation r S)
    (who : List Participant) (ok : Nat → Bool) :
    Clean interpretation r S who ok ⟨r.fresh, fun _ => []⟩ [] [] := by
  refine ⟨⟨init_matchedPrefix_nil hwf hS who, fun _ _ hi => nomatch hi⟩, ?_⟩
  rintro ⟨_, _, _, _, _, h, -⟩
  simp at h

private theorem init_cHist_of_traceInv {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} (htr : init_TraceInv (runTraceMoves r ms)) :
    CHist interpretation r S g ms := by
  refine ⟨fun st hst => (init_availableStates_nil htr hst).elim,
    fun st hst => (init_availableStates_nil htr hst).elim, ?_,
    fun st hst => (init_availableStates_nil htr hst).elim⟩
  intro _ _ _ _ _ src _ _ _ _ _ hstored
  have h0 := htr.1 src
  rw [hstored] at h0
  cases h0

/-- `PureCRel` holds at the initial empty state (`records = fun _ => none`, `sent = []`,
`accepted = []`, `acc = []`). -/
theorem pureCRel_nil {interp : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool) :
    PureCRel interp r S who ok (fun _ => none) [] [] [] where
  oooAll := fun _ _ h => nomatch h
  sendsFit := TR.sendsFit_nil
  bka := fun _ h => nomatch h
  bkn := pureBobKyberNone_empty r
  clean := fun g ms hc => by
    have hinv := init_traceInv_of_matchedPrefix_nil hwf hc.matched
    refine ⟨⟨(fun _ _ h => nomatch h),
      ⟨rfl, init_trNsBound_of_traceInv hinv, (fun _ h => nomatch h), fun ek hek => ?_⟩,
      init_cHist_of_traceInv hinv, init_roleSnapshots_of_traceInv hinv⟩,
      bobRecordBaseKeyInSession_of_none rfl⟩
    rw [init_bobDoneBaseKeys_eq_nil_of_traceInv hinv] at hek
    cases hek

end Symbolic.Swarm.CREF.CliPure
