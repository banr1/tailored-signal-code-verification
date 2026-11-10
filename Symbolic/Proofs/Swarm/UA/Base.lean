/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs

/-!
# CLI Event Schedule, Flattening, and Prefix-Restriction Lemmas

Schedule alignment (`callsOf`, `SchedFits`), event flattening (`flatEvents`), rejected-run
extensions (`explains_snoc_rejected`), and prefix-restriction lemmas for `ExplainsClassical` and
`ReadCollisionCliClassical`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.Base

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs (runOk flatEntry flatExit failedSend flatEvent flatEvents
  callsOf SchedFits)

/-! ## Calls and Schedules -/

theorem callsOf_append : ∀ (a b : List CliEvent), callsOf (a ++ b) = callsOf a ++ callsOf b
  | [], _ => rfl
  | .run ev :: a, b => by
    by_cases h : failedSend ev = true <;> simp [callsOf, h, callsOf_append a b]
  | .env _ :: a, b => by simp only [List.cons_append, callsOf, callsOf_append a b]

theorem callsOf_run_call (c : CliCall) (code : Nat) (out : HwBytes)
    (h : failedSend (runEventOf c (some (code, out))) = false) :
    callsOf [.run (runEventOf c (some (code, out)))] = [(c.party, decide (code = 0))] := by
  simp only [callsOf, h, Bool.false_eq_true, ↓reduceIte]
  cases code <;> simp [runOk, runEventOf]

theorem callsOf_leaks {r : ProtocolSetup} {t : CliTurn} :
    ∀ {leaks : List CliEvent}, LeaksFrom r t leaks → callsOf leaks = []
  | [], _ => rfl
  | e :: es, h => by
    obtain ⟨p, k, _, rfl⟩ := h e (by simp)
    simp only [callsOf]
    exact callsOf_leaks fun e he => h e (by simp [he])

theorem schedFits_of_append {a b : List (Participant × Bool)} {who : List Participant}
    {ok : Nat → Bool} (h : SchedFits (a ++ b) who ok) : SchedFits a who ok := by
  refine ⟨(List.prefix_append (a.map Prod.fst) (b.map Prod.fst)).trans ?_, fun k p b' hk => ?_⟩
  · simpa [List.map_append] using h.1
  · have hlt : k < a.length := (List.getElem?_eq_some_iff.mp hk).1
    exact h.2 k p b' (by rw [List.getElem?_append_left hlt]; exact hk)

theorem schedFits_exists (calls : List (Participant × Bool)) :
    ∃ who ok, SchedFits calls who ok :=
  ⟨calls.map Prod.fst, fun k => (calls[k]?.map Prod.snd).getD false,
    List.prefix_refl _, fun k p b hk => by simp [hk]⟩

/-! ## Flattening -/

@[simp] theorem flatEvents_nil : flatEvents [] = [] := rfl

theorem flatEvents_append (a b : List CliEvent) :
    flatEvents (a ++ b) = flatEvents a ++ flatEvents b := by
  simp [flatEvents, List.flatMap_append]

/-- A non-failed-`send` call flattens to `cliEntryEvents c ++ cliExitEvents c code out`. -/
theorem flatEvents_run_call (c : CliCall) (code : Nat) (out : HwBytes)
    (h : failedSend (runEventOf c (some (code, out))) = false) :
    flatEvents [.run (runEventOf c (some (code, out)))] =
      cliEntryEvents c ++ cliExitEvents c code out := by
  have h' := h
  rcases c with ⟨party, cmd, bundle, stdin, coins⟩
  simp only [flatEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, flatEvent, h',
    Bool.false_eq_true, ↓reduceIte]
  cases cmd <;> cases code <;>
    simp [flatEntry, flatExit, runEventOf, runInput, cliEntryEvents, cliExitEvents]

theorem flatEvents_run_failedSend {ev : RunEvent} (h : failedSend ev = true) :
    flatEvents [.run ev] = [] := by
  simp [flatEvents, flatEvent, h]

theorem failedSend_runEventOf (c : CliCall) (code : Nat) (out : HwBytes) :
    failedSend (runEventOf c (some (code, out))) = true ↔ (∃ peer, c.cmd = .send peer) ∧ code ≠ 0 := by
  rcases c with ⟨party, cmd, bundle, stdin, coins⟩
  cases cmd <;> cases code <;> simp [failedSend, runOk, runEventOf]

/-- The call-start count of `flatEvents evs` equals `(callsOf evs).length`. -/
theorem callStarts_flatEvents_length :
    ∀ evs : List CliEvent, (callStarts (flatEvents evs)).length = (callsOf evs).length
  | [] => rfl
  | .run ev :: evs => by
    have ih := callStarts_flatEvents_length evs
    have hcons : flatEvents (.run ev :: evs) = flatEvent (.run ev) ++ flatEvents evs := by
      simp [flatEvents]
    unfold callStarts at ih ⊢
    rw [hcons, List.filter_append, List.length_append, ih]
    by_cases h : failedSend ev = true
    · simp [flatEvent, callsOf, h]
    · rcases ev with ⟨party, cmd, input, coins, exit⟩
      simp only [Bool.not_eq_true] at h
      simp only [flatEvent, callsOf, h, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      cases cmd <;>
        rcases exit with _ | ⟨_ | code, out⟩ <;>
        simp_all [flatEntry, flatExit, failedSend, runOk, eventKind] <;> omega
  | .env e :: evs => by
    have ih := callStarts_flatEvents_length evs
    have hcons : flatEvents (.env e :: evs) = flatEvent (.env e) ++ flatEvents evs := by
      simp [flatEvents]
    unfold callStarts at ih ⊢
    rw [hcons, List.filter_append, List.length_append, ih]
    cases e <;> simp [flatEvent, callsOf, eventKind]

/-! ## Collisions and Rejected Runs -/

theorem collisionAtCli_append {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {evs : List CliEvent} (more : List CliEvent) (h : CollisionAfterExplainedPrefixClassical interp r S evs) :
    CollisionAfterExplainedPrefixClassical interp r S (evs ++ more) := by
  obtain ⟨evs₁, ev, evs₂, g, ss, vis, heq, hrest⟩ := h
  exact ⟨evs₁, ev, evs₂ ++ more, g, ss, vis, by simp [heq], hrest⟩

theorem runRejected_none (c : CliCall) : RunRejected (runEventOf c none) := by
  intro out h
  simp [runEventOf] at h

theorem matchesEventsAt_snoc_rejected {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {ev : RunEvent} (hrej : RunRejected ev)
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis) :
    MatchesEventsClassicalAt interp r S g initIds tr ss (evs ++ [.run ev]) vis := by
  induction h with
  | @nil initIds tr ss hinv =>
    have h0 : MatchesEventsClassicalAt interp r S g initIds tr (ss ++ []) [.run ev] [] :=
      .run0 hinv hrej (.nil (by simp))
    simpa using h0
  | run1 hpre hrm _ ih => exact .run1 hpre hrm ih
  | run0 hpre hrej' _ ih => exact .run0 hpre hrej' ih
  | env hpre hem _ ih => exact .env hpre hem ih

theorem matchesEvents_snoc_rejected {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ev : RunEvent} (hrej : RunRejected ev) {tr : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassical interp r S g tr ss evs vis) :
    MatchesEventsClassical interp r S g tr ss (evs ++ [.run ev]) vis :=
  matchesEventsAt_snoc_rejected hrej h

/-! ### Bundle ID State Threading -/

theorem activeBundleIds_append (evs₁ evs₂ : List CliEvent) :
    activeBundleIds (evs₁ ++ evs₂) = evs₂.foldl stepBundleIds (activeBundleIds evs₁) := by
  simp [activeBundleIds, List.foldl_append]

theorem stepBundleIds_run_of_runMatches {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step} {ev : RunEvent}
    {v : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hrm : RunMatches interp r S g tr s ev v initIds) :
    stepBundleIds initIds (.run ev) = nextBundleIds initIds ev := by
  obtain ⟨_, _, _, _, _, ⟨out, hexit⟩, _⟩ := hrm
  dsimp only [stepBundleIds, nextBundleIds]
  rw [hexit]
  cases ev.cmd <;> rfl

theorem stepBundleIds_run_of_runRejected {ev : RunEvent} (hrej : RunRejected ev)
    (initIds : Option BundlePreKeyIds) :
    stepBundleIds initIds (.run ev) = initIds := by
  dsimp only [stepBundleIds]
  rcases hexit : ev.exit with _ | ⟨_ | code, out⟩
  · rfl
  · exact (hrej out hexit).elim
  · rfl

theorem stepBundleIds_run_of_not_init {ev : RunEvent}
    (h : ∀ p bd, ev.cmd ≠ .init p bd)
    (initIds : Option BundlePreKeyIds) :
    stepBundleIds initIds (.run ev) = initIds := by
  dsimp only [stepBundleIds]
  rcases ev.exit with _ | ⟨_ | code, out⟩
  · rfl
  · cases hc : ev.cmd
    · exact (h _ _ hc).elim
    · rfl
    · rfl
  · rfl

theorem foldl_stepBundleIds_of_no_init :
    ∀ (evs : List CliEvent) (initIds : Option BundlePreKeyIds),
      (∀ ev, .run ev ∈ evs → ∀ p bd, ev.cmd ≠ .init p bd) →
      evs.foldl stepBundleIds initIds = initIds
  | [], initIds, _ => rfl
  | .env _ :: evs, initIds, h =>
    foldl_stepBundleIds_of_no_init evs initIds (fun ev hev => h ev (List.mem_cons_of_mem _ hev))
  | .run ev :: evs, initIds, h => by
    simp only [List.foldl_cons, stepBundleIds_run_of_not_init (h ev List.mem_cons_self)]
    exact foldl_stepBundleIds_of_no_init evs initIds
      (fun ev' hev' => h ev' (List.mem_cons_of_mem _ hev'))

theorem activeBundleIds_append_of_no_init {evs₁ evs₂ : List CliEvent}
    (h : ∀ ev, .run ev ∈ evs₂ → ∀ p bd, ev.cmd ≠ .init p bd) :
    activeBundleIds (evs₁ ++ evs₂) = activeBundleIds evs₁ := by
  rw [activeBundleIds_append]
  exact foldl_stepBundleIds_of_no_init evs₂ _ h

theorem activeBundleIds_snoc_rejected {evs₁ : List CliEvent} {ev : RunEvent} (hrej : RunRejected ev) :
    activeBundleIds (evs₁ ++ [.run ev]) = activeBundleIds evs₁ := by
  rw [activeBundleIds_append, List.foldl_cons, List.foldl_nil, stepBundleIds_run_of_runRejected hrej]

theorem activeBundleIds_snoc_init_ok {evs₁ : List CliEvent} {ev : RunEvent}
    {peer : CryptoVerification.SignalSession.Address} {bd : String} {out : HwBytes}
    (hcmd : ev.cmd = .init peer bd) (hexit : ev.exit = some (0, out)) :
    activeBundleIds (evs₁ ++ [.run ev]) = some (bundlePreKeyIds ev.input) := by
  rw [activeBundleIds_append, List.foldl_cons, List.foldl_nil]
  simp [stepBundleIds, hexit, hcmd]

/-- A rejected run extends `ExplainsClassical` without adding model steps or visible entries. -/
theorem explains_snoc_rejected {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {ev : RunEvent}
    (hrej : RunRejected ev) (h : ExplainsClassical interp r S g ss vis evs) :
    ExplainsClassical interp r S g ss vis (evs ++ [.run ev]) :=
  ⟨h.1, h.2.1, h.2.2.1, matchesEvents_snoc_rejected hrej h.2.2.2⟩

/-! ## Prefix Restriction -/

theorem runSteps_append : ∀ (a b : List Step) (tr : ExecTrace),
    runSteps (a ++ b) tr = runSteps b (runSteps a tr)
  | [], _, _ => rfl
  | s :: a, b, tr => runSteps_append a b (s.next tr)

theorem runTrace_append (r : ProtocolSetup) (a b : List Step) :
    runTrace r (a ++ b) = runSteps b (runTrace r a) :=
  runSteps_append a b (setupTrace r)

theorem stepsWF_of_append : ∀ {a b : List Step} {tr : ExecTrace},
    StepsWF (a ++ b) tr → StepsWF a tr
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1, h.2.1, stepsWF_of_append h.2.2⟩

theorem stepsStateFaithful_of_append {r : ProtocolSetup} {a b : List Step}
    (h : StepsStateFaithful r (a ++ b)) : StepsStateFaithful r a := by
  intro i j si sj p k bb hij hi hj hload hok hload'
  have hilt : i < a.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjlt : j < a.length := (List.getElem?_eq_some_iff.mp hj).1
  refine h i j si sj p k bb hij (by rw [List.getElem?_append_left hilt]; exact hi)
    (by rw [List.getElem?_append_left hjlt]; exact hj) hload ?_ hload'
  rw [List.take_append_of_le_length (Nat.le_of_lt hilt)]
  exact hok

theorem modelRunWF_of_append {r : ProtocolSetup} {a b : List Step} (h : ModelRunWF r (a ++ b)) :
    ModelRunWF r a :=
  ⟨h.1, h.2.1, stepsWF_of_append h.2.2.1, stepsStateFaithful_of_append h.2.2.2⟩

theorem ghostWF_of_append {g : Ghost} {v₁ v₂ : List VisEntry} (h : GhostWF g (v₁ ++ v₂)) :
    GhostWF g v₁ :=
  ⟨fun v hv => h.1 v (List.mem_append_left v₂ hv), h.2.1,
    fun v hv => h.2.2 v (List.mem_append_left v₂ hv)⟩

theorem readCollisionCli_append {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss₁ : List Step} {evs : List CliEvent} (ss₂ : List Step) (more : List CliEvent)
    (h : ReadCollisionCliClassical interp r S g ss₁ evs) :
    ReadCollisionCliClassical interp r S g (ss₁ ++ ss₂) (evs ++ more) := by
  obtain ⟨e₁, ev, e₂, s₁, s₂, m, vis₁, msgIdx, out, b, t, rfl, rfl, hrest⟩ := h
  exact ⟨e₁, ev, e₂ ++ more, s₁, s₂ ++ ss₂, m, vis₁, msgIdx, out, b, t, by simp, by simp, hrest⟩

end Symbolic.Proofs.Swarm.UA.Base
