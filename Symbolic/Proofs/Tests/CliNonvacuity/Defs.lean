/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ExternInterpretationProofDefs
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.PqModelRun
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil

/-!
# Shared Definitions and Combinators for CLI Non-Vacuity

Provides `cliSpecPq_satisfiable_proof`, the proof-side mirror `CliTraceReachableProof` matching
`Symbolic.Tests.CliNonvacuity.CliTraceReachable` definitionally, and reusable `ModelRunWF`,
`InvertsGuarded`, `MatchesEvents`, and prefix-restriction combinators.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Defs

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds nextBundleIds
   slice clamp ExternInterpretationTotalOnUsedSymbols ProtocolSetupWF
   GhostWF StepsWF StepsStateFaithful ModelRunWF
   RunMatches EnvMatches MatchesEventsAt MatchesEvents Explains runTrace)
open DY.Libsignal.Composed.Refinement.Cli
  (ExternContractsHoldCli HooksMatchInterpretation CliTurn initDirs CliTraces runFnToRelation
   dhCoinSecrets coinDraws exitedZeroDraws InvertsGuarded CoinsFresh
   ReadCollisionCli CollisionAfterExplainedPrefix)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession
  (Address CliRun CliHooks CliSpecPqxdh pqModelRun cliSpecPq_pqModelRun)
open Symbolic.Swarm.CREF.TR (setupRandoms_length setupTrace_reachable)

theorem cliSpecPq_satisfiable_proof (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    ∃ run : CliRun, CliSpecPqxdh run X ⟨W.C, W.Q⟩ :=
  ⟨pqModelRun X ⟨W.C, W.Q⟩, cliSpecPq_pqModelRun X ⟨W.C, W.Q⟩⟩

/-- Proof-side mirror of `Symbolic.Tests.CliNonvacuity.CliTraceReachable` with an identical body so
`Symbolic/Tests/CliNonvacuity.lean` delegates its theorem term definitionally without `by` blocks
or circular imports. -/
def CliTraceReachableProof (target : ExecTrace) : Prop :=
  ∃ (interp : ExternInterpretation) (W : CliHooks)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (evs : List CliEvent)
    (g : Ghost) (ss : List Step) (vis : List VisEntry),
    (∀ (X : UnreachedPqxdhPrimitives) (run : CliRun), CliSpecPqxdh run X ⟨W.C, W.Q⟩ →
      CliTraces (runFnToRelation run) interp r (CliTurn.init (initDirs interp r)) evs) ∧
    (∀ ev : RunEvent, .run ev ∈ evs → ∃ out, ev.exit = some (0, out)) ∧
    Explains interp r S g ss vis evs ∧
    runTrace r ss = target ∧
    ExternInterpretationTotalOnUsedSymbols interp ∧
    ExternContractsHoldCli interp ∧
    HooksMatchInterpretation interp W ∧
    ProtocolSetupWF r ∧
    InvertsGuarded interp r evs ∧
    CoinsFresh r evs ∧
    ¬ CollisionAfterExplainedPrefix interp r S evs

/-- Two exit-`0` `init` runs with identical `coins` violate `CoinsFresh` because both draw
`clamp (slice coins 0 32)`. -/
theorem not_coinsFresh_two_inits_same_coins_proof (r : ProtocolSetup) (party₁ party₂ : String)
    (peer₁ peer₂ : Address) (bundle₁ bundle₂ : String) (in₁ in₂ coins out₁ out₂ : HwBytes) :
    ¬ CoinsFresh r
      [.run { party := party₁, cmd := .init peer₁ bundle₁, input := in₁, coins := coins,
              exit := some (0, out₁) },
       .run { party := party₂, cmd := .init peer₂ bundle₂, input := in₂, coins := coins,
              exit := some (0, out₂) }] := by
  intro hnd
  have hsub := (List.nodup_append.mp hnd).2.1
  simp only [List.flatMap_cons, List.flatMap_nil, exitedZeroDraws, coinDraws, dhCoinSecrets,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil] at hsub
  exact (List.nodup_cons.mp hsub).1 (by simp)

theorem modelRunWF_nil (r : ProtocolSetup) (hwf : ProtocolSetupWF r) : ModelRunWF r [] :=
  ⟨setupRandoms_length r hwf.1, setupTrace_reachable r, trivial,
    fun _ _ _ _ _ _ _ _ hi => by simp at hi⟩

def noInvertEvent : CliEvent → Bool
  | .env (.invertDH ..) | .env (.invertKEM ..) => false
  | _ => true

theorem invertsGuarded_of_noInverts {interp : ExternInterpretation} {r : ProtocolSetup}
    {evs : List CliEvent} (h : evs.all noInvertEvent = true) :
    InvertsGuarded interp r evs := by
  intro pre post e heq
  have hmem : CliEvent.env e ∈ evs := by rw [heq]; simp
  have hok := List.all_eq_true.mp h (.env e) hmem
  cases e <;> simp [noInvertEvent] at hok ⊢

theorem matchesEvents_run1 {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {v vs : List VisEntry}
    {initIds : Option BundlePreKeyIds}
    (hrm : RunMatches interp r S g tr s ev v initIds)
    (hrest : MatchesEventsAt interp r S g (nextBundleIds initIds ev) (s.next tr) ss evs vs) :
    MatchesEventsAt interp r S g initIds tr (s :: ss) (.run ev :: evs) (v ++ vs) :=
  MatchesEventsAt.run1 (pre := []) (fun _ h => nomatch h) hrm hrest

theorem matchesEvents_env {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step} {ss : List Step}
    {ev : EnvEvent} {evs : List CliEvent} {v vs : List VisEntry}
    {initIds : Option BundlePreKeyIds}
    (hem : EnvMatches interp r S g tr s ev v)
    (hrest : MatchesEventsAt interp r S g initIds (s.next tr) ss evs vs) :
    MatchesEventsAt interp r S g initIds tr (s :: ss) (.env ev :: evs) (v ++ vs) :=
  MatchesEventsAt.env (pre := []) (fun _ h => nomatch h) hem hrest

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

theorem modelRunWF_of_append {r : ProtocolSetup} {a b : List Step}
    (h : ModelRunWF r (a ++ b)) : ModelRunWF r a :=
  ⟨h.1, h.2.1, stepsWF_of_append h.2.2.1, stepsStateFaithful_of_append h.2.2.2⟩

theorem ghostWF_of_append {g : Ghost} {v₁ v₂ : List VisEntry}
    (h : GhostWF g (v₁ ++ v₂)) : GhostWF g v₁ :=
  ⟨fun v hv => h.1 v (List.mem_append_left v₂ hv),
   h.2.1,
   fun v hv => h.2.2 v (List.mem_append_left v₂ hv)⟩

theorem readCollisionCli_append {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss₁ : List Step} {evs : List CliEvent}
    (ss₂ : List Step) (more : List CliEvent)
    (h : ReadCollisionCli interp r S g ss₁ evs) :
    ReadCollisionCli interp r S g (ss₁ ++ ss₂) (evs ++ more) := by
  obtain ⟨e₁, ev, e₂, s₁, s₂, m, vis₁, msgIdx, out, b, t, rfl, rfl, hrest⟩ := h
  exact ⟨e₁, ev, e₂ ++ more, s₁, s₂ ++ ss₂, m, vis₁, msgIdx, out, b, t, by simp, by simp, hrest⟩

theorem not_readCollisionCli_of_append {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss₁ ss₂ : List Step} {evs more : List CliEvent}
    (h : ¬ ReadCollisionCli interp r S g (ss₁ ++ ss₂) (evs ++ more)) :
    ¬ ReadCollisionCli interp r S g ss₁ evs :=
  fun hrc => h (readCollisionCli_append ss₂ more hrc)

end Symbolic.Proofs.Tests.CliNonvacuity.Defs
