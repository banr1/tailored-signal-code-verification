/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.ProtocolEvent
public import ProofLib.Lemmas
public import Symbolic.Specifications.Refinement.TraceExplanation
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.UA.PendingPreKey
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.Base -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Environment-Step Explanation Extensions

Combinators extending `GhostWF`, `ModelRunWF`, `MatchesEvents`, and `Explains` when a CLI
environment event `.env ev` is explained by an invisible-step prefix followed by an environment
step `s`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.Step

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful TraceEntryHas ExecTraceTypes)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Base (runTrace_append)
open Symbolic.Proofs.Swarm.UA.SlotInitTransfer (stepsWF_append_iff stepsStateFaithful_append_noLoad)
open Symbolic.Proofs.Swarm.UA.PendingPreKey (stepsWF_le)

/-! ## Reachability Step Projections -/

theorem stepIn_preCond_of (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : c.PreCond x tr) :
    reachability.PreCond (stepIn c x) tr :=
  (inst.pf_pre x tr).mp h

theorem stepIn_next (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

theorem stepIn_ok (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (inst.pf_step x).symm

theorem preCond_breakDH (tr : ExecTrace) : Step.breakDH.PreCond tr :=
  stepIn_preCond_of _root_.DY.Libsignal.PQXDH.breakDH.reachability () tr trivial

theorem preCond_breakKEM (tr : ExecTrace) : Step.breakKEM.PreCond tr :=
  stepIn_preCond_of _root_.DY.Libsignal.PQXDH.breakKEM.reachability () tr trivial

theorem next_breakDH (tr : ExecTrace) :
    Step.breakDH.next tr =
      tr.append (⟨_root_.DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH⟩ :
        _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent) := by
  refine (stepIn_next _root_.DY.Libsignal.PQXDH.breakDH.reachability () tr).trans ?_
  dsimp only [_root_.DY.Libsignal.PQXDH.breakDH.reachability, _root_.DY.Libsignal.PQXDH.breakDH]
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  dsimp only
  rw [Traceful.run_pure]

theorem next_breakKEM (tr : ExecTrace) :
    Step.breakKEM.next tr =
      tr.append (⟨_root_.DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM⟩ :
        _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent) := by
  refine (stepIn_next _root_.DY.Libsignal.PQXDH.breakKEM.reachability () tr).trans ?_
  dsimp only [_root_.DY.Libsignal.PQXDH.breakKEM.reachability, _root_.DY.Libsignal.PQXDH.breakKEM]
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  dsimp only
  rw [Traceful.run_pure]

theorem next_network (msg : _root_.DY.Bytes) (tr : ExecTrace) :
    (Step.network msg).next tr = tr.append (⟨msg⟩ : _root_.DY.Network.ExecEntryT) := by
  refine (stepIn_next _root_.DY.Network.reachability msg tr).trans ?_
  dsimp only [_root_.DY.Network.reachability]
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

theorem ok_invertDH_eq (pkIdx : Nat) (tr : ExecTrace) :
    (Step.invertDH pkIdx).ok tr =
      ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).1.isSome :=
  stepIn_ok _root_.DY.Libsignal.PQXDH.invertDH.reachability pkIdx tr

theorem next_invertDH_eq (pkIdx : Nat) (tr : ExecTrace) :
    (Step.invertDH pkIdx).next tr =
      ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).2.val :=
  stepIn_next _root_.DY.Libsignal.PQXDH.invertDH.reachability pkIdx tr

theorem ok_invertKEM_eq (pkIdx : Nat) (tr : ExecTrace) :
    (Step.invertKEM pkIdx).ok tr =
      ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).1.isSome :=
  stepIn_ok _root_.DY.Libsignal.PQXDH.invertKEM.reachability pkIdx tr

theorem next_invertKEM_eq (pkIdx : Nat) (tr : ExecTrace) :
    (Step.invertKEM pkIdx).next tr =
      ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).2.val :=
  stepIn_next _root_.DY.Libsignal.PQXDH.invertKEM.reachability pkIdx tr

/-! ## Environment-Event Extension Combinators -/

theorem ghostWF_append_nonRng {g : Ghost} {vis v : List VisEntry}
    (hg : GhostWF g vis) (hv : ∀ ve ∈ v, ve.kind ≠ .rng ∧ ve.kind ≠ .send) :
    GhostWF g (vis ++ v) := by
  refine ⟨fun w hw hwk => ?_, hg.2.1, fun w hw hwk => ?_⟩
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.1 w hw_vis hwk
    · exact absurd hwk (hv w hw_v).1
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.2.2 w hw_vis hwk
    · exact absurd hwk (hv w hw_v).2

theorem stateLoad_eq_none_of_invisible {s : Step} (h : s.cls = .invisible) :
    s.stateLoad? = none := by
  cases s <;> simp_all [Step.cls, Step.stateLoad?]

theorem modelRunWF_append_noLoad {r : ProtocolSetup} {ss extra : List Step}
    (hwf : ModelRunWF r ss)
    (hsteps : StepsWF extra (runTrace r ss))
    (hnoload : ∀ s ∈ extra, s.stateLoad? = none) :
    ModelRunWF r (ss ++ extra) :=
  ⟨hwf.1, hwf.2.1,
    (stepsWF_append_iff ss extra (setupTrace r)).mpr ⟨hwf.2.2.1, hsteps⟩,
    stepsStateFaithful_append_noLoad hwf.2.2.2 hnoload⟩

/-- Extend `MatchesEventsAt` by an invisible prefix `pre` and one environment step `s` matching
`.env ev` with visible entries `v`. -/
theorem matchesEventsAt_snoc_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss pre : List Step} {s : Step}
    {evs : List CliEvent} {ev : EnvEvent} {vis v : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hpre : ∀ x ∈ pre, x.cls = .invisible)
    (hem : EnvMatches interp r S g (runSteps pre (runSteps ss tr)) s ev v) :
    MatchesEventsAt interp r S g initIds tr (ss ++ (pre ++ [s])) (evs ++ [.env ev]) (vis ++ v) := by
  induction hme with
  | @nil initIds tr ss₀ hinv =>
    have hpre' : ∀ x ∈ ss₀ ++ pre, x.cls = .invisible := by
      intro x hx
      rcases List.mem_append.mp hx with hx₀ | hx₁
      · exact hinv x hx₀
      · exact hpre x hx₁
    have hem' : EnvMatches interp r S g (runSteps (ss₀ ++ pre) tr) s ev v := by
      rwa [runSteps_append]
    have h0 : MatchesEventsAt interp r S g initIds tr ((ss₀ ++ pre) ++ s :: []) [.env ev] (v ++ []) :=
      .env hpre' hem' (.nil (by simp))
    simpa [List.append_assoc] using h0
  | @run1 _ tr pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hrm₀ _ ih =>
    have hem' : EnvMatches interp r S g
        (runSteps pre (runSteps ss' (s₀.next (runSteps pre₀ tr)))) s ev v := by
      simpa only [runSteps_append, runSteps] using hem
    have ih' := ih hem'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run1 hpre₀ hrm₀ ih'
  | @run0 _ tr pre₀ ss' ev₀ evs' vs' hpre₀ hrej₀ _ ih =>
    have hem' : EnvMatches interp r S g
        (runSteps pre (runSteps ss' (runSteps pre₀ tr))) s ev v := by
      simpa only [runSteps_append] using hem
    have ih' := ih hem'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run0 hpre₀ hrej₀ ih'
  | @env _ tr pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hem₀ _ ih =>
    have hem' : EnvMatches interp r S g
        (runSteps pre (runSteps ss' (s₀.next (runSteps pre₀ tr)))) s ev v := by
      simpa only [runSteps_append, runSteps] using hem
    have ih' := ih hem'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.env hpre₀ hem₀ ih'

theorem matchesEvents_snoc_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {ss pre : List Step} {s : Step}
    {evs : List CliEvent} {ev : EnvEvent} {vis v : List VisEntry}
    (hme : MatchesEvents interp r S g tr ss evs vis)
    (hpre : ∀ x ∈ pre, x.cls = .invisible)
    (hem : EnvMatches interp r S g (runSteps pre (runSteps ss tr)) s ev v) :
    MatchesEvents interp r S g tr (ss ++ (pre ++ [s])) (evs ++ [.env ev]) (vis ++ v) :=
  matchesEventsAt_snoc_env hme hpre hem

/-- Extends `Explains interp r S g ss vis evs` by an invisible-step prefix `pre` and an
environment step `s` with non-`rng`, non-`send` visible entries `v`. -/
theorem explains_snoc_env_with_pre {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss pre : List Step} {s : Step} {vis v : List VisEntry}
    {evs : List CliEvent} {ev : EnvEvent}
    (h : Explains interp r S g ss vis evs)
    (hpre_inv : ∀ x ∈ pre, x.cls = .invisible)
    (hpre_wf : StepsWF pre (runTrace r ss))
    (hs_pre : s.PreCond (runSteps pre (runTrace r ss)))
    (hs_lok : s.LocalOk (runSteps pre (runTrace r ss)))
    (hs_noload : s.stateLoad? = none)
    (hv : ∀ ve ∈ v, ve.kind ≠ .rng ∧ ve.kind ≠ .send)
    (hem : EnvMatches interp r S g (runSteps pre (runTrace r ss)) s ev v) :
    Explains interp r S g (ss ++ (pre ++ [s])) (vis ++ v) (evs ++ [.env ev]) := by
  have hextra_wf : StepsWF (pre ++ [s]) (runTrace r ss) :=
    (stepsWF_append_iff pre [s] (runTrace r ss)).mpr ⟨hpre_wf, hs_pre, hs_lok, trivial⟩
  have hextra_noload : ∀ x ∈ pre ++ [s], x.stateLoad? = none := by
    intro x hx
    rcases List.mem_append.mp hx with hx_pre | hx_s
    · exact stateLoad_eq_none_of_invisible (hpre_inv x hx_pre)
    · rw [List.mem_singleton.mp hx_s]
      exact hs_noload
  exact ⟨h.1,
    ghostWF_append_nonRng h.2.1 hv,
    modelRunWF_append_noLoad h.2.2.1 hextra_wf hextra_noload,
    matchesEvents_snoc_env h.2.2.2 hpre_inv hem⟩

theorem explains_snoc_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {s : Step} {vis v : List VisEntry}
    {evs : List CliEvent} {ev : EnvEvent}
    (h : Explains interp r S g ss vis evs)
    (hs_pre : s.PreCond (runTrace r ss))
    (hs_lok : s.LocalOk (runTrace r ss))
    (hs_noload : s.stateLoad? = none)
    (hv : ∀ ve ∈ v, ve.kind ≠ .rng ∧ ve.kind ≠ .send)
    (hem : EnvMatches interp r S g (runTrace r ss) s ev v) :
    Explains interp r S g (ss ++ [s]) (vis ++ v) (evs ++ [.env ev]) :=
  explains_snoc_env_with_pre (pre := []) h (by simp) trivial hs_pre hs_lok hs_noload hv hem

theorem explains_snoc_env_silent {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {s : Step} {vis : List VisEntry}
    {evs : List CliEvent} {ev : EnvEvent}
    (h : Explains interp r S g ss vis evs)
    (hs_pre : s.PreCond (runTrace r ss))
    (hs_lok : s.LocalOk (runTrace r ss))
    (hs_noload : s.stateLoad? = none)
    (hem : EnvMatches interp r S g (runTrace r ss) s ev []) :
    Explains interp r S g (ss ++ [s]) vis (evs ++ [.env ev]) := by
  simpa only [List.append_nil] using
    explains_snoc_env h hs_pre hs_lok hs_noload (by simp) hem

end Symbolic.Proofs.Swarm.UA.BI.Step
