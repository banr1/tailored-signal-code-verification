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
import Symbolic.Specifications.Model.EquationalTheory.Kem
public import Symbolic.Specifications.Refinement.Statement
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# KEM Inversion Step

Proves `explains_snoc_invertKEM` and `explains_snoc_invertKEM_step`: a guarded `invertKEM pk sk`
environment event extends any `Explains` witness of `evs` by appending `Step.invertKEM 20`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.InvertKEM

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful ExecTraceTypes ReachabilityConfig)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent)
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF
  (Runs ini_EvE ini_NetE at?_append_self getMessageSentAt_of_at? setupPublic_6 setupTrace_at?_20)

private theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

private theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => Trace.le_refl tr
  | s :: ss, tr => Trace.le_trans tr (s.next tr) (runSteps ss (s.next tr))
      (step_le_next s tr) (runSteps_le ss (s.next tr))

private theorem at?_some_of_le {E : Type} [ExecTraceTypes.Has E] {t T : ExecTrace} (hle : t ≤ T)
    {j : Nat} {x : E} (h : (t.at? j : Option E) = some x) : (T.at? j : Option E) = some x := by
  have h' := Trace.at?_le (EntryT := E) t T j hle
  rwa [h] at h'

private theorem lt_length_of_at?_some {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    {j : Nat} {x : E} (h : (tr.at? j : Option E) = some x) : j < tr.length := by
  by_cases hlt : j < tr.length
  · exact hlt
  · simp [Trace.at?, hlt] at h

private theorem stepIn_preCond_of (c : ReachabilityConfig)
    [inst : ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : c.PreCond x tr) :
    reachability.PreCond (stepIn c x) tr :=
  (inst.pf_pre x tr).mp h

private theorem stepIn_next (c : ReachabilityConfig)
    [inst : ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

private theorem stepIn_ok (c : ReachabilityConfig)
    [inst : ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (inst.pf_step x).symm

private theorem brokenKEMB_mono {t T : ExecTrace} (hle : t ≤ T)
    (h : _root_.DY.Libsignal.PQXDH.brokenKEMB t = true) :
    _root_.DY.Libsignal.PQXDH.brokenKEMB T = true := by
  unfold _root_.DY.Libsignal.PQXDH.brokenKEMB at h ⊢; simp only [_root_.DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h
  cases hat : (t.at? i : Option (_root_.DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => rw [hat] at hi; cases hi
  | some e =>
    rw [hat] at hi
    have hatT := at?_some_of_le hle hat
    refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (lt_length_of_at?_some hatT), ?_⟩
    rwa [hatT]

private theorem brokenKEMB_breakKEM_next (tr : ExecTrace) :
    _root_.DY.Libsignal.PQXDH.brokenKEMB (Step.breakKEM.next tr) = true := by
  have hnext : Step.breakKEM.next tr = (tr.append (ini_EvE .BrokenKEM)) := by
    unfold Step.next Step.toInput
    rw [stepIn_next _root_.DY.Libsignal.PQXDH.breakKEM.reachability () tr]
    exact (Runs.logPQEvent tr .BrokenKEM).2
  rw [hnext]
  unfold _root_.DY.Libsignal.PQXDH.brokenKEMB; rw [_root_.DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  have hat := at?_append_self tr (ini_EvE .BrokenKEM)
  refine List.any_eq_true.mpr ⟨tr.length, List.mem_range.mpr (lt_length_of_at?_some hat), ?_⟩
  rw [hat]

private theorem brokenKEMB_of_matchesEvents {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis) (hmem : CliEvent.env .breakKEM ∈ evs) :
    _root_.DY.Libsignal.PQXDH.brokenKEMB (runSteps ss tr) = true := by
  induction hme with
  | nil _ => cases hmem
  | @run1 _ tr₀ pre s ss' ev evs' v vs _ _ _ ih =>
    rw [runSteps_append]
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · exact ih h
  | @run0 _ tr₀ pre ss' ev evs' vs _ _ _ ih =>
    rw [runSteps_append]
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · exact ih h
  | @env _ tr₀ pre s ss' ev evs' v vs _ hem _ ih =>
    rw [runSteps_append]
    rcases List.mem_cons.mp hmem with h | h
    · injection h with hev
      subst hev
      obtain ⟨rfl, _⟩ := hem
      exact brokenKEMB_mono (runSteps_le ss' _) (brokenKEMB_breakKEM_next (runSteps pre tr₀))
    · exact ih h

private theorem runs_invertKEM {tr : ExecTrace} {pkIdx : Nat} {sk : _root_.DY.Bytes}
    (hbr : _root_.DY.Libsignal.PQXDH.brokenKEMB tr = true)
    (hpk : (tr.at? pkIdx : Option _root_.DY.Network.ExecEntryT) =
      some (ini_NetE (_root_.DY.PQKem.CanPQKem.kemPk sk))) :
    Runs (_root_.DY.Libsignal.PQXDH.invertKEM pkIdx) tr tr.length (tr.append (ini_NetE sk)) := by
  have hsk : _root_.DY.PQKem.invertKemPublicKey (_root_.DY.PQKem.CanPQKem.kemPk sk) = some sk := by
    simp only [_root_.DY.PQKem.invertKemPublicKey, _root_.DY.PQKem.CanPQKem.kemPk,
      _root_.DY.BytesView.view_pack]
  unfold _root_.DY.Libsignal.PQXDH.invertKEM
  refine Runs.bind (Runs.requireTracePredicate hbr) (Runs.bind (Runs.ini_receiveMessage hpk) ?_)
  rw [hsk]
  exact Runs.bind ⟨by erw [_root_.DY.Traceful.run_mk]; rfl, by erw [_root_.DY.Traceful.run_mk]⟩
    (Runs.sendMessage tr sk)

private theorem step_invertKEM_ok_and_next {tr : ExecTrace} {pkIdx : Nat} {sk : _root_.DY.Bytes}
    (hbr : _root_.DY.Libsignal.PQXDH.brokenKEMB tr = true)
    (hpk : (tr.at? pkIdx : Option _root_.DY.Network.ExecEntryT) =
      some (ini_NetE (_root_.DY.PQKem.CanPQKem.kemPk sk))) :
    (Step.invertKEM pkIdx).ok tr = true ∧
      (Step.invertKEM pkIdx).next tr = tr.append (ini_NetE sk) := by
  have hrun := runs_invertKEM hbr hpk
  refine ⟨?_, ?_⟩
  · unfold Step.ok Step.toInput
    rw [stepIn_ok _root_.DY.Libsignal.PQXDH.invertKEM.reachability pkIdx tr]
    change ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).1.isSome = true
    rw [hrun.1]
    rfl
  · unfold Step.next Step.toInput
    rw [stepIn_next _root_.DY.Libsignal.PQXDH.invertKEM.reachability pkIdx tr]
    exact hrun.2

private theorem lastSent_append_net (tr : ExecTrace) (sk : _root_.DY.Bytes) :
    lastSent tr (tr.append (ini_NetE sk)) = some sk := by
  unfold lastSent
  have hlen : (tr.append (ini_NetE sk)).length = tr.length + 1 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt : tr.length < (tr.append (ini_NetE sk)).length := by omega
  have hsub : (tr.append (ini_NetE sk)).length - 1 = tr.length := by omega
  simp only [hlt, ↓reduceIte, hsub]
  exact getMessageSentAt_of_at? (at?_append_self tr (ini_NetE sk))

private theorem stepsWF_snoc {ss : List Step} {s : Step} {tr : ExecTrace}
    (hwf : StepsWF ss tr) (hpre : s.PreCond (runSteps ss tr))
    (hlok : s.LocalOk (runSteps ss tr)) :
    StepsWF (ss ++ [s]) tr := by
  induction ss generalizing tr with
  | nil => exact ⟨hpre, hlok, trivial⟩
  | cons _ xs ih => exact ⟨hwf.1, hwf.2.1, ih hwf.2.2 hpre hlok⟩

private theorem stepsStateFaithful_snoc_nonLoad {r : ProtocolSetup} {ss : List Step} {s : Step}
    (hsf : StepsStateFaithful r ss) (hn : s.stateLoad? = none) :
    StepsStateFaithful r (ss ++ [s]) := by
  intro i j si sj p k b hij hi hj hload hok hload'
  by_cases hjlt : j < ss.length
  · have hilt : i < ss.length := Nat.lt_trans hij hjlt
    rw [List.getElem?_append_left hilt] at hi
    rw [List.getElem?_append_left hjlt] at hj
    rw [List.take_append_of_le_length (Nat.le_of_lt hilt)] at hok
    exact hsf i j si sj p k b hij hi hj hload hok hload'
  · by_cases hjeq : j = ss.length
    · subst hjeq
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero] at hj
      injection hj with hseq
      subst hseq
      rw [hn] at hload'
      cases hload'
    · have hjge : (ss ++ [s]).length ≤ j := by
        simp only [List.length_append, List.length_singleton]; omega
      rw [List.getElem?_eq_none hjge] at hj
      cases hj

private theorem ghostWF_snoc_leak {g : Ghost} {vis : List VisEntry} {v : VisEntry}
    (hg : GhostWF g vis) (hv : v.kind = .leak) : GhostWF g (vis ++ [v]) := by
  refine ⟨fun w hw hwk => ?_, hg.2.1, fun w hw hwk => ?_⟩
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.1 w hw_vis hwk
    · rw [List.mem_singleton.mp hw_v, hv] at hwk
      cases hwk
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.2.2 w hw_vis hwk
    · rw [List.mem_singleton.mp hw_v, hv] at hwk
      cases hwk

private theorem matchesEvents_snoc_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {s : Step} {ev : EnvEvent} {v : VisEntry} :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss evs vis →
      EnvMatches interp r S g (runSteps ss tr) s ev [v] →
      MatchesEventsAt interp r S g initIds tr (ss ++ [s]) (evs ++ [.env ev]) (vis ++ [v])
  | _, _, _, _, _, .nil hinv, hem =>
    MatchesEventsAt.env (v := [v]) (vs := []) hinv hem (.nil fun _ hx => nomatch hx)
  | _, _, _, _, _, @MatchesEventsAt.run1 _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hrm hrest, hem => by
    have ih := matchesEvents_snoc_env hrest (by simpa only [runSteps_append, runSteps] using hem)
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run1 hpre hrm ih
  | _, _, _, _, _, @MatchesEventsAt.run0 _ _ _ _ _ _ _ _ _ _ _ hpre hrej hrest, hem => by
    have ih := matchesEvents_snoc_env hrest (by simpa only [runSteps_append] using hem)
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run0 hpre hrej ih
  | _, _, _, _, _, @MatchesEventsAt.env _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hem₀ hrest, hem => by
    have ih := matchesEvents_snoc_env hrest (by simpa only [runSteps_append, runSteps] using hem)
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.env hpre hem₀ ih

/-- Explicit-extension form of `explains_snoc_invertKEM` preserving the ghost `g` and appending
decrypt-free steps `ext`. -/
theorem explains_snoc_invertKEM_step {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {pk sk : HwBytes}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r)
    (h : Explains interp r S g ss vis evs)
    (hg : InvertsGuarded interp r (evs ++ [.env (.invertKEM pk sk)])) :
    ∃ ext v, (∀ x ∈ ext, x.decryptMsgIdx? = none) ∧
      Explains interp r S g (ss ++ ext) (vis ++ v) (evs ++ [.env (.invertKEM pk sk)]) := by
  let _ := hext
  obtain ⟨hbk_mem, rfl, rfl⟩ := hg evs [] (.invertKEM pk sk) rfl
  let tr := runTrace r ss
  have hbr : _root_.DY.Libsignal.PQXDH.brokenKEMB tr = true :=
    brokenKEMB_of_matchesEvents h.2.2.2 hbk_mem
  have hat20_pub : (tr.at? 20 : Option _root_.DY.Network.ExecEntryT) =
      some (ini_NetE (setupPublic r 6)) :=
    at?_some_of_le (runSteps_le ss (setupTrace r)) (setupTrace_at?_20 r hr.1)
  have hat20 : (tr.at? 20 : Option _root_.DY.Network.ExecEntryT) =
      some (ini_NetE (_root_.DY.PQKem.CanPQKem.kemPk (randTerm 16 64))) := by
    rwa [setupPublic_6 r hr.1] at hat20_pub
  obtain ⟨hok, hnext⟩ := step_invertKEM_ok_and_next hbr hat20
  let v : VisEntry := ⟨.leak, [randTerm 16 64], .leakPq true, none⟩
  have hinv_entry : invertEntry (.invertKEM 20) tr (.leakPq true) = [v] := by
    unfold invertEntry
    rw [hnext, lastSent_append_net]
    rfl
  have hmsg20 : tr.getMessageSentAt 20 = some (setupPublic r 6) :=
    getMessageSentAt_of_at? hat20_pub
  have hgam6 : gamma interp S g (setupPublic r 6) = r.opaqueBytes (setupPublic r 6) :=
    h.1.2.1 r.pqpkPubTerm (by simp)
  have hem : EnvMatches interp r S g tr (.invertKEM 20)
      (.invertKEM (r.opaqueBytes (setupPublic r 6)) r.kyberSecB) [v] := by
    refine ⟨20, rfl, hok, ?_, hinv_entry.symm, v, rfl, rfl, rfl⟩
    rw [hmsg20, Option.map_some, hgam6]
  have hpre : (Step.invertKEM 20).PreCond tr :=
    stepIn_preCond_of _root_.DY.Libsignal.PQXDH.invertKEM.reachability (20 : Nat) tr trivial
  refine ⟨[.invertKEM 20], [v], ?_, h.1, ghostWF_snoc_leak h.2.1 rfl,
    ⟨h.2.2.1.1, h.2.2.1.2.1, stepsWF_snoc (s := .invertKEM 20) h.2.2.1.2.2.1 hpre trivial,
      stepsStateFaithful_snoc_nonLoad h.2.2.1.2.2.2 rfl⟩,
    matchesEvents_snoc_env (s := .invertKEM 20) h.2.2.2 hem⟩
  intro x hx
  rcases List.mem_singleton.mp hx with rfl
  rfl

/-- A guarded `invertKEM pk sk` environment event extends any explanation of `evs`. -/
theorem explains_snoc_invertKEM {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {pk sk : HwBytes}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r)
    (h : Explains interp r S g ss vis evs)
    (hg : InvertsGuarded interp r (evs ++ [.env (.invertKEM pk sk)])) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env (.invertKEM pk sk)]) := by
  obtain ⟨ext, v, -, h'⟩ := explains_snoc_invertKEM_step hext hr h hg
  exact ⟨g, ss ++ ext, vis ++ v, h'⟩

end Symbolic.Proofs.Swarm.UA.BI.InvertKEM
