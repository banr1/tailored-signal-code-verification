/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps
import Symbolic.Proofs.Swarm.CREF.CBadReadableBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey
import Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Session-Promotion Pre-Key Receive Auxiliary Lemmas

Auxiliary lemmas for Bob's session-promotion pre-key `recv` slot: `ReadCollisionCli` preservation
on rejected and accepting `recv` runs, `MatchesEvents` non-invisible cut uniqueness across
environment steps, single-step `ValidLoadStep` bridges, and quiet-failure helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkPromAux

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Traceful)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup Ghost OpaqueSymbolSemantics Step VisEntry EnvMatches invertEntry
  ProtocolSetupWF Explains MatchesEvents MatchesEventsAt BundlePreKeyIds activeBundleIds RunRejected
  runSteps runTrace setupTrace PreKeyFields
  KnownBaseKeyOn recvRepresentationsOn RecvCollisionOn ReselectCollisionOn honestSaltsOf
  honestKeysOf principalTerms plaintextTerms
  prefixTerms MemoCollisionOn whisperTrials stepView runWrapped)
open _root_.DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCli)
open _root_.DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot)
open Symbolic.Swarm.COMPOSED.CompTrace (NetEntry NetE at?_append_cases proj_inj_eq)
open Symbolic.Swarm.CREF (SemReady)
open Symbolic.Proofs.Swarm.UA.Defs (SchedFits callsOf)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (XlateInvSpecB)
open Symbolic.Proofs.Swarm.UA.Base (callsOf_append schedFits_of_append runSteps_append)

/-! ## Rejected Runs and Cut Uniqueness -/

theorem not_readCollisionCli_snoc_rejected {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {evs : List CliEvent} {ev : RunEvent}
    (hrej : RunRejected ev) (hnrc : ¬ ReadCollisionCli interp r S g ss evs) :
    ¬ ReadCollisionCli interp r S g ss (evs ++ [.run ev]) := by
  rintro ⟨evs₁, ev₀, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out₀, b₀, t,
    heq, hss, hcmd₀, hexit₀, hbody₀, hme₁, hm, hmsg, hcol⟩
  rcases List.eq_nil_or_concat evs₂ with rfl | ⟨evs₂', last, rfl⟩
  · have hlast : [CliEvent.run ev] = [CliEvent.run ev₀] := List.append_inj_right' heq rfl
    injection hlast with hrun_eq
    injection hrun_eq with hev_eq
    subst hev_eq
    exact hrej out₀ hexit₀
  · rw [List.concat_eq_append, ← List.cons_append, ← List.append_assoc] at heq
    have hpre : evs = evs₁ ++ .run ev₀ :: evs₂' := List.append_inj_left' heq rfl
    exact hnrc ⟨evs₁, ev₀, evs₂', ss₁, ss₂, m, vis₁, msgIdx, out₀, b₀, t,
      hpre, hss, hcmd₀, hexit₀, hbody₀, hme₁, hm, hmsg, hcol⟩

private theorem matchesEvents_restrict_tail {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (more : List CliEvent) (evs : List CliEvent)
    {tr : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (h : MatchesEvents interp r S g tr ss (evs ++ more) vis) :
    ∃ ss₁ ss₂ vis₁ vis₂, ss = ss₁ ++ ss₂ ∧ vis = vis₁ ++ vis₂ ∧
      MatchesEvents interp r S g tr ss₁ evs vis₁ ∧
      MatchesEventsAt interp r S g (activeBundleIds evs) (runSteps ss₁ tr) ss₂ more vis₂ :=
  Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey.matchesEvents_split more evs h

private def envVis (s : Step) (tr : ExecTrace) : EnvEvent → List VisEntry
  | .leak _ _ => stepView s tr false
  | .breakDH | .breakKEM => []
  | .invertDH _ _ => invertEntry s tr .leakRecord
  | .invertKEM _ _ => invertEntry s tr (.leakPq true)
  | .registerCorrupt _ _ => []

private theorem envMatches_vis {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {ev : EnvEvent} {v : List VisEntry}
    (hem : EnvMatches interp r S g tr s ev v) : v = envVis s tr ev := by
  cases ev with
  | leak _ _ => exact hem.2.2.2.1
  | breakDH => exact hem.2
  | breakKEM => exact hem.2
  | invertDH _ _ => obtain ⟨_, _, _, _, hv, _⟩ := hem; exact hv
  | invertKEM _ _ => obtain ⟨_, _, _, _, hv, _⟩ := hem; exact hv
  | registerCorrupt _ _ => exact hem.elim

private theorem envMatches_cls {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {ev : EnvEvent} {v : List VisEntry}
    (hem : EnvMatches interp r S g tr s ev v) : s.cls = .env := by
  cases ev with
  | leak _ _ => exact hem.1
  | breakDH => rw [hem.1]; rfl
  | breakKEM => rw [hem.1]; rfl
  | invertDH _ _ => obtain ⟨_, rfl, _⟩ := hem; rfl
  | invertKEM _ _ => obtain ⟨_, rfl, _⟩ := hem; rfl
  | registerCorrupt _ _ => exact hem.elim

private def isActiveEvent : CliEvent → Bool
  | .env _ => true
  | .run ev =>
    match ev.exit with
    | some (0, _) => true
    | _ => false

private def isNonInvisible (s : Step) : Bool :=
  s.cls != .invisible

private theorem filter_nonInvisible_eq_nil {ss : List Step}
    (hinv : ∀ x ∈ ss, x.cls = .invisible) :
    ss.filter isNonInvisible = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  unfold isNonInvisible
  rw [hinv x hx]
  decide

private theorem matchesEvents_filter_nonInvisible_length {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis) :
    (ss.filter isNonInvisible).length = (evs.filter isActiveEvent).length := by
  induction hme with
  | nil hinv => rw [filter_nonInvisible_eq_nil hinv]; rfl
  | @run0 _ _ pre _ ev _ _ hpre hrej _ ih =>
    have hact : isActiveEvent (.run ev) = false := by
      unfold isActiveEvent
      cases hex : ev.exit with
      | none => simp [hex]
      | some p =>
        rcases p with ⟨code, out⟩
        cases code with
        | zero => exact absurd hex (hrej out)
        | succ _ => simp [hex]
    rw [List.filter_append, filter_nonInvisible_eq_nil hpre, List.nil_append,
      List.filter_cons_of_neg (by simp [hact]), ih]
  | @run1 _ _ pre s _ ev _ _ _ hpre hrm _ ih =>
    obtain ⟨out, hex⟩ := hrm.2.2.2.2.2.1
    have hact : isActiveEvent (.run ev) = true := by simp [isActiveEvent, hex]
    have hs : isNonInvisible s = true := by unfold isNonInvisible; rw [hrm.1]; decide
    rw [List.filter_append, filter_nonInvisible_eq_nil hpre, List.nil_append,
      List.filter_cons_of_pos hs, List.filter_cons_of_pos hact, List.length_cons,
      List.length_cons, ih]
  | @env _ _ pre s _ ev _ _ _ hpre hem _ ih =>
    have hs : isNonInvisible s = true := by
      unfold isNonInvisible; rw [envMatches_cls hem]; decide
    rw [List.filter_append, filter_nonInvisible_eq_nil hpre, List.nil_append,
      List.filter_cons_of_pos hs, List.filter_cons_of_pos rfl, List.length_cons,
      List.length_cons, ih]

private theorem matchesEvents_append_invisible {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss extra : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hextra : ∀ x ∈ extra, x.cls = .invisible) :
    MatchesEventsAt interp r S g initIds tr (ss ++ extra) evs vis := by
  induction hme with
  | @nil _ _ _ hinv =>
    exact .nil (fun x hx => (List.mem_append.mp hx).elim (hinv x) (hextra x))
  | @run0 _ _ _ _ _ _ _ hpre hrej _ ih => rw [List.append_assoc]; exact .run0 hpre hrej ih
  | @run1 _ _ _ _ _ _ _ _ _ hpre hrm _ ih =>
    rw [List.append_assoc, List.cons_append]; exact .run1 hpre hrm ih
  | @env _ _ _ _ _ _ _ _ _ hpre hem _ ih =>
    rw [List.append_assoc, List.cons_append]; exact .env hpre hem ih

private theorem matchesEvents_cons_invisible {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {x : Step} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hx : x.cls = .invisible) (hme : MatchesEventsAt interp r S g initIds tr (x :: ss) evs vis) :
    MatchesEventsAt interp r S g initIds (x.next tr) ss evs vis := by
  generalize hxs : x :: ss = xs at hme
  induction hme generalizing x ss with
  | nil hinv => subst hxs; exact .nil (fun y hy => hinv y (List.mem_cons_of_mem x hy))
  | @run0 _ _ pre _ _ _ _ hpre hrej hrest ih =>
    cases pre with
    | nil =>
      simp only [List.nil_append] at hxs
      dsimp only [runSteps] at ih
      exact .run0 (pre := []) (fun _ h => nomatch h) hrej (ih hx hxs)
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact .run0 (fun y hy => hpre y (List.mem_cons_of_mem _ hy)) hrej hrest
  | @run1 _ _ pre _ _ _ _ _ _ hpre hrm hrest _ =>
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, _⟩
      rw [hrm.1] at hx; cases hx
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact .run1 (fun y hy => hpre y (List.mem_cons_of_mem _ hy)) hrm hrest
  | @env _ _ pre _ _ ev _ _ _ hpre hem hrest _ =>
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, _⟩
      rw [envMatches_cls hem] at hx; cases hx
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact .env (fun y hy => hpre y (List.mem_cons_of_mem _ hy)) hem hrest

private theorem matchesEvents_vis_nonInvisible {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {x : Step} {ss : List Step}
    {ev₀ : CliEvent} {evs' : List CliEvent} {vis : List VisEntry}
    (hx : x.cls ≠ .invisible) (hme : MatchesEventsAt interp r S g initIds tr (x :: ss) (ev₀ :: evs') vis) :
    (∃ ev, ev₀ = .run ev ∧ RunRejected ev ∧ MatchesEventsAt interp r S g initIds tr (x :: ss) evs' vis) ∨
    (∃ ev vs initIds', ev₀ = .run ev ∧ (∃ out, ev.exit = some (0, out)) ∧
      vis = stepView x tr (runWrapped ev) ++ vs ∧ MatchesEventsAt interp r S g initIds' (x.next tr) ss evs' vs) ∨
    (∃ ev vs, ev₀ = .env ev ∧ vis = envVis x tr ev ++ vs ∧
      MatchesEventsAt interp r S g initIds (x.next tr) ss evs' vs) := by
  generalize hxs : x :: ss = xs at hme
  generalize hevs : ev₀ :: evs' = evs at hme
  cases hme with
  | nil _ => cases hevs
  | @run0 _ _ pre _ ev _ _ hpre hrej hrest =>
    injection hevs with hev₀ hevs₁; subst hev₀ hevs₁
    cases pre with
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs
      exact absurd (hpre p₀ List.mem_cons_self) (hxs.1 ▸ hx)
    | nil => simp only [List.nil_append] at hxs; subst hxs; exact Or.inl ⟨ev, rfl, hrej, hrest⟩
  | @run1 _ _ pre _ _ ev _ _ vs hpre hrm hrest =>
    injection hevs with hev₀ hevs₁; subst hev₀ hevs₁
    cases pre with
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs
      exact absurd (hpre p₀ List.mem_cons_self) (hxs.1 ▸ hx)
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl ⟨ev, vs, _, rfl, hrm.2.2.2.2.2.1,
        congrArg (· ++ vs) hrm.2.2.2.2.2.2.1, hrest⟩)
  | @env _ _ pre s _ ev _ v vs hpre hem hrest =>
    injection hevs with hev₀ hevs₁; subst hev₀ hevs₁
    cases pre with
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs
      exact absurd (hpre p₀ List.mem_cons_self) (hxs.1 ▸ hx)
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact Or.inr (Or.inr ⟨ev, vs, rfl, congrArg (· ++ vs) (envMatches_vis hem), hrest⟩)

private theorem matchesEvents_nil_steps_inv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ev₀ : CliEvent} {evs' : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr [] (ev₀ :: evs') vis) :
    MatchesEventsAt interp r S g initIds tr [] evs' vis := by
  generalize hxs : ([] : List Step) = xs at hme
  generalize hevs : ev₀ :: evs' = evs at hme
  cases hme with
  | nil _ => cases hevs
  | @run1 _ _ pre _ _ _ _ _ _ _ _ _ => cases pre <;> simp at hxs
  | @env _ _ pre _ _ _ _ _ _ _ _ _ => cases pre <;> simp at hxs
  | @run0 _ _ pre _ _ _ _ _ _ hrest =>
    injection hevs with _ hevs₁; subst hevs₁
    rcases List.append_eq_nil_iff.mp hxs.symm with ⟨rfl, rfl⟩; exact hrest

private theorem matchesEvents_vis_unique {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} :
    ∀ {evs : List CliEvent} {ss : List Step} {initIds₁ initIds₂ : Option BundlePreKeyIds}
      {tr : ExecTrace} {vis₁ vis₂ : List VisEntry},
      MatchesEventsAt interp r S g₁ initIds₁ tr ss evs vis₁ →
      MatchesEventsAt interp r S g₂ initIds₂ tr ss evs vis₂ →
      vis₁ = vis₂
  | [], _, _, _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; rfl
  | ev₀ :: evs', ss, initIds₁, initIds₂, tr, vis₁, vis₂, h₁, h₂ => by
    induction ss generalizing initIds₁ initIds₂ tr vis₁ vis₂ with
    | nil =>
      exact matchesEvents_vis_unique (matchesEvents_nil_steps_inv h₁) (matchesEvents_nil_steps_inv h₂)
    | cons x ss' ih_ss =>
      by_cases hx : x.cls = .invisible
      · exact @ih_ss initIds₁ initIds₂ (x.next tr) vis₁ vis₂
          (matchesEvents_cons_invisible hx h₁) (matchesEvents_cons_invisible hx h₂)
      · rcases matchesEvents_vis_nonInvisible hx h₁ with
            ⟨ev₁, rfl, hrej₁, hrest₁⟩ | ⟨ev₁, vs₁, _, rfl, ⟨out₁, hex₁⟩, rfl, hrest₁⟩ |
            ⟨ev₁, vs₁, rfl, rfl, hrest₁⟩
        · rcases matchesEvents_vis_nonInvisible hx h₂ with
              ⟨_, heq, _, hrest₂⟩ | ⟨_, _, _, heq, ⟨out₂, hex₂⟩, _, _⟩ | ⟨_, _, heq, _⟩
          · injection heq; exact matchesEvents_vis_unique hrest₁ hrest₂
          · injection heq with hev; subst hev; exact absurd hex₂ (hrej₁ out₂)
          · cases heq
        · rcases matchesEvents_vis_nonInvisible hx h₂ with
              ⟨_, heq, hrej₂, _⟩ | ⟨_, vs₂, _, heq, _, rfl, hrest₂⟩ | ⟨_, _, heq, _⟩
          · injection heq with hev; subst hev; exact absurd hex₁ (hrej₂ out₁)
          · injection heq with hev; subst hev; rw [matchesEvents_vis_unique hrest₁ hrest₂]
          · cases heq
        · rcases matchesEvents_vis_nonInvisible hx h₂ with
              ⟨_, heq, _⟩ | ⟨_, _, _, heq, _⟩ | ⟨_, vs₂, heq, rfl, hrest₂⟩
          · cases heq
          · cases heq
          · injection heq with hev; subst hev; rw [matchesEvents_vis_unique hrest₁ hrest₂]

private theorem honestKeysOf_append :
    ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
      honestKeysOf tr (ss₁ ++ ss₂) = honestKeysOf tr ss₁ ++ honestKeysOf (runSteps ss₁ tr) ss₂
  | [], _, _ => rfl
  | s :: ss₁, ss₂, tr => by
    simp only [List.cons_append, honestKeysOf, runSteps, honestKeysOf_append ss₁ ss₂ (s.next tr),
      List.append_assoc]

private theorem honestKeysOf_map_network :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      honestKeysOf tr (ext.map Step.network) = []
  | [], _ => rfl
  | x :: ext, tr => by
    simp [honestKeysOf, Step.publishedSpqrKey?, honestKeysOf_map_network ext ((Step.network x).next tr)]

private theorem honestSaltsOf_append_network (r : ProtocolSetup) (ss : List Step)
    (ext : List _root_.DY.Bytes) :
    honestSaltsOf r (ss ++ ext.map Step.network) = honestSaltsOf r ss := by
  simp [honestSaltsOf, honestKeysOf_append, honestKeysOf_map_network]

private theorem network_next_eq_append (tr : ExecTrace) (x : _root_.DY.Bytes) :
    (Step.network x).next tr = tr.append (NetE x) := by
  dsimp only [Step.next, Step.toInput, _root_.DY.Libsignal.Composed.Refinement.stepIn]
  rw [← (_root_.DY.ReachabilityConfig.HasStep.pf_step
    (config1 := _root_.DY.Network.reachability) (config2 := reachability) x)]
  dsimp only [_root_.DY.Network.reachability]
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_mk]

private theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

private theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => _root_.DY.Trace.le_refl tr
  | s :: ss, tr => _root_.DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

private theorem prefixTerms_runSteps_network {r : ProtocolSetup} {vis : List VisEntry} :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      prefixTerms r (runSteps (ext.map Step.network) tr) vis = prefixTerms r tr vis
  | [], _ => rfl
  | x :: ext, tr => by
    simp only [List.map_cons, runSteps, network_next_eq_append]
    rw [prefixTerms_runSteps_network ext]
    simp [prefixTerms, principalTerms, Symbolic.Swarm.CREF.storedStates_append_network,
      Symbolic.Swarm.CREF.storedSecrets_append_network, NetE]

private theorem whisperTrials_runSteps_network {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg} :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      whisperTrials interp r S g (runSteps (ext.map Step.network) tr) msg =
        whisperTrials interp r S g tr msg
  | [], _ => rfl
  | x :: ext, tr => by
    simp only [List.map_cons, runSteps, network_next_eq_append]
    rw [whisperTrials_runSteps_network ext,
      Symbolic.Swarm.CREF.whisperTrials_append_network interp r S g tr x msg]

private theorem recvCollisionOn_of_append_network {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {ext : List _root_.DY.Bytes} {vis : List VisEntry}
    {t : _root_.DY.Bytes}
    (hcol : RecvCollisionOn interp r S g (runTrace r (ss ++ ext.map Step.network)) vis
      (honestSaltsOf r (ss ++ ext.map Step.network)) t) :
    RecvCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t := by
  rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append, honestSaltsOf_append_network] at hcol
  have hle_ext : runTrace r ss ≤ runSteps (ext.map Step.network) (runTrace r ss) :=
    runSteps_le (ext.map Step.network) (runTrace r ss)
  have hkn : ∀ u : _root_.DY.Bytes,
      u.AttackerKnows (runTrace r ss) →
      u.AttackerKnows (runSteps (ext.map Step.network) (runTrace r ss)) :=
    fun _ hu => _root_.DY.Bytes.AttackerKnows_le _ _ _ hle_ext hu
  have hpfx : prefixTerms r (runSteps (ext.map Step.network) (runTrace r ss)) vis =
      prefixTerms r (runTrace r ss) vis :=
    prefixTerms_runSteps_network ext (runTrace r ss)
  have hpfx_sub : prefixTerms r (runSteps (ext.map Step.network) (runTrace r ss)) vis ⊆
      prefixTerms r (runTrace r ss) vis :=
    fun _ hu => by rwa [hpfx] at hu
  unfold RecvCollisionOn at hcol ⊢
  cases hp : _root_.DY.Libsignal.TripleRatchet.parseTrSignalMsg t with
  | none =>
    simp only [hp] at hcol ⊢
    exact Symbolic.Swarm.CREF.Stage1Trials.MemoCollisionOn.mono_quiet
      (List.Subset.refl _) hpfx_sub rfl hkn hcol
  | some msg =>
    simp only [hp] at hcol ⊢
    have hwt : whisperTrials interp r S g (runSteps (ext.map Step.network) (runTrace r ss)) msg =
        whisperTrials interp r S g (runTrace r ss) msg :=
      whisperTrials_runSteps_network ext (runTrace r ss)
    rw [hwt] at hcol
    rcases hcol with hmemo | hmac
    · exact Or.inl (Symbolic.Swarm.CREF.Stage1Trials.MemoCollisionOn.mono_quiet
        (List.Subset.refl _) hpfx_sub rfl hkn hmemo)
    · exact Or.inr (Symbolic.Swarm.CREF.Stage1Trials.MacTagForgeryOrCollision.mono_ctxs
        (List.Subset.refl _) hkn hmac)

private theorem getMessageSentAt_append_net {tr : ExecTrace} {x u : _root_.DY.Bytes} {idx : Nat}
    (h : (tr.append (NetE x)).getMessageSentAt idx = some u) :
    (∃ k, tr.getMessageSentAt k = some u) ∨ u = x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h
  rcases hat : ((tr.append (NetE x)).at? idx : Option NetEntry) with _ | ⟨y⟩
  · simp [hat] at h
  · simp [hat] at h; subst h
    rcases at?_append_cases hat with ⟨_, heq⟩ | ⟨_, hproj⟩
    · refine Or.inl ⟨idx, ?_⟩
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      simp [heq]
    · rw [proj_inj_eq] at hproj
      injection hproj with h1
      subst h1
      exact Or.inr rfl

private theorem getMessageSentAt_runSteps_network :
    ∀ (ext : List _root_.DY.Bytes) {tr : ExecTrace} {idx : Nat} {u : _root_.DY.Bytes},
      (runSteps (ext.map Step.network) tr).getMessageSentAt idx = some u →
      (∃ k, tr.getMessageSentAt k = some u) ∨ u ∈ ext
  | [], _, idx, _, h => Or.inl ⟨idx, h⟩
  | x :: ext, tr, _, _, h => by
    simp only [List.map_cons, runSteps, network_next_eq_append] at h
    rcases getMessageSentAt_runSteps_network ext h with ⟨k, hk⟩ | hmem
    · rcases getMessageSentAt_append_net hk with ⟨k', hk'⟩ | rfl
      · exact Or.inl ⟨k', hk'⟩
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem x hmem)

theorem recvCollision_iff_of_terms {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List _root_.DY.Libsignal.Composed.Refinement.Move} {tr : ExecTrace}
    {vis : List VisEntry} {salts : List _root_.DY.Bytes} {t : _root_.DY.Bytes}
    (htr : _root_.DY.Libsignal.Composed.Refinement.runTraceMoves r ms = tr)
    (hsalts : _root_.DY.Libsignal.Composed.Refinement.honestSalts r ms = salts)
    (hpre : prefixTerms r tr (_root_.DY.Libsignal.Composed.Refinement.runVis r ms) =
      prefixTerms r tr vis)
    (hpt : plaintextTerms (_root_.DY.Libsignal.Composed.Refinement.runVis r ms) = plaintextTerms vis) :
    _root_.DY.Libsignal.Composed.Refinement.RecvCollision interp r S g ms t ↔
      RecvCollisionOn interp r S g tr vis salts t := by
  subst htr; subst hsalts
  unfold _root_.DY.Libsignal.Composed.Refinement.RecvCollision RecvCollisionOn
  dsimp only
  cases _root_.DY.Libsignal.TripleRatchet.parseTrSignalMsg t with
  | none => simp only [MemoCollisionOn, hpre, hpt]
  | some msg => exact or_congr_left (by simp only [MemoCollisionOn, hpre, hpt])

private theorem recvCollisionOn_transfer_via_xlate {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {evs : List CliEvent} {g g₁ : Ghost} {ss : List Step} {vis : List VisEntry}
    {n : Nat} {t : _root_.DY.Bytes}
    (hInv : XlateInvSpecB) (hr : ProtocolSetupWF r) (hS : SemReady interp r S)
    (hfit : SchedFits (callsOf evs) who ok)
    (hex : Explains interp r S g ss vis evs)
    (hnrc : ¬ ReadCollisionCli interp r S g ss evs)
    (haddr : g₁.addr = g.addr)
    (hσ : ∀ i, i < n → g₁.σ i = g.σ i)
    (hlen : (runTrace r ss).length ≤ n)
    (ht_src : (∃ k, (runTrace r ss).getMessageSentAt k = some t) ∨ t.AttackerKnows (runTrace r ss))
    (hcol₁ : RecvCollisionOn interp r S g₁ (runTrace r ss) vis (honestSaltsOf r ss) t) :
    RecvCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t := by
  obtain ⟨τ, ms, hex_cli, hnrc_cli, gtr, gsalts, gpfx, gpt⟩ := hInv hr hS hfit hex hnrc
  have hc := Symbolic.Swarm.Coinsplit.Lift.explainsCli_toClean hex_cli hnrc_cli
  have hfr : Symbolic.Swarm.CREF.CBadSigmaFrame g g₁ n :=
    ⟨fun ts hts len => congrFun (hσ ts hts) len, haddr⟩
  have hga := Symbolic.Swarm.CREF.cbadG2_gammaAgree_of_sigmaFrame interp S hfr
  have hst := Symbolic.Swarm.CREF.cbadG2_stamps_of_matched hc.matched (gtr ▸ hlen)
  have ht_st := ht_src.elim
    (fun ⟨k, hk⟩ => Symbolic.Swarm.CREF.cbadG2_stampsLt_getMessageSentAt hst (gtr.symm ▸ hk))
    (fun hkn => hst.knows (gtr.symm ▸ hkn))
  have hcol₁_m := (recvCollision_iff_of_terms (g := g₁) gtr gsalts gpfx gpt).mpr hcol₁
  have hcol_m := Symbolic.Swarm.CREF.CliPure.cbadG2_recvCollision_transfer hga hst ht_st hcol₁_m
  exact (recvCollision_iff_of_terms (g := g) gtr gsalts gpfx gpt).mp hcol_m

private theorem eq_of_append_cons_filter {α : Type} {p : α → Bool} :
    ∀ {xs₁ xs₂ : List α} {a b : α} {ys₁ ys₂ : List α},
      xs₁ ++ a :: ys₁ = xs₂ ++ b :: ys₂ →
      p a = true → p b = true →
      (xs₁.filter p).length = (xs₂.filter p).length →
      xs₁ = xs₂ ∧ a = b ∧ ys₁ = ys₂
  | [], [], a, b, ys₁, ys₂, heq, _, _, _ => by
    simp only [List.nil_append, List.cons.injEq] at heq
    exact ⟨rfl, heq.1, heq.2⟩
  | [], x₂ :: xs₂, a, _, ys₁, ys₂, heq, ha, _, hlen => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, _⟩
    simp [ha] at hlen
  | x₁ :: xs₁, [], _, b, ys₁, ys₂, heq, _, hb, hlen => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, _⟩
    simp [hb] at hlen
  | x₁ :: xs₁, x₂ :: xs₂, a, b, ys₁, ys₂, heq, ha, hb, hlen => by
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, htail⟩
    have hlen' : (xs₁.filter p).length = (xs₂.filter p).length := by
      cases hx : p x₁ <;> simp [hx] at hlen <;> omega
    obtain ⟨rfl, rfl, rfl⟩ := eq_of_append_cons_filter htail ha hb hlen'
    exact ⟨rfl, rfl, rfl⟩

private theorem snoc_inj {α : Type} {xs ys : List α} {x y : α}
    (h : xs ++ [x] = ys ++ [y]) : xs = ys ∧ x = y := by
  have hlen : xs.length = ys.length := by
    have hl := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hl
    omega
  obtain ⟨rfl, hxy⟩ := List.append_inj h hlen
  exact ⟨rfl, List.singleton_injective hxy⟩

private theorem isNonInvisible_of_decryptMsgIdx {m : Step} {idx : Nat}
    (h : m.decryptMsgIdx? = some idx) : isNonInvisible m = true := by
  cases m <;> simp [Step.decryptMsgIdx?, isNonInvisible, Step.cls] at h ⊢

theorem not_readCollisionCli_of_acceptsViaCli {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {evs_pre : List CliEvent} {ev : RunEvent} {g g₁ : Ghost}
    {ss : List Step} {vis : List VisEntry} {ext : List _root_.DY.Bytes}
    {m : Step} {msgIdx : Nat} {t_acc : _root_.DY.Bytes}
    (hInv : XlateInvSpecB) (hr : ProtocolSetupWF r) (hS : SemReady interp r S)
    (hfit : SchedFits (callsOf evs_pre) who ok)
    (hex_pre : Explains interp r S g ss vis evs_pre)
    (hnrc_pre : ¬ ReadCollisionCli interp r S g ss evs_pre)
    (hext_kn : ∀ x ∈ ext, x.AttackerKnows (runTrace r ss))
    (hm_dec : m.decryptMsgIdx? = some msgIdx)
    (haddr : g₁.addr = g.addr)
    (hσ : ∀ i, i < (runTrace r ss).length → g₁.σ i = g.σ i)
    (hget_acc : (runTrace r (ss ++ ext.map Step.network)).getMessageSentAt msgIdx = some t_acc)
    (hncol_acc : ¬ RecvCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t_acc) :
    ¬ ReadCollisionCli interp r S g₁ (ss ++ ext.map Step.network ++ [m]) (evs_pre ++ [.run ev]) := by
  rintro ⟨evs₁, ev₀, evs₂, ss₁, ss₂, m₀, vis_a, msgIdx₀, out₀, b₀, t₀,
    hevs_eq, hss_eq, hcmd₀, hexit₀, hbody₀, hme_a, hm₀_dec, hget₀, hcol₀⟩
  have hm_ni : isNonInvisible m = true := isNonInvisible_of_decryptMsgIdx hm_dec
  have hm₀_ni : isNonInvisible m₀ = true := isNonInvisible_of_decryptMsgIdx hm₀_dec
  have hext_inv : ∀ x ∈ ext.map Step.network, x.cls = .invisible := by
    intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; rfl
  rcases List.eq_nil_or_concat evs₂ with rfl | ⟨evs₂', last, hlast⟩
  · obtain ⟨rfl, hev_eq⟩ := snoc_inj hevs_eq
    have hlen_filter : ((ss ++ ext.map Step.network).filter isNonInvisible).length =
        (ss₁.filter isNonInvisible).length := by
      rw [List.filter_append, filter_nonInvisible_eq_nil hext_inv, List.append_nil,
        matchesEvents_filter_nonInvisible_length hex_pre.2.2.2,
        matchesEvents_filter_nonInvisible_length hme_a]
    obtain ⟨hss₁_eq, rfl, _⟩ := eq_of_append_cons_filter hss_eq hm_ni hm₀_ni hlen_filter
    subst hss₁_eq
    cases Option.some.inj (hm_dec.symm.trans hm₀_dec)
    cases Option.some.inj (hget_acc.symm.trans hget₀)
    have hme_ext : MatchesEvents interp r S g (setupTrace r) (ss ++ ext.map Step.network)
        evs_pre vis := matchesEvents_append_invisible hex_pre.2.2.2 hext_inv
    have hvis_eq : vis_a = vis := matchesEvents_vis_unique hme_a hme_ext
    rw [hvis_eq] at hcol₀
    have hcol_ss := recvCollisionOn_of_append_network hcol₀
    rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append] at hget_acc
    have ht_src : (∃ k, (runTrace r ss).getMessageSentAt k = some t_acc) ∨
        t_acc.AttackerKnows (runTrace r ss) :=
      (getMessageSentAt_runSteps_network ext hget_acc).imp id (hext_kn t_acc)
    exact hncol_acc (recvCollisionOn_transfer_via_xlate hInv hr hS hfit hex_pre hnrc_pre
      haddr hσ (Nat.le_refl _) ht_src hcol_ss)
  · rw [List.concat_eq_append] at hlast
    subst hlast
    have hevs_assoc : evs₁ ++ .run ev₀ :: (evs₂' ++ [last]) =
        (evs₁ ++ .run ev₀ :: evs₂') ++ [last] := by simp [List.append_assoc]
    rw [hevs_assoc] at hevs_eq
    obtain ⟨hevs_pre, _⟩ := snoc_inj hevs_eq
    subst hevs_pre
    obtain ⟨ss_a, ss_b, vis₁', vis₂', rfl, rfl, hme₁', hme₂'⟩ :=
      matchesEvents_restrict_tail (.run ev₀ :: evs₂') evs₁ hex_pre.2.2.2
    generalize hE : CliEvent.run ev₀ :: evs₂' = E at hme₂'
    cases hme₂' with
    | nil _ => cases hE
    | env _ _ _ => cases hE
    | run0 _ hrej _ =>
      injection hE with hev _
      injection hev with hev'
      subst hev'
      exact hrej out₀ hexit₀
    | @run1 _ _ pre₀ s₀ ss_c _ _ v₀ vs₀ hpre₀ hrm₀ _ =>
      injection hE with hev _
      injection hev with hev'
      subst hev'
      have hs₀_ni : isNonInvisible s₀ = true := by
        simp [isNonInvisible, hrm₀.1]
      let ss_cut := ss_a ++ pre₀
      have hss_split : ss_a ++ (pre₀ ++ s₀ :: ss_c) = ss_cut ++ s₀ :: ss_c := by
        simp [ss_cut, List.append_assoc]
      have hme_cut : MatchesEvents interp r S g (setupTrace r) ss_cut evs₁ vis₁' :=
        matchesEvents_append_invisible hme₁' hpre₀
      have hss_eq' : ss_cut ++ s₀ :: (ss_c ++ ext.map Step.network ++ [m]) = ss₁ ++ m₀ :: ss₂ := by
        simpa [ss_cut, List.append_assoc] using hss_eq
      have hlen_filter : (ss_cut.filter isNonInvisible).length =
          (ss₁.filter isNonInvisible).length := by
        rw [matchesEvents_filter_nonInvisible_length hme_cut,
          matchesEvents_filter_nonInvisible_length hme_a]
      obtain ⟨hcut_eq, rfl, _⟩ := eq_of_append_cons_filter hss_eq' hs₀_ni hm₀_ni hlen_filter
      subst hcut_eq
      have hvis_eq : vis_a = vis₁' := matchesEvents_vis_unique hme_a hme_cut
      rw [hvis_eq] at hcol₀
      have hex_cut : Explains interp r S g ss_cut vis₁' evs₁ :=
        ⟨hex_pre.1, Symbolic.Proofs.Swarm.UA.Base.ghostWF_of_append hex_pre.2.1,
          Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append (hss_split ▸ hex_pre.2.2.1),
          hme_cut⟩
      have hnrc_cut : ¬ ReadCollisionCli interp r S g ss_cut evs₁ := fun hrc_cut =>
        hnrc_pre (hss_split ▸ Symbolic.Proofs.Swarm.UA.BI.RAB.Base.readCollisionCli_append
          (s₀ :: ss_c) (.run ev₀ :: evs₂') hrc_cut)
      have hfit_cut : SchedFits (callsOf evs₁) who ok := by
        rw [callsOf_append] at hfit; exact schedFits_of_append hfit
      have hlen_cut : (runTrace r ss_cut).length ≤ (runTrace r (ss_a ++ (pre₀ ++ s₀ :: ss_c))).length := by
        rw [hss_split, Symbolic.Proofs.Swarm.UA.Base.runTrace_append r ss_cut (s₀ :: ss_c)]
        exact _root_.DY.Trace.length_le _ _ (runSteps_le (s₀ :: ss_c) (runTrace r ss_cut))
      have hcol_g := recvCollisionOn_transfer_via_xlate hInv hr hS hfit_cut hex_cut hnrc_cut
        haddr hσ hlen_cut (Or.inl ⟨msgIdx₀, hget₀⟩) hcol₀
      exact hnrc_pre ⟨evs₁, ev₀, evs₂', ss_cut, ss_c, s₀, vis₁', msgIdx₀, out₀, b₀, t₀,
        rfl, hss_split, hcmd₀, hexit₀, hbody₀, hme_cut, hm₀_dec, hget₀, hcol_g⟩

/-! ## Step-to-Move and Quiet-Failure Bridges -/

def ValidLoadStep : Step → Prop
  | .network .. | .aliceStart .. | .bobStart ..
  | .messageEncrypt .. | .messageEncryptAbort ..
  | .messageDecrypt .. | .messageDecryptSkipped ..
  | .exposeKey .. | .exposeSpqr .. | .exposeSkipped ..
  | .compromiseIK .. | .compromiseSPK .. | .compromisePQSPK .. | .compromiseOPK .. => True
  | _ => False

def stepToLoadMove : Step → _root_.DY.Libsignal.Composed.Refinement.Move
  | .network msg => .attackerSend msg
  | .aliceStart a b i j h => .aliceStart a b i j h 0
  | .bobStart b a kh j mh p s => .bobStart b a kh j mh p s 0
  | .messageEncrypt me st c pq => .encrypt me st c pq none
  | .messageEncryptAbort me st => .encryptAbort me st
  | .messageDecrypt me st m pq s => .decrypt me st m pq s false
  | .messageDecryptSkipped me st m sk pq s => .decryptSkipped me st m sk pq s false
  | .exposeKey me st k => .exposeKey me st k
  | .exposeSpqr me st => .exposeSpqr me st
  | .exposeSkipped sk => .exposeSkipped sk
  | .compromiseIK p st => .compromiseIK p st
  | .compromiseSPK b st => .compromiseSPK b st
  | .compromisePQSPK b st => .compromisePQSPK b st
  | .compromiseOPK b st => .compromiseOPK b st
  | _ => .reject []

theorem run_bind_pure_unit_isSome {α : Type} (m : Traceful α) (tr : ExecTrace) :
    ((m >>= fun _ => pure () : Traceful Unit).run tr).1.isSome = (m.run tr).1.isSome := by
  rw [_root_.DY.Traceful.run_bind]
  rcases m.run tr with ⟨_ | a, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem run_bind_pure_unit_snd {α : Type} (m : Traceful α) (tr : ExecTrace) :
    ((m >>= fun _ => pure () : Traceful Unit).run tr).2.val = (m.run tr).2.val := by
  rw [_root_.DY.Traceful.run_bind]
  rcases m.run tr with ⟨_ | a, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem stepToLoadMove_next {s : Step} (hv : ValidLoadStep s) (tr : ExecTrace) :
    (stepToLoadMove s).next tr = s.next tr := by
  cases s <;> try exact False.elim hv
  all_goals
    simp only [stepToLoadMove, _root_.DY.Libsignal.Composed.Refinement.Move.next,
      _root_.DY.Libsignal.Composed.Refinement.Move.act, Step.next, Step.toInput,
      _root_.DY.Libsignal.Composed.Refinement.stepIn]
    try exact run_bind_pure_unit_snd _ tr

theorem stepToLoadMove_ok {s : Step} {p : Participant} {k : Nat} {b : Bool}
    (hload : s.stateLoad? = some (p, k, b)) (tr : ExecTrace) :
    (((stepToLoadMove s).act.run tr).1.isSome = true) ↔ (s.ok tr = true) := by
  cases s <;> simp [Step.stateLoad?] at hload
  all_goals
    simp only [stepToLoadMove, _root_.DY.Libsignal.Composed.Refinement.Move.act, Step.ok,
      Step.toInput, _root_.DY.Libsignal.Composed.Refinement.stepIn]
    rw [run_bind_pure_unit_isSome]
    rfl

theorem recvRepresentations_eq_of_trace {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List _root_.DY.Libsignal.Composed.Refinement.Move}
    {tr : ExecTrace} {b : HwBytes}
    (htr : _root_.DY.Libsignal.Composed.Refinement.runTraceMoves r ms = tr) :
    _root_.DY.Libsignal.Composed.Refinement.recvRepresentations interp r S g ms b =
      recvRepresentationsOn interp S g tr b := by
  unfold _root_.DY.Libsignal.Composed.Refinement.recvRepresentations recvRepresentationsOn
  rw [htr]

theorem knownBaseKey_iff_of_trace {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List _root_.DY.Libsignal.Composed.Refinement.Move}
    {tr : ExecTrace} {q : PreKeyFields}
    (htr : _root_.DY.Libsignal.Composed.Refinement.runTraceMoves r ms = tr) :
    _root_.DY.Libsignal.Composed.Refinement.KnownBaseKey interp r S g ms q ↔
      KnownBaseKeyOn interp S g tr q := by
  unfold _root_.DY.Libsignal.Composed.Refinement.KnownBaseKey KnownBaseKeyOn
  rw [htr]

theorem reselectCollision_iff_of_terms {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List _root_.DY.Libsignal.Composed.Refinement.Move}
    {tr : ExecTrace} {vis : List VisEntry} {salts : List _root_.DY.Bytes} {t : _root_.DY.Bytes}
    (htr : _root_.DY.Libsignal.Composed.Refinement.runTraceMoves r ms = tr)
    (hsalts : _root_.DY.Libsignal.Composed.Refinement.honestSalts r ms = salts)
    (hpfx : prefixTerms r tr (_root_.DY.Libsignal.Composed.Refinement.runVis r ms) =
      prefixTerms r tr vis)
    (hpt : plaintextTerms (_root_.DY.Libsignal.Composed.Refinement.runVis r ms) = plaintextTerms vis) :
    _root_.DY.Libsignal.Composed.Refinement.ReselectCollision interp r S g ms t ↔
      ReselectCollisionOn interp r S g tr vis salts t := by
  unfold _root_.DY.Libsignal.Composed.Refinement.ReselectCollision ReselectCollisionOn
  dsimp only
  simp only [htr, recvRepresentations_eq_of_trace htr,
    recvCollision_iff_of_terms htr hsalts hpfx hpt]

theorem runMoves_append_eq :
    ∀ (ms₁ ms₂ : List _root_.DY.Libsignal.Composed.Refinement.Move) (tr : ExecTrace),
      _root_.DY.Libsignal.Composed.Refinement.runMoves (ms₁ ++ ms₂) tr =
        let (tr₁, v₁) := _root_.DY.Libsignal.Composed.Refinement.runMoves ms₁ tr
        let (tr₂, v₂) := _root_.DY.Libsignal.Composed.Refinement.runMoves ms₂ tr₁
        (tr₂, v₁ ++ v₂)
  | [], _, _ => by simp [_root_.DY.Libsignal.Composed.Refinement.runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, _root_.DY.Libsignal.Composed.Refinement.runMoves,
      runMoves_append_eq ms₁ ms₂ (m.next tr), List.append_assoc]

theorem runMoves_attackerSend_map :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      _root_.DY.Libsignal.Composed.Refinement.runMoves
        (ext.map _root_.DY.Libsignal.Composed.Refinement.Move.attackerSend) tr =
        (runSteps (ext.map Step.network) tr, [])
  | [], _ => rfl
  | x :: ext, tr => by
    have hnext : (_root_.DY.Libsignal.Composed.Refinement.Move.attackerSend x).next tr =
        (Step.network x).next tr :=
      stepToLoadMove_next (s := .network x) trivial tr
    have hvis : (_root_.DY.Libsignal.Composed.Refinement.Move.attackerSend x).vis tr = [] :=
      Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind
        (m := _root_.DY.Libsignal.Composed.Refinement.Move.attackerSend x) (tr := tr) rfl
        (by intro h; cases h)
    simp only [List.map_cons, _root_.DY.Libsignal.Composed.Refinement.runMoves, runSteps,
      hnext, hvis, List.nil_append, runMoves_attackerSend_map ext ((Step.network x).next tr)]

theorem forall₂_append_eq_length_inv {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β},
      xs₁.length = ys₁.length →
      List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) →
      List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | _ :: _, _, [], _, hlen, _ => by simp at hlen
  | [], _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: xs₁, xs₂, _ :: ys₁, ys₂, hlen, .cons hr hrest => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    obtain ⟨h₁, h₂⟩ := forall₂_append_eq_length_inv hlen hrest
    exact ⟨.cons hr h₁, h₂⟩

theorem randTerm_inj_of_ne_zero {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {i₁ n₁ i₂ n₂ : Nat} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (h : _root_.DY.Libsignal.Composed.Refinement.randTerm i₁ n₁ =
      _root_.DY.Libsignal.Composed.Refinement.randTerm i₂ n₂) : i₁ = i₂ ∧ n₁ = n₂ := by
  let g_test : Ghost :=
    { σ := fun i n => if i = i₁ ∧ n = n₁ then [0#8] else [], addr := fun _ => [] }
  have h1 := Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.gamma_randTerm_eq interp S g_test i₁ n₁ hn₁
  have h2 := Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.gamma_randTerm_eq interp S g_test i₂ n₂ hn₂
  rw [h, h2] at h1
  dsimp only [g_test] at h1
  simp only [and_self, ↓reduceIte] at h1
  split at h1
  · rename_i heq₂
    exact ⟨heq₂.1.symm, heq₂.2.symm⟩
  · simp at h1

def NoTREvFrom (n : Nat) (t : ExecTrace) : Prop :=
  ∀ i, n ≤ i →
    ((t.at? i : Option (_root_.DY.ProtocolEvent.ExecEntryT
      _root_.DY.Libsignal.TripleRatchet.TREvent)) = none)

private theorem noTREvFrom_trans {n : Nat} {t₁ t₂ : ExecTrace}
    (h₁₂ : t₁ ≤ t₂) (h₁ : NoTREvFrom n t₁) (h₂ : NoTREvFrom t₁.length t₂) :
    NoTREvFrom n t₂ := by
  intro i hi
  by_cases hlt : i < t₁.length
  · rw [Symbolic.Swarm.CREF.XplSteps.xat?_le_eq h₁₂ hlt]
    exact h₁ i hi
  · exact h₂ i (Nat.le_of_not_lt hlt)

def QuietOnNone {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, (x.run tr).1 = none → NoTREvFrom tr.length (x.run tr).2.val

private theorem quietOnNone_failure {α : Type} : QuietOnNone (failure : Traceful α) := by
  intro tr _ i hi
  rw [_root_.DY.Traceful.run_failure]
  exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi

private theorem quietOnNone_bind_xquiet {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hq : Symbolic.Swarm.CREF.XplSteps.XQuiet x) (hf : ∀ a, QuietOnNone (f a)) :
    QuietOnNone (x >>= f) := by
  intro tr hnone
  have hqx : NoTREvFrom tr.length (x.run tr).2.val := fun i hi => (hq tr i hi).2.2.1
  rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd]
  rw [_root_.DY.Traceful.run_bind] at hnone
  rcases hx : x.run tr with ⟨_ | a, tr₁⟩
  · rw [hx] at hqx; exact hqx
  · rw [hx] at hnone hqx
    dsimp only at hnone hqx ⊢
    have hnone_f : ((f a).run tr₁.val).1 = none := by
      rcases hfa : (f a).run tr₁.val with ⟨_ | b, _⟩
      · rfl
      · rw [hfa] at hnone; cases hnone
    exact noTREvFrom_trans ((f a).run tr₁.val).2.property hqx (hf a tr₁.val hnone_f)

private theorem logSkippedKeys_isSome (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo)
    (rk : _root_.DY.Bytes) (rIdx stateIdx : Nat) (ck : _root_.DY.Bytes) (idx : UInt32)
    (n : Nat) (tr : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s rk rIdx stateIdx ck idx n).run tr).1.isSome =
      true := by
  rw [(Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeys_run s rk rIdx stateIdx ck idx n tr).1]
  rfl

private theorem logMessageKeyAndStore_isSome (me : Participant)
    (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : _root_.DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : _root_.DY.Bytes) (cnt : UInt32) (rIdx parentIdx : Nat)
    (st : TRState) (tr : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt cnt
      rIdx parentIdx st).run tr).1.isSome = true := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  rw [_root_.DY.Traceful.run_bind, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_bind,
    _root_.DY.Traceful.run_mk]
  dsimp only
  rw [_root_.DY.Traceful.run_pure]
  dsimp only
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_mk]
  rfl

private theorem quietOnNone_of_always_some {α : Type} {x : Traceful α}
    (hs : ∀ tr, (x.run tr).1.isSome = true) : QuietOnNone x := by
  intro tr hnone
  have h := hs tr
  rw [hnone] at h
  cases h

private theorem quietOnNone_bind_some {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : ∀ tr, (x.run tr).1.isSome = true)
    (hf : ∀ a tr, ((f a).run tr).1.isSome = true) :
    ∀ tr, ((x >>= f).run tr).1.isSome = true := by
  intro tr
  rw [_root_.DY.Traceful.run_bind]
  rcases hxr : x.run tr with ⟨_ | a, tr₁⟩
  · have h := hx tr; rw [hxr] at h; cases h
  · have h := hf a tr₁.val
    rcases (f a).run tr₁.val with ⟨_ | b, _⟩ <;> simp_all

theorem quietOnNone_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    QuietOnNone (_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine quietOnNone_bind_xquiet
    (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
      (Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx)) fun st => ?_
  refine quietOnNone_bind_xquiet
    (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg msgIdx) fun msg => ?_
  refine quietOnNone_bind_xquiet
    (Symbolic.Swarm.CREF.XplSteps.xquiet_ensureReceiverChain st msg.ratchetKey) fun x => ?_
  rcases x with ⟨st₁, c, ratcheted⟩
  dsimp only
  rcases _root_.DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact quietOnNone_failure
  · dsimp only
    rcases _root_.DY.Spqr.spqrRecv st₁.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact quietOnNone_failure
    · dsimp only
      refine quietOnNone_bind_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage key) fun _ => ?_
      refine quietOnNone_bind_xquiet
        (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
          (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx)) fun pqSalt => ?_
      refine quietOnNone_bind_xquiet
        (Symbolic.Swarm.CREF.XplSteps.xquiet_verifyMacAndDecrypt st₁ msg pqSalt seed) fun m => ?_
      have hlog : ∀ (ev : _root_.DY.Libsignal.TripleRatchet.TREvent) (tr : ExecTrace),
          ((_root_.DY.ProtocolEvent.logEvent ev).run tr).1.isSome = true := fun ev tr => by
        rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_bind,
          _root_.DY.Traceful.run_mk]
        dsimp only
        rw [_root_.DY.Traceful.run_pure]
        rfl
      cases ratcheted
      · exact quietOnNone_of_always_some
          (quietOnNone_bind_some (logSkippedKeys_isSome _ _ _ _ _ _ _) fun _ =>
            quietOnNone_bind_some (hlog _) fun _ =>
            logMessageKeyAndStore_isSome _ _ _ _ _ _ _ _ _)
      · exact quietOnNone_of_always_some
          (quietOnNone_bind_some (hlog _) fun _ =>
            quietOnNone_bind_some (hlog _) fun _ =>
            quietOnNone_bind_some (logSkippedKeys_isSome _ _ _ _ _ _ _) fun _ =>
            quietOnNone_bind_some (hlog _) fun _ =>
            logMessageKeyAndStore_isSome _ _ _ _ _ _ _ _ _)

theorem quietOnNone_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    QuietOnNone (_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
      me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) := by
  unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine quietOnNone_bind_xquiet
    (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
      (Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx)) fun st => ?_
  refine quietOnNone_bind_xquiet
    (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg msgIdx) fun msg => ?_
  refine quietOnNone_bind_xquiet
    (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
      (Symbolic.Swarm.CREF.XplSteps.xfix_getEntry skIdx)) fun e => ?_
  cases e.ev with
  | SkippedKeyStored s pk n seed rIdx srcIdx =>
    dsimp only
    refine quietOnNone_bind_xquiet
      (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_guard _)) fun _ => ?_
    refine quietOnNone_bind_xquiet
      (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _)) fun _ => ?_
    rcases _root_.DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact quietOnNone_failure
    · dsimp only
      refine quietOnNone_bind_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage key) fun _ => ?_
      refine quietOnNone_bind_xquiet
        (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
          (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx)) fun pqSalt => ?_
      refine quietOnNone_bind_xquiet
        (Symbolic.Swarm.CREF.XplSteps.xquiet_verifyMacAndDecrypt st msg pqSalt seed) fun m => ?_
      have hlog : ∀ (ev : _root_.DY.Libsignal.TripleRatchet.TREvent) (tr : ExecTrace),
          ((_root_.DY.ProtocolEvent.logEvent ev).run tr).1.isSome = true := fun ev tr => by
        rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_bind,
          _root_.DY.Traceful.run_mk]
        dsimp only
        rw [_root_.DY.Traceful.run_pure]
        rfl
      apply quietOnNone_of_always_some
      exact quietOnNone_bind_some (hlog _) fun _ =>
        quietOnNone_bind_some (hlog _) fun _ =>
        logMessageKeyAndStore_isSome _ _ _ _ _ _ _ _ _
  | _ => exact quietOnNone_failure

theorem receivedPlaintext_eq_none_of_xquietFrom {tr t : ExecTrace}
    (hq : NoTREvFrom tr.length t) :
    _root_.DY.Libsignal.Composed.Refinement.receivedPlaintext tr t = none := by
  unfold _root_.DY.Libsignal.Composed.Refinement.receivedPlaintext
  rw [List.findSome?_eq_none_iff]
  intro i hi
  obtain ⟨hlo, _⟩ := List.mem_range'_1.mp hi
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [hq i hlo]

theorem bobDoneBaseKeys_runSteps_network :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      _root_.DY.Libsignal.Composed.Refinement.bobDoneBaseKeys (runSteps (ext.map Step.network) tr) =
        _root_.DY.Libsignal.Composed.Refinement.bobDoneBaseKeys tr
  | [], _ => rfl
  | x :: ext, tr => by
    simp only [List.map_cons, runSteps, network_next_eq_append, bobDoneBaseKeys_runSteps_network ext]
    exact Symbolic.Swarm.CREF.bobDoneBaseKeys_append_network tr x

theorem attackerKnows_runSteps_network :
    ∀ (ext : List _root_.DY.Bytes) {tr : ExecTrace} {u : _root_.DY.Bytes},
      (∀ x ∈ ext, x.AttackerKnows tr) →
      u.AttackerKnows tr →
      u.AttackerKnows (runSteps (ext.map Step.network) tr)
  | [], _, _, _, hu => hu
  | x :: ext, _, _, hext, hu => by
    simp only [List.map_cons, runSteps, network_next_eq_append]
    have hx : x.AttackerKnows _ := hext x (.head _)
    refine attackerKnows_runSteps_network ext (fun y hy => ?_) ?_
    · exact (Symbolic.Swarm.CREF.attackerKnows_append_net_iff hx _).mpr (hext y (.tail _ hy))
    · exact (Symbolic.Swarm.CREF.attackerKnows_append_net_iff hx _).mpr hu

theorem stepsWF_network_map :
    ∀ (ext : List _root_.DY.Bytes) {tr : ExecTrace},
      (∀ x ∈ ext, x.AttackerKnows tr) →
      _root_.DY.Libsignal.Composed.Refinement.StepsWF (ext.map Step.network) tr
  | [], _, _ => trivial
  | x :: ext, _, hext => by
    have hx : x.AttackerKnows _ := hext x (.head _)
    refine ⟨hx, trivial, stepsWF_network_map ext fun y hy => ?_⟩
    rw [network_next_eq_append]
    exact (Symbolic.Swarm.CREF.attackerKnows_append_net_iff hx _).mpr (hext y (.tail _ hy))

theorem mid_accept_take_inv {coins out pt' : HwBytes} {mid : List MachineEvent} {k : Nat}
    (hmid : mid = [] ∨ mid = [MachineEvent.rng coins])
    (hk : (mid ++ [MachineEvent.accept out])[k]? = some (MachineEvent.accept pt'))
    (hrng : ((mid ++ [MachineEvent.accept out]).take k).all
      (fun ev => _root_.DY.Libsignal.Composed.Refinement.eventKind ev ==
        _root_.DY.Libsignal.Composed.Refinement.VisEventKind.rng) = true) :
    pt' = out ∧ (mid ++ [MachineEvent.accept out]).take (k + 1) = mid ++ [MachineEvent.accept out] := by
  rcases hmid with rfl | rfl
  · rcases k with _ | k
    · simp only [List.nil_append, List.getElem?_cons_zero, Option.some.injEq,
        MachineEvent.accept.injEq] at hk
      exact ⟨hk.symm, rfl⟩
    · simp at hk
  · rcases k with _ | _ | k
    · simp at hk
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq, MachineEvent.accept.injEq] at hk
      exact ⟨hk.symm, rfl⟩
    · simp at hk

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hhd _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self, hhd⟩
    · obtain ⟨y, hy, hry⟩ := ih hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

end Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkPromAux
