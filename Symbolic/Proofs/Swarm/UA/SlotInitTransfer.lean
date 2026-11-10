/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Monad
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredClassical
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.CREF.CBadG2.MacGuess
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReach
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReachBob
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Step-Level Trace, Stamp, and `CBadSigmaFrame` Transfer

Provides `Step`-level reachability and `MatchesEventsClassical` snoc/inversion lemmas, together
with `StampsLt` bounds for `stepView` and `CBadSigmaFrame` transfer of `GhostWF`,
`MatchesEventsClassical`, `RecvCollisionOn`, and `¬ ReadCollisionCliClassical`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.SlotInitTransfer

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCliClassical)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent BobKeyHandles)
open _root_.DY.Libsignal.TripleRatchet (parseTrSignalMsg trMsgKeys computeMac)
open Symbolic.Swarm.CREF (RoleStE CBadSigmaFrame CBadGammaAgree
  cBadSigmaFrame_updateFreshAt cbadG2_gammaAgree_of_sigmaFrame cbadG2_gamma_eq
  cbadG2_stampsLt_getMessageSentAt_of_entries cbadG2_getMessageSentAt_le
  g2b_bobDoneEk_stampsLt_of_reachable cbadG2_memoCollisionOn_iff
  cbadG2_stampsLt_prefixTerms cbadG2_stateStampsLt_availableStates
  cbadG2_stampsLt_skippedLogged_of_entries cbadG2_stampsLt_whisperTrials cbadG2_stampsLt_saltTerms
  stampsLt_wire_of_computeMac TR.setupTrace_reachable
  TR.FreshSigma.StampsLt TR.FreshSigma.VisStampsLt TR.FreshSigma.TraceEntriesLt
  TR.FreshSigma.PQStEntry TR.FreshSigma.updateFreshAt TR.FreshSigma.updateFreshAt_self
  TR.FreshSigma.traceEntriesLt_knows TR.FreshSigma.traceEntriesLt_at?_pqst
  TR.FreshSigma.stampsLt_dhPk_pack TR.FreshSigma.visStampsLt_of_terms
  TR.FreshSigma.visStampsLt_of_mem_aliceDraws TR.FreshSigma.stampsLt_of_mem_newRandoms
  TR.FreshSigma.stampsLt_of_receivedPlaintext TR.FreshSigma.visStampsLt_of_mem_encDraws
  TR.FreshSigma.stampsLt_of_mem_sessionBaseKeys TR.FreshSigma.stampsLt_parseTrSignalMsg
  TR.FreshSigma.traceEntriesLt_of_reachable TR.FreshSigma.stampsLt_zeroKey
  TR.FreshSigma.stampsLt_trMsgKeys TR.FreshSigma.stampsLt_computeMac
  Stage1Trials.whisperTrials_congr_gamma Stage1Trials.MacTagForgeryOrCollision.congr_gamma)
open Symbolic.Swarm.CREF.CliPure (cbadG2_bundleMatches_transfer cbadG2_sendMatches_transfer
  cbadG2_preKeyRecvOpkMatches_transfer cbadG2_preKeyRecvMatches_transfer)
open Symbolic.Proofs.Swarm.UA.Base (runSteps_append stepBundleIds_run_of_runMatches stepBundleIds_run_of_runRejected)

/-! ## `Step` Trace, Reachability, and `MatchesEventsClassical` Helpers -/

theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => _root_.DY.Trace.le_refl tr
  | s :: ss, tr => _root_.DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

theorem step_next_reachable {s : Step} {tr : ExecTrace}
    (hreach : tr.Reachable reachability) (hpre : s.PreCond tr) :
    (s.next tr).Reachable reachability :=
  .Step s.toInput hpre hreach

theorem runSteps_reachable :
    ∀ (ss : List Step) {tr : ExecTrace},
      tr.Reachable reachability → StepsWF ss tr → (runSteps ss tr).Reachable reachability
  | [], _, hreach, _ => hreach
  | _ :: ss, _, hreach, ⟨hpre, _, hwf⟩ =>
    runSteps_reachable ss (step_next_reachable hreach hpre) hwf

theorem stepsWF_append_iff :
    ∀ (xs ys : List Step) (tr : ExecTrace),
      StepsWF (xs ++ ys) tr ↔ StepsWF xs tr ∧ StepsWF ys (runSteps xs tr)
  | [], _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | s :: xs, ys, tr => by
    simp only [List.cons_append, StepsWF, runSteps, stepsWF_append_iff xs ys (s.next tr),
      and_assoc]

theorem stepsStateFaithful_append_noLoad {r : ProtocolSetup} {ss δ : List Step}
    (h : StepsStateFaithful r ss) (hδ : ∀ s ∈ δ, s.stateLoad? = none) :
    StepsStateFaithful r (ss ++ δ) := by
  intro i j si sj p k b hij hsi hsj hli hok hlj
  have hi_lt : i < ss.length := by
    by_contra hge
    have hge' : ss.length ≤ i := Nat.le_of_not_lt hge
    rw [List.getElem?_append_right hge'] at hsi
    have hmem : si ∈ δ := List.mem_of_getElem? hsi
    rw [hδ si hmem] at hli
    cases hli
  have hj_lt : j < ss.length := by
    by_contra hge
    have hge' : ss.length ≤ j := Nat.le_of_not_lt hge
    rw [List.getElem?_append_right hge'] at hsj
    have hmem : sj ∈ δ := List.mem_of_getElem? hsj
    rw [hδ sj hmem] at hlj
    cases hlj
  rw [List.getElem?_append_left hi_lt] at hsi
  rw [List.getElem?_append_left hj_lt] at hsj
  rw [List.take_append_of_le_length (Nat.le_of_lt hi_lt)] at hok
  exact h i j si sj p k b hij hsi hsj hli hok hlj

theorem matchesEventsAt_snoc_run1 {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss pre : List Step} {s : Step}
    {evs : List CliEvent} {ev : RunEvent} {vis v : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis)
    (hpre : ∀ x ∈ pre, x.cls = .invisible)
    (hrm : RunMatches interp r S g (runSteps pre (runSteps ss tr)) s ev v (evs.foldl stepBundleIds initIds)) :
    MatchesEventsClassicalAt interp r S g initIds tr (ss ++ pre ++ [s]) (evs ++ [.run ev]) (vis ++ v) := by
  induction hme with
  | @nil initIds tr ss₀ hinv =>
    have hpre' : ∀ x ∈ ss₀ ++ pre, x.cls = .invisible := by
      intro x hx
      rcases List.mem_append.mp hx with hx₀ | hx₁
      · exact hinv x hx₀
      · exact hpre x hx₁
    have hrm' : RunMatches interp r S g (runSteps (ss₀ ++ pre) tr) s ev v initIds := by
      simpa only [runSteps_append, List.foldl_nil] using hrm
    have h0 : MatchesEventsClassicalAt interp r S g initIds tr ((ss₀ ++ pre) ++ s :: []) [.run ev] (v ++ []) :=
      .run1 hpre' hrm' (.nil (by simp))
    simpa [List.append_assoc] using h0
  | @run1 initIds tr pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hrm₀ _ ih =>
    have hrm' : RunMatches interp r S g
        (runSteps pre (runSteps ss' (s₀.next (runSteps pre₀ tr)))) s ev v
        (evs'.foldl stepBundleIds (nextBundleIds initIds ev₀)) := by
      simpa only [runSteps_append, runSteps, List.foldl_cons, stepBundleIds_run_of_runMatches hrm₀] using hrm
    have ih' := ih hrm'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsClassicalAt.run1 hpre₀ hrm₀ ih'
  | @run0 initIds tr pre₀ ss' ev₀ evs' vs' hpre₀ hrej₀ _ ih =>
    have hrm' : RunMatches interp r S g
        (runSteps pre (runSteps ss' (runSteps pre₀ tr))) s ev v
        (evs'.foldl stepBundleIds initIds) := by
      simpa only [runSteps_append, List.foldl_cons, stepBundleIds_run_of_runRejected hrej₀] using hrm
    have ih' := ih hrm'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsClassicalAt.run0 hpre₀ hrej₀ ih'
  | @env initIds tr pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hem₀ _ ih =>
    have hrm' : RunMatches interp r S g
        (runSteps pre (runSteps ss' (s₀.next (runSteps pre₀ tr)))) s ev v
        (evs'.foldl stepBundleIds initIds) := by
      simpa only [runSteps_append, runSteps, List.foldl_cons, stepBundleIds] using hrm
    have ih' := ih hrm'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsClassicalAt.env hpre₀ hem₀ ih'

theorem matchesEvents_snoc_run1 {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {ss pre : List Step} {s : Step}
    {evs : List CliEvent} {ev : RunEvent} {vis v : List VisEntry}
    (hme : MatchesEventsClassical interp r S g tr ss evs vis)
    (hpre : ∀ x ∈ pre, x.cls = .invisible)
    (hrm : RunMatches interp r S g (runSteps pre (runSteps ss tr)) s ev v (activeBundleIds evs)) :
    MatchesEventsClassical interp r S g tr (ss ++ pre ++ [s]) (evs ++ [.run ev]) (vis ++ v) :=
  matchesEventsAt_snoc_run1 hme hpre hrm

theorem matchesEventsAt_snoc_run_inv {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ev : RunEvent} (hnotRej : ¬ RunRejected ev) :
    ∀ (evs : List CliEvent) {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {vis : List VisEntry},
      MatchesEventsClassicalAt interp r S g initIds tr ss (evs ++ [.run ev]) vis →
      ∃ ss₁ pre s post vis₁ v,
        ss = ss₁ ++ pre ++ [s] ++ post ∧
        vis = vis₁ ++ v ∧
        MatchesEventsClassicalAt interp r S g initIds tr ss₁ evs vis₁ ∧
        (∀ x ∈ pre, x.cls = .invisible) ∧
        RunMatches interp r S g (runSteps pre (runSteps ss₁ tr)) s ev v (evs.foldl stepBundleIds initIds) ∧
        (∀ x ∈ post, x.cls = .invisible)
  | [], _, tr, ss, vis, hme => by
    simp only [List.nil_append] at hme
    generalize hE : ([CliEvent.run ev] : List CliEvent) = E at hme
    cases hme with
    | nil _ => cases hE
    | run0 _ hrej _ =>
      injection hE with hev _
      injection hev with hev'
      subst hev'
      exact absurd hrej hnotRej
    | env _ _ _ =>
      injection hE with hev _
      cases hev
    | @run1 _ _ pre s post ev₀ evs' v vs' hpre hrm hrest =>
      injection hE with hev hevs
      injection hev with hev'
      subst hev' hevs
      generalize hNil : ([] : List CliEvent) = E₀ at hrest
      cases hrest with
      | nil hpost =>
        exact ⟨[], pre, s, post, [], v, by simp, by simp, .nil (by simp), hpre, hrm, hpost⟩
      | run1 _ _ _ => cases hNil
      | run0 _ _ _ => cases hNil
      | env _ _ _ => cases hNil
  | e :: evs, _, tr, ss, vis, hme => by
    rw [List.cons_append] at hme
    generalize hE : e :: (evs ++ [CliEvent.run ev]) = E at hme
    cases hme with
    | nil _ => cases hE
    | @run1 _ _ pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hrm₀ hrest =>
      injection hE with he hevs
      subst he hevs
      obtain ⟨ss₁', pre, s, post, vis₁', v, rfl, rfl, hme₁, hpre, hrm, hpost⟩ :=
        matchesEventsAt_snoc_run_inv hnotRej evs hrest
      refine ⟨pre₀ ++ s₀ :: ss₁', pre, s, post, v₀ ++ vis₁', v, by simp, by simp,
        .run1 hpre₀ hrm₀ hme₁, hpre, ?_, hpost⟩
      simpa only [runSteps_append, runSteps, List.foldl_cons, stepBundleIds_run_of_runMatches hrm₀] using hrm
    | @run0 _ _ pre₀ ss' ev₀ evs' vs' hpre₀ hrej₀ hrest =>
      injection hE with he hevs
      subst he hevs
      obtain ⟨ss₁', pre, s, post, vis₁', v, rfl, rfl, hme₁, hpre, hrm, hpost⟩ :=
        matchesEventsAt_snoc_run_inv hnotRej evs hrest
      refine ⟨pre₀ ++ ss₁', pre, s, post, vis₁', v, by simp, rfl,
        .run0 hpre₀ hrej₀ hme₁, hpre, ?_, hpost⟩
      simpa only [runSteps_append, List.foldl_cons, stepBundleIds_run_of_runRejected hrej₀] using hrm
    | @env _ _ pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hem₀ hrest =>
      injection hE with he hevs
      subst he hevs
      obtain ⟨ss₁', pre, s, post, vis₁', v, rfl, rfl, hme₁, hpre, hrm, hpost⟩ :=
        matchesEventsAt_snoc_run_inv hnotRej evs hrest
      refine ⟨pre₀ ++ s₀ :: ss₁', pre, s, post, v₀ ++ vis₁', v, by simp, by simp,
        .env hpre₀ hem₀ hme₁, hpre, ?_, hpost⟩
      simpa only [runSteps_append, runSteps, List.foldl_cons, stepBundleIds] using hrm

theorem matchesEvents_snoc_run_inv {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ev : RunEvent} (hnotRej : ¬ RunRejected ev)
    (evs : List CliEvent) {tr : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (hme : MatchesEventsClassical interp r S g tr ss (evs ++ [.run ev]) vis) :
    ∃ ss₁ pre s post vis₁ v,
      ss = ss₁ ++ pre ++ [s] ++ post ∧
      vis = vis₁ ++ v ∧
      MatchesEventsClassical interp r S g tr ss₁ evs vis₁ ∧
      (∀ x ∈ pre, x.cls = .invisible) ∧
      RunMatches interp r S g (runSteps pre (runSteps ss₁ tr)) s ev v (activeBundleIds evs) ∧
      (∀ x ∈ post, x.cls = .invisible) :=
  matchesEventsAt_snoc_run_inv hnotRej evs hme

/-! ## `Step`-Level Stamps and `CBadSigmaFrame` Transfer -/

section UnsealedRand
unseal _root_.DY.Bytes

theorem gamma_randTerm_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (idx n : Nat) (hn : n ≠ 0) :
    gamma interp S g (randTerm idx n) = g.σ idx n := by
  unfold gamma gamma' randTerm
  rw [_root_.DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interp S g)]
  simp [concretizeRandom, node, hn]

end UnsealedRand

theorem lt_of_stampsLt_randTerm {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts i n : Nat} (hn : n ≠ 0) (h : TR.FreshSigma.StampsLt interp S g ts (randTerm i n)) :
    i < ts := by
  by_contra hge
  have hle : ts ≤ i := Nat.le_of_not_lt hge
  let g' : Ghost := { g with σ := TR.FreshSigma.updateFreshAt g.σ i n (0#8 :: g.σ i n) }
  have hfr : CBadSigmaFrame g g' ts := cBadSigmaFrame_updateFreshAt g hle n (0#8 :: g.σ i n)
  have heq := cbadG2_gamma_eq (cbadG2_gammaAgree_of_sigmaFrame interp S hfr) h
  rw [gamma_randTerm_eq interp S g' i n hn, gamma_randTerm_eq interp S g i n hn] at heq
  simp only [g', TR.FreshSigma.updateFreshAt_self] at heq
  have hlen := congrArg List.length heq
  simp at hlen

private theorem eventLoggedAt_of_getEventAt_pq {tr : ExecTrace} {d : Nat} {ev : PQXDHEvent}
    (h : tr.getEventAt PQXDHEvent d = some ev) : tr.EventLoggedAt ev d := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rcases hat : (tr.at? d : Option (_root_.DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with _ | ⟨ev'⟩
  · simp [hat] at h
  · simp [hat] at h
    subst h
    rfl

private theorem pendingPreKey_stampsLt {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr T : ExecTrace} (hReach : tr.Reachable reachability) (hle : tr ≤ T)
    (htr : TR.FreshSigma.TraceEntriesLt interp S g ts T)
    {stateIdx : Nat} {ek ct : _root_.DY.Bytes} (h : pendingPreKey tr stateIdx = some (ek, ct)) :
    TR.FreshSigma.StampsLt interp S g ts ek ∧ TR.FreshSigma.StampsLt interp S g ts ct := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at h
  rcases hls : (tr.at? stateIdx : Option RoleStE) with _ | e
  · simp [hls] at h
  · simp only [hls, Option.map_some] at h
    have hdec : sessionHasDecrypted tr (e.st.state.sessionInfo e.st.participant) stateIdx = false := by
      cases hx : sessionHasDecrypted tr (e.st.state.sessionInfo e.st.participant) stateIdx <;> simp_all
    simp only [hdec, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨pqev₀, hpq_mem, hi⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨i, _, hce_get⟩ := List.mem_filterMap.mp hpq_mem
    rcases hce : (tr.getEventAt ComposedEvent i) with _ | cev
    · simp [hce] at hce_get
    · simp only [hce] at hce_get
      cases cev with
      | HandshakeSession s d =>
        by_cases hs : s = e.st.state.sessionInfo e.st.participant
        · simp only [hs, ↓reduceIte] at hce_get
          rcases hpq : (tr.getEventAt PQXDHEvent d) with _ | pqev
          · simp [hpq] at hce_get
          · simp only [hpq, Option.some.injEq] at hce_get
            subst pqev₀
            cases pqev with
            | AliceDone a b ikA ikB spk pqpk opk ek' ct' keys =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hi
              rcases hi with ⟨rfl, rfl⟩
              have hLog := eventLoggedAt_of_getEventAt_pq hpq
              obtain ⟨t, _, rfl, hSlot, _⟩ :=
                (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr hReach).aliceDone
                  a b ikA ikB spk pqpk opk ek' ct' keys d hLog
              obtain ⟨_, _, _, a', b', ikA', ikB', spk', pqpk', opk', ek'', ct'', keys',
                hNetEk, hNetCt, hLog'⟩ := hSlot
              rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hLog hLog'
              have hEq : (some ⟨.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek'' ct'' keys'⟩ :
                  Option (_root_.DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
                  some ⟨.AliceDone a b ikA ikB spk pqpk opk ek' ct' keys⟩ :=
                hLog'.symm.trans hLog
              injection hEq with hEntry
              injection hEntry with hEvEq
              injection hEvEq with _ _ _ _ _ _ _ hEk hCt _
              subst hEk; subst hCt
              exact ⟨TR.FreshSigma.traceEntriesLt_knows htr
                  (_root_.DY.Bytes.AttackerKnows_le _ _ _ hle
                    (Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt.attackerKnows hNetEk)),
                TR.FreshSigma.traceEntriesLt_knows htr
                  (_root_.DY.Bytes.AttackerKnows_le _ _ _ hle
                    (Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt.attackerKnows hNetCt))⟩
            | _ => cases hi
        · simp [hs] at hce_get

private theorem bobOpkPk_stampsLt {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {b : Participant} {kh : BobKeyHandles}
    {tr T : ExecTrace} (hle : tr ≤ T) (htr : TR.FreshSigma.TraceEntriesLt interp S g ts T)
    {t : _root_.DY.Bytes} (ht : t ∈ (bobOpkPk b kh tr).toList) :
    TR.FreshSigma.StampsLt interp S g ts t := by
  have ht' : bobOpkPk b kh tr = some t := Option.mem_toList.mp ht
  unfold bobOpkPk at ht'
  rcases hop : kh.opk with _ | idx
  · simp [hop] at ht'
  · simp only [hop, Option.bind_some] at ht'
    rcases hgk : ((_root_.DY.Libsignal.PQXDH.getKey b idx .oneTimePrekey).run tr).1 with _ | sk
    · simp [hgk] at ht'
    · simp only [hgk, Option.map_some, Option.some.injEq] at ht'
      subst ht'
      have hst : Symbolic.Swarm.COMPOSED.CompTrace.PQXDHStoredAt tr b
          { kind := .oneTimePrekey, sk := sk } idx := by
        unfold _root_.DY.Libsignal.PQXDH.getKey at hgk
        rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
          Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_pq_fst,
          Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_pq_snd] at hgk
        rcases hat : (tr.at? idx : Option Symbolic.Swarm.COMPOSED.CompTrace.PQXDHStEntry)
          with _ | ⟨⟨p, k, sk'⟩⟩
        · simp [hat] at hgk
        · simp only [hat] at hgk
          by_cases hp : p = b
          · subst hp
            simp only [↓reduceIte] at hgk
            by_cases hk : k = .oneTimePrekey
            · subst hk
              simp only [_root_.guard, ↓reduceIte, Symbolic.DYBridge.DY.Traceful.run_eq_1] at hgk
              change some sk' = some sk at hgk
              injection hgk with hsk_eq
              subst hsk_eq
              exact hat
            · simp only [_root_.guard, hk, ↓reduceIte, Symbolic.DYBridge.DY.Traceful.run_eq_1] at hgk
              cases hgk
          · simp [hp] at hgk
      have hatT : (T.at? idx : Option TR.FreshSigma.PQStEntry) =
          some ⟨⟨b, { kind := .oneTimePrekey, sk := sk }⟩⟩ := by
        have h1 := _root_.DY.Trace.at?_le (EntryT := TR.FreshSigma.PQStEntry) tr T idx hle
        rwa [hst] at h1
      have hsk : TR.FreshSigma.StampsLt interp S g ts sk :=
        TR.FreshSigma.traceEntriesLt_at?_pqst htr hatT
      exact (TR.FreshSigma.stampsLt_dhPk_pack interp S g ts ⟨sk⟩).mpr hsk

private theorem received_stampsLt {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr T : ExecTrace} (hle : tr ≤ T)
    (htr : TR.FreshSigma.TraceEntriesLt interp S g ts T)
    {hs : List Nat} {t : _root_.DY.Bytes} (ht : t ∈ received tr hs) :
    TR.FreshSigma.StampsLt interp S g ts t := by
  unfold received at ht
  obtain ⟨k, _, hk⟩ := List.mem_filterMap.mp ht
  exact cbadG2_stampsLt_getMessageSentAt_of_entries htr (cbadG2_getMessageSentAt_le hle hk)

theorem visStampsLt_of_stepView {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {s : Step} {tr T : ExecTrace} {wrapped : Bool}
    (hReach : tr.Reachable reachability) (hle : s.next tr ≤ T) (hlen : T.length ≤ ts)
    (htr : TR.FreshSigma.TraceEntriesLt interp S g ts T)
    {v : VisEntry} (hv : v ∈ stepView s tr wrapped) :
    TR.FreshSigma.VisStampsLt interp S g ts v := by
  have hle₀ : tr ≤ T := _root_.DY.Trace.le_trans _ _ _ (step_le_next s tr) hle
  have hlen' : (s.next tr).length ≤ ts := Nat.le_trans (_root_.DY.Trace.length_le _ _ hle) hlen
  unfold stepView at hv
  rcases List.mem_append.mp hv with hown | hexp
  · have hown' : v ∈ (match s with
        | .aliceStart _ _ _ _ h => aliceVis tr (s.next tr) h
        | .bobStart b _ kh _ mh _ _ => bobVis tr (s.next tr) mh (bobOpkPk b kh tr)
        | .messageEncrypt _ stateIdx .. =>
          encDraws (newRandoms tr (s.next tr)) ++ encSendEntry tr (s.next tr) stateIdx wrapped
        | .messageEncryptAbort .. => encDraws (newRandoms tr (s.next tr))
        | .messageDecrypt _ stateIdx msgIdx .. => decVis tr (s.next tr) stateIdx msgIdx wrapped
        | .messageDecryptSkipped _ stateIdx msgIdx .. =>
          decVis tr (s.next tr) stateIdx msgIdx wrapped
        | _ => []) := by
      split at hown
      · exact hown
      · exact List.mem_of_mem_filter hown
    cases s with
    | aliceStart _ _ _ _ h =>
      unfold aliceVis at hown'
      rcases List.mem_cons.mp hown' with rfl | hdr
      · exact TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => received_stampsLt hle₀ htr ht
      · refine TR.FreshSigma.visStampsLt_of_mem_aliceDraws _ _ (fun t ht => ?_) hdr
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
        exact TR.FreshSigma.stampsLt_of_mem_newRandoms hlen' hp
    | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
      unfold bobVis at hown'
      rcases List.mem_cons.mp hown' with rfl | hrest
      · refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
        rcases List.mem_append.mp ht with hrec | hopk
        · exact received_stampsLt hle₀ htr hrec
        · exact bobOpkPk_stampsLt hle₀ htr hopk
      · rcases List.mem_append.mp hrest with hrng | hacc
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrng
          refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
          rw [List.mem_singleton.mp ht]
          exact TR.FreshSigma.stampsLt_of_mem_newRandoms hlen' hp
        · rcases hpt : receivedPlaintext tr
              (Step.next (.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) tr) with _ | pt
          · simp [hpt] at hacc
          · simp only [hpt, Option.map_some, Option.toList_some, List.mem_singleton] at hacc
            subst hacc
            refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
            rw [List.mem_singleton.mp ht]
            exact TR.FreshSigma.stampsLt_of_receivedPlaintext hle htr hpt
    | messageEncrypt _ stateIdx _ _ =>
      rcases List.mem_append.mp hown' with hdr | hsend
      · exact TR.FreshSigma.visStampsLt_of_mem_encDraws _
          (fun _ hp => TR.FreshSigma.stampsLt_of_mem_newRandoms hlen' hp) hdr
      · unfold encSendEntry lastSent at hsend
        split at hsend
        · rename_i w hw
          split at hw
          · have hw_lt : TR.FreshSigma.StampsLt interp S g ts w :=
              cbadG2_stampsLt_getMessageSentAt_of_entries htr (cbadG2_getMessageSentAt_le hle hw)
            cases wrapped with
            | false =>
              rcases hppk : pendingPreKey tr stateIdx with _ | ⟨ek, ct⟩
              · simp only [hppk, List.mem_singleton] at hsend
                subst hsend
                refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
                rw [List.mem_singleton.mp ht]; exact hw_lt
              · simp [hppk] at hsend
            | true =>
              rcases hppk : pendingPreKey tr stateIdx with _ | ⟨ek, ct⟩
              · simp [hppk] at hsend
              · simp only [hppk, List.mem_singleton] at hsend
                subst hsend
                obtain ⟨hek, hct⟩ := pendingPreKey_stampsLt hReach hle₀ htr hppk
                refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
                simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
                rcases ht with rfl | rfl | rfl
                · exact hek
                · exact hct
                · exact hw_lt
          · simp at hw
        · cases hsend
    | messageEncryptAbort _ _ =>
      exact TR.FreshSigma.visStampsLt_of_mem_encDraws _
        (fun _ hp => TR.FreshSigma.stampsLt_of_mem_newRandoms hlen' hp) hown'
    | messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx =>
      unfold decVis at hown'
      rcases List.mem_append.mp hown' with h1 | hacc
      · rcases List.mem_append.mp h1 with hmsg | hrng
        · rcases hm : tr.getMessageSentAt msgIdx with _ | msgTerm
          · simp [hm] at hmsg
          · simp only [hm, Option.map_some, Option.toList_some, List.mem_singleton] at hmsg
            subst hmsg
            have hmt := cbadG2_stampsLt_getMessageSentAt_of_entries htr
              (cbadG2_getMessageSentAt_le hle₀ hm)
            refine ⟨fun t ht => by rw [List.mem_singleton.mp ht]; exact hmt, ?_⟩
            cases wrapped
            · intro _ ht; cases ht
            · exact fun ek hek => TR.FreshSigma.stampsLt_of_mem_sessionBaseKeys hle₀ htr hek
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrng
          refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
          rw [List.mem_singleton.mp ht]
          exact TR.FreshSigma.stampsLt_of_mem_newRandoms hlen' hp
      · rcases hpt : receivedPlaintext tr
            (Step.next (.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) tr) with _ | pt
        · simp [hpt] at hacc
        · simp only [hpt, Option.map_some, Option.toList_some, List.mem_singleton] at hacc
          subst hacc
          refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
          rw [List.mem_singleton.mp ht]
          exact TR.FreshSigma.stampsLt_of_receivedPlaintext hle htr hpt
    | messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx =>
      unfold decVis at hown'
      rcases List.mem_append.mp hown' with h1 | hacc
      · rcases List.mem_append.mp h1 with hmsg | hrng
        · rcases hm : tr.getMessageSentAt msgIdx with _ | msgTerm
          · simp [hm] at hmsg
          · simp only [hm, Option.map_some, Option.toList_some, List.mem_singleton] at hmsg
            subst hmsg
            have hmt := cbadG2_stampsLt_getMessageSentAt_of_entries htr
              (cbadG2_getMessageSentAt_le hle₀ hm)
            refine ⟨fun t ht => by rw [List.mem_singleton.mp ht]; exact hmt, ?_⟩
            cases wrapped
            · intro _ ht; cases ht
            · exact fun ek hek => TR.FreshSigma.stampsLt_of_mem_sessionBaseKeys hle₀ htr hek
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrng
          refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
          rw [List.mem_singleton.mp ht]
          exact TR.FreshSigma.stampsLt_of_mem_newRandoms hlen' hp
      · rcases hpt : receivedPlaintext tr
            (Step.next (.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) tr)
            with _ | pt
        · simp [hpt] at hacc
        · simp only [hpt, Option.map_some, Option.toList_some, List.mem_singleton] at hacc
          subst hacc
          refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_
          rw [List.mem_singleton.mp ht]
          exact TR.FreshSigma.stampsLt_of_receivedPlaintext hle htr hpt
    | network _ | registerIdentity _ | registerCorruptIdentity _ _ | genSignedPrekey _ _
    | genPQPrekey _ _ | genOneTimePrekey _ | exposeKey _ _ _ | exposeSpqr _ _ | exposeSkipped _
    | compromiseIK _ _ | compromiseSPK _ _ | compromisePQSPK _ _ | compromiseOPK _ _
    | breakDH | breakKEM | invertDH _ | invertKEM _ => cases hown'
  · unfold exposures at hexp
    rcases List.mem_append.mp hexp with hpq | htr_exp
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hpq
      unfold pqExposureAt at hj
      split at hj <;> (try cases hj) <;>
        (refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_;
         rcases hmsg : (s.next tr).getMessageSentAt (j + 1) with _ | m <;> simp [hmsg] at ht;
         subst ht;
         exact cbadG2_stampsLt_getMessageSentAt_of_entries htr (cbadG2_getMessageSentAt_le hle hmsg))
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp htr_exp
      unfold trExposureAt at hj
      split at hj <;> (try cases hj) <;>
        (refine TR.FreshSigma.visStampsLt_of_terms rfl fun t ht => ?_;
         rcases hmsg : (s.next tr).getMessageSentAt (j + 1) with _ | m <;> simp [hmsg] at ht;
         subst ht;
         exact cbadG2_stampsLt_getMessageSentAt_of_entries htr (cbadG2_getMessageSentAt_le hle hmsg))

theorem bytesMatchEntry_transfer {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₁ g₂ : Ghost} {ts : Nat} (hga : CBadGammaAgree interp S g₁ g₂ ts)
    {k : VisEventKind} {b : HwBytes} {v : VisEntry} {initIds : Option BundlePreKeyIds}
    (hv : TR.FreshSigma.VisStampsLt interp S g₁ ts v) :
    BytesMatchEntry interp r S g₂ k b v initIds ↔ BytesMatchEntry interp r S g₁ k b v initIds := by
  have hγ : ∀ t ∈ v.terms, gamma interp S g₂ t = gamma interp S g₁ t :=
    fun t ht => cbadG2_gamma_eq hga (hv.1 t ht)
  have hkeys := hv.2
  have hmap : v.terms.map (gamma interp S g₂) = v.terms.map (gamma interp S g₁) :=
    List.map_congr_left hγ
  unfold BytesMatchEntry; apply and_congr_right; intro _; dsimp only
  cases hl : v.layout with
  | single => rw [hmap]
  | whisper =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [hγ t (by simp [ht])]
  | bundle => exact cbadG2_bundleMatches_transfer hγ
  | preKeySend => exact cbadG2_sendMatches_transfer hγ
  | preKeyRecv => exact cbadG2_preKeyRecvOpkMatches_transfer hγ
  | preKeyInner eks =>
    rw [hl] at hkeys
    refine exists_congr fun t => exists_congr fun p => and_congr_right fun ht =>
      and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [hγ t (by simp [ht])]
    refine and_congr_left fun _ => exists_congr fun ek => and_congr_right fun hek => ?_
    rw [cbadG2_gamma_eq hga (hkeys ek hek)]
  | fresh _ => rfl
  | kyberCoin j =>
    apply and_congr_right; intro _
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [hγ t (by simp [ht])]
  | unconstrained => rfl
  | leakPq pq => cases pq <;> simp [hmap]
  | leakRecord =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [hγ t (by simp [ht])]

private theorem recvRepOn_transfer {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {ts : Nat} (hga : CBadGammaAgree interp S g₁ g₂ ts) {tr : ExecTrace}
    (htr : TR.FreshSigma.TraceEntriesLt interp S g₁ ts tr) {b : HwBytes} {t : _root_.DY.Bytes}
    (ht : t ∈ recvRepresentationsOn interp S g₁ tr b) :
    t ∈ recvRepresentationsOn interp S g₂ tr b := by
  obtain ⟨hk, hb, hp, hf⟩ := ht
  have hts := TR.FreshSigma.traceEntriesLt_knows htr hk
  refine ⟨hk, (cbadG2_gamma_eq hga hts).trans hb, hp, fun msg hmsg => ?_⟩
  obtain ⟨hw, hm, hrk, hct, hpq⟩ := TR.FreshSigma.stampsLt_parseTrSignalMsg hts hmsg
  obtain ⟨h1, h2, h3, h4⟩ := hf msg hmsg
  refine ⟨(cbadG2_gamma_eq hga hw).trans h1, (cbadG2_gamma_eq hga hm).trans h2, h3,
    fun m hm' => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := h4 m hm'
  exact ⟨(cbadG2_gamma_eq hga hct).trans e1, (cbadG2_gamma_eq hga hrk).trans e2,
    (cbadG2_gamma_eq hga hpq).trans e3, e4, e5⟩

private theorem preKeyRepOn_transfer {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {ts : Nat} (hga : CBadGammaAgree interp S g₁ g₂ ts) {tr : ExecTrace}
    (htr : TR.FreshSigma.TraceEntriesLt interp S g₁ ts tr) {b : HwBytes} {x : PreKeyRep}
    (hx : x ∈ preKeyRepresentationsOn interp r S g₁ tr b) :
    x ∈ preKeyRepresentationsOn interp r S g₂ tr b := by
  obtain ⟨hek, hct, hmsg, hm, p, hp, hfi⟩ := hx
  have h1 := TR.FreshSigma.traceEntriesLt_knows htr hek
  have h2 := TR.FreshSigma.traceEntriesLt_knows htr hct
  have h3 := TR.FreshSigma.traceEntriesLt_knows htr hmsg
  refine ⟨hek, hct, hmsg, ?_, p, hp, ?_⟩
  · have hγ : ∀ t ∈ [x.ek, x.ct, x.msg], gamma interp S g₂ t = gamma interp S g₁ t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact cbadG2_gamma_eq hga h1
      · exact cbadG2_gamma_eq hga h2
      · exact cbadG2_gamma_eq hga h3
    exact (cbadG2_preKeyRecvMatches_transfer hγ).mpr hm
  · obtain ⟨msg, hpm, e1, e2, e8, e3, e4, e7, e5, e6⟩ := hfi
    obtain ⟨hw, hmac, hrk, hct', hpq⟩ := TR.FreshSigma.stampsLt_parseTrSignalMsg h3 hpm
    exact ⟨msg, hpm, (cbadG2_gamma_eq hga hw).trans e1, (cbadG2_gamma_eq hga hmac).trans e2, e8,
      (cbadG2_gamma_eq hga hct').trans e3, (cbadG2_gamma_eq hga hrk).trans e4,
      (cbadG2_gamma_eq hga hpq).trans e7, e5, e6⟩

private theorem bobDoneBaseKeys_stampsLt {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr : ExecTrace} (hReach : tr.Reachable reachability) (hlen : tr.length ≤ ts)
    {ek : _root_.DY.Bytes} (hek : ek ∈ bobDoneBaseKeys tr) :
    TR.FreshSigma.StampsLt interp S g ts ek := by
  unfold bobDoneBaseKeys at hek
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hek
  split at hi
  · rename_i b a ikB ikA spk pqpk opk ek' ct keys hget
    cases hi
    exact g2b_bobDoneEk_stampsLt_of_reachable interp S g ts hReach hlen i b a ikB ikA spk pqpk opk
      ek ct keys hget
  · cases hi

theorem matchesEvents_visStampsLt {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {ts : Nat} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent}
    {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis)
    (hReach : tr.Reachable reachability)
    (hwf : StepsWF ss tr)
    (hlen : (runSteps ss tr).length ≤ ts)
    (htr : TR.FreshSigma.TraceEntriesLt interp S g ts (runSteps ss tr)) :
    ∀ v ∈ vis, TR.FreshSigma.VisStampsLt interp S g ts v := by
  induction hme with
  | nil _ => intro _ hv; cases hv
  | @run1 _ tr₀ pre s ss' ev evs' v vs _ hrm _ ih =>
    obtain ⟨hwf_pre, hpre_s, _, hwf_ss⟩ := (stepsWF_append_iff pre (s :: ss') tr₀).mp hwf
    have hReach₁ := runSteps_reachable pre hReach hwf_pre
    have hReach₂ := step_next_reachable hReach₁ hpre_s
    have hrun_eq : runSteps (pre ++ s :: ss') tr₀ = runSteps ss' (s.next (runSteps pre tr₀)) := by
      rw [runSteps_append]; rfl
    rw [hrun_eq] at hlen htr
    have hle_next : s.next (runSteps pre tr₀) ≤ runSteps ss' (s.next (runSteps pre tr₀)) :=
      runSteps_le ss' _
    have hv_eq : v = stepView s (runSteps pre tr₀) (runWrapped ev) := hrm.2.2.2.2.2.2.1
    intro u hu
    rcases List.mem_append.mp hu with huv | huvs
    · rw [hv_eq] at huv
      exact visStampsLt_of_stepView hReach₁ hle_next hlen htr huv
    · exact ih hReach₂ hwf_ss hlen htr u huvs
  | @run0 _ tr₀ pre ss' ev evs' vs _ _ _ ih =>
    obtain ⟨hwf_pre, hwf_ss⟩ := (stepsWF_append_iff pre ss' tr₀).mp hwf
    have hReach₁ := runSteps_reachable pre hReach hwf_pre
    rw [runSteps_append] at hlen htr
    exact ih hReach₁ hwf_ss hlen htr
  | @env _ tr₀ pre s ss' ev evs' v vs _ hem _ ih =>
    obtain ⟨hwf_pre, hpre_s, _, hwf_ss⟩ := (stepsWF_append_iff pre (s :: ss') tr₀).mp hwf
    have hReach₁ := runSteps_reachable pre hReach hwf_pre
    have hReach₂ := step_next_reachable hReach₁ hpre_s
    have hrun_eq : runSteps (pre ++ s :: ss') tr₀ = runSteps ss' (s.next (runSteps pre tr₀)) := by
      rw [runSteps_append]; rfl
    rw [hrun_eq] at hlen htr
    have hle_next : s.next (runSteps pre tr₀) ≤ runSteps ss' (s.next (runSteps pre tr₀)) :=
      runSteps_le ss' _
    cases ev with
    | leak p k =>
      have hv_eq : v = stepView s (runSteps pre tr₀) false := hem.2.2.2.1
      intro u hu
      rcases List.mem_append.mp hu with huv | huvs
      · rw [hv_eq] at huv
        exact visStampsLt_of_stepView hReach₁ hle_next hlen htr huv
      · exact ih hReach₂ hwf_ss hlen htr u huvs
    | breakDH | breakKEM | invertDH _ | invertKEM _ | registerCorrupt _ _ => cases hem

theorem ghostWF_transfer {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} {ts : Nat}
    (hfr : CBadSigmaFrame g₁ g₂ ts) {vis : List VisEntry}
    (hvis : ∀ v ∈ vis, Symbolic.Swarm.CREF.TR.FreshSigma.VisStampsLt interp S g₁ ts v)
    (hg : GhostWF g₁ vis) :
    GhostWF g₂ vis := by
  refine ⟨fun v hv hk i n hn hmem => ?_, by rw [hfr.2]; exact hg.2⟩
  have hlt : i < ts := lt_of_stampsLt_randTerm hn ((hvis v hv).1 (randTerm i n) hmem)
  rw [hfr.1 i hlt n]
  exact hg.1 v hv hk i n hn hmem

theorem matchesEvents_transfer {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₁ g₂ : Ghost} {initIds : Option BundlePreKeyIds} {ts : Nat} (hfr : CBadSigmaFrame g₁ g₂ ts)
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g₁ initIds tr ss evs vis)
    (hReach : tr.Reachable reachability)
    (hwf : StepsWF ss tr)
    (hlen : (runSteps ss tr).length ≤ ts) :
    MatchesEventsClassicalAt interp r S g₂ initIds tr ss evs vis := by
  have hga : CBadGammaAgree interp S g₁ g₂ ts := cbadG2_gammaAgree_of_sigmaFrame interp S hfr
  induction hme with
  | nil hinv => exact .nil hinv
  | @run0 _ tr₀ pre ss' ev evs' vs hpre hrej _ ih =>
    obtain ⟨hwf_pre, hwf_ss⟩ := (stepsWF_append_iff pre ss' tr₀).mp hwf
    rw [runSteps_append] at hlen
    exact .run0 hpre hrej (ih (runSteps_reachable pre hReach hwf_pre) hwf_ss hlen)
  | @env _ tr₀ pre s ss' ev evs' v vs hpre hem _ ih =>
    obtain ⟨hwf_pre, hpre_s, _, hwf_ss⟩ := (stepsWF_append_iff pre (s :: ss') tr₀).mp hwf
    have hReach₁ := runSteps_reachable pre hReach hwf_pre
    have hReach₂ := step_next_reachable hReach₁ hpre_s
    have hrun_eq : runSteps (pre ++ s :: ss') tr₀ = runSteps ss' (s.next (runSteps pre tr₀)) := by
      rw [runSteps_append]; rfl
    rw [hrun_eq] at hlen
    have hlen₂ : (s.next (runSteps pre tr₀)).length ≤ ts :=
      Nat.le_trans (_root_.DY.Trace.length_le _ _ (runSteps_le ss' _)) hlen
    have htr₂ := TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₂ hlen₂
    cases ev with
    | leak p k =>
      obtain ⟨hcls, hleak, hp, hv_eq, v₀, rfl, hbme⟩ := hem
      have hv₀_st : TR.FreshSigma.VisStampsLt interp S g₁ ts v₀ := by
        have hmem : v₀ ∈ stepView s (runSteps pre tr₀) false := by rw [← hv_eq]; simp
        exact visStampsLt_of_stepView hReach₁ (_root_.DY.Trace.le_refl _) hlen₂ htr₂ hmem
      have hem' : EnvMatchesClassical interp r S g₂ (runSteps pre tr₀) s (.leak p k) [v₀] :=
        ⟨hcls, hleak, hp, hv_eq, v₀, rfl, (bytesMatchEntry_transfer hga hv₀_st).mpr hbme⟩
      exact .env hpre hem' (ih hReach₂ hwf_ss hlen)
    | breakDH | breakKEM | invertDH _ | invertKEM _ | registerCorrupt _ _ => cases hem
  | @run1 initIds tr₀ pre s ss' ev evs' v vs hpre hrm _ ih =>
    obtain ⟨hwf_pre, hpre_s, _, hwf_ss⟩ := (stepsWF_append_iff pre (s :: ss') tr₀).mp hwf
    have hReach₁ := runSteps_reachable pre hReach hwf_pre
    have hReach₂ := step_next_reachable hReach₁ hpre_s
    have hrun_eq : runSteps (pre ++ s :: ss') tr₀ = runSteps ss' (s.next (runSteps pre tr₀)) := by
      rw [runSteps_append]; rfl
    rw [hrun_eq] at hlen
    have hlen₂ : (s.next (runSteps pre tr₀)).length ≤ ts :=
      Nat.le_trans (_root_.DY.Trace.length_le _ _ (runSteps_le ss' _)) hlen
    have hlen₁ : (runSteps pre tr₀).length ≤ ts :=
      Nat.le_trans (_root_.DY.Trace.length_le _ _ (step_le_next s _)) hlen₂
    have htr₁ := TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₁ hlen₁
    have htr₂ := TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₂ hlen₂
    obtain ⟨hcls, hparty, hfits, hpeer, hok, hexit, hv_eq,
      inp, drs, outs, hv_split, hinp, hdrs, houts, hrf, hpf⟩ := hrm
    have hv_st : ∀ u ∈ v, TR.FreshSigma.VisStampsLt interp S g₁ ts u := fun u hu => by
      rw [hv_eq] at hu
      exact visStampsLt_of_stepView hReach₁ (_root_.DY.Trace.le_refl _) hlen₂ htr₂ hu
    have hinp_st : TR.FreshSigma.VisStampsLt interp S g₁ ts inp :=
      hv_st inp (by rw [hv_split]; simp)
    have hinp' := (bytesMatchEntry_transfer hga hinp_st).mpr hinp
    have hdrs' : DrawsMatch interp r S g₂ drs ev.coins := by
      obtain ⟨pieces, hne, hpref, hrel⟩ := hdrs
      refine ⟨pieces, hne, hpref, ?_⟩
      have hsub : ∀ d ∈ drs, TR.FreshSigma.VisStampsLt interp S g₁ ts d :=
        fun d hd => hv_st d (by rw [hv_split]; simp [hd])
      clear hv_split hv_eq hne hpref
      revert pieces
      induction drs with
      | nil => intro pieces hrel; cases hrel; exact .nil
      | cons d ds ih_rel =>
        intro pieces hrel
        cases hrel with
        | cons hp htl =>
          exact .cons ((bytesMatchEntry_transfer hga (hsub d (by simp))).mpr hp)
            (ih_rel (fun d' hd' => hsub d' (by simp [hd'])) _ htl)
    have houts' : OutputsMatch interp r S g₂ ev outs initIds := by
      unfold OutputsMatch at houts ⊢
      split at houts
      · obtain ⟨o, rfl, ho⟩ := houts
        exact ⟨o, rfl, (bytesMatchEntry_transfer hga (hv_st o (by rw [hv_split]; simp))).mpr ho⟩
      · obtain ⟨o, rfl, ho⟩ := houts
        exact ⟨o, rfl, (bytesMatchEntry_transfer hga (hv_st o (by rw [hv_split]; simp))).mpr ho⟩
      · exact houts
    have hrf' : ReadsFaithfully interp r S g₂ (runSteps pre tr₀) inp ev.input := by
      unfold ReadsFaithfully at hrf ⊢
      split at hrf
      · exact recvRepOn_transfer hga htr₁ hrf
      · exact fun p hp => recvRepOn_transfer hga htr₁ (hrf p hp)
      · exact preKeyRepOn_transfer hga htr₁ hrf
      · trivial
    have hpf' : PathFaithfulAt interp S g₂ (runSteps pre tr₀) s ev.input := by
      intro p hp
      have hpf0 := hpf p hp
      have hknown_iff :
          (∃ ek ∈ bobDoneBaseKeys (runSteps pre tr₀),
              ecKey (gamma interp S g₂ ek) = p.baseKey.take 33) ↔
            (∃ ek ∈ bobDoneBaseKeys (runSteps pre tr₀),
              ecKey (gamma interp S g₁ ek) = p.baseKey.take 33) := by
        refine exists_congr fun ek => and_congr_right fun hek => ?_
        rw [cbadG2_gamma_eq hga (bobDoneBaseKeys_stampsLt hReach₁ hlen₁ hek)]
      dsimp only at hpf0 ⊢
      cases s <;> simp_all
    have hrm' : RunMatches interp r S g₂ (runSteps pre tr₀) s ev v initIds :=
      ⟨hcls, hparty, hfits, hpeer, hok, hexit, hv_eq,
        inp, drs, outs, hv_split, hinp', hdrs', houts', hrf', hpf'⟩
    exact .run1 hpre hrm' (ih hReach₂ hwf_ss hlen)

private theorem honestKeysOf_sent :
    ∀ (ss : List Step) (tr : ExecTrace) (u : _root_.DY.Bytes),
      u ∈ honestKeysOf tr ss → ∃ k, (runSteps ss tr).getMessageSentAt k = some u
  | [], _, _, hu => by simp [honestKeysOf] at hu
  | s :: ss, tr, u, hu => by
    unfold honestKeysOf Step.publishedSpqrKey? at hu
    rcases List.mem_append.mp hu with hu | hu
    · refine ⟨DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx tr,
        cbadG2_getMessageSentAt_le (runSteps_le ss (s.next tr)) ?_⟩
      cases s with
      | messageEncrypt me stateIdx coinsLen pqIdx =>
        by_cases hpq : pqIdx = DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx tr
        · simp [hpq] at hu
        · simp only [hpq, ↓reduceIte] at hu
          rcases hm :
              (Step.next (.messageEncrypt me stateIdx coinsLen pqIdx) tr).getMessageSentAt
                (DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx tr)
            with _ | m <;> simp [hm] at hu
          subst hu; rfl
      | _ => simp at hu
    · exact honestKeysOf_sent ss (s.next tr) u hu

private theorem honestSaltsOf_stampsLt {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {ss : List Step}
    (htr : TR.FreshSigma.TraceEntriesLt interp S g ts (runTrace r ss)) :
    ∀ s ∈ honestSaltsOf r ss, TR.FreshSigma.StampsLt interp S g ts s := by
  intro s hs
  unfold honestSaltsOf at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact TR.FreshSigma.stampsLt_zeroKey interp S g ts
  · obtain ⟨k, hk⟩ := honestKeysOf_sent ss (setupTrace r) s hs
    exact cbadG2_stampsLt_getMessageSentAt_of_entries htr hk

theorem recvCollisionOn_transfer {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₁ g₂ : Ghost} {ts : Nat} (hfr : CBadSigmaFrame g₁ g₂ ts)
    {ss₁ : List Step} {vis₁ : List VisEntry} {t : _root_.DY.Bytes}
    (hReach₁ : (runTrace r ss₁).Reachable reachability)
    (hlen₁ : (runTrace r ss₁).length ≤ ts)
    (hvis₁ : ∀ v ∈ vis₁, TR.FreshSigma.VisStampsLt interp S g₁ ts v)
    (ht : TR.FreshSigma.StampsLt interp S g₁ ts t)
    (hcol : RecvCollisionOn interp r S g₁ (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t) :
    RecvCollisionOn interp r S g₂ (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t := by
  let tr₁ := runTrace r ss₁
  have hga : CBadGammaAgree interp S g₁ g₂ ts := cbadG2_gammaAgree_of_sigmaFrame interp S hfr
  have htr₁ := TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₁ hlen₁
  have hpre := cbadG2_stampsLt_prefixTerms interp S g₁ r hReach₁ hlen₁ hvis₁
  have hstates := fun st (hst : st ∈ availableStates r tr₁) =>
    cbadG2_stateStampsLt_availableStates (S := S) (g := g₁) (n := ts) htr₁ hst
  have hsalts := honestSaltsOf_stampsLt (r := r) (ss := ss₁) htr₁
  have hsk := cbadG2_stampsLt_skippedLogged_of_entries htr₁
  unfold RecvCollisionOn at hcol ⊢
  cases hp : parseTrSignalMsg t with
  | none =>
    simp only [hp] at hcol ⊢
    exact (cbadG2_memoCollisionOn_iff hga hpre (fun u hu => List.mem_singleton.mp hu ▸ ht)).mpr hcol
  | some msg =>
    simp only [hp] at hcol ⊢
    have hmsg := TR.FreshSigma.stampsLt_parseTrSignalMsg ht hp
    have htrials := cbadG2_stampsLt_whisperTrials (r := r) htr₁ hstates hmsg
    have hwt_eq : whisperTrials interp r S g₂ tr₁ msg = whisperTrials interp r S g₁ tr₁ msg :=
      Stage1Trials.whisperTrials_congr_gamma
        (cbadG2_gamma_eq hga hmsg.2.2.1)
        (fun st hst_mem c hc => cbadG2_gamma_eq hga ((hstates st hst_mem).2.2.2.2.2.2 c hc).1)
        (fun idx hlt s pk ctr seed rIdx src hget =>
          cbadG2_gamma_eq hga (hsk idx s pk ctr seed rIdx src hlt hget).2)
    rw [hwt_eq]
    have hnew : ∀ u ∈ t :: (whisperTrials interp r S g₁ tr₁ msg).flatMap
        (trialTerms (honestSaltsOf r ss₁) msg), TR.FreshSigma.StampsLt interp S g₁ ts u := by
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht
      · obtain ⟨ctx, hctx, hu_ctx⟩ := List.mem_flatMap.mp hu
        have htr_ctx := htrials ctx hctx
        unfold trialTerms at hu_ctx
        rcases List.mem_append.mp hu_ctx with hu_ex | hu_rest
        · exact htr_ctx.2.2.1 u hu_ex
        · revert hu_rest
          cases hseed_eq : ctx.seed? with
          | none => intro h; cases h
          | some seed =>
            dsimp only; intro hu_flat
            obtain ⟨salt, hsalt, hu_salt⟩ := List.mem_flatMap.mp hu_flat
            exact cbadG2_stampsLt_saltTerms htr_ctx.1 htr_ctx.2.1 hmsg
              (htr_ctx.2.2.2.2 seed hseed_eq) (hsalts salt hsalt) u hu_salt
    rcases hcol with hmemo | hmac
    · exact Or.inl ((cbadG2_memoCollisionOn_iff hga hpre hnew).mpr hmemo)
    · refine Or.inr ?_
      have hkeys_lt : ∀ ctx ∈ whisperTrials interp r S g₁ tr₁ msg,
          ∀ seed, ctx.seed? = some seed → ∀ s ∈ ctx.ownSalts ++ honestSaltsOf r ss₁,
            let mk := trMsgKeys s seed
            TR.FreshSigma.StampsLt interp S g₁ ts mk.cipherKey ∧
            TR.FreshSigma.StampsLt interp S g₁ ts mk.macKey ∧
            TR.FreshSigma.StampsLt interp S g₁ ts mk.iv ∧
            TR.FreshSigma.StampsLt interp S g₁ ts (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) := by
        intro ctx hctx seed hseed s hs
        have htr_ctx := htrials ctx hctx
        have hs_lt : TR.FreshSigma.StampsLt interp S g₁ ts s := by
          rcases List.mem_append.mp hs with hs_own | hs_hon
          · exact htr_ctx.2.2.2.1 s hs_own
          · exact hsalts s hs_hon
        obtain ⟨hc_lt, hm_lt, hi_lt⟩ :=
          TR.FreshSigma.stampsLt_trMsgKeys hs_lt (htr_ctx.2.2.2.2 seed hseed)
        exact ⟨hc_lt, hm_lt, hi_lt,
          TR.FreshSigma.stampsLt_computeMac hm_lt htr_ctx.1 htr_ctx.2.1 hmsg.1⟩
      exact Stage1Trials.MacTagForgeryOrCollision.congr_gamma
        (cbadG2_gamma_eq hga hmsg.2.1).symm
        (cbadG2_gamma_eq hga hmsg.1).symm
        (fun ctx hctx seed hseed =>
          (cbadG2_gamma_eq hga ((htrials ctx hctx).2.2.2.2 seed hseed)).symm)
        (fun ctx hctx seed hseed s hs =>
          let ⟨hc, hm, hi, hcm⟩ := hkeys_lt ctx hctx seed hseed s hs
          ⟨(cbadG2_gamma_eq hga hc).symm, (cbadG2_gamma_eq hga hm).symm,
           (cbadG2_gamma_eq hga hi).symm, (cbadG2_gamma_eq hga hcm).symm⟩)
        (fun peerIk₀ myIk₀ salt₀ seed₀ w hterm => by
          have hmac_lt := hmsg.2.1
          rw [hterm] at hmac_lt
          exact (cbadG2_gamma_eq hga (stampsLt_wire_of_computeMac hmac_lt)).symm)
        hmac

theorem not_readCollisionCli_snoc_noDecrypt {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ g' : Ghost} {ts : Nat} {ss₀ δ : List Step} {evs_pre : List CliEvent} {ev₀ : RunEvent}
    (hfr : CBadSigmaFrame g₀ g' ts)
    (hwf₀ : ModelRunWF r ss₀)
    (hlen₀ : (runTrace r ss₀).length ≤ ts)
    (hδ : ∀ x ∈ δ, x.decryptMsgIdx? = none)
    (hnoAccRecv : ∀ peer out, ev₀.cmd = .recv peer → ev₀.exit ≠ some (0, out))
    (hnrc₀ : ¬ ReadCollisionCliClassical interp r S g₀ ss₀ evs_pre) :
    ¬ ReadCollisionCliClassical interp r S g' (ss₀ ++ δ) (evs_pre ++ [.run ev₀]) := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
    hevs, hss, ⟨peer, hcmd⟩, hexit, hbody, hme₁, hdec, hsent, hcol⟩
  have hevs₂_ne : evs₂ ≠ [] := by
    intro hnil
    subst hnil
    have heq := List.append_inj_right' hevs rfl
    simp only [List.cons.injEq, CliEvent.run.injEq, and_true] at heq
    subst heq
    exact hnoAccRecv peer out hcmd hexit
  have hevs_pre : evs_pre = evs₁ ++ .run ev :: evs₂.dropLast := by
    have hsplit : evs₁ ++ .run ev :: evs₂ =
        (evs₁ ++ .run ev :: evs₂.dropLast) ++ [evs₂.getLast hevs₂_ne] := by
      have hlast := (List.dropLast_append_getLast hevs₂_ne).symm
      calc evs₁ ++ .run ev :: evs₂
          = evs₁ ++ (.run ev :: (evs₂.dropLast ++ [evs₂.getLast hevs₂_ne])) := by rw [← hlast]
        _ = (evs₁ ++ .run ev :: evs₂.dropLast) ++ [evs₂.getLast hevs₂_ne] := by simp
    exact List.append_inj_left' (hevs.trans hsplit) rfl
  have hilt : ss₁.length < ss₀.length := by
    by_contra hge
    have hle : ss₀.length ≤ ss₁.length := Nat.le_of_not_lt hge
    have hget : (ss₀ ++ δ)[ss₁.length]? = (ss₁ ++ m :: ss₂)[ss₁.length]? :=
      congrArg (·[ss₁.length]?) hss
    rw [List.getElem?_append_right hle, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self] at hget
    have hm_in : m ∈ δ := List.mem_of_getElem? hget
    rw [hδ m hm_in] at hdec
    cases hdec
  obtain ⟨k, hk⟩ : ∃ k, ss₀.length - ss₁.length = k + 1 := ⟨ss₀.length - ss₁.length - 1, by omega⟩
  have hss₀ : ss₀ = ss₁ ++ m :: ss₂.take k := by
    have htake := congrArg (List.take ss₀.length) hss
    rw [List.take_left, List.take_append,
      List.take_of_length_le (Nat.le_of_lt hilt), hk, List.take_succ_cons] at htake
    exact htake
  have hfr_symm : CBadSigmaFrame g' g₀ ts := ⟨fun i hi n => (hfr.1 i hi n).symm, hfr.2.symm⟩
  have hReach_setup : (setupTrace r).Reachable reachability := TR.setupTrace_reachable r
  have hwf₁ : StepsWF ss₁ (setupTrace r) := by
    have hwf_all := hwf₀.2.2.1
    rw [hss₀] at hwf_all
    exact ((stepsWF_append_iff ss₁ (m :: ss₂.take k) (setupTrace r)).mp hwf_all).1
  have hReach₁ : (runTrace r ss₁).Reachable reachability :=
    runSteps_reachable ss₁ hReach_setup hwf₁
  have hle_tr : runTrace r ss₁ ≤ runTrace r ss₀ := by
    rw [hss₀, Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
    exact runSteps_le (m :: ss₂.take k) (runTrace r ss₁)
  have hlen₁ : (runTrace r ss₁).length ≤ ts :=
    Nat.le_trans (_root_.DY.Trace.length_le _ _ hle_tr) hlen₀
  have hme₁_0 : MatchesEventsClassical interp r S g₀ (setupTrace r) ss₁ evs₁ vis₁ :=
    matchesEvents_transfer hfr_symm hme₁ hReach_setup hwf₁ hlen₁
  have htr₁' := TR.FreshSigma.traceEntriesLt_of_reachable interp S g' ts hReach₁ hlen₁
  have hvis₁' := matchesEvents_visStampsLt hme₁ hReach_setup hwf₁ hlen₁ htr₁'
  have ht' := cbadG2_stampsLt_getMessageSentAt_of_entries htr₁' hsent
  have hcol_0 : RecvCollisionOn interp r S g₀ (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t :=
    recvCollisionOn_transfer hfr_symm hReach₁ hlen₁ hvis₁' ht' hcol
  exact hnrc₀ ⟨evs₁, ev, evs₂.dropLast, ss₁, ss₂.take k, m, vis₁, msgIdx, out, b, t,
    hevs_pre, hss₀, ⟨peer, hcmd⟩, hexit, hbody, hme₁_0, hdec, hsent, hcol_0⟩

end Symbolic.Proofs.Swarm.UA.SlotInitTransfer
