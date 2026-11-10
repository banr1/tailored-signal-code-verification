/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Misc.Fixpoint
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Specifications.Security.AsmSecure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Misc.Fixpoint
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Attacker-Knowledge Transfer across CLI Event Explanations

Proves `hwAttackerKnows_implies_attackerKnows_of_explains'`: every term derivable by the hardware
attacker from `setupSent r` and the `send`, `recv`, and `leak` entries of an explanation
`Explains interp r S g ss vis evs` satisfies `AttackerKnows` on `runTrace r ss`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.HwKnows

open DY DY.Comparse
open scoped DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.PQXDH (PQXDHEvent registerCorruptIdentity breakDH breakKEM invertDH invertKEM)
open DY.Libsignal.Composed (reachability ComposedEvent)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry StepsWF
  BundlePreKeyIds MatchesEvents MatchesEventsAt
  Explains HwAttackerKnows setupTrace setupSent runSteps runTrace stepView encDraws encSendEntry
  pendingPreKey lastSent bobOpkPk runWrapped OpkNetOK opkNetOK_nil opkNetOK_append_other VisKnown
  visKnown_of_kind encDraws_kind lastSent_known aliceVis_known bobVis_known bobOpkPk_known
  decVis_known exposures_known newSent_known invertEntry)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves composed_reachable_induction NetE NetMsgAt)
open Symbolic.Swarm.COMPOSED.CompInv (spqrInv_of_reachable)

/-! ## `OpkNetOK` on Reachable Composed Traces -/

private theorem opkNetOK_preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves OpkNetOK (registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage skIdx) fun _ => ?_
  refine Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
  exact OpkNetOK.preserves_logEvent_pq _

private theorem opkNetOK_preserves_breakDH : Preserves OpkNetOK breakDH :=
  OpkNetOK.preserves_logEvent_pq _

private theorem opkNetOK_preserves_breakKEM : Preserves OpkNetOK breakKEM :=
  OpkNetOK.preserves_logEvent_pq _

private theorem opkNetOK_preserves_invertDH (msgIdx : Nat) :
    Preserves OpkNetOK (invertDH msgIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage msgIdx) fun _ => ?_
  split
  · exact OpkNetOK.preserves_sendMessage _
  · exact Preserves.failure

private theorem opkNetOK_preserves_invertKEM (msgIdx : Nat) :
    Preserves OpkNetOK (invertKEM msgIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage msgIdx) fun _ => ?_
  refine Preserves.bind (Preserves.monadLiftErr _) fun _ => ?_
  exact OpkNetOK.preserves_sendMessage _

private theorem opkNetOK_of_reachable {tr : ExecTrace} (hReach : tr.Reachable reachability) :
    OpkNetOK tr :=
  composed_reachable_induction
    opkNetOK_nil
    (fun msg _ _ hok => opkNetOK_append_other hok (NetE msg) rfl)
    OpkNetOK.preserves_registerIdentity
    opkNetOK_preserves_registerCorruptIdentity
    OpkNetOK.preserves_genSignedPrekey
    OpkNetOK.preserves_genPQPrekey
    OpkNetOK.preserves_genOneTimePrekey
    OpkNetOK.preserves_aliceStart
    OpkNetOK.preserves_bobStart
    OpkNetOK.preserves_messageEncrypt
    OpkNetOK.preserves_messageEncryptAbort
    OpkNetOK.preserves_messageDecrypt
    OpkNetOK.preserves_messageDecryptSkipped
    OpkNetOK.preserves_exposeKey
    OpkNetOK.preserves_exposeSpqr
    OpkNetOK.preserves_exposeSkipped
    OpkNetOK.preserves_compromiseIK
    OpkNetOK.preserves_compromiseSPK
    OpkNetOK.preserves_compromisePQSPK
    OpkNetOK.preserves_compromiseOPK
    opkNetOK_preserves_breakDH
    opkNetOK_preserves_breakKEM
    opkNetOK_preserves_invertDH
    opkNetOK_preserves_invertKEM
    hReach

/-! ## Per-Step Visibility Knowledge -/

private theorem eventLoggedAt_of_getEventAt_pq {tr : ExecTrace} {d : Nat} {ev : PQXDHEvent}
    (h : tr.getEventAt PQXDHEvent d = some ev) : tr.EventLoggedAt ev d := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rcases hat : (tr.at? d : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with _ | ⟨ev'⟩
  · simp [hat] at h
  · simp [hat] at h
    subst h
    rfl

private theorem aliceDone_ek_ct_known {tr : ExecTrace} (hReach : tr.Reachable reachability)
    {a b : Participant} {ikA ikB spk pqpk : DY.Bytes} {opk : Option DY.Bytes} {ek ct : DY.Bytes}
    {keys : DY.Libsignal.PQXDH.HandshakeKeys} {d : Nat}
    (hEv : tr.getEventAt PQXDHEvent d = some (.AliceDone a b ikA ikB spk pqpk opk ek ct keys)) :
    ek.AttackerKnows tr ∧ ct.AttackerKnows tr := by
  have hLog := eventLoggedAt_of_getEventAt_pq hEv
  obtain ⟨t, _, rfl, hSlot, _⟩ :=
    (spqrInv_of_reachable tr hReach).aliceDone a b ikA ikB spk pqpk opk ek ct keys d hLog
  obtain ⟨_, _, _, a', b', ikA', ikB', spk', pqpk', opk', ek', ct', keys', hNetEk, hNetCt, hLog'⟩ :=
    hSlot
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hLog hLog'
  have hEq : (some ⟨.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys'⟩ :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) =
      some ⟨.AliceDone a b ikA ikB spk pqpk opk ek ct keys⟩ :=
    hLog'.symm.trans hLog
  injection hEq with hEntry
  injection hEntry with hEvEq
  injection hEvEq with _ _ _ _ _ _ _ hEk hCt _
  subst hEk; subst hCt
  exact ⟨NetMsgAt.attackerKnows hNetEk, NetMsgAt.attackerKnows hNetCt⟩

private theorem pendingPreKey_known {tr : ExecTrace} (hReach : tr.Reachable reachability)
    {stateIdx : Nat} {ek ct : DY.Bytes} (h : pendingPreKey tr stateIdx = some (ek, ct)) :
    ek.AttackerKnows tr ∧ ct.AttackerKnows tr := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · obtain ⟨pqev, hpq_mem, hi⟩ := List.exists_of_findSome?_eq_some h
      obtain ⟨i, _, hget⟩ := List.mem_filterMap.mp hpq_mem
      split at hi
      · cases hi
        split at hget
        · split at hget
          · exact aliceDone_ek_ct_known hReach hget
          · cases hget
        · cases hget
      · cases hi
  · cases h

private theorem encSendEntry_known {tr tr' : ExecTrace} (hReach : tr.Reachable reachability)
    (hle : tr ≤ tr') {stateIdx : Nat} {wrapped : Bool} {v : VisEntry}
    (hv : v ∈ encSendEntry tr tr' stateIdx wrapped) : VisKnown tr' v := by
  rcases hw : lastSent tr tr' with _ | w
  · simp [encSendEntry, hw] at hv
  · have hwKnown : w.AttackerKnows tr' := lastSent_known hw
    rcases hp : pendingPreKey tr stateIdx with _ | ⟨ek, ct⟩ <;> cases wrapped <;>
      simp only [encSendEntry, hw, hp] at hv
    · rcases List.mem_singleton.mp hv with rfl
      intro _ t ht
      rcases List.mem_singleton.mp ht with rfl
      exact hwKnown
    · cases hv
    · cases hv
    · rcases List.mem_singleton.mp hv with rfl
      obtain ⟨hEk, hCt⟩ := pendingPreKey_known hReach hp
      intro _ t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact Bytes.AttackerKnows_le _ _ _ hle hEk
      · exact Bytes.AttackerKnows_le _ _ _ hle hCt
      · exact hwKnown

private theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

private theorem stepView_known {s : Step} {tr : ExecTrace} {wrapped : Bool}
    (hReach : tr.Reachable reachability) {v : VisEntry} (hv : v ∈ stepView s tr wrapped) :
    VisKnown (s.next tr) v := by
  have hle : tr ≤ s.next tr := step_le_next s tr
  have hopk : OpkNetOK tr := opkNetOK_of_reachable hReach
  unfold stepView at hv
  rcases List.mem_append.mp hv with hown | hexp
  · have hown' : v ∈ (match s with
        | .aliceStart _ _ _ _ h => DY.Libsignal.Composed.Refinement.aliceVis tr (s.next tr) h
        | .bobStart b _ kh _ mh _ _ =>
          DY.Libsignal.Composed.Refinement.bobVis tr (s.next tr) mh (bobOpkPk b kh tr)
        | .messageEncrypt _ stateIdx .. =>
          encDraws (DY.Libsignal.Composed.Refinement.newRandoms tr (s.next tr)) ++
            encSendEntry tr (s.next tr) stateIdx wrapped
        | .messageEncryptAbort .. =>
          encDraws (DY.Libsignal.Composed.Refinement.newRandoms tr (s.next tr))
        | .messageDecrypt _ stateIdx msgIdx .. =>
          DY.Libsignal.Composed.Refinement.decVis tr (s.next tr) stateIdx msgIdx wrapped
        | .messageDecryptSkipped _ stateIdx msgIdx .. =>
          DY.Libsignal.Composed.Refinement.decVis tr (s.next tr) stateIdx msgIdx wrapped
        | _ => []) := by
      split at hown
      · exact hown
      · exact List.mem_of_mem_filter hown
    cases s with
    | aliceStart _ _ _ _ h => exact aliceVis_known hle hown'
    | bobStart b _ kh _ mh _ _ =>
      exact bobVis_known hle
        (fun t ht => Bytes.AttackerKnows_le _ _ _ hle (bobOpkPk_known hopk ht)) hown'
    | messageEncrypt _ stateIdx _ _ =>
      rcases List.mem_append.mp hown' with hdr | hsend
      · exact visKnown_of_kind ((encDraws_kind _ hdr).elim Or.inl (Or.inr ∘ Or.inl))
      · exact encSendEntry_known hReach hle hsend
    | messageEncryptAbort _ _ =>
      exact visKnown_of_kind ((encDraws_kind _ hown').elim Or.inl (Or.inr ∘ Or.inl))
    | messageDecrypt _ _ _ _ _ => exact decVis_known hle hown'
    | messageDecryptSkipped _ _ _ _ _ _ => exact decVis_known hle hown'
    | network _ | registerIdentity _ | registerCorruptIdentity _ _ | genSignedPrekey _ _
    | genPQPrekey _ _ | genOneTimePrekey _ | exposeKey _ _ _ | exposeSpqr _ _ | exposeSkipped _
    | compromiseIK _ _ | compromiseSPK _ _ | compromisePQSPK _ _ | compromiseOPK _ _
    | breakDH | breakKEM | invertDH _ | invertKEM _ => cases hown'
  · exact exposures_known hexp

/-! ## `MatchesEvents` Induction and Main Theorem -/

private theorem runSteps_append : ∀ (xs ys : List Step) (tr : ExecTrace),
    runSteps (xs ++ ys) tr = runSteps ys (runSteps xs tr)
  | [], _, _ => rfl
  | s :: xs, ys, tr => runSteps_append xs ys (s.next tr)

private theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => Trace.le_refl tr
  | s :: ss, tr => Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

private theorem stepsWF_append : ∀ (xs : List Step) {ys : List Step} {tr : ExecTrace},
    StepsWF (xs ++ ys) tr → StepsWF xs tr ∧ StepsWF ys (runSteps xs tr)
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: xs, _, _, ⟨hpre, hloc, hrest⟩ =>
    let ⟨hxs, hys⟩ := stepsWF_append xs hrest
    ⟨⟨hpre, hloc, hxs⟩, hys⟩

private theorem runSteps_reachable : ∀ (ss : List Step) {tr : ExecTrace},
    tr.Reachable reachability → StepsWF ss tr → (runSteps ss tr).Reachable reachability
  | [], _, hReach, _ => hReach
  | s :: ss, _, hReach, ⟨hpre, _, hwf⟩ =>
    runSteps_reachable ss (Trace.Reachable.Step s.toInput hpre hReach) hwf

private theorem invertEntry_known {s : Step} {tr : ExecTrace} {layout : DY.Libsignal.Composed.Refinement.VisByteLayout} {v : VisEntry}
    (hv : v ∈ invertEntry s tr layout) : VisKnown (s.next tr) v := by
  unfold invertEntry at hv
  cases hls : lastSent tr (s.next tr) with
  | none => rw [hls] at hv; cases hv
  | some w =>
    rw [hls] at hv
    simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hv
    subst hv
    intro _ t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact lastSent_known hls

private theorem matchesEvents_known {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hMe : MatchesEventsAt interp r S g initIds tr ss evs vis) (hReach : tr.Reachable reachability)
    (hWF : StepsWF ss tr) : ∀ {v : VisEntry}, v ∈ vis → VisKnown (runSteps ss tr) v := by
  induction hMe with
  | nil _ =>
    intro _ hv
    cases hv
  | @run1 _ tr₀ pre s ss' ev _ vStep vs _ hRun _ ih =>
    obtain ⟨hWFPre, hPreS, _, hWFSS⟩ := stepsWF_append pre hWF
    have hReach₁ : (runSteps pre tr₀).Reachable reachability := runSteps_reachable pre hReach hWFPre
    have hReach₂ : (s.next (runSteps pre tr₀)).Reachable reachability :=
      Trace.Reachable.Step s.toInput hPreS hReach₁
    rw [runSteps_append]
    show ∀ {v : VisEntry}, v ∈ vStep ++ vs → VisKnown (runSteps ss' (s.next (runSteps pre tr₀))) v
    intro v hv
    rcases List.mem_append.mp hv with hvStep | hvs
    · rw [hRun.2.2.2.2.2.2.1] at hvStep
      exact (stepView_known hReach₁ hvStep).mono (runSteps_le ss' _)
    · exact ih hReach₂ hWFSS hvs
  | @run0 _ tr₀ pre ss' _ _ vs _ _ _ ih =>
    obtain ⟨hWFPre, hWFSS⟩ := stepsWF_append pre hWF
    rw [runSteps_append]
    exact ih (runSteps_reachable pre hReach hWFPre) hWFSS
  | @env _ tr₀ pre s ss' ev _ vStep vs _ hEnv _ ih =>
    obtain ⟨hWFPre, hPreS, _, hWFSS⟩ := stepsWF_append pre hWF
    have hReach₁ : (runSteps pre tr₀).Reachable reachability :=
      runSteps_reachable pre hReach hWFPre
    have hReach₂ : (s.next (runSteps pre tr₀)).Reachable reachability :=
      Trace.Reachable.Step s.toInput hPreS hReach₁
    rw [runSteps_append]
    show ∀ {v : VisEntry},
        v ∈ vStep ++ vs → VisKnown (runSteps ss' (s.next (runSteps pre tr₀))) v
    intro v hv
    rcases List.mem_append.mp hv with hvStep | hvs
    · cases ev with
      | leak p k =>
        rw [hEnv.2.2.2.1] at hvStep
        exact (stepView_known hReach₁ hvStep).mono (runSteps_le ss' _)
      | breakDH | breakKEM =>
        rw [hEnv.2] at hvStep
        cases hvStep
      | invertDH _ _ | invertKEM _ _ =>
        obtain ⟨_, _, _, _, hv_eq, _⟩ := hEnv
        rw [hv_eq] at hvStep
        exact (invertEntry_known hvStep).mono (runSteps_le ss' _)
      | registerCorrupt _ _ => exact False.elim hEnv
    · exact ih hReach₂ hWFSS hvs

/-- Every term derivable by the hardware attacker from `setupSent r` and the `send`, `recv`, and
`leak` entries of `vis` under `Explains interp r S g ss vis evs` satisfies `AttackerKnows` on
`runTrace r ss`. -/
theorem hwAttackerKnows_implies_attackerKnows_of_explains' {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs : List CliEvent} (h : Explains interp r S g ss vis evs) {t : DY.Bytes}
    (ht : HwAttackerKnows r vis t) : t.AttackerKnows (runTrace r ss) := by
  obtain ⟨_, _, ⟨_, hSetupReach, hStepsWF, _⟩, hMe⟩ := h
  unfold HwAttackerKnows at ht
  rw [Symbolic.DYBridge.DY.Fixpoint.mkLeastFixpoint_eq_1] at ht
  refine ht (fun b => b.AttackerKnows (runTrace r ss)) fun b hb =>
    hb.elim (Bytes.AttackerKnows.prove AttackerKnowledge.attackerKnowledge b (runTrace r ss)) ?_
  rintro (hs | ⟨v, hv, htMem, ho⟩)
  · exact Bytes.AttackerKnows_le _ _ _ (runSteps_le ss (setupTrace r)) (newSent_known hs)
  · have hvk : VisKnown (runTrace r ss) v := matchesEvents_known hMe hSetupReach hStepsWF hv
    cases hk : v.kind <;> rw [hk] at ho <;>
      first | exact False.elim ho | exact hvk (Or.inl hk) b htMem
            | exact hvk (Or.inr (Or.inl hk)) b htMem | exact hvk (Or.inr (Or.inr hk)) b htMem

end Symbolic.Proofs.Swarm.UA.HwKnows

-- AUTO-BRIDGE BEGIN
namespace DY.Libsignal.Composed.Refinement.Cli.UA
export Symbolic.Proofs.Swarm.UA.HwKnows (hwAttackerKnows_implies_attackerKnows_of_explains')
end DY.Libsignal.Composed.Refinement.Cli.UA
-- AUTO-BRIDGE END
