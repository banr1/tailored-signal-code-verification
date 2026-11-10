/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.AsmSecure
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
import DY.Misc.Fixpoint
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.ProtocolEvent
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.DYBridge.DY.Misc.Fixpoint
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign

/-!
# Positive `HwAttackerKnows` Non-Vacuity Proof

Proves that on the CLI-explained exposed-session trace (`evsExposed`, hardware view `visAt 11`),
Alice's leaked receiving chain key `keys1.ck` matches the leaked bytes `ckrBytes` of
`.env (.leak "alice" ckrBytes)` on `leakCkrEntry`, is absent from `setupSent r0`, and satisfies
`HwAttackerKnows r0 (visAt 11) keys1.ck`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HwAttackerKnows

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.TripleRatchet (TREvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   newIndices trExposureAt exposures stepView setupTrace setupSent nextBundleIds
   BytesMatchEntry EnvMatches MatchesEventsAt Explains HwAttackerKnows)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (registerIdentityTr genSignedPrekeyTr genPQPrekeyTr)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB spkNonce pqNonce keys1 stA4
   t11 t12 t11_length t12_length t12_exposedCKr_at t12_ck_sent_at)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
  (keys1_eq_pqxdhKdf)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 S0 myGhost msHonest msLeaks msTail msExposed
   move0_init move1_enc0 move2_enc1 move3_bobStart move4_dec1 move5_encReply0
   move6_decReply0 move7_leakCkr
   setupTrace_r0_eq move0_next move1_next move2_next move3_next move4_next
   move5_next move6_next move7_next move7_ok)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionTraces
  (ckrBytes leakEvCkr evsHonest evsExposed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
  (visBetween visSteps visAt)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
  (explains_exposed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (t1Pure t2Pure t3Pure t4Pure t4_eq_pure)

/-- The visible `.leak` entry emitted by `move7_leakCkr` at trace index `72` of `t12`. -/
def leakCkrEntry : VisEntry :=
  ⟨.leak, [keys1.ck], .leakRecord, some 72⟩

private theorem length_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [length_append]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

private theorem at?_append_self {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hlt, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem newIndices_nil_getMessageSentAt_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    ((newIndices Trace.nil (tr.append e)).filterMap
        fun i => (tr.append e).getMessageSentAt i) =
      ((newIndices Trace.nil tr).filterMap
        fun i => tr.getMessageSentAt i) ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option Network.ExecEntryT)).map (·.msg)).toList := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  unfold newIndices
  have h0 : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  rw [h0, length_append, Nat.sub_zero, Nat.sub_zero, List.range'_concat, Nat.zero_add, Nat.one_mul,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, at?_append_self]
  refine congrArg₂ List.append (List.filterMap_congr fun i hi => ?_) ?_
  · have hi' := List.mem_range'_1.mp hi
    rw [at?_append_of_lt tr e (by omega)]
  · cases (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option Network.ExecEntryT) <;>
      rfl

private theorem setupSent_r0_eq :
    setupSent r0 =
      [DY.DiffieHellman.dhPk ikA, DY.Signature.vk ikA,
       DY.DiffieHellman.dhPk ikB, DY.Signature.vk ikB,
       DY.DiffieHellman.dhPk spkB,
       DY.Signature.sign ikB spkNonce
         (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk spkB)),
       DY.PQKem.kemPk pqskB,
       DY.Signature.sign ikB pqNonce
         (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk pqskB))] := by
  rw [setupSent, setupTrace_r0_eq, t4_eq_pure]
  have hnil : newIndices (Trace.nil : ExecTrace) Trace.nil = [] := by
    simp [newIndices]
  simp only [t4Pure, t3Pure, t2Pure, t1Pure, registerIdentityTr, genSignedPrekeyTr, genPQPrekeyTr,
    newIndices_nil_getMessageSentAt_append, hnil, List.filterMap_nil,
    length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
  rfl

private theorem leakCkrEntry_mem_exposures : leakCkrEntry ∈ exposures t11 t12 := by
  have hev : t12.getEventAt TREvent 72 =
      some (.ExposedCKr (stA4.sessionInfo "alice") keys1.ck 0 1) := by
    have h := t12_exposedCKr_at
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h]
  have hmsg : t12.getMessageSentAt 73 = some keys1.ck := by
    have h := t12_ck_sent_at
    rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1] at h
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, h]
  have htr : trExposureAt t12 72 = some leakCkrEntry := by
    simp [trExposureAt, hev, hmsg, leakCkrEntry]
  have h72 : 72 ∈ newIndices t11 t12 := by
    simp [newIndices, t11_length, t12_length]
  unfold exposures
  exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨72, h72, htr⟩)

theorem leakCkrEntry_mem_visAt_11 : leakCkrEntry ∈ visAt 11 := by
  have hv7 : leakCkrEntry ∈ visBetween move7_leakCkr t11 t12 none false := by
    simpa [visBetween, move7_leakCkr] using leakCkrEntry_mem_exposures
  have hstep : visBetween move7_leakCkr t11 t12 none false ∈ visSteps.take 11 := by
    simp [visSteps]
  exact List.mem_flatten.mpr ⟨_, hstep, hv7⟩

private theorem matchesEventsAt_run_step {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {s : Step} {ss : List Step} {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry}
    (hcls : s.cls ≠ .invisible) (hexit : ∃ out, ev.exit = some (0, out))
    (hm : MatchesEventsAt myInterp r0 S0 myGhost initIds tr (s :: ss) (.run ev :: evs) vis) :
    ∃ vs, MatchesEventsAt myInterp r0 S0 myGhost (nextBundleIds initIds ev) (s.next tr) ss evs vs := by
  generalize hss : s :: ss = ss' at hm
  generalize hevs : CliEvent.run ev :: evs = evs' at hm
  cases hm with
  | nil _ => cases hevs
  | env _ _ _ => cases hevs
  | @run0 _ _ pre _ _ _ _ _ hrej _ =>
    injection hevs with hev _
    injection hev with hev; subst hev
    obtain ⟨out, hout⟩ := hexit
    exact (hrej out hout).elim
  | @run1 _ _ pre s0 ss0 _ _ _ vs hpre _ hm' =>
    injection hevs with hev hevs0
    injection hev with hev; subst hev hevs0
    cases pre with
    | nil =>
      injection hss with hs0 hss0; subst hs0 hss0
      exact ⟨vs, hm'⟩
    | cons x xs =>
      injection hss with hx _
      have hinv := hpre x (.head xs)
      rw [← hx] at hinv
      exact (hcls hinv).elim

private theorem matchesEventsAt_env_step {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {s : Step} {ss : List Step} {ev : EnvEvent} {evs : List CliEvent} {vis : List VisEntry}
    (hcls : s.cls ≠ .invisible)
    (hm : MatchesEventsAt myInterp r0 S0 myGhost initIds tr (s :: ss) (.env ev :: evs) vis) :
    ∃ v, EnvMatches myInterp r0 S0 myGhost tr s ev v := by
  generalize hss : s :: ss = ss' at hm
  generalize hevs : CliEvent.env ev :: evs = evs' at hm
  cases hm with
  | nil _ => cases hevs
  | run0 _ _ _ => cases hevs
  | run1 _ _ _ => cases hevs
  | @env _ _ pre s0 _ _ _ v _ hpre henv _ =>
    injection hevs with hev _
    injection hev with hev; subst hev
    cases pre with
    | nil =>
      injection hss with hs0 _; subst hs0
      exact ⟨v, henv⟩
    | cons x xs =>
      injection hss with hx _
      have hinv := hpre x (.head xs)
      rw [← hx] at hinv
      exact (hcls hinv).elim

theorem bytesMatchEntry_leakCkrEntry :
    BytesMatchEntry myInterp r0 S0 myGhost .leak ckrBytes leakCkrEntry := by
  have hm := explains_exposed.2.2.2
  dsimp only [DY.Libsignal.Composed.Refinement.MatchesEvents,
    msExposed, msHonest, msLeaks, msTail, evsExposed, evsHonest,
    List.cons_append, List.nil_append] at hm
  rw [setupTrace_r0_eq] at hm
  obtain ⟨_, hm⟩ := matchesEventsAt_run_step (by decide) ⟨_, rfl⟩ hm
  rw [move0_next] at hm
  obtain ⟨_, hm⟩ := matchesEventsAt_run_step (by decide) ⟨_, rfl⟩ hm
  rw [move1_next] at hm
  obtain ⟨_, hm⟩ := matchesEventsAt_run_step (by decide) ⟨_, rfl⟩ hm
  rw [move2_next] at hm
  obtain ⟨_, hm⟩ := matchesEventsAt_run_step (by decide) ⟨_, rfl⟩ hm
  rw [move3_next] at hm
  obtain ⟨_, hm⟩ := matchesEventsAt_run_step (by decide) ⟨_, rfl⟩ hm
  rw [move4_next] at hm
  obtain ⟨_, hm⟩ := matchesEventsAt_run_step (by decide) ⟨_, rfl⟩ hm
  rw [move5_next] at hm
  obtain ⟨_, hm⟩ := matchesEventsAt_run_step (by decide) ⟨_, rfl⟩ hm
  rw [move6_next] at hm
  obtain ⟨vlist, henv⟩ := matchesEventsAt_env_step (by decide) hm
  dsimp only [leakEvCkr, EnvMatches] at henv
  obtain ⟨_, _, _, hvlist, v0, hv0, hbme⟩ := henv
  have hstep : stepView move7_leakCkr t11 false = exposures t11 t12 := by
    unfold stepView
    rw [move7_next, move7_ok]
    rfl
  have hmem : leakCkrEntry ∈ [v0] := by
    rw [← hv0, hvlist, hstep]
    exact leakCkrEntry_mem_exposures
  rw [List.mem_singleton.mp hmem]
  exact hbme

theorem keys1_ck_not_mem_setupSent : keys1.ck ∉ setupSent r0 := by
  rw [setupSent_r0_eq]
  intro hmem
  obtain ⟨ikm, hikm⟩ := keys1_eq_pqxdhKdf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with heq | heq | heq | heq | heq | heq | heq | heq <;>
    rw [hikm] at heq <;>
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none heq

theorem hwAttackerKnows_keys1_ck : HwAttackerKnows r0 (visAt 11) keys1.ck := by
  unfold HwAttackerKnows
  rw [Symbolic.DYBridge.DY.Fixpoint.mkLeastFixpoint_eq_1]
  exact fun _ hstep =>
    hstep keys1.ck
      (Or.inr (Or.inr ⟨leakCkrEntry, leakCkrEntry_mem_visAt_11,
        List.mem_singleton.mpr rfl, trivial⟩))

theorem leakEvCkr_mem_evsExposed : .env (.leak "alice" ckrBytes) ∈ evsExposed := by
  simp [evsExposed, leakEvCkr]

theorem hwAttackerKnows_leak_nonvacuous_proof :
    ∃ (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
      (g : Ghost) (ss : List Step) (vis : List VisEntry) (evs : List CliEvent)
      (t : DY.Bytes) (p : Participant) (bs : HwBytes),
      Explains interp r S g ss vis evs ∧
      .env (.leak p bs) ∈ evs ∧
      (∃ v ∈ vis, v.kind = .leak ∧ t ∈ v.terms ∧ BytesMatchEntry interp r S g .leak bs v) ∧
      t ∉ setupSent r ∧
      HwAttackerKnows r vis t :=
  ⟨myInterp, r0, S0, myGhost, msExposed, visAt 11, evsExposed, keys1.ck, "alice", ckrBytes,
    explains_exposed, leakEvCkr_mem_evsExposed,
    ⟨leakCkrEntry, leakCkrEntry_mem_visAt_11, rfl, List.mem_singleton.mpr rfl,
      bytesMatchEntry_leakCkrEntry⟩,
    keys1_ck_not_mem_setupSent, hwAttackerKnows_keys1_ck⟩

end Symbolic.Proofs.Tests.CliNonvacuity.HwAttackerKnows
