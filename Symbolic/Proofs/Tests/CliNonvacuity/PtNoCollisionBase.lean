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
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase
public import Symbolic.Specifications.Refinement.TraceExplanation
import Symbolic.Proofs.Swarm.UA.HwKnows
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Tests.CliNonvacuity.Witness -- shake: keep
import Symbolic.DYBridge.DY.Misc.Fixpoint
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Plaintext Draw Non-Collision Base Helpers

Provides `RandAt`, `runSteps`, `prefixTerms_termRandAt`, and non-random transition preservation
lemmas (`noRandAt_*`, `randAt_invisible`) supporting `PtNoCollision`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent)
open DY.Libsignal.PQXDH (PQXDHEvent BundleHandles)
open DY.Libsignal.Composed (ComposedEvent reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma' gamma
   setupTrace newIndices newRandoms rngEntry eventIdx isAliceDone
   kyberCoinEntries aliceDraws aliceVis bobOpkPk bobVis encDraws encSendEntry decVis
   invertEntry stepView runSteps
   randTerm setupRandomsAt runTrace ptEntryAt
   storedStates storedSecrets principalTerms
   BytesMatchEntry DrawsMatch OutputsMatch inputKind runWrapped
   EnvMatches RunMatches MatchesEventsAt MatchesEvents Explains HwAttackerKnows
   plaintextTerms prefixTerms MemoCollisionOn)
open DY.Libsignal.Composed.Refinement.Cli
  (PrefixExplainingGhosts NextEventCollides)
open DY.Libsignal.Composed.Refinement.Cli.UA
  (hwAttackerKnows_implies_attackerKnows_of_explains')
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp mkRecords mySem not_mem_109_freshBytes)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (RandAt TermRandAt termRandAt_rand StEntry TREntry PQStEntry PQEvEntry
   TraceEntriesRand traceEntriesRand_knows traceEntriesRand_at?_st traceEntriesRand_at?_pqst
   termRandAt_serialize_tr termRandAt_serialize_pq traceEntriesRand_of_reachable
   pack_of_view_eq_some memo_entry_inv gamma'_randTerm_32 gamma_randTerm_of_ne_zero
   nonRandom_assumedInjective_len_ne_9)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (randTerm_inj)
open Symbolic.Proofs.Swarm.UA.XlateSteps
  (stepIn_next stepIn_ok runSteps_reachable invisible_eq_network
   exposures_kind encSendEntry_kind
   bobStart_newRandoms_32 messageDecrypt_newRandoms_32 messageDecryptSkipped_newRandoms_32)
open Symbolic.Swarm.CREF.TR
  (at?_append_of_lt at?_append_self at?_append_eq_of_proj
   setupTrace_eq newRandoms_setupTr4 newRandoms_setupTr5)

/-! ## `RandAt` and `runSteps` Helpers -/

theorem lt_of_randAt {tr : ExecTrace} {ts sz : Nat} (h : RandAt tr ts sz) :
    ts < tr.length := by
  unfold RandAt DY.Trace.at? at h
  split at h
  · assumption
  · cases h

theorem randAt_of_le_of_lt {tr₁ tr₂ : ExecTrace} (hle : tr₁ ≤ tr₂) {ts sz : Nat}
    (hlt : ts < tr₁.length) (h : RandAt tr₂ ts sz) : RandAt tr₁ ts sz := by
  have hlt₂ : ts < tr₂.length := lt_of_randAt h
  unfold RandAt DY.Trace.at? at h ⊢
  simp only [hlt, hlt₂, ↓reduceDIte] at h ⊢
  rw [DY.Trace.at_le tr₁ tr₂ ts hlt hle]
  exact h

theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => DY.Trace.le_refl tr
  | s :: ss, tr => DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

theorem runSteps_append :
    ∀ (xs ys : List Step) (tr : ExecTrace),
      runSteps (xs ++ ys) tr = runSteps ys (runSteps xs tr)
  | [], _, _ => rfl
  | x :: xs, ys, tr => runSteps_append xs ys (x.next tr)

theorem mem_newRandoms_of_randAt {tr₀ tr₁ : ExecTrace} {ts sz : Nat}
    (hlo : tr₀.length ≤ ts) (hrnd : RandAt tr₁ ts sz) :
    (randTerm ts sz, sz) ∈ newRandoms tr₀ tr₁ := by
  have hlt : ts < tr₁.length := lt_of_randAt hrnd
  have hidx : ts ∈ newIndices tr₀ tr₁ := by
    unfold newIndices
    rw [List.mem_range']
    exact ⟨ts - tr₀.length, by omega, by omega⟩
  unfold newRandoms
  rw [List.mem_filterMap]
  refine ⟨ts, hidx, ?_⟩
  unfold RandAt at hrnd
  rw [hrnd]
  rfl

private theorem randAt_of_mem_newRandoms {tr₀ tr₁ : ExecTrace} {m : DY.Bytes} {n : Nat}
    (h : (m, n) ∈ newRandoms tr₀ tr₁) :
    ∃ ts, m = randTerm ts n ∧ RandAt tr₁ ts n := by
  unfold newRandoms at h
  obtain ⟨ts, _, hm⟩ := List.mem_filterMap.mp h
  rcases hat : (tr₁.at? ts : Option DY.Random.ExecEntryT) with _ | ⟨sz⟩
  · rw [hat] at hm; cases hm
  · rw [hat] at hm
    injection hm with hp
    injection hp with hm_eq hn_eq
    subst hm_eq hn_eq
    exact ⟨ts, rfl, hat⟩

private theorem at?_append_gt {E F : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has F]
    (tr : ExecTrace) (e : E) {j : Nat} (hj : tr.length < j) :
    ((tr.append e).at? j : Option F) = none := by
  unfold DY.Trace.at?
  have hlen : ¬ j < (tr.append e).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  exact dite_eq_right_iff.mpr fun h => absurd h hlen

private theorem randAt_append_nonRnd {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none)
    {ts sz : Nat} (hrnd : RandAt (tr.append e) ts sz) : RandAt tr ts sz := by
  unfold RandAt at hrnd ⊢
  by_cases hj : ts < tr.length
  · rwa [at?_append_of_lt tr e hj] at hrnd
  · by_cases heq : ts = tr.length
    · rw [at?_append_eq_of_proj tr e heq _ hproj] at hrnd; cases hrnd
    · rw [at?_append_gt tr e (by omega)] at hrnd; cases hrnd

theorem randAt_setupTrace_mem_setupRandomsAt {r : ProtocolSetup} (_hNe : r.alice ≠ r.bob)
    {ts sz : Nat} (hrnd : RandAt (setupTrace r) ts sz) : (ts, sz) ∈ setupRandomsAt r := by
  unfold setupRandomsAt newIndices
  unfold RandAt at hrnd
  have hlt : ts < (setupTrace r).length := by
    unfold DY.Trace.at? at hrnd
    by_cases h : ts < (setupTrace r).length
    · exact h
    · simp [h] at hrnd
  refine List.mem_filterMap.mpr ⟨ts, ?_, by simp [hrnd]⟩
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1, hlt]

/-! ## Plaintext Entries and `prefixTerms_termRandAt` -/

private theorem aliceDraws_kind (done : Option Nat) (xs : List DY.Bytes) {v : VisEntry}
    (hv : v ∈ aliceDraws done xs) : v.kind = .rng := by
  cases xs with
  | nil => cases hv
  | cons ek rest =>
    cases rest with
    | nil => rcases List.mem_singleton.mp hv with rfl; rfl
    | cons ent rest2 =>
      rcases List.mem_cons.mp hv with rfl | htail
      · rfl
      · rcases List.mem_append.mp htail with hkyb | hdhs
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkyb; rfl
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hdhs; rfl

private theorem encDraws_pt_randAt {tr₀ tr₁ : ExecTrace} {v : VisEntry}
    (hv : v ∈ encDraws (newRandoms tr₀ tr₁)) (hk : v.kind = .pt) {t : DY.Bytes}
    (ht : t ∈ v.terms) : ∃ ts sz, t = randTerm ts sz ∧ RandAt tr₁ ts sz := by
  cases hnr : newRandoms tr₀ tr₁ with
  | nil => rw [hnr] at hv; cases hv
  | cons r0 rest =>
    rcases r0 with ⟨m0, n0⟩
    rw [hnr] at hv
    rcases List.mem_cons.mp hv with rfl | hrest
    · rcases List.mem_singleton.mp ht with rfl
      have hmem0 : (t, n0) ∈ newRandoms tr₀ tr₁ := by rw [hnr]; exact List.mem_cons_self
      obtain ⟨ts, heq, hrnd⟩ := randAt_of_mem_newRandoms hmem0
      exact ⟨ts, n0, heq, hrnd⟩
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrest
      cases hk

private theorem stepView_pt_randAt (s : Step) (tr₀ : ExecTrace) (wrapped : Bool) {v : VisEntry}
    (hv : v ∈ stepView s tr₀ wrapped) (hk : v.kind = .pt) {t : DY.Bytes} (ht : t ∈ v.terms) :
    ∃ ts sz, t = randTerm ts sz ∧ RandAt (s.next tr₀) ts sz := by
  unfold stepView at hv
  rcases List.mem_append.mp hv with hv_if | hexp
  · have hv_own : v ∈ (match s with
        | .aliceStart _ _ _ _ h => aliceVis tr₀ (s.next tr₀) h
        | .bobStart b _ kh _ mh _ _ => bobVis tr₀ (s.next tr₀) mh (bobOpkPk b kh tr₀)
        | .messageEncrypt _ stateIdx .. =>
          encDraws (newRandoms tr₀ (s.next tr₀)) ++ encSendEntry tr₀ (s.next tr₀) stateIdx wrapped
        | .messageEncryptAbort .. => encDraws (newRandoms tr₀ (s.next tr₀))
        | .messageDecrypt _ stateIdx msgIdx .. => decVis tr₀ (s.next tr₀) stateIdx msgIdx wrapped
        | .messageDecryptSkipped _ stateIdx msgIdx .. =>
          decVis tr₀ (s.next tr₀) stateIdx msgIdx wrapped
        | _ => []) := by
      split at hv_if
      · exact hv_if
      · exact (List.mem_filter.mp hv_if).1
    cases s with
    | messageEncrypt _ _ _ _ =>
      rcases List.mem_append.mp hv_own with hd | hs
      · exact encDraws_pt_randAt hd hk ht
      · exact absurd (hk.symm.trans (encSendEntry_kind hs)) (by decide)
    | messageEncryptAbort _ _ => exact encDraws_pt_randAt hv_own hk ht
    | aliceStart _ _ _ _ _ =>
      rcases List.mem_cons.mp hv_own with rfl | hd
      · cases hk
      · rw [aliceDraws_kind _ _ hd] at hk; cases hk
    | bobStart _ _ _ _ _ _ _ =>
      rcases List.mem_cons.mp hv_own with rfl | hb
      · cases hk
      · rcases List.mem_append.mp hb with hrng | hacc
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; cases hk
        · rcases hp : DY.Libsignal.Composed.Refinement.receivedPlaintext tr₀ _ with _ | _
          · rw [hp] at hacc; cases hacc
          · rw [hp] at hacc; rcases List.mem_singleton.mp hacc with rfl; cases hk
    | messageDecrypt _ _ _ _ _ | messageDecryptSkipped _ _ _ _ _ _ =>
      unfold decVis at hv_own
      rcases List.mem_append.mp hv_own with hv12 | hacc
      · rcases List.mem_append.mp hv12 with hrecv | hrng
        · rcases hm : tr₀.getMessageSentAt _ with _ | _
          · rw [hm] at hrecv; cases hrecv
          · rw [hm] at hrecv; rcases List.mem_singleton.mp hrecv with rfl; cases hk
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; cases hk
      · rcases hp : DY.Libsignal.Composed.Refinement.receivedPlaintext tr₀ _ with _ | _
        · rw [hp] at hacc; cases hacc
        · rw [hp] at hacc; rcases List.mem_singleton.mp hacc with rfl; cases hk
    | _ => cases hv_own
  · exact absurd (hk.symm.trans (exposures_kind hexp)) (by decide)

private theorem invertEntry_not_pt {s : Step} {tr : ExecTrace}
    {lay : DY.Libsignal.Composed.Refinement.VisByteLayout} {v : VisEntry}
    (hv : v ∈ invertEntry s tr lay) : v.kind ≠ .pt := by
  unfold invertEntry at hv
  rcases hls : DY.Libsignal.Composed.Refinement.lastSent tr (s.next tr) with _ | sk
  · rw [hls] at hv; cases hv
  · rw [hls] at hv
    rcases List.mem_singleton.mp hv with rfl
    intro h; cases h

private theorem matchesEvents_pt_randAt {i : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr₀ : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry}
    (hMe : MatchesEventsAt i r S g initIds tr₀ ss evs vis) {v : VisEntry}
    (hv : v ∈ vis) (hk : v.kind = .pt) {t : DY.Bytes} (ht : t ∈ v.terms) :
    ∃ ts sz, t = randTerm ts sz ∧ RandAt (runSteps ss tr₀) ts sz := by
  induction hMe with
  | nil _ => cases hv
  | run0 _ _ _ ih =>
    rw [runSteps_append]
    exact ih hv
  | @run1 _ tr pre s ss' ev evs' v_step vs _ hrm _ ih =>
    rw [runSteps_append]
    rcases List.mem_append.mp hv with hv1 | hvs
    · rw [hrm.2.2.2.2.2.2.1] at hv1
      obtain ⟨ts, sz, rfl, hrnd⟩ := stepView_pt_randAt s (runSteps pre tr) (runWrapped ev) hv1 hk ht
      exact ⟨ts, sz, rfl, RandAt.mono (runSteps_le ss' _) hrnd⟩
    · exact ih hvs
  | @env _ tr pre s ss' ev evs' v_step vs _ hem _ ih =>
    rw [runSteps_append]
    rcases List.mem_append.mp hv with hv1 | hvs
    · cases ev with
      | registerCorrupt _ _ => exact False.elim hem
      | breakDH | breakKEM => rw [hem.2] at hv1; cases hv1
      | invertDH _ _ | invertKEM _ _ =>
        obtain ⟨_, _, _, _, hv_eq, _⟩ := hem
        rw [hv_eq] at hv1
        exact absurd hk (invertEntry_not_pt hv1)
      | leak _ _ =>
        rw [hem.2.2.2.1] at hv1
        obtain ⟨ts, sz, rfl, hrnd⟩ := stepView_pt_randAt s (runSteps pre tr) false hv1 hk ht
        exact ⟨ts, sz, rfl, RandAt.mono (runSteps_le ss' _) hrnd⟩
    · exact ih hvs

theorem prefixTerms_termRandAt
    {i : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs₁ : List CliEvent}
    (hex : Explains i r S g ss vis evs₁)
    {t : DY.Bytes} (ht : t ∈ prefixTerms r (runTrace r ss) vis) :
    TermRandAt i S g (runTrace r ss) t := by
  have hreach : (runTrace r ss).Reachable reachability :=
    runSteps_reachable ss hex.2.2.1.2.1 hex.2.2.1.2.2.1
  have htr := traceEntriesRand_of_reachable i S g hreach
  unfold prefixTerms principalTerms at ht
  rcases List.mem_append.mp ht with hprin | hpt
  · rcases List.mem_append.mp hprin with h12 | hsec
    · rcases List.mem_append.mp h12 with hsend | hst
      · obtain ⟨v, hv_filt, ht_v⟩ := List.mem_flatMap.mp hsend
        obtain ⟨hv_vis, hv_kind⟩ := List.mem_filter.mp hv_filt
        have hk : v.kind = .send := beq_iff_eq.mp hv_kind
        have hhw : HwAttackerKnows r vis t := by
          unfold HwAttackerKnows
          rw [Symbolic.DYBridge.DY.Fixpoint.mkLeastFixpoint_eq_1]
          exact fun _ hstep => hstep t (Or.inr (Or.inr ⟨v, hv_vis, ht_v, by rw [hk]; trivial⟩))
        exact traceEntriesRand_knows htr
          (hwAttackerKnows_implies_attackerKnows_of_explains' hex hhw)
      · obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
        unfold storedStates DY.ExecTrace.getLocalStateAt at hls
        obtain ⟨idx, _, hidx⟩ := List.mem_filterMap.mp hls
        rcases hat : ((runTrace r ss).at? idx : Option StEntry) with _ | e
        · rw [hat] at hidx; cases hidx
        · rw [hat] at hidx; injection hidx with he; subst he
          exact termRandAt_serialize_tr e.st (traceEntriesRand_at?_st htr hat)
    · unfold storedSecrets DY.ExecTrace.getLocalStateAt at hsec
      simp only [Option.map_map] at hsec
      obtain ⟨idx, _, hidx⟩ := List.mem_filterMap.mp hsec
      rcases hat : ((runTrace r ss).at? idx : Option PQStEntry) with _ | e
      · rw [hat] at hidx; cases hidx
      · rw [hat] at hidx; injection hidx with he; subst he
        exact termRandAt_serialize_pq e.st (traceEntriesRand_at?_pqst htr hat)
  · unfold plaintextTerms at hpt
    obtain ⟨v, hv_filt, ht_v⟩ := List.mem_flatMap.mp hpt
    obtain ⟨hv_vis, hv_kind⟩ := List.mem_filter.mp hv_filt
    have hk : v.kind = .pt := beq_iff_eq.mp hv_kind
    obtain ⟨ts, sz, rfl, hrnd⟩ := matchesEvents_pt_randAt hex.2.2.2 hv_vis hk ht_v
    exact termRandAt_rand i S g hrnd

/-! ## Random-Draw Preservation Along Non-Random Steps -/

private theorem newIndices_append_ge {E : Type} [ExecTraceTypes.Has E]
    {tr₀ tr : ExecTrace} (hle : tr₀.length ≤ tr.length) (e : E) :
    newIndices tr₀ (tr.append e) = newIndices tr₀ tr ++ [tr.length] := by
  unfold newIndices
  have hlen : (tr.append e).length - tr₀.length = (tr.length - tr₀.length) + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  rw [hlen, List.range'_concat]
  simp only [Nat.one_mul, Nat.add_sub_of_le hle]

theorem newRandoms_self (tr : ExecTrace) : newRandoms tr tr = [] := by
  simp [newRandoms, newIndices]

theorem newRandoms_append_rnd_ge {tr₀ tr : ExecTrace} (hle : tr₀.length ≤ tr.length)
    (n : Nat) :
    newRandoms tr₀ (tr.append (DY.Random.ExecEntryT.mk n)) =
      newRandoms tr₀ tr ++ [(randTerm tr.length n, n)] := by
  unfold newRandoms
  rw [newIndices_append_ge hle, List.filterMap_append]
  congr 1
  · refine List.filterMap_congr fun j hj => ?_
    have hlt : j < tr.length := by
      unfold newIndices at hj; rw [List.mem_range'] at hj; omega
    rw [at?_append_of_lt tr _ hlt]
  · simp [at?_append_self]

theorem newRandoms_append_nonRnd_ge {E : Type} [ExecTraceTypes.Has E]
    {tr₀ tr : ExecTrace} (hle : tr₀.length ≤ tr.length) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none) :
    newRandoms tr₀ (tr.append e) = newRandoms tr₀ tr := by
  unfold newRandoms
  rw [newIndices_append_ge hle, List.filterMap_append]
  have hnil : ([tr.length].filterMap fun i =>
      (((tr.append e).at? i : Option DY.Random.ExecEntryT).map fun r =>
        (randTerm i r.length, r.length))) = [] := by
    simp [at?_append_eq_of_proj tr e rfl _ hproj]
  rw [hnil, List.append_nil]
  refine List.filterMap_congr fun j hj => ?_
  have hlt : j < tr.length := by
    unfold newIndices at hj; rw [List.mem_range'] at hj; omega
  rw [at?_append_of_lt tr e hlt]

theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with | none => none | some a => ((f a).run (x.run tr).2.val).1 := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, _, _⟩ <;> rfl

theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | none => (x.run tr).2.val
      | some a => ((f a).run (x.run tr).2.val).2.val := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, _, _⟩ <;> rfl

structure Preserves (P : ExecTrace → Prop) {α : Type} (x : Traceful α) : Prop where
  run : ∀ tr, P tr → P (x.run tr).2.val

theorem Preserves.pure {P : ExecTrace → Prop} {α : Type} {a : α} :
    Preserves P (Pure.pure a : Traceful α) :=
  ⟨fun _ h => by erw [DY.Traceful.run_pure]; exact h⟩
theorem Preserves.failure {P : ExecTrace → Prop} {α : Type} :
    Preserves P (Alternative.failure : Traceful α) :=
  ⟨fun _ h => by erw [DY.Traceful.run_failure]; exact h⟩
private theorem Preserves.bind {P : ExecTrace → Prop} {α β : Type} {x : Traceful α}
    {f : α → Traceful β} (hx : Preserves P x) (hf : ∀ a, Preserves P (f a)) :
    Preserves P (x >>= f) :=
  ⟨fun tr h => by
    rw [run_bind_snd]
    cases (x.run tr).1 with
    | none => exact hx.run tr h
    | some a => exact (hf a).run _ (hx.run tr h)⟩
theorem Preserves.guardP {P : ExecTrace → Prop} (p : Prop) {_ : Decidable p} :
    Preserves P (@_root_.guard Traceful _ p _) :=
  ⟨fun _ h => by
    unfold _root_.guard
    split
    · erw [DY.Traceful.run_pure]; exact h
    · erw [DY.Traceful.run_failure]; exact h⟩
private theorem Preserves.guardTrace {P : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves P (DY.Libsignal.TripleRatchet.guardTrace p) :=
  ⟨fun _ h => by unfold DY.Libsignal.TripleRatchet.guardTrace; erw [DY.Traceful.run_mk]; exact h⟩
private theorem Preserves.requireTracePredicate {P : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves P (DY.Libsignal.PQXDH.guardTrace p) :=
  ⟨fun _ h => by unfold DY.Libsignal.PQXDH.guardTrace; erw [DY.Traceful.run_mk]; exact h⟩
private theorem Preserves.monadLiftOpt {P : ExecTrace → Prop} {α : Type} (x : DY.Err α) :
    Preserves P (MonadLift.monadLift x : Traceful α) := by
  cases (x : Option α) <;>
    exact ⟨fun _ h => by dsimp only [MonadLift.monadLift]; erw [DY.Traceful.run_mk]; exact h⟩
private theorem Preserves.getEntry {P : ExecTrace → Prop} {E : Type} [ExecTraceTypes.Has E]
    (j : Nat) : Preserves P (DY.getEntry j : Traceful E) :=
  ⟨fun _ h => by rw [Symbolic.DYBridge.DY.getEntry_eq_1]; erw [DY.Traceful.run_mk]; exact h⟩
theorem Preserves.receiveMessage {P : ExecTrace → Prop} (j : Nat) :
    Preserves P (Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Preserves.bind (Preserves.getEntry j) fun _ => Preserves.pure
private theorem Preserves.getLocalState {P : ExecTrace → Prop} {St : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT St)]
    (me : Participant) (j : Nat) :
    Preserves P (PersistentLocalState.getLocalState me j : Traceful St) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact Preserves.bind (Preserves.bind (Preserves.getEntry j) fun _ => Preserves.pure) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure
theorem Preserves.getKey {P : ExecTrace → Prop} (p : Participant) (j : Nat)
    (k : DY.Libsignal.PQXDH.KeyKind) :
    Preserves P (DY.Libsignal.PQXDH.getKey p j k) :=
  Preserves.bind (Preserves.getLocalState p j) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure
theorem Preserves.lookupIdentity {P : ExecTrace → Prop} (p : Participant) (j : Nat) :
    Preserves P (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  apply Preserves.bind (Preserves.getEntry j); intro e
  cases e.ev with
  | IdentityRegistered _ _ _ _ => exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure
  | _ => exact Preserves.failure

theorem noRandAt_append_nonRnd {E : Type} [ExecTraceTypes.Has E] (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none)
    {ts sz : Nat} {tr : ExecTrace} (h : ¬ RandAt tr ts sz) : ¬ RandAt (tr.append e) ts sz :=
  fun h' => h (randAt_append_nonRnd tr e hproj h')

theorem noRandAt_compromise {ts sz : Nat} (p : Participant) (stateIdx : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) (mkEv : DY.Bytes → PQXDHEvent) :
    Preserves (fun tr => ¬ RandAt tr ts sz)
      (do let sk ← DY.Libsignal.PQXDH.getKey p stateIdx kind
          DY.ProtocolEvent.logEvent (mkEv sk)
          DY.Network.sendMessage sk) := by
  apply Preserves.bind (Preserves.getKey p stateIdx kind); intro sk
  apply Preserves.bind ⟨fun _ h => by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
    exact noRandAt_append_nonRnd (⟨mkEv sk⟩ : PQEvEntry) rfl h⟩; intro _
  exact ⟨fun _ h => by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]
    exact noRandAt_append_nonRnd (⟨sk⟩ : Network.ExecEntryT) rfl h⟩

theorem noRandAt_compromiseOPK {ts sz : Nat} (b : Participant) (stateIdx : Nat) :
    Preserves (fun tr => ¬ RandAt tr ts sz)
      (DY.Libsignal.PQXDH.compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  apply Preserves.bind (Preserves.getKey b stateIdx .oneTimePrekey); intro sk
  apply Preserves.bind (Preserves.requireTracePredicate _); intro _
  apply Preserves.bind ⟨fun _ h => by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
    exact noRandAt_append_nonRnd (⟨PQXDHEvent.CompromisedOPK b (DY.DiffieHellman.CanDH.dhPk sk)⟩ : PQEvEntry) rfl h⟩; intro _
  exact ⟨fun _ h => by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]
    exact noRandAt_append_nonRnd (⟨sk⟩ : Network.ExecEntryT) rfl h⟩

theorem noRandAt_exposeKey {ts sz : Nat} (me : Participant) (stateIdx : Nat)
    (k : DY.Libsignal.TripleRatchet.KeyComponent) :
    Preserves (fun tr => ¬ RandAt tr ts sz)
      (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  have hlog : ∀ ev : TREvent, Preserves (fun tr => ¬ RandAt tr ts sz) (DY.ProtocolEvent.logEvent ev) :=
    fun ev => ⟨fun _ h => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
      exact noRandAt_append_nonRnd (⟨ev⟩ : TREntry) rfl h⟩
  have hsend : ∀ m : DY.Bytes, Preserves (fun tr => ¬ RandAt tr ts sz) (DY.Network.sendMessage m) :=
    fun m => ⟨fun _ h => by
      simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]
      exact noRandAt_append_nonRnd (⟨m⟩ : Network.ExecEntryT) rfl h⟩
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply Preserves.bind (Preserves.getLocalState me stateIdx); intro st
  cases k with
  | rk | dhs | cks =>
    apply Preserves.bind (hlog _); intro _
    exact hsend _
  | ckr pk =>
    dsimp only; split
    · apply Preserves.bind (hlog _); intro _
      exact hsend _
    · exact Preserves.failure

theorem noRandAt_exposeSpqr {ts sz : Nat} (me : Participant) (stateIdx : Nat) :
    Preserves (fun tr => ¬ RandAt tr ts sz)
      (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  apply Preserves.bind (Preserves.getLocalState me stateIdx); intro _
  apply Preserves.bind ⟨fun _ h => by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
    exact noRandAt_append_nonRnd (_ : TREntry) rfl h⟩; intro _
  exact ⟨fun _ h => by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]
    exact noRandAt_append_nonRnd (_ : Network.ExecEntryT) rfl h⟩

theorem noRandAt_exposeSkipped {ts sz : Nat} (skippedKeyEventIdx : Nat) :
    Preserves (fun tr => ¬ RandAt tr ts sz)
      (DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply Preserves.bind (Preserves.getEntry skippedKeyEventIdx); intro (e : TREntry)
  split
  · apply Preserves.bind (Preserves.guardTrace _); intro _
    apply Preserves.bind ⟨fun _ h => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
      exact noRandAt_append_nonRnd (_ : TREntry) rfl h⟩; intro _
    exact ⟨fun _ h => by
      simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]
      exact noRandAt_append_nonRnd (_ : Network.ExecEntryT) rfl h⟩
  · exact Preserves.failure

theorem noRandAt_invertDH {ts sz : Nat} (msgIdx : Nat) :
    Preserves (fun tr => ¬ RandAt tr ts sz) (DY.Libsignal.PQXDH.invertDH msgIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  apply Preserves.bind (Preserves.requireTracePredicate _); intro _
  apply Preserves.bind (Preserves.receiveMessage msgIdx); intro _
  split
  · exact ⟨fun _ h => by
      simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]
      exact noRandAt_append_nonRnd (_ : Network.ExecEntryT) rfl h⟩
  · exact Preserves.failure

theorem noRandAt_invertKEM {ts sz : Nat} (msgIdx : Nat) :
    Preserves (fun tr => ¬ RandAt tr ts sz) (DY.Libsignal.PQXDH.invertKEM msgIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  apply Preserves.bind (Preserves.requireTracePredicate _); intro _
  apply Preserves.bind (Preserves.receiveMessage msgIdx); intro _
  apply Preserves.bind (Preserves.monadLiftOpt _); intro _
  exact ⟨fun _ h => by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]
    exact noRandAt_append_nonRnd (_ : Network.ExecEntryT) rfl h⟩

theorem randAt_invisible :
    ∀ {pre : List Step} {tr : ExecTrace} {ts sz : Nat},
      (∀ x ∈ pre, x.cls = .invisible) → RandAt (runSteps pre tr) ts sz → RandAt tr ts sz
  | [], _, _, _, _, hrnd => hrnd
  | x :: xs, tr, ts, sz, hinv, hrnd => by
    obtain ⟨msg, rfl⟩ := invisible_eq_network (hinv x List.mem_cons_self)
    have hrnd' : RandAt ((Step.network msg).next tr) ts sz :=
      randAt_invisible (fun y hy => hinv y (List.mem_cons_of_mem _ hy)) hrnd
    have hnext : (Step.network msg).next tr = tr.append (⟨msg⟩ : Network.ExecEntryT) := by
      dsimp only [Step.next, Step.toInput]
      erw [stepIn_next DY.Network.reachability msg tr]
      dsimp only [DY.Network.reachability]
      simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]
    rw [hnext] at hrnd'
    exact randAt_append_nonRnd tr (⟨msg⟩ : Network.ExecEntryT) rfl hrnd'

end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase

-- AUTO-BRIDGE BEGIN
namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (lt_of_randAt randAt_of_le_of_lt step_le_next runSteps_le runSteps_append)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (mem_newRandoms_of_randAt randAt_setupTrace_mem_setupRandomsAt)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (prefixTerms_termRandAt newRandoms_self newRandoms_append_rnd_ge)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (newRandoms_append_nonRnd_ge run_bind_fst run_bind_snd Preserves)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (noRandAt_append_nonRnd noRandAt_compromise noRandAt_compromiseOPK noRandAt_exposeKey)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (noRandAt_exposeSpqr noRandAt_exposeSkipped noRandAt_invertDH noRandAt_invertKEM)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (randAt_invisible)
end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision
namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision.Preserves
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase.Preserves (pure failure guardP receiveMessage getKey lookupIdentity)
end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision.Preserves
-- AUTO-BRIDGE END
