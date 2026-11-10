/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Actions.Random
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse

/-!
# Step-Level View Reductions and Call 0 Ghost Pinning

Proves `newRandoms`, `lastSent`, `exposures`, and `pendingPreKey` equations on clean traces,
party-step `MatchesEventsAt` splitting, and setup plus Call 0 (`aliceStart`) ghost pinning
(`SetupAndCall0Pinned`, `peel_setup_and_call0`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins1

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

open DY (Bytes Participant ExecTrace Trace ExecTraceTypes TraceEntryHas)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg TREvent parseTrSignalMsg)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry Step BundlePreKeyIds
   newIndices newRandoms lastSent pqExposureAt trExposureAt exposures
   pendingPreKey encDraws encSendEntry aliceDraws aliceVis bobVis decVis
   stepView rngEntry kyberCoinEntries eventIdx isAliceDone received receivedPlaintext bobOpkPk
   ecKey pubBytes setupRandomsAt secretBytes setupPublic randTerm
   bundlePreKeyIds nextBundleIds runWrapped inputKind preKeyWire plaintextTerms
   GhostAndSemMatchSetup GhostWF BytesMatchEntry DrawsMatch OutputsMatch SendMatches
   RunMatches RunRejected MatchesEventsAt runSteps gamma gamma')
open Symbolic.Proofs.Tests.Shared.Composed.Runs (RndE NetE StT EvP EvC EvT rnd)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (bh1 kh1 o1 stA0 pqskB t4 t5 t4_length t5_length)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (t1Pure t2Pure t3Pure t4Pure t4_eq_pure)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (gamma'_kemEncap_of_len32)
open Symbolic.BugInjection (fillFresh hexBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compKyberEncaps)
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy (setupPublic_6)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup
  (w0 r0 r_alice_eq r_bob_eq r_secret3_eq r_secret4_eq r_secret5_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets (dag_nodes_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
  (r_withOpk_eq setupPublic_eq_r0 step0_next_t4)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators (TermAt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
  (termAt_rand termAt_dhPk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0
  (length_append at?_append_of_lt at?_append_self encTrGen encTrGen_getMessageSentAt_msg decTr0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (stA1c pqKeyOf pqKey0 sendMsgOf trClean1 trClean2 trClean3 step3_bobStart_next)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins0
  (preKeyWire_msg_inj gamma_randTerm_ne_zero drawsMatch_singleton_single drawsMatch_aliceStart)

theorem newIndices_self (tr : ExecTrace) : newIndices tr tr = [] := by
  simp [newIndices]

theorem newIndices_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr₀ tr : ExecTrace) (e : E1) (hle : tr₀.length ≤ tr.length) :
    newIndices tr₀ (tr.append e) = newIndices tr₀ tr ++ [tr.length] := by
  unfold newIndices
  rw [length_append, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
      List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega]

theorem newRandoms_self (tr : ExecTrace) : newRandoms tr tr = [] := by
  simp [newRandoms]

theorem newRandoms_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr₀ tr : ExecTrace) (e : E1) (hle : tr₀.length ≤ tr.length) :
    newRandoms tr₀ (tr.append e) = newRandoms tr₀ tr ++
      match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option DY.Random.ExecEntryT) with
      | some r => [(randTerm tr.length r.length, r.length)]
      | none => [] := by
  unfold newRandoms
  rw [newIndices_append tr₀ tr e hle, List.filterMap_append]
  congr 1
  · apply List.filterMap_congr
    intro i hi
    unfold newIndices at hi
    have hm := List.mem_range'.mp hi
    rw [at?_append_of_lt tr e (by omega)]
  · simp only [List.filterMap_cons, List.filterMap_nil, at?_append_self]
    cases (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) <;> rfl

theorem newRandoms_t4_t5 :
    newRandoms t4 t5 = [(randTerm 22 32, 32), (randTerm 23 32, 32), (randTerm 24 32, 32)] := by
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  repeat rw [newRandoms_append t4 _ _ (by simp -failIfUnchanged only [length_append]; omega)]
  rw [newRandoms_self]; simp only [length_append, t4_length]; rfl

theorem newRandoms_encTrGen (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (cl : Nat) (pq : Bytes) :
    newRandoms tr (encTrGen tr me stH st cl pq) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cl, cl)] := by
  unfold encTrGen; dsimp only
  repeat rw [newRandoms_append tr _ _ (by simp -failIfUnchanged only [length_append]; omega)]
  rw [newRandoms_self]; simp only [length_append]; rfl

theorem newRandoms_trClean3 (cls : Nat → Nat) (idx : UInt32) :
    newRandoms (trClean2 cls) (trClean3 cls idx) = [(randTerm 45 32, 32)] := by
  have hlen2 : (trClean2 cls).length = 45 := by
    unfold trClean2 trClean1
    rw [RecvMemoTrace0.length_encTrGen, RecvMemoTrace0.length_encTrGen, t5_length]
  unfold trClean3; dsimp only
  repeat rw [newRandoms_append (trClean2 cls) _ _
    (by simp -failIfUnchanged only [length_append, hlen2]; omega)]
  rw [newRandoms_self, hlen2]; rfl

theorem newRandoms_decTr0 (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (peerDhs pq pqm m : Bytes) :
    newRandoms tr (decTr0 tr me stH st peerDhs pq pqm m) = [(randTerm tr.length 32, 32)] := by
  unfold decTr0; dsimp only
  repeat rw [newRandoms_append tr _ _ (by simp -failIfUnchanged only [length_append]; omega)]
  rw [newRandoms_self]; rfl

theorem lastSent_encTrGen (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (cl : Nat) :
    lastSent tr (encTrGen tr me stH st cl (pqKeyOf st cl tr.length)) =
      some (sendMsgOf st cl tr.length) := by
  unfold lastSent
  simp only [RecvMemoTrace0.length_encTrGen, show tr.length + 7 - 1 = tr.length + 6 by omega,
    show tr.length < tr.length + 7 by omega, ↓reduceIte]
  exact encTrGen_getMessageSentAt_msg tr me stH st cl (pqKeyOf st cl tr.length) rfl

def isNotPqExposure (o : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) : Bool :=
  match o with
  | none => true
  | some x =>
    match x.ev with
    | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedOPK .. | .CompromisedPQSPK .. => false
    | _ => true

def isNotTrExposure (o : Option (DY.ProtocolEvent.ExecEntryT TREvent)) : Bool :=
  match o with
  | none => true
  | some x =>
    match x.ev with
    | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs ..
    | .ExposedCKr .. | .ExposedMK .. | .ExposedSpqr .. => false
    | _ => true

def NoExposureBetween (tr₀ tr : ExecTrace) : Prop :=
  ∀ j ∈ newIndices tr₀ tr,
    isNotPqExposure (tr.at? j) = true ∧ isNotTrExposure (tr.at? j) = true

theorem noExposureBetween_self (tr : ExecTrace) : NoExposureBetween tr tr := by
  intro j hj; rw [newIndices_self] at hj; cases hj

theorem noExposureBetween_append {E1 : Type} [ExecTraceTypes.Has E1]
    {tr₀ tr : ExecTrace} (e : E1) (hle : tr₀.length ≤ tr.length)
    (hprev : NoExposureBetween tr₀ tr)
    (hpq : isNotPqExposure
             (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
               Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = true)
    (htr : isNotTrExposure
             (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
               Option (DY.ProtocolEvent.ExecEntryT TREvent)) = true) :
    NoExposureBetween tr₀ (tr.append e) := by
  intro j hj
  rw [newIndices_append tr₀ tr e hle, List.mem_append, List.mem_singleton] at hj
  rcases hj with hj | rfl
  · have hlt : j < tr.length := by
      unfold newIndices at hj
      have hm := List.mem_range'.mp hj; omega
    rw [at?_append_of_lt tr e hlt, at?_append_of_lt tr e hlt]
    exact hprev j hj
  · rw [at?_append_self, at?_append_self]
    exact ⟨hpq, htr⟩

theorem exposures_eq_nil_of_noExposure {tr₀ tr : ExecTrace}
    (h : NoExposureBetween tr₀ tr) : exposures tr₀ tr = [] := by
  unfold exposures
  have hpq : (newIndices tr₀ tr).filterMap (pqExposureAt tr) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro j hj
    have hj_ok := (h j hj).1
    unfold pqExposureAt
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    cases hat : (tr.at? j : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with
    | none => rfl
    | some x =>
      rw [hat] at hj_ok; unfold isNotPqExposure at hj_ok; dsimp only at hj_ok ⊢
      generalize x.ev = ev at hj_ok ⊢
      cases ev <;> first | rfl | cases hj_ok
  have htr : (newIndices tr₀ tr).filterMap (trExposureAt tr) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro j hj
    have hj_ok := (h j hj).2
    unfold trExposureAt
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    cases hat : (tr.at? j : Option (DY.ProtocolEvent.ExecEntryT TREvent)) with
    | none => rfl
    | some x =>
      rw [hat] at hj_ok; unfold isNotTrExposure at hj_ok; dsimp only at hj_ok ⊢
      generalize x.ev = ev at hj_ok ⊢
      cases ev <;> first | rfl | cases hj_ok
  rw [hpq, htr]; rfl

theorem exposures_t4_t5 : exposures t4 t5 = [] := by
  apply exposures_eq_nil_of_noExposure
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  repeat refine noExposureBetween_append _ (by simp -failIfUnchanged only [length_append]; omega) ?_ rfl rfl
  exact noExposureBetween_self t4

theorem exposures_encTrGen (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (cl : Nat) (pq : Bytes) :
    exposures tr (encTrGen tr me stH st cl pq) = [] := by
  apply exposures_eq_nil_of_noExposure
  unfold encTrGen; dsimp only
  repeat refine noExposureBetween_append _ (by simp -failIfUnchanged only [length_append]; omega) ?_ rfl rfl
  exact noExposureBetween_self tr

theorem exposures_trClean3 (cls : Nat → Nat) (idx : UInt32) :
    exposures (trClean2 cls) (trClean3 cls idx) = [] := by
  apply exposures_eq_nil_of_noExposure
  unfold trClean3; dsimp only
  repeat refine noExposureBetween_append _ (by simp -failIfUnchanged only [length_append]; omega) ?_ rfl rfl
  exact noExposureBetween_self _

theorem exposures_decTr0 (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (peerDhs pq pqm m : Bytes) :
    exposures tr (decTr0 tr me stH st peerDhs pq pqm m) = [] := by
  apply exposures_eq_nil_of_noExposure
  unfold decTr0; dsimp only
  repeat refine noExposureBetween_append _ (by simp -failIfUnchanged only [length_append]; omega) ?_ rfl rfl
  exact noExposureBetween_self tr

def aliceDonePairs (tr : ExecTrace) : List (Bytes × Bytes) :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt PQXDHEvent i with
    | some (.AliceDone _ _ _ _ _ _ _ ek ct _) => some (ek, ct)
    | _ => none

theorem aliceDonePairs_nil : aliceDonePairs Trace.nil = [] := by
  rw [aliceDonePairs, Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

theorem aliceDonePairs_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    aliceDonePairs (tr.append e) = aliceDonePairs tr ++
      match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with
      | some ⟨.AliceDone _ _ _ _ _ _ _ ek ct _⟩ => [(ek, ct)]
      | _ => [] := by
  unfold aliceDonePairs
  rw [length_append, List.range_succ, List.filterMap_append]
  congr 1
  · apply List.filterMap_congr
    intro i hi
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt tr e (List.mem_range.mp hi)]
  · simp only [List.filterMap_cons, List.filterMap_nil,
      Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self]
    cases h : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with
    | none => rfl
    | some x => cases x with | mk ev => cases ev <;> rfl

theorem aliceDonePairs_t5 : aliceDonePairs t5 = [(o1.ek, o1.ct)] := by
  have ht4 : aliceDonePairs t4 = [] := by
    rw [t4_eq_pure]
    simp only [t4Pure, t3Pure, t2Pure, t1Pure,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr,
      aliceDonePairs_append, aliceDonePairs_nil]
    rfl
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  simp only [aliceDonePairs_append, ht4]
  rfl

theorem aliceDonePairs_trClean1 (cls : Nat → Nat) :
    aliceDonePairs (trClean1 cls) = [(o1.ek, o1.ct)] := by
  unfold trClean1 encTrGen; dsimp only
  simp only [aliceDonePairs_append, aliceDonePairs_t5]
  rfl

theorem pendingPreKey_mem_aliceDonePairs {tr : ExecTrace} {stateIdx : Nat} {ek ct : Bytes}
    (h : pendingPreKey tr stateIdx = some (ek, ct)) :
    (ek, ct) ∈ aliceDonePairs tr := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt at h
  rcases hat : (tr.at? stateIdx : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState))) with _ | e
  · simp [hat] at h
  · rw [hat] at h; dsimp only [Option.map, Option.bind] at h
    split at h
    · cases h
    · obtain ⟨ev, hev_mem, hmatch⟩ := List.exists_of_findSome?_eq_some h
      unfold DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hev_mem
      obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hev_mem
      split at hi
      · rename_i s d _
        split at hi
        · cases ev <;> try cases hmatch
          have hd_lt : d < tr.length := by
            by_contra hge
            have hnone : (tr.at? d : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
              simp [Trace.at?, hge]
            rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hnone] at hi
            cases hi
          unfold aliceDonePairs
          rw [List.mem_filterMap]
          exact ⟨d, List.mem_range.mpr hd_lt, by rw [hi]⟩
        · cases hi
      · cases hi

theorem matchesEventsAt_nil_vis {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {vis : List VisEntry}
    (hm : MatchesEventsAt evictedI0 r S g initIds tr [] [] vis) :
    vis = [] := by
  generalize hss : ([] : List Step) = ss at hm
  generalize hevs : ([] : List CliEvent) = evs at hm
  cases hm with
  | nil => rfl
  | env => cases hevs
  | run0 => cases hevs
  | run1 => cases hevs

theorem matchesEventsAt_party_cons {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {s : Step} {ss : List Step}
    {e : RunEvent} {evs : List CliEvent} {vis visAll : List VisEntry}
    (hparty : s.cls = .party) (hnotRej : ¬ RunRejected e)
    (hm : MatchesEventsAt evictedI0 r S g initIds tr (s :: ss) (.run e :: evs) vis)
    (hsub : ∀ w ∈ vis, w ∈ visAll) :
    ∃ v vs,
      vis = v ++ vs ∧
      RunMatches evictedI0 r S g tr s e v initIds ∧
      (∀ w ∈ v, w ∈ visAll) ∧
      (∀ w ∈ vs, w ∈ visAll) ∧
      MatchesEventsAt evictedI0 r S g (nextBundleIds initIds e) (s.next tr) ss evs vs := by
  generalize hss_eq : s :: ss = ss_full at hm
  generalize hevs_eq : CliEvent.run e :: evs = evs_full at hm
  cases hm with
  | nil => cases hevs_eq
  | env => cases hevs_eq
  | run0 _ hrej _ =>
    injection hevs_eq with he_eq _
    injection he_eq with he_eq'
    subst he_eq'
    exact False.elim (hnotRej hrej)
  | @run1 _ _ pre s' ss' e' evs' v vs hinv hrm hrest =>
    injection hevs_eq with he_eq hevs_tail
    injection he_eq with he_eq'
    subst he_eq' hevs_tail
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hss_eq
      obtain ⟨rfl, rfl⟩ := hss_eq
      exact ⟨v, vs, rfl, hrm,
        fun w hw => hsub w (List.mem_append_left _ hw),
        fun w hw => hsub w (List.mem_append_right _ hw), hrest⟩
    | cons p0 pre' =>
      simp only [List.cons_append, List.cons.injEq] at hss_eq
      obtain ⟨hp0, _⟩ := hss_eq
      have hinv0 := hinv p0 List.mem_cons_self
      rw [← hp0, hparty] at hinv0; cases hinv0

/-- Concrete `dagBytes` equations for setup randomness, Call 0 (`aliceStart`) coins, Bob's Kyber
public key, and Alice's handshake outputs `(o1.ek, o1.ct)`. -/
structure SetupAndCall0Pinned (S : OpaqueSymbolSemantics) (g : Ghost) : Prop where
  sig0  : g.σ 0 32 = dagBytes 21
  sig5  : g.σ 5 32 = dagBytes 22
  sig10 : g.σ 10 32 = dagBytes 23
  sig11 : g.σ 11 64 = dagBytes 24
  sig16 : g.σ 16 64 = dagBytes 25
  sig17 : g.σ 17 64 = dagBytes 26
  sig22 : g.σ 22 32 = dagBytes 65
  sig23 : g.σ 23 32 = dagBytes 66
  sig24 : g.σ 24 32 = dagBytes 67
  pqpk  : gamma evictedI0 S g (DY.PQKem.kemPk (randTerm 16 64)) = dagBytes 71
  ek0   : gamma evictedI0 S g o1.ek = dagBytes 68
  ct0   : gamma evictedI0 S g o1.ct = dagBytes 73

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private def ev0CoinsChars : List Char := nfe_chars_of_hex (ev 0).coins
private def ev0CoinsFast : HwBytes := hexBytes.go hexDigit ev0CoinsChars

private theorem ev0Coins_eq : (ev 0).coins = ev0CoinsFast := by
  have h1 : (ev 0).coins = hexBytes (nfe_str_of_hex (ev 0).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 0).coins) = String.ofList ev0CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private theorem ev0_coins_22_24 :
    ev0CoinsFast.take 32 = dagBytes 65 ∧
    (ev0CoinsFast.drop 160).take 32 = dagBytes 67 ∧
    (dagBytes 66).length = 32 ∧
    ((List.range 32).all fun j => (dagBytes 66)[j]? == ev0CoinsFast[32 + 4 * j]?) = true ∧
    (compKyberEncaps (dagBytes 66)).take 1568 = dagBytes 73 := by
  decide +kernel

/-- Extracts `SetupAndCall0Pinned` and empty `.send` and `.pt` visible-entry slices from
`GhostAndSemMatchSetup` and Call 0 `RunMatches`. -/
theorem peel_setup_and_call0 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {v0 visAll : List VisEntry}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hsetup : GhostAndSemMatchSetup evictedI0 r S g)
    (hgwf : GhostWF g visAll)
    (hrm0 : RunMatches evictedI0 r S g t4 (Step.aliceStart "alice" "bob" 4 6 bh1) (ev 0) v0 none)
    (hv0 : ∀ w ∈ v0, w ∈ visAll) :
    SetupAndCall0Pinned S g ∧
    (v0.filter (·.kind == .send)).flatMap (·.terms) = [] ∧
    plaintextTerms v0 = [] ∧
    nextBundleIds none (ev 0) = some (bundlePreKeyIds (ev 0).input) := by
  have hopk : r.withOpk = false := r_withOpk_eq hfit
  have hs0 : secretBytes r 0 = w0.aliceId := hfit.1.1.2.2.2.2.2.2.1
  have hs1 : secretBytes r 1 = w0.bobId := hfit.1.1.2.2.2.2.2.2.2.1
  have hs2 : secretBytes r 2 = w0.spk := hfit.1.1.2.2.2.2.2.2.2.2.1
  have hopq6 : r.opaqueBytes (setupPublic r 6) = w0.kyberPk :=
    hfit.1.1.2.2.2.2.2.2.2.2.2.2.1
  have hs3 : secretBytes r 3 = fillFresh 11 64 := r_secret3_eq hfit
  have hs4 : secretBytes r 4 = fillFresh 16 64 := r_secret4_eq hfit
  have hs5 : secretBytes r 5 = fillFresh 17 64 := r_secret5_eq hfit
  have hnames := Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace.r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  have hrands : setupRandomsAt r = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe, hopk]; rfl
  have hsec_fresh : ∀ (k : Nat) (p : Nat × Nat), (setupRandomsAt r)[k]? = some p →
      secretBytes r k = r.fresh p.1 p.2 := by
    intro k p hk; unfold secretBytes; rw [hk]; rfl
  have hsig0 : g.σ 0 32 = dagBytes 21 := by
    rw [hsetup.1 (0, 32) (by rw [hrands]; decide),
        ← hsec_fresh 0 (0, 32) (by rw [hrands]; rfl), hs0]
    decide +kernel
  have hsig5 : g.σ 5 32 = dagBytes 22 := by
    rw [hsetup.1 (5, 32) (by rw [hrands]; decide),
        ← hsec_fresh 1 (5, 32) (by rw [hrands]; rfl), hs1]
    decide +kernel
  have hsig10 : g.σ 10 32 = dagBytes 23 := by
    rw [hsetup.1 (10, 32) (by rw [hrands]; decide),
        ← hsec_fresh 2 (10, 32) (by rw [hrands]; rfl), hs2]
    decide +kernel
  have hsig11 : g.σ 11 64 = dagBytes 24 := by
    rw [hsetup.1 (11, 64) (by rw [hrands]; decide),
        ← hsec_fresh 3 (11, 64) (by rw [hrands]; rfl), hs3]
    decide +kernel
  have hsig16 : g.σ 16 64 = dagBytes 25 := by
    rw [hsetup.1 (16, 64) (by rw [hrands]; decide),
        ← hsec_fresh 4 (16, 64) (by rw [hrands]; rfl), hs4]
    decide +kernel
  have hsig17 : g.σ 17 64 = dagBytes 26 := by
    rw [hsetup.1 (17, 64) (by rw [hrands]; decide),
        ← hsec_fresh 5 (17, 64) (by rw [hrands]; rfl), hs5]
    decide +kernel
  have hpqpk : gamma evictedI0 S g (DY.PQKem.kemPk (randTerm 16 64)) = dagBytes 71 := by
    have hpub6 : setupPublic r 6 = DY.PQKem.kemPk (randTerm 16 64) := by
      rw [setupPublic_eq_r0 hfit]
      exact setupPublic_6 (r := r0) (by decide)
    have h6 : gamma evictedI0 S g (setupPublic r 6) = r.opaqueBytes (setupPublic r 6) :=
      hsetup.2.1 r.pqpkPubTerm (by simp)
    rw [← hpub6, h6, hopq6]
    decide +kernel
  obtain ⟨_, _, _, _, hok0, _, hv0_eq, inp0, drs0, outs0, hv0_split, _, hdrs0, houts0, _, _⟩ := hrm0
  have houts0_nil : outs0 = [] := by
    unfold OutputsMatch at houts0
    have ⟨a0, b0, hcmd0⟩ : ∃ a0 b0, (ev 0).cmd = .init a0 b0 := ⟨_, _, rfl⟩
    rw [hcmd0] at houts0
    cases (ev 0).exit <;> exact houts0
  rw [houts0_nil, List.append_nil] at hv0_split
  unfold stepView at hv0_eq
  simp only [hok0, ↓reduceIte] at hv0_eq
  rw [step0_next_t4, exposures_t4_t5, List.append_nil] at hv0_eq
  unfold aliceVis at hv0_eq
  rw [newRandoms_t4_t5] at hv0_eq
  dsimp only [List.map, aliceDraws, List.take] at hv0_eq
  let v24 : VisEntry := { rngEntry (randTerm 24 32) with anchor := eventIdx isAliceDone t4 t5 }
  have hv0_form : v0 =
      ⟨.recv, received t4 ([bh1.spk, bh1.spkSig, bh1.pqpk, bh1.pqpkSig] ++ bh1.opk.toList),
        .bundle, none⟩ ::
      (rngEntry (randTerm 22 32) :: kyberCoinEntries (randTerm 23 32) ++ [v24]) := hv0_eq
  have hdrs0_eq : drs0 = rngEntry (randTerm 22 32) :: kyberCoinEntries (randTerm 23 32) ++ [v24] :=
    (List.cons.inj (hv0_split.symm.trans hv0_form)).2
  rw [hdrs0_eq] at hdrs0
  have hsub_drs : ∀ w ∈ rngEntry (randTerm 22 32) :: kyberCoinEntries (randTerm 23 32) ++ [v24],
      w ∈ visAll := by
    intro w hw; apply hv0; rw [hv0_form]; exact List.mem_cons_of_mem _ hw
  obtain ⟨h22, hlen23, hget23, h24⟩ :=
    drawsMatch_aliceStart hgwf hsub_drs rfl rfl rfl hdrs0
  obtain ⟨hc22, hc24, hlen66, hall66, hkct73⟩ := ev0_coins_22_24
  have hsig22 : g.σ 22 32 = dagBytes 65 := by rw [h22, ev0Coins_eq, hc22]
  have hsig24 : g.σ 24 32 = dagBytes 67 := by rw [h24, ev0Coins_eq, hc24]
  have hsig23 : g.σ 23 32 = dagBytes 66 := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < 32
    · rw [hget23 j hj, ev0Coins_eq]
      rw [List.all_eq_true] at hall66
      have hj66 := hall66 j (List.mem_range.mpr hj)
      rw [beq_iff_eq] at hj66
      exact hj66.symm
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hek0 : gamma evictedI0 S g o1.ek = dagBytes 68 := by
    dsimp only [o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [t4_length]
    exact (termAt_dhPk (S := S) dag_nodes_ok (pts := []) (by decide : 68 < dagSize) rfl
      (termAt_rand (S := S) dag_nodes_ok (by decide : 65 < dagSize) rfl hsig22)).gamma_eq
  have hct0 : gamma evictedI0 S g o1.ct = dagBytes 73 := by
    have hg23 : gamma evictedI0 S g (rnd 23 32) = dagBytes 66 := by
      change gamma evictedI0 S g (randTerm 23 32) = dagBytes 66
      rw [gamma_randTerm_ne_zero S g (by decide), hsig23]
    have helen : (gamma evictedI0 S g (rnd 23 32)).length = 32 := by rw [hg23, hlen66]
    dsimp only [o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t4_length]
    unfold gamma
    change (gamma' evictedI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).1).bytes =
      dagBytes 73
    rw [gamma'_kemEncap_of_len32 (i := evictedI0) (S := S) (g := g) helen, hg23]
    exact hkct73
  have hsend0 : (v0.filter (·.kind == .send)).flatMap (·.terms) = [] := by
    rw [hv0_form]
    simp only [List.filter_cons, List.filter_append, kyberCoinEntries, List.filter_map,
      rngEntry, v24]
    rfl
  have hpt0 : plaintextTerms v0 = [] := by
    unfold plaintextTerms; rw [hv0_form]
    simp only [List.filter_cons, List.filter_append, kyberCoinEntries, List.filter_map,
      rngEntry, v24]
    rfl
  exact ⟨⟨hsig0, hsig5, hsig10, hsig11, hsig16, hsig17, hsig22, hsig23, hsig24,
    hpqpk, hek0, hct0⟩, hsend0, hpt0, rfl⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins1
