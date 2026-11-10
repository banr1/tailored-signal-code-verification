/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.Adversary
import Init.Data.String.Defs
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

@[expose] public section

set_option autoImplicit false

/-!
# Theorem 1 Corollary Premise Tightness Traces

Provides event-absence lemmas on the shared PQXDH compromise traces and defines the KCI witness
trace `trKCI` (`trIKA` extended with `compromiseIK "bob"`) for proving tightness of the premise
conjuncts of `HandshakeForwardSecrecy`, `HNDLResistance`, `SessionIndependence`,
`PeerAuthentication`, and `KCIResistance`.
-/

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.ScopeTraces

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (advEkSk advForgedBobCt advForgedBobKeys
  advIkA advIkB advPqSk advPqskB advSetup advSpkB advSpkSk breakDHTr breakKEMTr compIkTr
  compIkTr_reach compPqTr compSpkTr forgedBobStartTr forgedBundlePrefix forgedPreKeyPrefix
  forgedPreKeyStage2 invertTr isBrokenDH isBrokenKEM isCompIK isCompIkOf isCompOPK isCompPQ
  isCompSPK logged_after_of_singleton trBrokenDHA trBrokenDHA_pre trBrokenDHB trBrokenDHB_pre
  trIKA trIKA_bobDone trIKA_compIK trIKA_pre trIKA_reach trIKB trIKB_pre trSPKB trSPKB_pre
  trThm7Case3_kem trThm7Case3_pq)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (evIdx ikA ikB mem_evIdx not_logged pqskB
  spkB t1 t1_length t2 t3 t4 t4_length t5 t5_length)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvP NetE Runs StP aliceTr aliceTrOpt
  genPQPrekeyTr genSignedPrekeyTr registerIdentityTr)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys IsHandshakeBlock SessionStateExposed LoggedBefore
  SameOPK HandshakeAuthWasCompromised ResponderSessionAgreement)

/-! ## Local trace and `evIdx` helpers -/

private theorem append_len_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E) :
    (tr.append x).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem le_append_loc {E : Type} [ExecTraceTypes.Has E] {tr1 tr2 : ExecTrace}
    (h : tr1 ≤ tr2) (x : E) : tr1 ≤ tr2.append x :=
  Trace.le_trans _ _ _ h (Trace.append_le tr2 x)

private theorem at?_mono_loc {E : Type} [ExecTraceTypes.Has E] {tr1 tr2 : ExecTrace}
    (hle : tr1 ≤ tr2) {i : Nat} {v : E} (h : tr1.at? i = some v) : tr2.at? i = some v := by
  have hi : i < tr1.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := E) tr1 i
    rwa [h] at this
  have hi2 : i < tr2.length := Nat.lt_of_lt_of_le hi (Trace.length_le tr1 tr2 hle)
  unfold Trace.at? at h ⊢
  simp only [hi, ↓reduceDIte] at h
  simp only [hi2, ↓reduceDIte]
  rwa [← Trace.at_le tr1 tr2 i hi hle]

private theorem hat_snoc_loc {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : ExecTrace.Entry) (i : Nat) :
    ((tr.snoc e).at? i : Option E) =
      (if i = tr.length then TraceEntryHas.proj e
       else if i < tr.length then tr.at? i else none) := by
  simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_2]
  by_cases h1 : i = tr.length
  · subst h1
    have hlt : tr.length < tr.length + 1 := Nat.lt_succ_self _
    simp only [hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
  · by_cases h2 : i < tr.length
    · have hlt : i < tr.length + 1 := by omega
      simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
    · have hlt : ¬ i < tr.length + 1 := by omega
      simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte]

private theorem at?_append_self_proj_loc {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc_loc, ↓reduceIte]

private theorem at?_append_of_lt_loc {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = tr.at? i := by
  have hne : i ≠ tr.length := Nat.ne_of_lt hi
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc_loc, hne, hi, ↓reduceIte]

private theorem eventLoggedAt_of_at?_loc {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {tr : ExecTrace} {ev : Ev} {i : Nat}
    (h : tr.at? i = some ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact h

private theorem eventLoggedAt_mono_loc {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {tr1 tr2 : ExecTrace} {ev : Ev} {i : Nat}
    (hle : tr1 ≤ tr2) (h : tr1.EventLoggedAt ev i) : tr2.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono_loc hle h

private theorem evIdx_nil_loc (p : PQXDHEvent → Bool) : evIdx Trace.nil p = [] := by
  simp only [evIdx, Symbolic.DYBridge.DY.Trace.length_eq_1, List.range_zero, List.filter_nil]

private theorem evIdx_append_non_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    evIdx (tr.append x) p = evIdx tr p := by
  unfold evIdx
  rw [append_len_loc, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj_loc, hnone]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt_loc tr x (List.mem_range.mp hi)]

private theorem evIdx_append_ev_loc (tr : ExecTrace) (ev : PQXDHEvent) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (EvP ev)) p = cond (p ev) (evIdx tr p ++ [tr.length]) (evIdx tr p) := by
  unfold evIdx
  rw [append_len_loc, List.range_succ, List.filter_append]
  cases hp : p ev
  · rw [List.filter_cons_of_neg (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]
        decide),
      List.filter_nil, List.append_nil]
    exact List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt_loc tr (EvP ev) (List.mem_range.mp hi)]
  · rw [List.filter_cons_of_pos (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]),
      List.filter_nil]
    exact congrArg (· ++ [tr.length]) (List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt_loc tr (EvP ev) (List.mem_range.mp hi)])

private theorem evIdx_aliceTrOpt_false_loc (tr : ExecTrace) (a b : Participant)
    (ikA' ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) (p : PQXDHEvent → Bool)
    (hp : ∀ x1 x2 x3 x4 x5 x6 x7 x8,
      p (.AliceDone a b x1 x2 x3 x4 x5 x6 x7 x8) = false) :
    evIdx (aliceTrOpt tr a b ikA' ikBPk spkPk pqPk opkPk) p = evIdx tr p := by
  dsimp only [aliceTrOpt]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc, hp, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl]

private theorem evIdx_forgedBundlePrefix_loc (tr : ExecTrace) (ik : Bytes)
    (p : PQXDHEvent → Bool) :
    evIdx (forgedBundlePrefix tr ik) p = evIdx tr p := by
  dsimp only [forgedBundlePrefix]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl]

private theorem evIdx_forgedPreKeyPrefix_loc (tr : ExecTrace) (x1 x2 x3 x4 : Bytes)
    (p : PQXDHEvent → Bool) :
    evIdx (forgedPreKeyPrefix tr x1 x2 x3 x4) p = evIdx tr p := by
  dsimp only [forgedPreKeyPrefix, forgedPreKeyStage2]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl]

private theorem evIdx_forgedBobStartTr_false_loc (trPre : ExecTrace) (b a : Participant)
    (x1 x2 x3 x4 : Bytes) (p : PQXDHEvent → Bool)
    (hp : ∀ y1 y2 y3 y4 y5 y6 y7 y8,
      p (.BobDone b a y1 y2 y3 y4 y5 y6 y7 y8) = false) :
    evIdx (forgedBobStartTr trPre b a x1 x2 x3 x4) p = evIdx trPre p := by
  dsimp only [forgedBobStartTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, hp, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl]

private theorem someEventB_of_evIdx_nil_loc {tr : ExecTrace} {p : PQXDHEvent → Bool}
    (h : evIdx tr p = []) : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_false]
  intro i hi
  cases hat : (tr.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => dsimp only; exact Bool.false_ne_true
  | some ev =>
    dsimp only
    cases hp : p ev.ev
    · exact Bool.false_ne_true
    · intro _
      have hmem : i ∈ evIdx tr p := mem_evIdx (eventLoggedAt_of_at?_loc hat) hp
      rw [h] at hmem
      exact List.not_mem_nil hmem

private theorem t1_eq_loc : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (by
    simp only [Bool.not_eq_true']
    exact someEventB_of_evIdx_nil_loc (evIdx_nil_loc _))).2

private theorem t2_eq_loc : t2 = registerIdentityTr t1 "bob" :=
  (Runs.registerIdentity (by
    simp only [Bool.not_eq_true']
    refine someEventB_of_evIdx_nil_loc ?_
    rw [t1_eq_loc]; dsimp only [registerIdentityTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc]
    dsimp only
    rw [show ("alice" == "bob") = false by decide,
      Bool.cond_false, evIdx_append_non_loc _ _ _ rfl, evIdx_nil_loc])).2

private theorem t3_eq_loc : t3 = genSignedPrekeyTr t2 "bob" ikB :=
  (Runs.genSignedPrekey (by
    rw [t2_eq_loc]
    simp only [registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc_loc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t1_length, ↓reduceIte]
    rfl)).2

private theorem t4_eq_loc : t4 = genPQPrekeyTr t3 "bob" ikB :=
  (Runs.genPQPrekey (by
    rw [t3_eq_loc, t2_eq_loc]
    simp only [genSignedPrekeyTr, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      hat_snoc_loc, Symbolic.DYBridge.DY.Trace.length_eq_2, t1_length, ↓reduceIte]
    rfl)).2

private theorem t4_at?_9_loc :
    t4.at? 9 = some (StP "bob" { kind := .identity, sk := advIkB }) := by
  rw [t4_eq_loc, t3_eq_loc, t2_eq_loc, t1_eq_loc]
  simp only [genPQPrekeyTr, genSignedPrekeyTr, registerIdentityTr,
    Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc_loc,
    Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1, ↓reduceIte]
  rfl

private theorem evIdx_t4_false_loc (p : PQXDHEvent → Bool)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx t4 p = [] := by
  rw [t4_eq_loc]; dsimp only [genPQPrekeyTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc, h3, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl]
  rw [t3_eq_loc]; dsimp only [genSignedPrekeyTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc, h2, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl]
  rw [t2_eq_loc]; dsimp only [registerIdentityTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc, h1, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl]
  rw [t1_eq_loc]; dsimp only [registerIdentityTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc, h1, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl, evIdx_nil_loc]

private theorem evIdx_t5_false_loc (p : PQXDHEvent → Bool)
    (ha : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.AliceDone "alice" "bob" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx t5 p = [] := by
  dsimp only [t5, aliceTr]
  rw [evIdx_aliceTrOpt_false_loc _ _ _ _ _ _ _ _ _ ha]
  exact evIdx_t4_false_loc p h1 h2 h3

private theorem evIdx_trIKA_false_loc (p : PQXDHEvent → Bool)
    (hc : p (.CompromisedIK "alice" (dhPk advIkA)) = false)
    (hb : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.BobDone "bob" "alice" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx trIKA p = [] := by
  dsimp only [trIKA, trIKA_pre, compIkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false_loc _ _ _ _ _ _ _ _ hb,
    evIdx_forgedPreKeyPrefix_loc, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, hc, Bool.cond_false]
  exact evIdx_t4_false_loc p h1 h2 h3

private theorem evIdx_trIKB_false_loc (p : PQXDHEvent → Bool)
    (hc : p (.CompromisedIK "bob" (dhPk advIkB)) = false)
    (ha : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.AliceDone "alice" "bob" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx trIKB p = [] := by
  dsimp only [trIKB, aliceTr, trIKB_pre, compIkTr, advSetup]
  rw [evIdx_aliceTrOpt_false_loc _ _ _ _ _ _ _ _ _ ha,
    evIdx_forgedBundlePrefix_loc, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, hc, Bool.cond_false]
  exact evIdx_t4_false_loc p h1 h2 h3

private theorem evIdx_trSPKB_false_loc (p : PQXDHEvent → Bool)
    (hc : p (.CompromisedSPK "bob" (dhPk advSpkB)) = false)
    (hb : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.BobDone "bob" "alice" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx trSPKB p = [] := by
  dsimp only [trSPKB, trSPKB_pre, compSpkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false_loc _ _ _ _ _ _ _ _ hb,
    evIdx_forgedPreKeyPrefix_loc, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, hc, Bool.cond_false]
  exact evIdx_t4_false_loc p h1 h2 h3

private theorem evIdx_trBrokenDHA_false_loc (p : PQXDHEvent → Bool)
    (hc : p .BrokenDH = false)
    (ha : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.AliceDone "alice" "bob" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx trBrokenDHA p = [] := by
  dsimp only [trBrokenDHA, aliceTr, trBrokenDHA_pre, invertTr, breakDHTr, advSetup]
  rw [evIdx_aliceTrOpt_false_loc _ _ _ _ _ _ _ _ _ ha,
    evIdx_forgedBundlePrefix_loc, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, hc, Bool.cond_false]
  exact evIdx_t4_false_loc p h1 h2 h3

private theorem evIdx_trBrokenDHB_false_loc (p : PQXDHEvent → Bool)
    (hc : p .BrokenDH = false)
    (hb : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.BobDone "bob" "alice" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx trBrokenDHB p = [] := by
  dsimp only [trBrokenDHB, trBrokenDHB_pre, invertTr, breakDHTr, advSetup]
  rw [evIdx_forgedBobStartTr_false_loc _ _ _ _ _ _ _ _ hb,
    evIdx_forgedPreKeyPrefix_loc, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, hc, Bool.cond_false]
  exact evIdx_t4_false_loc p h1 h2 h3

/-! ## Event-absence lemmas on compromise traces -/

abbrev isAnyAliceDone : PQXDHEvent → Bool :=
  fun | .AliceDone .. => true | _ => false

theorem not_thm8Agreement_of_no_aliceDone {tr : ExecTrace}
    (hidx : evIdx tr isAnyAliceDone = [])
    (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes) (i : Nat) :
    ¬ ResponderSessionAgreement a spk pqpk opk i tr := by
  rintro ⟨b', ikA', ikB', spk', opk', ek', ct', keys', j, hj, _⟩
  exact not_logged hidx (e := .AliceDone a b' ikA' ikB' spk' pqpk opk' ek' ct' keys') rfl ⟨j, hj⟩

theorem trIKA_no_compIK_bob :
    ¬ trIKA.EventLogged (PQXDHEvent.CompromisedIK "bob" (dhPk advIkB)) :=
  not_logged (p := isCompIkOf "bob")
    (evIdx_trIKA_false_loc _ (by decide) (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKA_no_compSPK (s : Bytes) :
    ¬ trIKA.EventLogged (PQXDHEvent.CompromisedSPK "bob" s) :=
  not_logged (p := isCompSPK)
    (evIdx_trIKA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKA_no_compPQ (q : Bytes) :
    ¬ trIKA.EventLogged (PQXDHEvent.CompromisedPQSPK "bob" q) :=
  not_logged (p := isCompPQ)
    (evIdx_trIKA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKA_no_compOPK (o : Bytes) :
    ¬ trIKA.EventLogged (PQXDHEvent.CompromisedOPK "bob" o) :=
  not_logged (p := isCompOPK)
    (evIdx_trIKA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKA_no_brokenDH :
    ¬ trIKA.EventLogged PQXDHEvent.BrokenDH :=
  not_logged (p := isBrokenDH)
    (evIdx_trIKA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKA_no_brokenKEM :
    ¬ trIKA.EventLogged PQXDHEvent.BrokenKEM :=
  not_logged (p := isBrokenKEM)
    (evIdx_trIKA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKA_no_thm8Agreement :
    ¬ ResponderSessionAgreement "alice" (dhPk advSpkB) (kemPk advPqskB) none 29 trIKA :=
  not_thm8Agreement_of_no_aliceDone
    (evIdx_trIKA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) _ _ _ _ _

theorem trIKB_no_compIK_alice :
    ¬ trIKB.EventLogged (PQXDHEvent.CompromisedIK "alice" (dhPk advIkA)) :=
  not_logged (p := isCompIkOf "alice")
    (evIdx_trIKB_false_loc _ (by decide) (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKB_no_compSPK (s : Bytes) :
    ¬ trIKB.EventLogged (PQXDHEvent.CompromisedSPK "bob" s) :=
  not_logged (p := isCompSPK)
    (evIdx_trIKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKB_no_compPQ (q : Bytes) :
    ¬ trIKB.EventLogged (PQXDHEvent.CompromisedPQSPK "bob" q) :=
  not_logged (p := isCompPQ)
    (evIdx_trIKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKB_no_compOPK (o : Bytes) :
    ¬ trIKB.EventLogged (PQXDHEvent.CompromisedOPK "bob" o) :=
  not_logged (p := isCompOPK)
    (evIdx_trIKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKB_no_brokenDH :
    ¬ trIKB.EventLogged PQXDHEvent.BrokenDH :=
  not_logged (p := isBrokenDH)
    (evIdx_trIKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trIKB_no_brokenKEM :
    ¬ trIKB.EventLogged PQXDHEvent.BrokenKEM :=
  not_logged (p := isBrokenKEM)
    (evIdx_trIKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trSPKB_no_compIK (p : Participant) (ik : Bytes) :
    ¬ trSPKB.EventLogged (PQXDHEvent.CompromisedIK p ik) :=
  not_logged (p := isCompIK)
    (evIdx_trSPKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trSPKB_no_compPQ (q : Bytes) :
    ¬ trSPKB.EventLogged (PQXDHEvent.CompromisedPQSPK "bob" q) :=
  not_logged (p := isCompPQ)
    (evIdx_trSPKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trSPKB_no_compOPK (o : Bytes) :
    ¬ trSPKB.EventLogged (PQXDHEvent.CompromisedOPK "bob" o) :=
  not_logged (p := isCompOPK)
    (evIdx_trSPKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trSPKB_no_brokenDH :
    ¬ trSPKB.EventLogged PQXDHEvent.BrokenDH :=
  not_logged (p := isBrokenDH)
    (evIdx_trSPKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trSPKB_no_brokenKEM :
    ¬ trSPKB.EventLogged PQXDHEvent.BrokenKEM :=
  not_logged (p := isBrokenKEM)
    (evIdx_trSPKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trSPKB_no_thm8Agreement :
    ¬ ResponderSessionAgreement "alice" (dhPk advSpkB) (kemPk advPqskB) none 29 trSPKB :=
  not_thm8Agreement_of_no_aliceDone
    (evIdx_trSPKB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) _ _ _ _ _

theorem trBrokenDHA_no_compIK (p : Participant) (ik : Bytes) :
    ¬ trBrokenDHA.EventLogged (PQXDHEvent.CompromisedIK p ik) :=
  not_logged (p := isCompIK)
    (evIdx_trBrokenDHA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trBrokenDHA_no_compSPK (s : Bytes) :
    ¬ trBrokenDHA.EventLogged (PQXDHEvent.CompromisedSPK "bob" s) :=
  not_logged (p := isCompSPK)
    (evIdx_trBrokenDHA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trBrokenDHA_no_compPQ (q : Bytes) :
    ¬ trBrokenDHA.EventLogged (PQXDHEvent.CompromisedPQSPK "bob" q) :=
  not_logged (p := isCompPQ)
    (evIdx_trBrokenDHA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trBrokenDHA_no_compOPK (o : Bytes) :
    ¬ trBrokenDHA.EventLogged (PQXDHEvent.CompromisedOPK "bob" o) :=
  not_logged (p := isCompOPK)
    (evIdx_trBrokenDHA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trBrokenDHA_no_brokenKEM :
    ¬ trBrokenDHA.EventLogged PQXDHEvent.BrokenKEM :=
  not_logged (p := isBrokenKEM)
    (evIdx_trBrokenDHA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trBrokenDHB_no_compIK (p : Participant) (ik : Bytes) :
    ¬ trBrokenDHB.EventLogged (PQXDHEvent.CompromisedIK p ik) :=
  not_logged (p := isCompIK)
    (evIdx_trBrokenDHB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trBrokenDHB_no_compSPK (s : Bytes) :
    ¬ trBrokenDHB.EventLogged (PQXDHEvent.CompromisedSPK "bob" s) :=
  not_logged (p := isCompSPK)
    (evIdx_trBrokenDHB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trBrokenDHB_no_thm8Agreement :
    ¬ ResponderSessionAgreement "alice" (dhPk advSpkB) (kemPk advPqskB) none 29 trBrokenDHB :=
  not_thm8Agreement_of_no_aliceDone
    (evIdx_trBrokenDHB_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) _ _ _ _ _

private theorem evIdx_trThm7Case3_kem_loc (p : PQXDHEvent → Bool)
    (hkem : p .BrokenKEM = false)
    (ha : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.AliceDone "alice" "bob" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx trThm7Case3_kem p = cond (p .BrokenDH) [31] [] := by
  dsimp only [trThm7Case3_kem, invertTr, breakKEMTr, breakDHTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc, hkem, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, evIdx_t5_false_loc p ha h1 h2 h3, t5_length]
  cases p .BrokenDH <;> rfl

private theorem evIdx_trThm7Case3_pq_loc (p : PQXDHEvent → Bool)
    (hpq : p (.CompromisedPQSPK "bob" (kemPk pqskB)) = false)
    (ha : ∀ x1 x2 x3 x4 x5 x6 x7 x8, p (.AliceDone "alice" "bob" x1 x2 x3 x4 x5 x6 x7 x8) = false)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx trThm7Case3_pq p = cond (p .BrokenDH) [31] [] := by
  dsimp only [trThm7Case3_pq, compPqTr, invertTr, breakDHTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc, hpq, Bool.cond_false,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_ev_loc, evIdx_t5_false_loc p ha h1 h2 h3, t5_length]
  cases p .BrokenDH <;> rfl

theorem trThm7Case3_kem_dh_after :
    ∀ j, trThm7Case3_kem.EventLoggedAt PQXDHEvent.BrokenDH j → 27 < j :=
  logged_after_of_singleton (p := isBrokenDH) (k := 31)
    (evIdx_trThm7Case3_kem_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl (by omega)

theorem trThm7Case3_kem_no_compIK (p : Participant) (ik : Bytes) :
    ¬ trThm7Case3_kem.EventLogged (PQXDHEvent.CompromisedIK p ik) :=
  not_logged (p := isCompIK)
    (evIdx_trThm7Case3_kem_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trThm7Case3_kem_no_compSPK (s : Bytes) :
    ¬ trThm7Case3_kem.EventLogged (PQXDHEvent.CompromisedSPK "bob" s) :=
  not_logged (p := isCompSPK)
    (evIdx_trThm7Case3_kem_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trThm7Case3_kem_no_compPQ (q : Bytes) :
    ¬ trThm7Case3_kem.EventLogged (PQXDHEvent.CompromisedPQSPK "bob" q) :=
  not_logged (p := isCompPQ)
    (evIdx_trThm7Case3_kem_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trThm7Case3_pq_dh_after :
    ∀ j, trThm7Case3_pq.EventLoggedAt PQXDHEvent.BrokenDH j → 27 < j :=
  logged_after_of_singleton (p := isBrokenDH) (k := 31)
    (evIdx_trThm7Case3_pq_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl (by omega)

theorem trThm7Case3_pq_no_brokenKEM :
    ¬ trThm7Case3_pq.EventLogged PQXDHEvent.BrokenKEM :=
  not_logged (p := isBrokenKEM)
    (evIdx_trThm7Case3_pq_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trThm7Case3_pq_no_compIK (p : Participant) (ik : Bytes) :
    ¬ trThm7Case3_pq.EventLogged (PQXDHEvent.CompromisedIK p ik) :=
  not_logged (p := isCompIK)
    (evIdx_trThm7Case3_pq_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

theorem trThm7Case3_pq_no_compSPK (s : Bytes) :
    ¬ trThm7Case3_pq.EventLogged (PQXDHEvent.CompromisedSPK "bob" s) :=
  not_logged (p := isCompSPK)
    (evIdx_trThm7Case3_pq_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) rfl

/-! ## KCI witness trace `trKCI` -/

/-- `trIKA` extended with `compromiseIK "bob"` after `BobDone`. -/
def trKCI : ExecTrace := compIkTr trIKA "bob" advIkB

theorem trKCI_reach : trKCI.Reachable reachability :=
  compIkTr_reach (idx := 9) trIKA_reach (by
    refine at?_mono_loc ?_ t4_at?_9_loc
    dsimp only [trIKA, forgedBobStartTr, trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2,
      compIkTr, advSetup]
    iterate 14 refine le_append_loc ?_ _
    exact Trace.le_refl _)

theorem trKCI_bobDone :
    trKCI.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
        none (dhPk advEkSk) advForgedBobCt advForgedBobKeys) 29 :=
  eventLoggedAt_mono_loc (le_append_loc (le_append_loc (Trace.le_refl _) _) _) trIKA_bobDone

theorem trKCI_compIK_alice :
    trKCI.EventLoggedAt (PQXDHEvent.CompromisedIK "alice" (dhPk advIkA)) 22 :=
  eventLoggedAt_mono_loc (le_append_loc (le_append_loc (Trace.le_refl _) _) _) trIKA_compIK

theorem trKCI_compIK_bob :
    trKCI.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk advIkB)) 36 := by
  have hlen : trIKA.length = 36 := by
    dsimp only [trIKA, forgedBobStartTr, trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2,
      compIkTr, advSetup]
    simp only [append_len_loc, t4_length]
  refine eventLoggedAt_mono_loc (Trace.append_le _ _) (eventLoggedAt_of_at?_loc ?_)
  exact hlen ▸ Trace.at?_append trIKA (EvP (.CompromisedIK "bob" (dhPk advIkB)))

theorem trKCI_no_thm8Agreement :
    ¬ ResponderSessionAgreement "alice" (dhPk advSpkB) (kemPk advPqskB) none 29 trKCI :=
  not_thm8Agreement_of_no_aliceDone (by
    dsimp only [trKCI, compIkTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc,
      show isAnyAliceDone (.CompromisedIK "bob" (dhPk advIkB)) = false from rfl, Bool.cond_false]
    exact evIdx_trIKA_false_loc _ rfl (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) _ _ _ _ _

theorem trKCI_thm8Excuse :
    HandshakeAuthWasCompromised "bob" "alice" (dhPk advIkA) (dhPk advSpkB) 29 trKCI :=
  .inl ⟨22, trKCI_compIK_alice, by omega⟩

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.ScopeTraces
