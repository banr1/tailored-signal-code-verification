/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
import DY.Trace.Basic
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean Schedule Visible Entries

Defines the visible-entry list `visClean r cls m` produced by running `ssClean cls cleanSpqrIdxs m`
from `setupTrace r`, and computes explicit `stepView` formulas for Calls `0..2` (`aliceStart` and
Alice's two `messageEncrypt` steps).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.PQXDH (PQXDHEvent encodeEC encodeKEM)
open DY.Libsignal.TripleRatchet (TRState TREvent kdfCk)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Step VisEntry setupTrace runTrace runSteps stepView
   aliceVis pendingPreKey sessionHasDecrypted
   newIndices newRandoms received eventIdx isAliceDone
   exposures pqExposureAt trExposureAt rngEntry kyberCoinEntries randTerm
   runWrapped)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs RndE NetE EvP EvT EvC StP StT rnd encSt
   aliceTr aliceTrOpt registerIdentityTr genSignedPrekeyTr genPQPrekeyTr)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB spkNonce pqskB pqNonce dhsA
   t1 t2 t3 t4 t5
   t1_length t2_length t3_length t4_length t5_length
   bh1 o1 stA0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (cleanCallSteps ssClean cleanCallSteps_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs append_len le_append_of_le at?_mono
   at?_append_at at?_append_self_proj at?_append_of_lt
   encTrGen encTrGen_length encTrGen_le
   coins1Clean stA1Clean m1Clean trClean2 trClean2_length
   m2Clean s0_next_ok s1_next_ok s2_next_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSend
  (encTrGen_stepView_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
  (ssClean_succ)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

/-- Concatenated `stepView` visible entries across a step list starting at event index `j` from `tr`. -/
def visOfSteps : ExecTrace → Nat → List Step → List VisEntry
  | _, _, [] => []
  | tr, j, s :: ss =>
    stepView s tr (runWrapped (ev j)) ++ visOfSteps (s.next tr) (j + 1) ss

/-- Visible entries emitted by the first `m` steps of `cleanCallSteps cls cleanSpqrIdxs` from
`setupTrace r`. -/
def visClean (r : ProtocolSetup) (cls : Nat → Nat) (m : Nat) : List VisEntry :=
  visOfSteps (setupTrace r) 0 (ssClean cls cleanSpqrIdxs m)

theorem visOfSteps_append :
    ∀ (xs ys : List Step) (tr : ExecTrace) (j : Nat),
      visOfSteps tr j (xs ++ ys) =
        visOfSteps tr j xs ++ visOfSteps (runSteps xs tr) (j + xs.length) ys
  | [], ys, tr, j => by simp [visOfSteps, runSteps]
  | s :: xs, ys, tr, j => by
    simp only [List.cons_append, visOfSteps, List.length_cons,
      visOfSteps_append xs ys (s.next tr) (j + 1), List.append_assoc, runSteps]
    rw [show j + (xs.length + 1) = j + 1 + xs.length by omega]

theorem visClean_succ {r : ProtocolSetup} {cls : Nat → Nat} {k : Nat} {s : Step}
    (hk : k < 24) (hs : (cleanCallSteps cls cleanSpqrIdxs)[k]? = some s) :
    visClean r cls (k + 1) =
      visClean r cls k ++ stepView s (runTrace r (ssClean cls cleanSpqrIdxs k)) (runWrapped (ev k)) := by
  have hlen : (ssClean cls cleanSpqrIdxs k).length = k := by
    unfold ssClean
    rw [List.length_take_of_le (by rw [cleanCallSteps_length]; omega)]
  unfold visClean
  rw [ssClean_succ hs, visOfSteps_append, Nat.zero_add, hlen]
  simp only [visOfSteps, List.append_nil, runTrace]

theorem entry_proj_at {E1 E2 : Type} [ExecTraceTypes.Has E1]
    [ExecTraceTypes.Has E2] (j : Nat)
    {tr₀ tr' : ExecTrace} {e : E1}
    (hle : tr₀.append e ≤ tr') (hj : j = tr₀.length) :
    (tr'.at? j : Option E2) =
      DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) := by
  subst hj
  have hlt1 : tr₀.length < (tr₀.append e).length := by simp only [append_len, Nat.lt_succ_self]
  have hlt2 : tr₀.length < tr'.length := Nat.lt_of_lt_of_le hlt1 (DY.Trace.length_le _ _ hle)
  have hat_eq : tr'.at tr₀.length hlt2 = (tr₀.append e).at tr₀.length hlt1 :=
    (DY.Trace.at_le _ _ tr₀.length hlt1 hle).symm
  have h1 : (tr'.at? tr₀.length : Option E2) =
      DY.TraceEntryHas.proj (tr'.at tr₀.length hlt2) := by
    simp only [DY.Trace.at?, hlt2, ↓reduceDIte]
  have h2 : ((tr₀.append e).at? tr₀.length : Option E2) =
      DY.TraceEntryHas.proj ((tr₀.append e).at tr₀.length hlt1) := by
    simp only [DY.Trace.at?, hlt1, ↓reduceDIte]
  rw [h1, hat_eq, ← h2, at?_append_self_proj]

theorem entry_proj_none {E1 E2 : Type} [ExecTraceTypes.Has E1]
    [ExecTraceTypes.Has E2] (j : Nat)
    {tr₀ tr' : ExecTrace} {e : E1}
    (hle : tr₀.append e ≤ tr') (hj : j = tr₀.length)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none) :
    (tr'.at? j : Option E2) = none :=
  (entry_proj_at j hle hj).trans hnone

theorem pqExp_non {E : Type} [ExecTraceTypes.Has E]
    {tr₀ tr' : ExecTrace} {e : E} (j : Nat)
    (hle : tr₀.append e ≤ tr') (hj : j = tr₀.length)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    pqExposureAt tr' j = none := by
  unfold pqExposureAt
  have hat := entry_proj_at (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) j hle hj
  rw [hnone] at hat
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat]

theorem trExp_non {E : Type} [ExecTraceTypes.Has E]
    {tr₀ tr' : ExecTrace} {e : E} (j : Nat)
    (hle : tr₀.append e ≤ tr') (hj : j = tr₀.length)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none) :
    trExposureAt tr' j = none := by
  unfold trExposureAt
  have hat := entry_proj_at (E2 := DY.ProtocolEvent.ExecEntryT TREvent) j hle hj
  rw [hnone] at hat
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat]

/-- Once a session logs a `.receiver` `MessageKey` event prior to `stateIdx`,
`pendingPreKey tr stateIdx` is cleared to `none`. -/
theorem pendingPreKey_eq_none_of_receiver_mk {tr : ExecTrace} {stateIdx j : Nat}
    {me : Participant} {st : TRState}
    {seed pq : Bytes} {n : UInt32} {rIdx pIdx : Nat}
    (hat_st : tr.at? stateIdx = some (StT me st))
    (hj : j < stateIdx)
    (hat_mk : tr.at? j =
      some (EvT (.MessageKey (st.sessionInfo me) .receiver seed pq n rIdx pIdx))) :
    pendingPreKey tr stateIdx = none := by
  have hdec : sessionHasDecrypted tr (st.sessionInfo me) stateIdx = true := by
    unfold sessionHasDecrypted
    refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat_mk, EvT]
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
  rw [hat_st]
  dsimp only [StT, Option.map, Option.bind]
  simp only [hdec, ↓reduceIte]

private theorem getEventAt_of_le (E : Type) [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)]
    {t1 t2 : ExecTrace} (hle : t1 ≤ t2) {i : Nat} (hlt : i < t1.length) :
    t2.getEventAt E i = t1.getEventAt E i := by
  have hlt2 : i < t2.length := Nat.lt_of_lt_of_le hlt (DY.Trace.length_le _ _ hle)
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, DY.Trace.at?, hlt, hlt2, ↓reduceDIte,
    DY.Trace.at_le _ _ i hlt hle]

private theorem t5_def_eq :
    t5 = ((((((((t4.append (RndE 32)).append (RndE 32)).append (RndE 32)).append
      (NetE o1.ek)).append (NetE o1.ct)).append
      (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys))).append
      (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk))).append
      (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27))).append
      (StT "alice" stA0) := by
  have hdhs : rnd (t4.length + 2) 32 = dhsA := by rw [t4_length]
  have h27 : t4.length + 5 = 27 := by rw [t4_length]
  dsimp only [t5, aliceTr, aliceTrOpt]
  rw [hdhs, h27]
  rfl

private theorem t4_le_t5 : t4 ≤ t5 :=
  Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase.aliceTrOpt_le ..

private theorem t4_tr_eqs :
    t1 = registerIdentityTr DY.Trace.nil "alice" ∧
    t2 = registerIdentityTr t1 "bob" ∧
    t3 = genSignedPrekeyTr t2 "bob" ikB ∧
    t4 = genPQPrekeyTr t3 "bob" ikB := by
  have nil_len : (DY.Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have someEventB_nil : ∀ p : PQXDHEvent → Bool,
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) DY.Trace.nil p = false := fun p => by
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]; rw [nil_len]; rfl
  have someEventB_non : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
      (p : PQXDHEvent → Bool),
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = false →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) (tr.append x) p = false := by
    intro E _ tr x p hnone h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr x (List.mem_range.mp hi)]
      exact h i hi
    · rw [at?_append_self_proj, hnone]
  have someEventB_ev : ∀ (tr : ExecTrace) (ev : PQXDHEvent)
      (p : PQXDHEvent → Bool), p ev = false →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = false →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) (tr.append (EvP ev)) p = false := by
    intro tr ev p hp h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
      exact h i hi
    · rw [DY.Trace.at?_append]; exact hp
  have ht1 : t1 = registerIdentityTr DY.Trace.nil "alice" :=
    (Runs.registerIdentity
      (by unfold DY.Libsignal.PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2
  have ht2 : t2 = registerIdentityTr t1 "bob" := by
    refine (Runs.registerIdentity ?_).2
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [ht1]; dsimp only [registerIdentityTr]
    rw [someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
      (someEventB_non _ _ _ rfl (someEventB_ev _ _ _ rfl
        (someEventB_non _ _ _ rfl (someEventB_nil _)))))]
    rfl
  have hb2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  have ht3 : t3 = genSignedPrekeyTr t2 "bob" ikB :=
    (Runs.genSignedPrekey hb2).2
  have h23 : t2 ≤ t3 := by
    rw [ht3]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (DY.Trace.append_le t2 _) _) _) _) _) _
  have ht4 : t4 = genPQPrekeyTr t3 "bob" ikB :=
    (Runs.genPQPrekey (at?_mono h23 hb2)).2
  exact ⟨ht1, ht2, ht3, ht4⟩

theorem t4_bundle_msgs :
    t4.getMessageSentAt 14 = some (dhPk spkB) ∧
    t4.getMessageSentAt 15 = some (DY.Signature.sign ikB spkNonce (encodeEC (dhPk spkB))) ∧
    t4.getMessageSentAt 20 = some (kemPk pqskB) ∧
    t4.getMessageSentAt 21 = some (DY.Signature.sign ikB pqNonce (encodeKEM (kemPk pqskB))) := by
  obtain ⟨_, _, ht3, ht4⟩ := t4_tr_eqs
  have h34 : t3 ≤ t4 := by
    rw [ht4]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (DY.Trace.append_le t3 _) _) _) _) _) _
  have hs14 : t4.at? 14 = some (NetE (dhPk spkB)) := by
    refine at?_mono h34 ?_; rw [ht3]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (DY.Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t2_length]))
  have hs15 : t4.at? 15 = some (NetE (DY.Signature.sign ikB spkNonce (encodeEC (dhPk spkB)))) := by
    refine at?_mono h34 ?_; rw [ht3]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_append_at _ _ (by simp only [append_len, t2_length])
  have hp20 : t4.at? 20 = some (NetE (kemPk pqskB)) := by
    rw [ht4]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (DY.Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t3_length]))
  have hp21 : t4.at? 21 = some (NetE (DY.Signature.sign ikB pqNonce (encodeKEM (kemPk pqskB)))) := by
    rw [ht4]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_append_at _ _ (by simp only [append_len, t3_length])
  simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hs14, hs15, hp20, hp21]

theorem stepView_s0 (w : Bool) :
    stepView (.aliceStart "alice" "bob" 4 6 bh1) t4 w =
      ⟨.recv,
        [dhPk spkB, DY.Signature.sign ikB spkNonce (encodeEC (dhPk spkB)),
         kemPk pqskB, DY.Signature.sign ikB pqNonce (encodeKEM (kemPk pqskB))],
        .bundle, none⟩ ::
      rngEntry (randTerm 22 32) ::
      (kyberCoinEntries (randTerm 23 32) ++
        [{ rngEntry (randTerm 24 32) with anchor := some 27 }]) := by
  obtain ⟨hn0, hok0⟩ := s0_next_ok
  obtain ⟨hm14, hm15, hm20, hm21⟩ := t4_bundle_msgs
  have hni : newIndices t4 t5 = [22, 23, 24, 25, 26, 27, 28, 29, 30] := by
    unfold newIndices; rw [t4_length, t5_length]; decide
  let a0 := t4
  let a1 := a0.append (RndE 32)
  let a2 := a1.append (RndE 32)
  let a3 := a2.append (RndE 32)
  let a4 := a3.append (NetE o1.ek)
  let a5 := a4.append (NetE o1.ct)
  let a6 := a5.append (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys))
  let a7 := a6.append (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk))
  let a8 := a7.append (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27))
  have ha8 : a8 ≤ t5 := by rw [t5_def_eq]; exact DY.Trace.append_le _ _
  have ha7 : a7 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha8
  have ha6 : a6 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha7
  have ha5 : a5 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha6
  have ha4 : a4 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha5
  have ha3 : a3 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha4
  have ha2 : a2 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha3
  have ha1 : a1 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha2
  have hnr : newRandoms t4 t5 =
      [(randTerm 22 32, 32), (randTerm 23 32, 32), (randTerm 24 32, 32)] := by
    unfold newRandoms; rw [hni]
    have r22 : (t5.at? 22 : Option DY.Random.ExecEntryT) = some (RndE 32) :=
      at?_mono ha1 (at?_append_at a0 _ t4_length)
    have r23 : (t5.at? 23 : Option DY.Random.ExecEntryT) = some (RndE 32) :=
      at?_mono ha2 (at?_append_at a1 _ (by simp +zetaDelta only [append_len, t4_length]))
    have r24 : (t5.at? 24 : Option DY.Random.ExecEntryT) = some (RndE 32) :=
      at?_mono ha3 (at?_append_at a2 _ (by simp +zetaDelta only [append_len, t4_length]))
    have r25 := entry_proj_none (E2 := DY.Random.ExecEntryT) 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have r26 := entry_proj_none (E2 := DY.Random.ExecEntryT) 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have r27 := entry_proj_none (E2 := DY.Random.ExecEntryT) 27 ha6 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have r28 := entry_proj_none (E2 := DY.Random.ExecEntryT) 28 ha7 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have r29 := entry_proj_none (E2 := DY.Random.ExecEntryT) 29 ha8 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have r30 : (t5.at? 30 : Option DY.Random.ExecEntryT) = none := by
      refine entry_proj_none (tr₀ := a8) (e := StT "alice" stA0) 30 ?_
        (by simp +zetaDelta only [append_len, t4_length]) rfl
      rw [t5_def_eq]
    change List.filterMap (fun i => (t5.at? i : Option DY.Random.ExecEntryT).map _) _ = _
    simp [r22, r23, r24, r25, r26, r27, r28, r29, r30, RndE]
  have hev : eventIdx isAliceDone t4 t5 = some 27 := by
    unfold eventIdx; rw [hni]
    have p22 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 22 ha1 t4_length.symm rfl
    have p23 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 23 ha2 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have p24 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 24 ha3 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have p25 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have p26 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have p27 : (t5.at? 27 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
        some (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys)) :=
      at?_mono ha6 (at?_append_at a5 _ (by simp +zetaDelta only [append_len, t4_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, p22, p23, p24, p25, p26, p27, EvP, isAliceDone]
  have hexp : exposures t4 t5 = [] := by
    unfold exposures; rw [hni]
    have hp22 := pqExp_non 22 ha1 t4_length.symm rfl
    have hp23 := pqExp_non 23 ha2 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have hp24 := pqExp_non 24 ha3 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have hp25 := pqExp_non 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have hp26 := pqExp_non 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have hp27 : pqExposureAt t5 27 = none := by
      unfold pqExposureAt
      have p27 : (t5.at? 27 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys)) :=
        at?_mono ha6 (at?_append_at a5 _ (by simp +zetaDelta only [append_len, t4_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, p27, EvP]
    have hp28 := pqExp_non 28 ha7 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have hp29 := pqExp_non 29 ha8 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have hp30 : pqExposureAt t5 30 = none := by
      refine pqExp_non (tr₀ := a8) (e := StT "alice" stA0) 30 ?_
        (by simp +zetaDelta only [append_len, t4_length]) rfl
      rw [t5_def_eq]
    have ht22 := trExp_non 22 ha1 t4_length.symm rfl
    have ht23 := trExp_non 23 ha2 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have ht24 := trExp_non 24 ha3 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have ht25 := trExp_non 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have ht26 := trExp_non 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have ht27 := trExp_non 27 ha6 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have ht28 : trExposureAt t5 28 = none := by
      unfold trExposureAt
      have t28 : (t5.at? 28 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk)) :=
        at?_mono ha7 (at?_append_at a6 _ (by simp +zetaDelta only [append_len, t4_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t28, EvT]
    have ht29 := trExp_non 29 ha8 (by simp +zetaDelta only [append_len, t4_length]) rfl
    have ht30 : trExposureAt t5 30 = none := by
      refine trExp_non (tr₀ := a8) (e := StT "alice" stA0) 30 ?_
        (by simp +zetaDelta only [append_len, t4_length]) rfl
      rw [t5_def_eq]
    change List.filterMap (pqExposureAt t5) _ ++ List.filterMap (trExposureAt t5) _ = []
    simp [hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30,
      ht22, ht23, ht24, ht25, ht26, ht27, ht28, ht29, ht30]
  unfold stepView aliceVis
  simp only [hok0, ↓reduceIte, hn0, hexp, List.append_nil, hnr, hev]
  dsimp only [bh1, Option.toList, List.append_nil, received, List.filterMap,
    DY.Libsignal.Composed.Refinement.aliceDraws]
  simp [hm14, hm15, hm20, hm21]

private theorem no_cev_t4 {i : Nat} : t4.getEventAt ComposedEvent i = none := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t4_tr_eqs
  have hpeel : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) = none →
      tr.getEventAt ComposedEvent i = none →
      (tr.append e).getEventAt ComposedEvent i = none := by
    intro E _ tr e hnone h0
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h0 ⊢
    by_cases hlt : i < tr.length
    · rw [at?_append_of_lt tr e hlt]; exact h0
    · by_cases heq : i = tr.length
      · subst heq; rw [at?_append_self_proj, hnone]
      · rcases hat : ((tr.append e).at? i : Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) with _ | _
        · rfl
        · have := DY.Trace.at?_eq_some_implies_length_le
            (EntryT := DY.ProtocolEvent.ExecEntryT ComposedEvent) (tr.append e) i
          rw [hat, append_len] at this; simp at this; omega
  have hnil : (DY.Trace.nil : ExecTrace).getEventAt ComposedEvent i = none := by
    have h0 : ¬ i < (DY.Trace.nil : ExecTrace).length := by
      rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, DY.Trace.at?, h0]
  rw [ht4]; dsimp only [genPQPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht3]; dsimp only [genSignedPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht2]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  rw [ht1]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  exact hnil

private theorem no_trev_t4 {i : Nat} : t4.getEventAt TREvent i = none := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t4_tr_eqs
  have hpeel : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none →
      tr.getEventAt TREvent i = none →
      (tr.append e).getEventAt TREvent i = none := by
    intro E _ tr e hnone h0
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h0 ⊢
    by_cases hlt : i < tr.length
    · rw [at?_append_of_lt tr e hlt]; exact h0
    · by_cases heq : i = tr.length
      · subst heq; rw [at?_append_self_proj, hnone]
      · rcases hat : ((tr.append e).at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) with _ | _
        · rfl
        · have := DY.Trace.at?_eq_some_implies_length_le
            (EntryT := DY.ProtocolEvent.ExecEntryT TREvent) (tr.append e) i
          rw [hat, append_len] at this; simp at this; omega
  have hnil : (DY.Trace.nil : ExecTrace).getEventAt TREvent i = none := by
    have h0 : ¬ i < (DY.Trace.nil : ExecTrace).length := by
      rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, DY.Trace.at?, h0]
  rw [ht4]; dsimp only [genPQPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht3]; dsimp only [genSignedPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht2]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  rw [ht1]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  exact hnil

private theorem no_receiver_mk_encTrGen {tr : ExecTrace} {me : Participant} {stH cl : Nat}
    {st : TRState} {pq : Bytes} {s : DY.Libsignal.TripleRatchet.SessionInfo}
    (h0 : ∀ j < tr.length, ∀ seed pq' n rIdx pIdx,
      tr.getEventAt TREvent j ≠ some (.MessageKey s .receiver seed pq' n rIdx pIdx)) :
    ∀ j < (encTrGen tr me stH cl st pq).length, ∀ seed pq' n rIdx pIdx,
      (encTrGen tr me stH cl st pq).getEventAt TREvent j ≠
        some (.MessageKey s .receiver seed pq' n rIdx pIdx) := by
  intro j hj seed pq' n rIdx pIdx hget
  rw [encTrGen_length] at hj
  by_cases hlt : j < tr.length
  · rw [getEventAt_of_le TREvent (encTrGen_le tr me stH cl st pq) hlt] at hget
    exact h0 j hlt seed pq' n rIdx pIdx hget
  · let t0 := tr
    let t1' := t0.append (RndE 32)
    let t2' := t1'.append (RndE cl)
    let t3' := t2'.append (NetE (DY.Spqr.spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1)
    let t4' := t3'.append (EvT (.Sent me st.peer (dhPk st.dhs) st.ns (rnd tr.length 32)))
    let t5' := t4'.append (EvT (.MessageKey (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pq st.ns st.rIdx stH))
    let t6' := t5'.append (StT me (encSt st (rnd (tr.length + 1) cl)))
    let t7' := encTrGen tr me stH cl st pq
    have h67 : t6' ≤ t7' := DY.Trace.append_le _ _
    have h57 : t5' ≤ t7' := le_append_of_le (DY.Trace.append_le _ _) _
    have h47 : t4' ≤ t7' := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h57
    have h37 : t3' ≤ t7' := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h47
    have h27 : t2' ≤ t7' := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h37
    have h17 : t1' ≤ t7' := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h27
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
    have hd : j = tr.length ∨ j = tr.length + 1 ∨ j = tr.length + 2 ∨ j = tr.length + 3 ∨
        j = tr.length + 4 ∨ j = tr.length + 5 ∨ j = tr.length + 6 := by omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [entry_proj_none _ h17 rfl rfl] at hget; cases hget
    · rw [entry_proj_none _ h27 (by simp +zetaDelta only [append_len]) rfl] at hget; cases hget
    · rw [entry_proj_none _ h37 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl] at hget; cases hget
    · have hat : (t7'.at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.Sent me st.peer (dhPk st.dhs) st.ns (rnd tr.length 32))) :=
        at?_mono h47 (at?_append_at t3' _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
      rw [hat] at hget; cases hget
    · have hat : (t7'.at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.MessageKey (st.sessionInfo me) .sender
            (kdfCk st.cks).2 pq st.ns st.rIdx stH)) :=
        at?_mono h57 (at?_append_at t4' _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
      rw [hat] at hget; cases hget
    · rw [entry_proj_none _ h67 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl] at hget; cases hget
    · rw [entry_proj_none (tr₀ := t6') _ (DY.Trace.le_refl t7')
        (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl] at hget
      cases hget

private theorem no_receiver_mk_t5 (s : DY.Libsignal.TripleRatchet.SessionInfo) :
    ∀ j < t5.length, ∀ seed pq' n rIdx pIdx,
      t5.getEventAt TREvent j ≠ some (.MessageKey s .receiver seed pq' n rIdx pIdx) := by
  intro j hj seed pq' n rIdx pIdx hget
  rw [t5_length] at hj
  by_cases hlt : j < 22
  · rw [getEventAt_of_le TREvent t4_le_t5 (by rw [t4_length]; exact hlt), no_trev_t4] at hget
    cases hget
  · let a0 := t4
    let a1 := a0.append (RndE 32)
    let a2 := a1.append (RndE 32)
    let a3 := a2.append (RndE 32)
    let a4 := a3.append (NetE o1.ek)
    let a5 := a4.append (NetE o1.ct)
    let a6 := a5.append (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys))
    let a7 := a6.append (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk))
    let a8 := a7.append (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27))
    have ha8 : a8 ≤ t5 := by rw [t5_def_eq]; exact DY.Trace.append_le _ _
    have ha7 : a7 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha8
    have ha6 : a6 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha7
    have ha5 : a5 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha6
    have ha4 : a4 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha5
    have ha3 : a3 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha4
    have ha2 : a2 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha3
    have ha1 : a1 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha2
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
    have hd : j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 := by omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [entry_proj_none 22 ha1 t4_length.symm rfl] at hget; cases hget
    · rw [entry_proj_none 23 ha2 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 24 ha3 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 27 ha6 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · have t28 : (t5.at? 28 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk)) :=
        at?_mono ha7 (at?_append_at a6 _ (by simp +zetaDelta only [append_len, t4_length]))
      rw [t28] at hget; cases hget
    · rw [entry_proj_none 29 ha8 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget
      cases hget
    · have t30 : (t5.at? 30 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
        refine entry_proj_none (tr₀ := a8) (e := StT "alice" stA0) 30 ?_
          (by simp +zetaDelta only [append_len, t4_length]) rfl
        rw [t5_def_eq]
      rw [t30] at hget; cases hget

private theorem no_cev_lt29 {tr : ExecTrace} (h5 : t5 ≤ tr) {i : Nat} (hi : i < 29) :
    tr.getEventAt ComposedEvent i = none := by
  rw [getEventAt_of_le ComposedEvent h5 (by rw [t5_length]; omega)]
  by_cases h22 : i < 22
  · rw [getEventAt_of_le ComposedEvent t4_le_t5 (by rw [t4_length]; exact h22)]
    exact no_cev_t4
  · let a0 := t4
    let a1 := a0.append (RndE 32)
    let a2 := a1.append (RndE 32)
    let a3 := a2.append (RndE 32)
    let a4 := a3.append (NetE o1.ek)
    let a5 := a4.append (NetE o1.ct)
    let a6 := a5.append (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys))
    let a7 := a6.append (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk))
    let a8 := a7.append (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27))
    have ha8 : a8 ≤ t5 := by rw [t5_def_eq]; exact DY.Trace.append_le _ _
    have ha7 : a7 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha8
    have ha6 : a6 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha7
    have ha5 : a5 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha6
    have ha4 : a4 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha5
    have ha3 : a3 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha4
    have ha2 : a2 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha3
    have ha1 : a1 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha2
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    have hd : i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 := by omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [entry_proj_none 22 ha1 t4_length.symm rfl]
    · rw [entry_proj_none 23 ha2 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 24 ha3 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 27 ha6 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 28 ha7 (by simp +zetaDelta only [append_len, t4_length]) rfl]

private theorem findSome?_range_29 {tr : ExecTrace} {st : TRState}
    (h5 : t5 ≤ tr) (h29 : 29 < tr.length)
    (hsinfo : st.sessionInfo "alice" = stA0.sessionInfo "alice") :
    (DY.Libsignal.Composed.Refinement.sessionHandshakeEvents tr (st.sessionInfo "alice")).findSome?
      (fun
        | .AliceDone _ _ _ _ _ _ _ ek ct _ => some (ek, ct)
        | _ => none) = some (o1.ek, o1.ct) := by
  unfold DY.Libsignal.Composed.Refinement.sessionHandshakeEvents
  have hsplit : List.range tr.length =
      List.range 29 ++ (29 :: List.map (30 + ·) (List.range (tr.length - 30))) := by
    have h1 : List.range 30 = List.range 29 ++ [29] := List.range_succ
    have h2 : tr.length = 30 + (tr.length - 30) := by omega
    conv => lhs; rw [h2, List.range_add, h1, List.append_assoc]
    rfl
  rw [hsplit, List.filterMap_append, List.filterMap_cons]
  rw [(List.filterMap_eq_nil_iff (l := List.range 29)).mpr ?hnil, List.nil_append]
  case hnil =>
    intro i hi
    rw [no_cev_lt29 h5 (List.mem_range.mp hi)]
  have hhs : tr.getEventAt ComposedEvent 29 =
      some (.HandshakeSession (stA0.sessionInfo "alice") 27) := by
    have hat : t5.at? 29 = some (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27)) := by
      rw [t5_def_eq]
      exact at?_mono (DY.Trace.append_le _ _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    have hat' := at?_mono h5 hat
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat', EvC]
  have had : tr.getEventAt PQXDHEvent 27 =
      some (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys) := by
    have hat : t5.at? 27 =
        some (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys)) := by
      rw [t5_def_eq]
      exact at?_mono (le_append_of_le (le_append_of_le (DY.Trace.append_le _ _) _) _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    have hat' := at?_mono h5 hat
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat', EvP]
  simp only [hhs, hsinfo, ↓reduceIte, had, List.findSome?_cons]

theorem pendingPreKey_t5_eq : pendingPreKey t5 30 = some (o1.ek, o1.ct) := by
  have hat : t5.at? 30 = some (StT "alice" stA0) := by
    rw [t5_def_eq]
    exact at?_append_at _ _ (by simp only [append_len, t4_length])
  have hdec : sessionHasDecrypted t5 (stA0.sessionInfo "alice") 30 = false := by
    unfold sessionHasDecrypted
    simp only [List.any_eq_false, Bool.not_eq_true]
    intro j hj
    have hj' : j < t5.length := by rw [t5_length]; exact Nat.lt_trans (List.mem_range.mp hj) (by decide)
    split
    · next s' mk pq n rIdx pIdx hget =>
      by_cases heq : s' = stA0.sessionInfo "alice"
      · subst heq; exact absurd hget (no_receiver_mk_t5 _ j hj' _ _ _ _ _)
      · exact decide_eq_false heq
    · rfl
  have hlen5 : 29 < t5.length := by rw [t5_length]; decide
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
  rw [hat]; dsimp only [StT, Option.map, Option.bind]
  simp only [hdec, Bool.false_eq_true, ↓reduceIte]
  exact findSome?_range_29 (DY.Trace.le_refl t5) hlen5 rfl

theorem pendingPreKey_trClean2_eq (cls : Nat → Nat) :
    pendingPreKey (trClean2 cls) 36 = some (o1.ek, o1.ct) := by
  have hat : (trClean2 cls).at? 36 = some (StT "alice" (stA1Clean cls)) := by
    dsimp only [trClean2, encTrGen, stA1Clean]
    have hc : rnd (t5.length + 1) (cls 0) = coins1Clean cls := by rw [t5_length]; rfl
    rw [hc]
    exact at?_mono (DY.Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t5_length]))
  have hsinfo : (stA1Clean cls).sessionInfo "alice" = stA0.sessionInfo "alice" := rfl
  have hdec : sessionHasDecrypted (trClean2 cls) ((stA1Clean cls).sessionInfo "alice") 36 = false := by
    unfold sessionHasDecrypted
    simp only [List.any_eq_false, Bool.not_eq_true]
    intro j hj
    have hj' : j < (trClean2 cls).length := by
      rw [trClean2_length]; exact Nat.lt_trans (List.mem_range.mp hj) (by decide)
    split
    · next s' mk pq n rIdx pIdx hget =>
      by_cases heq : s' = (stA1Clean cls).sessionInfo "alice"
      · subst heq
        exact absurd hget
          (no_receiver_mk_encTrGen (no_receiver_mk_t5 _) j hj' _ _ _ _ _)
      · exact decide_eq_false heq
    · rfl
  have hlen2 : 29 < (trClean2 cls).length := by rw [trClean2_length]; decide
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
  rw [hat]; dsimp only [StT, Option.map, Option.bind]
  simp only [hdec, Bool.false_eq_true, ↓reduceIte]
  exact findSome?_range_29 (encTrGen_le ..) hlen2 hsinfo

theorem stepView_s1 (cls : Nat → Nat) :
    stepView (.messageEncrypt "alice" 30 (cls 0) 33) t5 true =
      ⟨.pt, [randTerm 31 32], .single, none⟩ ::
      ((if cls 0 != 0 then [rngEntry (randTerm 32 (cls 0))] else []) ++
       [⟨.send, [o1.ek, o1.ct, m1Clean cls], .preKeySend, none⟩]) := by
  obtain ⟨hn1, hok1⟩ := s1_next_ok cls
  have h := encTrGen_stepView_ok (wrapped := true) hok1 hn1
  rw [t5_length, pendingPreKey_t5_eq] at h
  exact h

theorem stepView_s2 (cls : Nat → Nat) :
    stepView (.messageEncrypt "alice" 36 (cls 1) 40) (trClean2 cls) true =
      ⟨.pt, [randTerm 38 32], .single, none⟩ ::
      ((if cls 1 != 0 then [rngEntry (randTerm 39 (cls 1))] else []) ++
       [⟨.send, [o1.ek, o1.ct, m2Clean cls], .preKeySend, none⟩]) := by
  obtain ⟨hn2, hok2⟩ := s2_next_ok cls
  have h := encTrGen_stepView_ok (wrapped := true) hok2 hn2
  rw [trClean2_length, pendingPreKey_trClean2_eq] at h
  exact h

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis
