/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs

/-!
# Protocol Setup Normalization to `r0`

Reduces `r : ProtocolSetup` under `evictedCompFitsPinned` to the reference setup `r0` across trace,
state, salt, trial, and collision predicates, and identifies the PQXDH fields `(ek, ct)` of
`cleanPreKeyRep` with `(o1.ek, o1.ct)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup

open scoped DY.Libsignal.Composed
open DY (Bytes ExecTrace Trace)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry PreKeyFields PreKeyRep Step
   setupTrace setupRandoms setupSent setupSecret setupPublic runTrace runSteps
   storedStates availableStates ownKeys principalTerms prefixTerms honestSaltsOf
   whisperTrials bobTrials MemoCollisionOn RecvCollisionOn
   BobSessionStartCollidesOrImplicitRejectsOn randTerm)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (bh1 t4 t5 o1 pqskB t5_runs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup
  (r0 r_alice_eq r_bob_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ssClean cleanPreKeyRep cleanRecvTerm emptyLit)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (step_le_next)

theorem r_withOpk_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    r.withOpk = false :=
  hfit.1.1.2.1

theorem setupTrace_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    setupTrace r = setupTrace r0 := by
  unfold setupTrace
  rw [r_alice_eq hfit, r_bob_eq hfit, r_withOpk_eq hfit]
  rfl

theorem setupTrace_r0_eq_t4 : setupTrace r0 = t4 := by
  have h : setupTrace r0 = setupTrace Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.r0 := rfl
  rw [h]
  exact Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.setupTrace_r0_eq

theorem runTrace_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) (ss : List Step) :
    runTrace r ss = runTrace r0 ss := by
  unfold runTrace
  rw [setupTrace_eq_r0 hfit]

theorem storedStates_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) (tr : ExecTrace) :
    storedStates r tr = storedStates r0 tr := by
  unfold storedStates
  rw [setupTrace_eq_r0 hfit]

theorem availableStates_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) (tr : ExecTrace) :
    availableStates r tr = availableStates r0 tr := by
  unfold availableStates
  rw [storedStates_eq_r0 hfit]

theorem honestSaltsOf_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) (ss : List Step) :
    honestSaltsOf r ss = honestSaltsOf r0 ss := by
  unfold honestSaltsOf
  rw [setupTrace_eq_r0 hfit]

theorem setupSecret_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) (i : Nat) :
    setupSecret r i = setupSecret r0 i := by
  unfold setupSecret setupRandoms
  rw [setupTrace_eq_r0 hfit]

theorem setupPublic_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) (i : Nat) :
    setupPublic r i = setupPublic r0 i := by
  unfold setupPublic setupSent
  rw [setupTrace_eq_r0 hfit]

theorem cleanRecvTerm_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (k : Nat) :
    cleanRecvTerm r cls spqrIdxs k = cleanRecvTerm r0 cls spqrIdxs k := by
  unfold cleanRecvTerm
  rw [runTrace_eq_r0 hfit]

theorem cleanPreKeyRep_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    cleanPreKeyRep r cls spqrIdxs = cleanPreKeyRep r0 cls spqrIdxs := by
  unfold cleanPreKeyRep
  rw [runTrace_eq_r0 hfit, cleanRecvTerm_eq_r0 hfit]

theorem principalTerms_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (tr : ExecTrace) (vis : List VisEntry) :
    principalTerms r tr vis = principalTerms r0 tr vis := by
  unfold principalTerms
  rw [storedStates_eq_r0 hfit]

theorem prefixTerms_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (tr : ExecTrace) (vis : List VisEntry) :
    prefixTerms r tr vis = prefixTerms r0 tr vis := by
  unfold prefixTerms
  rw [principalTerms_eq_r0 hfit]

theorem memoCollisionOn_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost) (known : Bytes → Prop)
    (tr : ExecTrace) (vis : List VisEntry) (newTerms newPts : List Bytes) :
    MemoCollisionOn i r S g known tr vis newTerms newPts ↔
      MemoCollisionOn i r0 S g known tr vis newTerms newPts := by
  unfold MemoCollisionOn
  rw [prefixTerms_eq_r0 hfit]

theorem ownKeys_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (tr : ExecTrace) (st : DY.Libsignal.TripleRatchet.TRState)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) :
    ownKeys r tr st msg = ownKeys r0 tr st msg := by
  unfold ownKeys
  rw [availableStates_eq_r0 hfit]

theorem whisperTrials_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) :
    whisperTrials i r S g tr msg = whisperTrials i r0 S g tr msg := by
  unfold whisperTrials
  simp only [availableStates_eq_r0 hfit, ownKeys_eq_r0 hfit]

theorem bobTrials_eq_r0 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) :
    bobTrials r tr p x msg = bobTrials r0 tr p x msg := by
  have hopk : r.withOpk = false := r_withOpk_eq hfit
  have hopk0 : r0.withOpk = false := rfl
  unfold bobTrials ProtocolSetup.ikAPubTerm ProtocolSetup.ikBPubTerm ProtocolSetup.spkSecTerm ProtocolSetup.ikBSecTerm ProtocolSetup.pqskSecTerm ProtocolSetup.opkSecTerm
  rw [hopk, hopk0]
  cases p.preKeyId <;>
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.all_none,
      setupPublic_eq_r0 hfit, setupSecret_eq_r0 hfit]

theorem bobSessionStartCollides_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (vis : List VisEntry) (salts : List Bytes)
    (p : PreKeyFields) (x : PreKeyRep) :
    BobSessionStartCollidesOrImplicitRejectsOn i r S g tr vis salts p x ↔
      BobSessionStartCollidesOrImplicitRejectsOn i r0 S g tr vis salts p x := by
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  cases DY.Libsignal.TripleRatchet.parseTrSignalMsg x.msg with
  | none => exact memoCollisionOn_eq_r0 hfit S g _ tr vis [x.ek, x.ct, x.msg] []
  | some msg =>
    dsimp only
    rw [bobTrials_eq_r0 hfit, memoCollisionOn_eq_r0 hfit]

theorem recvCollisionOn_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (vis : List VisEntry) (salts : List Bytes) (t : Bytes) :
    RecvCollisionOn i r S g tr vis salts t ↔
      RecvCollisionOn i r0 S g tr vis salts t := by
  unfold RecvCollisionOn
  cases DY.Libsignal.TripleRatchet.parseTrSignalMsg t with
  | none => exact memoCollisionOn_eq_r0 hfit S g _ tr vis [t] []
  | some msg =>
    dsimp only
    rw [whisperTrials_eq_r0 hfit, memoCollisionOn_eq_r0 hfit]

theorem setupSecret_r0_4 : setupSecret r0 4 = pqskB :=
  Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.setupSecret_4 (r := r0) (by decide)

theorem step0_next_t4 :
    (Step.aliceStart "alice" "bob" 4 6 bh1).next t4 = t5 := by
  dsimp only [Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next
    DY.Libsignal.Composed.aliceStart.reachability ("alice", "bob", 4, 6, bh1) t4]
  exact t5_runs.2

private theorem length_append {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem at?_append_of_lt {E1 E2 : Type} [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [length_append]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

private theorem at?_append_self {E1 E2 : Type} [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (DY.TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hlt, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem getMessageSentAt_append_of_lt {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    (tr.append e).getMessageSentAt i = tr.getMessageSentAt i := by
  simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?,
    at?_append_of_lt tr e hi]

private theorem getMessageSentAt_append_self (tr : ExecTrace) (b : Bytes) :
    (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt tr.length =
      some b := by
  simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?,
    at?_append_self]
  rfl

theorem t5_getMessageSentAt_25 : t5.getMessageSentAt 25 = some o1.ek := by
  unfold t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  repeat rw [getMessageSentAt_append_of_lt _ _
    (by simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; omega)]
  convert getMessageSentAt_append_self _ _ using 2
  simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]

theorem t5_getMessageSentAt_26 : t5.getMessageSentAt 26 = some o1.ct := by
  unfold t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  repeat rw [getMessageSentAt_append_of_lt _ _
    (by simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; omega)]
  convert getMessageSentAt_append_self _ _ using 2
  simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]

private theorem getMessageSentAt_mono {t1 t2 : ExecTrace} {i : Nat} {m : Bytes}
    (hle : t1 ≤ t2) (h : t1.getMessageSentAt i = some m) :
    t2.getMessageSentAt i = some m := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?] at h ⊢
  have hle' := Trace.at?_le (EntryT := DY.Network.ExecEntryT) t1 t2 i hle
  cases hat : (t1.at? i : Option DY.Network.ExecEntryT) with
  | none => rw [hat] at h; cases h
  | some e =>
    rw [hat] at h hle'
    rw [hle']
    exact h

theorem cleanPreKeyRep_ek_ct (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    (cleanPreKeyRep r0 cls spqrIdxs).ek = o1.ek ∧
    (cleanPreKeyRep r0 cls spqrIdxs).ct = o1.ct := by
  have hss : ssClean cls spqrIdxs 3 =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33,
       Step.messageEncrypt "alice" 36 (cls 1) 40] := rfl
  have htr : runTrace r0 (ssClean cls spqrIdxs 3) =
      (Step.messageEncrypt "alice" 36 (cls 1) 40).next
        ((Step.messageEncrypt "alice" 30 (cls 0) 33).next t5) := by
    rw [hss]; unfold runTrace; simp only [runSteps, setupTrace_r0_eq_t4, step0_next_t4]
  have hle : t5 ≤ runTrace r0 (ssClean cls spqrIdxs 3) := by
    rw [htr]
    exact Trace.le_trans _ _ _ (step_le_next _ _) (step_le_next _ _)
  unfold cleanPreKeyRep
  dsimp only
  rw [getMessageSentAt_mono hle t5_getMessageSentAt_25,
      getMessageSentAt_mono hle t5_getMessageSentAt_26]
  exact ⟨rfl, rfl⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
