/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Init.Data.Repr
import Init.Data.String.Defs
import Symbolic.DYBridge.DY.Bytes.Basic
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

/-!
# Symbolic Trace, Vis, and Salt Reduction Lemmas

Reduces `ExecTrace`, `VisEntry`, `ProtocolSetup`, and `honestSaltsOf` queries at call cuts
`k ∈ {3, 4, 6, 10}` (`storedStates`, `storedSecrets`, `send`-entry terms, `plaintextTerms`,
`saltsAt`, `whisperTrials`, `storedRatchetKeys`, `bobDoneBaseKeys`, and `setupPublic`/`setupSecret`)
to explicit constructor lists of `DY.Bytes` and `TRState` terms so `decide +kernel` collision
checks do not traverse monadic `Traceful` definitions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux

set_option maxRecDepth 200000

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
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg TREvent
   messageVersion recvChainFor consumeMessageKey skippedSeeds)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry
   setupPublic setupSecret setupSent setupRandoms
   storedStates availableStates ownKeys storedSecrets plaintextTerms
   TrialCtx whisperTrials storedRatchetKeys bobDoneBaseKeys gamma)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (registerIdentityTr genSignedPrekeyTr genPQPrekeyTr
   Runs.registerIdentity Runs.genSignedPrekey Runs.genPQPrekey
   RndE NetE EvT EvP EvC StT StP rnd encMsg encSt encTr aliceTr aliceTrOpt
   exposeCkrTr exposeCksTr)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB spkNonce pqNonce o1
   m0 m1 m2 m3 key0 key1 key2 key3
   stA0 stA1 stA2 stA4 stA5 stB1 stB2 stB3
   t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14
   t4_length t5_length t6_length t7_length t8_length t9_length t10_length t13_length)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
  (decEqBytesFast instDecidableEqBytes_eq_fast instDecidableEqBytes_pq instDecidableEqBytes_composed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag (r0Comp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (move0_init move1_enc0 move2_enc1 move3_bobStart move4_dec1 move5_encReply0
   move6_decReply0 move7_leakCkr move8_leakCks move9_enc2)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
  (trAt visAt saltsAt saltStep saltSteps visBetween encSendBetween visSteps)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
  (ekTerm ctTerm msg0Term msg1Term msgReply0Term msg2Term x4Rep setupTrace_r0Comp)

/-! ## Fast `@decide` Rewrites for Symbolic `DY.Bytes` Equality -/

theorem decide_bytes_composed_eq_fast (a b : DY.Bytes) :
    @decide (a = b) (@DY.instDecidableEqBytes DY.Libsignal.Composed.instBytesFunctor_symbolic a b) =
    @decide (a = b) (decEqBytesFast a b) := by
  rw [instDecidableEqBytes_composed]

theorem decide_bytes_tr_eq_fast (a b : DY.Bytes) :
    @decide (a = b)
      (@DY.instDecidableEqBytes
        (@DY.Libsignal.TripleRatchet.HasExecBytes.bytesFunc
          (@DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.instHasExecBytes))
        a b) =
    @decide (a = b) (decEqBytesFast a b) := by
  rw [instDecidableEqBytes_eq_fast]

theorem decide_bytes_pq_eq_fast (a b : DY.Bytes) :
    @decide (a = b) (@DY.instDecidableEqBytes DY.Libsignal.PQXDH.HasExecBytes.bytesFunc a b) =
    @decide (a = b) (decEqBytesFast a b) := by
  rw [instDecidableEqBytes_pq]

/-! ## Pure Constructor Form of `t1..t4` and `r0Comp` Setup Lookups -/

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

private theorem getMessageSentAt_append_of_lt {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    (tr.append e).getMessageSentAt i = tr.getMessageSentAt i := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, at?_append_of_lt tr e hi]

private theorem getMessageSentAt_append_self (tr : ExecTrace) (b : DY.Bytes) :
    (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt tr.length =
      some b := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, at?_append_self]
  rfl

private theorem range_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) (f : Option E2 → Option α) :
    ((List.range (tr.append e).length).filterMap fun i => f ((tr.append e).at? i)) =
      ((List.range tr.length).filterMap fun i => f (tr.at? i)) ++
      (f (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  rw [length_append, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  rw [at?_append_of_lt tr e (List.mem_range.mp hi)]

private theorem newIndices_self (tr : ExecTrace) :
    DY.Libsignal.Composed.Refinement.newIndices tr tr = [] := by
  simp [DY.Libsignal.Composed.Refinement.newIndices]

private theorem newIndices_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr₀ tr : ExecTrace) (e : E1) (f : Nat → Option E2 → Option α)
    (hle : tr₀.length ≤ tr.length) :
    ((DY.Libsignal.Composed.Refinement.newIndices tr₀ (tr.append e)).filterMap fun i =>
        f i ((tr.append e).at? i)) =
      ((DY.Libsignal.Composed.Refinement.newIndices tr₀ tr).filterMap fun i =>
        f i (tr.at? i)) ++
      (f tr.length (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  unfold DY.Libsignal.Composed.Refinement.newIndices
  rw [length_append, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
    List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  have hi' := List.mem_range'_1.mp hi
  rw [at?_append_of_lt tr e (by omega)]

private theorem someEventB_nil (p : DY.Libsignal.PQXDH.PQXDHEvent → Bool) :
    (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) Trace.nil p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem someEventB_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) (p : DY.Libsignal.PQXDH.PQXDHEvent → Bool) :
    (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) (tr.append e) p =
      ((DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p ||
        match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
            Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with
        | some x => p x.ev
        | none => false) := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [length_append, List.range_succ, List.any_append, List.any_cons, List.any_nil,
    Bool.or_false, at?_append_self]
  refine congrArg₂ Bool.or ?_ ?_
  · rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    exact exists_congr fun i => and_congr_right fun hi => by
      rw [at?_append_of_lt tr e (List.mem_range.mp hi)]
  · cases (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) <;> rfl

private theorem newIndices_nil_getMessageSentAt_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    ((DY.Libsignal.Composed.Refinement.newIndices Trace.nil (tr.append e)).filterMap
        fun i => (tr.append e).getMessageSentAt i) =
      ((DY.Libsignal.Composed.Refinement.newIndices Trace.nil tr).filterMap
        fun i => tr.getMessageSentAt i) ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option Network.ExecEntryT)).map (·.msg)).toList := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  unfold DY.Libsignal.Composed.Refinement.newIndices
  have h0 : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  rw [h0, length_append, Nat.sub_zero, Nat.sub_zero, List.range'_concat, Nat.zero_add, Nat.one_mul,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, at?_append_self]
  refine congrArg₂ List.append (List.filterMap_congr fun i hi => ?_) ?_
  · have hi' := List.mem_range'_1.mp hi
    rw [at?_append_of_lt tr e (by omega)]
  · cases (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option Network.ExecEntryT) <;>
      rfl

private theorem newRandoms_self (tr : ExecTrace) :
    DY.Libsignal.Composed.Refinement.newRandoms tr tr = [] := by
  simp [DY.Libsignal.Composed.Refinement.newRandoms, newIndices_self]

private theorem newRandoms_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr₀ tr : ExecTrace) (e : E1) (hle : tr₀.length ≤ tr.length) :
    DY.Libsignal.Composed.Refinement.newRandoms tr₀ (tr.append e) =
      DY.Libsignal.Composed.Refinement.newRandoms tr₀ tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option Random.ExecEntryT)).map
        fun r => (DY.Libsignal.Composed.Refinement.randTerm tr.length r.length, r.length)).toList := by
  unfold DY.Libsignal.Composed.Refinement.newRandoms
  exact newIndices_filterMap_at?_append (E2 := Random.ExecEntryT) tr₀ tr e
    (fun i o => o.map fun r => (DY.Libsignal.Composed.Refinement.randTerm i r.length, r.length)) hle

private theorem newRandoms_nil_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    DY.Libsignal.Composed.Refinement.newRandoms Trace.nil (tr.append e) =
      DY.Libsignal.Composed.Refinement.newRandoms Trace.nil tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option Random.ExecEntryT)).map
        fun r => (DY.Libsignal.Composed.Refinement.randTerm tr.length r.length, r.length)).toList :=
  newRandoms_append Trace.nil tr e
    (by rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; exact Nat.zero_le _)

def t1Pure : ExecTrace := registerIdentityTr Trace.nil "alice"
def t2Pure : ExecTrace := registerIdentityTr t1Pure "bob"
def t3Pure : ExecTrace := genSignedPrekeyTr t2Pure "bob" ikB
def t4Pure : ExecTrace := genPQPrekeyTr t3Pure "bob" ikB

theorem t1_eq_pure : t1 = t1Pure :=
  (Runs.registerIdentity (tr := Trace.nil) (p := "alice")
    (by simp only [DY.Libsignal.PQXDH.isRegisteredB, someEventB_nil]; rfl)).2

theorem t2_eq_pure : t2 = t2Pure := by
  unfold t2
  rw [t1_eq_pure]
  exact (Runs.registerIdentity (tr := t1Pure) (p := "bob")
    (by simp only [t1Pure, registerIdentityTr, DY.Libsignal.PQXDH.isRegisteredB,
          someEventB_append, someEventB_nil]; rfl)).2

private theorem t2Pure_at?_9 :
    t2Pure.at? 9 =
      some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob" { kind := .identity, sk := ikB }) := by
  have ht1 : t1Pure.length = 5 := by
    simp only [t1Pure, registerIdentityTr, length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
  unfold t2Pure registerIdentityTr
  dsimp only
  rw [ht1]
  convert Trace.at?_append _ _ using 2
  simp only [length_append, ht1]

theorem t3_eq_pure : t3 = t3Pure := by
  unfold t3
  rw [t2_eq_pure]
  exact (Runs.genSignedPrekey (tr := t2Pure) (b := "bob") (idH := 9) (ik := ikB) t2Pure_at?_9).2

theorem t4_eq_pure : t4 = t4Pure := by
  unfold t4
  rw [t3_eq_pure]
  have ht2 : t2Pure.length = 10 := by
    simp only [t2Pure, t1Pure, registerIdentityTr, length_append,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
  have h9 : t3Pure.at? 9 =
      some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob" { kind := .identity, sk := ikB }) := by
    unfold t3Pure genSignedPrekeyTr
    dsimp only
    repeat rw [at?_append_of_lt _ _ (by simp only [length_append, ht2]; omega)]
    exact t2Pure_at?_9
  exact (Runs.genPQPrekey (tr := t3Pure) (b := "bob") (idH := 9) (ik := ikB) h9).2

private theorem setupSent_r0Comp_eq :
    setupSent r0Comp =
      [DY.DiffieHellman.dhPk ikA, DY.Signature.vk ikA,
       DY.DiffieHellman.dhPk ikB, DY.Signature.vk ikB,
       DY.DiffieHellman.dhPk spkB,
       DY.Signature.sign ikB Symbolic.Proofs.Tests.Shared.Composed.HonestSession.spkNonce
         (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk spkB)),
       DY.PQKem.kemPk pqskB,
       DY.Signature.sign ikB Symbolic.Proofs.Tests.Shared.Composed.HonestSession.pqNonce
         (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk pqskB))] := by
  rw [setupSent, setupTrace_r0Comp, t4_eq_pure]
  simp only [t4Pure, t3Pure, t2Pure, t1Pure, registerIdentityTr, genSignedPrekeyTr, genPQPrekeyTr,
    newIndices_nil_getMessageSentAt_append, newIndices_self, List.filterMap_nil,
    length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
  rfl

private theorem setupRandoms_r0Comp_eq :
    setupRandoms r0Comp =
      [ikA, ikB, spkB, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.spkNonce,
       pqskB, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.pqNonce] := by
  rw [setupRandoms, setupTrace_r0Comp, t4_eq_pure]
  simp only [t4Pure, t3Pure, t2Pure, t1Pure, registerIdentityTr, genSignedPrekeyTr, genPQPrekeyTr,
    newRandoms_nil_append, newRandoms_self,
    length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
  rfl

theorem setupPublic_r0Comp_0 : setupPublic r0Comp 0 = DY.DiffieHellman.dhPk ikA := by
  rw [setupPublic, setupSent_r0Comp_eq]; rfl

theorem setupPublic_r0Comp_2 : setupPublic r0Comp 2 = DY.DiffieHellman.dhPk ikB := by
  rw [setupPublic, setupSent_r0Comp_eq]; rfl

theorem setupSecret_r0Comp_1 : setupSecret r0Comp 1 = ikB := by
  rw [setupSecret, setupRandoms_r0Comp_eq]; rfl

theorem setupSecret_r0Comp_2 : setupSecret r0Comp 2 = spkB := by
  rw [setupSecret, setupRandoms_r0Comp_eq]; rfl

theorem setupSecret_r0Comp_4 : setupSecret r0Comp 4 = pqskB := by
  rw [setupSecret, setupRandoms_r0Comp_eq]; rfl

/-! ## `saltsAt`, `visAt` Send/Plaintext Projections, `storedStates`, and `storedSecrets` -/

private theorem length_encTr (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : DY.Bytes) :
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq).length =
      tr.length + 7 := by
  simp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr, length_append]

private theorem getMessageSentAt_encTr_of_lt (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : DY.Bytes) {i : Nat} (hi : i < tr.length) :
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq).getMessageSentAt i =
      tr.getMessageSentAt i := by
  unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
  dsimp only
  repeat rw [getMessageSentAt_append_of_lt _ _
    (by simp -failIfUnchanged only [length_append]; omega)]

private theorem getMessageSentAt_encTr_pq (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : DY.Bytes) :
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq).getMessageSentAt
      (tr.length + 2) =
      some (DY.Spqr.spqrSend st.spqr
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd (tr.length + 1) 32)).2.1 := by
  unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
  dsimp only
  rw [getMessageSentAt_append_of_lt _ _ (by simp only [length_append]; omega),
    getMessageSentAt_append_of_lt _ _ (by simp only [length_append]; omega),
    getMessageSentAt_append_of_lt _ _ (by simp only [length_append]; omega),
    getMessageSentAt_append_of_lt _ _ (by simp only [length_append]; omega)]
  convert getMessageSentAt_append_self _ _ using 2
  simp only [length_append]

private theorem getMessageSentAt_encTr_last (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : DY.Bytes) :
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq).getMessageSentAt
      (tr.length + 6) =
      some (Symbolic.Proofs.Tests.Shared.Composed.Runs.encMsg st
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd (tr.length + 1) 32) pq
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd tr.length 32)) := by
  unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
  dsimp only
  convert getMessageSentAt_append_self _ _ using 2
  simp only [length_append]

private theorem lastSent_encTr (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : DY.Bytes) :
    DY.Libsignal.Composed.Refinement.lastSent tr
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) =
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq).getMessageSentAt
        (tr.length + 6) := by
  unfold DY.Libsignal.Composed.Refinement.lastSent
  rw [length_encTr]
  have hlt : tr.length < tr.length + 7 := by omega
  simp only [hlt, ↓reduceIte]
  exact congrArg
    (fun k => (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq).getMessageSentAt k)
    (by omega)

private theorem newRandoms_encTr (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : DY.Bytes) :
    DY.Libsignal.Composed.Refinement.newRandoms tr
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) =
      [(DY.Libsignal.Composed.Refinement.randTerm tr.length 32, 32),
       (DY.Libsignal.Composed.Refinement.randTerm (tr.length + 1) 32, 32)] := by
  unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
  dsimp only
  repeat rw [newRandoms_append _ _ _ (by simp -failIfUnchanged only [length_append]; omega)]
  rw [newRandoms_self]
  simp only [length_append]
  rfl

private theorem saltStep_encTr (me' : Participant) (stH' len pqIdx : Nat)
    (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (pq : DY.Bytes)
    (hne : pqIdx ≠ tr.length + 3) :
    Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.saltStep
      (.messageEncrypt me' stH' len pqIdx) tr
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) =
      [(DY.Spqr.spqrSend st.spqr
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd (tr.length + 1) 32)).2.1] := by
  simp only [Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.saltStep, hne, ↓reduceIte,
    getMessageSentAt_encTr_pq]
  rfl

private theorem saltSteps_prefix :
    saltSteps.take 10 = [[], [key0], [key1], [], [], [key2], [], [], [], [key3]] := by
  dsimp only [saltSteps, List.take, move0_init, move1_enc0, move2_enc1, move3_bobStart,
    move4_dec1, move5_encReply0, move6_decReply0, move7_leakCkr, move8_leakCks, move9_enc2]
  have s1 : saltStep (.messageEncrypt "alice" 30 32 33) t5 t6 = [key0] := by
    unfold t6; rw [saltStep_encTr _ _ _ _ _ _ _ _ _ (by rw [t5_length]; omega), t5_length]; rfl
  have s2 : saltStep (.messageEncrypt "alice" 36 32 40) t6 t7 = [key1] := by
    unfold t7; rw [saltStep_encTr _ _ _ _ _ _ _ _ _ (by rw [t6_length]; omega), t6_length]; rfl
  have s5 : saltStep (.messageEncrypt "bob" 57 32 60) t9 t10 = [key2] := by
    unfold t10; rw [saltStep_encTr _ _ _ _ _ _ _ _ _ (by rw [t9_length]; omega), t9_length]; rfl
  have s9 : saltStep (.messageEncrypt "alice" 71 32 78) t13 t14 = [key3] := by
    unfold t14; rw [saltStep_encTr _ _ _ _ _ _ _ _ _ (by rw [t13_length]; omega), t13_length]; rfl
  rw [s1, s2, s5, s9]; rfl

theorem saltsAt_3_eq : saltsAt 3 = [DY.Spqr.zeroKey, key0, key1] := by
  unfold saltsAt
  rw [show saltSteps.take 3 = (saltSteps.take 10).take 3 by rw [List.take_take]; rfl,
    saltSteps_prefix]; rfl

theorem saltsAt_4_eq : saltsAt 4 = [DY.Spqr.zeroKey, key0, key1] := by
  unfold saltsAt
  rw [show saltSteps.take 4 = (saltSteps.take 10).take 4 by rw [List.take_take]; rfl,
    saltSteps_prefix]; rfl

theorem saltsAt_6_eq : saltsAt 6 = [DY.Spqr.zeroKey, key0, key1, key2] := by
  unfold saltsAt
  rw [show saltSteps.take 6 = (saltSteps.take 10).take 6 by rw [List.take_take]; rfl,
    saltSteps_prefix]; rfl

theorem saltsAt_10_eq : saltsAt 10 = [DY.Spqr.zeroKey, key0, key1, key2, key3] := by
  unfold saltsAt; rw [saltSteps_prefix]; rfl

private theorem filter_kind_kyberCoinEntries (entropy : DY.Bytes)
    (k : DY.Libsignal.Composed.Refinement.VisEventKind) (hk : (.rng == k) = false) :
    (DY.Libsignal.Composed.Refinement.kyberCoinEntries entropy).filter (·.kind == k) = [] := by
  unfold DY.Libsignal.Composed.Refinement.kyberCoinEntries
  rw [List.filter_eq_nil_iff]
  intro x hx
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
  exact Bool.eq_false_iff.mp hk

private theorem filter_kind_aliceDraws (done : Option Nat) (rs : List DY.Bytes)
    (k : DY.Libsignal.Composed.Refinement.VisEventKind) (hk : (.rng == k) = false) :
    (DY.Libsignal.Composed.Refinement.aliceDraws done rs).filter (·.kind == k) = [] := by
  cases rs with
  | nil => rfl
  | cons ek rest =>
    cases rest with
    | nil => simp [DY.Libsignal.Composed.Refinement.aliceDraws,
        DY.Libsignal.Composed.Refinement.rngEntry, hk]
    | cons entropy rest' =>
      simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.filter_cons,
        List.filter_append, DY.Libsignal.Composed.Refinement.rngEntry, hk,
        Bool.false_eq_true, ↓reduceIte,
        filter_kind_kyberCoinEntries entropy k hk, List.nil_append]
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      exact Bool.eq_false_iff.mp hk

private theorem filter_kind_exposures (tr tr' : ExecTrace)
    (k : DY.Libsignal.Composed.Refinement.VisEventKind) (hk : (.leak == k) = false) :
    (DY.Libsignal.Composed.Refinement.exposures tr tr').filter (·.kind == k) = [] := by
  unfold DY.Libsignal.Composed.Refinement.exposures
  rw [List.filter_eq_nil_iff]
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h1
    unfold DY.Libsignal.Composed.Refinement.pqExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj
    all_goals (subst hj; exact Bool.eq_false_iff.mp hk)
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h2
    unfold DY.Libsignal.Composed.Refinement.trExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj
    all_goals (subst hj; exact Bool.eq_false_iff.mp hk)

private theorem filter_kind_map_rngEntry {α : Type} (xs : List α) (f : α → DY.Bytes)
    (k : DY.Libsignal.Composed.Refinement.VisEventKind) (hk : (.rng == k) = false) :
    (xs.map fun r => DY.Libsignal.Composed.Refinement.rngEntry (f r)).filter (·.kind == k) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
  exact Bool.eq_false_iff.mp hk

private theorem filter_kind_visBetween_nonEnc
    (s : DY.Libsignal.Composed.Refinement.Step) (tr tr' : ExecTrace)
    (wrap : Option (Nat × Nat)) (wd : Bool)
    (k : DY.Libsignal.Composed.Refinement.VisEventKind)
    (hrecv : (.recv == k) = false) (hrng : (.rng == k) = false)
    (hacc : (.accept == k) = false) (hleak : (.leak == k) = false)
    (hne : ∀ a b c d, s ≠ .messageEncrypt a b c d) :
    (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visBetween s tr tr' wrap wd).filter
      (·.kind == k) = [] := by
  unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visBetween
  rw [List.filter_append, filter_kind_exposures tr tr' k hleak, List.append_nil]
  cases s with
  | aliceStart =>
    simp [DY.Libsignal.Composed.Refinement.aliceVis, hrecv,
      filter_kind_aliceDraws _ _ k hrng]
  | bobStart =>
    simp only [DY.Libsignal.Composed.Refinement.bobVis, List.filter_append, List.filter_cons,
      hrecv, Bool.false_eq_true, ↓reduceIte, filter_kind_map_rngEntry _ _ k hrng, List.nil_append]
    cases DY.Libsignal.Composed.Refinement.receivedPlaintext tr tr' <;> simp [hacc]
  | messageEncrypt a b c d => exact (hne a b c d rfl).elim
  | messageDecrypt _ _ msgIdx =>
    simp only [DY.Libsignal.Composed.Refinement.decVis, List.filter_append,
      filter_kind_map_rngEntry _ _ k hrng, List.append_nil]
    cases tr.getMessageSentAt msgIdx <;>
      cases DY.Libsignal.Composed.Refinement.receivedPlaintext tr tr' <;>
      simp [hrecv, hacc]
  | messageDecryptSkipped _ _ msgIdx =>
    simp only [DY.Libsignal.Composed.Refinement.decVis, List.filter_append,
      filter_kind_map_rngEntry _ _ k hrng, List.append_nil]
    cases tr.getMessageSentAt msgIdx <;>
      cases DY.Libsignal.Composed.Refinement.receivedPlaintext tr tr' <;>
      simp [hrecv, hacc]
  | _ => rfl

private theorem filter_send_visBetween_enc (a : Participant) (b c d : Nat)
    (tr tr' : ExecTrace) (wrap : Option (Nat × Nat)) (wd : Bool) :
    (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visBetween
      (.messageEncrypt a b c d) tr tr' wrap wd).filter (·.kind == .send) =
      Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.encSendBetween tr tr' wrap := by
  unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visBetween
  rw [List.filter_append, filter_kind_exposures tr tr' .send rfl, List.append_nil,
    List.filter_append]
  have henc : (DY.Libsignal.Composed.Refinement.encDraws
      (DY.Libsignal.Composed.Refinement.newRandoms tr tr')).filter (·.kind == .send) = [] := by
    cases DY.Libsignal.Composed.Refinement.newRandoms tr tr' with
    | nil => rfl
    | cons hd tl =>
      simp [DY.Libsignal.Composed.Refinement.encDraws,
        filter_kind_map_rngEntry _ _ .send rfl]
  have hsend : (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.encSendBetween tr tr' wrap).filter
      (·.kind == .send) =
      Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.encSendBetween tr tr' wrap := by
    unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.encSendBetween
    cases DY.Libsignal.Composed.Refinement.lastSent tr tr' with
    | none => rfl
    | some w =>
      rcases wrap with _ | ⟨ekIdx, ctIdx⟩
      · rfl
      · dsimp only
        cases tr.getMessageSentAt ekIdx <;> cases tr.getMessageSentAt ctIdx <;> rfl
  rw [henc, List.nil_append, hsend]

private theorem filter_pt_visBetween_enc (a : Participant) (b c d : Nat)
    (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (pq : DY.Bytes)
    (wrap : Option (Nat × Nat)) (wd : Bool) :
    (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visBetween
      (.messageEncrypt a b c d) tr
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) wrap wd).filter
      (·.kind == .pt) =
      [⟨.pt, [DY.Libsignal.Composed.Refinement.randTerm tr.length 32], .single, none⟩] := by
  unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visBetween
  rw [List.filter_append, filter_kind_exposures _ _ .pt rfl, List.append_nil,
    List.filter_append, newRandoms_encTr]
  have hsend : (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.encSendBetween tr
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) wrap).filter
      (·.kind == .pt) = [] := by
    unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.encSendBetween
    cases DY.Libsignal.Composed.Refinement.lastSent tr
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) with
    | none => rfl
    | some w =>
      rcases wrap with _ | ⟨ekIdx, ctIdx⟩
      · rfl
      · dsimp only
        cases tr.getMessageSentAt ekIdx <;> cases tr.getMessageSentAt ctIdx <;> rfl
  rw [hsend, List.append_nil]
  rfl

private theorem t5_getMessageSentAt_25 :
    t5.getMessageSentAt 25 = some Symbolic.Proofs.Tests.Shared.Composed.HonestSession.o1.ek := by
  unfold t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  repeat rw [getMessageSentAt_append_of_lt _ _
    (by simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; omega)]
  convert getMessageSentAt_append_self _ _ using 2
  simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]

private theorem ekTerm_eq_o1_ek :
    ekTerm = Symbolic.Proofs.Tests.Shared.Composed.HonestSession.o1.ek := by
  unfold ekTerm; rw [t5_getMessageSentAt_25]; rfl

private theorem t5_getMessageSentAt_26 :
    t5.getMessageSentAt 26 = some ctTerm := by
  have h : t5.getMessageSentAt 26 =
      some Symbolic.Proofs.Tests.Shared.Composed.HonestSession.o1.ct := by
    unfold t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    repeat rw [getMessageSentAt_append_of_lt _ _
      (by simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; omega)]
    convert getMessageSentAt_append_self _ _ using 2
    simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
  unfold ctTerm; rw [h]; rfl

private theorem visSteps_filter_send_prefix :
    (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 10).map
      (fun vs => (vs.filter (·.kind == .send)).flatMap (·.terms)) =
      [[], [ekTerm, ctTerm, msg0Term], [ekTerm, ctTerm, msg1Term],
       [], [], [msgReply0Term], [], [], [], [msg2Term]] := by
  dsimp only [Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps, List.take, List.map,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move0_init,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move1_enc0,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move2_enc1,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move3_bobStart,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move4_dec1,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move5_encReply0,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move6_decReply0,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move7_leakCkr,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move8_leakCks,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.move9_enc2]
  rw [filter_kind_visBetween_nonEnc _ _ _ _ _ .send rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t7 _ _ _ .send rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t8 _ _ _ .send rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t10 _ _ _ .send rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t11 _ _ _ .send rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t12 _ _ _ .send rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_send_visBetween_enc, filter_send_visBetween_enc,
    filter_send_visBetween_enc, filter_send_visBetween_enc]
  have ht5_25 : t5.getMessageSentAt 25 = some ekTerm := by
    rw [t5_getMessageSentAt_25, ekTerm_eq_o1_ek]
  have ht6_25 : t6.getMessageSentAt 25 = some ekTerm := by
    unfold t6
    rw [getMessageSentAt_encTr_of_lt _ _ _ _ _
      (by rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t5_length]; omega), ht5_25]
  have ht6_26 : t6.getMessageSentAt 26 = some ctTerm := by
    unfold t6
    rw [getMessageSentAt_encTr_of_lt _ _ _ _ _
      (by rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t5_length]; omega),
      t5_getMessageSentAt_26]
  have hl1 : DY.Libsignal.Composed.Refinement.lastSent t5 t6 = some msg0Term := by
    have hm := getMessageSentAt_encTr_last t5 "alice" 30 stA0 key0
    rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t5_length] at hm
    unfold t6 msg0Term
    rw [lastSent_encTr, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t5_length]
    change t6.getMessageSentAt 37 = some ((t6.getMessageSentAt 37).getD _)
    change t6.getMessageSentAt 37 = _ at hm
    rw [hm]; rfl
  have hl2 : DY.Libsignal.Composed.Refinement.lastSent t6 t7 = some msg1Term := by
    have hm := getMessageSentAt_encTr_last t6 "alice" 36 stA1 key1
    rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t6_length] at hm
    unfold t7 msg1Term
    rw [lastSent_encTr, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t6_length]
    change t7.getMessageSentAt 44 = some ((t7.getMessageSentAt 44).getD _)
    change t7.getMessageSentAt 44 = _ at hm
    rw [hm]; rfl
  have hl5 : DY.Libsignal.Composed.Refinement.lastSent t9 t10 = some msgReply0Term := by
    have hm := getMessageSentAt_encTr_last t9 "bob" 57 stB2 key2
    rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t9_length] at hm
    unfold t10 msgReply0Term
    rw [lastSent_encTr, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t9_length]
    change t10.getMessageSentAt 64 = some ((t10.getMessageSentAt 64).getD _)
    change t10.getMessageSentAt 64 = _ at hm
    rw [hm]; rfl
  have hl9 : DY.Libsignal.Composed.Refinement.lastSent t13 t14 = some msg2Term := by
    have hm := getMessageSentAt_encTr_last t13 "alice" 71 stA4 key3
    rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13_length] at hm
    unfold t14 msg2Term
    rw [lastSent_encTr, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13_length]
    change t14.getMessageSentAt 82 = some ((t14.getMessageSentAt 82).getD _)
    change t14.getMessageSentAt 82 = _ at hm
    rw [hm]; rfl
  simp only [Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.encSendBetween,
    hl1, hl2, hl5, hl9, ht5_25, t5_getMessageSentAt_26, ht6_25, ht6_26]
  rfl

private theorem filter_flatMap_flatten {α β : Type} (xss : List (List α))
    (p : α → Bool) (f : α → List β) :
    ((xss.flatten).filter p).flatMap f =
      (xss.map (fun xs => (xs.filter p).flatMap f)).flatten := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    rw [List.flatten_cons, List.filter_append, List.flatMap_append, ih, List.map_cons,
      List.flatten_cons]

theorem sendTerms_visAt_3 :
    ((visAt 3).filter (·.kind == .send)).flatMap (·.terms) =
      [ekTerm, ctTerm, msg0Term, ekTerm, ctTerm, msg1Term] := by
  unfold visAt
  rw [filter_flatMap_flatten,
    show Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 3 =
      (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 10).take 3 by
        rw [List.take_take]; rfl,
    List.map_take, visSteps_filter_send_prefix]
  rfl

theorem sendTerms_visAt_4 :
    ((visAt 4).filter (·.kind == .send)).flatMap (·.terms) =
      [ekTerm, ctTerm, msg0Term, ekTerm, ctTerm, msg1Term] := by
  unfold visAt
  rw [filter_flatMap_flatten,
    show Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 4 =
      (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 10).take 4 by
        rw [List.take_take]; rfl,
    List.map_take, visSteps_filter_send_prefix]
  rfl

theorem sendTerms_visAt_6 :
    ((visAt 6).filter (·.kind == .send)).flatMap (·.terms) =
      [ekTerm, ctTerm, msg0Term, ekTerm, ctTerm, msg1Term, msgReply0Term] := by
  unfold visAt
  rw [filter_flatMap_flatten,
    show Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 6 =
      (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 10).take 6 by
        rw [List.take_take]; rfl,
    List.map_take, visSteps_filter_send_prefix]
  rfl

theorem sendTerms_visAt_10 :
    ((visAt 10).filter (·.kind == .send)).flatMap (·.terms) =
      [ekTerm, ctTerm, msg0Term, ekTerm, ctTerm, msg1Term, msgReply0Term, msg2Term] := by
  unfold visAt
  rw [filter_flatMap_flatten, visSteps_filter_send_prefix]
  rfl

private theorem visSteps_filter_pt_prefix :
    (visSteps.take 10).map (fun vs => (vs.filter (·.kind == .pt)).flatMap (·.terms)) =
      [[], [m0], [m1], [], [], [m2], [], [], [], [m3]] := by
  dsimp only [visSteps, List.take, List.map, move0_init, move1_enc0, move2_enc1, move3_bobStart,
    move4_dec1, move5_encReply0, move6_decReply0, move7_leakCkr, move8_leakCks, move9_enc2]
  rw [filter_kind_visBetween_nonEnc _ _ _ _ _ .pt rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t7 _ _ _ .pt rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t8 _ _ _ .pt rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t10 _ _ _ .pt rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t11 _ _ _ .pt rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    filter_kind_visBetween_nonEnc _ t12 _ _ _ .pt rfl rfl rfl rfl (by intro _ _ _ _ h; cases h),
    show visBetween _ t5 t6 _ _ = visBetween _ t5 (encTr t5 "alice" 30 stA0 key0) _ _ from rfl,
    filter_pt_visBetween_enc,
    show visBetween _ t6 t7 _ _ = visBetween _ t6 (encTr t6 "alice" 36 stA1 key1) _ _ from rfl,
    filter_pt_visBetween_enc,
    show visBetween _ t9 t10 _ _ = visBetween _ t9 (encTr t9 "bob" 57 stB2 key2) _ _ from rfl,
    filter_pt_visBetween_enc,
    show visBetween _ t13 t14 _ _ = visBetween _ t13 (encTr t13 "alice" 71 stA4 key3) _ _ from rfl,
    filter_pt_visBetween_enc, t5_length, t6_length, t9_length, t13_length]
  rfl

theorem plaintextTerms_visAt_3 : plaintextTerms (visAt 3) = [m0, m1] := by
  unfold plaintextTerms visAt
  rw [filter_flatMap_flatten,
    show Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 3 =
      (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 10).take 3 by
        rw [List.take_take]; rfl,
    List.map_take, visSteps_filter_pt_prefix]
  rfl

theorem plaintextTerms_visAt_4 : plaintextTerms (visAt 4) = [m0, m1] := by
  unfold plaintextTerms visAt
  rw [filter_flatMap_flatten,
    show Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 4 =
      (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 10).take 4 by
        rw [List.take_take]; rfl,
    List.map_take, visSteps_filter_pt_prefix]
  rfl

theorem plaintextTerms_visAt_6 : plaintextTerms (visAt 6) = [m0, m1, m2] := by
  unfold plaintextTerms visAt
  rw [filter_flatMap_flatten,
    show Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 6 =
      (Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux.visSteps.take 10).take 6 by
        rw [List.take_take]; rfl,
    List.map_take, visSteps_filter_pt_prefix]
  rfl

theorem plaintextTerms_visAt_10 : plaintextTerms (visAt 10) = [m0, m1, m2, m3] := by
  unfold plaintextTerms visAt
  rw [filter_flatMap_flatten, visSteps_filter_pt_prefix]
  rfl

private theorem storedStates_self (r : ProtocolSetup) :
    storedStates r (DY.Libsignal.Composed.Refinement.setupTrace r) = [] := by
  simp [storedStates, DY.Libsignal.Composed.Refinement.newIndices]

private theorem storedStates_append {E1 : Type} [ExecTraceTypes.Has E1]
    (r : ProtocolSetup) (tr : ExecTrace) (e : E1)
    (hle : (DY.Libsignal.Composed.Refinement.setupTrace r).length ≤ tr.length) :
    storedStates r (tr.append e) =
      storedStates r tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (PersistentGlobalState.State.ExecEntryT
            (PersistentLocalState.LocalState TRState)))).map (·.st)).toList := by
  change ((DY.Libsignal.Composed.Refinement.newIndices
      (DY.Libsignal.Composed.Refinement.setupTrace r) (tr.append e)).filterMap fun i =>
      (((tr.append e).at? i : Option (PersistentGlobalState.State.ExecEntryT
        (PersistentLocalState.LocalState TRState)))).map (·.st)) =
    ((DY.Libsignal.Composed.Refinement.newIndices
      (DY.Libsignal.Composed.Refinement.setupTrace r) tr).filterMap fun i =>
      ((tr.at? i : Option (PersistentGlobalState.State.ExecEntryT
        (PersistentLocalState.LocalState TRState)))).map (·.st)) ++ _
  exact newIndices_filterMap_at?_append
    (E2 := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))
    (DY.Libsignal.Composed.Refinement.setupTrace r) tr e
    (fun _ o => o.map (·.st)) hle

private theorem storedStates_encTr (r : ProtocolSetup) (tr : ExecTrace) (me : Participant)
    (stH : Nat) (st : TRState) (pq : DY.Bytes)
    (hle : (DY.Libsignal.Composed.Refinement.setupTrace r).length ≤ tr.length) :
    storedStates r (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) =
      storedStates r tr ++
      [⟨me, Symbolic.Proofs.Tests.Shared.Composed.Runs.encSt st
          (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd (tr.length + 1) 32)⟩] := by
  unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
  dsimp only
  repeat rw [storedStates_append _ _ _ (by simp -failIfUnchanged only [length_append]; omega)]
  repeat erw [List.append_nil]
  rfl

theorem storedStates_trAt_3 :
    storedStates r0Comp (trAt 3) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1⟩, ⟨"alice", stA2⟩] := by
  change storedStates r0Comp t7 = _
  have ht4 : (DY.Libsignal.Composed.Refinement.setupTrace r0Comp).length = 22 := by
    rw [setupTrace_r0Comp, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
  have hs5 : storedStates r0Comp t5 = [⟨"alice", stA0⟩] := by
    unfold t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    repeat rw [storedStates_append _ _ _
      (by simp -failIfUnchanged only [length_append, ht4,
        Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; omega)]
    rw [← setupTrace_r0Comp, storedStates_self, setupTrace_r0Comp,
      Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
    rfl
  have hs6 : storedStates r0Comp t6 = [⟨"alice", stA0⟩, ⟨"alice", stA1⟩] := by
    unfold t6
    rw [storedStates_encTr _ _ _ _ _ _
      (by rw [ht4, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t5_length]; omega),
      hs5, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t5_length]
    rfl
  unfold t7
  rw [storedStates_encTr _ _ _ _ _ _
    (by rw [ht4, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t6_length]; omega),
    hs6, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t6_length]
  rfl

theorem storedStates_trAt_4 :
    storedStates r0Comp (trAt 4) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1⟩, ⟨"alice", stA2⟩, ⟨"bob", stB1⟩] := by
  change storedStates r0Comp t8 = _
  have ht4 : (DY.Libsignal.Composed.Refinement.setupTrace r0Comp).length = 22 := by
    rw [setupTrace_r0Comp, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
  unfold t8
  dsimp only
  repeat rw [storedStates_append _ _ _
    (by simp -failIfUnchanged only [length_append, ht4,
      Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t7_length]; omega)]
  rw [show t7 = trAt 3 from rfl, storedStates_trAt_3]
  rfl

theorem storedStates_trAt_6 :
    storedStates r0Comp (trAt 6) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1⟩, ⟨"alice", stA2⟩,
       ⟨"bob", stB1⟩, ⟨"bob", stB2⟩, ⟨"bob", stB3⟩] := by
  change storedStates r0Comp t10 = _
  have ht4 : (DY.Libsignal.Composed.Refinement.setupTrace r0Comp).length = 22 := by
    rw [setupTrace_r0Comp, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
  have hs9 : storedStates r0Comp t9 =
      [⟨"alice", stA0⟩, ⟨"alice", stA1⟩, ⟨"alice", stA2⟩, ⟨"bob", stB1⟩, ⟨"bob", stB2⟩] := by
    unfold t9
    dsimp only
    repeat rw [storedStates_append _ _ _
      (by simp -failIfUnchanged only [length_append, ht4,
        Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t8_length]; omega)]
    rw [show t8 = trAt 4 from rfl, storedStates_trAt_4]
    rfl
  unfold t10
  rw [storedStates_encTr _ _ _ _ _ _
    (by rw [ht4, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t9_length]; omega),
    hs9, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t9_length]
  rfl

theorem storedStates_trAt_10 :
    storedStates r0Comp (trAt 10) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1⟩, ⟨"alice", stA2⟩,
       ⟨"bob", stB1⟩, ⟨"bob", stB2⟩, ⟨"bob", stB3⟩,
       ⟨"alice", stA4⟩, ⟨"alice", stA5⟩] := by
  change storedStates r0Comp t14 = _
  have ht4 : (DY.Libsignal.Composed.Refinement.setupTrace r0Comp).length = 22 := by
    rw [setupTrace_r0Comp, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
  have hs13 : storedStates r0Comp t13 =
      [⟨"alice", stA0⟩, ⟨"alice", stA1⟩, ⟨"alice", stA2⟩,
       ⟨"bob", stB1⟩, ⟨"bob", stB2⟩, ⟨"bob", stB3⟩, ⟨"alice", stA4⟩] := by
    unfold t13 t12 t11
      Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCksTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCkrTr
    dsimp only
    repeat rw [storedStates_append _ _ _
      (by simp -failIfUnchanged only [length_append, ht4,
        Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t10_length]; omega)]
    rw [show t10 = trAt 6 from rfl, storedStates_trAt_6]
    rfl
  unfold t14
  rw [storedStates_encTr _ _ _ _ _ _
    (by rw [ht4, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13_length]; omega),
    hs13, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13_length]
  rfl

def pqSecretsList : List DY.Bytes :=
  [Comparse.serialize (⟨"alice", { kind := .identity, sk := ikA }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   Comparse.serialize (⟨"bob", { kind := .identity, sk := ikB }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   Comparse.serialize (⟨"bob", { kind := .signedPrekey, sk := spkB }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   Comparse.serialize (⟨"bob", { kind := .pqPrekey, sk := pqskB }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)]

private theorem storedSecrets_nil : storedSecrets Trace.nil = [] := by
  rw [storedSecrets, Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem storedSecrets_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    storedSecrets (tr.append e) =
      storedSecrets tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (PersistentGlobalState.State.ExecEntryT
            (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)))).map
        fun x => Comparse.serialize x.st).toList := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  simp only [Option.map_map]
  exact range_filterMap_at?_append
    (E2 := PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState))
    tr e (fun o => o.map fun x => Comparse.serialize x.st)

private theorem storedSecrets_encTr (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : DY.Bytes) :
    storedSecrets (Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr tr me stH st pq) =
      storedSecrets tr := by
  simp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr, storedSecrets_append]
  repeat erw [List.append_nil]

theorem storedSecrets_trAt_3 : storedSecrets (trAt 3) = pqSecretsList := by
  change storedSecrets t7 = _
  have hs4 : storedSecrets t4 = pqSecretsList := by
    rw [t4_eq_pure]
    simp only [t4Pure, t3Pure, t2Pure, t1Pure, registerIdentityTr, genSignedPrekeyTr, genPQPrekeyTr,
      storedSecrets_append, storedSecrets_nil, length_append,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  unfold t7 t6 t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  simp only [storedSecrets_encTr, storedSecrets_append, hs4]
  rfl

theorem storedSecrets_trAt_4 : storedSecrets (trAt 4) = pqSecretsList := by
  change storedSecrets t8 = _
  unfold t8
  simp only [storedSecrets_append]
  rw [show t7 = trAt 3 from rfl, storedSecrets_trAt_3]; rfl

theorem storedSecrets_trAt_6 : storedSecrets (trAt 6) = pqSecretsList := by
  change storedSecrets t10 = _
  unfold t10 t9
  simp only [storedSecrets_encTr, storedSecrets_append]
  rw [show t8 = trAt 4 from rfl, storedSecrets_trAt_4]; rfl

theorem storedSecrets_trAt_10 : storedSecrets (trAt 10) = pqSecretsList := by
  change storedSecrets t14 = _
  unfold t14 t13 t12 t11
    Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCksTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCkrTr
  simp only [storedSecrets_encTr, storedSecrets_append]
  rw [show t10 = trAt 6 from rfl, storedSecrets_trAt_6]; rfl

/-! ## `bobDoneBaseKeys`, `storedRatchetKeys`, and `whisperTrials` -/

private theorem bobDoneBaseKeys_nil : bobDoneBaseKeys Trace.nil = [] := by
  rw [bobDoneBaseKeys, Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem bobDoneBaseKeys_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    bobDoneBaseKeys (tr.append e) =
      bobDoneBaseKeys tr ++
      (match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with
        | some ⟨.BobDone _ _ _ _ _ _ _ ek _ _⟩ => some ek
        | _ => none).toList := by
  unfold bobDoneBaseKeys
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [length_append, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, at?_append_self]
  refine congrArg₂ List.append (List.filterMap_congr fun i hi => ?_) ?_
  · rw [at?_append_of_lt tr e (List.mem_range.mp hi)]
  · cases (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with
    | none => rfl
    | some entry => rcases entry with ⟨ev⟩; cases ev <;> rfl

theorem bobDoneBaseKeys_trAt_4 : bobDoneBaseKeys (trAt 4) = [x4Rep.ek] := by
  change bobDoneBaseKeys t8 = [ekTerm]
  rw [ekTerm_eq_o1_ek]
  have hb4 : bobDoneBaseKeys t4 = [] := by
    rw [t4_eq_pure]
    simp only [t4Pure, t3Pure, t2Pure, t1Pure, registerIdentityTr, genSignedPrekeyTr, genPQPrekeyTr,
      bobDoneBaseKeys_append, bobDoneBaseKeys_nil]
    rfl
  unfold t8 t7 t6 t5
    Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  simp only [bobDoneBaseKeys_append, hb4]
  rfl

def noSkippedKeyStored (tr : ExecTrace) : Bool :=
  (List.range tr.length).all fun i =>
    match tr.getEventAt TREvent i with
    | some (.SkippedKeyStored ..) => false
    | _ => true

private theorem noSkippedKeyStored_nil : noSkippedKeyStored Trace.nil = true := by
  rw [noSkippedKeyStored, Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem noSkippedKeyStored_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    noSkippedKeyStored (tr.append e) =
      (noSkippedKeyStored tr &&
        match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
            Option (ProtocolEvent.ExecEntryT TREvent)) with
        | some ⟨.SkippedKeyStored ..⟩ => false
        | _ => true) := by
  unfold noSkippedKeyStored
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [length_append, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    at?_append_self]
  refine congrArg₂ Bool.and ?_ ?_
  · rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact forall_congr' fun i => imp_congr_right fun hi => by
      rw [at?_append_of_lt tr e (List.mem_range.mp hi)]
  · cases (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT TREvent)) with
    | none => rfl
    | some entry => rcases entry with ⟨ev⟩; cases ev <;> rfl

theorem noSkippedKeyStored_trAt_4 : noSkippedKeyStored (trAt 4) = true := by
  change noSkippedKeyStored t8 = true
  have hn4 : noSkippedKeyStored t4 = true := by
    rw [t4_eq_pure]
    simp only [t4Pure, t3Pure, t2Pure, t1Pure, registerIdentityTr, genSignedPrekeyTr, genPQPrekeyTr,
      noSkippedKeyStored_append, noSkippedKeyStored_nil]
    rfl
  unfold t8 t7 t6 t5
    Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  simp only [noSkippedKeyStored_append, hn4]
  rfl

theorem noSkippedKeyStored_trAt_6 : noSkippedKeyStored (trAt 6) = true := by
  change noSkippedKeyStored t10 = true
  unfold t10 t9 Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
  simp only [noSkippedKeyStored_append]
  rw [show t8 = trAt 4 from rfl, noSkippedKeyStored_trAt_4]; rfl

theorem noSkippedKeyStored_trAt_10 : noSkippedKeyStored (trAt 10) = true := by
  change noSkippedKeyStored t14 = true
  unfold t14 t13 t12 t11
    Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCksTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCkrTr
  simp only [noSkippedKeyStored_append]
  rw [show t10 = trAt 6 from rfl, noSkippedKeyStored_trAt_6]; rfl

def storedRatchetKeysNoSkipped (r : ProtocolSetup) (tr : ExecTrace) : List DY.Bytes :=
  (availableStates r tr).flatMap fun st => st.toDRState.recv.map (·.ratchetKey)

theorem storedRatchetKeys_of_noSkipped {r : ProtocolSetup} {tr : ExecTrace}
    (h : noSkippedKeyStored tr = true) (msg : TRSignalMsg) :
    storedRatchetKeys r tr msg = storedRatchetKeysNoSkipped r tr := by
  unfold storedRatchetKeys storedRatchetKeysNoSkipped
  refine List.append_right_eq_self.mpr ?_
  rw [List.filterMap_eq_nil_iff]
  intro i hi
  have hi' := List.all_eq_true.mp h i hi
  rcases he : tr.getEventAt TREvent i with _ | e
  · rfl
  · rw [he] at hi'; cases e <;> simp_all

theorem storedRatchetKeys_trAt_4 (msg : TRSignalMsg) :
    storedRatchetKeys r0Comp (trAt 4) msg = storedRatchetKeysNoSkipped r0Comp (trAt 4) :=
  storedRatchetKeys_of_noSkipped noSkippedKeyStored_trAt_4 msg

theorem storedRatchetKeys_trAt_6 (msg : TRSignalMsg) :
    storedRatchetKeys r0Comp (trAt 6) msg = storedRatchetKeysNoSkipped r0Comp (trAt 6) :=
  storedRatchetKeys_of_noSkipped noSkippedKeyStored_trAt_6 msg

theorem storedRatchetKeys_trAt_10 (msg : TRSignalMsg) :
    storedRatchetKeys r0Comp (trAt 10) msg = storedRatchetKeysNoSkipped r0Comp (trAt 10) :=
  storedRatchetKeys_of_noSkipped noSkippedKeyStored_trAt_10 msg

noncomputable def whisperTrialsNoSkipped (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (msg : TRSignalMsg) : List TrialCtx :=
  if msg.version = messageVersion then
    let γ := gamma interp S g
    (availableStates r tr).flatMap fun st =>
      let own := ownKeys r tr st msg
      let chains :=
        (st.toDRState.recv.filter fun c => decide (γ c.ratchetKey = γ msg.ratchetKey)) ++
        match recvChainFor st.toDRState msg.ratchetKey with
        | some (c, true) => [c]
        | _ => []
      chains.map fun c =>
        match consumeMessageKey c msg.counter with
        | none =>
          { peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
            ownSalts := [], seed? := none }
        | some (seed, c') =>
          { peerIk := st.peerIk, myIk := st.myIk,
            extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
            ownSalts := own, seed? := some seed }
  else []

theorem whisperTrials_of_noSkipped {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace}
    (h : noSkippedKeyStored tr = true) (msg : TRSignalMsg) :
    whisperTrials interp r S g tr msg = whisperTrialsNoSkipped interp r S g tr msg := by
  unfold whisperTrials whisperTrialsNoSkipped
  split
  · dsimp only
    congr 1; funext st
    refine (List.append_right_eq_self.mpr ?_).trans ?_
    · rw [List.filterMap_eq_nil_iff]
      intro i hi
      have hi' := List.all_eq_true.mp h i hi
      rcases he : tr.getEventAt TREvent i with _ | e
      · rfl
      · rw [he] at hi'; cases e <;> simp_all
    · congr 1; congr 1
      unfold recvChainFor DY.Libsignal.TripleRatchet.recvHalfStep
      dsimp only [TRState.toDRState]
      cases h1 : DY.Libsignal.TripleRatchet.findRecvChain st.recv msg.ratchetKey <;>
        cases h2 : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey <;>
        rfl
  · rfl

theorem whisperTrials_trAt_4 (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (msg : TRSignalMsg) :
    whisperTrials interp r0Comp S g (trAt 4) msg =
      whisperTrialsNoSkipped interp r0Comp S g (trAt 4) msg :=
  whisperTrials_of_noSkipped noSkippedKeyStored_trAt_4 msg

theorem whisperTrials_trAt_6 (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (msg : TRSignalMsg) :
    whisperTrials interp r0Comp S g (trAt 6) msg =
      whisperTrialsNoSkipped interp r0Comp S g (trAt 6) msg :=
  whisperTrials_of_noSkipped noSkippedKeyStored_trAt_6 msg

theorem whisperTrials_trAt_10 (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (msg : TRSignalMsg) :
    whisperTrials interp r0Comp S g (trAt 10) msg =
      whisperTrialsNoSkipped interp r0Comp S g (trAt 10) msg :=
  whisperTrials_of_noSkipped noSkippedKeyStored_trAt_10 msg

end Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
