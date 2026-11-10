/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Specifications.Refinement.TraceExplanation
import Mathlib.Data.List.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Initial Setup Trace and Empty Composed Model Run

Proves that for any well-formed `ProtocolSetupWF r`, the empty move list forms a valid composed
`ModelRun r []` (`modelRun_nil_pq` / `modelRun_nil`), together with explicit `setupTr1`..`setupTr5`
characterizations, `newRandoms` evaluations, and setup reachability (`setupTrace_reachable`).
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

/-! ## Propositional `Trace.at?` and `newRandoms` append lemmas -/

theorem proj_inj_eq {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_self {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e := by
  have hlt : tr.length < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]
  exact proj_inj_eq e

theorem at?_append_eq {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    {i : Nat} (hi : i = tr.length) :
    ((tr.append e).at? i : Option E) = some e := by
  subst hi; exact at?_append_self tr e

theorem at?_append_eq_of_proj {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i = tr.length) (o : Option E2)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = o) :
    ((tr.append e).at? i : Option E2) = o := by
  subst hi
  have hlt : tr.length < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]
  exact hproj

theorem newIndices_nil_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    newIndices Trace.nil (tr.append e) = newIndices Trace.nil tr ++ [tr.length] := by
  have hlen0 : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have hlen1 : (tr.append e).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [newIndices, hlen0, hlen1, Nat.sub_zero]
  rw [List.range'_concat]
  simp only [Nat.one_mul, Nat.zero_add]

theorem newRandoms_nil : newRandoms Trace.nil Trace.nil = [] := by
  simp only [newRandoms, newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  rfl

theorem newRandoms_append_aux {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    newRandoms Trace.nil (tr.append e) =
      newRandoms Trace.nil tr ++
        (((tr.append e).at? tr.length : Option DY.Random.ExecEntryT).map
          fun r => (randTerm tr.length r.length, r.length)).toList := by
  have hlen0 : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have hcongr :
      List.filterMap
        (fun i => ((tr.append e).at? i : Option DY.Random.ExecEntryT).map fun r => (randTerm i r.length, r.length))
        (newIndices Trace.nil tr) =
      newRandoms Trace.nil tr := by
    unfold newRandoms
    refine List.filterMap_congr fun i hi => ?_
    have hlt : i < tr.length := by
      simp only [newIndices, hlen0, Nat.sub_zero, List.mem_range'_1] at hi
      omega
    rw [at?_append_of_lt tr e hlt]
  unfold newRandoms
  rw [newIndices_nil_append, List.filterMap_append, hcongr, List.filterMap_cons, List.filterMap_nil]
  cases ((tr.append e).at? tr.length : Option DY.Random.ExecEntryT) <;> rfl

abbrev EvE (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent :=
  DY.ProtocolEvent.ExecEntryT.mk ev

abbrev NetE (b : DY.Bytes) : DY.Network.ExecEntryT :=
  DY.Network.ExecEntryT.mk b

abbrev StE (me : DY.Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :=
  DY.PersistentGlobalState.State.ExecEntryT.mk
    ({ participant := me, state := st } :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)

abbrev RndE (n : Nat) : DY.Random.ExecEntryT :=
  DY.Random.ExecEntryT.mk n

theorem newRandoms_append_rnd (tr : ExecTrace) (n : Nat) :
    newRandoms Trace.nil (tr.append (RndE n)) =
      newRandoms Trace.nil tr ++ [(randTerm tr.length n, n)] := by
  rw [newRandoms_append_aux, at?_append_self]
  rfl

theorem newRandoms_append_nonRnd {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none) :
    newRandoms Trace.nil (tr.append e) = newRandoms Trace.nil tr := by
  rw [newRandoms_append_aux, at?_append_eq_of_proj tr e rfl none hproj]
  simp

/-! ## Symbolic `Runs` combinators for `setupAct` -/

def Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

theorem Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} {b : β}
    (h1 : Runs x tr a tr1) (h2 : Runs (f a) tr1 b tr2) :
    Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b
  cases h1a
  cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b
  cases h2a
  cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

theorem Runs.pure {α : Type} (a : α) (tr : ExecTrace) :
    Runs (Pure.pure a : Traceful α) tr a tr := by
  unfold Runs; simp only [Traceful.run_pure, and_self]

theorem Runs.getEntry {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : tr.at? i = some e) : Runs (DY.getEntry i : Traceful E) tr e tr := by
  unfold Runs; simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨h, trivial⟩

theorem Runs.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold Runs; simp only [Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk, and_self]

theorem Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    Runs (_root_.guard p : Traceful Unit) tr () tr := by
  unfold Runs; simp only [_root_.guard, h, ↓reduceIte, Traceful.run_pure, and_self]

theorem Runs.logEvent (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    Runs (DY.ProtocolEvent.logEvent ev) tr () (tr.append (EvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

theorem Runs.genRand (tr : ExecTrace) (n : Nat) :
    Runs (DY.Random.genRand n) tr (randTerm tr.length n) (tr.append (RndE n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

theorem Runs.sendMessage (tr : ExecTrace) (b : DY.Bytes) :
    Runs (DY.Network.sendMessage b) tr tr.length (tr.append (NetE b)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact Runs.appendEntry _ _

theorem Runs.storeLocalState (tr : ExecTrace) (me : DY.Participant)
    (st : DY.Libsignal.PQXDH.PQXDHState) :
    Runs (DY.PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (StE me st)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact Runs.appendEntry _ _

theorem Runs.getKey {tr : ExecTrace} {me : DY.Participant} {h : Nat}
    {kind : DY.Libsignal.PQXDH.KeyKind} {sk : DY.Bytes}
    (hst : tr.at? h = some (StE me { kind, sk })) :
    Runs (DY.Libsignal.PQXDH.getKey me h kind) tr sk tr := by
  unfold DY.Libsignal.PQXDH.getKey
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Runs.bind (Runs.bind (Runs.bind (Runs.getEntry hst) (Runs.pure _ _))
    (Runs.bind (Runs.guard _ rfl) (Runs.pure _ _))) ?_
  exact Runs.bind (Runs.guard _ rfl) (Runs.pure _ _)

theorem Runs.requireTracePredicate {p : ExecTrace → Bool} {tr : ExecTrace} (h : p tr = true) :
    Runs (DY.Libsignal.PQXDH.guardTrace p) tr () tr := by
  unfold Runs DY.Libsignal.PQXDH.guardTrace
  simp only [Traceful.run_mk, h, ↓reduceIte]
  exact ⟨trivial, trivial⟩

/-! ## Explicit setup traces -/

def setupTr1 (a : DY.Participant) : ExecTrace :=
  ((((Trace.nil.append (RndE 32)).append
    (EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
      (DY.Signature.vk (randTerm 0 32)) true))).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 0 32)))).append
    (NetE (DY.Signature.vk (randTerm 0 32)))).append
    (StE a { kind := .identity, sk := randTerm 0 32 })

def setupTr2 (a b : DY.Participant) : ExecTrace :=
  (((((setupTr1 a).append (RndE 32)).append
    (EvE (.IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32))
      (DY.Signature.vk (randTerm 5 32)) true))).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 5 32)))).append
    (NetE (DY.Signature.vk (randTerm 5 32)))).append
    (StE b { kind := .identity, sk := randTerm 5 32 })

def setupTr3 (a b : DY.Participant) : ExecTrace :=
  ((((((setupTr2 a b).append (RndE 32)).append (RndE 64)).append
    (EvE (.SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 10 32))))).append
    (StE b { kind := .signedPrekey, sk := randTerm 10 32 })).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 10 32)))).append
    (NetE (DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
      (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32)))))

def setupTr4 (a b : DY.Participant) : ExecTrace :=
  ((((((setupTr3 a b).append (RndE 64)).append (RndE 64)).append
    (EvE (.PQPrekeyPublished b (DY.PQKem.kemPk (randTerm 16 64))))).append
    (StE b { kind := .pqPrekey, sk := randTerm 16 64 })).append
    (NetE (DY.PQKem.kemPk (randTerm 16 64)))).append
    (NetE (DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
      (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))))

def setupTr5 (a b : DY.Participant) : ExecTrace :=
  ((((setupTr4 a b).append (RndE 32)).append
    (EvE (.OneTimePrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 22 32))))).append
    (StE b { kind := .oneTimePrekey, sk := randTerm 22 32 })).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 22 32)))

theorem runs_registerIdentity_a (a : DY.Participant) :
    Runs (DY.Libsignal.PQXDH.registerIdentity a) Trace.nil 4 (setupTr1 a) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  have hpred : (!DY.Libsignal.PQXDH.isRegisteredB Trace.nil a) = true := by
    simp only [DY.Libsignal.PQXDH.isRegisteredB, DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  refine Runs.bind (Runs.requireTracePredicate hpred) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  convert Runs.storeLocalState _ _ _ using 2
  · simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  · rfl

theorem setupTr1_at?_ev_0 (a : DY.Participant) :
    ((setupTr1 a).at? 0 :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
  unfold setupTr1
  rw [at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])]
  exact at?_append_eq_of_proj _ _ (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1]) none rfl

theorem setupTr1_at?_ev_1 (a : DY.Participant) :
    ((setupTr1 a).at? 1 :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
      some (EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
        (DY.Signature.vk (randTerm 0 32)) true)) := by
  unfold setupTr1
  rw [at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])]
  exact at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])

theorem setupTr1_at?_ev_2 (a : DY.Participant) :
    ((setupTr1 a).at? 2 :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
  unfold setupTr1
  rw [at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])]
  exact at?_append_eq_of_proj _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]) none rfl

theorem setupTr1_at?_ev_3 (a : DY.Participant) :
    ((setupTr1 a).at? 3 :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
  unfold setupTr1
  rw [at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])]
  exact at?_append_eq_of_proj _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]) none rfl

theorem setupTr1_at?_ev_4 (a : DY.Participant) :
    ((setupTr1 a).at? 4 :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
  unfold setupTr1
  exact at?_append_eq_of_proj _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]) none rfl

theorem not_isRegisteredB_setupTr1 {a b : DY.Participant} (hNe : a ≠ b) :
    (!DY.Libsignal.PQXDH.isRegisteredB (setupTr1 a) b) = true := by
  have hbeq : (a == b) = false := beq_false_of_ne hNe
  have hlen : (setupTr1 a).length = 5 := by
    simp [setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hrng : List.range 5 = [0, 1, 2, 3, 4] := rfl
  unfold DY.Libsignal.PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [hlen, hrng]
  simp only [List.any_cons, List.any_nil, Bool.or_false,
    setupTr1_at?_ev_0, setupTr1_at?_ev_1, setupTr1_at?_ev_2,
    setupTr1_at?_ev_3, setupTr1_at?_ev_4, hbeq]
  rfl

theorem runs_registerIdentity_b {a b : DY.Participant} (hNe : a ≠ b) :
    Runs (DY.Libsignal.PQXDH.registerIdentity b) (setupTr1 a) 9 (setupTr2 a b) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  have hlen1 : (setupTr1 a).length = 5 := by
    simp [setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  refine Runs.bind (Runs.requireTracePredicate (not_isRegisteredB_setupTr1 hNe)) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  rw [hlen1]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  convert Runs.storeLocalState _ _ _ using 2
  · simp [hlen1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  · rfl

theorem setupTr2_at?_9 (a b : DY.Participant) :
    (setupTr2 a b).at? 9 = some (StE b { kind := .identity, sk := randTerm 5 32 }) := by
  unfold setupTr2
  exact at?_append_eq _ _ (by
    simp [setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])

theorem setupTr2_length (a b : DY.Participant) : (setupTr2 a b).length = 10 := by
  simp [setupTr2, setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem setupTr3_at?_9 (a b : DY.Participant) :
    (setupTr3 a b).at? 9 = some (StE b { kind := .identity, sk := randTerm 5 32 }) := by
  unfold setupTr3
  rw [at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]),
    at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]),
    at?_append_of_lt _ _ (by simp [setupTr2_length])]
  exact setupTr2_at?_9 a b

theorem runs_genSignedPrekey (a b : DY.Participant) :
    Runs (DY.Libsignal.PQXDH.genSignedPrekey b 9) (setupTr2 a b) 13 (setupTr3 a b) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  have h10 := setupTr2_length a b
  have h11 : ((setupTr2 a b).append (RndE 32)).length = 11 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, h10]
  refine Runs.bind (Runs.getKey (setupTr2_at?_9 a b)) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  rw [h10]
  refine Runs.bind (Runs.genRand _ _) ?_
  rw [h11]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.storeLocalState _ _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  convert Runs.pure _ _ using 2
  · simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, h10]
  · rfl

theorem runs_genPQPrekey (a b : DY.Participant) :
    Runs (DY.Libsignal.PQXDH.genPQPrekey b 9) (setupTr3 a b) 19 (setupTr4 a b) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  have h16 : (setupTr3 a b).length = 16 := by
    simp [setupTr3, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]
  have h17 : ((setupTr3 a b).append (RndE 64)).length = 17 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, h16]
  refine Runs.bind (Runs.getKey (setupTr3_at?_9 a b)) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  rw [h16]
  refine Runs.bind (Runs.genRand _ _) ?_
  rw [h17]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.storeLocalState _ _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  convert Runs.pure _ _ using 2
  · simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, h16]
  · rfl

theorem runs_genOneTimePrekey (a b : DY.Participant) :
    Runs (DY.Libsignal.PQXDH.genOneTimePrekey b) (setupTr4 a b) 24 (setupTr5 a b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  have h22 : (setupTr4 a b).length = 22 := by
    simp [setupTr4, setupTr3, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]
  refine Runs.bind (Runs.genRand _ _) ?_
  rw [h22]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.storeLocalState _ _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  convert Runs.pure _ _ using 2
  · simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, h22]
  · rfl

/-! ## Evaluating `newRandoms` on `setupTr4` and `setupTr5` -/

theorem newRandoms_setupTr1 (a : DY.Participant) :
    newRandoms Trace.nil (setupTr1 a) = [(randTerm 0 32, 32)] := by
  unfold setupTr1
  rw [newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_rnd, newRandoms_nil]
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1]

theorem newRandoms_setupTr2 (a b : DY.Participant) :
    newRandoms Trace.nil (setupTr2 a b) = [(randTerm 0 32, 32), (randTerm 5 32, 32)] := by
  unfold setupTr2
  rw [newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_rnd, newRandoms_setupTr1]
  simp [setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem newRandoms_setupTr3 (a b : DY.Participant) :
    newRandoms Trace.nil (setupTr3 a b) =
      [(randTerm 0 32, 32), (randTerm 5 32, 32), (randTerm 10 32, 32), (randTerm 11 64, 64)] := by
  unfold setupTr3
  rw [newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_rnd, newRandoms_append_rnd, newRandoms_setupTr2]
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]

theorem newRandoms_setupTr4 (a b : DY.Participant) :
    newRandoms Trace.nil (setupTr4 a b) =
      [(randTerm 0 32, 32), (randTerm 5 32, 32), (randTerm 10 32, 32), (randTerm 11 64, 64),
       (randTerm 16 64, 64), (randTerm 17 64, 64)] := by
  unfold setupTr4
  rw [newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_rnd, newRandoms_append_rnd, newRandoms_setupTr3]
  simp [setupTr3, Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]

theorem newRandoms_setupTr5 (a b : DY.Participant) :
    newRandoms Trace.nil (setupTr5 a b) =
      [(randTerm 0 32, 32), (randTerm 5 32, 32), (randTerm 10 32, 32), (randTerm 11 64, 64),
       (randTerm 16 64, 64), (randTerm 17 64, 64), (randTerm 22 32, 32)] := by
  unfold setupTr5
  rw [newRandoms_append_nonRnd _ _ rfl, newRandoms_append_nonRnd _ _ rfl,
    newRandoms_append_nonRnd _ _ rfl, newRandoms_append_rnd, newRandoms_setupTr4]
  simp [setupTr4, setupTr3, Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2, setupTr2_length]

attribute [local irreducible] setupTr1 setupTr2 setupTr3 setupTr4 setupTr5

theorem runs_setupAct (a b : DY.Participant) (withOpk : Bool) (hNe : a ≠ b) :
    Runs (setupAct a b withOpk) Trace.nil ()
      (if withOpk then setupTr5 a b else setupTr4 a b) := by
  unfold setupAct
  refine Runs.bind (runs_registerIdentity_a a) ?_
  refine Runs.bind (runs_registerIdentity_b hNe) ?_
  refine Runs.bind (runs_genSignedPrekey a b) ?_
  refine Runs.bind (runs_genPQPrekey a b) ?_
  cases withOpk with
  | false => exact Runs.pure () _
  | true => exact Runs.bind (runs_genOneTimePrekey a b) (Runs.pure () _)

theorem setupTrace_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupTrace r = if r.withOpk then setupTr5 r.alice r.bob else setupTr4 r.alice r.bob :=
  (runs_setupAct r.alice r.bob r.withOpk hNe).2

/-! ## Reachability of the setup steps -/

def ReachStep {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable DY.Libsignal.Composed.reachability →
    ((x.run tr).2.val).Reachable DY.Libsignal.Composed.reachability

theorem ReachStep.pure {α : Type} (a : α) : ReachStep (Pure.pure a : Traceful α) := by
  intro tr h; simp only [Traceful.run_pure]; exact h

theorem ReachStep.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : ReachStep x) (hf : ∀ a, ReachStep (f a)) : ReachStep (x >>= f) := by
  intro tr htr
  rw [Traceful.run_bind]
  rcases h : x.run tr with ⟨_ | a, trMid, _⟩
  · have := hx tr htr; rwa [h] at this
  · have := hx tr htr; rw [h] at this; exact hf a trMid this

theorem ReachStep.registerIdentity (p : Participant) :
    ReachStep (DY.Libsignal.PQXDH.registerIdentity p) :=
  fun tr h =>
    (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.registerIdentity.reachability
      DY.Libsignal.Composed.reachability p tr h trivial).1

theorem ReachStep.genSignedPrekey (b : Participant) (i : Nat) :
    ReachStep (DY.Libsignal.PQXDH.genSignedPrekey b i) :=
  fun tr h =>
    (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.genSignedPrekey.reachability
      DY.Libsignal.Composed.reachability (b, i) tr h trivial).1

theorem ReachStep.genPQPrekey (b : Participant) (i : Nat) :
    ReachStep (DY.Libsignal.PQXDH.genPQPrekey b i) :=
  fun tr h =>
    (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.genPQPrekey.reachability
      DY.Libsignal.Composed.reachability (b, i) tr h trivial).1

theorem ReachStep.genOneTimePrekey (b : Participant) :
    ReachStep (DY.Libsignal.PQXDH.genOneTimePrekey b) :=
  fun tr h =>
    (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.genOneTimePrekey.reachability
      DY.Libsignal.Composed.reachability b tr h trivial).1

theorem ReachStep.setupAct (a b : Participant) (withOpk : Bool) :
    ReachStep (DY.Libsignal.Composed.Refinement.setupAct a b withOpk) := by
  unfold DY.Libsignal.Composed.Refinement.setupAct
  refine ReachStep.bind (ReachStep.registerIdentity a) fun _ =>
    ReachStep.bind (ReachStep.registerIdentity b) fun hB =>
    ReachStep.bind (ReachStep.genSignedPrekey b hB) fun _ =>
    ReachStep.bind (ReachStep.genPQPrekey b hB) fun _ => ?_
  cases withOpk with
  | false => exact ReachStep.pure ()
  | true => exact ReachStep.bind (ReachStep.genOneTimePrekey b) fun _ => ReachStep.pure ()

/-! ## Main theorems -/

theorem setupRandoms_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupRandoms r =
      if r.withOpk then
        [randTerm 0 32, randTerm 5 32, randTerm 10 32, randTerm 11 64,
         randTerm 16 64, randTerm 17 64, randTerm 22 32]
      else
        [randTerm 0 32, randTerm 5 32, randTerm 10 32, randTerm 11 64,
         randTerm 16 64, randTerm 17 64] := by
  rw [setupRandoms, setupTrace_eq r hNe]
  cases r.withOpk with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, newRandoms_setupTr4]
    rfl
  | true =>
    simp only [↓reduceIte, newRandoms_setupTr5]
    rfl

theorem setupRandoms_length (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    (setupRandoms r).length = (if r.withOpk then 7 else 6) := by
  rw [setupRandoms_eq r hNe]
  cases r.withOpk <;> rfl

theorem setupTrace_reachable (r : ProtocolSetup) :
    (setupTrace r).Reachable DY.Libsignal.Composed.reachability :=
  ReachStep.setupAct r.alice r.bob r.withOpk Trace.nil .Base

/-- The empty move list forms a valid composed `ModelRun` for any well-formed setup `r`. -/
theorem modelRun_nil_pq (r : ProtocolSetup) (hwf : ProtocolSetupWF r) : ModelRun r [] := by
  refine ⟨setupRandoms_length r hwf.1, ?_, ⟨?_, trivial, fun k => ?_⟩, rfl, rfl, ?_, ?_⟩
  · intro m hm
    cases hm
  · rw [runTraceMoves, runMoves, setupMove_next_nil]
    exact setupTrace_reachable r
  · rw [List.take_nil, runTraceMoves, runMoves, setupMove_next_nil]
    exact setupTrace_reachable r
  · intro m hm
    cases hm
  · intro i _ _ _ _ _ _ _ hi
    simp at hi

alias modelRun_nil := modelRun_nil_pq

end Symbolic.Swarm.CREF.TR
