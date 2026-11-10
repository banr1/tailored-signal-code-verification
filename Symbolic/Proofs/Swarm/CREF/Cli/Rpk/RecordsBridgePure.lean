/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Actions.PersistentGlobalState
public import Symbolic.Specifications.Refinement.ModelTraces
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Composed Setup-Trace Stepping

Defines the intermediate setup traces `setupTr1`..`setupTr5` for `Composed.Refinement.setupTrace`
and characterizes `setupTrace` when `r.alice = r.bob`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

open DY DY.Comparse
open DY.Libsignal

private def Runs {α : Type} [DY.ExecTraceTypes] (x : DY.Traceful α) (tr : DY.ExecTrace) (a : α)
    (tr' : DY.ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

private def Fails {α : Type} [DY.ExecTraceTypes] (x : DY.Traceful α) (tr tr' : DY.ExecTrace) :
    Prop :=
  (x.run tr).1 = none ∧ (x.run tr).2.val = tr'

private theorem Runs.bind {α β : Type} [DY.ExecTraceTypes] {x : DY.Traceful α}
    {f : α → DY.Traceful β} {tr tr1 tr2 : DY.ExecTrace} {a : α} {b : β}
    (h1 : Runs x tr a tr1) (h2 : Runs (f a) tr1 b tr2) :
    Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [DY.Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem Fails.bind_left {α β : Type} [DY.ExecTraceTypes] {x : DY.Traceful α}
    (f : α → DY.Traceful β) {tr tr1 : DY.ExecTrace} (h1 : Fails x tr tr1) :
    Fails (x >>= f) tr tr1 := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  refine ⟨?_, ?_⟩ <;> rw [DY.Traceful.run_bind, hx]

private theorem Fails.bind_right {α β : Type} [DY.ExecTraceTypes] {x : DY.Traceful α}
    {f : α → DY.Traceful β} {tr tr1 tr2 : DY.ExecTrace} {a : α}
    (h1 : Runs x tr a tr1) (h2 : Fails (f a) tr1 tr2) :
    Fails (x >>= f) tr tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [DY.Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem Runs.pure {α : Type} [DY.ExecTraceTypes] (a : α) (tr : DY.ExecTrace) :
    Runs (Pure.pure a : DY.Traceful α) tr a tr := by
  unfold Runs; rw [DY.Traceful.run_pure]; exact ⟨rfl, rfl⟩

private theorem Runs.appendEntry {E : Type} [DY.ExecTraceTypes] [DY.ExecTraceTypes.Has E]
    (tr : DY.ExecTrace) (e : E) :
    Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold Runs; rw [Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]; exact ⟨rfl, rfl⟩

section SetupStepping

open scoped DY.Libsignal.Composed
attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic

attribute [local irreducible] Bind.bind

private theorem Runs.getEntry {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : DY.ExecTrace} {i : Nat} {e : E}
    (h : tr.at? i = some e) : Runs (DY.getEntry i : DY.Traceful E) tr e tr := by
  unfold Runs; rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]; exact ⟨h, rfl⟩

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

private theorem Runs.logEvent (tr : DY.ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    Runs (DY.ProtocolEvent.logEvent ev) tr () (tr.append (EvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

private theorem Runs.genRand (tr : DY.ExecTrace) (n : Nat) :
    Runs (DY.Random.genRand n) tr (DY.Libsignal.Composed.Refinement.randTerm tr.length n)
      (tr.append (RndE n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

private theorem Runs.sendMessage (tr : DY.ExecTrace) (b : DY.Bytes) :
    Runs (DY.Network.sendMessage b) tr tr.length (tr.append (NetE b)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact Runs.appendEntry _ _

private theorem Runs.storeLocalState (tr : DY.ExecTrace) (me : DY.Participant)
    (st : DY.Libsignal.PQXDH.PQXDHState) :
    Runs (DY.PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (StE me st)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact Runs.appendEntry _ _

private theorem Runs.requireTracePredicate {p : DY.ExecTrace → Bool} {tr : DY.ExecTrace} (h : p tr = true) :
    Runs (DY.Libsignal.PQXDH.guardTrace p) tr () tr := by
  unfold Runs DY.Libsignal.PQXDH.guardTrace
  simp only [DY.Traceful.run_mk, h, ↓reduceIte]
  exact ⟨trivial, trivial⟩

private theorem Fails.requireTracePredicate {p : DY.ExecTrace → Bool} {tr : DY.ExecTrace} (h : p tr = false) :
    Fails (DY.Libsignal.PQXDH.guardTrace p) tr tr := by
  unfold Fails DY.Libsignal.PQXDH.guardTrace
  simp only [DY.Traceful.run_mk, h]
  exact ⟨rfl, trivial⟩

open DY.Libsignal.Composed.Refinement (randTerm)

def setupTr1 (a : DY.Participant) : DY.ExecTrace :=
  ((((Trace.nil.append (RndE 32)).append
    (EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
      (DY.Signature.vk (randTerm 0 32)) true))).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 0 32)))).append
    (NetE (DY.Signature.vk (randTerm 0 32)))).append
    (StE a { kind := .identity, sk := randTerm 0 32 })

def setupTr2 (a b : DY.Participant) : DY.ExecTrace :=
  (((((setupTr1 a).append (RndE 32)).append
    (EvE (.IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32))
      (DY.Signature.vk (randTerm 5 32)) true))).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 5 32)))).append
    (NetE (DY.Signature.vk (randTerm 5 32)))).append
    (StE b { kind := .identity, sk := randTerm 5 32 })

def setupTr3 (a b : DY.Participant) : DY.ExecTrace :=
  ((((((setupTr2 a b).append (RndE 32)).append (RndE 64)).append
    (EvE (.SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 10 32))))).append
    (StE b { kind := .signedPrekey, sk := randTerm 10 32 })).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 10 32)))).append
    (NetE (DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
      (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32)))))

def setupTr4 (a b : DY.Participant) : DY.ExecTrace :=
  ((((((setupTr3 a b).append (RndE 64)).append (RndE 64)).append
    (EvE (.PQPrekeyPublished b (DY.PQKem.kemPk (randTerm 16 64))))).append
    (StE b { kind := .pqPrekey, sk := randTerm 16 64 })).append
    (NetE (DY.PQKem.kemPk (randTerm 16 64)))).append
    (NetE (DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
      (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))))

def setupTr5 (a b : DY.Participant) : DY.ExecTrace :=
  ((((setupTr4 a b).append (RndE 32)).append
    (EvE (.OneTimePrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 22 32))))).append
    (StE b { kind := .oneTimePrekey, sk := randTerm 22 32 })).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 22 32)))

private theorem runs_registerIdentity_a (a : DY.Participant) :
    Runs (DY.Libsignal.PQXDH.registerIdentity a) Trace.nil 4 (setupTr1 a) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  have hpred : (!DY.Libsignal.PQXDH.isRegisteredB Trace.nil a) = true := by
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  refine Runs.bind (Runs.requireTracePredicate hpred) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  unfold setupTr1
  have hst := Runs.storeLocalState
    ((((Trace.nil.append (RndE 32)).append
      (EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
        (DY.Signature.vk (randTerm 0 32)) true))).append
      (NetE (DY.DiffieHellman.dhPk (randTerm 0 32)))).append
      (NetE (DY.Signature.vk (randTerm 0 32))))
    a { kind := .identity, sk := randTerm 0 32 }
  simpa only [Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2] using hst

private theorem not_isRegisteredB_setupTr1_self (a : DY.Participant) :
    (!DY.Libsignal.PQXDH.isRegisteredB (setupTr1 a) a) = false := by
  unfold DY.Libsignal.PQXDH.isRegisteredB setupTr1; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  simp [List.range_succ, Trace.at?,
    Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2,
    Symbolic.DYBridge.DY.Trace.at_eq_2]
  intro _ h _ _
  exfalso
  revert h
  change (a == a) = false → False
  simp

private theorem fails_registerIdentity_self (a : DY.Participant) :
    Fails (DY.Libsignal.PQXDH.registerIdentity a) (setupTr1 a) (setupTr1 a) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact Fails.bind_left _ (Fails.requireTracePredicate (not_isRegisteredB_setupTr1_self a))

theorem setupTrace_eq_self (r : Composed.Refinement.ProtocolSetup)
    (hEq : r.alice = r.bob) :
    Composed.Refinement.setupTrace r = setupTr1 r.alice := by
  unfold Composed.Refinement.setupTrace
  have h : Fails (Composed.Refinement.setupAct r.alice r.bob r.withOpk) Trace.nil
      (setupTr1 r.alice) := by
    unfold Composed.Refinement.setupAct
    rw [← hEq]
    refine Fails.bind_right (runs_registerIdentity_a r.alice) ?_
    exact Fails.bind_left _ (fails_registerIdentity_self r.alice)
  exact h.2

end SetupStepping

end Symbolic.Swarm.CREF.CliPure
