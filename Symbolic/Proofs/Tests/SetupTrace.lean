/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ModelTraces
import all DY.Trace.Monad

/-!
# Reachability Proof for `Refinement.setupTrace`

Proves that `Refinement.setupTrace r` (both with and without a one-time prekey) is reachable in
`DY.Libsignal.Composed.reachability` for every protocol setup `r : Refinement.ProtocolSetup`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.SetupTrace

open DY
open DY.Libsignal.PQXDH (registerIdentity genSignedPrekey genPQPrekey genOneTimePrekey)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement (ProtocolSetup setupAct setupTrace)

private def ReachStep {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → ((x.run tr).2.val).Reachable reachability

private theorem ReachStep.pure {α : Type} (a : α) : ReachStep (Pure.pure a : Traceful α) :=
  fun _ h => h

private theorem ReachStep.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : ReachStep x) (hf : ∀ a, ReachStep (f a)) : ReachStep (x >>= f) := by
  intro tr htr
  rw [Traceful.run_bind]
  rcases h : x.run tr with ⟨_ | a, trMid, _⟩
  · have := hx tr htr; rwa [h] at this
  · have := hx tr htr; rw [h] at this; exact hf a trMid this

private theorem ReachStep.registerIdentity (p : Participant) :
    ReachStep (registerIdentity p) :=
  fun tr h =>
    (Traceful.PreservesReachability_base registerIdentity.reachability
      reachability p tr h trivial).1

private theorem ReachStep.genSignedPrekey (b : Participant) (i : Nat) :
    ReachStep (genSignedPrekey b i) :=
  fun tr h =>
    (Traceful.PreservesReachability_base genSignedPrekey.reachability
      reachability (b, i) tr h trivial).1

private theorem ReachStep.genPQPrekey (b : Participant) (i : Nat) :
    ReachStep (genPQPrekey b i) :=
  fun tr h =>
    (Traceful.PreservesReachability_base genPQPrekey.reachability
      reachability (b, i) tr h trivial).1

private theorem ReachStep.genOneTimePrekey (b : Participant) :
    ReachStep (genOneTimePrekey b) :=
  fun tr h =>
    (Traceful.PreservesReachability_base genOneTimePrekey.reachability
      reachability b tr h trivial).1

private theorem ReachStep.setupAct (a b : Participant) (withOpk : Bool) :
    ReachStep (setupAct a b withOpk) := by
  unfold DY.Libsignal.Composed.Refinement.setupAct
  refine ReachStep.bind (ReachStep.registerIdentity a) fun _ =>
    ReachStep.bind (ReachStep.registerIdentity b) fun hB =>
    ReachStep.bind (ReachStep.genSignedPrekey b hB) fun _ =>
    ReachStep.bind (ReachStep.genPQPrekey b hB) fun _ => ?_
  cases withOpk with
  | false => exact ReachStep.pure ()
  | true => exact ReachStep.bind (ReachStep.genOneTimePrekey b) fun _ => ReachStep.pure ()

theorem setupTrace_reachable_proof (r : ProtocolSetup) :
    (setupTrace r).Reachable reachability :=
  ReachStep.setupAct r.alice r.bob r.withOpk Trace.nil .Base

end Symbolic.Proofs.Tests.SetupTrace
