/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib

/-!
# Local Fetch Hypothesis Regression Tests

Positive and negative regression tests for the local-hypothesis scan in
`ProofLib.tryCloseFetchFromHasCode` (`proofLib.fetchLocalHypIndex`).
-/

@[expose] public section

namespace ProofLib.Testing.FetchLocalHyp

open Arm64 _root_.ProofLib

/-- Runs `tryCloseFetchFromHasCode` and fails unless it closes the goal. -/
macro "close_fetch" : tactic =>
  `(tactic| run_tac do
    unless ← _root_.ProofLib.tryCloseFetchFromHasCode do throwError "not closed")

example (P : Program) (b : BitVec 64) (h : P.fetch (b + 0x8#64) = some .nop) :
    P.fetch (b + 0x8#64) = some .nop := by
  close_fetch

/-- A fact introduced by `have` from a lemma (its type is instantiated before matching). The
    fetch goal is a fresh `by` goal: the main goal after tactic `have` carries `mdata`. -/
example (P : Program) (b : BitVec 64)
    (hP : ∀ b : BitVec 64, P.fetch (b + 0x4#64) = some (.ret (.gpr 30#5))) :
    P.fetch (b + 0x4#64) = some (.ret (.gpr 30#5)) := by
  have := hP b
  exact (by close_fetch : P.fetch (b + 0x4#64) = some (.ret (.gpr 30#5)))

/-- The PC literal is matched by value, not by syntax. -/
example (P : Program) (b : BitVec 64) (h : P.fetch (b + BitVec.ofNat 64 8) = some .nop) :
    P.fetch (b + 0x8#64) = some .nop := by
  close_fetch

example (P : Program) (b : BitVec 64) (_h : P.fetch (b + 0x4#64) = some .nop) :
    P.fetch (b + 0x8#64) = some .nop ∨ True := by
  refine Or.inr trivial
  fail_if_success
    have : P.fetch (b + 0x8#64) = some .nop := by close_fetch

example (P Q : Program) (b : BitVec 64) (_h : Q.fetch (b + 0x8#64) = some .nop) :
    P.fetch (b + 0x8#64) = some .nop ∨ True := by
  refine Or.inr trivial
  fail_if_success
    have : P.fetch (b + 0x8#64) = some .nop := by close_fetch

example (P : Program) (b : BitVec 64) (_h : P.fetch (b + 0x8#64) = some (.ret (.gpr 30#5))) :
    P.fetch (b + 0x8#64) = some .nop ∨ True := by
  refine Or.inr trivial
  fail_if_success
    have : P.fetch (b + 0x8#64) = some .nop := by close_fetch

-- With `proofLib.fetchLocalHypIndex` disabled, the local hypothesis is ignored.
set_option proofLib.fetchLocalHypIndex false in
example (P : Program) (b : BitVec 64) (h : P.fetch (b + 0x8#64) = some .nop) :
    P.fetch (b + 0x8#64) = some .nop := by
  fail_if_success close_fetch
  exact h

end ProofLib.Testing.FetchLocalHyp
