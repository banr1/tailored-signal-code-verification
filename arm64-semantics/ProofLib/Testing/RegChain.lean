/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.RegChain
public import Arm64

/-!
# Regression Tests for `reg_chain`, `reg_chain?`, and `reg_rw`

Positive and negative (`#guard_msgs`) tests for equational chaining across register and
calling-convention preservation predicates, goal-directed congruence, `closeLeaves`, and `reg_rw`
rewriting.
-/

@[expose] public section

set_option linter.unusedVariables false

namespace Testing.RegChain

open Arm64

/-! ## Generic equations -/

section Generic

variable {σ : Type} (rd : σ → Nat → Nat) (s0 s1 s2 s3 : σ) (box vt : Nat)

/-- A preservation predicate in the shape of `CalleeSavedPreserved`. -/
def Saved (rd : σ → Nat → Nat) (s s' : σ) : Prop :=
  rd s' 19 = rd s 19 ∧ rd s' 20 = rd s 20 ∧ rd s' 22 = rd s 22

example (h1 : rd s1 19 = box) (hcs : Saved rd s1 s2) (hf : rd s3 19 = rd s2 19) :
    rd s3 19 = box := by reg_chain

example (h1 : rd s1 19 = box) (h1' : rd s1 22 = vt) (hcs : Saved rd s1 s2)
    (hf : rd s3 19 = rd s2 19 ∧ rd s3 22 = rd s2 22) (hx : rd s3 7 = 3) :
    rd s3 7 = 3 ∧ box = rd s3 19 ∧ rd s3 22 = vt ∧ rd s0 5 = rd s0 5 := by reg_chain

-- the goal may itself be a preservation predicate (unfolded and split)
example (h01 : Saved rd s0 s1) (h12 : Saved rd s1 s2) (h23 : Saved rd s2 s3) :
    Saved rd s0 s3 := by reg_chain

-- goal-directed congruence: `f a = f b` from `a = b`
example (h : rd s1 0 = rd s0 0 + 16) (h' : rd s2 0 = rd s1 0) :
    rd s2 0 + 8 = (rd s0 0 + 16) + 8 := by reg_chain

-- extra facts and `only`
example (h : rd s1 0 = 5) (h' : rd s2 0 = rd s1 0) : rd s2 0 = 5 := by
  reg_chain only [h, h']

-- non-equational leaves are closed by a hypothesis with the same type
example (h : rd s1 0 = 5) (hlt : rd s0 1 < 7) : rd s1 0 = 5 ∧ rd s0 1 < 7 := by reg_chain

/-- error: reg_chain: could not close 1 leaf goal(s):
  rd s0 1 = 3 -/
#guard_msgs in
example (h : rd s0 1 = 2) : rd s0 1 = 3 := by reg_chain

-- a missing link: `s1` and `s2` are not connected for register 20
/-- error: reg_chain: could not close 1 leaf goal(s):
  rd s2 20 = box -/
#guard_msgs in
example (h1 : rd s1 20 = box) (hf : rd s3 20 = rd s2 20) : rd s3 19 = rd s3 19 ∧ rd s2 20 = box := by
  reg_chain

-- `only` ignores the local context
/-- error: reg_chain: could not close 1 leaf goal(s):
  rd s1 0 = 5 -/
#guard_msgs in
example (h : rd s1 0 = 5) (h' : rd s2 0 = rd s1 0) : rd s1 0 = 5 := by
  reg_chain only [h']

-- non-equational leaf without a hypothesis
/-- error: reg_chain: could not close 1 leaf goal(s):
  rd s0 1 < 7 -/
#guard_msgs in
example (h : rd s0 1 < 8) : rd s0 1 < 7 := by reg_chain

/-- A preservation predicate the user sealed: `reg_chain` does not look inside it. -/
@[irreducible] def SavedSealed (rd : σ → Nat → Nat) (s s' : σ) : Prop := rd s' 19 = rd s 19

/-- error: reg_chain: could not close 1 leaf goal(s):
  rd s1 19 = box -/
#guard_msgs in
example (h0 : rd s0 19 = box) (h : SavedSealed rd s0 s1) : rd s1 19 = box := by reg_chain

/-- Reducible zero-arity head alias with matching arity: `congr?` succeeds across `myAdd` vs `Nat.add`. -/
abbrev myAdd : Nat → Nat → Nat := Nat.add

example (h : rd s1 0 = rd s0 0) : myAdd (rd s1 0) 8 = Nat.add (rd s0 0) 8 := by reg_chain

/-- Reducible partially-applied head alias: `canon` gives both sides head `Nat.add` with 2 args,
    whereas unnormalized `add8 x` has 1 arg and `Nat.add 8 y` has 2 args (`congr?` must guard arity
    instead of panicking on `bs[i]!`). -/
abbrev add8 : Nat → Nat := Nat.add 8

/-- error: reg_chain: could not close 1 leaf goal(s):
  Nat.add 8 (rd s1 0) = add8 (rd s0 0) -/
#guard_msgs in
example (h : rd s1 0 = rd s0 0) : Nat.add 8 (rd s1 0) = add8 (rd s0 0) := by reg_chain

/-- info: Try this: exact Eq.trans (Eq.trans hf hcs.left) h1 -/
#guard_msgs in
example (h1 : rd s1 19 = box) (hcs : Saved rd s1 s2) (hf : rd s3 19 = rd s2 19) :
    rd s3 19 = box := by reg_chain?

end Generic

/-! ## `Arm64.State` registers, SP and callee-saved predicates -/

section State

-- `Reg.x19` in hypotheses vs `.gpr 19#5` inside `CalleeSavedPreserved`
example (s0 s1 s2 : State) (box : BitVec 64) (h0 : s0.readReg64 .x19 = box)
    (hcs1 : CalleeSavedPreserved s0 s1) (hcs2 : CalleeSavedPreserved s1 s2) :
    s2.readReg64 .x19 = box := by reg_chain

-- the full callee-saved conjunction through three calls, and the SP chain
example (s0 s1 s2 s3 : State)
    (hc1 : CallingConventionPreserved s0 s1) (hc2 : CallingConventionPreserved s1 s2)
    (hc3 : CallingConventionPreserved s2 s3) :
    CallingConventionPreserved s0 s3 := by reg_chain

-- SP arithmetic through congruence
example (s sf s1 : State) (sp : BitVec 64) (hsp : s.sp = sp) (h1 : s1.sp = sp - 16#64)
    (hf : sf.sp = s1.sp) : sf.sp + 8#64 = s.sp - 16#64 + 8#64 := by reg_chain

-- a postcondition tuple in the shape of a callee-saved goal after two calls
example (s s1 s2 sf : State) (box vt : BitVec 64)
    (hx19_1 : s1.readReg64 .x19 = box) (hx20_1 : s1.readReg64 .x20 = vt)
    (hx22_1 : s1.readReg64 .x22 = s.readReg64 .x22)
    (hcs2 : CalleeSavedPreserved s1 s2)
    (hf : sf.readReg64 .x19 = s2.readReg64 .x19 ∧ sf.readReg64 .x20 = s2.readReg64 .x20 ∧
      sf.readReg64 .x22 = s2.readReg64 .x22)
    (htr1 : s1.trace = s.trace) (htr2 : s2.trace = s1.trace) (htrf : sf.trace = s2.trace) :
    sf.trace = s.trace ∧ sf.readReg64 .x19 = box ∧ sf.readReg64 .x20 = vt ∧
      sf.readReg64 .x22 = s.readReg64 .x22 := by reg_chain

-- MetaM entry point: close the chain leaves, leave the arithmetic leaf to `omega`
open Lean Elab Tactic in
elab "reg_chain_then_omega" : tactic => do
  let rest ← ProofLib.RegChain.closeLeaves (← getMainGoal)
  replaceMainGoal rest
  for g in rest do
    setGoals [g]
    evalTactic (← `(tactic| omega))
  setGoals []

example (s0 s1 : State) (n : Nat) (h : s1.readReg64 .x19 = s0.readReg64 .x19) (hn : n < 4) :
    s1.readReg64 .x19 = s0.readReg64 .x19 ∧ n < 5 := by reg_chain_then_omega

-- `reg_rw`: express the goal in terms of entry-state values
example (sp : BitVec 64) (s s1 sf : State) (P : BitVec 64 → Prop) (hsp : s.sp = sp - 176#64)
    (h1 : s1.sp = s.sp) (hf : sf.sp = s1.sp) (hp : P (sp - 176#64 + 240#64)) :
    P (sf.sp + 240#64) := by
  reg_rw
  exact hp

-- `reg_rw ←`: express the goal in terms of the newest state
example (sp : BitVec 64) (s s1 sf : State) (P : BitVec 64 → Prop) (hsp : s.sp = sp - 176#64)
    (h1 : s1.sp = s.sp) (hf : sf.sp = s1.sp) (hp : P (sf.sp + 240#64)) :
    P (s.sp + 240#64) := by
  reg_rw ←
  exact hp

/-- error: reg_rw: nothing to rewrite -/
#guard_msgs in
example (s : State) (P : BitVec 64 → Prop) (hp : P s.sp) : P s.sp := by
  reg_rw
  exact hp

-- `reg_rw`: when a candidate occurrence is in a dependent position that `MVarId.rewrite` cannot
-- abstract (motive not type-correct), skip it and still rewrite other occurrences in the goal
example (s0 s1 : State) (Q : ∀ n : Nat, Fin n → Prop) (P : BitVec 64 → Prop)
    (h_dep : s1.sp.toNat = s0.sp.toNat) (ix : Fin s1.sp.toNat)
    (h_reg : s1.readReg64 .x19 = s0.readReg64 .x19)
    (hq : Q s1.sp.toNat ix) (hp : P (s0.readReg64 .x19)) :
    Q s1.sp.toNat ix ∧ P (s1.readReg64 .x19) := by
  reg_rw
  exact ⟨hq, hp⟩

-- `reg_rw`: when the only candidate occurrence in `todo` fails `MVarId.rewrite` (dependent motive),
-- `reg_rw` must fail instead of succeeding as a no-op
/-- error: reg_rw: nothing to rewrite -/
#guard_msgs in
example (s0 s1 : State) (Q : ∀ n : Nat, Fin n → Prop)
    (h_dep : s1.sp.toNat = s0.sp.toNat) (ix : Fin s1.sp.toNat) (hq : Q s1.sp.toNat ix) :
    Q s1.sp.toNat ix := by
  reg_rw
  exact hq

end State

end Testing.RegChain

/-- info: 'Testing.RegChain.Saved' does not depend on any axioms -/
#guard_msgs in
#print axioms Testing.RegChain.Saved
