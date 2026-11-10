/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# Tests for `wp_omega_bounded`

Positive and negative tests for `wp_omega_bounded` context-pruning tiers (`goalOnly`, `strict`,
`transitive`, machine-state facts) and `omegaWrapFilter?` modular-arithmetic filtering and budget
cutoffs.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.OmegaBounded

open Arm64 _root_.ProofLib

variable (st : State) (a b c d : BitVec 64) (n m k p q r : Nat)

/-! ## Positive -/

set_option maxHeartbeats 100000 in
/-- Goal-only tier: the goal holds without hypotheses, and the irrelevant ones are dropped. -/
example (_h : st.mem.read64 a = c) (_hq : q - r < k - m) : (a + 8#64) - 8#64 = a := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- Strict tier: every needed hypothesis is over the goal's atoms. -/
example (h : a.toNat + 8 ≤ b.toNat) : a.toNat < b.toNat := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- Transitive tier: `h2` mentions `c`, which is not in the goal, and connects `a` to `b`. -/
example (h1 : a = c + 4#64) (h2 : c = b - 4#64) : a = b := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- A register definition that the goal needs is kept. -/
example (h : st.readReg64 .x0 = a + 1#64) : st.readReg64 .x0 - 1#64 = a := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- Tier keeping machine-state facts: `h` (a memory read, cleared by the lighter tiers) is the only
    link between the goal and `hc`. -/
example (h : st.mem.read64 a = c) (hc : c = 8#64) : st.mem.read64 a + 1#64 = 9#64 := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- Tier keeping machine-state facts with a `BitVec` comparison of a sum but no `Nat` subtraction:
    kept by `omegaWrapFilter?`. -/
example (h : st.mem.read64 a = c) (hc : c = 8#64) (_hw : (c + 1#64).ult 100#64 = true) :
    st.mem.read64 a + 1#64 = 9#64 := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- Relevance pruning looks through projections of constructor applications: `h` is about
    `(st, v).snd`, i.e. the goal's atom `v`, so the strict tier keeps it. -/
example (st : BitVec 64) (v : BitVec 32) (h : (st, v).snd.slt 8#32 = true) :
    ¬ (v != 16#32) = false := by
  run_tac do
    unless ← proveOmegaBounded? (← Lean.Elab.Tactic.getMainGoal) [← `(tactic| (bv_fallback; done))]
        [.strict] do
      throwError "not closed"
    Lean.Elab.Tactic.replaceMainGoal []

set_option maxHeartbeats 100000 in
/-- A goal that needs a `BitVec` comparison of a sum (`hw`: `a + 8#64` does not wrap) closes when
    the problem has no `Nat` subtraction: `omegaWrapFilter?` keeps the comparison. -/
example (hw : a.ule (a + 8#64) = true) (hb : (a + 8#64).toNat ≤ n) : a.toNat + 8 ≤ n := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- Known limitation: with a `Nat` subtraction in the problem, `omegaWrapFilter?` drops the
    comparison of a sum, so a goal that needs both is not closed (and fails fast). -/
example (_hw : a.ule (a + 8#64) = true) (_hb : (a + 8#64).toNat ≤ n) : True := by
  fail_if_success
    have : a.toNat + 8 ≤ n - (k - k) := by wp_omega_bounded
  trivial

set_option maxHeartbeats 100000 in
/-- `Nat` subtraction in the goal, with irrelevant hypotheses in context. -/
example (hp : p + 64 ≤ n) (_hq : q - r < k - m) (_hr : r - q ≤ m - k) : n - (n - p) = p := by
  wp_omega_bounded

/-- Defined `abbrev` predicate in the strict tier: `omegaRelAtoms`
    extracts the argument atom `a` from `SmallBound a.toNat`. -/
abbrev SmallBound (x : Nat) : Prop := x < 2 ^ 62

set_option maxHeartbeats 100000 in
example (h : SmallBound a.toNat) : a.toNat < 2 ^ 63 := by
  run_tac do
    unless ← proveOmegaBounded? (← Lean.Elab.Tactic.getMainGoal)
        [← `(tactic| (omega; done))] [.strict] do
      throwError "not closed in strict tier"
    Lean.Elab.Tactic.replaceMainGoal []

/-! ## Negative -/

/-- error: wp_omega_bounded: bv_omega / omega failed on every pruned context -/
#guard_msgs in
example (h : a.toNat + 8 ≤ b.toNat) : b.toNat < a.toNat + 16 := by
  wp_omega_bounded

/--
error: wp_omega_bounded: bv_omega / omega failed on every pruned context
hint: goal or context has modular BitVec arithmetic (2^64 wraparound); supply an overflow bound (or rewrite with BitVec.toNat_add_of_lt / BitVec.toNat_sub_of_le), or use bv_lin / bv_arith
-/
#guard_msgs in
example : (a + 8#64).toNat = a.toNat + 8 := by
  wp_omega_bounded

set_option maxHeartbeats 200000 in
/-- An unprovable goal whose transitive context has more `Nat` subtractions than
    `omegaMaxNatSubs` fails cheaply (only the goal-only and strict tiers run), and `first | ...`
    recovers from the failure. -/
example (_hp : p + 64 ≤ n) (_hcov : n ≤ p + 128)
    (_h1 : q - r < k - m) (_h2 : r - q ≤ m - k) (_h3 : k - q < r - m) (_h4 : m - r ≤ q - k)
    (_h5 : n - k ≤ p - q) : True := by
  fail_if_success have : n - p = 70 := by wp_omega_bounded
  first | ((have : n - p = 70 := by wp_omega_bounded); trivial) | trivial

set_option maxHeartbeats 100000 in
/-- With a `Nat` subtraction in the problem, `omegaWrapFilter?` drops the `BitVec` wrap-around
    comparison `_hw` (with it, `bv_omega` runs for minutes without checking heartbeats; without
    the filter this example does not terminate), and the remaining problem closes. -/
example (base : BitVec 64) (d a m m' : Nat) (_h1 : m' + 1 ≤ m)
    (_hw : (base + BitVec.ofNat 64 (d + (a + 8 * (m + 1)))).ule (base + BitVec.ofNat 64 (d + a)) =
      false) :
    base + BitVec.ofNat 64 (d + (a + 8 * (m - (m' + 1)))) + 8#64 =
      base + BitVec.ofNat 64 (d + (a + 8 * (m - m'))) := by
  wp_omega_bounded

set_option maxHeartbeats 100000 in
/-- When the goal has `Nat` subtractions, `omegaWrapFilter?` also drops compound `BitVec`
    wrap-around equalities without `Nat` subtractions (`isBvWrapEq`, such as `_heq`, whose atoms
    all occur in the goal so the strict tier keeps it; with `_heq` in context, `bv_omega` does not
    terminate), and the remaining problem closes. -/
example (base : BitVec 64) (o a m m' : Nat) (_h1 : m' + 1 ≤ m) (_ha : a < 8)
    (_heq : base + BitVec.ofNat 64 o + BitVec.ofNat 64 a = base + BitVec.ofNat 64 (o + a)) :
    base + BitVec.ofNat 64 (o + (a + 8 * (m - (m' + 1)))) + 8#64 =
      base + BitVec.ofNat 64 (o + (a + 8 * (m - m'))) := by
  wp_omega_bounded

/-- `omegaWrapFilter?` skips a problem whose size `2^k * t` (`k` `Nat` subtractions, `t`
    wrap-around terms) exceeds `omegaWrapBudget`, keeps one within it, and passes a problem without
    `Nat` subtractions unchanged. -/
example (x y z : BitVec 64) (i j l : Nat)
    (_h1 : x + BitVec.ofNat 64 (i - j) = y + BitVec.ofNat 64 (j - l))
    (_h2 : y + BitVec.ofNat 64 (l - i) = z + BitVec.ofNat 64 (i + j))
    (_h3 : z + x + BitVec.ofNat 64 (i * 2) = y + z + BitVec.ofNat 64 (l * 3))
    (_h4 : x * y + BitVec.ofNat 64 (j + l) = z * x + BitVec.ofNat 64 (l + i)) :
    True := by
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let copy (g : Lean.MVarId) : Lean.MetaM Lean.MVarId := g.withContext do
      return (← Lean.Meta.mkFreshExprMVar (← g.getType)).mvarId!
    if (← omegaWrapFilter? (← copy g)).isSome then throwError "large problem not skipped"
    let lctx ← g.withContext Lean.getLCtx
    let small ← (← copy g).tryClearMany
      (#[`_h2, `_h3, `_h4].filterMap fun n => (lctx.findFromUserName? n).map (·.fvarId))
    if (← omegaWrapFilter? small).isNone then throwError "small problem skipped"
  trivial

set_option maxHeartbeats 100000 in
/-- End to end: an unprovable goal whose connected problem exceeds `omegaWrapBudget` fails fast
    (the large tiers are skipped before `omega` runs), with the `wp_omega_bounded` error alone. -/
example (x y z : BitVec 64) (i j l : Nat)
    (_h1 : x + BitVec.ofNat 64 (i - j) = y + BitVec.ofNat 64 (j - l))
    (_h2 : y + BitVec.ofNat 64 (l - i) = z + BitVec.ofNat 64 (i + j))
    (_h3 : z + x + BitVec.ofNat 64 (i * 2) = y + z + BitVec.ofNat 64 (l * 3))
    (_h4 : x * y + BitVec.ofNat 64 (j + l) = z * x + BitVec.ofNat 64 (l + i)) : True := by
  fail_if_success have : x + BitVec.ofNat 64 (i - l) = z := by wp_omega_bounded
  trivial

end Examples.Testing.ProofLib.OmegaBounded
