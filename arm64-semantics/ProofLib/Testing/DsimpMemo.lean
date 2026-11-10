/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public meta import Lean.Elab.Tactic

/-!
# Regression Tests for `dsimpOnlyAtStarMemo`

Tests that `dsimpOnlyAtStarMemo` (backing `wp_unfold_specs`) skips unchanged hypotheses and goals
across repeated passes with the same key, simplifies newly introduced hypotheses, respects
`set_option proofLib.dsimpAtStarMemo false`, and unfolds `Spec` constants added mid-proof.
-/

@[expose] public section

namespace ProofLib.Testing.DsimpMemo

open Arm64 _root_.ProofLib Lean Elab Tactic

def memoP (n : Nat) : Prop := n ≤ n + 1

/-- `memo_dsimp_p`: `dsimp only [memoP] at *` through `dsimpOnlyAtStarMemo` (key `7`); logs
    whether it made progress. -/
elab "memo_dsimp_p" : tactic => do
  let progress ← dsimpOnlyAtStarMemo 7 (← `(tactic| dsimp only [memoP] at *))
  logInfo m!"progress: {progress}"

/-
Pass 1 unfolds `h1` and the goal (`h2` is left unchanged and memoized). Pass 2 rescans only the
types pass 1 produced (`h1`, the goal); they are now unchanged, so it reports no progress. Pass 3
has nothing left to scan. Pass 4 scans `h3`, introduced after the earlier passes, and the goal
that `have` rebuilt; it skips `h1` and `h2`. (Traces are reported after the `info` messages.)
-/
/--
info: progress: true
---
info: progress: false
---
info: progress: false
---
info: progress: true
---
trace: [proofLib.dsimpMemo] pass 7: 2/2 hyps, target true
---
trace: [proofLib.dsimpMemo] pass 7: 1/2 hyps, target true
---
trace: [proofLib.dsimpMemo] pass 7: 0/2 hyps, target false
---
trace: [proofLib.dsimpMemo] pass 7: 1/3 hyps, target true
-/
#guard_msgs in
set_option trace.proofLib.dsimpMemo true in
example (a b : Nat) (_h1 : memoP a) (h2 : a = b) : memoP b ∨ a = b := by
  memo_dsimp_p
  memo_dsimp_p
  memo_dsimp_p
  have h3 : memoP b := by unfold memoP; omega
  memo_dsimp_p
  guard_hyp _h1 : a ≤ a + 1
  guard_hyp h3 : b ≤ b + 1
  guard_target = b ≤ b + 1 ∨ a = b
  exact Or.inr h2

/- With the memo disabled, every pass rescans; a pass with nothing to do reports no progress. -/
/--
info: progress: true
---
info: progress: false
-/
#guard_msgs in
set_option proofLib.dsimpAtStarMemo false in
example (a : Nat) (h1 : memoP a) : memoP a := by
  memo_dsimp_p
  memo_dsimp_p
  exact h1

def memoSpec (P : SepProp) : Spec Unit where
  pre := fun _ _ => P
  post := fun _ _ _ => P

/- `wp_unfold_specs` unfolds a `Spec` in a hypothesis introduced after an earlier call. -/
example (P : SepProp) (Q : Prop) (s : Arm64.State) (_h1 : (memoSpec P).pre () s = P) (hq : Q) : Q := by
  wp_unfold_specs
  have _h2 : (memoSpec P).post () s s = P := rfl
  wp_unfold_specs
  guard_hyp _h1 : P = P
  guard_hyp _h2 : P = P
  exact hq

end ProofLib.Testing.DsimpMemo
