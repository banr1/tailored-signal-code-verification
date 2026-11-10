/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProofTerm

/-!
# `ProofTerm` Regression Tests

Regression tests for `#kernel_profile`, `#kernel_profile!`, `#kernel_profile_module`,
`#kernel_hotspots`, `#kernel_lint`, `#kernel_lint!`, `kfold`, `kfold?`, `clear_dead`,
`clear_dead!`, and `clear_dead?` under deterministic timing output
(`proofLib.kernelProfile.deterministic`).
-/

@[expose] public section

set_option linter.unusedVariables false

namespace Testing.ProofTerm

structure Table where
  entries : List (String × Nat)

def Table.off (t : Table) (n : String) : Nat :=
  ((t.entries.find? (·.1 == n)).map (·.2)).getD 0

/-- Table constant of more than 64 nodes used to trigger heavy-constant lint rules. -/
def table : Table := ⟨[("<Widget as Codec>::alpha", 0), ("<Widget as Codec>::beta", 16),
  ("<Widget as Codec>::gamma", 48), ("<Widget as Codec>::delta", 96),
  ("<Widget as Codec>::epsilon", 160), ("<Widget as Codec>::zeta", 240)]⟩

abbrev betaName : String := "<Widget as Codec>::beta"
abbrev deltaName : String := "<Widget as Codec>::delta"

theorem table_off_beta : table.off "<Widget as Codec>::beta" = 16 := by decide +kernel
theorem table_off_delta : table.off "<Widget as Codec>::delta" = 96 := by decide +kernel

theorem side_decide : table.off betaName + 80 = table.off deltaName := by decide +kernel
theorem side_rw : table.off betaName + 80 = table.off deltaName := by
  rw [table_off_beta, table_off_delta]
theorem side_simp : table.off betaName + 80 = table.off deltaName := by
  simp only [betaName, deltaName, table_off_beta, table_off_delta]

set_option proofLib.kernelProfile.deterministic true

/-! ## `#kernel_profile` -/

/--
info: [kernel_profile] scope=explicit decls=3 over_threshold=3 threshold=<t> total=<t>
[kernel_profile] Testing.ProofTerm.side_decide kernel=<t> (value <t> + type <t>) share=<p> aux_decls=1
[kernel_profile] Testing.ProofTerm.side_rw kernel=<t> (value <t> + type <t>) share=<p>
[kernel_profile] Testing.ProofTerm.side_simp kernel=<t> (value <t> + type <t>) share=<p>
-/
#guard_msgs in
set_option proofLib.kernelProfile.thresholdMs 0 in
#kernel_profile side_rw side_decide side_simp

/-- error: 'Nat.zero' has no value to re-check (axiom, constructor, or body not visible from this module; use `import all` for module-system files) -/
#guard_msgs in
#kernel_profile Nat.zero

/--
error: [kernel_profile] scope=explicit decls=1 over_threshold=1 threshold=<t> total=<t>
[kernel_profile] Testing.ProofTerm.side_rw kernel=<t> (value <t> + type <t>) share=<p>
-/
#guard_msgs in
set_option proofLib.kernelProfile.thresholdMs 0 in
#kernel_profile! side_rw

/--
info: [kernel_profile] scope=explicit decls=2 over_threshold=0 threshold=<t> total=<t>
[kernel_profile] Testing.ProofTerm.side_rw kernel=<t> (value <t> + type <t>) share=<p>
[kernel_profile] Testing.ProofTerm.side_simp kernel=<t> (value <t> + type <t>) share=<p>
-/
#guard_msgs in
set_option proofLib.kernelProfile.thresholdMs 100000 in
#kernel_profile! side_rw side_simp

/-! ## `#kernel_hotspots` -/

/--
info: [kernel_hotspots] Testing.ProofTerm.side_rw kernel=<t> sites_timed=<n> over_min=<n> (min 0 ms)
#1 <t>  argument 3 of `Eq.mpr` — rewrite cast (rw / simp / subst)
   expected: 16 + 80 = 96
   actual: 16 + 80 = 16 + 80
   only in expected: []
   only in actual: []
-/
#guard_msgs in
set_option proofLib.kernelHotspots.minMs 0 in
set_option proofLib.kernelHotspots.top 1 in
#kernel_hotspots side_rw

/-! ## `#kernel_lint` -/

set_option proofLib.kernelLint.heavyNodes 64

-- Default rules: `decide` on the heavy table is reported; the cheap `rw` casts of `side_rw` are
-- not (`cast-unfolds-heavy` only reports sites the kernel takes at least `castMs` to re-check).
/--
info: [kernel_lint] scope=explicit decls=4 findings=1 in_decls=1
[kernel_lint] Testing.ProofTerm.side_decide decide-on-heavy: `decide` makes the kernel evaluate `table.off betaName + 80 = table.off deltaName` (heavy: [Testing.ProofTerm.table]); prove it with rewriting lemmas (e.g. `simp only [arm64_norm]`) instead
-/
#guard_msgs in
#kernel_lint side_decide side_rw side_simp

/-- info: [kernel_lint] scope=explicit decls=1 findings=0 in_decls=0 -/
#guard_msgs in
#kernel_lint! side_simp

-- The static `rw` rule (opt-in) reports every rewrite of a heavy term, here both offset lemmas.
/--
error: [kernel_lint] scope=explicit decls=1 findings=2 in_decls=1
[kernel_lint] Testing.ProofTerm.side_rw rw-on-heavy: `rw` rewrites `table.off "<Widget as Codec>::beta"`, a term over heavy constants [Testing.ProofTerm.table]: if the goal's occurrence differs from it (e.g. through an `abbrev`), the kernel compares the two by evaluating them; close the goal with `simp only [...]` / the generated lemmas (or drop the hand-written side-condition proof and use the default autoParam)
[kernel_lint] Testing.ProofTerm.side_rw rw-on-heavy: `rw` rewrites `table.off "<Widget as Codec>::delta"`, a term over heavy constants [Testing.ProofTerm.table]: if the goal's occurrence differs from it (e.g. through an `abbrev`), the kernel compares the two by evaluating them; close the goal with `simp only [...]` / the generated lemmas (or drop the hand-written side-condition proof and use the default autoParam)
-/
#guard_msgs in
set_option proofLib.kernelLint.staticRw true in
#kernel_lint! side_rw

-- With confirmation disabled (`castMs 0`), the `rw` cast that compares `table.off betaName` with
-- `table.off "<literal>"` is reported as `cast-unfolds-heavy`.
/--
info: [kernel_lint] scope=explicit decls=1 findings=2 in_decls=1
[kernel_lint] Testing.ProofTerm.side_rw cast-unfolds-heavy: argument 1 of `id` (rewrite motive cast (rw)): expected and actual types differ around heavy constants [Testing.ProofTerm.table], and the kernel takes over 0 ms to compare them; state the step through a lemma generic in the differing parts (generic transport), or prove it with rewriting lemmas (`simp only [...]`) instead of `rw` / `change` / `dsimp`
    expected: (table.off betaName + 80 = table.off deltaName) = (16 + 80 = table.off deltaName)
    actual:   (table.off "<Widget as Codec>::beta" + 80 = table.off deltaName) = (16 + 80 = table.off deltaName)
[kernel_lint] Testing.ProofTerm.side_rw cast-unfolds-heavy: argument 1 of `id` (rewrite motive cast (rw)): expected and actual types differ around heavy constants [Testing.ProofTerm.table], and the kernel takes over 0 ms to compare them; state the step through a lemma generic in the differing parts (generic transport), or prove it with rewriting lemmas (`simp only [...]`) instead of `rw` / `change` / `dsimp`
    expected: (16 + 80 = table.off deltaName) = (16 + 80 = 96)
    actual:   (16 + 80 = table.off "<Widget as Codec>::delta") = (16 + 80 = 96)
-/
#guard_msgs in
set_option proofLib.kernelLint.castMs 0 in
#kernel_lint side_rw

-- With the default threshold the six-entry table is not heavy: no findings, even when unconfirmed.
/-- info: [kernel_lint] scope=explicit decls=1 findings=0 in_decls=0 -/
#guard_msgs in
set_option proofLib.kernelLint.heavyNodes 2000 in
set_option proofLib.kernelLint.castMs 0 in
set_option proofLib.kernelLint.staticRw true in
#kernel_lint side_rw

/-- A transport through a definitional cast that unfolds the heavy table. -/
theorem cast_unfold (h : table.entries.length = 6) :
    (⟨[("<Widget as Codec>::alpha", 0), ("<Widget as Codec>::beta", 16),
      ("<Widget as Codec>::gamma", 48), ("<Widget as Codec>::delta", 96),
      ("<Widget as Codec>::epsilon", 160), ("<Widget as Codec>::zeta", 240)]⟩ : Table).entries.length
      = 6 := by
  change table.entries.length = 6
  exact h

-- With confirmation disabled (`castMs 0`) the `change` cast that unfolds `table` is reported; with
-- the default confirmation threshold (1000 ms) this cheap cast is not.
/--
info: [kernel_lint] scope=explicit decls=1 findings=1 in_decls=1
[kernel_lint] Testing.ProofTerm.cast_unfold cast-unfolds-heavy: argument 1 of `id` (definitional cast (change / show / dsimp / unfold)): expected and actual types differ around heavy constants [Testing.ProofTerm.table], and the kernel takes over 0 ms to compare them; state the step through a lemma generic in the differing parts (generic transport), or prove it with rewriting lemmas (`simp only [...]`) instead of `rw` / `change` / `dsimp`
    expected: { entries := [("<Widget as Codec>::alpha", 0), ("<Widget as Codec>::beta", ⋯), ⋯, ⋯] }.entries.length = 6
    actual:   table.entries.length = 6
-/
#guard_msgs in
set_option proofLib.kernelLint.castMs 0 in
#kernel_lint cast_unfold

/-- info: [kernel_lint] scope=explicit decls=1 findings=0 in_decls=0 -/
#guard_msgs in
#kernel_lint cast_unfold

/-- `@[kernel_heavy]` marks a constant heavy regardless of its size. -/
def smallTable : Table := ⟨[("a", 0)]⟩
attribute [kernel_heavy] smallTable
theorem small_decide : smallTable.off "a" = 0 := by decide

/--
info: [kernel_lint] scope=explicit decls=1 findings=1 in_decls=1
[kernel_lint] Testing.ProofTerm.small_decide decide-on-heavy: `decide` makes the kernel evaluate `smallTable.off "a" = 0` (heavy: [Testing.ProofTerm.smallTable]); prove it with rewriting lemmas (e.g. `simp only [arm64_norm]`) instead
-/
#guard_msgs in
set_option proofLib.kernelLint.heavyNodes 2000 in
#kernel_lint small_decide

/-! ## `kfold` -/

/--
info: kfold: 1 let-bindings, goal tree size 217 → 5
  kf_1: 2 occurrences × 107 nodes: List.map (fun x => x + 1) [1, 2, 3, 4, 5]
-/
#guard_msgs in
example (f : List Nat → List Nat → Prop) (h : ∀ x, f x x) :
    f ([1, 2, 3, 4, 5].map (· + 1)) ([1, 2, 3, 4, 5].map (· + 1)) := by
  kfold?
  exact h _

/-- info: kfold: no closed sub-term of at least 24 nodes occurs twice -/
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b := by
  kfold?
  exact h

/-- The folded goal is still closed by tactics that see through `let` variables. -/
example (xs : List Nat) (h : xs = [2, 3, 4, 5, 6]) :
    [1, 2, 3, 4, 5].map (· + 1) = xs ∧ xs = [1, 2, 3, 4, 5].map (· + 1) := by
  kfold (minSize := 8)
  subst h
  exact ⟨rfl, rfl⟩

/-! ## `clear_dead` -/

/-- info: Try this: clear c d h2 h3 -/
#guard_msgs in
example (a b c d : Nat) (h1 : a = b) (h2 : c = d) (h3 : d = 5) (h4 : b = 3) : a = 3 := by
  clear_dead?
  omega

/-- info: Try this: clear c d h2 h3 -/
#guard_msgs in
example (a b c d e : Nat) (h1 : a = b) (h2 : c = d) (h3 : d = 5) (h4 : b = 3) (h5 : e = 1) :
    a = 3 := by
  clear_dead? keep h5
  omega

/-- info: clear_dead: nothing to clear -/
#guard_msgs in
example (a b : Nat) (h1 : a = b) (h4 : b = 3) : a = 3 := by
  clear_dead?
  omega

-- `clear_dead!` keeps only equations reachable left-to-right from the goal: `h1 : b = a` is
-- oriented the wrong way, so it is cleared and `omega` fails.
/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  0 ≤ b ≤ 2
where
 b := ↑a
-/
#guard_msgs in
example (a b : Nat) (h1 : b = a) (h4 : b = 3) : a = 3 := by
  clear_dead!
  omega

/-- The conservative variant keeps `h1` (it mentions the goal's free variable `a`). -/
example (a b : Nat) (h1 : b = a) (h4 : b = 3) : a = 3 := by
  clear_dead
  omega

end Testing.ProofTerm
