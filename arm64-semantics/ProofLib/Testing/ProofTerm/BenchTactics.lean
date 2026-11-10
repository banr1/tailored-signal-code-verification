/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProofTerm

/-!
# Synthetic Benchmarks for `clear_dead` and `kfold`

Size-parameterized benchmarks comparing plain proofs against proofs preceded by `clear_dead`
(pruning irrelevant arithmetic hypotheses before `omega`) or `kfold` (abstracting repeated large
list literals before `simp only`).
-/

@[expose] public section

namespace Testing.ProofTerm.BenchTactics

set_option linter.unusedVariables false

open Lean Elab Term Meta

/-! ## `clear_dead` -/

theorem cd_omega_20 (a b y x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
    (h0 : x0 + 0 = x1 * 2 + y)
    (h1 : x1 + 1 = x2 * 2 + y)
    (h2 : x2 + 2 = x3 * 2 + y)
    (h3 : x3 + 3 = x4 * 2 + y)
    (h4 : x4 + 4 = x5 * 2 + y)
    (h5 : x5 + 5 = x6 * 2 + y)
    (h6 : x6 + 6 = x7 * 2 + y)
    (h7 : x7 + 7 = x8 * 2 + y)
    (h8 : x8 + 8 = x9 * 2 + y)
    (h9 : x9 + 9 = x10 * 2 + y)
    (h10 : x10 + 10 = x11 * 2 + y)
    (h11 : x11 + 11 = x12 * 2 + y)
    (h12 : x12 + 12 = x13 * 2 + y)
    (h13 : x13 + 13 = x14 * 2 + y)
    (h14 : x14 + 14 = x15 * 2 + y)
    (h15 : x15 + 15 = x16 * 2 + y)
    (h16 : x16 + 16 = x17 * 2 + y)
    (h17 : x17 + 17 = x18 * 2 + y)
    (h18 : x18 + 18 = x19 * 2 + y)
    (hab : a + 1 = b) (hb : b ≤ 3) : a ≤ 2 := by
  omega

theorem cd_clear_dead_20 (a b y x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Nat)
    (h0 : x0 + 0 = x1 * 2 + y)
    (h1 : x1 + 1 = x2 * 2 + y)
    (h2 : x2 + 2 = x3 * 2 + y)
    (h3 : x3 + 3 = x4 * 2 + y)
    (h4 : x4 + 4 = x5 * 2 + y)
    (h5 : x5 + 5 = x6 * 2 + y)
    (h6 : x6 + 6 = x7 * 2 + y)
    (h7 : x7 + 7 = x8 * 2 + y)
    (h8 : x8 + 8 = x9 * 2 + y)
    (h9 : x9 + 9 = x10 * 2 + y)
    (h10 : x10 + 10 = x11 * 2 + y)
    (h11 : x11 + 11 = x12 * 2 + y)
    (h12 : x12 + 12 = x13 * 2 + y)
    (h13 : x13 + 13 = x14 * 2 + y)
    (h14 : x14 + 14 = x15 * 2 + y)
    (h15 : x15 + 15 = x16 * 2 + y)
    (h16 : x16 + 16 = x17 * 2 + y)
    (h17 : x17 + 17 = x18 * 2 + y)
    (h18 : x18 + 18 = x19 * 2 + y)
    (hab : a + 1 = b) (hb : b ≤ 3) : a ≤ 2 := by
  clear_dead
  omega

theorem cd_omega_40 (a b y x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Nat)
    (h0 : x0 + 0 = x1 * 2 + y)
    (h1 : x1 + 1 = x2 * 2 + y)
    (h2 : x2 + 2 = x3 * 2 + y)
    (h3 : x3 + 3 = x4 * 2 + y)
    (h4 : x4 + 4 = x5 * 2 + y)
    (h5 : x5 + 5 = x6 * 2 + y)
    (h6 : x6 + 6 = x7 * 2 + y)
    (h7 : x7 + 7 = x8 * 2 + y)
    (h8 : x8 + 8 = x9 * 2 + y)
    (h9 : x9 + 9 = x10 * 2 + y)
    (h10 : x10 + 10 = x11 * 2 + y)
    (h11 : x11 + 11 = x12 * 2 + y)
    (h12 : x12 + 12 = x13 * 2 + y)
    (h13 : x13 + 13 = x14 * 2 + y)
    (h14 : x14 + 14 = x15 * 2 + y)
    (h15 : x15 + 15 = x16 * 2 + y)
    (h16 : x16 + 16 = x17 * 2 + y)
    (h17 : x17 + 17 = x18 * 2 + y)
    (h18 : x18 + 18 = x19 * 2 + y)
    (h19 : x19 + 19 = x20 * 2 + y)
    (h20 : x20 + 20 = x21 * 2 + y)
    (h21 : x21 + 21 = x22 * 2 + y)
    (h22 : x22 + 22 = x23 * 2 + y)
    (h23 : x23 + 23 = x24 * 2 + y)
    (h24 : x24 + 24 = x25 * 2 + y)
    (h25 : x25 + 25 = x26 * 2 + y)
    (h26 : x26 + 26 = x27 * 2 + y)
    (h27 : x27 + 27 = x28 * 2 + y)
    (h28 : x28 + 28 = x29 * 2 + y)
    (h29 : x29 + 29 = x30 * 2 + y)
    (h30 : x30 + 30 = x31 * 2 + y)
    (h31 : x31 + 31 = x32 * 2 + y)
    (h32 : x32 + 32 = x33 * 2 + y)
    (h33 : x33 + 33 = x34 * 2 + y)
    (h34 : x34 + 34 = x35 * 2 + y)
    (h35 : x35 + 35 = x36 * 2 + y)
    (h36 : x36 + 36 = x37 * 2 + y)
    (h37 : x37 + 37 = x38 * 2 + y)
    (h38 : x38 + 38 = x39 * 2 + y)
    (hab : a + 1 = b) (hb : b ≤ 3) : a ≤ 2 := by
  omega

theorem cd_clear_dead_40 (a b y x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Nat)
    (h0 : x0 + 0 = x1 * 2 + y)
    (h1 : x1 + 1 = x2 * 2 + y)
    (h2 : x2 + 2 = x3 * 2 + y)
    (h3 : x3 + 3 = x4 * 2 + y)
    (h4 : x4 + 4 = x5 * 2 + y)
    (h5 : x5 + 5 = x6 * 2 + y)
    (h6 : x6 + 6 = x7 * 2 + y)
    (h7 : x7 + 7 = x8 * 2 + y)
    (h8 : x8 + 8 = x9 * 2 + y)
    (h9 : x9 + 9 = x10 * 2 + y)
    (h10 : x10 + 10 = x11 * 2 + y)
    (h11 : x11 + 11 = x12 * 2 + y)
    (h12 : x12 + 12 = x13 * 2 + y)
    (h13 : x13 + 13 = x14 * 2 + y)
    (h14 : x14 + 14 = x15 * 2 + y)
    (h15 : x15 + 15 = x16 * 2 + y)
    (h16 : x16 + 16 = x17 * 2 + y)
    (h17 : x17 + 17 = x18 * 2 + y)
    (h18 : x18 + 18 = x19 * 2 + y)
    (h19 : x19 + 19 = x20 * 2 + y)
    (h20 : x20 + 20 = x21 * 2 + y)
    (h21 : x21 + 21 = x22 * 2 + y)
    (h22 : x22 + 22 = x23 * 2 + y)
    (h23 : x23 + 23 = x24 * 2 + y)
    (h24 : x24 + 24 = x25 * 2 + y)
    (h25 : x25 + 25 = x26 * 2 + y)
    (h26 : x26 + 26 = x27 * 2 + y)
    (h27 : x27 + 27 = x28 * 2 + y)
    (h28 : x28 + 28 = x29 * 2 + y)
    (h29 : x29 + 29 = x30 * 2 + y)
    (h30 : x30 + 30 = x31 * 2 + y)
    (h31 : x31 + 31 = x32 * 2 + y)
    (h32 : x32 + 32 = x33 * 2 + y)
    (h33 : x33 + 33 = x34 * 2 + y)
    (h34 : x34 + 34 = x35 * 2 + y)
    (h35 : x35 + 35 = x36 * 2 + y)
    (h36 : x36 + 36 = x37 * 2 + y)
    (h37 : x37 + 37 = x38 * 2 + y)
    (h38 : x38 + 38 = x39 * 2 + y)
    (hab : a + 1 = b) (hb : b ≤ 3) : a ≤ 2 := by
  clear_dead
  omega

/-! ## `kfold` -/

/-- Elaborate the literal list `[0, 3, 6, ...]` with `m` elements. -/
elab "bench_list% " m:num : term => do
  let xs := (List.range m.getNat).map fun i => mkNatLit (3 * i)
  mkListLit (mkConst ``Nat) xs

set_option maxRecDepth 8000

theorem kf_simp_400 (f g : List Nat → Nat) (hf : ∀ l, f l = 0) (hg : ∀ l, g l = 0) :
    f (bench_list% 400) + g (bench_list% 400) + f (bench_list% 400) + g (bench_list% 400) +
      f (bench_list% 400) + g (bench_list% 400) + f (bench_list% 400) + g (bench_list% 400) = 0 := by
  simp only [hf, hg]

theorem kf_kfold_400 (f g : List Nat → Nat) (hf : ∀ l, f l = 0) (hg : ∀ l, g l = 0) :
    f (bench_list% 400) + g (bench_list% 400) + f (bench_list% 400) + g (bench_list% 400) +
      f (bench_list% 400) + g (bench_list% 400) + f (bench_list% 400) + g (bench_list% 400) = 0 := by
  kfold
  simp only [hf, hg]

theorem kf_simp_800 (f g : List Nat → Nat) (hf : ∀ l, f l = 0) (hg : ∀ l, g l = 0) :
    f (bench_list% 800) + g (bench_list% 800) + f (bench_list% 800) + g (bench_list% 800) +
      f (bench_list% 800) + g (bench_list% 800) + f (bench_list% 800) + g (bench_list% 800) = 0 := by
  simp only [hf, hg]

theorem kf_kfold_800 (f g : List Nat → Nat) (hf : ∀ l, f l = 0) (hg : ∀ l, g l = 0) :
    f (bench_list% 800) + g (bench_list% 800) + f (bench_list% 800) + g (bench_list% 800) +
      f (bench_list% 800) + g (bench_list% 800) + f (bench_list% 800) + g (bench_list% 800) = 0 := by
  kfold
  simp only [hf, hg]

/-! ## Axioms -/

/-- info: 'Testing.ProofTerm.BenchTactics.cd_clear_dead_20' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cd_clear_dead_20
/-- info: 'Testing.ProofTerm.BenchTactics.cd_omega_20' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cd_omega_20
/-- info: 'Testing.ProofTerm.BenchTactics.cd_clear_dead_40' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cd_clear_dead_40
/-- info: 'Testing.ProofTerm.BenchTactics.cd_omega_40' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cd_omega_40
/-- info: 'Testing.ProofTerm.BenchTactics.kf_kfold_400' depends on axioms: [propext] -/
#guard_msgs in #print axioms kf_kfold_400
/-- info: 'Testing.ProofTerm.BenchTactics.kf_simp_400' depends on axioms: [propext] -/
#guard_msgs in #print axioms kf_simp_400
/-- info: 'Testing.ProofTerm.BenchTactics.kf_kfold_800' depends on axioms: [propext] -/
#guard_msgs in #print axioms kf_kfold_800
/-- info: 'Testing.ProofTerm.BenchTactics.kf_simp_800' depends on axioms: [propext] -/
#guard_msgs in #print axioms kf_simp_800

end Testing.ProofTerm.BenchTactics
