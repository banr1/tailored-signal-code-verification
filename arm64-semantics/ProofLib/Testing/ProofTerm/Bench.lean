/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProofTerm
public import Arm64

/-!
# Kernel Hot-Spot Benchmarks for `ProofLib.ProofTerm`

Size-parameterized benchmarks over synthetic `Program` symbol tables (`n = 25, 50, 100`) comparing
three proofs of `code.fnOff nameA + k = code.fnOff nameB` where `nameA` and `nameB` are `abbrev`s
for symbol string literals:
- `hk_rw_*`: `rw [code_fnOff_A, code_fnOff_B]`, whose motive cast forces the kernel to reduce
  `Program.fnOff` across the symbol table;
- `hk_decide_*`: `decide +kernel`, which evaluates both `fnOff` calls in the kernel;
- `hk_simp_*`: `simp only [code_fnOff_A, code_fnOff_B]`, which builds a direct chain of lemma
  applications without evaluating `fnOff` in the kernel.
-/

@[expose] public section

namespace Testing.ProofTerm.Bench

open Lean Elab Command Meta Arm64

/-- Symbol name `i` of the synthetic table, sharing a long prefix with other entries. -/
meta def benchSym (i : Nat) : String :=
  s!"<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_{i}"

/-- `#bench_program name n` defines `name : Arm64.Program` with a literal `n`-entry symbol table
    `(benchSym i, 16 * i)`. -/
elab "#bench_program " id:ident n:num : command => do
  let n := n.getNat
  let base ← liftTermElabM do
    let e ← Term.elabTerm (← `(({ svc := Arm64.noSyscalls } : Arm64.Program))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Nat)
  let pairs := (List.range n).map fun i =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``Nat)
      (mkStrLit (benchSym i)) (mkRawNatLit (16 * i))
  let syms ← liftTermElabM <| mkListLit pairTy pairs
  let args := base.getAppArgs.set! 2 syms
  let val := mkAppN base.getAppFn args
  liftCoreM <| addDecl <| .defnDecl
    { name := (← getCurrNamespace) ++ id.getId, levelParams := [], type := mkConst ``Arm64.Program,
      value := val, hints := .regular 0, safety := .safe }

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ## n = 25 -/

#bench_program prog25 25

abbrev nameA25 : String :=
  "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_15"
abbrev nameB25 : String :=
  "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_20"

theorem prog25_fnOff_A :
    prog25.fnOff
      "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_15"
      = 240 := by decide +kernel
theorem prog25_fnOff_B :
    prog25.fnOff
      "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_20"
      = 320 := by decide +kernel

/-- Baseline: hand-written `rw` chain (the kernel evaluates `fnOff` on the table). -/
theorem hk_rw_25 : prog25.fnOff nameA25 + 80 = prog25.fnOff nameB25 := by
  rw [prog25_fnOff_A, prog25_fnOff_B]
/-- Baseline: `decide` (the kernel evaluates both `fnOff` calls). -/
theorem hk_decide_25 : prog25.fnOff nameA25 + 80 = prog25.fnOff nameB25 := by
  decide +kernel
/-- Fixed: `simp` with the offset lemmas (a chain of lemma applications). -/
theorem hk_simp_25 : prog25.fnOff nameA25 + 80 = prog25.fnOff nameB25 := by
  simp only [prog25_fnOff_A, prog25_fnOff_B]

/-! ## n = 50 -/

#bench_program prog50 50

abbrev nameA50 : String :=
  "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_30"
abbrev nameB50 : String :=
  "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_40"

theorem prog50_fnOff_A :
    prog50.fnOff
      "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_30"
      = 480 := by decide +kernel
theorem prog50_fnOff_B :
    prog50.fnOff
      "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_40"
      = 640 := by decide +kernel

/-- Baseline: hand-written `rw` chain (the kernel evaluates `fnOff` on the table). -/
theorem hk_rw_50 : prog50.fnOff nameA50 + 160 = prog50.fnOff nameB50 := by
  rw [prog50_fnOff_A, prog50_fnOff_B]
/-- Baseline: `decide` (the kernel evaluates both `fnOff` calls). -/
theorem hk_decide_50 : prog50.fnOff nameA50 + 160 = prog50.fnOff nameB50 := by
  decide +kernel
/-- Fixed: `simp` with the offset lemmas (a chain of lemma applications). -/
theorem hk_simp_50 : prog50.fnOff nameA50 + 160 = prog50.fnOff nameB50 := by
  simp only [prog50_fnOff_A, prog50_fnOff_B]

/-! ## n = 100 -/

#bench_program prog100 100

abbrev nameA100 : String :=
  "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_60"
abbrev nameB100 : String :=
  "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_80"

theorem prog100_fnOff_A :
    prog100.fnOff
      "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_60"
      = 960 := by decide +kernel
theorem prog100_fnOff_B :
    prog100.fnOff
      "<widget_core::codec::Engine<alloc::vec::Vec<u8>> as widget_core::traits::Codec>::method_80"
      = 1280 := by decide +kernel

/-- Baseline: hand-written `rw` chain (the kernel evaluates `fnOff` on the table). -/
theorem hk_rw_100 : prog100.fnOff nameA100 + 320 = prog100.fnOff nameB100 := by
  rw [prog100_fnOff_A, prog100_fnOff_B]
/-- Baseline: `decide` (the kernel evaluates both `fnOff` calls). -/
theorem hk_decide_100 : prog100.fnOff nameA100 + 320 = prog100.fnOff nameB100 := by
  decide +kernel
/-- Fixed: `simp` with the offset lemmas (a chain of lemma applications). -/
theorem hk_simp_100 : prog100.fnOff nameA100 + 320 = prog100.fnOff nameB100 := by
  simp only [prog100_fnOff_A, prog100_fnOff_B]

/-! ## Axioms (kernel-checked proofs only) -/

/-- info: 'Testing.ProofTerm.Bench.hk_rw_25' does not depend on any axioms -/
#guard_msgs in #print axioms hk_rw_25
/-- info: 'Testing.ProofTerm.Bench.hk_decide_25' does not depend on any axioms -/
#guard_msgs in #print axioms hk_decide_25
/-- info: 'Testing.ProofTerm.Bench.hk_simp_25' depends on axioms: [propext] -/
#guard_msgs in #print axioms hk_simp_25
/-- info: 'Testing.ProofTerm.Bench.hk_rw_50' does not depend on any axioms -/
#guard_msgs in #print axioms hk_rw_50
/-- info: 'Testing.ProofTerm.Bench.hk_decide_50' does not depend on any axioms -/
#guard_msgs in #print axioms hk_decide_50
/-- info: 'Testing.ProofTerm.Bench.hk_simp_50' depends on axioms: [propext] -/
#guard_msgs in #print axioms hk_simp_50
/-- info: 'Testing.ProofTerm.Bench.hk_rw_100' does not depend on any axioms -/
#guard_msgs in #print axioms hk_rw_100
/-- info: 'Testing.ProofTerm.Bench.hk_decide_100' does not depend on any axioms -/
#guard_msgs in #print axioms hk_decide_100
/-- info: 'Testing.ProofTerm.Bench.hk_simp_100' depends on axioms: [propext] -/
#guard_msgs in #print axioms hk_simp_100

/-! ## Static `#kernel_lint` check

The 25-entry table has about 150 distinct nodes, below the default `heavyNodes` threshold (2000),
so the threshold is lowered to `100` for this check. -/

/--
info: [kernel_lint] scope=explicit decls=3 findings=1 in_decls=1
[kernel_lint] Testing.ProofTerm.Bench.hk_decide_25 decide-on-heavy: `decide` makes the kernel evaluate `prog25.fnOff nameA25 + 80 = prog25.fnOff nameB25` (heavy: [Testing.ProofTerm.Bench.prog25]); prove it with rewriting lemmas (e.g. `simp only [arm64_norm]`) instead
-/
#guard_msgs in
set_option proofLib.kernelLint.heavyNodes 100 in
#kernel_lint hk_decide_25 hk_simp_25

end Testing.ProofTerm.Bench
