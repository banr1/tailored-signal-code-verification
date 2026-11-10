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
# Synthetic Benchmarks for `reg_chain` and `reg_rw`

Defines `#regchain_bench K L`, generating paired manual and automated theorems for size-`K`
callee-saved register preservation chains (`cs_hand_K` vs `cs_auto_K`, each leaf of length `2K + 1`
through `CalleeSavedPreserved` and straight-line segment tuples) and size-`L` stack-pointer
equality chains (`sp_hand_L` vs `sp_auto_L` via `reg_rw`, and `spc_hand_L` vs `spc_auto_L` via
`reg_chain` with congruence).
-/

@[expose] public section

set_option linter.unusedVariables false

namespace Testing.RegChainBench

open Arm64

/-- Callee-saved registers `.x19` through `.x29`. -/
meta def csRegs : List Nat := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

/-- Binders and hypotheses of the callee-saved benchmark of size `K` (states `s0 ... s(2K)`, `sf`). -/
meta def csBinders (K : Nat) : String := Id.run do
  let n := 2 * K
  let states := String.intercalate " " ((List.range (n + 1)).map (s!"s{·}") ++ ["sf"])
  let mut out := s!"({states} : State)"
  for i in [1:K+1] do
    let a := 2 * i - 2
    let b := 2 * i - 1
    let c := 2 * i
    out := out ++ s!"\n    (hcs{i} : CalleeSavedPreserved s{a} s{b}) (hsp{i} : s{b}.sp = s{a}.sp)" ++
      s!" (htr{i} : s{b}.trace = s{a}.trace)"
    let regs := String.intercalate " ∧ " (csRegs.map fun r => s!"s{c}.readReg64 .x{r} = s{b}.readReg64 .x{r}")
    out := out ++ s!"\n    (hseg{i} : s{c}.sp = s{b}.sp ∧ s{c}.trace = s{b}.trace ∧ {regs})"
  let regs := String.intercalate " ∧ " (csRegs.map fun r => s!"sf.readReg64 .x{r} = s{n}.readReg64 .x{r}")
  out := out ++ s!"\n    (hf : sf.sp = s{n}.sp ∧ sf.trace = s{n}.trace ∧ {regs})"
  return out

/-- Goal of the callee-saved benchmark. -/
meta def csGoal : String :=
  "sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ " ++
    String.intercalate " ∧ " (csRegs.map fun r => s!"sf.readReg64 .x{r} = s0.readReg64 .x{r}")

/-- Manual proof baseline: destructure hypotheses and build one `.trans` chain per leaf. -/
meta def csHand (K : Nat) : String := Id.run do
  let names (p : String) (i : Nat) := csRegs.map fun r => s!"{p}{r}_{i}"
  let mut out := ""
  for i in [1:K+1] do
    out := out ++ s!"\n  rcases hcs{i} with ⟨{String.intercalate ", " (names "c" i)}, _⟩"
    out := out ++ s!"\n  rcases hseg{i} with ⟨gsp_{i}, gtr_{i}, {String.intercalate ", " (names "g" i)}⟩"
  out := out ++ s!"\n  rcases hf with ⟨fsp, ftr, {String.intercalate ", " (names "f" 0)}⟩"
  -- chain sf -> s(2K) -> s(2K-1) -> ... -> s0
  let chain (f : String) (seg call : Nat → String) : String := Id.run do
    let mut t := call 1
    for i in [2:K+1] do
      t := s!"{call i}.trans ({seg (i - 1)}.trans ({t}))"
    return s!"{f}.trans ({seg K}.trans ({t}))"
  let leaves := [chain "fsp" (s!"gsp_{·}") (s!"hsp{·}"), chain "ftr" (s!"gtr_{·}") (s!"htr{·}")] ++
    csRegs.map fun r => chain s!"f{r}_0" (s!"g{r}_{·}") (s!"c{r}_{·}")
  out := out ++ s!"\n  exact ⟨{String.intercalate ",\n    " leaves}⟩"
  return out

/-- Binders of the SP benchmark of size `L`: `sf0 ... sfL`, `h0 : sf0.sp = s0.sp - 176#64`,
    `hi : sfi.sp = sf(i-1).sp`. -/
meta def spBinders (L : Nat) : String := Id.run do
  let states := String.intercalate " " ("s0" :: (List.range (L + 1)).map (s!"sf{·}"))
  let mut out := s!"({states} : State) (h0 : sf0.sp = s0.sp - 176#64)"
  for i in [1:L+1] do
    out := out ++ s!" (h{i} : sf{i}.sp = sf{i-1}.sp)"
  return out

/-- Manual rewrite list `h_L, ..., h_1, h_0`. -/
meta def spRws (L : Nat) : String :=
  String.intercalate ", " ((List.range (L + 1)).reverse.map (s!"h{·}"))

open Lean Elab Command in
meta def elabSrc (src : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => elabCommand stx
  | .error e => throwError "bench generator: parse error {e}\n{src}"

open Lean Elab Command in
/-- `#regchain_bench K L`: generates the callee-saved benchmark of size `K` and SP benchmarks of size `L`. -/
elab "#regchain_bench " k:num l:num : command => do
  let K := k.getNat
  let L := l.getNat
  elabSrc s!"theorem cs_hand_{K} {csBinders K} :\n    {csGoal} := by{csHand K}"
  elabSrc s!"theorem cs_auto_{K} {csBinders K} :\n    {csGoal} := by\n  reg_chain"
  elabSrc s!"theorem sp_hand_{L} {spBinders L} (P : BitVec 64 → Prop)\n    (hp : P (s0.sp - 176#64 + 240#64)) : P (sf{L}.sp + 240#64) := by\n  rw [{spRws L}]\n  exact hp"
  elabSrc s!"theorem sp_auto_{L} {spBinders L} (P : BitVec 64 → Prop)\n    (hp : P (s0.sp - 176#64 + 240#64)) : P (sf{L}.sp + 240#64) := by\n  reg_rw\n  exact hp"
  elabSrc s!"theorem spc_hand_{L} {spBinders L} :\n    sf{L}.sp + 240#64 = s0.sp - 176#64 + 240#64 := by\n  rw [{spRws L}]"
  elabSrc s!"theorem spc_auto_{L} {spBinders L} :\n    sf{L}.sp + 240#64 = s0.sp - 176#64 + 240#64 := by\n  reg_chain"

/-! ## Explicit `K = 2` instances -/

theorem cs_hand_2_literal (s0 s1 s2 s3 s4 sf : State)
    (hcs1 : CalleeSavedPreserved s0 s1) (hsp1 : s1.sp = s0.sp) (htr1 : s1.trace = s0.trace)
    (hseg1 : s2.sp = s1.sp ∧ s2.trace = s1.trace ∧ s2.readReg64 .x19 = s1.readReg64 .x19 ∧
      s2.readReg64 .x20 = s1.readReg64 .x20 ∧ s2.readReg64 .x29 = s1.readReg64 .x29)
    (hcs2 : CalleeSavedPreserved s2 s3) (hsp2 : s3.sp = s2.sp) (htr2 : s3.trace = s2.trace)
    (hseg2 : s4.sp = s3.sp ∧ s4.trace = s3.trace ∧ s4.readReg64 .x19 = s3.readReg64 .x19 ∧
      s4.readReg64 .x20 = s3.readReg64 .x20 ∧ s4.readReg64 .x29 = s3.readReg64 .x29)
    (hf : sf.sp = s4.sp ∧ sf.trace = s4.trace ∧ sf.readReg64 .x19 = s4.readReg64 .x19 ∧
      sf.readReg64 .x20 = s4.readReg64 .x20 ∧ sf.readReg64 .x29 = s4.readReg64 .x29) :
    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ sf.readReg64 .x19 = s0.readReg64 .x19 ∧
      sf.readReg64 .x20 = s0.readReg64 .x20 ∧ sf.readReg64 .x29 = s0.readReg64 .x29 := by
  rcases hcs1 with ⟨c19_1, c20_1, -, -, -, -, -, -, -, -, c29_1, -⟩
  rcases hcs2 with ⟨c19_2, c20_2, -, -, -, -, -, -, -, -, c29_2, -⟩
  rcases hseg1 with ⟨gsp_1, gtr_1, g19_1, g20_1, g29_1⟩
  rcases hseg2 with ⟨gsp_2, gtr_2, g19_2, g20_2, g29_2⟩
  rcases hf with ⟨fsp, ftr, f19, f20, f29⟩
  exact ⟨fsp.trans (gsp_2.trans (hsp2.trans (gsp_1.trans hsp1))),
    ftr.trans (gtr_2.trans (htr2.trans (gtr_1.trans htr1))),
    f19.trans (g19_2.trans (c19_2.trans (g19_1.trans c19_1))),
    f20.trans (g20_2.trans (c20_2.trans (g20_1.trans c20_1))),
    f29.trans (g29_2.trans (c29_2.trans (g29_1.trans c29_1)))⟩

theorem cs_auto_2_literal (s0 s1 s2 s3 s4 sf : State)
    (hcs1 : CalleeSavedPreserved s0 s1) (hsp1 : s1.sp = s0.sp) (htr1 : s1.trace = s0.trace)
    (hseg1 : s2.sp = s1.sp ∧ s2.trace = s1.trace ∧ s2.readReg64 .x19 = s1.readReg64 .x19 ∧
      s2.readReg64 .x20 = s1.readReg64 .x20 ∧ s2.readReg64 .x29 = s1.readReg64 .x29)
    (hcs2 : CalleeSavedPreserved s2 s3) (hsp2 : s3.sp = s2.sp) (htr2 : s3.trace = s2.trace)
    (hseg2 : s4.sp = s3.sp ∧ s4.trace = s3.trace ∧ s4.readReg64 .x19 = s3.readReg64 .x19 ∧
      s4.readReg64 .x20 = s3.readReg64 .x20 ∧ s4.readReg64 .x29 = s3.readReg64 .x29)
    (hf : sf.sp = s4.sp ∧ sf.trace = s4.trace ∧ sf.readReg64 .x19 = s4.readReg64 .x19 ∧
      sf.readReg64 .x20 = s4.readReg64 .x20 ∧ sf.readReg64 .x29 = s4.readReg64 .x29) :
    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ sf.readReg64 .x19 = s0.readReg64 .x19 ∧
      sf.readReg64 .x20 = s0.readReg64 .x20 ∧ sf.readReg64 .x29 = s0.readReg64 .x29 := by
  reg_chain

#regchain_bench 1 2
#regchain_bench 2 4
#regchain_bench 4 8
#regchain_bench 8 16

/-- info: 'Testing.RegChainBench.cs_auto_8' does not depend on any axioms -/
#guard_msgs in
#print axioms cs_auto_8

/-- info: 'Testing.RegChainBench.cs_hand_8' does not depend on any axioms -/
#guard_msgs in
#print axioms cs_hand_8

/-- info: 'Testing.RegChainBench.sp_auto_16' does not depend on any axioms -/
#guard_msgs in
#print axioms sp_auto_16

/-- info: 'Testing.RegChainBench.sp_hand_16' does not depend on any axioms -/
#guard_msgs in
#print axioms sp_hand_16

/-- info: 'Testing.RegChainBench.spc_auto_16' does not depend on any axioms -/
#guard_msgs in
#print axioms spc_auto_16

/-- info: 'Testing.RegChainBench.spc_hand_16' does not depend on any axioms -/
#guard_msgs in
#print axioms spc_hand_16

end Testing.RegChainBench
