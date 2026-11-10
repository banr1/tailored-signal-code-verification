/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.VCGen
public import ProofLib.SepLogic.WP
import Arm64.Trusted.Spec.SepLogic

/-!
# `BV.Linear` Integration Tests

Tests linear address normalization inside `DisjointRegions` read-over-write simplification,
chained literal-offset folding under `wp_norm`, and `evalPCBaseOff?` PC base/offset extraction.
-/

@[expose] public section

namespace ProofLib.BV.IntegrationTests

open Arm64

-- Syntactic fast path
example (m : Memory) (b1 b2 v : BitVec 64) (h : DisjointRegions b1 32 b2 32) :
    (m.write64 (b1 + 8#64) v).read64 (b2 + 16#64) = m.read64 (b2 + 16#64) := by
  simp only [arm64_norm]

-- Region base `b + i`, read at `b + (i + 16)` via linear normal form
example (m : Memory) (b i j v : BitVec 64) (h : DisjointRegions (b + i) 32 j 32) :
    (m.write64 j v).read64 (b + (i + 16#64)) = m.read64 (b + (i + 16#64)) := by
  simp only [arm64_norm]

-- `sp - 32 + 8 + x * 0` address in downward frame `[sp - 32, sp)`
example (m : Memory) (sp g x v : BitVec 64) (h : DisjointRegions (sp - 32#64) 32 g 64) :
    (m.write64 (sp - 32#64 + 8#64 + x * 0#64) v).read64 (g + 8#64) = m.read64 (g + 8#64) := by
  simp only [arm64_norm]

-- Reordered atoms: `8 + (x + b)` against base `b + x`
example (m : Memory) (b x g : BitVec 64) (v : BitVec 32) (h : DisjointRegions g 16 (b + x) 16) :
    (m.write32 (8#64 + (x + b)) v).read64 g = m.read64 g := by
  simp only [arm64_norm]

set_option linter.unusedVariables false in
-- Out-of-region offset 32 outside `[b, b + 32)` must not fire
example (m : Memory) (b g v : BitVec 64) (h : DisjointRegions b 32 g 32) : True := by
  fail_if_success
    have : (m.write64 (b + 32#64) v).read64 g = m.read64 g := by simp only [arm64_norm]
  trivial

/-! ## `wp_norm` Literal-Offset Folds -/

example (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by simp only [wp_norm]
example (sp : BitVec 64) : (sp - 8#64) + 8#64 = sp := by simp only [wp_norm]
example (sp : BitVec 64) : sp - 16#64 - 16#64 = sp - 32#64 := by simp only [wp_norm]
example (sp : BitVec 64) (P : BitVec 64 → Prop) (h : P (sp - 592#64)) :
    P (sp - 80#64 - 512#64) := by
  simp only [wp_norm]
  exact h

/-! ## PC Base/Offset Recognition -/

open Lean Meta Elab Term in
/-- info: [some 12, some 12, some 8, some 8] -/
#guard_msgs in
#eval show TermElabM _ from do
  let ty ← elabType (← `(BitVec 64))
  withLocalDeclD `base ty fun base => withLocalDeclD `x ty fun x => do
  let lit (n : Nat) := toExpr (BitVec.ofNat 64 n)
  let e1 ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[base, lit 4], lit 8]
  let e2 ← mkAppM ``HAdd.hAdd #[lit 12, base]
  let e3 ← mkAppM ``HAdd.hAdd #[← mkAppM ``HSub.hSub #[← mkAppM ``HAdd.hAdd #[base, x], x], lit 8]
  -- `(base + x) + 8`: the syntactic path takes `base + x` as the base (offset 8)
  let e4 ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[base, x], lit 8]
  let rs ← [e1, e2, e3, e4].mapM fun e => do
    return (← ProofLib.evalPCBaseOff? e).map (·.2)
  return rs

end ProofLib.BV.IntegrationTests
