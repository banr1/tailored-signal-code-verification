/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.Arith
public import ProofLib.Testing.AxiomAudit.Core
public meta import Std.Tactic.BVDecide.Reflect

/-!
# Regression Tests for Kernel-Only Bitvector Automation

Tests `bv_kernel`, `bv_fallback`, and `bv_solve`. Verifies that bit-level goals close with
kernel-only proofs audited clean by `#axiom_audit`, goals outside the kernel chain fail without
invoking `bv_decide`, and `set_option proofLib.bvDecideFallback true` enables `bv_decide` (flagged
as `kind=bv_decide` by `#axiom_audit`).
-/

@[expose] public section

namespace Testing.BvKernel

/-! ## Positive: kernel-only chain closes bit-level goals -/

theorem mask_sub (x : BitVec 64) : x &&& (-8#64) = x - (x &&& 7#64) := by bv_kernel

theorem mask_low (b : BitVec 8) : BitVec.zeroExtend 64 b &&& 255#64 = BitVec.zeroExtend 64 b := by
  bv_fallback

theorem mask_ge {x : BitVec 64} (h : ¬(x &&& 7#64).ult 4#64) : x &&& (-5#64) = x - 4#64 := by
  bv_solve

theorem lin_ult (x : BitVec 64) (h : x < 16#64) : x + 1#64 ≤ 16#64 := by bv_fallback

/-- info: [axiom_audit] scope=explicit theorems=4 clean=4 dirty=0 culprits=0 -/
#guard_msgs in
#axiom_audit Testing.BvKernel.mask_sub Testing.BvKernel.mask_low Testing.BvKernel.mask_ge
  Testing.BvKernel.lin_ult

/-! ## Negative: no silent `bv_decide` -/

-- A non-linear bitwise identity that only bit-blasting proves: the kernel chain must fail.
example (x y : BitVec 8) : x ^^^ y = (x ||| y) - (x &&& y) := by
  fail_if_success bv_kernel
  fail_if_success bv_fallback
  fail_if_success bv_solve
  bv_decide

-- The opt-in escape hatch does run `bv_decide`, and the audit flags the result.
set_option proofLib.bvDecideFallback true in
theorem opt_in (x y : BitVec 8) : x ^^^ y = (x ||| y) - (x &&& y) := by bv_fallback

/--
info: [axiom_audit] scope=explicit theorems=1 clean=0 dirty=1 culprits=1
[axiom_audit] blame Testing.BvKernel.opt_in kind=bv_decide dependents=1
[axiom_audit] dirty Testing.BvKernel.opt_in <- [Testing.BvKernel.opt_in]
-/
#guard_msgs in #axiom_audit Testing.BvKernel.opt_in

end Testing.BvKernel
