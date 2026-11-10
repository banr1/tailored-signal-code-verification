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
# Regression Tests for `maxRecDepth` Diagnostics in `arm64_norm`, `wp_step`, and `wp_steps`

Checks `maxRecDepth` diagnostics across `arm64_norm`, `wp_step`, and `wp_steps`: deep well-behaved
terms still normalize, `maxRecDepth` failures report the offending hypothesis, term depth, and
repeated head, `try arm64_norm` propagates the runtime exception, and `wp_steps` emits an explicit
stop diagnostic instead of halting silently.
-/

@[expose] public section

namespace ProofLib.Testing.MaxRecDepthDiag

open Arm64 _root_.ProofLib Lean Elab Term Meta

/-- `deep_sum% n x` elaborates to the left-nested sum `x + 1#64 + 1#64 + ... + 1#64` (`n` terms). -/
elab "deep_sum% " n:num x:term : term => do
  let x ← elabTerm x (some (mkApp (mkConst ``BitVec) (toExpr (64 : Nat))))
  let one ← elabTerm (← `((1#64 : BitVec 64))) none
  let mut e := x
  for _ in [0:n.getNat] do
    e ← mkAppM ``HAdd.hAdd #[e, one]
  return e

/-- `deep_writes% n s` elaborates to the `writeReg64` tower
    `((s.writeReg64 (.gpr 1#5) 0#64).writeReg64 (.gpr 2#5) 0#64) ...` (`n` writes, cycling
    through `x1`..`x20`). -/
elab "deep_writes% " n:num s:term : term => do
  let s ← elabTerm s (some (mkConst ``Arm64.State))
  let zero ← elabTerm (← `((0#64 : BitVec 64))) none
  let mut e := s
  for i in [0:n.getNat] do
    let r ← elabTerm (← `((Reg.gpr (BitVec.ofNat 5 $(Syntax.mkNumLit (toString (1 + i % 20)))) : Reg))) none
    e ← mkAppM ``Arm64.State.writeReg64 #[e, r, zero]
  return e

/-! ## `arm64_norm` -/

-- Success path unchanged: read-over-write normalization still fires.
example (s : Arm64.State) (v : BitVec 64)
    (h : (s.writeReg64 (.gpr 1#5) v).readReg64 (.gpr 1#5) = 0#64) : v = 0#64 := by
  arm64_norm
  exact h

-- A deep but well-behaved term (300-deep `writeReg64` tower) still normalizes: no false positive.
example (s : Arm64.State) (h : (deep_writes% 300 s).readReg64 .x0 = 0#64) :
    s.readReg64 .x0 = 0#64 := by
  arm64_norm
  exact h

-- No progress still fails like `simp ... at *`.
/-- error: `simp` made no progress -/
#guard_msgs in
example (x : BitVec 64) (h : x = 0#64) : x = 0#64 := by
  arm64_norm

-- A 600-deep arithmetic chain in a hypothesis: the error names `h`, its depth and repeated head.
/--
error: arm64_norm: maximum recursion depth (`maxRecDepth`) reached while normalizing hypothesis `h`
deepest term: hypothesis `h` (term depth 605, most frequent head on the deepest path: `HAdd.hAdd` ×600)
hint: generalize (`generalize hx : <deep subterm> = x at h ⊢`) or pre-fold the deep subterm, and restrict the rewrite to one location (`simp only [...] at h`) instead of `at *`
hint: `set_option maxRecDepth N` is not the fix: it only moves the limit (and on a rewrite loop just delays the failure); shrink the term or break the loop instead
-/
#guard_msgs in
example (s : Arm64.State) (x : BitVec 64) (h : s.readReg64 .x0 = deep_sum% 600 x) : True := by
  arm64_norm
  trivial

-- The diagnostic is still a runtime exception: `try` does not swallow it.
/--
error: arm64_norm: maximum recursion depth (`maxRecDepth`) reached while normalizing hypothesis `h`
deepest term: hypothesis `h` (term depth 605, most frequent head on the deepest path: `HAdd.hAdd` ×600)
hint: generalize (`generalize hx : <deep subterm> = x at h ⊢`) or pre-fold the deep subterm, and restrict the rewrite to one location (`simp only [...] at h`) instead of `at *`
hint: `set_option maxRecDepth N` is not the fix: it only moves the limit (and on a rewrite loop just delays the failure); shrink the term or break the loop instead
-/
#guard_msgs in
example (s : Arm64.State) (x : BitVec 64) (h : s.readReg64 .x0 = deep_sum% 600 x) : True := by
  try arm64_norm
  trivial

/-! ## `wp_step` and `wp_steps` -/

-- Success path unchanged: a shallow register hypothesis is folded into the stepped state.
example (prog : Program) (s0 : Arm64.State) (x : BitVec 64)
    (h_code : prog.hasWords 0x10310#64
      [ 0x91000400#32 -- add x0, x0, #1
      , 0xd503201f#32 -- nop
      ])
    (h_pc : s0.pc = 0x10310#64)
    (h_x0 : s0.readReg64 .x0 = x + 1#64)
    (h_run : s0.status = .Running) :
    SepWP prog 0x10318#64 s0 emp (fun _ _ => True) := by
  wp_steps
  wp_done

-- The step rewrites with `h_x0`, whose right-hand side is a 600-deep chain.
/--
error: wp_step: maximum recursion depth (`maxRecDepth`) reached while stepping instruction `Instr.addSubImm RegWidth.W64 AddSubOp.ADD (Reg.gpr 0#5) (Reg.gpr 0#5) (1#12) false` at pc 66320#64
failing sub-step: Tactic `simp` failed with a nested error
deepest term: hypothesis `h_x0` (term depth 605, most frequent head on the deepest path: `HAdd.hAdd` ×600)
hint: generalize (`generalize hx : <deep subterm> = x at h ⊢`) or pre-fold the deep subterm, and restrict the rewrite to one location (`simp only [...] at h`) instead of `at *`
hint: `set_option maxRecDepth N` is not the fix: it only moves the limit (and on a rewrite loop just delays the failure); shrink the term or break the loop instead
-/
#guard_msgs in
example (prog : Program) (s0 : Arm64.State) (x : BitVec 64)
    (h_code : prog.hasWords 0x10310#64
      [ 0x91000400#32 -- add x0, x0, #1
      , 0xd503201f#32 -- nop
      ])
    (h_pc : s0.pc = 0x10310#64)
    (h_x0 : s0.readReg64 .x0 = deep_sum% 600 x)
    (h_run : s0.status = .Running) :
    SepWP prog 0x10318#64 s0 emp (fun _ _ => True) := by
  wp_step

-- The `wp_step` error is an ordinary tactic error: `first` / `try` still fall back.
example (prog : Program) (s0 : Arm64.State) (x : BitVec 64)
    (_h_code : prog.hasWords 0x10310#64
      [ 0x91000400#32 -- add x0, x0, #1
      , 0xd503201f#32 -- nop
      ])
    (_h_pc : s0.pc = 0x10310#64)
    (_h_x0 : s0.readReg64 .x0 = deep_sum% 600 x)
    (_h_run : s0.status = .Running)
    (h : SepWP prog 0x10318#64 s0 emp (fun _ _ => True)) :
    SepWP prog 0x10318#64 s0 emp (fun _ _ => True) := by
  first | wp_step | exact h

-- `wp_steps` still stops before the failing step (callers may continue with another tactic),
-- but says why instead of stopping silently.
/--
info: wp_steps: stopped before instruction #1 (0 stepped): it fails with `maxRecDepth`
wp_step: maximum recursion depth (`maxRecDepth`) reached while stepping instruction `Instr.addSubImm RegWidth.W64 AddSubOp.ADD (Reg.gpr 0#5) (Reg.gpr 0#5) (1#12) false` at pc 66320#64
run `wp_step` here for the deepest term and remedies
-/
#guard_msgs (info, drop error) in
example (prog : Program) (s0 : Arm64.State)
    (h_code : prog.hasWords 0x10310#64
      [ 0x91000400#32 -- add x0, x0, #1
      , 0xd503201f#32 -- nop
      ])
    (h_pc : s0.pc = 0x10310#64)
    (h_run : s0.status = .Running) :
    SepWP prog 0x10318#64 (deep_writes% 300 s0) emp (fun _ _ => True) := by
  wp_steps

end ProofLib.Testing.MaxRecDepthDiag
