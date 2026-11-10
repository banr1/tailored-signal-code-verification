/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public meta import ProofLib.Testing.Perf.Budget

/-!
# Performance Regression: Deep Straight-Line Register Chains

Benchmarks a 42-instruction straight-line register-dependency chain under `#perf_budget` across
`wp_steps`, `wp_compact`, `wp_done`, and fast-failing `wp_done` diagnostics on mismatched
postconditions, incomplete stepping, and open residual goals.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.Perf.DeepChain

open Arm64 _root_.ProofLib

@[simp, arm64_norm] def deep_chain_addr : BitVec 64 := 0x20000#64

/-- `x1 := x0 + 1; x2 := x1 + 1; ...` cycling through `x1..x15` for 40 instructions (the last write
    is `x10 = x0 + 40`), then `x0 := x10` and `ret`. -/
def deepChainCode : FnCode :=
  .atAddr "deep_chain" deep_chain_addr
    ("91000401 " ++ -- 0x20000: add x1, x0, #1
     "91000422 " ++ -- 0x20004: add x2, x1, #1
     "91000443 " ++ -- 0x20008: add x3, x2, #1
     "91000464 " ++ -- 0x2000c: add x4, x3, #1
     "91000485 " ++ -- 0x20010: add x5, x4, #1
     "910004a6 " ++ -- 0x20014: add x6, x5, #1
     "910004c7 " ++ -- 0x20018: add x7, x6, #1
     "910004e8 " ++ -- 0x2001c: add x8, x7, #1
     "91000509 " ++ -- 0x20020: add x9, x8, #1
     "9100052a " ++ -- 0x20024: add x10, x9, #1
     "9100054b " ++ -- 0x20028: add x11, x10, #1
     "9100056c " ++ -- 0x2002c: add x12, x11, #1
     "9100058d " ++ -- 0x20030: add x13, x12, #1
     "910005ae " ++ -- 0x20034: add x14, x13, #1
     "910005cf " ++ -- 0x20038: add x15, x14, #1
     "910005e1 " ++ -- 0x2003c: add x1, x15, #1
     "91000422 " ++ -- 0x20040: add x2, x1, #1
     "91000443 " ++ -- 0x20044: add x3, x2, #1
     "91000464 " ++ -- 0x20048: add x4, x3, #1
     "91000485 " ++ -- 0x2004c: add x5, x4, #1
     "910004a6 " ++ -- 0x20050: add x6, x5, #1
     "910004c7 " ++ -- 0x20054: add x7, x6, #1
     "910004e8 " ++ -- 0x20058: add x8, x7, #1
     "91000509 " ++ -- 0x2005c: add x9, x8, #1
     "9100052a " ++ -- 0x20060: add x10, x9, #1
     "9100054b " ++ -- 0x20064: add x11, x10, #1
     "9100056c " ++ -- 0x20068: add x12, x11, #1
     "9100058d " ++ -- 0x2006c: add x13, x12, #1
     "910005ae " ++ -- 0x20070: add x14, x13, #1
     "910005cf " ++ -- 0x20074: add x15, x14, #1
     "910005e1 " ++ -- 0x20078: add x1, x15, #1
     "91000422 " ++ -- 0x2007c: add x2, x1, #1
     "91000443 " ++ -- 0x20080: add x3, x2, #1
     "91000464 " ++ -- 0x20084: add x4, x3, #1
     "91000485 " ++ -- 0x20088: add x5, x4, #1
     "910004a6 " ++ -- 0x2008c: add x6, x5, #1
     "910004c7 " ++ -- 0x20090: add x7, x6, #1
     "910004e8 " ++ -- 0x20094: add x8, x7, #1
     "91000509 " ++ -- 0x20098: add x9, x8, #1
     "9100052a " ++ -- 0x2009c: add x10, x9, #1
     "91000140 " ++ -- 0x200a0: add x0, x10, #0
     "d65f03c0")    -- 0x200a4: ret

abbrev DeepChainCodeAt (prog : Program) : Prop :=
  deepChainCode.holds prog

/-- Correct contract: `x0 = x + 40` and the callee-saved registers are preserved. -/
abbrev deepChainSpec : Spec (BitVec 64) where
  pre  := fun x s0 => ⌜s0.readReg64 .x0 = x⌝
  post := fun x s0 sf => ⌜sf.readReg64 .x0 = x + 40#64 ∧ CalleeSavedPreserved s0 sf⌝

/-! ## Complete proof -/

-- Measured: ~9k heartbeats.
#perf_budget 25000 in
theorem deep_chain_ok (prog : Program) (h_code : DeepChainCodeAt prog) :
    prog.subroutineOk "deep_chain" deepChainSpec := by
  wp_init x s0
  wp_steps
  wp_done

-- Measured: ~9k heartbeats.
#perf_budget 25000 in
theorem deep_chain_ok_compact (prog : Program) (h_code : DeepChainCodeAt prog) :
    prog.subroutineOk "deep_chain" deepChainSpec := by
  wp_init x s0
  wp_steps
  wp_compact
  wp_done

/-! ## Fast-failing diagnostic cases -/

-- Wrong expected return value. Measured: ~7k heartbeats.
/--
error: wp_done: postcondition value mismatch:
  actual:   x + 40#64
  expected: x + 41#64
-/
#guard_msgs (error, drop info) in
#perf_budget 20000 in
example (prog : Program) (h_code : DeepChainCodeAt prog) :
    prog.subroutineOk "deep_chain" {
      pre  := fun (x : BitVec 64) s0 => ⌜s0.readReg64 .x0 = x⌝
      post := fun x s0 sf => ⌜sf.readReg64 .x0 = x + 41#64 ∧ CalleeSavedPreserved s0 sf⌝
    } := by
  wp_init x s0
  wp_steps
  wp_done

-- Wrong value for a register written early in the chain (`x15` holds `x + 30`). Measured: ~7k.
/--
error: wp_done: postcondition value mismatch:
  actual:   x + 30#64
  expected: x + 29#64
-/
#guard_msgs (error, drop info) in
#perf_budget 20000 in
example (prog : Program) (h_code : DeepChainCodeAt prog) :
    prog.subroutineOk "deep_chain" {
      pre  := fun (x : BitVec 64) s0 => ⌜s0.readReg64 .x0 = x⌝
      post := fun x s0 sf => ⌜sf.readReg64 .x0 = x + 40#64 ∧
        sf.readReg64 (.gpr 15#5) = x + 29#64 ∧ CalleeSavedPreserved s0 sf⌝
    } := by
  wp_init x s0
  wp_steps
  wp_done

-- Stopped short of the return (`wp_steps 20`). Measured: ~2k heartbeats. Matched by substring
-- because the target PC is printed as a raw free variable.
/--
hint: execution is stopped at `Instr.addSubImm RegWidth.W64 AddSubOp.ADD (Reg.gpr 6#5) (Reg.gpr 5#5) (1#12) false` at `0x20050#64`; run `wp_steps` (or `wp_step` to inspect why stepping stopped) before `wp_done`
-/
#guard_msgs (error, drop info, substring := true) in
#perf_budget 8000 in
example (prog : Program) (h_code : DeepChainCodeAt prog) :
    prog.subroutineOk "deep_chain" deepChainSpec := by
  wp_init x s0
  wp_steps 20
  wp_done

-- A residual side goal (unprovable here) left open next to the main goal. Measured: ~8k.
/--
error: wp_done: closed current goal, but 1 unfocused goal remains open:
  1. [case hb] pure side condition (BitVec bound):
     goal: ⊢ (x + 40#64).ult 10#64 = true
     try:  `bv_arith` (or `bv_omega`) (or use `wp_done?` to keep residual goals open)
-/
#guard_msgs (error, drop info) in
#perf_budget 20000 in
example (prog : Program) (h_code : DeepChainCodeAt prog) :
    prog.subroutineOk "deep_chain" deepChainSpec := by
  wp_init x s0
  wp_steps
  have _hb : (x + 40#64).ult 10#64 = true := ?hb
  wp_done

end Examples.Testing.ProofLib.Perf.DeepChain
