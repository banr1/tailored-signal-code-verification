/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.RelocDecode
public meta import Lean.Elab.Tactic

/-!
# Regression Tests for `wp_call` Early-Stop Mnemonics and `wp_step` Fetch Failure Hints

Tests two diagnostic paths:
- `wp_call` early-stop error messages report the halted PC and decoded AArch64 instruction
  mnemonic (`halted at <pc> (<insn>), K instructions before the call`) on both concrete
  `hasWords` blocks and relocatable `Obj.patchRelocs` segments.
- `closeFetchSubgoal` in `wp_step` reports the normalized target PC and suggests checking
  `codeAt`, `hasWords`, or relocation hypotheses when instruction fetch cannot be closed.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpDiag

open Arm64 _root_.ProofLib

/-! ## `wp_call` Early-Stop Halted-Instruction Mnemonics -/

-- Concrete `hasWords` caller: `wp_call` auto-steps past `nop` at `0x10310`, halts at
-- `ldr x0, [x1]` (`0x10314`, 2 instructions before `bl` at `0x1031c`) because `x1` has no
-- points-to cell in `emp`, and reports the halted PC `0x10314#64` instead of `0x10310#64`.
/--
error: wp_call: call target address does not match callee entry: stepping stopped early (halted at 0x10314#64 (ldr x0, [x1]), 2 instructions before the call)
  call target PC: 0x10314#64
  callee entry:   0x10300#64
  raw target PC:  66324#64
  raw callee:     66304#64
  caller insn:    Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 0#5) (AddrMode.Offset (Reg.gpr 1#5) 0#64)
hint: execution is currently stopped at caller instruction `Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 0#5) (AddrMode.Offset (Reg.gpr 1#5) 0#64)` at `0x10314#64` (`wp_steps` / `wp_sym_steps` stopped early before reaching the call target); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 100000 in
example (prog : Program) (target_pc : BitVec 64) (s0 : State)
    (h_code : prog.hasWords 0x10310#64
      [ 0xd503201f#32 -- 0x10310: nop
      , 0xf9400020#32 -- 0x10314: ldr x0, [x1]
      , 0xd503201f#32 -- 0x10318: nop
      , 0x97fffff9#32 -- 0x1031c: bl 0x10300
      , 0xd65f03c0#32 -- 0x10320: ret
      ])
    (h_pc : s0.pc = 0x10310#64)
    (h_run : s0.status = .Running)
    (h_sp : s0.spAligned = true)
    (h_callee : subroutine_ok prog 0x10300#64
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 1#64) (fun _ => emp))) :
    SepWP prog target_pc s0 emp (fun _ _ => True) := by
  wp_call h_callee ()

-- Relocatable `prog.hasWords a (Obj.patchRelocs ...)` caller halted at `a + 0x4#64`
-- (`str x0, [x1]`), 2 instructions before the relocated `BL` at offset 12: `wp_call` unwraps
-- `Obj.patchRelocs`, decodes the template word at `a + 0x4#64`, and reports the assembly mnemonic.
/--
error: wp_call: call target address does not match callee entry: stepping stopped early (halted at a + 0x4#64 (str x0, [x1]), 2 instructions before the call)
  call target PC: a + 0x4#64
  callee entry:   callee_addr
  raw target PC:  a + 4#64
  raw callee:     callee_addr
  caller insn:    Instr.str MemWidth.X64 (Reg.gpr 0#5) (AddrMode.Offset (Reg.gpr 1#5) 0#64)
hint: execution is currently stopped at caller instruction `Instr.str MemWidth.X64 (Reg.gpr 0#5) (AddrMode.Offset (Reg.gpr 1#5) 0#64)` at `a + 0x4#64` (`wp_steps` / `wp_sym_steps` stopped early before reaching the call target); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 100000 in
example (prog : Program) (a callee_addr target_pc : BitVec 64)
    (resolve : String → BitVec 64) (s : State)
    (h_code : prog.hasWords a
      (Obj.patchRelocs
        [{ off := 12, kind := .call26, sym := "alpha_callee", addend := 0 }]
        [ 0xd503201f#32 -- +0x0: nop
        , 0xf9000020#32 -- +0x4: str x0, [x1]
        , 0xd503201f#32 -- +0x8: nop
        , 0x94000000#32 -- +0xc: bl alpha_callee
        , 0xd65f03c0#32 -- +0x10: ret
        ]
        a
        resolve))
    (h_pc : s.pc = a + 4#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_callee : subroutine_ok prog callee_addr
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 1#64) (fun _ => emp))) :
    SepWP prog target_pc s emp (fun _ _ => True) := by
  wp_call h_callee ()

/-! ## `wp_step` Instruction-Fetch Subgoal Failure Hint -/

/-- Wrapper modeling an unreduced symbolic PC expression that simplifies under `@[arm64_norm]`
    without being definitionally equal to `x`. -/
def unsimplifiedPc : Nat → BitVec 64 → BitVec 64
  | 0, x => x
  | n + 1, x => unsimplifiedPc n x

@[simp, arm64_norm] theorem unsimplifiedPc_eq (n : Nat) (x : BitVec 64) :
    unsimplifiedPc n x = x := by
  induction n <;> simp [unsimplifiedPc, *]

-- End-to-end `wp_step`: `applyWriteback (s0.setPC (unsimplifiedPc n base + 8#64)) none` carries
-- `unsimplifiedPc n base + 8#64` into `fetchResOpt` (matching `h_fetch`), while `SepWP.step_stxr64`
-- simplifies `.pc` to `base + 8#64` via `wp_norm_lhs`, causing `closeFetchSubgoal` to fail on
-- `prog.fetch (base + 8#64) = some ...` with the targeted PC and hint.
/--
wp_step: failed to close instruction fetch subgoal at target PC `base + 8#64` (subgoal: `prog.fetch (base + 8#64) = some (Instr.stxr MemWidth.X64 ?rel ?rs ?rn ?rt)`)
hint: check for a missing code-shard / `codeAt` / `hasWords` / `reloc` (`CodeRelocInRange` / `Lo12Aligned` / `BranchInRange`) hypothesis covering this PC, or simplify an unreduced `base + offset` PC term (`simp only [wp_norm, arm64_norm, addr_norm]`)
-/
#guard_msgs (error, drop info, substring := true, whitespace := lax) in
set_option maxHeartbeats 80000 in
example (prog : Program) (base target_pc : BitVec 64) (n : Nat) (s0 : State)
    (h_run : s0.status = .Running)
    (h_fetch : prog.fetch (unsimplifiedPc n base + 8#64) =
      some (.stxr .X64 false (.gpr 2#5) .x0 .x1)) :
    SepWP prog target_pc
      (ProofLib.applyWriteback (s0.setPC (unsimplifiedPc n base + 8#64)) none)
      emp (fun _ _ => True) := by
  wp_step

-- Direct `closeFetchSubgoal` test when the subgoal's PC is `s0.pc` with `h_pc : s0.pc = base + 0x10#64`:
-- resolves `s0.pc` to `base + 16#64` in the target PC diagnostic.
local elab "test_close_fetch_subgoal" : tactic => ProofLib.closeFetchSubgoal none

/--
error: wp_step: failed to close instruction fetch subgoal at target PC `base + 16#64` (subgoal: `prog.fetch s0.pc = some Instr.nop`)
hint: check for a missing code-shard / `codeAt` / `hasWords` / `reloc` (`CodeRelocInRange` / `Lo12Aligned` / `BranchInRange`) hypothesis covering this PC, or simplify an unreduced `base + offset` PC term (`simp only [wp_norm, arm64_norm, addr_norm]`)
-/
#guard_msgs (error, drop info, whitespace := lax) in
example (prog : Program) (base : BitVec 64) (s0 : State)
    (h_pc : s0.pc = base + 0x10#64) :
    prog.fetch s0.pc = some .nop := by
  test_close_fetch_subgoal

end Examples.Testing.ProofLib.WpDiag
