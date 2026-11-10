/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Arm64
public meta import Arm64
public import ProofLib
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.SymWP.InsnSteps
public import ProofLib.SepLogic.SymWP

/-!
# Regression Tests for Unscaled `LDUR*` and `STUR*` Step Rules

Tests `classifyInsnStepRule`, `wp_sym_steps`, and `wp_steps` on unscaled byte, halfword, and
signed-word loads and stores (`SepWP.step_ldur*` and `SepWP.step_stur*`) across halfword cells,
odd-offset byte-pair cells, and byte slices (`↦ₛ`), along with `proofLib.wpStrict` diagnostics on
missing cells.
-/

@[expose] public section

namespace Testing.UnscaledLdurSteps

open Arm64 ProofLib

/-! ## `classifyInsnStepRule` coverage -/

public meta section Classifier
open Lean Meta

def decodeWordExpr (w : BitVec 32) : MetaM Expr := do
  let r ← withTransparency .all (reduce (mkApp (mkConst ``Arm64.decode) (toExpr w)))
  if r.isAppOfArity ``Option.some 2 then
    return r.getArg! 1
  throwError "decodeWordExpr: failed to decode {w}"

def testUnscaledClassifier : MetaM Unit := do
  let check (label : String) (w : BitVec 32) (expected : SymInsnStepRule) : MetaM Unit := do
    let (rule, _) := classifyInsnStepRule (← decodeWordExpr w)
    unless rule == expected do
      throwError "classifyInsnStepRule [{label}]: got theorems {rule.theoremNames}, expected {expected.theoremNames}"
  check "LDURH W9, [X0, #1]"   0x78401009#32 .ldr16
  check "LDURSH W9, [X0, #1]"  0x78c01009#32 .ldrsh16
  check "LDURSH X9, [X0, #1]"  0x78801009#32 .ldrsh16
  check "STURH W9, [X0, #1]"   0x78001009#32 .str16
  check "LDURB W9, [X0, #1]"   0x38401009#32 .ldr8
  check "LDURSB W9, [X0, #1]"  0x38c01009#32 .ldrsb
  check "LDURSB X9, [X0, #1]"  0x38801009#32 .ldrsb
  check "STURB W9, [X0, #1]"   0x38001009#32 .str8
  check "LDURSW X9, [X0, #1]"  0xb8801009#32 .ldrsw32
  check "LDUR W9, [X0, #1]"    0xb8401009#32 .ldr32
  let (rule64, _) := classifyInsnStepRule (← decodeWordExpr 0xf8401009#32)
  unless rule64.theoremNames == #[``SepWP.step_ldr64] do
    throwError "classifyInsnStepRule [LDUR X9, [X0, #1]]: got {rule64.theoremNames}"

#eval testUnscaledClassifier

end Classifier

/-! ## End-to-end `wp_sym_steps` and `wp_steps` proofs -/

section EndToEnd

set_option maxHeartbeats 400000
arm64_proof_prelude

@[simp, arm64_norm] def ldur_addr : BitVec 64 := 0x50000#64

/-- `ldurh w9, [x0, #1]; ret` -/
def ldurhCode : FnCode := .atAddr "ldurh" ldur_addr ("78401009 " ++ "d65f03c0")

theorem ldurh_cell_ok (prog : Program) (h : ldurhCode.holds prog) :
    prog.subroutineOk "ldurh"
      ({ pre := fun (g : BitVec 64 × BitVec 16) s0 =>
           ⌜s0.readReg64 .x0 = g.1⌝ ∗ ((g.1 + 1#64) ↦₁₆ g.2)
         post := fun g _ sf =>
           ⌜sf.readReg64 .x9 = g.2.zeroExtend 64⌝ ∗ ((g.1 + 1#64) ↦₁₆ g.2) } : Spec _) := by
  wp_init g s0
  wp_sym_steps
  wp_done

abbrev BytePairSpec (rx : BitVec 8 → BitVec 8 → BitVec 64) : Spec (BitVec 64 × BitVec 8 × BitVec 8) where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.1⌝ ∗ ((g.1 + 1#64) ↦₈ g.2.1) ∗ ((g.1 + 2#64) ↦₈ g.2.2)
  post := fun g _ sf =>
    ⌜sf.readReg64 .x9 = rx g.2.1 g.2.2⌝ ∗ ((g.1 + 1#64) ↦₈ g.2.1) ∗ ((g.1 + 2#64) ↦₈ g.2.2)

theorem ldurh_bytes_sym_ok (prog : Program) (h : ldurhCode.holds prog) :
    prog.subroutineOk "ldurh" (BytePairSpec fun b0 b1 => (b1 ++ b0).zeroExtend 64) := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem ldurh_bytes_wp_ok (prog : Program) (h : ldurhCode.holds prog) :
    prog.subroutineOk "ldurh" (BytePairSpec fun b0 b1 => (b1 ++ b0).zeroExtend 64) := by
  wp_init g s0
  wp_steps
  wp_done

theorem ldurh_byteslist_ok (prog : Program) (h : ldurhCode.holds prog) :
    prog.subroutineOk "ldurh"
      ({ pre := fun (g : BitVec 64 × BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8) s0 =>
           ⌜s0.readReg64 .x0 = g.1⌝ ∗ (g.1 ↦ₛ [g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2])
         post := fun g _ sf =>
           ⌜sf.readReg64 .x9 = (g.2.2.2.1 ++ g.2.2.1).zeroExtend 64⌝ ∗
           (g.1 ↦ₛ [g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2]) } : Spec _) := by
  wp_init g s0
  wp_sym_steps
  wp_done

/-- `ldursh x9, [x0, #1]; ret` -/
def ldurshXCode : FnCode := .atAddr "ldursh_x" ldur_addr ("78801009 " ++ "d65f03c0")
/-- `ldursh w9, [x0, #1]; ret` -/
def ldurshWCode : FnCode := .atAddr "ldursh_w" ldur_addr ("78c01009 " ++ "d65f03c0")

theorem ldursh_x_bytes_ok (prog : Program) (h : ldurshXCode.holds prog) :
    prog.subroutineOk "ldursh_x" (BytePairSpec fun b0 b1 => (b1 ++ b0).signExtend 64) := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem ldursh_w_bytes_ok (prog : Program) (h : ldurshWCode.holds prog) :
    prog.subroutineOk "ldursh_w"
      (BytePairSpec fun b0 b1 => ((b1 ++ b0).signExtend 32).zeroExtend 64) := by
  wp_init g s0
  wp_sym_steps
  wp_done

/-- `sturh w9, [x0, #1]; ret` -/
def sturhCode : FnCode := .atAddr "sturh" ldur_addr ("78001009 " ++ "d65f03c0")

theorem sturh_bytes_ok (prog : Program) (h : sturhCode.holds prog) :
    prog.subroutineOk "sturh"
      ({ pre := fun (g : BitVec 64 × BitVec 8 × BitVec 8) s0 =>
           ⌜s0.readReg64 .x0 = g.1⌝ ∗ ((g.1 + 1#64) ↦₈ g.2.1) ∗ ((g.1 + 2#64) ↦₈ g.2.2)
         post := fun g s0 _ =>
           ((g.1 + 1#64) ↦₈ (s0.readReg64 .x9).truncate 8) ∗
           ((g.1 + 2#64) ↦₈ (s0.readReg64 .x9).extractLsb' 8 8) } : Spec _) := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem sturh_cell_ok (prog : Program) (h : sturhCode.holds prog) :
    prog.subroutineOk "sturh"
      ({ pre := fun (g : BitVec 64 × BitVec 16) s0 =>
           ⌜s0.readReg64 .x0 = g.1⌝ ∗ ((g.1 + 1#64) ↦₁₆ g.2)
         post := fun g s0 _ => ((g.1 + 1#64) ↦₁₆ (s0.readReg64 .x9).truncate 16) } : Spec _) := by
  wp_init g s0
  wp_sym_steps
  wp_done

/-- `ldursb x9, [x0, #1]; sturb w9, [x0, #2]; ret` -/
def bytesCode : FnCode :=
  .atAddr "bytes" ldur_addr ("38801009 " ++ "38002009 " ++ "d65f03c0")

theorem ldursb_sturb_ok (prog : Program) (h : bytesCode.holds prog) :
    prog.subroutineOk "bytes"
      ({ pre := fun (g : BitVec 64 × BitVec 8 × BitVec 8) s0 =>
           ⌜s0.readReg64 .x0 = g.1⌝ ∗ ((g.1 + 1#64) ↦₈ g.2.1) ∗ ((g.1 + 2#64) ↦₈ g.2.2)
         post := fun g _ sf =>
           ⌜sf.readReg64 .x9 = g.2.1.signExtend 64⌝ ∗
           ((g.1 + 1#64) ↦₈ g.2.1) ∗ ((g.1 + 2#64) ↦₈ g.2.1) } : Spec _) := by
  wp_init g s0
  wp_sym_steps
  wp_done

/-- `ldursw x9, [x0, #1]; ret` -/
def ldurswCode : FnCode := .atAddr "ldursw" ldur_addr ("b8801009 " ++ "d65f03c0")

abbrev ldurswSpec : Spec (BitVec 64 × BitVec 32) where
  pre := fun g s0 => ⌜s0.readReg64 .x0 = g.1⌝ ∗ ((g.1 + 1#64) ↦₃₂ g.2)
  post := fun g _ sf => ⌜sf.readReg64 .x9 = g.2.signExtend 64⌝ ∗ ((g.1 + 1#64) ↦₃₂ g.2)

theorem ldursw_sym_ok (prog : Program) (h : ldurswCode.holds prog) :
    prog.subroutineOk "ldursw" ldurswSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem ldursw_wp_ok (prog : Program) (h : ldurswCode.holds prog) :
    prog.subroutineOk "ldursw" ldurswSpec := by
  wp_init g s0
  wp_steps
  wp_done

end EndToEnd

/-! ## Negative tests: missing cell and `proofLib.wpStrict` diagnostics -/

section Negative

set_option maxHeartbeats 200000
arm64_proof_prelude

abbrev ldurhMissingSpec : Spec (BitVec 64) where
  pre := fun p s0 => ⌜s0.readReg64 .x0 = p⌝
  post := fun _ _ _ => emp

/--
error: wp_sym_steps: stuck at pc prog.fnAddr
  "ldurh": no step rule applies (set_option proofLib.wpStrict false to stop silently instead)
wp_step: no step rule succeeded for instruction `Instr.ldr RegWidth.W32 MemWidth.H16 false (Reg.gpr 9#5)
  (AddrMode.UnscaledOffset (Reg.gpr 0#5)
    1#64)` (full: `Instr.ldr RegWidth.W32 MemWidth.H16 false (Reg.gpr 9#5)
  (AddrMode.UnscaledOffset (Reg.gpr 0#5) 1#64)`) at PC `prog.fnAddr "ldurh"`
effective address: `p + 1#64`
spatial context points-to atoms: (none)
(detail: `simp` made no progress)
hint: if the target cell is in context at a different width (`↦₆₄` vs `↦₈`/`↦₁₆`/`↦₃₂`) or inside a byte slice/region (`↦ₛ`, `↦ᵣ`, `memRegion`, `stackFrameAt`), prove the slice length bound (`off + w ≤ bs.length` for `wp_sep_access`), split the cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), or use `wp_sym_steps`
-/
#guard_msgs (error) in
set_option proofLib.wpStrict true in
example (prog : Program) (h : ldurhCode.holds prog) :
    prog.subroutineOk "ldurh" ldurhMissingSpec := by
  wp_init p s0
  wp_sym_steps

/--
error: wp_steps: stuck at pc prog.fnAddr
  "ldurh": no step rule applies (set_option proofLib.wpStrict false to stop silently instead)
wp_step: no step rule succeeded for instruction `Instr.ldr RegWidth.W32 MemWidth.H16 false (Reg.gpr 9#5)
  (AddrMode.UnscaledOffset (Reg.gpr 0#5)
    1#64)` (full: `Instr.ldr RegWidth.W32 MemWidth.H16 false (Reg.gpr 9#5)
  (AddrMode.UnscaledOffset (Reg.gpr 0#5) 1#64)`) at PC `prog.fnAddr "ldurh"`
effective address: `p + 1#64`
spatial context points-to atoms: (none)
(detail: `simp` made no progress)
hint: if the target cell is in context at a different width (`↦₆₄` vs `↦₈`/`↦₁₆`/`↦₃₂`) or inside a byte slice/region (`↦ₛ`, `↦ᵣ`, `memRegion`, `stackFrameAt`), prove the slice length bound (`off + w ≤ bs.length` for `wp_sep_access`), split the cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), or use `wp_sym_steps`
-/
#guard_msgs (error) in
set_option proofLib.wpStrict true in
example (prog : Program) (h : ldurhCode.holds prog) :
    prog.subroutineOk "ldurh" ldurhMissingSpec := by
  wp_init p s0
  wp_steps

-- With `wpStrict` off, `proofLib.wpVerbose` reports the stuck step as info (the goal stays open).
/--
info: wp_sym_steps: stopped at pc prog.fnAddr "ldurh" (target s0.readReg64 Reg.lr): no step rule applies
wp_step: no step rule succeeded for instruction `Instr.ldr RegWidth.W32 MemWidth.H16 false (Reg.gpr 9#5)
  (AddrMode.UnscaledOffset (Reg.gpr 0#5)
    1#64)` (full: `Instr.ldr RegWidth.W32 MemWidth.H16 false (Reg.gpr 9#5)
  (AddrMode.UnscaledOffset (Reg.gpr 0#5) 1#64)`) at PC `prog.fnAddr "ldurh"`
effective address: `p + 1#64`
spatial context points-to atoms: (none)
(detail: `simp` made no progress)
hint: if the target cell is in context at a different width (`↦₆₄` vs `↦₈`/`↦₁₆`/`↦₃₂`) or inside a byte slice/region (`↦ₛ`, `↦ᵣ`, `memRegion`, `stackFrameAt`), prove the slice length bound (`off + w ≤ bs.length` for `wp_sep_access`), split the cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), or use `wp_sym_steps`
next: prove any missing side condition (e.g. `have h : ... := by bv_arith`), focus/split the accessed memory cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), check `*Fns`/`*Code` `HasCode` hypotheses, or apply a custom step lemma before `wp_sym_steps`
-/
#guard_msgs (info, drop error) in
set_option proofLib.wpStrict false in
set_option proofLib.wpVerbose true in
example (prog : Program) (h : ldurhCode.holds prog) :
    prog.subroutineOk "ldurh" ldurhMissingSpec := by
  wp_init p s0
  wp_sym_steps

end Negative

end Testing.UnscaledLdurSteps
