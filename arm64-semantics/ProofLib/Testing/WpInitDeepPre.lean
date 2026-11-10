/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPp

/-!
# Deep-Precondition Tests for `wp_init` and `wpp_init`

Tests `wp_init` and `wpp_init` on preconditions with more than 50 right-associated
separating-conjunction atoms under `pp.deepTerms = false`, including `#guard_msgs` checks
on `wp_done` postcondition mismatch diagnostics.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpInitDeepPre

open Arm64 _root_.ProofLib

@[simp, arm64_norm] def bump_deep_addr : BitVec 64 := 0x30000#64

def bumpDeepCode : FnCode :=
  .atAddr "bump_deep" bump_deep_addr
    ("f9400001 " ++ -- 0x30000: ldr x1, [x0]
     "91000421 " ++ -- 0x30004: add x1, x1, #1
     "f9000001 " ++ -- 0x30008: str x1, [x0]
     "d65f03c0")    -- 0x3000c: ret

abbrev BumpDeepCodeAt (prog : Program) : Prop :=
  bumpDeepCode.holds prog

/-- 52 right-associated separating-conjunction atoms, exceeding the default
    `pp.deepTerms.threshold = 50` when `pp.deepTerms = false`. -/
def deepExtra52 (q v : BitVec 64) : SepProp :=
  ((q + 0x008#64) ↦₆₄ v) ∗ ((q + 0x010#64) ↦₆₄ v) ∗ ((q + 0x018#64) ↦₆₄ v) ∗ ((q + 0x020#64) ↦₆₄ v) ∗
  ((q + 0x028#64) ↦₆₄ v) ∗ ((q + 0x030#64) ↦₆₄ v) ∗ ((q + 0x038#64) ↦₆₄ v) ∗ ((q + 0x040#64) ↦₆₄ v) ∗
  ((q + 0x048#64) ↦₆₄ v) ∗ ((q + 0x050#64) ↦₆₄ v) ∗ ((q + 0x058#64) ↦₆₄ v) ∗ ((q + 0x060#64) ↦₆₄ v) ∗
  ((q + 0x068#64) ↦₆₄ v) ∗ ((q + 0x070#64) ↦₆₄ v) ∗ ((q + 0x078#64) ↦₆₄ v) ∗ ((q + 0x080#64) ↦₆₄ v) ∗
  ((q + 0x088#64) ↦₆₄ v) ∗ ((q + 0x090#64) ↦₆₄ v) ∗ ((q + 0x098#64) ↦₆₄ v) ∗ ((q + 0x0a0#64) ↦₆₄ v) ∗
  ((q + 0x0a8#64) ↦₆₄ v) ∗ ((q + 0x0b0#64) ↦₆₄ v) ∗ ((q + 0x0b8#64) ↦₆₄ v) ∗ ((q + 0x0c0#64) ↦₆₄ v) ∗
  ((q + 0x0c8#64) ↦₆₄ v) ∗ ((q + 0x0d0#64) ↦₆₄ v) ∗ ((q + 0x0d8#64) ↦₆₄ v) ∗ ((q + 0x0e0#64) ↦₆₄ v) ∗
  ((q + 0x0e8#64) ↦₆₄ v) ∗ ((q + 0x0f0#64) ↦₆₄ v) ∗ ((q + 0x0f8#64) ↦₆₄ v) ∗ ((q + 0x100#64) ↦₆₄ v) ∗
  ((q + 0x108#64) ↦₆₄ v) ∗ ((q + 0x110#64) ↦₆₄ v) ∗ ((q + 0x118#64) ↦₆₄ v) ∗ ((q + 0x120#64) ↦₆₄ v) ∗
  ((q + 0x128#64) ↦₆₄ v) ∗ ((q + 0x130#64) ↦₆₄ v) ∗ ((q + 0x138#64) ↦₆₄ v) ∗ ((q + 0x140#64) ↦₆₄ v) ∗
  ((q + 0x148#64) ↦₆₄ v) ∗ ((q + 0x150#64) ↦₆₄ v) ∗ ((q + 0x158#64) ↦₆₄ v) ∗ ((q + 0x160#64) ↦₆₄ v) ∗
  ((q + 0x168#64) ↦₆₄ v) ∗ ((q + 0x170#64) ↦₆₄ v) ∗ ((q + 0x178#64) ↦₆₄ v) ∗ ((q + 0x180#64) ↦₆₄ v) ∗
  ((q + 0x188#64) ↦₆₄ v) ∗ ((q + 0x190#64) ↦₆₄ v) ∗ ((q + 0x198#64) ↦₆₄ v) ∗ ((q + 0x1a0#64) ↦₆₄ v)

abbrev deepBumpSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre  := fun (p, q, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v) ∗ deepExtra52 q v
  post := fun (p, q, v) _ _sf => (p ↦₆₄ (v + 1#64)) ∗ deepExtra52 q v

def deepBumpPanicSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) :=
  Spec.allowPanicWhen deepBumpSpec (fun (_, _, v) _ _ => v = 0#64)

/-- Implicit `pInitExpr` with 53 spatial atoms under default `pp.deepTerms = false`. -/
theorem wp_init_deep_pre_52_ok (prog : Program) (h_code : BumpDeepCodeAt prog) :
    prog.subroutineOk "bump_deep" deepBumpSpec := by
  simp only [deepBumpSpec, deepExtra52]
  wp_init a s0
  wp_steps
  wp_done

/-- Explicit `P_init` leaving a 52-atom `frameInitExpr` under default `pp.deepTerms = false`. -/
theorem wp_init_deep_frame_52_ok (prog : Program) (h_code : BumpDeepCodeAt prog) :
    prog.subroutineOk "bump_deep" deepBumpSpec := by
  simp only [deepBumpSpec, deepExtra52]
  wp_init a s0 (a.1 ↦₆₄ a.2.2)
  wp_steps
  wp_done

/-- Panic-aware `wpp_init` with 53 spatial atoms under default `pp.deepTerms = false`. -/
theorem wpp_init_deep_pre_52_ok (prog : Program) (h_code : BumpDeepCodeAt prog) :
    prog.subroutineOk "bump_deep" deepBumpPanicSpec := by
  simp only [deepBumpPanicSpec, Spec.allowPanicWhen, deepExtra52]
  wpp_init a s0
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/--
error: wp_done: postcondition memory mismatch at `a.fst`:
  actual:   a.2.snd + 1#64
  expected: a.2.snd + 2#64
-/
#guard_msgs in
set_option pp.deepTerms false in
example (prog : Program) (h_code : BumpDeepCodeAt prog) :
    prog.subroutineOk "bump_deep"
      { pre  := fun (p, q, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v) ∗ deepExtra52 q v
        post := fun (p, q, v) _ _sf => (p ↦₆₄ (v + 2#64)) ∗ deepExtra52 q v } := by
  simp only [deepExtra52]
  wp_init a s0
  wp_steps
  wp_done

/--
error: wp_done: postcondition memory mismatch at `a.fst`:
  actual:   a.2.snd + 1#64
  expected: a.2.snd + 2#64
-/
#guard_msgs in
set_option pp.deepTerms false in
example (prog : Program) (h_code : BumpDeepCodeAt prog) :
    prog.subroutineOk "bump_deep"
      (Spec.allowPanicWhen
        { pre  := fun (p, q, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v) ∗ deepExtra52 q v
          post := fun (p, q, v) _ _sf => (p ↦₆₄ (v + 2#64)) ∗ deepExtra52 q v }
        (fun (_, _, v) _ _ => v = 0#64)) := by
  simp only [Spec.allowPanicWhen, deepExtra52]
  wpp_init a s0
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

end Examples.Testing.ProofLib.WpInitDeepPre
