/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# Closed `Nat` Offset Call-Target Tests

Regression tests checking that `wp_call` discharges callee-entry equality on ground non-numeral
`Nat` offsets (`entry + BitVec.ofNat 64 d`) via `@[simp, arm64_norm]` lemmas without unfolding `d`
under default-transparency `whnf`, and still reports mismatches for distinct offsets.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpCallClosedNatOffset

open Arm64 _root_.ProofLib

/-! ## Fixture -/

/-- Always `0`, but `whnf` of `widgetTree n a` (a literal `n`) unfolds `2 ^ n` distinct calls
    (the arguments `2 * a`, `2 * a + 1` keep subterms distinct, so `whnf`'s cache does not help). -/
def widgetTree : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a => widgetTree n (2 * a) + widgetTree n (2 * a + 1)

theorem widgetTree_eq (n a : Nat) : widgetTree n a = 0 := by
  induction n generalizing a <;> simp [widgetTree, *]

/-- Offset of a callee `Widget.run` in a synthetic code layout (`= 4096`). -/
def widgetCalleeOff : Nat := widgetTree 16 0 + 4096

/-- Offset of the calling function `Widget.main` in the same layout (`= 1024`). -/
def widgetCallerOff : Nat := widgetTree 16 0 + 1024

@[simp, arm64_norm] theorem widgetCalleeOff_eq : widgetCalleeOff = 4096 := by
  unfold widgetCalleeOff; rw [widgetTree_eq]

@[simp, arm64_norm] theorem widgetCallerOff_eq : widgetCallerOff = 1024 := by
  unfold widgetCallerOff; rw [widgetTree_eq]

/-- A ground offset that is cheap to evaluate but is not a numeral (`= 3076`). -/
def widgetNearOff : Nat := 3076

/-! ## Positive Tests -/

-- `s.pc` from a local hypothesis. One default-transparency `whnf` of the distance costs more than
-- 40000 heartbeats.
set_option maxHeartbeats 20000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 3072#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry + BitVec.ofNat 64 (widgetCalleeOff - widgetCallerOff))
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 42#64) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_call h_callee ()
  exact SepWP.done (by assumption) (by assumption) (by assumption)

-- `s.pc` from a `State.setPC` spine, as after stepping to a `BL`.
set_option maxHeartbeats 20000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_callee : subroutine_ok prog (entry + BitVec.ofNat 64 (widgetCalleeOff - widgetCallerOff))
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 11#64) (fun _ => emp))) :
    SepWP prog ret_pc ((s.writeReg64 .lr ret_pc).setPC (entry + 3072#64)) emp
      (fun sf _ => sf.readReg64 .x0 = 11#64) := by
  wp_call h_callee ()
  exact SepWP.done (by assumption) (by assumption) (by assumption)

/-! ## Negative Test -/

/--
error: wp_call: call target address does not match callee entry: h_callee is the wrong contract (expected entry entry + 0xc00#64 / got entry + 0xc04#64)
  call target PC: entry + 0xc00#64
  callee entry:   entry + 0xc04#64
  raw target PC:  entry + 3072#64
  raw callee:     entry + BitVec.ofNat 64 widgetNearOff
hint: ensure execution has stepped to the `BL` call site (`wp_steps` / `wp_sym_steps`) and pass the contract matching the call target PC
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 20000 in
example (prog : Program) (entry target_pc ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 3072#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry + BitVec.ofNat 64 widgetNearOff)
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 42#64) (fun _ => emp))) :
    SepWP prog target_pc s emp
      (fun sf Q => sf.pc = ret_pc ∧ sf.readReg64 .x0 = 42#64 ∧ Q = emp) := by
  wp_call h_callee ()

end Examples.Testing.ProofLib.WpCallClosedNatOffset
