/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# Regression Tests for `wp_call` Negative PC Offsets and Signed Index Scaling

Regression tests verifying `wp_call` address normalization across signed two's-complement PC
displacements (including mismatch diagnostics) and `@[simp, width_norm]` simplification of
`(BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - s)` under `s <= 32` and `k < 2 ^ 31`.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpCallAndAshrNorm

open Arm64 _root_.ProofLib

section WpCallNegativePcOffset

set_option maxHeartbeats 40000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 0xfffffffffffffe5c#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry - 0x1a4#64)
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 42#64) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_call h_callee ()
  exact SepWP.done (by assumption) (by assumption) (by assumption)

set_option maxHeartbeats 40000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry - 0x1a4#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_x1 : s.readReg64 .x1 = 7#64)
    (h_callee : subroutine_ok prog (entry + 0xfffffffffffffe5c#64)
      (Spec.split (fun (v : BitVec 64) s0 => s0.readReg64 .x1 = v) (fun _ => emp)
        (fun v _ sf => sf.readReg64 .x0 = v) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 7#64) := by
  wp_call h_callee
  exact SepWP.done (by assumption) (by assumption) (Eq.trans (by assumption) h_x1)

set_option maxHeartbeats 40000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_callee : subroutine_ok prog (entry - 0x1a4#64)
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 11#64) (fun _ => emp))) :
    SepWP prog ret_pc
      ((s.writeReg64 .lr ret_pc).setPC (entry + 0xfffffffffffffe5c#64)) emp
      (fun sf _ => sf.readReg64 .x0 = 11#64) := by
  wp_call h_callee ()
  exact SepWP.done (by assumption) (by assumption) (by assumption)

set_option maxHeartbeats 40000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = (entry + 0x200#64) - 0x3a4#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry - 0x1a4#64)
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 17#64) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 17#64) := by
  wp_call h_callee ()
  exact SepWP.done (by assumption) (by assumption) (by assumption)

/--
error: wp_call: call target address does not match callee entry: h_callee is the wrong contract (expected entry entry + 0xfffffffffffffe5c#64 (= entry - 0x1a4#64) / got entry + 0xfffffffffffffe60#64 (= entry - 0x1a0#64))
  call target PC: entry + 0xfffffffffffffe5c#64 (= entry - 0x1a4#64)
  callee entry:   entry + 0xfffffffffffffe60#64 (= entry - 0x1a0#64)
  raw target PC:  entry + 18446744073709551196#64
  raw callee:     entry - 416#64
hint: ensure execution has stepped to the `BL` call site (`wp_steps` / `wp_sym_steps`) and pass the contract matching the call target PC
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 40000 in
example (prog : Program) (entry target_pc ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 0xfffffffffffffe5c#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry - 0x1a0#64)
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 42#64) (fun _ => emp))) :
    SepWP prog target_pc s emp
      (fun sf Q => sf.pc = ret_pc ∧ sf.readReg64 .x0 = 42#64 ∧ Q = emp) := by
  wp_call h_callee ()

end WpCallNegativePcOffset

section SignedIndexScaling

example (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) := by
  simp [hs, hk]

example (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) := by
  simp only [width_norm, hs, hk]

example (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) := by
  simp [hs, hk]

example (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (4294967296 * k)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) := by
  simp only [width_norm, hs, hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 31 = BitVec.ofNat 64 (k * 2) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - 1) = BitVec.ofNat 64 (k * 2 ^ 1) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight 31 = BitVec.ofNat 64 (k * 2) := by
  simp only [wp_norm, width_norm, hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight 31 = BitVec.ofNat 64 (k * 2) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 30 = BitVec.ofNat 64 (k * 4) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - 2) = BitVec.ofNat 64 (k * 2 ^ 2) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight 30 = BitVec.ofNat 64 (k * 4) := by
  simp only [wp_norm, width_norm, hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (4294967296 * k)).sshiftRight 30 = BitVec.ofNat 64 (k * 4) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 29 = BitVec.ofNat 64 (k * 8) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - 3) = BitVec.ofNat 64 (k * 2 ^ 3) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight 29 = BitVec.ofNat 64 (k * 8) := by
  simp only [wp_norm, width_norm, hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight 29 = BitVec.ofNat 64 (k * 8) := by
  simp [hk]

example (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 32 = BitVec.ofNat 64 k := by
  simp [hk]

opaque HoldBV : BitVec 64 → Prop

/--
error: `simp` made no progress
-/
#guard_msgs in
example (k : Nat) (h : HoldBV ((BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 31)) :
    HoldBV ((BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 31) := by
  simp only [width_norm] at h ⊢

/--
error: `simp` made no progress
-/
#guard_msgs in
example (k s : Nat) (hs : s ≤ 32)
    (h : HoldBV ((BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - s))) :
    HoldBV ((BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - s)) := by
  simp only [width_norm, hs] at h ⊢

end SignedIndexScaling

end Examples.Testing.ProofLib.WpCallAndAshrNorm
