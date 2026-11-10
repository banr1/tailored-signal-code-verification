/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import ProofLib

/-!
# Step Tactic Tests for SIMD, `DC ZVA`, and 32-Bit Branches

Regression tests for `wp_step`, `wp_steps`, `wp_sym_step`, and `wp_sym_steps` covering `MRS DCZID_EL0`,
`DC ZVA`, 32-bit and 64-bit `TBZ`/`TBNZ`/`CBZ`/`CBNZ`/`CMP`/`CCMP` branches, 128-bit SIMD memory
accesses and lane operations, diagnostic error messages, and subword auto-focus.
-/

@[expose] public section

namespace Testing.SimdZvaSteps

open Arm64 ProofLib

set_option maxHeartbeats 400000
arm64_proof_prelude

/-! ## `MRS DCZID_EL0` and `DC ZVA` -/

@[simp, arm64_norm] def mrs_dczva_addr : BitVec 64 := 0x60000#64

def mrsDcZvaCode : FnCode :=
  .atAddr "mrs_dczva" mrs_dczva_addr
    ("d53b00e5 " ++ -- 0x60000: mrs x5, dczid_el0
     "d50b7420 " ++ -- 0x60004: dc zva, x0
     "d65f03c0")    -- 0x60008: ret

theorem mrs_dczva_wp_steps_test (prog : Program) (s0 : State)
    (ptr v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr)
    (halign : ptr &&& ~~~63#64 = ptr) :
    SepWP prog (s0.readReg64 .lr) s0
      ((ptr ↦₆₄ v0) ∗ ((ptr + 8#64) ↦₆₄ v1) ∗ ((ptr + 16#64) ↦₆₄ v2) ∗ ((ptr + 24#64) ↦₆₄ v3) ∗
       ((ptr + 32#64) ↦₆₄ v4) ∗ ((ptr + 40#64) ↦₆₄ v5) ∗ ((ptr + 48#64) ↦₆₄ v6) ∗ ((ptr + 56#64) ↦₆₄ v7))
      (sepPost (fun sf => sf.readReg64 .x5 = 4#64)
        ((ptr ↦₆₄ 0#64) ∗ ((ptr + 8#64) ↦₆₄ 0#64) ∗ ((ptr + 16#64) ↦₆₄ 0#64) ∗ ((ptr + 24#64) ↦₆₄ 0#64) ∗
         ((ptr + 32#64) ↦₆₄ 0#64) ∗ ((ptr + 40#64) ↦₆₄ 0#64) ∗ ((ptr + 48#64) ↦₆₄ 0#64) ∗ ((ptr + 56#64) ↦₆₄ 0#64))) := by
  wp_steps
  wp_done

theorem mrs_dczva_wp_sym_steps_test (prog : Program) (s0 : State)
    (ptr v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr)
    (halign : ptr &&& ~~~63#64 = ptr) :
    SepWP prog (s0.readReg64 .lr) s0
      ((ptr ↦₆₄ v0) ∗ ((ptr + 8#64) ↦₆₄ v1) ∗ ((ptr + 16#64) ↦₆₄ v2) ∗ ((ptr + 24#64) ↦₆₄ v3) ∗
       ((ptr + 32#64) ↦₆₄ v4) ∗ ((ptr + 40#64) ↦₆₄ v5) ∗ ((ptr + 48#64) ↦₆₄ v6) ∗ ((ptr + 56#64) ↦₆₄ v7))
      (sepPost (fun sf => sf.readReg64 .x5 = 4#64)
        ((ptr ↦₆₄ 0#64) ∗ ((ptr + 8#64) ↦₆₄ 0#64) ∗ ((ptr + 16#64) ↦₆₄ 0#64) ∗ ((ptr + 24#64) ↦₆₄ 0#64) ∗
         ((ptr + 32#64) ↦₆₄ 0#64) ∗ ((ptr + 40#64) ↦₆₄ 0#64) ∗ ((ptr + 48#64) ↦₆₄ 0#64) ∗ ((ptr + 56#64) ↦₆₄ 0#64))) := by
  wp_sym_steps
  wp_done

theorem mrs_dczva_masked_ea_wp_steps_test (prog : Program) (s0 : State)
    (ptr ea v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr)
    (hea : ptr &&& ~~~63#64 = ea) :
    SepWP prog (s0.readReg64 .lr) s0
      ((ea ↦₆₄ v0) ∗ ((ea + 8#64) ↦₆₄ v1) ∗ ((ea + 16#64) ↦₆₄ v2) ∗ ((ea + 24#64) ↦₆₄ v3) ∗
       ((ea + 32#64) ↦₆₄ v4) ∗ ((ea + 40#64) ↦₆₄ v5) ∗ ((ea + 48#64) ↦₆₄ v6) ∗ ((ea + 56#64) ↦₆₄ v7))
      (sepPost (fun sf => sf.readReg64 .x5 = 4#64)
        ((ea ↦₆₄ 0#64) ∗ ((ea + 8#64) ↦₆₄ 0#64) ∗ ((ea + 16#64) ↦₆₄ 0#64) ∗ ((ea + 24#64) ↦₆₄ 0#64) ∗
         ((ea + 32#64) ↦₆₄ 0#64) ∗ ((ea + 40#64) ↦₆₄ 0#64) ∗ ((ea + 48#64) ↦₆₄ 0#64) ∗ ((ea + 56#64) ↦₆₄ 0#64))) := by
  wp_steps
  wp_done

theorem mrs_dczva_masked_ea_wp_sym_steps_test (prog : Program) (s0 : State)
    (ptr ea v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr)
    (hea : ptr &&& ~~~63#64 = ea) :
    SepWP prog (s0.readReg64 .lr) s0
      ((ea ↦₆₄ v0) ∗ ((ea + 8#64) ↦₆₄ v1) ∗ ((ea + 16#64) ↦₆₄ v2) ∗ ((ea + 24#64) ↦₆₄ v3) ∗
       ((ea + 32#64) ↦₆₄ v4) ∗ ((ea + 40#64) ↦₆₄ v5) ∗ ((ea + 48#64) ↦₆₄ v6) ∗ ((ea + 56#64) ↦₆₄ v7))
      (sepPost (fun sf => sf.readReg64 .x5 = 4#64)
        ((ea ↦₆₄ 0#64) ∗ ((ea + 8#64) ↦₆₄ 0#64) ∗ ((ea + 16#64) ↦₆₄ 0#64) ∗ ((ea + 24#64) ↦₆₄ 0#64) ∗
         ((ea + 32#64) ↦₆₄ 0#64) ∗ ((ea + 40#64) ↦₆₄ 0#64) ∗ ((ea + 48#64) ↦₆₄ 0#64) ∗ ((ea + 56#64) ↦₆₄ 0#64))) := by
  wp_sym_steps
  wp_done

theorem mrs_dczva_bytes_wp_steps_test (prog : Program) (s0 : State)
    (dst : BitVec 64) (bs : List (BitVec 8)) (k : Nat)
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 k)
    (halign : dst &&& 0xffffffffffffffc0#64 = dst)
    (hk_mod : k % 64 = 0)
    (hk_len : k + 64 ≤ bs.length) :
    SepWP prog (s0.readReg64 .lr) s0
      (dst ↦ₛ ByteSlice.fillPrefix bs 0#8 k)
      (sepPost (fun sf => sf.readReg64 .x5 = 4#64)
        (dst ↦ₛ ByteSlice.fillPrefix bs 0#8 (k + 64))) := by
  wp_steps
  wp_done

theorem mrs_dczva_bytes_wp_sym_steps_test (prog : Program) (s0 : State)
    (dst : BitVec 64) (bs : List (BitVec 8)) (k : Nat)
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 k)
    (halign : dst &&& 0xffffffffffffffc0#64 = dst)
    (hk_mod : k % 64 = 0)
    (hk_len : k + 64 ≤ bs.length) :
    SepWP prog (s0.readReg64 .lr) s0
      (dst ↦ₛ ByteSlice.fillPrefix bs 0#8 k)
      (sepPost (fun sf => sf.readReg64 .x5 = 4#64)
        (dst ↦ₛ ByteSlice.fillPrefix bs 0#8 (k + 64))) := by
  wp_sym_steps
  wp_done

theorem mrs_dczva_bytes_compl63_wp_steps_test (prog : Program) (s0 : State)
    (dst : BitVec 64) (bs : List (BitVec 8)) (k : Nat)
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 k)
    (halign : dst &&& ~~~63#64 = dst)
    (hk_mod : k % 64 = 0)
    (hk_len : k + 64 ≤ bs.length) :
    SepWP prog (s0.readReg64 .lr) s0
      (dst ↦ₛ ByteSlice.fillPrefix bs 0#8 k)
      (sepPost (fun sf => sf.readReg64 .x5 = 4#64)
        (dst ↦ₛ ByteSlice.fillPrefix bs 0#8 (k + 64))) := by
  wp_steps
  wp_done

-- Negative test: `dc zva` over a `↦ₛ` slice shorter than 64 bytes is rejected by `wp_step`.
/--
error: wp_step: no step rule succeeded for instruction `Instr.dcZva
  (Reg.gpr 0#5)` (full: `Instr.dcZva (Reg.gpr 0#5)`) at PC `393220#64`
spatial context points-to atoms: dst ↦ₛ bs
(detail: wp_sep_access: no 64-byte slice in
  dst ↦ₛ bs for
  dst)
-/
#guard_msgs in
example (prog : Program) (s0 : State) (dst : BitVec 64) (bs : List (BitVec 8))
    (hc : mrsDcZvaCode.holds prog)
    (hpc : s0.pc = mrs_dczva_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst)
    (halign : dst &&& 0xffffffffffffffc0#64 = dst)
    (hlen : bs.length = 32) :
    SepWP prog (s0.readReg64 .lr) s0
      (dst ↦ₛ bs)
      (sepPost (fun _ => True) (dst ↦ₛ bs)) := by
  wp_step
  wp_step

/-! ## `TBZ` and `TBNZ` on `W` and `X` registers -/

@[simp, arm64_norm] def tbz_tbnz_addr : BitVec 64 := 0x60100#64

def tbzTbnzCode : FnCode :=
  .atAddr "tbz_tbnz" tbz_tbnz_addr
    ("36180060 " ++ -- 0x60100: tbz  w0, #3, 0x6010c
     "d2800022 " ++ -- 0x60104: mov  x2, #1
     "d65f03c0 " ++ -- 0x60108: ret
     "b7180061 " ++ -- 0x6010c: tbnz x1, #35, 0x60118
     "d2800042 " ++ -- 0x60110: mov  x2, #2
     "d65f03c0 " ++ -- 0x60114: ret
     "d2800062 " ++ -- 0x60118: mov  x2, #3
     "d65f03c0")    -- 0x6011c: ret

theorem tbz_tbnz_wp_steps_test (prog : Program) (s0 : State) (x0 x1 : BitVec 64)
    (hc : tbzTbnzCode.holds prog)
    (hpc : s0.pc = tbz_tbnz_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x0) (hx1 : s0.readReg64 .x1 = x1)
    (hb3 : x0.getLsbD 3 = false) (hb35 : x1.getLsbD 35 = true) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x2 = 3#64) emp) := by
  wp_steps
  wp_done

theorem tbz_tbnz_wp_sym_steps_test (prog : Program) (s0 : State) (x0 x1 : BitVec 64)
    (hc : tbzTbnzCode.holds prog)
    (hpc : s0.pc = tbz_tbnz_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x0) (hx1 : s0.readReg64 .x1 = x1)
    (hb3 : x0.getLsbD 3 = false) (hb35 : x1.getLsbD 35 = true) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x2 = 3#64) emp) := by
  wp_sym_steps
  wp_done

/-! ## `CBZ` and `CBNZ` on 32-bit `W` registers -/

@[simp, arm64_norm] def cbz_cbnz_w_addr : BitVec 64 := 0x60200#64

def cbzCbnzWCode : FnCode :=
  .atAddr "cbz_cbnz_w" cbz_cbnz_w_addr
    ("34000060 " ++ -- 0x60200: cbz  w0, 0x6020c
     "d2800022 " ++ -- 0x60204: mov  x2, #1
     "d65f03c0 " ++ -- 0x60208: ret
     "35000061 " ++ -- 0x6020c: cbnz w1, 0x60218
     "d2800042 " ++ -- 0x60210: mov  x2, #2
     "d65f03c0 " ++ -- 0x60214: ret
     "d2800062 " ++ -- 0x60218: mov  x2, #3
     "d65f03c0")    -- 0x6021c: ret

theorem cbz_cbnz_w_wp_steps_test (prog : Program) (s0 : State)
    (hc : cbzCbnzWCode.holds prog)
    (hpc : s0.pc = cbz_cbnz_w_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = 0x100000000#64)
    (hx1 : s0.readReg64 .x1 = 5#64) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x2 = 3#64) emp) := by
  wp_steps
  wp_done

theorem cbz_cbnz_w_wp_sym_steps_test (prog : Program) (s0 : State)
    (hc : cbzCbnzWCode.holds prog)
    (hpc : s0.pc = cbz_cbnz_w_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = 0x100000000#64)
    (hx1 : s0.readReg64 .x1 = 5#64) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x2 = 3#64) emp) := by
  wp_sym_steps
  wp_done

theorem cbz_cbnz_w_sym_wp_steps_test (prog : Program) (s0 : State) (x0 x1 : BitVec 64)
    (hc : cbzCbnzWCode.holds prog)
    (hpc : s0.pc = cbz_cbnz_w_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x0)
    (hx1 : s0.readReg64 .x1 = x1)
    (hw0 : (x0.truncate 32 == 0#32) = true)
    (hw1 : (x1.truncate 32 == 0#32) = false) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x2 = 3#64) emp) := by
  wp_steps
  wp_done

theorem cbz_cbnz_w_sym_wp_sym_steps_test (prog : Program) (s0 : State) (x0 x1 : BitVec 64)
    (hc : cbzCbnzWCode.holds prog)
    (hpc : s0.pc = cbz_cbnz_w_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x0)
    (hx1 : s0.readReg64 .x1 = x1)
    (hw0 : (x0.truncate 32 == 0#32) = true)
    (hw1 : (x1.truncate 32 == 0#32) = false) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x2 = 3#64) emp) := by
  wp_sym_steps
  wp_done

/-! ## 32-bit `CMP`, `CCMP`, and `B.cond` -/

@[simp, arm64_norm] def cmp32_ccmp32_addr : BitVec 64 := 0x60300#64

def cmp32Ccmp32Code : FnCode :=
  .atAddr "cmp32_ccmp32" cmp32_ccmp32_addr
    ("7100401f " ++ -- 0x60300: cmp  w0, #16
     "540000a3 " ++ -- 0x60304: b.lo 0x60318
     "6b01001f " ++ -- 0x60308: cmp  w0, w1
     "7a402820 " ++ -- 0x6030c: ccmp w1, #0, #0, cs
     "54000081 " ++ -- 0x60310: b.ne 0x60320
     "d65f03c0 " ++ -- 0x60314: ret
     "d2800140 " ++ -- 0x60318: mov  x0, #10
     "d65f03c0 " ++ -- 0x6031c: ret
     "d2800280 " ++ -- 0x60320: mov  x0, #20
     "d65f03c0")    -- 0x60324: ret

theorem cmp32_ccmp32_wp_steps_test (prog : Program) (s0 : State)
    (hc : cmp32Ccmp32Code.holds prog)
    (hpc : s0.pc = cmp32_ccmp32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = 32#64)
    (hx1 : s0.readReg64 .x1 = 8#64) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 20#64) emp) := by
  wp_steps
  wp_done

theorem cmp32_ccmp32_wp_sym_steps_test (prog : Program) (s0 : State)
    (hc : cmp32Ccmp32Code.holds prog)
    (hpc : s0.pc = cmp32_ccmp32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = 32#64)
    (hx1 : s0.readReg64 .x1 = 8#64) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 20#64) emp) := by
  wp_sym_steps
  wp_done

theorem cmp32_ccmp32_sym_wp_steps_test (prog : Program) (s0 : State) (x0 x1 : BitVec 64)
    (hc : cmp32Ccmp32Code.holds prog)
    (hpc : s0.pc = cmp32_ccmp32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x0)
    (hx1 : s0.readReg64 .x1 = x1)
    (hcmp1 : BitVec.ult (x0.truncate 32) 16#32 = false)
    (hcmp2 : BitVec.ule (x1.truncate 32) (x0.truncate 32) = true)
    (hne : (x1.truncate 32 == 0#32) = false) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 20#64) emp) := by
  wp_steps
  wp_done

theorem cmp32_ccmp32_sym_wp_sym_steps_test (prog : Program) (s0 : State) (x0 x1 : BitVec 64)
    (hc : cmp32Ccmp32Code.holds prog)
    (hpc : s0.pc = cmp32_ccmp32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x0)
    (hx1 : s0.readReg64 .x1 = x1)
    (hcmp1 : BitVec.ult (x0.truncate 32) 16#32 = false)
    (hcmp2 : BitVec.ule (x1.truncate 32) (x0.truncate 32) = true)
    (hne : (x1.truncate 32 == 0#32) = false) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 20#64) emp) := by
  wp_sym_steps
  wp_done

/-! ## 128-bit SIMD loads and stores -/

@[simp, arm64_norm] def simd_mem_addr : BitVec 64 := 0x60400#64

def simdMemCode : FnCode :=
  .atAddr "simd_mem" simd_mem_addr
    ("ad410400 " ++ -- 0x60400: ldp  q0, q1, [x0, #0x20]
     "ad820460 " ++ -- 0x60404: stp  q0, q1, [x3, #0x40]!
     "acc20c62 " ++ -- 0x60408: ldp  q2, q3, [x3], #0x40
     "ad010c02 " ++ -- 0x6040c: stp  q2, q3, [x0, #0x20]
     "adfe0460 " ++ -- 0x60410: ldp  q0, q1, [x3, #-0x40]!
     "ac820460 " ++ -- 0x60414: stp  q0, q1, [x3], #0x40
     "3d800002 " ++ -- 0x60418: str  q2, [x0]
     "3c9f0083 " ++ -- 0x6041c: stur q3, [x4, #-0x10]
     "d65f03c0")    -- 0x60420: ret

theorem simd_mem_wp_steps_test (prog : Program) (s0 : State)
    (p0 p3 p4 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 c0 c1 : BitVec 64)
    (hc : simdMemCode.holds prog)
    (hpc : s0.pc = simd_mem_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p0)
    (hx3 : s0.readReg64 .x3 = p3)
    (hx4 : s0.readReg64 .x4 = p4) :
    SepWP prog (s0.readReg64 .lr) s0
      ((p0 ↦₆₄ a0) ∗ ((p0 + 8#64) ↦₆₄ a1) ∗
       ((p0 + 32#64) ↦₆₄ a2) ∗ ((p0 + 40#64) ↦₆₄ a3) ∗
       ((p0 + 48#64) ↦₆₄ a4) ∗ ((p0 + 56#64) ↦₆₄ a5) ∗
       ((p3 + 64#64) ↦₆₄ b0) ∗ ((p3 + 72#64) ↦₆₄ b1) ∗
       ((p3 + 80#64) ↦₆₄ b2) ∗ ((p3 + 88#64) ↦₆₄ b3) ∗
       ((p4 - 16#64) ↦₆₄ c0) ∗ ((p4 - 8#64) ↦₆₄ c1))
      (sepPost (fun sf => sf.readReg64 .x3 = p3 + 128#64)
        ((p0 ↦₆₄ a2) ∗ ((p0 + 8#64) ↦₆₄ a3) ∗
         ((p0 + 32#64) ↦₆₄ a2) ∗ ((p0 + 40#64) ↦₆₄ a3) ∗
         ((p0 + 48#64) ↦₆₄ a4) ∗ ((p0 + 56#64) ↦₆₄ a5) ∗
         ((p3 + 64#64) ↦₆₄ a2) ∗ ((p3 + 72#64) ↦₆₄ a3) ∗
         ((p3 + 80#64) ↦₆₄ a4) ∗ ((p3 + 88#64) ↦₆₄ a5) ∗
         ((p4 - 16#64) ↦₆₄ a4) ∗ ((p4 - 8#64) ↦₆₄ a5))) := by
  wp_steps
  wp_done

theorem simd_mem_wp_sym_steps_test (prog : Program) (s0 : State)
    (p0 p3 p4 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 c0 c1 : BitVec 64)
    (hc : simdMemCode.holds prog)
    (hpc : s0.pc = simd_mem_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p0)
    (hx3 : s0.readReg64 .x3 = p3)
    (hx4 : s0.readReg64 .x4 = p4) :
    SepWP prog (s0.readReg64 .lr) s0
      ((p0 ↦₆₄ a0) ∗ ((p0 + 8#64) ↦₆₄ a1) ∗
       ((p0 + 32#64) ↦₆₄ a2) ∗ ((p0 + 40#64) ↦₆₄ a3) ∗
       ((p0 + 48#64) ↦₆₄ a4) ∗ ((p0 + 56#64) ↦₆₄ a5) ∗
       ((p3 + 64#64) ↦₆₄ b0) ∗ ((p3 + 72#64) ↦₆₄ b1) ∗
       ((p3 + 80#64) ↦₆₄ b2) ∗ ((p3 + 88#64) ↦₆₄ b3) ∗
       ((p4 - 16#64) ↦₆₄ c0) ∗ ((p4 - 8#64) ↦₆₄ c1))
      (sepPost (fun sf => sf.readReg64 .x3 = p3 + 128#64)
        ((p0 ↦₆₄ a2) ∗ ((p0 + 8#64) ↦₆₄ a3) ∗
         ((p0 + 32#64) ↦₆₄ a2) ∗ ((p0 + 40#64) ↦₆₄ a3) ∗
         ((p0 + 48#64) ↦₆₄ a4) ∗ ((p0 + 56#64) ↦₆₄ a5) ∗
         ((p3 + 64#64) ↦₆₄ a2) ∗ ((p3 + 72#64) ↦₆₄ a3) ∗
         ((p3 + 80#64) ↦₆₄ a4) ∗ ((p3 + 88#64) ↦₆₄ a5) ∗
         ((p4 - 16#64) ↦₆₄ a4) ∗ ((p4 - 8#64) ↦₆₄ a5))) := by
  wp_sym_steps
  wp_done

/-! ## Register-offset `LDRB` and SIMD `DUP` / `MOV` -/

@[simp, arm64_norm] def ldrb_dup_mov_addr : BitVec 64 := 0x60500#64

def ldrbDupMovCode : FnCode :=
  .atAddr "ldrb_dup_mov" ldrb_dup_mov_addr
    ("38626801 " ++ -- 0x60500: ldrb w1, [x0, x2]
     "4e010c20 " ++ -- 0x60504: dup  v0.16b, w1
     "4e083c01 " ++ -- 0x60508: mov  x1, v0.d[0]
     "f9000061 " ++ -- 0x6050c: str  x1, [x3]
     "d65f03c0")    -- 0x60510: ret

theorem ldrb_dup_mov_wp_steps_test (prog : Program) (s0 : State)
    (base idx dst old64 : BitVec 64)
    (hc : ldrbDupMovCode.holds prog)
    (hpc : s0.pc = ldrb_dup_mov_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = base)
    (hx2 : s0.readReg64 .x2 = idx)
    (hx3 : s0.readReg64 .x3 = dst) :
    SepWP prog (s0.readReg64 .lr) s0
      (((base + idx) ↦₈ 0xab#8) ∗ (dst ↦₆₄ old64))
      (sepPost (fun sf => sf.readReg64 .x1 = 0xabababababababab#64)
        (((base + idx) ↦₈ 0xab#8) ∗ (dst ↦₆₄ 0xabababababababab#64))) := by
  wp_steps
  wp_done

theorem ldrb_dup_mov_wp_sym_steps_test (prog : Program) (s0 : State)
    (base idx dst old64 : BitVec 64)
    (hc : ldrbDupMovCode.holds prog)
    (hpc : s0.pc = ldrb_dup_mov_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = base)
    (hx2 : s0.readReg64 .x2 = idx)
    (hx3 : s0.readReg64 .x3 = dst) :
    SepWP prog (s0.readReg64 .lr) s0
      (((base + idx) ↦₈ 0xab#8) ∗ (dst ↦₆₄ old64))
      (sepPost (fun sf => sf.readReg64 .x1 = 0xabababababababab#64)
        (((base + idx) ↦₈ 0xab#8) ∗ (dst ↦₆₄ 0xabababababababab#64))) := by
  wp_sym_steps
  wp_done

/-- Symbolic 64-bit value produced by `dup v0.16b, w1` + `mov x1, v0.d[0]` from byte `b : BitVec 8`. -/
@[reducible] def symDupByte64 (b : BitVec 8) : BitVec 64 :=
  (getSimdLane (mapLanes 8 0#128 (fun _ => (b.zeroExtend 64).zeroExtend 128 &&& 255#128) 16) 64 0).truncate 64

theorem ldrb_dup_mov_sym_wp_steps_test (prog : Program) (s0 : State)
    (base idx dst old64 : BitVec 64) (b : BitVec 8)
    (hc : ldrbDupMovCode.holds prog)
    (hpc : s0.pc = ldrb_dup_mov_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = base)
    (hx2 : s0.readReg64 .x2 = idx)
    (hx3 : s0.readReg64 .x3 = dst) :
    SepWP prog (s0.readReg64 .lr) s0
      (((base + idx) ↦₈ b) ∗ (dst ↦₆₄ old64))
      (sepPost (fun sf => sf.readReg64 .x1 = symDupByte64 b)
        (((base + idx) ↦₈ b) ∗ (dst ↦₆₄ symDupByte64 b))) := by
  wp_steps
  dsimp only [symDupByte64, getSimdLane, mapLanes, laneMask]
  wp_done

theorem ldrb_dup_mov_sym_wp_sym_steps_test (prog : Program) (s0 : State)
    (base idx dst old64 : BitVec 64) (b : BitVec 8)
    (hc : ldrbDupMovCode.holds prog)
    (hpc : s0.pc = ldrb_dup_mov_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = base)
    (hx2 : s0.readReg64 .x2 = idx)
    (hx3 : s0.readReg64 .x3 = dst) :
    SepWP prog (s0.readReg64 .lr) s0
      (((base + idx) ↦₈ b) ∗ (dst ↦₆₄ old64))
      (sepPost (fun sf => sf.readReg64 .x1 = symDupByte64 b)
        (((base + idx) ↦₈ b) ∗ (dst ↦₆₄ symDupByte64 b))) := by
  wp_sym_steps
  dsimp only [symDupByte64, getSimdLane, mapLanes, laneMask]
  wp_done

/-! ## `wp_sym_step` diagnostic messages -/

/--
error: wp_sym_step: current PC is an unresolved conditional branch:
  condition: (BitVec.zeroExtend 64 w == 0#64) = true
  then PC:   393740#64
  else PC:   393732#64
hint: split with `wp_if hcond` (if both branches are reachable) or prove `have hcond : (BitVec.zeroExtend 64 w == 0#64) = true := by bv_omega` (or `= false`) before stepping (or `wp_simp_pre [hcond]`)
-/
#guard_msgs (whitespace := lax) in
example (prog : Program) (s0 : State) (w : BitVec 32)
    (hc : cbzCbnzWCode.holds prog)
    (hpc : s0.pc = cbz_cbnz_w_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = w.zeroExtend 64) :
    SepWP prog (s0.readReg64 .lr) s0 emp (sepPost (fun _ => True) emp) := by
  wp_sym_step
  wp_sym_step

/--
error: wp_sym_step: could not fetch/decode instruction at PC `s0.pc`
hint: check (1) the `*Fns.lean` / `*Code.lean` decode module is imported or a `hasWords` / `hasCode` / `code_fetches` hypothesis is in context, (2) the PC offset is normalized (e.g. `entry + <off>#64`; try `wp_simp_pre` or `examples_generalize_entry`), or (3) execution did not step past function exit or into an un-inlined `BL` callee
-/
#guard_msgs in
example (prog : Program) (s0 : State) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (sepPost (fun _ => True) emp) := by
  wp_sym_step

/-! ## Branch decision, subword auto-focus, and close fallback options -/

set_option proofLib.wpDecideBranchOnStep false in
/--
error: wp_step: current PC is an unresolved conditional branch:
  condition: w.ult 16#32 = true
  then PC:   394008#64
  else PC:   393992#64
hint: split with `wp_if hcond` (if both branches are reachable) or prove `have hcond : w.ult 16#32 = true := by bv_omega` (or `= false`) before stepping (or `wp_simp_pre [hcond]`)
-/
#guard_msgs (whitespace := lax) in
example (prog : Program) (s0 : State) (w : BitVec 32)
    (hc : cmp32Ccmp32Code.holds prog)
    (hpc : s0.pc = cmp32_ccmp32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = w.zeroExtend 64)
    (hx1 : s0.readReg64 .x1 = 0#64)
    (hlt : w.toNat < 16) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 10#64) emp) := by
  wp_step
  wp_step
  wp_step

theorem wp_decide_branch_on_step_test (prog : Program) (s0 : State) (w : BitVec 32)
    (hc : cmp32Ccmp32Code.holds prog)
    (hpc : s0.pc = cmp32_ccmp32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = w.zeroExtend 64)
    (hlt : w.toNat < 16) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 10#64) emp) := by
  wp_step
  wp_step
  wp_step
  wp_step
  wp_done

theorem wp_sym_step_decide_branch_on_step_test (prog : Program) (s0 : State) (w : BitVec 32)
    (hc : cmp32Ccmp32Code.holds prog)
    (hpc : s0.pc = cmp32_ccmp32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = w.zeroExtend 64)
    (hlt : w.toNat < 16) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 10#64) emp) := by
  wp_sym_step
  wp_sym_step
  wp_sym_step
  wp_sym_step
  wp_done

@[simp, arm64_norm] def auto_focus_ldr32_addr : BitVec 64 := 0x60600#64

def autoFocusLdr32Code : FnCode :=
  .atAddr "auto_focus_ldr32" auto_focus_ldr32_addr
    ("b9400000 " ++ -- 0x60600: ldr w0, [x0]
     "d65f03c0")    -- 0x60604: ret

set_option proofLib.wpAutoSubwordFocus false in
/--
error: wp_step: no step rule succeeded for instruction `Instr.ldr RegWidth.W32 MemWidth.W32 false (Reg.gpr 0#5)
  (AddrMode.Offset (Reg.gpr 0#5)
    0#64)` (full: `Instr.ldr RegWidth.W32 MemWidth.W32 false (Reg.gpr 0#5)
  (AddrMode.Offset (Reg.gpr 0#5) 0#64)`) at PC `394752#64`
effective address: `p`
spatial context points-to atoms: p ↦₃₂ᵣ v
(detail: wp_sep_access: no cell at p - 4#64 in
  p ↦₃₂ᵣ v)
hint: if the target cell is in context at a different width (`↦₆₄` vs `↦₈`/`↦₁₆`/`↦₃₂`) or inside a byte slice/region (`↦ₛ`, `↦ᵣ`, `memRegion`, `stackFrameAt`), prove the slice length bound (`off + w ≤ bs.length` for `wp_sep_access`), split the cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), or use `wp_sym_steps`
-/
#guard_msgs (whitespace := lax) in
example (prog : Program) (s0 : State) (p : BitVec 64) (v : BitVec 32)
    (hc : autoFocusLdr32Code.holds prog)
    (hpc : s0.pc = auto_focus_ldr32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) :
    SepWP prog (s0.readReg64 .lr) s0 (p ↦₃₂ᵣ v)
      (sepPost (fun sf => sf.readReg64 .x0 = v.zeroExtend 64) (p ↦₃₂ᵣ v)) := by
  wp_step

theorem auto_focus_ldr32_ro_test (prog : Program) (s0 : State) (p : BitVec 64) (v : BitVec 32)
    (hc : autoFocusLdr32Code.holds prog)
    (hpc : s0.pc = auto_focus_ldr32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) :
    SepWP prog (s0.readReg64 .lr) s0 (p ↦₃₂ᵣ v)
      (sepPost (fun sf => sf.readReg64 .x0 = v.zeroExtend 64) (p ↦₃₂ᵣ v)) := by
  wp_step
  wp_step
  wp_done

theorem auto_focus_subword_from_64_test (prog : Program) (s0 : State) (p : BitVec 64) (v : BitVec 64)
    (hc : autoFocusLdr32Code.holds prog)
    (hpc : s0.pc = auto_focus_ldr32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) :
    SepWP prog (s0.readReg64 .lr) s0 (p ↦₆₄ v)
      (sepPost (fun sf => sf.readReg64 .x0 = (v.truncate 32).zeroExtend 64) (p ↦₆₄ v)) := by
  wp_step
  wp_step
  wp_done

@[simp, arm64_norm] def auto_focus_str32_addr : BitVec 64 := 0x60610#64

def autoFocusStr32Code : FnCode :=
  .atAddr "auto_focus_str32" auto_focus_str32_addr
    ("b9000001 " ++ -- 0x60610: str w1, [x0]
     "b9400000 " ++ -- 0x60614: ldr w0, [x0]
     "d65f03c0")    -- 0x60618: ret

set_option proofLib.wpAutoSubwordFocus false in
/--
error: wp_step: no step rule succeeded for instruction `Instr.str MemWidth.W32 (Reg.gpr 1#5)
  (AddrMode.Offset (Reg.gpr 0#5)
    0#64)` (full: `Instr.str MemWidth.W32 (Reg.gpr 1#5)
  (AddrMode.Offset (Reg.gpr 0#5) 0#64)`) at PC `394768#64`
effective address: `sp - 8#64`
spatial context points-to atoms: stackFrameAt sp 16
(detail: wp_sep_access: no cell at sp - 12#64 in
  stackFrameAt sp 16)
hint: if the target cell is in context at a different width (`↦₆₄` vs `↦₈`/`↦₁₆`/`↦₃₂`) or inside a byte slice/region (`↦ₛ`, `↦ᵣ`, `memRegion`, `stackFrameAt`), prove the slice length bound (`off + w ≤ bs.length` for `wp_sep_access`), split the cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), or use `wp_sym_steps`
-/
#guard_msgs (whitespace := lax) in
example (prog : Program) (s0 : State) (sp : BitVec 64)
    (hc : autoFocusStr32Code.holds prog)
    (hpc : s0.pc = auto_focus_str32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = sp - 8#64)
    (hx1 : s0.readReg64 .x1 = 0x12345678#64) :
    SepWP prog (s0.readReg64 .lr) s0 (stackFrameAt sp 16)
      (sepPost (fun sf => sf.readReg64 .x0 = 0x12345678#64) (stackFrameAt sp 16)) := by
  wp_step

theorem auto_focus_stack_frame_str32_ldr32_test (prog : Program) (s0 : State) (sp : BitVec 64)
    (hc : autoFocusStr32Code.holds prog)
    (hpc : s0.pc = auto_focus_str32_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = sp - 8#64)
    (hx1 : s0.readReg64 .x1 = 0x12345678#64) :
    SepWP prog (s0.readReg64 .lr) s0 (stackFrameAt sp 16)
      (sepPost (fun sf => sf.readReg64 .x0 = 0x12345678#64) (memRegion (sp - 16#64) 16)) := by
  wp_step
  wp_step
  wp_step
  wp_done

set_option proofLib.wpFocusCloseFallback false in
/--
error: wp_focus_close (after running `(try wp_assumption)`): unsolved side goal:
a + 4#64 + 4#64 = a + 8#64
hint: address/value equality side goal was not closed by `(try wp_assumption)`; simplify or prove `a + 4#64 + 4#64 = a + 8#64` before stepping
-/
#guard_msgs (whitespace := lax) in
example (a : BitVec 64) : (a + 4#64) + 4#64 = a + 8#64 := by
  wp_focus_close (try wp_assumption)

theorem wp_focus_close_fallback_bv_lin_test (a : BitVec 64) :
    (a + 4#64) + 4#64 = a + 8#64 := by
  wp_focus_close wp_assumption

theorem wp_focus_close_fallback_omega_test (x : BitVec 64) (hx : x.toNat < 10) :
    x.toNat + 4 ≤ 16 := by
  wp_focus_close wp_assumption

end Testing.SimdZvaSteps
