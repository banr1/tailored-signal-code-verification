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
# Carry-Less Polynomial Multiplication Step Tests

Unit tests for `ProofLib.BV.PolyMul`, `wp_steps`, and `wp_sym_steps` covering packed
two-lane 16x16 `PMULL`, high-lane 64x64 `PMULL2` after `LDP`, and rejection of the
reserved `size = 01` `PMULL` encoding.
-/

@[expose] public section

namespace Testing.PolyMulSteps

open Arm64 ProofLib

set_option maxHeartbeats 400000
arm64_proof_prelude

/-! ## Packed two-lane 16x16 `PMULL` -/

@[simp, arm64_norm] def pack_pmull_u16_addr : BitVec 64 := 0x70000#64

/-- Subroutine computing two independent 16x16-to-32-bit carry-less products `(a * b1, a * b2)`
    via `PMULL V0.1Q, V1.1D, V0.1D`. -/
def packPmullU16Code : FnCode :=
  .atAddr "pack_pmull_u16" pack_pmull_u16_addr
    ("12003c28 " ++ -- 0x70000: and   w8, w1, #0xffff
     "92403c49 " ++ -- 0x70004: and   x9, x2, #0xffff
     "aa088128 " ++ -- 0x70008: orr   x8, x9, x8, lsl #32
     "92403c09 " ++ -- 0x7000c: and   x9, x0, #0xffff
     "9e670121 " ++ -- 0x70010: fmov  d1, x9
     "9e670100 " ++ -- 0x70014: fmov  d0, x8
     "0ee0e020 " ++ -- 0x70018: pmull v0.1q, v1.1d, v0.1d
     "4e183c01 " ++ -- 0x7001c: mov   x1, v0.d[1]
     "9e660000 " ++ -- 0x70020: fmov  x0, d0
     "d65f03c0")    -- 0x70024: ret

private theorem mask16_64_eq_zeroExtend (x : BitVec 64) :
    x &&& 0xffff#64 = (x.truncate 16).zeroExtend 64 := by
  bv_bits

private theorem zeroExtend_16_truncate_32 (x : BitVec 64) :
    BitVec.zeroExtend 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by
  bv_bits

private theorem zeroExtend_32_eq_truncate32_64 (x : BitVec 128) :
    BitVec.zeroExtend 32 x = (x.truncate 64).truncate 32 := by
  bv_bits

private theorem setWidth64_and_mask64 (v : BitVec 128) :
    BitVec.setWidth 64 (v &&& 0xffffffffffffffff#128) = v.truncate 64 :=
  truncate_64_and_mask64 v

private theorem setWidth64_ushr64_eq_extractLsb (v : BitVec 128) :
    BitVec.setWidth 64 (v >>> 64) = v.extractLsb' 64 64 := by
  bv_bits

theorem pack_pmull_u16_wp_sym_steps_test (prog : Program) (s0 : State) (r0 r1 r2 : BitVec 64)
    (hc : packPmullU16Code.holds prog)
    (hpc : s0.pc = pack_pmull_u16_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = r0)
    (hx1 : s0.readReg64 .x1 = r1)
    (hx2 : s0.readReg64 .x2 = r2) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf =>
        let a := r0.truncate 16
        let b1 := r1.truncate 16
        let b2 := r2.truncate 16
        sf.readReg64 .x1 = 0#64 ∧
        (sf.readReg64 .x0).truncate 32 =
          (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 ∧
        ((sf.readReg64 .x0) >>> 32).truncate 32 =
          (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32) emp) := by
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, Entails.refl emp⟩
  simp only [wp_norm, arm64_norm, setWidth64_and_mask64, setWidth64_ushr64_eq_extractLsb,
    mask16_64_eq_zeroExtend, zeroExtend_16_truncate_32]
  exact ⟨polyMul_64_pack32_u16_hi64 _ _ _,
         (zeroExtend_32_eq_truncate32_64 _).trans (polyMul_64_pack32_u16_lo32 _ _ _),
         polyMul_64_pack32_u16_hi32 _ _ _⟩

theorem pack_pmull_u16_wp_steps_test (prog : Program) (s0 : State) (r0 r1 r2 : BitVec 64)
    (hc : packPmullU16Code.holds prog)
    (hpc : s0.pc = pack_pmull_u16_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = r0)
    (hx1 : s0.readReg64 .x1 = r1)
    (hx2 : s0.readReg64 .x2 = r2) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf =>
        let a := r0.truncate 16
        let b1 := r1.truncate 16
        let b2 := r2.truncate 16
        sf.readReg64 .x1 = 0#64 ∧
        (sf.readReg64 .x0).truncate 32 =
          (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 ∧
        ((sf.readReg64 .x0) >>> 32).truncate 32 =
          (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32) emp) := by
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, Entails.refl emp⟩
  simp only [wp_norm, arm64_norm, truncate_64_and_mask64, mask16_64_eq_zeroExtend,
    zeroExtend_16_truncate_32]
  exact ⟨polyMul_64_pack32_u16_hi64 _ _ _,
         (zeroExtend_32_eq_truncate32_64 _).trans (polyMul_64_pack32_u16_lo32 _ _ _),
         polyMul_64_pack32_u16_hi32 _ _ _⟩

/-! ## High-lane `PMULL2` after `LDP` -/

@[simp, arm64_norm] def pmull2_ldp_addr : BitVec 64 := 0x70100#64

def pmull2LdpCode : FnCode :=
  .atAddr "pmull2_ldp" pmull2_ldp_addr
    ("ad400400 " ++ -- 0x70100: ldp    q0, q1, [x0]
     "4ee1e002 " ++ -- 0x70104: pmull2 v2.1q, v0.2d, v1.2d
     "4e183c41 " ++ -- 0x70108: mov    x1, v2.d[1]
     "9e660040 " ++ -- 0x7010c: fmov   x0, d2
     "d65f03c0")    -- 0x70110: ret

theorem pmull2_ldp_wp_sym_steps_test (prog : Program) (s0 : State)
    (p a0 a1 b0 b1 : BitVec 64)
    (hc : pmull2LdpCode.holds prog)
    (hpc : s0.pc = pmull2_ldp_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) :
    SepWP prog (s0.readReg64 .lr) s0
      ((p ↦₆₄ a0) ∗ ((p + 8#64) ↦₆₄ a1) ∗ ((p + 16#64) ↦₆₄ b0) ∗ ((p + 24#64) ↦₆₄ b1))
      (sepPost (fun sf =>
        sf.readReg64 .x0 = (polyMul 64 a1 b1).truncate 64 ∧
        sf.readReg64 .x1 = (polyMul 64 a1 b1).extractLsb' 64 64)
        ((p ↦₆₄ a0) ∗ ((p + 8#64) ↦₆₄ a1) ∗ ((p + 16#64) ↦₆₄ b0) ∗ ((p + 24#64) ↦₆₄ b1))) := by
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, Entails.refl _⟩
  simp only [wp_norm, arm64_norm, setWidth64_and_mask64]
  exact setWidth64_ushr64_eq_extractLsb _

/-! ## Reserved `PMULL` `size = 01` encoding -/

@[simp, arm64_norm] def bad_pmull_size_addr : BitVec 64 := 0x70200#64

def badPmullSizeCode : FnCode :=
  .atAddr "bad_pmull_size" bad_pmull_size_addr
    ("0e61e000 " ++ -- 0x70200: reserved size=01 in PMULL encoding space (`decode = none`)
     "d65f03c0")

/--
error: wp_sym_step: could not fetch/decode instruction at PC `459264#64`
hint: check (1) the `*Fns.lean` / `*Code.lean` decode module is imported or a `hasWords` / `hasCode` / `code_fetches` hypothesis is in context, (2) the PC offset is normalized (e.g. `entry + <off>#64`; try `wp_simp_pre` or `examples_generalize_entry`), or (3) execution did not step past function exit or into an un-inlined `BL` callee
-/
#guard_msgs (whitespace := lax) in
example (prog : Program) (s0 : State)
    (hc : badPmullSizeCode.holds prog)
    (hpc : s0.pc = bad_pmull_size_addr) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (sepPost (fun _ => True) emp) := by
  wp_sym_step

end Testing.PolyMulSteps
