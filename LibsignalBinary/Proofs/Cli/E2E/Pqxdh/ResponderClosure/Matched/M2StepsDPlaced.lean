/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsD
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable Stage P2 `remote_identity_key` Shift Blocks

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2StepsD` on Block `518`
(`lsProg_518 ext`, `(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-- `(blkPl_518).base + 0x1064 → +0x12fc` (`None`) under `[LibsignalPlacement]`. -/
theorem p2_seg_1064_none_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr q2 q3 q4 u_a90 : BitVec 64)
    (w0 u_920 : BitVec 32) (h1 h5 u_924 u_a98 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1064#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x12fc#64) s
      (((s.sp + 0x3e1#64) ↦₈ 0#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
       ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
       ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ u_920) ∗
       ((s.sp + 0x924#64) ↦₁₆ u_924) ∗ ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₁₆ u_a98))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e1#64) ↦₈ 0#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
          ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
          ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ w0) ∗
          ((s.sp + 0x924#64) ↦₁₆ h1) ∗ ((s.sp + 0xa90#64) ↦₆₄ q4) ∗
          ((s.sp + 0xa98#64) ↦₁₆ h5)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have h72 : (s.sp + 0x370#64) + 0x72#64 = s.sp + 0x3e2#64 := by bv_omega
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x1064 → +0x1094` (`Some` load) under `[LibsignalPlacement]`. -/
theorem p2_seg_1064_some_load_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr q2 q3 q4 u_a90 : BitVec 64)
    (w0 u_920 : BitVec 32) (h1 h5 u_924 u_a98 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1064#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1094#64) s
      (((s.sp + 0x3e1#64) ↦₈ 1#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
       ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
       ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ u_920) ∗
       ((s.sp + 0x924#64) ↦₁₆ u_924) ∗ ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₁₆ u_a98))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e1#64) ↦₈ 1#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
          ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
          ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ w0) ∗
          ((s.sp + 0x924#64) ↦₁₆ h1) ∗ ((s.sp + 0xa90#64) ↦₆₄ q4) ∗
          ((s.sp + 0xa98#64) ↦₁₆ h5)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x8 = q3 ∧ s1.readReg64 .x9 = q2 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have h72 : (s.sp + 0x370#64) + 0x72#64 = s.sp + 0x3e2#64 := by bv_omega
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x1094 → PublicKey::eq` (`Some` store) under `[LibsignalPlacement]`. -/
theorem p2_seg_1094_some_store_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr q2 q3 q4 d2 d3 d4 : BitVec 64)
    (w0 d0 : BitVec 32) (h1 h5 d1 d5 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1094#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = q3)
    (hx9 : s.readReg64 .x9 = q2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 212) s
      (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((s.sp + 0x3e0#64) ↦₃₂ d0) ∗ ((s.sp + 0x3e4#64) ↦₁₆ d1) ∗
       ((s.sp + 0x3e6#64) ↦₆₄ d2) ∗ ((s.sp + 0x3ee#64) ↦₆₄ d3) ∗
       ((s.sp + 0x3f6#64) ↦₆₄ d4) ∗ ((s.sp + 0x3fe#64) ↦₁₆ d5) ∗
       ((s.sp + 0x920#64) ↦₃₂ w0) ∗ ((s.sp + 0x924#64) ↦₁₆ h1) ∗
       ((s.sp + 0xa90#64) ↦₆₄ q4) ∗ ((s.sp + 0xa98#64) ↦₁₆ h5))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3e0#64) ↦₃₂ w0) ∗ ((s.sp + 0x3e4#64) ↦₁₆ h1) ∗
          ((s.sp + 0x3e6#64) ↦₆₄ q2) ∗ ((s.sp + 0x3ee#64) ↦₆₄ q3) ∗
          ((s.sp + 0x3f6#64) ↦₆₄ q4) ∗ ((s.sp + 0x3fe#64) ↦₁₆ h5) ∗
          ((s.sp + 0x920#64) ↦₃₂ w0) ∗ ((s.sp + 0x924#64) ↦₁₆ h1) ∗
          ((s.sp + 0xa90#64) ↦₆₄ q4) ∗ ((s.sp + 0xa98#64) ↦₁₆ h5)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = msgPtr + 0xc8#64 ∧ s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x10cc#64) := by
  have hx8' : s.readReg64 (Reg.gpr 8#5) = q3 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = q2 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have h76 : (s.sp + 0x370#64) + 0x76#64 = s.sp + 0x3e6#64 := by bv_omega
  have h7e : (s.sp + 0x370#64) + 0x7e#64 = s.sp + 0x3ee#64 := by bv_omega
  have h86 : (s.sp + 0x370#64) + 0x86#64 = s.sp + 0x3f6#64 := by bv_omega
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
