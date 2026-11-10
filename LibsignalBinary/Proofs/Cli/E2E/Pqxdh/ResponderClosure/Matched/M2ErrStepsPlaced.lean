/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrSteps
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable Stage P2 Remote-Identity Check and Error Unwind

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2ErrSteps` on Block `518`
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

/-- `(blkPl_518).base + 0x094c → +0x1064` under `[LibsignalPlacement]`. -/
theorem p2_seg_094c_ok_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1064#64) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3e0#64) ↦₈ 0#8))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3e0#64) ↦₈ 0#8)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x10cc → +0x1648` (`x0 = 1#64`) under `[LibsignalPlacement]`. -/
theorem p2_seg_10cc_match_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr u_a8 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x10cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1648#64) s
      (((s.sp + 0xa8#64) ↦₆₄ u_a8))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xa8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = 2#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 1#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x10cc → +0x12fc` (`x0 = 0#64`) under `[LibsignalPlacement]`. -/
theorem p2_seg_10cc_mismatch_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x10cc#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x12fc#64) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x12fc → strToOwnedLocal2Name` under `[LibsignalPlacement]`. -/
theorem p2_seg_12fc_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x12fc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 =
          lsρ "libsignal_cli_handshake:.rodata..Lanon.86" ∧
        s1.readReg64 .x2 = 70#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1310#64) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
