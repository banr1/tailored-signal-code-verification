/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Steps
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import ProofLib.SepLogic.WPp

/-!
# Relocatable Stage P2 Matched-Session Basic Blocks

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2Steps` on Block `518`
(`lsProg_518 ext`, `(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
/-- `(blkPl_518).base + 0x1698 → +0x1778` under `[LibsignalPlacement]`. -/
theorem p2_seg6f_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
      opkPacked kyberPacked ss0 v_330 v_388
      u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
      u_80 u_88 u_90 u_a0 u_a8 u_b0 v_d0
      u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (opkIdIsSome u_268 u_26c u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_390 b_3ac : BitVec 8)
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hpack_lo : (opkPacked &&& 0xff#64) = (opkIdIsSome.zeroExtend 64 &&& 0xff#64))
    (hpc : s.pc = (blkPl_518).base + 0x1698#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx22 : s.readReg64 .x22 = kyberPacked)
    (hx23 : s.readReg64 .x23 = opkIdIsSome.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = opkPacked) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1778#64) s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((s.sp + 0x80#64) ↦₆₄ u_80) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
       ((s.sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((s.sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
       ((s.sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((s.sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ u_3d8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x260#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x268#64) ↦₃₂ v_d0.truncate 32) ∗
          ((coroPtr + 0x26c#64) ↦₃₂ (s.readReg64 (Reg.gpr 11#5)).truncate 32) ∗
          ((coroPtr + 0x270#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x278#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x298#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
          ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0x90#64) ↦₆₄ v_388) ∗
          ((s.sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_330) ∗
          ((s.sp + 0xb0#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
          ((s.sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3ac#64)) ∗
          ((s.sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3c0#64) ↦₆₄ (s.sp + 0x3a0#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ 8#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x9 = 8#64 ∧
        s1.readReg64 .x10 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x11 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = kyberPacked ∧
        s1.readReg64 .x23 = opkPacked ∧
        s1.readReg64 .x24 = opkPacked ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_330 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = kyberPacked := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = opkIdIsSome.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkPacked := hx24
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  have hbfm1 : ((opkIdIsSome.zeroExtend 64 &&& 255#64) |||
    ((opkPacked >>> 8 &&& 72057594037927935#64) <<< 8)) = opkPacked := by
    revert hpack_lo; clear * -; bv_slice
  refine ⟨?_, rfl, rfl,
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', hbfm1, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', hbfm1, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', arm64_norm],
    rfl⟩
  rw [hbfm1]
  exact Entails.refl _

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
