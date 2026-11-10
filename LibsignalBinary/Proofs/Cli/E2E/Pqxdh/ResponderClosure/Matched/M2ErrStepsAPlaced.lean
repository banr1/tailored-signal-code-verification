/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import ProofLib.SepLogic.WPp

/-!
# Relocatable Stage P2 Matched-Session Shared Error Unwind: Part A

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2ErrStepsA` on Block `518`
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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private theorem coro_268_split32_std3_placed (coroPtr w : BitVec 64) :
    (coroPtr + 0x268#64) ↦₆₄ w =
    ((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
    ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32, BitVec.add_assoc]; rfl

private theorem coro_268_pair32_std3_placed (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x268#64) ↦₃₂ lo) ∗ ((coroPtr + 0x26c#64) ↦₃₂ hi) =
    (coroPtr + 0x268#64) ↦₆₄ (hi ++ lo) := by
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_bits
  have hhi : (hi ++ lo).extractLsb' 32 32 = hi := by bv_bits
  rw [coro_268_split32_std3_placed coroPtr (hi ++ lo), hlo, hhi]

private theorem realign_40_at_a98_std3_placed (sp w0 w1 w2 w3 w4 : BitVec 64) :
    (((sp + 0xa98#64) ↦₆₄ w0) ∗ ((sp + 0xaa0#64) ↦₆₄ w1) ∗ ((sp + 0xaa8#64) ↦₆₄ w2) ∗
     ((sp + 0xab0#64) ↦₆₄ w3) ∗ ((sp + 0xab8#64) ↦₆₄ w4)) =
    (((sp + 0xa98#64) ↦₃₂ w0.extractLsb' 0 32) ∗
     ((sp + 0xa9c#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
     ((sp + 0xaa4#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
     ((sp + 0xaac#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
     ((sp + 0xab4#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
     ((sp + 0xabc#64) ↦₃₂ w4.extractLsb' 32 32)) := by
  have h := realign_40 (sp + 0xa98#64) w0 w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-- `(blkPl_518).base + 0x1698 → +0x1898` under `[LibsignalPlacement]`. -/
theorem p2_err_tail_b1_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errTag outPtr
    v_a8 v_d0 u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 : BitVec 64)
    (b_390 : BitVec 8)
    (herr_ne_neg2 : errTag ≠ 0xfffffffffffffffe#64)
    (hpc : s.pc = (blkPl_518).base + 0x1698#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx20 : s.readReg64 .x20 = errTag)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1898#64) s
      (((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗ ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗ ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗ ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ u_ab8))
      (fun s1 P_f =>
        (∃ w_258 w_260 w_268 w_270 w_278 v_a9c v_aa4 v_aac v_ab4 : BitVec 64,
         ∃ v_a98 v_abc : BitVec 32,
          P_f ⊢
            ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            ((coroPtr + 0x250#64) ↦₆₄ errTag) ∗ ((coroPtr + 0x258#64) ↦₆₄ w_258) ∗
            ((coroPtr + 0x260#64) ↦₆₄ w_260) ∗ ((coroPtr + 0x268#64) ↦₆₄ w_268) ∗
            ((coroPtr + 0x270#64) ↦₆₄ w_270) ∗ ((coroPtr + 0x278#64) ↦₆₄ w_278) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗ ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
            ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗ ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
            ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗ ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
            ((s.sp + 0xabc#64) ↦₃₂ v_abc)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = errTag ∧
        s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hcond := cond_ne_adds64_of_ne_neg2_std3 herr_ne_neg2
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = errTag := hx20
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [lsLogFilterAddr]
  apply SepWP.fold (Entails.of_eq (coro_268_split32_std3_placed coroPtr u_268)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq (coro_268_pair32_std3_placed coroPtr _ _)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq (realign_40_at_a98_std3_placed s.sp _ _ _ _ _)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨⟨_, _, _, _, _, _, _, _, _, _, _, by sep_frame⟩,
    rfl, rfl, by simp [calleeSavedVRegs, arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x1898 → +0x3588` under `[LibsignalPlacement]`. -/
theorem p2_err_tail_b2_to_3588_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errTag outPtr
    v_a9c v_aa4 v_aac v_ab4 u_370 u_378 u_380 u_388 : BitVec 64)
    (v_a98 v_abc u_390 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x1898#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x3588#64) s
      (((s.sp + 0xa90#64) ↦₆₄ errTag) ∗ ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
       ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗ ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
       ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗ ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
       ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗ ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗ ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗ ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗ ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_a9c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0x380#64) ↦₆₄ v_aac) ∗ ((s.sp + 0x388#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0x390#64) ↦₃₂ v_abc)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_a98.zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = errTag ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, by simp [calleeSavedVRegs, arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `(blkPl_518).base + 0x3588 → dropSessionStructure3` (`ssCap ≠ -1`) under `[LibsignalPlacement]`. -/
theorem p2_err_drop_ss_to_call_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_std3 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
