/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StoreStepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDrop
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Placed 1-Element `previous_sessions` Stage P4 `Ok` Drop Basic Block

Proves `p4_seg4e_prev1_of_dealloc_placed_wp` (`+0x048c → retAddr`) on `lsProg_518 ext` under
`[LibsignalPlacement]`, dropping a 1-element `previous_sessions` vector `prevVecAt [enc]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Stage P4 `store_session` `Ok` Epilogue (`+0x048c → retAddr`) -/

set_option maxHeartbeats 1200000 in
private theorem p4_seg4e_prev1_c0_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr retPtr prevCap prevPtr p
      ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64)
    (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x48c#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = retPtr) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ 0#64) ∗ ((prevPtr + 8#64) ↦₆₄ p) ∗
       memRegion (prevPtr + 16#64) 8 ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((retPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((retPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((retPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((retPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((retPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((retPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((retPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((retPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((retPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((retPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((retPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((retPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((retPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((retPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  obtain ⟨hmul_s1, hmul_s2, hmul1, hmul2⟩ := mul24_shift_eq hcapb.2
  rw [hdrP_coro_eq]
  simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptextHead.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = retPtr := hx26
  dsimp only [dpClosureEntryP34Placed] at hpc
  wp_steps
  refine SepWP.weaken_pre
    (entails_replace_sub_p34 (prevVec1_outer_merge prevPtr 0#64 p prevCap.toNat hcapb.1 (by have := hcapb.2; omega))
      (by sep_frame) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by apply Entails.of_eq; simp only [BitVec.add_zero]; ac_rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [calleeSavedVRegs, arm64_norm]⟩

set_option maxHeartbeats 1200000 in
private theorem p4_seg4e_prev1_cnz_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr retPtr prevCap prevPtr c p
      ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64)
    (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hc_nz : c ≠ 0#64) (hc_lt : c.toNat < 2 ^ 63)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x48c#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = retPtr) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ c) ∗ ((prevPtr + 8#64) ↦₆₄ p) ∗
       memRegion (prevPtr + 16#64) 8 ∗
       A.live p c.toNat 1 ∗ memRegion p c.toNat ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((retPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((retPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((retPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((retPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((retPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((retPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((retPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((retPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((retPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((retPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((retPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((retPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((retPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((retPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  have hc_beq : (c == 0#64) = false := beq_eq_false_iff_ne.mpr hc_nz
  have hc_pos : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with h0 | hpos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hc_nz
    · exact hpos
  obtain ⟨hmul_s1, hmul_s2, hmul1, hmul2⟩ := mul24_shift_eq hcapb.2
  rw [hdrP_coro_eq]
  simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptextHead.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = retPtr := hx26
  dsimp only [dpClosureEntryP34Placed] at hpc
  wp_steps
  wp_call hdealloc (p, c.toNat, 1)
  wp_steps
  refine SepWP.weaken_pre
    (entails_replace_sub_p34 (prevVec1_outer_merge prevPtr c p prevCap.toNat hcapb.1 (by have := hcapb.2; omega))
      (by sep_frame) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by apply Entails.of_eq; simp only [BitVec.add_zero, *]; ac_rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [calleeSavedVRegs, arm64_norm]⟩

/-- Placed 1-element `previous_sessions` Stage P4 `Ok` epilogue (`+0x048c → retAddr`) from `dealloc`
`subroutine_ok`. -/
theorem p4_seg4e_prev1_of_dealloc_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr retPtr prevCap prevPtr
      ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (enc : List (BitVec 8))
    (hpc : s.pc = dpClosureEntryP34Placed + 0x48c#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = retPtr) :
    SepWP (lsProg_518 ext) retAddr s
      (prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((retPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((retPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((retPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((retPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((retPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((retPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((retPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((retPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((retPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((retPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((retPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((retPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((retPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((retPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  by_cases hcap : prevCap = 0#64
  · subst hcap
    refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_cap0_false A (coroPtr + 0xe0#64) prevPtr enc)) ?_
    exact sepWP_pure_elim_p34 False.elim
  · refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_drop_split_p34 A (coroPtr + 0xe0#64) prevCap prevPtr enc hcap)) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine sepWP_exists_elim_p34 fun c => sepWP_exists_elim_p34 fun p => ?_
    refine sepWP_pure_elim_p34 fun ⟨hcap1, hcap2, _⟩ => ?_
    refine sepWP_pure_elim_p34 fun hc => ?_
    by_cases hc0 : c = 0#64
    · subst hc0
      simp only [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (p4_seg4e_prev1_c0_placed_wp ext hdealloc s coroPtr retPtr prevCap prevPtr p
          ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          ptextHead w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hpc hrun hsp hx19 hx22 hx25 hx26)
    · simp only [hc0, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (p4_seg4e_prev1_cnz_placed_wp ext hdealloc s coroPtr retPtr prevCap prevPtr c p
          ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          ptextHead w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hc0 hc hpc hrun hsp hx19 hx22 hx25 hx26)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
