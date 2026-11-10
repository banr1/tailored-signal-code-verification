/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecodesPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Relocatable Dispatch and Shared `Ok` Epilogue

Jump-table dispatch (`+36 -> +off` and `+1056`) and shared `Ok` epilogue (`+8176` / `+8180`)
in Block `333`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Relocatable Jump-Table Decomposition and Dispatch (`+36 -> target`) -/

theorem statesFromPbJumpTablePlacedAt_eq [LibsignalPlacement] :
    statesFromPbJumpTablePlacedAt =
      statesFromPbJumpTableBytesAt (lsρ statesFromPbJumpTableSym) := by
  have h0000 : ((0x0000#16).extractLsb' 0 8 = 0x00#8) ∧ ((0x0000#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00ed : ((0x00ed#16).extractLsb' 0 8 = 0xed#8) ∧ ((0x00ed#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0058 : ((0x0058#16).extractLsb' 0 8 = 0x58#8) ∧ ((0x0058#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0086 : ((0x0086#16).extractLsb' 0 8 = 0x86#8) ∧ ((0x0086#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0017 : ((0x0017#16).extractLsb' 0 8 = 0x17#8) ∧ ((0x0017#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0129 : ((0x0129#16).extractLsb' 0 8 = 0x29#8) ∧ ((0x0129#16).extractLsb' 8 8 = 0x01#8) := ⟨by decide, by decide⟩
  have h0147 : ((0x0147#16).extractLsb' 0 8 = 0x47#8) ∧ ((0x0147#16).extractLsb' 8 8 = 0x01#8) := ⟨by decide, by decide⟩
  have h00e1 : ((0x00e1#16).extractLsb' 0 8 = 0xe1#8) ∧ ((0x00e1#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0192 : ((0x0192#16).extractLsb' 0 8 = 0x92#8) ∧ ((0x0192#16).extractLsb' 8 8 = 0x01#8) := ⟨by decide, by decide⟩
  have h0048 : ((0x0048#16).extractLsb' 0 8 = 0x48#8) ∧ ((0x0048#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0171 : ((0x0171#16).extractLsb' 0 8 = 0x71#8) ∧ ((0x0171#16).extractLsb' 8 8 = 0x01#8) := ⟨by decide, by decide⟩
  unfold statesFromPbJumpTablePlacedAt statesFromPbJumpTableBytes statesFromPbJumpTableBytesAt pointsTo16RO
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    h0000.1, h0000.2, h00ed.1, h00ed.2, h0058.1, h0058.2, h0086.1, h0086.2,
    h0017.1, h0017.2, h0129.1, h0129.2, h0147.1, h0147.2, h00e1.1, h00e1.2,
    h0192.1, h0192.2, h0048.1, h0048.2, h0171.1, h0171.2,
    sepConj_assoc, arm64_norm]

/-- Relocatable jump-table dispatch (`+36 -> +off` in Block `333`) for all 10 tagged `V1State.InnerState`
    variants (`TaggedVariantDispatch tag off`). -/
theorem states_from_pb_dispatch_tagged_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA tag off : BitVec 64) (Rest : SepProp)
    (htag : TaggedVariantDispatch tag off)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + off) s1
      ((pbA ↦₆₄ tag) ∗
        statesFromPbJumpTablePlacedAt ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0) := by
  rw [statesFromPbJumpTablePlacedAt_eq]
  change s1.pc = (blkPl_333).base + 36#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + off) s1 _ _
  dsimp only [statesFromPbJumpTableBytesAt, statesFromPbJumpTableSym, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  cases htag <;> (wp_steps; wp_done)

/-- Relocatable jump-table dispatch (`+36 -> +1056` in Block `333`) for the niche-encoded `Ct1Sampled`
    variant when `[pbA] = noneCap` (`uc = none`) or `[pbA] = cap` with `cap.toNat < 2 ^ 63`
    (`uc = some _`). -/
theorem states_from_pb_dispatch_ct1Sampled_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA w0 : BitVec 64) (Rest : SepProp)
    (hw0 : w0 = noneCap ∨ w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1056#64) s1
      ((pbA ↦₆₄ w0) ∗
        statesFromPbJumpTablePlacedAt ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0) := by
  rw [statesFromPbJumpTablePlacedAt_eq]
  change s1.pc = (blkPl_333).base + 36#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1056#64) s1 _ _
  dsimp only [statesFromPbJumpTableBytesAt, statesFromPbJumpTableSym, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  rcases hw0 with rfl | hlt
  · dsimp only [noneCap]
    wp_steps; wp_done
  · have hne2 := cap_add_two_beq_zero_false hlt
    have hcc := cap_xor_highBit_cc_11_false hlt
    wp_steps; wp_done

/-! ## Relocatable Shared `Ok` Epilogue Wrapper (`+8180 / +8176 -> s0.x30`) -/

theorem epilogue_step_8180_8284_region_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (w208 w880 : BitVec 64)
    (q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8284#64)
      s
      ((memRegion out 103 ∗ memRegion (out + 145#64) 16 ∗ memRegion (out + 264#64) 128) ∗
       epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutPartANo145 out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            q704 q720 q736 q752 q768 q784 q800 q816 ∗
          ((out + 145#64) ↦₁₂₈ q848) ∗
          epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 560#64 ∧
        sm.readReg64 .x1 = s.readReg64 .x1 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧
        sm.readReg64 .x5 = s.readReg64 .x5 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧
        sm.readReg64 .x7 = s.readReg64 .x7 ∧
        sm.readReg32 .x8 = (s.readReg64 .x27 >>> 48).setWidth 32 ∧
        sm.readReg64 .x9 = w880 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧
        sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧
        sm.readReg64 .x16 = s.readReg64 .x16 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg32 .x21 = s.readReg32 .x21 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_partA_split out)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro uq376; apply ProofLib.SepWP.exists_left; intro uq360
  apply ProofLib.SepWP.exists_left; intro uq344; apply ProofLib.SepWP.exists_left; intro uq328
  apply ProofLib.SepWP.exists_left; intro uq312; apply ProofLib.SepWP.exists_left; intro uq296
  apply ProofLib.SepWP.exists_left; intro uq280; apply ProofLib.SepWP.exists_left; intro uq264
  apply ProofLib.SepWP.exists_left; intro uq145; apply ProofLib.SepWP.exists_left; intro uh101
  apply ProofLib.SepWP.exists_left; intro ud97; apply ProofLib.SepWP.exists_left; intro ub96
  apply ProofLib.SepWP.exists_left; intro u88; apply ProofLib.SepWP.exists_left; intro u80
  apply ProofLib.SepWP.exists_left; intro u72; apply ProofLib.SepWP.exists_left; intro u64
  apply ProofLib.SepWP.exists_left; intro u56; apply ProofLib.SepWP.exists_left; intro u48
  apply ProofLib.SepWP.exists_left; intro u40; apply ProofLib.SepWP.exists_left; intro u32
  apply ProofLib.SepWP.exists_left; intro u24; apply ProofLib.SepWP.exists_left; intro u16
  apply ProofLib.SepWP.exists_left; intro u8; apply ProofLib.SepWP.exists_left; intro u0
  have hstep := epilogue_step_8180_8284_placed (ext := ext) s fsp out
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88
    ub96 ud97 uh101 uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376
    w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 Frame
    hfsp_align hpc hrun hsp hx19
  refine SepWP.weaken_pre ?_ (SepWP.mono hstep ?_)
  · unfold epilogueOutPartA
    exact Entails.of_eq (by ac_rfl)
  · intro sm Pm _ _ ⟨hPm, hregs⟩
    refine ⟨Entails.trans hPm ?_, hregs⟩
    rw [epilogueOutPartA_eq_no145]
    exact Entails.of_eq (by ac_rfl)

theorem epilogue_step_8284_8468_region_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64) (q848 : BitVec 128) (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887 : BitVec 64)
    (q576 q608 q624 q640 q656 q672 q688 : BitVec 128) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64) (hx6 : s.readReg64 .x6 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8468#64) s
      ((memRegion (out + 103#64) 42 ∗ (((out + 145#64) ↦₁₂₈ q848) ∗ memRegion (out + 161#64) 7) ∗
        memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168) ∗
       epilogueStackPartBPre fsp d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
         q576 q608 q624 q640 q656 q672 q688 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
          ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
          epilogueOutPartBPost out
            ((s.readReg32 .x8).setWidth 8) (s.readReg64 .x4) (s.readReg64 .x5)
            ((s.readReg32 .x21).setWidth 8) (s.readReg64 .x9) w887 (s.readReg64 .x7)
            (d172.setWidth 8) w863 q608 q624 q640 q656 q672 q688
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) ∗
          epilogueStackPartBPost fsp d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
            q576 q608 q624 q640 q656 q672 q688 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = out + 560#64 ∧ sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x2 = 328#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_partB_split out q848)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u552; apply ProofLib.SepWP.exists_left; intro u545
  apply ProofLib.SepWP.exists_left; intro u537; apply ProofLib.SepWP.exists_left; intro ub536
  apply ProofLib.SepWP.exists_left; intro u528; apply ProofLib.SepWP.exists_left; intro u520
  apply ProofLib.SepWP.exists_left; intro u512; apply ProofLib.SepWP.exists_left; intro u504
  apply ProofLib.SepWP.exists_left; intro u496; apply ProofLib.SepWP.exists_left; intro u488
  apply ProofLib.SepWP.exists_left; intro u480; apply ProofLib.SepWP.exists_left; intro u472
  apply ProofLib.SepWP.exists_left; intro u464; apply ProofLib.SepWP.exists_left; intro u456
  apply ProofLib.SepWP.exists_left; intro u448; apply ProofLib.SepWP.exists_left; intro u440
  apply ProofLib.SepWP.exists_left; intro u432; apply ProofLib.SepWP.exists_left; intro u424
  apply ProofLib.SepWP.exists_left; intro u416; apply ProofLib.SepWP.exists_left; intro u408
  apply ProofLib.SepWP.exists_left; intro u400; apply ProofLib.SepWP.exists_left; intro u392
  apply ProofLib.SepWP.exists_left; intro uq248; apply ProofLib.SepWP.exists_left; intro uq232
  apply ProofLib.SepWP.exists_left; intro uq216; apply ProofLib.SepWP.exists_left; intro uq200
  apply ProofLib.SepWP.exists_left; intro uq184; apply ProofLib.SepWP.exists_left; intro uq168
  apply ProofLib.SepWP.exists_left; intro u160; apply ProofLib.SepWP.exists_left; intro ub144
  apply ProofLib.SepWP.exists_left; intro u136; apply ProofLib.SepWP.exists_left; intro u128
  apply ProofLib.SepWP.exists_left; intro u121; apply ProofLib.SepWP.exists_left; intro ub120
  apply ProofLib.SepWP.exists_left; intro u112; apply ProofLib.SepWP.exists_left; intro u104
  apply ProofLib.SepWP.exists_left; intro ub103
  have hstep := epilogue_step_8284_8468_placed (ext := ext) s fsp out
    ub103 u104 u112 ub120 u121 u128 u136 ub144 u160 uq168 uq184 uq200 uq216 uq232 uq248
    u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528
    ub536 u537 u545 u552 d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
    q576 q608 q624 q640 q656 q672 q688
    (((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
     ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗ Frame)
    hfsp_align hpc hrun hsp hx0 hx6 hx19 hx23
  refine SepWP.weaken_pre ?_ (SepWP.mono hstep ?_)
  · unfold epilogueOutPartBPre; exact Entails.of_eq (by ac_rfl)
  · intro sm Pm _ _ ⟨hPm, hregs⟩; exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hregs⟩

theorem epilogue_step_8468_64_region_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64) (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64) s
      (stackAt fsp allocHookStack ∗ memRegion (out + 560#64) 368 ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          (((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q1888) ∗
           ((out + 904#64) ↦₁₂₈ q1904) ∗ ((out + 920#64) ↦₆₄ w1920)) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_partC_split out))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u920
  apply ProofLib.SepWP.exists_left; intro uq904
  apply ProofLib.SepWP.exists_left; intro uq888
  have hstep := epilogue_step_8468_64_placed hmemcpy_sat s fsp out bs240 hbs240
    uq888 uq904 q1888 q1904 u920 w1920 Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
  intro sm Pm _ _ ⟨hPm, hregs⟩
  exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hregs⟩

/-- Relocatable complete shared `Ok` epilogue from `+8180` to `s0.x30` in Block `333`. -/
theorem states_from_pb_epilogue_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8180#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx6 : s.readReg64 .x6 = (s0.sp - 2400#64) + 576#64) (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp halign
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_928_split_8 out))) ?_
  unfold epilogueStackSlots
  refine SepWP.seq (epilogue_step_8180_8284_region_placed (ext := ext) s (s0.sp - 2400#64) out w208 w880
    q704 q720 q736 q752 q768 q784 q800 q816 q848
    (((s0.sp - 2400#64 + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
     ((s0.sp - 2400#64 + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
     memRegion (out + 103#64) 42 ∗ memRegion (out + 161#64) 7 ∗
     memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168 ∗ memRegion (out + 560#64) 368 ∗
     ((s0.sp - 2400#64 + 92#64) ↦₃₂ d92) ∗
     ((s0.sp - 2400#64 + 104#64) ↦₆₄ w104) ∗ ((s0.sp - 2400#64 + 112#64) ↦₆₄ w112) ∗
     ((s0.sp - 2400#64 + 120#64) ↦₆₄ w120) ∗ ((s0.sp - 2400#64 + 160#64) ↦₆₄ w160) ∗
     ((s0.sp - 2400#64 + 172#64) ↦₃₂ d172) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
     ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
     ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240) ∗
     ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ q576) ∗ ((s0.sp - 2400#64 + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
     ((s0.sp - 2400#64 + 608#64) ↦₁₂₈ q608) ∗ ((s0.sp - 2400#64 + 624#64) ↦₁₂₈ q624) ∗
     ((s0.sp - 2400#64 + 640#64) ↦₁₂₈ q640) ∗ ((s0.sp - 2400#64 + 656#64) ↦₁₂₈ q656) ∗
     ((s0.sp - 2400#64 + 672#64) ↦₁₂₈ q672) ∗ ((s0.sp - 2400#64 + 688#64) ↦₁₂₈ q688) ∗
     ((s0.sp - 2400#64 + 832#64) ↦₆₄ w832) ∗
     ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ q1888) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ q1904) ∗
     ((s0.sp - 2400#64 + 1920#64) ↦₆₄ w1920) ∗
     memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
     epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
    hfsp_align hpc hrun hsp hx19 |>
    SepWP.weaken_pre (by unfold epilogueStackPartA; exact Entails.of_eq (by ac_rfl))) ?_
  intro sA PA hpcA hrunA ⟨hPA, hspA, hx0A, hx1A, hx2A, hx4A, hx5A, hx6A, hx7A, hx8A, hx9A,
    hx10A, hx11A, hx12A, hx16A, hx19A, hx21A, hx22A, hx23A, hx24A, hx26A, hx28A, _, htrA⟩
  have hPA' : PA ⊢
      ((memRegion (out + 103#64) 42 ∗ (((out + 145#64) ↦₁₂₈ q848) ∗ memRegion (out + 161#64) 7) ∗
        memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168) ∗
       epilogueStackPartBPre (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 w224 w232 w592
         w832 (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
         q576 q608 q624 q640 q656 q672 q688 ∗
       (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
        memRegion (out + 560#64) 368 ∗ ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240) ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ q1888) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ q1904) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ w1920) ∗
        epilogueOutPartANo145 out
          (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
          (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
          (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
          ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
          (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
          q704 q720 q736 q752 q768 q784 q800 q816 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
        ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
        ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
        ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
        ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
        ((s0.sp - 2400#64 + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
        ((s0.sp - 2400#64 + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
        ((s0.sp - 2400#64 + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
        epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)) := by
    refine Entails.trans hPA ?_
    rw [sepConj_assoc, sepConj_assoc, ← sepConj_assoc (epilogueStackPartA _ _ _ _ _ _ _ _ _ _ _ _),
        ← sepConj_assoc (epilogueStackPartA _ _ _ _ _ _ _ _ _ _ _ _ ∗ _),
        epilogueStackPartA_realign_eq]
    unfold epilogueStackPartBPre
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.seq (SepWP.weaken_pre hPA' (epilogue_step_8284_8468_region_placed (ext := ext) sA (s0.sp - 2400#64) out q848
    d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832
    (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
    q576 q608 q624 q640 q656 q672 q688 _
    hfsp_align hpcA hrunA hspA hx0A (hx6A.trans hx6) hx19A (hx23A.trans hx23))) ?_
  intro sB PB hpcB hrunB ⟨hPB, hspB, hx0B, hx1B, hx2B, hx19B, _, htrB⟩
  rw [hx8A, hx4A, hx5A, hx21A, hx9A, hx7A, hx2A, hx11A, hx22A, hx24A, hx10A, hx26A, hx12A, hx1A, hx28A, hx16A] at hPB
  refine SepWP.seq (SepWP.weaken_pre (Entails.trans hPB (Entails.of_eq (by ac_rfl)))
    (epilogue_step_8468_64_region_placed hmemcpy_sat sB (s0.sp - 2400#64) out bs240 hbs240 q1888 q1904 w1920
      (((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
       epilogueOutPartBPost out
         (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
         (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
         w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
         (d172.setWidth 8) (overlapWord7 (q848.extractLsb' 64 64) w864)
         q608 q624 q640 q656 q672 q688
         w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
         (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
         (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
         (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
         w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) ∗
       epilogueStackPartBPost (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 w224 w232 w592
         w832 (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
         q576 q608 q624 q640 q656 q672 q688 ∗
       memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       epilogueOutPartANo145 out
         (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
         (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
         (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
         ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
         (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
         q704 q720 q736 q752 q768 q784 q800 q816 ∗
       ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
       ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
       ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
       ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
       ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
       ((s0.sp - 2400#64 + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
       ((s0.sp - 2400#64 + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
       ((s0.sp - 2400#64 + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      hfsp_align hpcB hrunB hspB hx0B hx1B hx2B hx19B)) ?_
  intro sC PC hpcC hrunC ⟨hPC, hspC, htrC⟩
  have hPC' : PC ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (epilogueOutFull out
        (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
        (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
        (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
        ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
        (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
        (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
        (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
        w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
        (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
        (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
        (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
        (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
        w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240 q1888 q1904 w1920 ∗
       Frame) := by
    refine Entails.trans hPC ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    have hstk := epilogueStackPost_entails_2304 (s0.sp - 2400#64)
      d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240 hbs240
      q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 q1888 q1904 w1920
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hstk))
    unfold epilogueStackPartBPost epilogueStackGaps
      epilogueOutPartANo145 epilogueOutPartBPost epilogueOutFull
    exact Entails.of_eq (by ac_rfl)
  have hep := states_from_pb_epilogue_64_placed (ext := ext) s0 sC
    (epilogueOutFull out
      (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
      (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
      (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
      ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
      (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
      (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
      (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
      w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
      (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
      (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
      (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
      (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
      w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240 q1888 q1904 w1920 ∗
     Frame)
    halign hpcC hrunC hspC (htrC.trans (htrB.trans (htrA.trans htr)))
  refine SepWP.weaken_pre hPC' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Relocatable complete shared `Ok` epilogue from `+8176` (`add x6, sp, #576`) to `s0.x30` in Block `333`. -/
theorem states_from_pb_epilogue_8176_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8176#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hstep : ∀ (P_pre : SepProp),
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 8180#64) s P_pre
        (fun s1 P1 =>
          (P1 ⊢ P_pre) ∧ s1.sp = s.sp ∧ s1.readReg64 .x6 = s.sp + 576#64 ∧
          s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
          s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg32 .x3 = s.readReg32 .x3 ∧
          s1.readReg64 .x4 = s.readReg64 .x4 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
          s1.readReg64 .x7 = s.readReg64 .x7 ∧ s1.readReg64 .x8 = s.readReg64 .x8 ∧
          s1.readReg64 .x9 = s.readReg64 .x9 ∧ s1.readReg64 .x10 = s.readReg64 .x10 ∧
          s1.readReg64 .x11 = s.readReg64 .x11 ∧ s1.readReg64 .x12 = s.readReg64 .x12 ∧
          s1.readReg64 .x13 = s.readReg64 .x13 ∧ s1.readReg64 .x14 = s.readReg64 .x14 ∧
          s1.readReg64 .x15 = s.readReg64 .x15 ∧ s1.readReg64 .x16 = s.readReg64 .x16 ∧
          s1.readReg64 .x17 = s.readReg64 .x17 ∧ s1.readReg64 .x18 = s.readReg64 .x18 ∧
          s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
          s1.readReg32 .x21 = s.readReg32 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg32 .x27 = s.readReg32 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x30 = s.readReg64 .x30 ∧
          TraceCalleeSaved s1 s) := by
    intro P_pre
    change s.pc = (blkPl_333).base + 8176#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8180#64) s P_pre _
    wp_steps; wp_done
  refine SepWP.seq (hstep _) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx6_1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx7_1,
    hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
    hx28_1, hx30_1, htr1⟩
  have hep := states_from_pb_epilogue_8180_placed hmemcpy_sat s0 s1 out
    d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240 hbs240
    q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame
    halign hpc1 hrun1 (hsp1.trans hsp) (hx6_1.trans (congrArg (· + 576#64) hsp))
    (hx19_1.trans hx19) (hx23_1.trans hx23) (htr1.trans htr)
  rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
      hx3_1, hx27_32_1, hx27_1, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1,
      hx10_1, hx26_1, hx12_1, hx1_1, hx28_1, hx16_1] at hep
  exact SepWP.weaken_pre hP1 hep

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  statesFromPbJumpTablePlacedAt_eq
  states_from_pb_dispatch_tagged_placed
  states_from_pb_dispatch_ct1Sampled_placed
  epilogue_step_8180_8284_region_placed
  epilogue_step_8284_8468_region_placed
  epilogue_step_8468_64_region_placed
  states_from_pb_epilogue_8180_placed
  states_from_pb_epilogue_8176_placed
)
end CryptoVerification.SpqrV1.States.FromPb
