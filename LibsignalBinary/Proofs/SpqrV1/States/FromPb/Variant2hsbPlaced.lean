/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1
open LibsignalBinary.Proofs.SpqrV1.States
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v2hs_bv_sub_sub_lit

private theorem sepWPp_of_sepWP_lscl [LibsignalPlacement]
    {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {onPanic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun s' P' =>
      LibsignalCodeLoaded lsmpl s'.mem → SepWPp prog target_pc s' P' post onPanic)) :
    SepWPp prog target_pc s P post onPanic :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

theorem v2hs_copy_pb_to_stack_508_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (d_w0 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 3348#64
       else lsmpl.base 333 + 592#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64)
            d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
            w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  rw [← v2hs_words_eq_pb128 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32]
  refine SepWP.weaken_pre (sepConj_mono_left (v2hs_memRegion_2304_split_896_176_1232 (s0.sp - 2400#64))) ?_
  wp_simp_pre [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt, pointsTo128,
    arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro q10
  apply ProofLib.SepWP.exists_left; intro q9
  apply ProofLib.SepWP.exists_left; intro q8
  apply ProofLib.SepWP.exists_left; intro q7
  apply ProofLib.SepWP.exists_left; intro q6
  apply ProofLib.SepWP.exists_left; intro q5
  apply ProofLib.SepWP.exists_left; intro q4
  apply ProofLib.SepWP.exists_left; intro q3
  apply ProofLib.SepWP.exists_left; intro q2
  apply ProofLib.SepWP.exists_left; intro q1
  apply ProofLib.SepWP.exists_left; intro q0
  by_cases hcmn : (d_w0 + 1#64 == 0#64) = true <;>
    simp only [hcmn, Bool.false_eq_true, ↓reduceIte]
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 508#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3348#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 508#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 592#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done

theorem v2hs_check_ptsNeeded_592_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 592#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (d_w24.extractLsb' 0 32 == 480#32) = true
       then lsmpl.base 333 + 3348#64
       else lsmpl.base 333 + 604#64)
      s1
      (v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  wp_simp_pre [v2hs_optProtoDecoderWordsAt, arm64_norm, sepConj_assoc]
  by_cases hpts : (d_w24.extractLsb' 0 32 == 480#32) = true <;>
    simp only [hpts, Bool.false_eq_true, ↓reduceIte]
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 592#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3348#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_optProtoDecoderWordsAt]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
    · wp_done
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 592#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 604#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_optProtoDecoderWordsAt]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
    · wp_done

theorem v2hs_uc_none_3348_to_4392_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4392#64) s1
      (v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
        noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  wp_simp_pre [v2hs_ucWordsAt, noneCap, arm64_norm, sepConj_assoc]
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 3348#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4392#64) _ _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · dsimp only [v2hs_ucWordsAt, noneCap]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
  · wp_done

theorem v2hs_validate_err_dk_3348_to_4660_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4660#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hu8_ne := cap_add_one_beq_zero_false hu8
  wp_simp_pre [v2hs_ucWordsAt, arm64_norm, sepConj_assoc]
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 3348#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4660#64) _ _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · dsimp only [v2hs_ucWordsAt]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
  · wp_done

theorem v2hs_validate_err_auth_3348_to_4720_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4720#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hu8_ne := cap_add_one_beq_zero_false hu8
  wp_simp_pre [v2hs_ucWordsAt, noneCap, arm64_norm, sepConj_assoc]
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 3348#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4720#64) _ _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · dsimp only [v2hs_ucWordsAt, noneCap]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
  · wp_done

theorem v2hs_validate_ok_3348_3436_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w200 w216 w224 w232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hu32 : u32.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3436#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 736 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x8 = u72 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u48 ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        s2.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hu8_ne := cap_add_one_beq_zero_false hu8
  have hu32_ne := cap_add_one_beq_zero_false hu32
  have hmerge := v2hs_merge_240_656_80_736 (s0.sp - 2400#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  dsimp only [v2hs_ucWordsAt] at hmerge
  simp only [arm64_norm, sepConj_assoc] at hmerge
  wp_simp_pre [v2hs_ucWordsAt, arm64_norm, sepConj_assoc]
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 3348#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 3436#64) _ _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · simp only [arm64_norm]
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2160#64) 656 ∗
       (((s0.sp - 1504#64) ↦₆₄ u8) ∗
        ((s0.sp - 1496#64) ↦₆₄ u16) ∗
        ((s0.sp - 1488#64) ↦₆₄ u24) ∗
        ((s0.sp - 1480#64) ↦₆₄ u32) ∗
        ((s0.sp - 1472#64) ↦₆₄ u40) ∗
        ((s0.sp - 1464#64) ↦₆₄ u48) ∗
        ((s0.sp - 1456#64) ↦₆₄ u56) ∗
        ((s0.sp - 1448#64) ↦₆₄ u64) ∗
        ((s0.sp - 1440#64) ↦₆₄ u72) ∗
        ((s0.sp - 1432#64) ↦₆₄ u80))) ∗
      (((s0.sp - 2304#64) ↦₆₄ u24) ∗
       ((s0.sp - 2248#64) ↦₆₄ u8) ∗
       ((s0.sp - 2224#64) ↦₆₄ u16) ∗
       ((s0.sp - 2200#64) ↦₆₄ u48) ∗
       ((s0.sp - 2184#64) ↦₆₄ u40) ∗
       ((s0.sp - 2176#64) ↦₆₄ u80) ∗
       ((s0.sp - 2168#64) ↦₆₄ u72) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
  · wp_done

private theorem sepWPp_seq_clean_lscl [LibsignalPlacement]
    {prog : Program} {target_pc mid : BitVec 64} {s0 : State}
    {P P_mid : SepProp} {Q_regs : State → Prop}
    {post : State → SepProp → Prop} {onPanic : State → SepProp → Prop}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h1 : SepWP prog mid s0 P (fun s1 P1 => (P1 ⊢ P_mid) ∧ Q_regs s1))
    (h2 : ∀ s1, s1.pc = mid → s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem → Q_regs s1 →
      SepWPp prog target_pc s1 P_mid post onPanic) :
    SepWPp prog target_pc s0 P post onPanic :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl0
    (SepWP.mono h1 fun s1 _ hpc1 hrun1 ⟨hP1, hQ1⟩ hcl1 =>
      SepWPp.weaken_pre hP1 (h2 s1 hpc1 hrun1 hcl1 hQ1))

set_option maxHeartbeats 800000 in
theorem v2hs_auth_from_pb_step1_3436_8700_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (target_pc fsp out d_w0 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 333 + 3436#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = lsmpl.base 333 + 8700#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
       s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x21 = s.readReg64 .x21 ∧
       s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
       s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
       s1.readReg64 .x28 = u80 ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 216#64) ↦₆₄ u40) ∗
         vecCapPtrDealloc A u32 u40 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 216#64) ↦₆₄ u40) ∗
       vecU8Payload A u32 u40 auth.rootKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  rw [← ls_blockPlacement_base (i := 333)] at hpc hnext
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · refine sepWPp_seq_clean_lscl
      (mid := (blkPl_333).base + 8700#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        vecCapPtrDealloc A u32 u40 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) 1#64 auth.rootKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
        s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s1 s0)
      hcl ?_ (hnext 1#64)
    clear hnext; rw [hr_nil] at hx20 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
    change s.pc = (blkPl_333).base + 3436#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8700#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u32 u40 []
      have hn := v2hs_vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u32 u40 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hs_vecU8Payload_pos_unpack A u32 u40 auth.rootKey hr_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          (⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
            u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
           (A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
            memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
          u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
         A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
         memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩ => ?_
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hr_lay3 : auth.rootKey.length + 1 ≤ 2 ^ 63 := hr_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
      spqr_hook_ok_of_mem hA.shim
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
      spqr_hook_ok_of_mem hA.alloc
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrMemcpySym) sessionMemcpySpec :=
      spqr_hook_ok_of_mem hA.memcpy
    simp only [sessionMemcpySpec] at hmc
    have hpanic : ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
      fromPb_externAt?_handleError hA
    dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hA
    change s.pc = (blkPl_333).base + 3436#64 at hpc
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s _ _ _
    apply sepWPp_of_sepWP_lscl (mid := (blkPl_333).base + 3456#64) hcl
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl_sf1
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [v2hs_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [v2hs_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean_lscl (mid := (blkPl_333).base + 8700#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          vecCapPtrDealloc A u32 u40 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) (sf_1.readReg64 Reg.x0) auth.rootKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x21 = s.readReg64 .x21 ∧
          s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = sf_1.readReg64 Reg.x0 ∧
          s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
          s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = u80 ∧
          TraceCalleeSaved s1 s0)
        hcl_sf1 ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := v2hs_vecU8Payload_pos_dealloc A u32 u40 auth.rootKey hr_le hr_cap hptr0 hcap0_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.rootKey hr_pos hr_lt63 hoom0
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
           memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.rootKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.rootKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 216#64) ↦₆₄ u40) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

set_option maxHeartbeats 800000 in
theorem v2hs_auth_from_pb_step2_8700_8884_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (target_pc fsp out d_w0 pa1 w184 : BitVec 64)
    (u32 u56 u64 u72 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 333 + 8700#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = lsmpl.base 333 + 8884#64 →
      s2.status = .Running →
      LibsignalCodeLoaded lsmpl s2.mem →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
       s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x21 = s.readReg64 .x21 ∧
       s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
       s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
       s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
       TraceCalleeSaved s2 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s2
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 232#64) ↦₆₄ u72) ∗
         vecCapPtrDealloc A u56 u64 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗
       vecU8Payload A u56 u64 auth.macKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  rw [← ls_blockPlacement_base (i := 333)] at hpc hnext
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · refine sepWPp_seq_clean_lscl
      (mid := (blkPl_333).base + 8884#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ vecCapPtrDealloc A u56 u64 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) 1#64 auth.macKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
        s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0)
      hcl ?_ (hnext 1#64)
    clear hnext; subst hu72; rw [hm_nil]
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hpc ⊢
    change s.pc = (blkPl_333).base + 8700#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8884#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u56 u64 []
      have hn := v2hs_vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u56 u64 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        ((fsp + 232#64) ↦₆₄ 0#64) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · subst hu72
    refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hs_vecU8Payload_pos_unpack A u56 u64 auth.macKey hm_pos))))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          (⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
            u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
           (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
            memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
          u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
         ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hm_le, hm_cap, hptr1, hcap1_ne⟩ => ?_
    have hm_lt63 : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : auth.macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 auth.macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hm_lay3 : auth.macKey.length + 1 ≤ 2 ^ 63 := hm_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
      spqr_hook_ok_of_mem hA.shim
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
      spqr_hook_ok_of_mem hA.alloc
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrMemcpySym) sessionMemcpySpec :=
      spqr_hook_ok_of_mem hA.memcpy
    simp only [sessionMemcpySpec] at hmc
    have hpanic : ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
      fromPb_externAt?_handleError hA
    dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hA
    change s.pc = (blkPl_333).base + 8700#64 at hpc
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s _ _ _
    apply sepWPp_of_sepWP_lscl (mid := (blkPl_333).base + 8724#64) hcl
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl_sf1
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [v2hs_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [v2hs_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean_lscl (mid := (blkPl_333).base + 8884#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          vecCapPtrDealloc A u56 u64 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (sf_1.readReg64 Reg.x0) auth.macKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s2.readReg64 .x21 = s.readReg64 .x21 ∧
          s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
          s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
          s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
          TraceCalleeSaved s2 s0)
        hcl_sf1 ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := v2hs_vecU8Payload_pos_dealloc A u56 u64 auth.macKey hm_le hm_cap hptr1 hcap1_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.macKey hm_pos hm_lt63 hoom1
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
           memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.macKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.macKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

theorem v2hs_auth_from_pb_step3_8884_8944_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (out d_w0 pa1 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8944#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A u32 u40 ∗
        vecCapPtrDealloc A u56 u64 ∗
        A.pool ∗
        Rest)
      (fun s3 P3 =>
        (P3 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          A.pool ∗
          Rest) ∧
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = s.readReg64 .x21 ∧
        s3.readReg64 .x22 = d_w0 ∧
        s3.readReg64 .x23 = pa1 ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 auth.rootKey.length ∧
        s3.readReg64 .x26 = pa1 >>> 8 ∧
        s3.readReg64 .x27 = s.readReg64 .x27 ∧
        s3.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s3 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hr_lt63
  have hcmn : ¬((BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = true) :=
    cap_add_one_beq_zero_false hr_toNat
  have hdealloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem hA.dealloc
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  wp_simp_pre [arm64_norm, sepConj_assoc]
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 8912#64)
    (P_mid :=
      memRegion (s0.sp - 7552#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((s0.sp - 2184#64) ↦₆₄ u40) ∗
      ((s0.sp - 2176#64) ↦₆₄ u80) ∗
      vecCapPtrDealloc A u56 u64 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = s.readReg64 .x21 ∧
      s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = pa1 ∧
      s2.readReg64 .x24 = u56 ∧
      s2.readReg64 .x25 = u64 ∧
      s2.readReg64 .x26 = pa1 >>> 8 ∧
      s2.readReg64 .x27 = s.readReg64 .x27 ∧
      s2.readReg64 .x28 = u80 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 8884#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8912#64) _ _ _
    by_cases hc_r : (u32 == 0#64) = true <;>
      simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
    dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc2 ⊢
    change s2.pc = (blkPl_333).base + 8912#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8944#64) _ _ _
    by_cases hc_m : (u56 == 0#64) = true <;>
      simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
      · wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
      · wp_done

theorem v2hs_assemble_ekSent_8944_9032_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out d_w0 pa1 pa2 : BitVec 64)
    (u8 u16 u24 u48 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8944#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = pa1 >>> 8) (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (w0 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 9152#64
       else lsmpl.base 333 + 9036#64)
      s
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
          v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
          memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x9 = u24 ∧
        sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = u48 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = u80 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hpre_split :
      ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗ Rest ⊢
      (memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        (∃∗ e0 : BitVec 64, (s0.sp - 2400#64 + 1264#64) ↦₆₄ e0) ∗
        (∃∗ e1 : BitVec 64, (s0.sp - 2400#64 + 1272#64) ↦₆₄ e1) ∗
        (∃∗ e2 : BitVec 64, (s0.sp - 2400#64 + 1280#64) ↦₆₄ e2) ∗
        (∃∗ e3 : BitVec 64, (s0.sp - 2400#64 + 1288#64) ↦₆₄ e3) ∗
        (∃∗ e4 : BitVec 64, (s0.sp - 2400#64 + 1296#64) ↦₆₄ e4) ∗
        (∃∗ e5 : BitVec 64, (s0.sp - 2400#64 + 1304#64) ↦₆₄ e5) ∗
        (∃∗ e6 : BitVec 64, (s0.sp - 2400#64 + 1312#64) ↦₆₄ e6) ∗
        (∃∗ e7 : BitVec 64, (s0.sp - 2400#64 + 1320#64) ↦₆₄ e7) ∗
        (∃∗ e8 : BitVec 64, (s0.sp - 2400#64 + 1328#64) ↦₆₄ e8) ∗
        (∃∗ e9 : BitVec 64, (s0.sp - 2400#64 + 1336#64) ↦₆₄ e9) ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960) ∗
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        Rest) := by
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_left (v2hs_memRegion_1232_split_1264 (s0.sp - 2400#64)))
  refine SepWP.weaken_pre hpre_split ?_; clear hpre_split
  wp_simp_pre [v1_optProtoPolyEncoderWordsAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro e9
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e7
  apply ProofLib.SepWP.exists_left; intro e6
  apply ProofLib.SepWP.exists_left; intro e5
  apply ProofLib.SepWP.exists_left; intro e4
  apply ProofLib.SepWP.exists_left; intro e3
  apply ProofLib.SepWP.exists_left; intro e2
  apply ProofLib.SepWP.exists_left; intro e1
  apply ProofLib.SepWP.exists_left; intro e0
  rw [v10_pointsTo64_split_1_4_2_1 (s0.sp - 2400#64 + 1272#64) e1]
  wp_simp_pre [arm64_norm, sepConj_assoc]
  have hrec := v2hs_reconstruct_pa1 s0.sp pa1
  by_cases hw0 : (w0 + 1#64 == 0#64) = true <;>
    simp only [hw0, Bool.false_eq_true, ↓reduceIte]
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 8944#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9152#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, v2hs_ekSentWordsAt]
      simp only [arm64_norm]
      refine Entails.trans (Entails.of_eq (show _ =
        (((s0.sp - 1128#64) ↦₈ BitVec.zeroExtend 8 pa1) ∗
         ((s0.sp - 1127#64) ↦₃₂ BitVec.truncate 32 (pa1 >>> 8)) ∗
         ((s0.sp - 1123#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40))) ∗
         ((s0.sp - 1121#64) ↦₈ BitVec.zeroExtend 8 (pa1 >>> 56))) ∗
        (((s0.sp - 2304#64) ↦₆₄ u24) ∗ ((s0.sp - 2248#64) ↦₆₄ u8) ∗
         ((s0.sp - 2224#64) ↦₆₄ u16) ∗ ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
         ((s0.sp - 2168#64) ↦₆₄ u72) ∗ ((s0.sp - 1424#64) ↦₆₄ w0) ∗
         ((s0.sp - 1416#64) ↦₆₄ w8) ∗ ((s0.sp - 1408#64) ↦₆₄ w16) ∗
         ((s0.sp - 1400#64) ↦₆₄ w24) ∗ ((s0.sp - 1392#64) ↦₆₄ w32) ∗
         ((s0.sp - 1384#64) ↦₆₄ w40) ∗ ((s0.sp - 1376#64) ↦₆₄ w48) ∗
         memRegion (s0.sp - 1328#64) 192 ∗ ((s0.sp - 1136#64) ↦₆₄ u48) ∗
         ((s0.sp - 1120#64) ↦₆₄ u48) ∗ ((s0.sp - 1112#64) ↦₆₄ u72) ∗
         ((s0.sp - 1104#64) ↦₆₄ pa2) ∗ ((s0.sp - 1096#64) ↦₆₄ u72) ∗
         ((s0.sp - 1088#64) ↦₆₄ u8) ∗ ((s0.sp - 1080#64) ↦₆₄ u16) ∗
         ((s0.sp - 1072#64) ↦₆₄ u24) ∗ ((s0.sp - 1064#64) ↦₆₄ u80) ∗
         memRegion (s0.sp - 1056#64) 960 ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hrec) (Entails.of_eq (by ac_rfl))
    · wp_done
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 8944#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9036#64) _ _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, v2hs_ekSentWordsAt]
      simp only [arm64_norm]
      refine Entails.trans (Entails.of_eq (show _ =
        (((s0.sp - 1128#64) ↦₈ BitVec.zeroExtend 8 pa1) ∗
         ((s0.sp - 1127#64) ↦₃₂ BitVec.truncate 32 (pa1 >>> 8)) ∗
         ((s0.sp - 1123#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40))) ∗
         ((s0.sp - 1121#64) ↦₈ BitVec.zeroExtend 8 (pa1 >>> 56))) ∗
        (((s0.sp - 2304#64) ↦₆₄ u24) ∗ ((s0.sp - 2248#64) ↦₆₄ u8) ∗
         ((s0.sp - 2224#64) ↦₆₄ u16) ∗ ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
         ((s0.sp - 2168#64) ↦₆₄ u72) ∗ ((s0.sp - 1424#64) ↦₆₄ w0) ∗
         ((s0.sp - 1416#64) ↦₆₄ w8) ∗ ((s0.sp - 1408#64) ↦₆₄ w16) ∗
         ((s0.sp - 1400#64) ↦₆₄ w24) ∗ ((s0.sp - 1392#64) ↦₆₄ w32) ∗
         ((s0.sp - 1384#64) ↦₆₄ w40) ∗ ((s0.sp - 1376#64) ↦₆₄ w48) ∗
         memRegion (s0.sp - 1328#64) 192 ∗ ((s0.sp - 1136#64) ↦₆₄ u48) ∗
         ((s0.sp - 1120#64) ↦₆₄ u48) ∗ ((s0.sp - 1112#64) ↦₆₄ u72) ∗
         ((s0.sp - 1104#64) ↦₆₄ pa2) ∗ ((s0.sp - 1096#64) ↦₆₄ u72) ∗
         ((s0.sp - 1088#64) ↦₆₄ u8) ∗ ((s0.sp - 1080#64) ↦₆₄ u16) ∗
         ((s0.sp - 1072#64) ↦₆₄ u24) ∗ ((s0.sp - 1064#64) ↦₆₄ u80) ∗
         memRegion (s0.sp - 1056#64) 960 ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hrec) (Entails.of_eq (by ac_rfl))
    · wp_done

end CryptoVerification.SpqrV1.States.FromPb
