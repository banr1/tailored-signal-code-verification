/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 1 (`KeysSampled`, `+1104`) — Part D

Relocatable Block-`333` `sendingHdr` dispatch and stack staging (`+4016 -> +5860 | +4096`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlaced

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
open CryptoVerification.CodeLayout

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1c_bv_add_add_lit v1c_bv_sub_sub_lit
  v1d_bv_add_add_lit v1_bfm_pa1 v1_x23_add_57 v1_x23_add_57_sext
  v1_x25_sub_887 v1_x25_add_96 v1_pbA_add_121 v1_pbA_144_add_8
  v1_pbA_121_add_8 v1_fsp_928_add_8 v1_fsp_905_add_8

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bfm_pa1_comm (pa1 : BitVec 64) :
    (255#64 &&& BitVec.zeroExtend 64 (BitVec.truncate 32 pa1) |||
      (72057594037927935#64 &&& pa1 >>> 8) <<< 8) = pa1 := by
  bv_kernel

/-! ## `sendingHdr` Check at `+4016` (`None -> +5860`, `Some -> +4096`) -/

/-- At `+4016`, when `s.sendingHdr = none` (`[fsp + 1496] = noneCap`), reconstructs `x0 := pa1`
    and branches at `+4032` (`b.eq +5860`) to `+5860`. -/
theorem v1_sendingHdr_none_4016_5860_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pa1 u8 u32 u72 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5860#64) s
      (((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = pa1 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  change s.pc = (blkPl_333).base + 4016#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5860#64) s _ _
  wp_steps
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- At `+4016`, when `s.sendingHdr = some pbEnc` (`w0.toNat < 2 ^ 63`), copies the 56-byte
    `ProtoPolynomialEncoder` from `pbA + 112..168` to `fsp + 896..952`, stores `pa1` at
    `[fsp + 200]`, sets `x0 = fsp + 1888, x1 = fsp + 896, x23 = fsp + 848`, and reaches `+4096`
    (`bl <PolyEncoder>::from_pb`). -/
theorem v1_sendingHdr_some_copy_4016_4096_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA pa1 v200 u8 u32 u72 : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0 : w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4096#64) s
      (((fsp + 200#64) ↦₆₄ v200) ∗
        memRegion (fsp + 896#64) 56 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 200#64) ↦₆₄ pa1) ∗
          protoPolynomialEncoderAt A (fsp + 896#64) pbEnc ∗
          memRegion (fsp + 1496#64) 56 ∗
          memRegion (pbA + 112#64) 56 ∗
          Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = fsp + 1888#64 ∧
        s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  subst hsp
  have hcmn : (w0 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw0)
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (v1_memRegion_896_56_split s.sp))) ?_
  dsimp only [v1_optProtoPolyEncoderWordsAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [pointsTo64_split_1_7 (s.sp + 1504#64) w8]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, pointsTo128, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d48
  apply ProofLib.SepWP.exists_left; intro q32
  apply ProofLib.SepWP.exists_left; intro d24
  apply ProofLib.SepWP.exists_left; intro d16
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d0
  change s.pc = (blkPl_333).base + 4016#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4096#64) s _ _
  wp_conv_pre =>
    rw [v1_fsp_904_triple_rest s.sp d8 d16 d24,
        v1_pbA_120_triple_rest pbA w8 w16 w24]
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [← v1_pbA_120_triple_rest pbA w8 w16 w24]
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v1_fsp_913_realign_rest s.sp _ d24]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hdst := v1_dst24_realign_final (s.sp + 904#64) w8 w16 w24
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdst
    have hfsp1504 : ((s.sp + 1504#64) ↦₈ loByte w8) ∗ ((s.sp + 1505#64) ↦ₛ EncoderFromPb.hiBytes7 w8) =
        ((s.sp + 1504#64) ↦₆₄ w8) := by
      have h := (pointsTo64_split_1_7 (s.sp + 1504#64) w8).symm
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
    have hpack := v1_optProtoPolyEncoderAt_pack_some A (s.sp + 896#64) pbEnc w0 w8 w16 w24 w32 w40 w48
    have hm1496 := v1_optProtoPolyEncoderWordsAt_entails_56 (s.sp + 1496#64) w0 w8 w16 w24 w32 w40 w48
    have hm112 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48
    dsimp only [v1_optProtoPolyEncoderWordsAt] at hpack hm1496 hm112
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack hm1496 hm112
    refine Entails.trans (Entails.of_eq (show _ =
      ((s.sp + 200#64) ↦₆₄ pa1) ∗
      (((s.sp + 896#64) ↦₆₄ w0) ∗
       (((s.sp + 904#64) ↦₈ loByte w8) ∗
        ((s.sp + 905#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
        ((s.sp + 913#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
        ((s.sp + 920#64) ↦₆₄ w24)) ∗
       ((s.sp + 928#64) ↦₆₄ w32) ∗
       ((s.sp + 936#64) ↦₆₄ w40) ∗
       ((s.sp + 944#64) ↦₆₄ w48) ∗
       v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
      (((s.sp + 1496#64) ↦₆₄ w0) ∗
       (((s.sp + 1504#64) ↦₈ loByte w8) ∗ ((s.sp + 1505#64) ↦ₛ EncoderFromPb.hiBytes7 w8)) ∗
       ((s.sp + 1512#64) ↦₆₄ w16) ∗
       ((s.sp + 1520#64) ↦₆₄ w24) ∗
       ((s.sp + 1528#64) ↦₆₄ w32) ∗
       ((s.sp + 1536#64) ↦₆₄ w40) ∗
       ((s.sp + 1544#64) ↦₆₄ w48)) ∗
      (((pbA + 112#64) ↦₆₄ w0) ∗
       ((pbA + 120#64) ↦₆₄ w8) ∗
       ((pbA + 128#64) ↦₆₄ w16) ∗
       ((pbA + 136#64) ↦₆₄ w24) ∗
       ((pbA + 144#64) ↦₆₄ w32) ∗
       ((pbA + 152#64) ↦₆₄ w40) ∗
       ((pbA + 160#64) ↦₆₄ w48)) ∗
      Rest by ac_rfl)) ?_
    rw [hdst, hfsp1504]
    have h896 : ((s.sp + 896#64) ↦₆₄ w0) ∗
        (((s.sp + 904#64) ↦₆₄ w8) ∗ ((s.sp + 912#64) ↦₆₄ w16) ∗ ((s.sp + 920#64) ↦₆₄ w24)) ∗
        ((s.sp + 928#64) ↦₆₄ w32) ∗
        ((s.sp + 936#64) ↦₆₄ w40) ∗
        ((s.sp + 944#64) ↦₆₄ w48) ∗
        v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 =
        (((s.sp + 896#64) ↦₆₄ w0) ∗ ((s.sp + 904#64) ↦₆₄ w8) ∗ ((s.sp + 912#64) ↦₆₄ w16) ∗
         ((s.sp + 920#64) ↦₆₄ w24) ∗ ((s.sp + 928#64) ↦₆₄ w32) ∗
         ((s.sp + 936#64) ↦₆₄ w40) ∗ ((s.sp + 944#64) ↦₆₄ w48)) ∗
        v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 := by ac_rfl
    rw [h896]
    exact sepConj_mono_right (sepConj_mono hpack (sepConj_mono hm1496 (sepConj_mono_left hm112)))
  · wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlaced (
  v1_sendingHdr_none_4016_5860_placed
  v1_sendingHdr_some_copy_4016_4096_placed
)

end CryptoVerification.SpqrV1.States.FromPb
