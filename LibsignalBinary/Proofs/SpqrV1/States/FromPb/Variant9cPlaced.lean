/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9c
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) — Part C

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant9c.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9cPlaced

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
  v9_bv_add_add_lit v9_lsr8_lsl8 v9_unshift_lsr56
  v9_overlapWord7_unshift_lsr8 v9_overlapWord7_midQ128_lsr8
  v9_overlapLow7_unshift v9_zext32_setWidth8
  v9_lsr8_d97 v9_lsr8_h101 v9_lsr8_b103 v9_w_setWidth8_eq_extract0
  v9_x25_add_209 v9_x25_add_209_sext v9_pbA_add_145
  v9_x21_add_57 v9_x21_add_57_sext v9_x24_add_9 v9_x24_add_9_sext
  v9_x21_add_15 v9_x21_add_15_sext v9_x21_add_39 v9_x21_add_39_sext
  v9_fsp_add_247_sext

/-! ## 1. Stepping `+2864 -> +6904` when `receivingEk = none` -/

/-- At `+2864`, when `ct1SentFromPb` returned `Ok(uc)` (`rkCap.toNat < 2 ^ 63`) and
    `receivingEk = none` (`x21 = noneCap`), spills `hdr`, `es`, `ct1Len`, and `uc.epoch`
    and branches at `+2968` (`b.eq +6904`) to `+6904`. -/
theorem v9_step_2864_ok_none_to_6904_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w72 w128 w144 w152 w240 w248 : BitVec 64) (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = noneCap) (hx25 : s.readReg64 .x25 = fsp + 1792#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6904#64) s
      (((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ ((fsp + 128#64) ↦₆₄ w128) ∗
        ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
        ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
        v9_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗ memRegion (fsp + 1888#64) 128 ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = mkPtr ∧ s1.readReg64 .x1 = mkCap ∧
        s1.readReg64 .x10 = rkCap ∧ s1.readReg64 .x13 = ct1Cap ∧ s1.readReg64 .x14 = ct1Ptr ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) := by
  subst hsp
  have hrk_ne : (rkCap + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hrk_lt)
  dsimp only [v9_optProtoUcWordsAt, noneCap] at hx21 ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  change s.pc = (blkPl_333).base + 2864#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6904#64) s _ _
  iterate 21 wp_step
  wp_conv_pre => rw [v9_fsp_2000_realign_rest s.sp ct1Len ep]
  wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v9_fsp_240_realign_64_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) w248,
        v9_fsp_2000_unrealign_rest s.sp ct1Len ep]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm1888 := v9_optProtoUcWordsAt_entails_128 (s.sp + 1888#64)
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
    dsimp only [v9_optProtoUcWordsAt] at hm1888
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1888
    refine Entails.trans (Entails.of_eq (show _ =
      ((s.sp + 72#64) ↦₆₄ esPtr) ∗ ((s.sp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
      ((s.sp + 128#64) ↦₆₄ esCap) ∗ ((s.sp + 144#64) ↦₆₄ hdrPtr) ∗ ((s.sp + 152#64) ↦₆₄ hdrCap) ∗
      ((s.sp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
      ((s.sp + 247#64) ↦₆₄ ep) ∗
      (((s.sp + 1888#64) ↦₆₄ rkCap) ∗ ((s.sp + 1896#64) ↦₆₄ rkPtr) ∗ ((s.sp + 1904#64) ↦₆₄ rkLen) ∗
       ((s.sp + 1912#64) ↦₆₄ mkCap) ∗ ((s.sp + 1920#64) ↦₆₄ mkPtr) ∗ ((s.sp + 1928#64) ↦₆₄ mkLen) ∗
       ((s.sp + 1936#64) ↦₆₄ hdrCap) ∗ ((s.sp + 1944#64) ↦₆₄ hdrPtr) ∗ ((s.sp + 1952#64) ↦₆₄ hdrLen) ∗
       ((s.sp + 1960#64) ↦₆₄ esCap) ∗ ((s.sp + 1968#64) ↦₆₄ esPtr) ∗ ((s.sp + 1976#64) ↦₆₄ esLen) ∗
       ((s.sp + 1984#64) ↦₆₄ ct1Cap) ∗ ((s.sp + 1992#64) ↦₆₄ ct1Ptr) ∗ ((s.sp + 2000#64) ↦₆₄ ct1Len) ∗
       ((s.sp + 2008#64) ↦₆₄ ep)) ∗ Rest by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm1888)))))))
  · wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9cPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9cPlaced (
  v9_step_2864_ok_none_to_6904_placed
)

end CryptoVerification.SpqrV1.States.FromPb
