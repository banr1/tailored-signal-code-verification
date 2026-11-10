/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part D

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant6d.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6dPlaced

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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
  v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt
  v6hr_stackRest10000 v6hr_decHeap
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit
  v6hr_bv_add_lit_add_lit
  v6hr_overlapWord7_unshift v6hr_overlapWord7_midQ128_lsr8
  v6hr_orr_x27_w8 v6hr_w8_d97 v6hr_w8_h101 v6hr_w8_b103 v6hr_zext32_setWidth8
  v6hr_fsp_1888_add_9 v6hr_fsp_1888_add_13 v6hr_fsp_1888_add_33 v6hr_fsp_1888_add_57
  v6hr_fsp_848_add_39 v6hr_fsp_848_add_15

/-! ## Step `+10000 -> +8180` (77 instructions) -/

set_option maxHeartbeats 1600000 in
theorem v6hr_step_10000_ok_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out c0 p0 l0 l1 p1_new l2 p2_new ep : BitVec 64)
    (dw : v6hr_DecWords)
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u224 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u888 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : dw.g0.w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10000#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = p1_new)
    (hx26 : s.readReg64 .x26 = l1)
    (hx27 : s.readReg64 .x27 = c0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 80#64) ↦₆₄ l0) ∗
        ((fsp + 128#64) ↦₆₄ ep) ∗
        ((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 144#64) ↦₆₄ p0) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        v6hr_stagingSlotsPre fsp u160 d172 u208 u224 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u888 ∗
        v6hr_decWordsAt (fsp + 1888#64) dw ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 80#64) ↦₆₄ l0) ∗
          ((fsp + 128#64) ↦₆₄ ep) ∗
          ((fsp + 136#64) ↦₆₄ p2_new) ∗
          ((fsp + 144#64) ↦₆₄ p0) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗
          v6hr_stagingSlotsPost fsp dw p1_new ∗
          v6hr_decWordsAt (fsp + 1888#64) dw ∗
          Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧
        s2.readReg64 .x8 = 8#64 ∧
        s2.readReg64 .x15 = l1 ∧
        s2.readReg64 .x20 = l1 ∧
        s2.readReg64 .x13 = l2 ∧
        s2.readReg64 .x25 = p2_new ∧
        s2.readReg64 .x30 = l2 ∧
        s2.readReg64 .x9 = c0 ∧
        s2.readReg64 .x14 = p0 ∧
        s2.readReg64 .x18 = l0 ∧
        s2.readReg64 .x17 = ep ∧
        s2.readReg64 .x0 = dw.g0.w0 ∧
        (s2.readReg32 .x3).setWidth 8 = dw.g0.w8.extractLsb' 0 8 ∧
        s2.readReg32 .x27 = dw.g0.w8.extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = dw.g0.w8.extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = dw.g0.w8.extractLsb' 56 8 ∧
        s2.readReg64 .x4 = dw.g0.w16 ∧
        s2.readReg64 .x5 = dw.g0.w24 ∧
        (s2.readReg32 .x21).setWidth 8 = EncoderFromPb.loByte dw.g0.w32 ∧
        s2.readReg64 .x7 = dw.g0.w48 ∧
        s2.readReg64 .x2 = dw.g3.u312 ∧
        s2.readReg64 .x11 = dw.g3.u320 ∧
        s2.readReg64 .x22 = dw.g3.u328 ∧
        s2.readReg64 .x24 = dw.g3.u336 ∧
        s2.readReg64 .x10 = dw.g4.u352 ∧
        s2.readReg64 .x26 = dw.g4.u368 ∧
        s2.readReg64 .x12 = dw.g4.u376 ∧
        s2.readReg64 .x1 = dw.g4.u384 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0) := by
  subst hsp
  have hw0_ne1 := v6hr_cap_add_one_beq_zero_false hw0_lt
  unfold v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt
  simp only [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  change s.pc = (blkPl_333).base + 10000#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8180#64) s _ _
  wp_simp_pre only [v6hr_fsp_1896_split_rest, v6hr_fsp_1920_realign_rest,
    v6hr_fsp_1944_realign_rest, sepConj_assoc]
  iterate 13 wp_step
  wp_simp_pre only [v6hr_fsp_1920_unrealign_rest, v6hr_fsp_1920_split_1_7_rest,
    v6hr_fsp_880_realign_rest, sepConj_assoc]
  iterate 18 wp_step
  wp_simp_pre only [v6hr_fsp_1944_unrealign_rest, v6hr_fsp_1944_split_1_7_rest,
    v6hr_fsp_856_realign_rest, sepConj_assoc]
  iterate 46 wp_step
  wp_simp_pre only [v6hr_fsp_856_unrealign_midQ128_rest, v6hr_fsp_880_unrealign_unshift_rest,
    v6hr_fsp_1896_unsplit_rest, v6hr_fsp_1920_unsplit_1_7_rest,
    v6hr_fsp_1944_unsplit_1_7_rest, sepConj_assoc]
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6dPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6dPlaced
  (v6hr_step_10000_ok_to_8180_placed)

end CryptoVerification.SpqrV1.States.FromPb
