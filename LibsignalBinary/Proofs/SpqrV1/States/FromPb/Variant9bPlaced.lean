/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) — Part B

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant9b.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9bPlaced

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
  v9_zext_loByte_extract8 v9_zext_loByte_setWidth8

/-! ## 1. Block 1 (`+444 -> +2768 | +488`) -/

/-- Block 1 (`+444 -> +2768`) when `receivingEk = none` (`w0 = noneCap`). -/
theorem v9_states_from_pb_step_444_to_2768_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 444#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = noneCap ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  rw [v9_optProtoUcWordsAt_pbA8_split16, v9_optProtoPolyDecoderWordsAt_pbA136_eq]
  simp only [sepConj_assoc]
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  change s.pc = (blkPl_333).base + 444#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2768#64) s _ _
  wp_steps
  wp_done

/-- Block 1 (`+444 -> +2768`) when `receivingEk = some d` (`w0.toNat * 24 < 2^63` and `d24 = 576#32`). -/
theorem v9_states_from_pb_step_444_to_2768_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 444#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x10 = (576#32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  have hw0_ne := cap_add_one_beq_zero_false hw0_lt
  rw [v9_optProtoUcWordsAt_pbA8_split16, v9_optProtoPolyDecoderWordsAt_pbA136_eq]
  simp only [sepConj_assoc]
  change s.pc = (blkPl_333).base + 444#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2768#64) s _ _
  wp_steps
  wp_done

/-- Block 1 (`+444 -> +488`) when `receivingEk = some d` with `d24 ≠ 576#32`. -/
theorem v9_states_from_pb_step_444_to_488_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hd24_ne : d24 ≠ 576#32)
    (hpc : s.pc = lsmpl.base 333 + 444#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 488#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hw0_ne := cap_add_one_beq_zero_false hw0_lt
  have hd24_sub_ne : ¬((d24.zeroExtend 64).extractLsb' 0 32 - 576#32 == 0#32) = true := by
    rw [beq_iff_eq]
    intro heq
    apply hd24_ne
    have h1 : (d24.zeroExtend 64).extractLsb' 0 32 = d24 := by bv_kernel
    rw [h1] at heq
    bv_omega
  rw [v9_optProtoUcWordsAt_pbA8_split16, v9_optProtoPolyDecoderWordsAt_pbA136_eq]
  simp only [sepConj_assoc]
  change s.pc = (blkPl_333).base + 444#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 488#64) s _ _
  wp_steps
  wp_done

/-! ## 2. Block 2 (`+2768 -> lsmpl.base 339`) & Block 3 (`+2864 -> +5360`) -/

/-- Block 2 (`+2768 -> lsmpl.base 339`, 24 instructions including `bl` to `<Ct1Sent>::from_pb`):
copies the 128-byte `ProtoUnchunkedCt1Sent` from `pbA + 8..136` to `fsp + 1392..1520`
and calls `<Unchunked::SendCt::Ct1Sent>::from_pb` (Block `339`) with `x0 = fsp + 1888`, `x1 = fsp + 1392`,
and `x30 = lsmpl.base 333 + 2864`. -/
theorem v9_states_from_pb_copy_uc_to_call_2768_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 w32 : BitVec 64)
    (z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472 z1480 z1488 z1496 z1504 z1512 : BitVec 64)
    (b1400 : BitVec 8)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hu0_lt : u0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = u0)
    (hx9 : s.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = w8)
    (hx21 : s.readReg64 .x21 = w0)
    (hx22 : s.readReg64 .x22 = w16)
    (hx23 : s.readReg64 .x23 = w32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 339) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        ((fsp + 1392#64) ↦₆₄ z1392) ∗
        ((fsp + 1400#64) ↦₈ b1400) ∗
        ((fsp + 1401#64) ↦₆₄ z1401) ∗
        ((fsp + 1409#64) ↦₆₄ z1409) ∗
        ((fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 z1417) ∗
        ((fsp + 1424#64) ↦₆₄ z1424) ∗
        ((fsp + 1432#64) ↦₆₄ z1432) ∗
        ((fsp + 1440#64) ↦₆₄ z1440) ∗
        ((fsp + 1448#64) ↦₆₄ z1448) ∗
        ((fsp + 1456#64) ↦₆₄ z1456) ∗
        ((fsp + 1464#64) ↦₆₄ z1464) ∗
        ((fsp + 1472#64) ↦₆₄ z1472) ∗
        ((fsp + 1480#64) ↦₆₄ z1480) ∗
        ((fsp + 1488#64) ↦₆₄ z1488) ∗
        ((fsp + 1496#64) ↦₆₄ z1496) ∗
        ((fsp + 1504#64) ↦₆₄ z1504) ∗
        ((fsp + 1512#64) ↦₆₄ z1512) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 2864#64 ∧
        TraceCalleeSaved sm s0) := by
  subst hsp
  have hu0_ne := cap_add_one_beq_zero_false hu0_lt
  rw [v9_optProtoUcWordsAt_pbA8_eq, v9_optProtoUcWordsAt_fsp1392_eq]
  simp only [sepConj_assoc]
  change s.pc = (blkPl_333).base + 2768#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 339) s _ _
  iterate 18 wp_step
  wp_simp_pre only [v9_pbA_16_realign_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v9_fsp_1409_realign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre only [v9_pbA_16_unrealign_rest, v9_fsp_1400_realign_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  dsimp only [blkPl_333, Obj.MultiPlacedLib.blockPlacement]
  wp_done

/-- Error branch after `ct1SentFromPb` (`+2864..+2884 -> +5356 -> +5360`):
    when `[fsp + 1888] = noneCap`, loads `x28 = w1896` and jumps to `+5360`. -/
theorem v9_step_2864_err_to_5360_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64)
    (w1896 w1904 w1912 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2864#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5360#64) s
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗
        ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗
        ((fsp + 1912#64) ↦₆₄ w1912) ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗
          ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗
          ((fsp + 1912#64) ↦₆₄ w1912) ∗
          Frame) ∧
        v9_Saved5368Preserved s0 s' fsp out ptsPtr ptsCap w1896 ∧
        s'.readReg64 .x22 = ptsLen) := by
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  change s.pc = (blkPl_333).base + 2864#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5360#64) s _ _
  wp_steps
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9bPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9bPlaced (
  v9_states_from_pb_step_444_to_2768_none_placed
  v9_states_from_pb_step_444_to_2768_some_placed
  v9_states_from_pb_step_444_to_488_err_placed
  v9_states_from_pb_copy_uc_to_call_2768_placed
  v9_step_2864_err_to_5360_placed
)

end CryptoVerification.SpqrV1.States.FromPb
