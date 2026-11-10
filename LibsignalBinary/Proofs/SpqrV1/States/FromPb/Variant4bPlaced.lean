/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 4 (`EkSentCt1Received`, `+248`) — Part B

Relocatable Block-`333` straight-line branches at `+248`, `+2228`, and `+2308`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
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
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-- Entry loads at `+248..+292 -> +2228` when `d0 = noneCap` (`receivingCt2 = none`). -/
theorem v4b_step_248_none_to_2228_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2228#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
          Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = noneCap ∧
        TraceCalleeSaved s' s) := by
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 248#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2228#64) _ _ _
  dsimp only [noneCap] at hpc ⊢
  simp only [v4b_optProtoUcWordsAt, v4b_optProtoPolyDecoderWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Branch at `+2228 -> +4364 -> +5264` when `x22 = noneCap` (`uc = none`). -/
theorem v4b_step_2228_none_to_5264_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 2228#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = noneCap) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5264#64) s
      Frame
      (fun s' P' =>
        (P' ⊢ Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧
        s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x26 = 0#64 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s' s) := by
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 2228#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5264#64) _ _ _
  dsimp only [noneCap] at hpc hx22 ⊢
  wp_steps
  wp_done

/-- Entry loads at `+248..+300 -> +2228` when `d0.toNat < 2^63` and `d24 = 80#32`. -/
theorem v4b_step_248_some_eq_to_2228_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2228#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
          Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = 80#64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  have hd0_ne := cap_add_one_beq_zero_false hd0_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 248#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2228#64) _ _ _
  simp only [v4b_optProtoUcWordsAt, v4b_optProtoPolyDecoderWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Entry loads at `+248..+300 -> +304` when `d0.toNat < 2^63` and `d24 ≠ 80#32`. -/
theorem v4b_step_248_some_ne_to_304_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hd24_ne : d24 ≠ 80#32)
    (hpc : s.pc = lsmpl.base 333 + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 304#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
          Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  have hd0_ne := cap_add_one_beq_zero_false hd0_lt
  have hd24_f := v4b_ptsNeeded_sub_80_beq_zero_false hd24_ne
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 248#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 304#64) _ _ _
  simp only [v4b_optProtoUcWordsAt, v4b_optProtoPolyDecoderWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Copy `uc` words to `fsp + 1392..1496`, spill `d32, d28` to `fsp + 224..236`,
    and branch-with-link at `+2228..+2304 -> lsmpl.base 348` (`ekSentCt1ReceivedFromPb`). -/
theorem v4b_step_2228_some_to_18368_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp pbA out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u : BitVec 64)
    (v224 : BitVec 64) (v232 : BitVec 32)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hu0_lt : u0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u56)
    (hx1 : s.readReg64 .x1 = u48)
    (hx8 : s.readReg64 .x8 = u16)
    (hx9 : s.readReg64 .x9 = u40)
    (hx10 : s.readReg64 .x10 = u64)
    (hx11 : s.readReg64 .x11 = u8)
    (hx12 : s.readReg64 .x12 = u32)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx14 : s.readReg64 .x14 = d28.zeroExtend 64)
    (hx15 : s.readReg64 .x15 = d32)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx21 : s.readReg64 .x21 = u24)
    (hx22 : s.readReg64 .x22 = u0)
    (hx23 : s.readReg64 .x23 = d24.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = d8)
    (hx25 : s.readReg64 .x25 = u80)
    (hx26 : s.readReg64 .x26 = u72)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 348) s
      (((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
        ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 232#64) ↦₃₂ v232) ∗
        v4b_optProtoUcWordsAt (fsp + 1392#64)
          s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
          v4b_optProtoUcWordsAt (fsp + 1392#64)
            u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = fsp + 1888#64 ∧
        s'.readReg64 .x1 = fsp + 1392#64 ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        s'.readReg64 .x30 = (blkPl_333).base + 2308#64 ∧
        TraceCalleeSaved s' s) := by
  have hu0_ne := cap_add_one_beq_zero_false hu0_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc
  change s.pc = (blkPl_333).base + 2228#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 348) _ _ _
  simp only [v4b_optProtoUcWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Error branch after `ekSentCt1ReceivedFromPb` (`+2308..+2328 -> +5260 -> +5264`):
    when `[fsp + 1888] = noneCap`, loads `x26 = w1896` and jumps to `+5264`. -/
theorem v4b_step_2308_err_to_5264_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out d0 d8 d16 : BitVec 64) (d28 : BitVec 32)
    (w1896 w1904 w1912 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5264#64) s
      (((fsp + 232#64) ↦₃₂ d28) ∗
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗
        ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗
        ((fsp + 1912#64) ↦₆₄ w1912) ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((fsp + 232#64) ↦₃₂ d28) ∗
          ((fsp + 1888#64) ↦₆₄ noneCap) ∗
          ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗
          ((fsp + 1912#64) ↦₆₄ w1912) ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x26 = w1896 ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 2308#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5264#64) _ _ _
  dsimp only [noneCap] at hpc ⊢
  wp_steps
  wp_done

/-- `Ok(uc)` followed by `receivingCt2 = none` (`x28 = noneCap`) at `+2308..+2368 -> +6860`:
    loads `uc` fields and branches to `+6860` (`v4_states_from_pb_drop_uc_6860_placed`). -/
theorem v4b_step_2308_ok_none_to_6860_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (v72 v128 v144 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = noneCap) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6860#64) s
      (((fsp + 72#64) ↦₆₄ v72) ∗
        ((fsp + 128#64) ↦₆₄ v128) ∗
        ((fsp + 144#64) ↦₆₄ v144) ∗
        v4b_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          v4b_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = mkPtr ∧
        s'.readReg64 .x1 = mkCap ∧
        s'.readReg64 .x9 = rkCap ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x26 = rkPtr ∧
        TraceCalleeSaved s' s) := by
  have hrk_ne := cap_add_one_beq_zero_false hrk_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 2308#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6860#64) _ _ _
  dsimp only [noneCap] at hpc hx28 ⊢
  simp only [v4b_optProtoUcWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v4b_step_248_none_to_2228_placed
  v4b_step_2228_none_to_5264_placed
  v4b_step_248_some_eq_to_2228_placed
  v4b_step_248_some_ne_to_304_placed
  v4b_step_2228_some_to_18368_placed
  v4b_step_2308_err_to_5264_placed
  v4b_step_2308_ok_none_to_6860_placed)
end CryptoVerification.SpqrV1.States.FromPb
