/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Relocatable Variant 10 (`Ct2Sampled`, `+1632`) — Encoder Dispatch

Relocatable `[LibsignalPlacement]` Block `333` steps for Variant 10 (`Ct2Sampled`): `+1632 -> +1720`
field loads, `+5728 -> +7212` (`sending_ct2 = none`), `+5728 -> lsmpl.base 374` (`<PolyEncoder>::from_pb`
call), and post-call `+5808 -> +5820` (`Err`) / `+5808 -> +7904` (`Ok`) branches.
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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local arm64_norm, local wp_norm]
  v10_reconstruct_p1
  v10_fsp_1264_add_137
  v10_fsp_1401_add_8
  v10_fsp_1424_add_8
  v10_pbA_17_add_8
  v10_pbA_40_add_8
  v10_extract_loByte_zext

/-- Subroutine contract for `<PolyEncoder>::from_pb` (Block `374`) on `lsProg_333`. -/
theorem v10_sub_ok_encoder_from_pb_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hEnc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec A)) :=
  hEnc

/-! ## 1. `+1632 -> +1720`: Loading `Authenticator` PB and `epoch` -/

/-- Steps `+1632 -> +1720` when `uc = some { auth := some authPb, epoch := ep }`:
loads `cap_enc = [pbA + 8]`, `b16 = [pbA + 16]`, `c1, p1, l1, c2, p2, l2` from `pbA + 64..112`,
and `ep = [pbA + 112]`, storing `ep` at `[sp + 152]`, `l1` at `[sp + 200]`, `b16.zeroExtend 32` at
`[sp + 224]`, and `p2` at `[sp + 232]`. -/
theorem v10_ct2Sent_load_1632_to_1720_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA cap_enc c1 p1 l1 c2 p2 l2 ep v152 v200 v232 : BitVec 64)
    (b16 : BitVec 8) (v224 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1720#64) s1
      (((pbA + 8#64) ↦₆₄ cap_enc) ∗
        ((pbA + 16#64) ↦₈ b16) ∗
        ((pbA + 64#64) ↦₆₄ c1) ∗
        ((pbA + 72#64) ↦₆₄ p1) ∗
        ((pbA + 80#64) ↦₆₄ l1) ∗
        ((pbA + 88#64) ↦₆₄ c2) ∗
        ((pbA + 96#64) ↦₆₄ p2) ∗
        ((pbA + 104#64) ↦₆₄ l2) ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗
        (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((pbA + 8#64) ↦₆₄ cap_enc) ∗
          ((pbA + 16#64) ↦₈ b16) ∗
          ((pbA + 64#64) ↦₆₄ c1) ∗
          ((pbA + 72#64) ↦₆₄ p1) ∗
          ((pbA + 80#64) ↦₆₄ l1) ∗
          ((pbA + 88#64) ↦₆₄ c2) ∗
          ((pbA + 96#64) ↦₆₄ p2) ∗
          ((pbA + 104#64) ↦₆₄ l2) ∗
          ((pbA + 112#64) ↦₆₄ ep) ∗
          (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = l1 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hc1_ne2 := v10_cap_add_two_beq_zero_false hc1_lt
  have hc1_ne1 := v10_cap_add_one_beq_zero_false hc1_lt
  have hp1_split := v10_pointsTo64_split_1_4_2_1 (pbA + 72#64) p1
  have ha73 : (pbA + 72#64) + 1#64 = pbA + 73#64 := by bv_omega
  have ha77 : (pbA + 72#64) + 5#64 = pbA + 77#64 := by bv_omega
  have ha79 : (pbA + 72#64) + 7#64 = pbA + 79#64 := by bv_omega
  have h152 : (s0.sp - 2400#64) + 152#64 = s0.sp - 2248#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h224 : (s0.sp - 2400#64) + 224#64 = s0.sp - 2176#64 := by bv_omega
  have h232 : (s0.sp - 2400#64) + 232#64 = s0.sp - 2168#64 := by bv_omega
  rw [ha73, ha77, ha79] at hp1_split
  rw [hp1_split, h152, h200, h224, h232]
  simp only [sepConj_assoc]
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 1632#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1720#64) _ _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · exact Entails.of_eq (by ac_rfl)
  · wp_done

/-! ## 2. `+5728 -> +7212`: `sending_ct2 = none` Branch -/

/-- At `+5728`, when `l1.toNat < 2 ^ 63` (`[sp + 200] = l1`) and `x22 = noneCap`
(`sending_ct2 = none`), `cmn x8, #1` is false and `cmn x22, #1` is true, branching to `+7212`. -/
theorem v10_ct2Sent_5728_to_7212_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa1 l1 l2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 5728#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx22_1 : s1.readReg64 .x22 = noneCap)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7212#64) s1
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x26 = l2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hl1_ne1 := v10_cap_add_one_beq_zero_false hl1_lt
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  rw [h200]
  dsimp only [noneCap] at hx22_1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 5728#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7212#64) _ _ _
  wp_steps
  wp_done

/-! ## 3. `+5728 -> +5808`: Copying `ProtoPolynomialEncoder` and Calling `<PolyEncoder>::from_pb` -/

/-- Steps `+5728 -> lsmpl.base 374` (`20` instructions including `bl <PolyEncoder>::from_pb`):
copies the 56-byte `ProtoPolynomialEncoder` from `pbA + 8..64` to `fsp + 1392..1448` and enters
`<PolyEncoder>::from_pb` with `x0 = fsp + 1888`, `x1 = fsp + 1392`, and `x30 = lsmpl.base 333 + 5808`. -/
theorem v10_ct2Sent_copy_to_encoder_call_5728_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State)
    (fsp out pbA pa1 l1 l2 cap_pts ptr_pts len_pts cap_polys ptr_polys len_polys w56 : BitVec 64)
    (u1392 u1401 u1409 u1417 u1424 u1432 u1440 : BitVec 64) (b1400 : BitVec 8)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hcap_pts_lt : cap_pts.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 5728#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx22_1 : s1.readReg64 .x22 = cap_pts)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1
      (((fsp + 200#64) ↦₆₄ l1) ∗
        ((fsp + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
        ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
        ((pbA + 24#64) ↦₆₄ len_pts) ∗
        ((pbA + 32#64) ↦₆₄ cap_polys) ∗
        ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
        ((pbA + 48#64) ↦₆₄ len_polys) ∗
        ((pbA + 56#64) ↦₆₄ w56) ∗
        ((fsp + 1392#64) ↦₆₄ u1392) ∗
        ((fsp + 1400#64) ↦₈ b1400) ∗
        ((fsp + 1401#64) ↦₆₄ u1401) ∗
        ((fsp + 1409#64) ↦₆₄ u1409) ∗
        ((fsp + 1417#64) ↦ₛ loBytes7 u1417) ∗
        ((fsp + 1424#64) ↦₆₄ u1424) ∗
        ((fsp + 1432#64) ↦₆₄ u1432) ∗
        ((fsp + 1440#64) ↦₆₄ u1440) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 200#64) ↦₆₄ l1) ∗
          ((fsp + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
          ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
          ((pbA + 24#64) ↦₆₄ len_pts) ∗
          ((pbA + 32#64) ↦₆₄ cap_polys) ∗
          ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
          ((pbA + 48#64) ↦₆₄ len_polys) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗
          ((fsp + 1392#64) ↦₆₄ cap_pts) ∗
          ((fsp + 1400#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 1408#64) ↦₆₄ len_pts) ∗
          ((fsp + 1416#64) ↦₆₄ cap_polys) ∗
          ((fsp + 1424#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 1432#64) ↦₆₄ len_polys) ∗
          ((fsp + 1440#64) ↦₆₄ w56) ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x22 = cap_pts ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 5808#64 ∧
        TraceCalleeSaved sm s1) := by
  subst hsp1
  have hl1_ne1 := v10_cap_add_one_beq_zero_false hl1_lt
  have hcap_ne1 := v10_cap_add_one_beq_zero_false hcap_pts_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 5728#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 374) _ _ _
  wp_simp_pre [v10_pbA_16_realign_rest, sepConj_assoc]
  iterate 16 wp_step
  wp_simp_pre [v10_pbA_16_unrealign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre [v10_fsp_1409_realign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre [v10_fsp_1400_realign_rest, sepConj_assoc]
  wp_done

/-! ## 4. Post-`<PolyEncoder>::from_pb` Error and Ok Branches (`+5808 -> +5820` and `+5808 -> +7904`) -/

/-- At `+5808`, when `[sp + 1888] = 2#64` (`fromPbResult pb = .error err`),
`ldr x15, [sp, #1888]; cmp x15, #2; b.ne +7904` falls through to `+5820`. -/
theorem v10_ct2Sent_5808_to_5820_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa1 ca2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5808#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5820#64) s1
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x26 = ca2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
  rw [h1888]
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 5808#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5820#64) _ _ _
  wp_steps
  wp_done

/-- Step `+5808 -> +7904` (3 instructions) when `PolyEncoder::from_pb`
returns `Ok(enc)` (`tag = 0 ∨ tag = 1`). -/
theorem v10_ct2Sent_5808_to_7904_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp : BitVec 64)
    (tag : BitVec 64) (htag : tag = 0#64 ∨ tag = 1#64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 5808#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7904#64) s
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x19 = s.readReg64 .x19 ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        TraceCalleeSaved s2 s0) := by
  subst hsp
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 5808#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7904#64) _ _ _
  rcases htag with rfl | rfl
  · wp_steps
    wp_done
  · wp_steps
    wp_done

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v10_sub_ok_encoder_from_pb_placed
  v10_ct2Sent_load_1632_to_1720_placed
  v10_ct2Sent_5728_to_7212_none_placed
  v10_ct2Sent_copy_to_encoder_call_5728_placed
  v10_ct2Sent_5808_to_5820_err_placed
  v10_ct2Sent_5808_to_7904_ok_placed
)

end CryptoVerification.SpqrV1.States.FromPb
