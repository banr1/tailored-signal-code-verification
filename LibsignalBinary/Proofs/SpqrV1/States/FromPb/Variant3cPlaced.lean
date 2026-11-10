/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3c
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 3 (`Ct1Received`, `+692`) — Execution Segments

Relocatable Block-`333` forward execution segments (`+692..+1012` and `+4984 -> +8180`).
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

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v3cr_bv_add_add_lit
attribute [local arm64_norm, local wp_norm]
  v3cr_pbA_17_add_8 v3cr_pbA_40_add_8 v3cr_pbA_56_add_8 v3cr_pbA_72_add_8
  v3cr_pbA_88_add_8 v3cr_pbA_121_add_8 v3cr_pbA_144_add_8
  v3cr_fsp_905_add_8 v3cr_fsp_928_add_8 v3cr_fsp_944_add_8 v3cr_fsp_960_add_8 v3cr_fsp_976_add_8
  v3cr_fsp_249_add_8 v3cr_fsp_272_add_8 v3cr_fsp_848_add_48
  v3cr_fsp_1792_add_233 v3cr_fsp_848_add_15 v3cr_fsp_848_add_39

/-! ## `+692 -> +4176` (`uc = none`) and `+692 -> +784` (`uc = some u`): 160B PB Copy -/

theorem v3cr_copy_pb_692_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4176#64) s1
      (v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = 0#64 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 692#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4176#64) _ _ _
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  wp_simp_pre only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]
  wp_steps
  simp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]; wp_done

theorem v3cr_copy_pb_692_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hu8_lt : u8.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 784#64) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x8 = u8 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  have hu8_ne1 := v10_cap_add_one_beq_zero_false hu8_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 692#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 784#64) _ _ _
  wp_simp_pre only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]
  wp_steps
  simp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, sepConj_assoc]; wp_done

/-! ## (`+784 -> lsmpl.base 348`): Unaligned 24-Byte Copy & `<EkSentCt1Received>::from_pb` Call -/

theorem v3cr_copy_uc_to_call_784_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 784#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = u8) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 348) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        ((fsp + 1400#64) ↦₆₄ u16) ∗
        v1_ucWordsAt (fsp + 896#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          ((fsp + 1400#64) ↦₆₄ u16) ∗
          v1_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 896#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 860#64 ∧
        TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 784#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 348) _ _ _
  wp_simp_pre only [v1_ucWordsAt, v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
    v3cr_fsp_904_triple64_rest,
    v10_pbA_16_realign_rest, v3cr_fsp_1400_split_1_7_rest, sepConj_assoc]
  iterate 13 wp_step
  wp_simp_pre only [v10_pbA_16_unrealign_rest, v3cr_fsp_1400_unsplit_1_7_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v3cr_fsp_913_realign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre only [v3cr_fsp_904_realign_rest, sepConj_assoc]
  simp only [v1_ucWordsAt, sepConj_assoc]; wp_done

/-! ## (`+860 -> +4176 | +4884 | +924`): Post-`EkSentCt1Received.from_pb` Dispatch -/

theorem v3cr_post_uc_860_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp out w1896 w1904 w1912 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4176#64) s1
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = w1896 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 860#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4176#64) _ _ _
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  wp_steps; wp_done

theorem v3cr_post_uc_860_ok_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State)
    (fsp out ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hca1_lt : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4884#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1; have hca1_ne1 := v10_cap_add_one_beq_zero_false hca1_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 860#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4884#64) _ _ _
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  wp_simp_pre only [v1_ucWordsAt, sepConj_assoc]; wp_steps
  simp only [v1_ucWordsAt, sepConj_assoc]; wp_done

theorem v3cr_post_uc_860_ok_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State)
    (fsp out pbA ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1_lt : ca1.toNat < 2 ^ 63) (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 924#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧ sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = ca2 ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  have hca1_ne1 := v10_cap_add_one_beq_zero_false hca1_lt
  have hw0_ne1 := v10_cap_add_one_beq_zero_false hw0_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 860#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 924#64) _ _ _
  wp_simp_pre only [v1_ucWordsAt, sepConj_assoc]; wp_steps
  simp only [v1_ucWordsAt, sepConj_assoc]; wp_done

/-! ## (`+924 -> lsmpl.base 374`): Saving `uc` Fields & Copying `sendingEk` -/

theorem v3cr_copy_enc_to_call_924_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w0 w8 w16 w24 w32 w40 w48 v64 v96 v184 v192 v200
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 924#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2) (hx1_1 : s1.readReg64 .x1 = ca1)
    (hx8_1 : s1.readReg64 .x8 = w0) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa4) (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx24_1 : s1.readReg64 .x24 = la1)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1
      (((fsp + 64#64) ↦₆₄ v64) ∗ ((fsp + 96#64) ↦₆₄ v96) ∗
        ((fsp + 184#64) ↦₆₄ v184) ∗ ((fsp + 192#64) ↦₆₄ v192) ∗ ((fsp + 200#64) ↦₆₄ v200) ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
        ((fsp + 1504#64) ↦₆₄ w8) ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 64#64) ↦₆₄ uc_ep) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          ((fsp + 1504#64) ↦₆₄ w8) ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = ca2 ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 1012#64 ∧
        TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 924#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 374) _ _ _
  wp_simp_pre only [v1_optProtoPolyEncoderWordsAt, v1_ucWordsAt,
    v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
    v3cr_fsp_248_triple64_rest,
    v3cr_pbA_120_realign_rest, v3cr_fsp_1504_split_1_7_rest, sepConj_assoc]
  iterate 14 wp_step
  wp_simp_pre only [v3cr_pbA_120_unrealign_rest, v3cr_fsp_1504_unsplit_1_7_rest, sepConj_assoc]
  iterate 6 wp_step
  wp_simp_pre only [v3cr_fsp_257_realign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre only [v3cr_fsp_248_realign_rest, sepConj_assoc]
  simp only [v1_optProtoPolyEncoderWordsAt, v1_ucWordsAt, sepConj_assoc]; wp_done

/-! ## (`+1012 -> +1024 | +4984`): Post-`<PolyEncoder>::from_pb` Branch -/

theorem v3cr_post_enc_1012_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp out pa1 pa4 ca3 ca2 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1012#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa4)
    (hx22_1 : s1.readReg64 .x22 = pa1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1024#64) s1
      (((fsp + 1888#64) ↦₆₄ 2#64) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ 2#64) ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 1012#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1024#64) _ _ _
  wp_steps; wp_done

theorem v3cr_post_enc_1012_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp out tag la2 pa4 pa1 la1 ca3 ca2 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (htag_ne2 : (tag - 2#64 == 0#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 1012#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = la2)
    (hx21_1 : s1.readReg64 .x21 = pa4) (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx24_1 : s1.readReg64 .x24 = la1)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4984#64) s1
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x15 = tag ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 1012#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4984#64) _ _ _
  wp_steps; wp_done

/-! ## (`+4984 -> +8180`): `PolyEncoder` Relocation -/

set_option maxHeartbeats 3200000 in
/-- Execution segment `+4984 -> +8180` (`lsmpl.base 333 + 4984 -> +8180`, 69 instructions):
unpacks the `PolyEncoder` from `fsp + 1888..2288` and the `unchunkedEkSentCt1ReceivedAt` words
from stack slots `fsp + 64, 96, 176, 184, 192, 200, 224` and registers `x20, x21, x22, x24, x26, x28`,
populating `epilogueStackSlots` for the shared epilogue at `+8180`. -/
theorem v3cr_pack_enc_4984_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State)
    (fsp out w_tag ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80 e_w88 e_w96
     e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
     e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 u160 u208 u232 : BitVec 64) (u172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (u832 : BitVec 64) (q848 : BitVec 128) (u864 u880 u887 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4984#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx15_1 : s1.readReg64 .x15 = w_tag) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = la2) (hx21_1 : s1.readReg64 .x21 = pa4)
    (hx22_1 : s1.readReg64 .x22 = pa1) (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = la1) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx28_1 : s1.readReg64 .x28 = ca2) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s1
      (((fsp + 64#64) ↦₆₄ uc_ep) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ u160) ∗
        ((fsp + 172#64) ↦₃₂ u172) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
        ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 232#64) ↦₆₄ u232) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ u832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 u864) ∗
        ((fsp + 880#64) ↦ₛ loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ u887) ∗
        v3cr_polyEncoderWordsAt (fsp + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 64#64) ↦₆₄ uc_ep) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ la2) ∗
          ((fsp + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 208#64) ↦₆₄ e_w8) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 608#64) ↦₁₂₈ e_q160) ∗ ((fsp + 624#64) ↦₁₂₈ e_q176) ∗ ((fsp + 640#64) ↦₁₂₈ e_q192) ∗
          ((fsp + 656#64) ↦₁₂₈ e_q208) ∗ ((fsp + 672#64) ↦₁₂₈ e_q224) ∗ ((fsp + 688#64) ↦₁₂₈ e_q240) ∗
          ((fsp + 704#64) ↦₁₂₈ e_q256) ∗ ((fsp + 720#64) ↦₁₂₈ e_q272) ∗ ((fsp + 736#64) ↦₁₂₈ e_q288) ∗
          ((fsp + 752#64) ↦₁₂₈ e_q304) ∗ ((fsp + 768#64) ↦₁₂₈ e_q320) ∗ ((fsp + 784#64) ↦₁₂₈ e_q336) ∗
          ((fsp + 800#64) ↦₁₂₈ e_q352) ∗ ((fsp + 816#64) ↦₁₂₈ e_q368) ∗ ((fsp + 832#64) ↦₆₄ e_w384) ∗
          ((fsp + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
          ((fsp + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
          ((fsp + 864#64) ↦ₛ hiBytes7 e_w152) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
          ((fsp + 888#64) ↦ₛ hiBytes7 e_w120) ∗
          v3cr_polyEncoderWordsAt (fsp + 1888#64)
            w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
            e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
            e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
            e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = e_w80 ∧ sm.readReg64 .x1 = la3 ∧
        sm.readReg64 .x2 = e_w392 ∧ sm.readReg32 .x3 = (e_w88.extractLsb' 0 8).zeroExtend 32 ∧
        sm.readReg64 .x4 = e_w96 ∧ sm.readReg64 .x5 = e_w104 ∧
        sm.readReg64 .x6 = fsp + 576#64 ∧ sm.readReg64 .x7 = e_w128 ∧
        sm.readReg64 .x8 = 5#64 ∧ sm.readReg64 .x9 = e_w48 ∧
        sm.readReg64 .x10 = pa2 ∧ sm.readReg64 .x11 = ca1 ∧
        sm.readReg64 .x12 = pa3 ∧ sm.readReg64 .x13 = e_w24 ∧
        sm.readReg64 .x14 = e_w56 ∧ sm.readReg64 .x15 = w_tag ∧
        sm.readReg64 .x16 = uc_ep ∧ sm.readReg64 .x17 = e_w72 ∧
        sm.readReg64 .x18 = e_w64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = e_w16 ∧ sm.readReg32 .x21 = (loByte e_w112).zeroExtend 32 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = la1 ∧ sm.readReg64 .x25 = e_w32 ∧
        sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x27 = v3a_pack88 e_w88 ∧
        sm.readReg64 .x28 = pa4 ∧ sm.readReg64 .x30 = e_w40 ∧ TraceCalleeSaved sm s1) := by
  subst hsp1
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 4984#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8180#64) _ _ _
  dsimp only [v3cr_polyEncoderWordsAt,
    v3a_tripleVecGF16WordsAt, v3cr_quadPairsWordsAt, v3cr_pairVecGF16WordsAt,
    BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  wp_simp_pre only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
    v3a_fsp_1976_realign_rest, v3a_fsp_2024_realign_rest, sepConj_assoc]
  iterate 3 wp_step
  wp_simp_pre only [v3a_fsp_2024_unrealign_rest, pointsTo128,
    v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 9 wp_step
  wp_simp_pre only [v3a_fsp_2000_realign_rest, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 12 wp_step
  wp_simp_pre only [v3cr_fsp_848_871_before_863_pair_eq, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_step
  wp_simp_pre only [v3cr_fsp_848_871_after_863_pair_eq, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 12 wp_step
  wp_simp_pre only [v3cr_fsp_880_895_after_887_rest_eq, v3a_fsp_2000_unrealign_rest,
    v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  iterate 32 wp_step
  wp_simp_pre only [v3a_fsp_1976_unrealign_rest, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  have hz1 : ∀ w : BitVec 64, (loByte w).zeroExtend 32 = BitVec.setWidth 32 (BitVec.setWidth 8 w) := by
    intro w; unfold loByte; bv_kernel
  have hz2 : ∀ w : BitVec 64, (w.extractLsb' 0 8).zeroExtend 32 = BitVec.setWidth 32 (BitVec.setWidth 8 w) := by
    intro w; bv_kernel
  have hz3 : ∀ w : BitVec 64, (loByte w).zeroExtend 64 = BitVec.zeroExtend 64 (BitVec.setWidth 8 w) := by
    intro w; unfold loByte; bv_kernel
  have hp88 : BitVec.zeroExtend 64 (BitVec.extractLsb' 8 32 e_w88) |||
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.extractLsb' 40 16 e_w88) |||
          BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.extractLsb' 56 8 e_w88) <<< 16))) <<< 32 =
      v3a_pack88 e_w88 := by unfold v3a_pack88; bv_kernel
  simp only [pointsTo128, BitVec.extractLsb'_zero, hz1, hz2, hz3, hp88, v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  refine SepWP.done rfl hrun1 ⟨Entails.of_eq (by ac_rfl), ?_⟩
  dsimp only [TraceCalleeSaved, CalleeSavedPreserved]
  simp only [wp_norm, arm64_norm, *]

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v3cr_copy_pb_692_none_placed
  v3cr_copy_pb_692_some_placed
  v3cr_copy_uc_to_call_784_placed
  v3cr_post_uc_860_err_placed
  v3cr_post_uc_860_ok_none_placed
  v3cr_post_uc_860_ok_some_placed
  v3cr_copy_enc_to_call_924_placed
  v3cr_post_enc_1012_err_placed
  v3cr_post_enc_1012_ok_placed
  v3cr_pack_enc_4984_to_8180_placed
)

end CryptoVerification.SpqrV1.States.FromPb
