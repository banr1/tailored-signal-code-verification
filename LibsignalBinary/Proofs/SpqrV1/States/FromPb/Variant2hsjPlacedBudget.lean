/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsgPlacedBudget
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsh
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hshPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsiPlacedBudget

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part J

Total-correctness relocatable Block-`333` `+9036 -> ret` continuation (`sendingEk = some pbEnc`)
for `InnerState.headerSent` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsjPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsProg_333 lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder ProtoAuthenticator States V1State pbToProtoPolyDecoder pbToProtoPolyEncoder
   spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize protoPolynomialDecoderAt
   protoPolynomialDecoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize
   resultPolyDecoderFromPbAt resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack fromPbResult loByte)
open CryptoVerification.SpqrV1.States.FromPb hiding
  DecoderFromPbPlacedOkExt
  v2hstop_SomeEnc9036HypPlaced
  v2hsh_encoder_call_9096_placed
  v2hsh_decoder_call_9384_placed
  v2hsh_branch_enc_err_9100_placed
  v2hsh_branch_none_dec_9328_placed
  v2hsh_branch_err_dec_9388_placed
  v2hsh_branch_ok_dec_9388_placed
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget encoder_from_pb_ok_of_alloc_placed
   seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlacedBudget
  (v2hse_copy_enc_9032_to_9096_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2PlacedBudget
  (v2hse2_enc_ok_move_9100_to_9328_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3PlacedBudget
  (v2hse3_copy_dec_9328_to_9384_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsgPlacedBudget
  (encoderFromPbEnv_imp_headerSentSomeEnc9036Env
   fitsEnv_decoderAlloc_of_headerSentSomeEnc9036Env
   fitsEnv_encoderAlloc_of_headerSentSomeEnc9036Env
   headerSentSomeEnc9036Env_append_freeOnly
   headerSentSomeEnc9036Env_of_some_dec
   headerSentSomeEncOptEnv_of_some
   v2hstop_SomeEnc9036HypPlaced
   v2hstop_SomeEnc9036SepWPHypPlaced
   v2hstop_someEnc9036HypPlacedOfEnv_of_sepWP)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hshPlacedBudget
  (v2hsh_branch_enc_err_9100_placed v2hsh_decoder_call_9384_sepWP_placed
   v2hsh_encoder_call_9096_sepWP_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsiPlacedBudget
  (v2hsh_branch_err_dec_9388_placed v2hsh_branch_none_dec_9328_placed
   v2hsh_branch_ok_dec_9388_placed)

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit v2hsh_bv_add_add_lit

/-! ## Main `+9036 -> s0.x30` Continuation (`v2hstop_some_enc_9036_to_ret*_placed`) -/

set_option maxHeartbeats 1200000 in
/-- Proves `v2hstop_SomeEnc9036SepWPHypPlaced`: from `+9036` (`sendingEk = some pbEnc`) to `s0.x30`
    under `RustCliAllocBudget M` and `HeaderSentSomeEncOptEnv s`. -/
theorem v2hstop_some_enc_9036_to_ret_sepWP_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc_ok : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec_ok_ext : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    v2hstop_SomeEnc9036SepWPHypPlaced M A lim F ext s := by
  intro st s0 sm out pbA u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
    hcl hpts_bound hdec_ok hfits huc hdk_len hauth henc hu8 hu24 hu48 hu72 hu80 hrk_lt hsp0_align
    hpc hrun hsp hx0 hx8 hx9 hx10 hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 htr
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hpts_len : ∀ bs ∈ (pbToProtoPolyEncoder pbEnc).pts, bs.length ≤ 2 * 0x0555555555555555 := by
    simp only [optEncoderPtsBound, henc] at hpts_bound
    exact hpts_bound
  have hfits_enc := fitsEnv_encoderAlloc_of_headerSentSomeEnc9036Env hfits
  rw [v2hsh_from_pb_headerSent_some_enc_eq F s u auth pbEnc hdec_ok huc hdk_len hauth henc]
  have h960_split := v2hsh_memRegion_1344_960_split fsp
  have h976_def :
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 =
      ((fsp + 984#64) ↦₆₄ w8) ∗
      (((fsp + 976#64) ↦₆₄ w0) ∗ ((fsp + 992#64) ↦₆₄ w16) ∗ ((fsp + 1000#64) ↦₆₄ w24) ∗
       ((fsp + 1008#64) ↦₆₄ w32) ∗ ((fsp + 1016#64) ↦₆₄ w40) ∗ ((fsp + 1024#64) ↦₆₄ w48)) := by
    dsimp only [v1_optProtoPolyEncoderWordsAt, fsp]; simp only [arm64_norm]; sep_ac_rfl
  have hpbA_def :
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 =
      ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
      ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
      (memRegion pbA 96 ∗ memRegion (pbA + 144#64) 80) := by
    dsimp only [v2hstop_pbEncTailAt]; sep_ac_rfl
  let Frame9036 : SepProp :=
    stackAt fsp encoderFromPbStack ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
    vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
    (((fsp + 976#64) ↦₆₄ w0) ∗ ((fsp + 992#64) ↦₆₄ w16) ∗ ((fsp + 1000#64) ↦₆₄ w24) ∗
     ((fsp + 1008#64) ↦₆₄ w32) ∗ ((fsp + 1016#64) ↦₆₄ w40) ∗ ((fsp + 1024#64) ↦₆₄ w48)) ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 1848#64) 40 ∗ memRegion (fsp + 1888#64) polyEncoderSize ∗
    memRegion (fsp + 2288#64) 16 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA 96 ∗ memRegion (pbA + 144#64) 80) ∗ statesFromPbJumpTablePlacedAt
  have hpre9036 :
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st sm) ⊢
      ((fsp + 984#64) ↦₆₄ w8) ∗
        ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
        ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
        memRegion (fsp + 1792#64) 56 ∗ A.pool lim st sm ∗ Frame9036 := by
    rw [h976_def, hpbA_def]; dsimp only [Frame9036]
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 1344#64) 960 ∗
      (((fsp + 984#64) ↦₆₄ w8) ∗
       ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
       ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
       A.pool lim st sm ∗
       stackAt fsp encoderFromPbStack ∗
       ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
       ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
       ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
       memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
       v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
       (((fsp + 976#64) ↦₆₄ w0) ∗ ((fsp + 992#64) ↦₆₄ w16) ∗ ((fsp + 1000#64) ↦₆₄ w24) ∗
        ((fsp + 1008#64) ↦₆₄ w32) ∗ ((fsp + 1016#64) ↦₆₄ w40) ∗ ((fsp + 1024#64) ↦₆₄ w48)) ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 192 ∗
       v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (memRegion pbA 96 ∗ memRegion (pbA + 144#64) 80) ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h960_split) (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre9036 ?_
  refine seq_clean_lscl_st hcl
    (mid := lsmpl.base 333 + 9096#64)
    (P_mid := fun s1 =>
      ((fsp + 984#64) ↦₆₄ w8) ∗
      ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
      ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
      v2hse_protoPolyEncoderWordsAt (fsp + 1792#64) w0 w8 w16 w24 w32 w40 w48 ∗
      A.pool lim st s1 ∗ Frame9036)
    (Q := fun s1 =>
      VmPreserved sm s1 ∧
      s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧
      s1.readReg64 .x1 = fsp + 1792#64 ∧ s1.readReg64 .x19 = out ∧
      s1.readReg64 .x21 = sm.readReg64 .x21 ∧ s1.readReg64 .x22 = d_w0 ∧
      s1.readReg64 .x23 = sm.readReg64 .x23 ∧ s1.readReg64 .x24 = fsp + 1888#64 ∧
      s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x26 = u8 ∧
      s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = sm.readReg64 .x28 ∧
      TraceCalleeSaved s1 s0)
    (v2hse_copy_enc_9032_to_9096_placed_budget A lim st (ext := ext)
      s0 sm fsp out d_w0 u8 pbA w0 w8 w16 w24 w32 w40 w48 Frame9036
      hfsp_align hpc hrun hsp hx8 hx19 hx22 hx26 hx27 htr) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨_hvm1, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, htr1⟩
  rw [hx21] at hx21_1; rw [hx23] at hx23_1; rw [hx28] at hx28_1
  have hproto_enc := v2hsh_protoPolyEncoder_pack A.repAlloc (fsp + 1792#64) (pbToProtoPolyEncoder pbEnc)
    w0 w8 w16 w24 w32 w40 w48
  have hpbA_full := v2hstop_pbEncTailAt_entails_full_224 pbA w8 w16 w24 w32 w40 w48
  rw [hpbA_def] at hpbA_full
  let RestRO : SepProp := memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
  let Rest9096 : SepProp :=
    memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
    vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ RestRO
  have hpre9096 :
      (((fsp + 984#64) ↦₆₄ w8) ∗
        ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
        ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
        v2hse_protoPolyEncoderWordsAt (fsp + 1792#64) w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool lim st s1 ∗ Frame9036) ⊢
      stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) (pbToProtoPolyEncoder pbEnc) ∗
        A.pool lim st s1 ∗ Rest9096 := by
    dsimp only [Frame9036, Rest9096, RestRO]
    rw [h976_def]
    refine Entails.trans (Entails.of_eq (show _ =
      (v2hse_protoPolyEncoderWordsAt (fsp + 1792#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48) ∗
      (((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
       ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
       (memRegion pbA 96 ∗ memRegion (pbA + 144#64) 80)) ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1888#64) polyEncoderSize ∗ A.pool lim st s1 ∗
       (memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        (((fsp + 984#64) ↦₆₄ w8) ∗
         (((fsp + 976#64) ↦₆₄ w0) ∗ ((fsp + 992#64) ↦₆₄ w16) ∗ ((fsp + 1000#64) ↦₆₄ w24) ∗
          ((fsp + 1008#64) ↦₆₄ w32) ∗ ((fsp + 1016#64) ↦₆₄ w40) ∗ ((fsp + 1024#64) ↦₆₄ w48))) ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hproto_enc (sepConj_mono_left hpbA_full))
      (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre9096 ?_
  refine v2hsh_encoder_call_9096_sepWP_placed henc_ok st s0 s1 (s0.readReg64 .x30) fsp out d_w0 pa1 u8 pbA u80
    (pbToProtoPolyEncoder pbEnc) Rest9096 _ hcl1 hfsp_align hpts_len hfits_enc
    hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1 ?_
  intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
  cases henc_res : fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | error err =>
    have herr := v2hsh_branch_enc_err_9100_placed (F := F) hA (M.stepEvents evs1 st) s0 s2 out u.dk auth
      u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
      (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
      err RestRO hu48 hu72 hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [Rest9096, protoPolynomialEncoderSize, fsp]; sep_ac_rfl))
      (SepWP.mono herr fun sf Pf _ _ ⟨evs_f, hfree, hPf, hspf, hcsf, htrf⟩ => ?_)
    refine ⟨⟨evs1 ++ evs_f,
      headerSentSomeEncOptEnv_of_some henc
        (headerSentSomeEnc9036Env_append_freeOnly
          (encoderFromPbEnv_imp_headerSentSomeEnc9036Env hevs1) hfree),
      ?_⟩, hspf, hcsf, htrf⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by dsimp only [RestRO]; sep_ac_rfl))
  | ok enc =>
    rw [v2hse2_resultPolyEncoder_ok_eq A.repAlloc (fsp + 1888#64) enc]
    have henc_rel := v2hse2_polyEncoderAt_relocate A.repAlloc (fsp + 1888#64) enc
    have hscratch_split := v2hsh_stack896ScratchRest_split_56 fsp
    have h240_split := v2hsh_memRegion_240_736_split_24 fsp
    dsimp only [Rest9096, protoPolynomialEncoderSize]
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        polyEncoderAt A.repAlloc (fsp + 1888#64) enc ∗
        memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        (stackAt fsp encoderFromPbStack ∗
         memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
         memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
         memRegion (fsp + 2288#64) 16 ∗
         ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
         ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
         ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
         v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
         vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 192 ∗
         v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs1 st) s2 ∗ RestRO) by sep_ac_rfl))
        (sepConj_mono henc_rel (sepConj_mono h240_split (sepConj_mono_left hscratch_split)))) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_elim; intro slot56_old
    apply ProofLib.SepWP.exists_elim; intro bs
    apply ProofLib.SepWP.exists_elim; intro hi32
    apply ProofLib.SepWP.exists_elim; intro P_enc_heap
    apply ProofLib.SepWP.pure_elim; intro hreloc_all
    obtain ⟨w8_e, w16_e, w24_e, tail368, hw8_e, hsplit_all⟩ :=
      v2hse2_bs384_w392_split_368 bs.val bs.property (hi32 ++ enc.idx)
    have hsplit_1888 := hsplit_all (fsp + 1888#64)
    simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hsplit_1888
    let Frame9100_ok : SepProp :=
      P_enc_heap ∗
      memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
      memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
      memRegion (fsp + 264#64) 712 ∗
      memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
      memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
      memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
      ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
      ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
      v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
      vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 192 ∗
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ RestRO
    have hpre9100_ok :
        (((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          (((fsp + 1888#64) + 8#64) ↦ₛ bs.val) ∗
          (((fsp + 1888#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ∗
          memRegion (fsp + 240#64) 24 ∗ memRegion (fsp + 264#64) 712 ∗
          memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ slot56_old) ∗
          memRegion (fsp + 64#64) 32 ∗ memRegion (fsp + 104#64) 48 ∗
          memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
          memRegion (fsp + 208#64) 8 ∗
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
          memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 2288#64) 16 ∗
          ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
          ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
          v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
          vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (fsp + 1072#64) 192 ∗
          v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ RestRO) ⊢
        stackAt fsp encoderFromPbStack ∗
          ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((fsp + 1896#64) ↦₆₄ w8_e) ∗ ((fsp + 1904#64) ↦₆₄ w16_e) ∗
          ((fsp + 1912#64) ↦₆₄ w24_e) ∗ ((fsp + 1920#64) ↦ₛ tail368.val) ∗
          memRegion (fsp + 1392#64) 400 ∗ memRegion (fsp + 240#64) 24 ∗
          ((fsp + 56#64) ↦₆₄ slot56_old) ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9100_ok := by
      simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1896#64) ↦ₛ bs.val) ∗ ((fsp + 2280#64) ↦₆₄ (hi32 ++ enc.idx))) ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
         memRegion (fsp + 1392#64) 400 ∗ memRegion (fsp + 240#64) 24 ∗
         ((fsp + 56#64) ↦₆₄ slot56_old) ∗
         A.pool lim (M.stepEvents evs1 st) s2 ∗ Frame9100_ok) by
          dsimp only [Frame9100_ok]; sep_ac_rfl)) ?_
      rw [hsplit_1888]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hpre9100_ok ?_
    refine seq_clean_lscl_st hcl2
      (mid := lsmpl.base 333 + 9328#64)
      (P_mid := fun s3 =>
        stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
        ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        A.pool lim (M.stepEvents evs1 st) s3 ∗ Frame9100_ok)
      (Q := fun s3 =>
        VmPreserved s2 s3 ∧
        s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x20 = (loByte w8_e).zeroExtend 64 ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧ s3.readReg64 .x22 = d_w0 ∧
        s3.readReg64 .x23 = fsp + 1392#64 ∧ s3.readReg64 .x24 = fsp + 1888#64 ∧
        s3.readReg64 .x25 = fsp + 1792#64 ∧ s3.readReg64 .x26 = u8 ∧
        s3.readReg64 .x27 = pbA ∧ s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.pstate = addsPState64 d_w0 1#64 ∧ TraceCalleeSaved s3 s0)
      (v2hse2_enc_ok_move_9100_to_9328_placed_budget hA s0 s2 fsp out d_w0 u8 pbA slot56_old w8_e w16_e w24_e
        tail368 enc (M.stepEvents evs1 st) Frame9100_ok
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 htr2) ?_
    intro s3 hpc3 hrun3 hcl3 ⟨_hvm3, hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hpstate3, htr3⟩
    rw [hx21_2] at hx21_3; rw [hx28_2] at hx28_3
    have hw8_word0 := v2hsh_wordAt_0_eq_of_take8 bs.val w8_e hw8_e
    rw [← hw8_word0] at hx20_3
    cases hrec : s.receivingCt1 with
    | none =>
      dsimp only [Frame9100_ok]
      rw [hrec]
      dsimp only [Option.map, v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap]
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ⌜d_w0 = noneCap⌝ ∗
        (stackAt fsp encoderFromPbStack ∗
         memRegion (fsp + 1888#64) 400 ∗
         ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
         ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
         ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
         memRegion (fsp + 240#64) 24 ∗
         ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
         P_enc_heap ∗
         memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
         memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
         memRegion (fsp + 264#64) 712 ∗
         memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
         memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
         memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
         ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
         ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
         ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
         v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
         vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 192 ∗
         v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs1 st) s3 ∗ RestRO) by sep_ac_rfl)) ?_
      apply ProofLib.SepWP.pure_elim; intro hd_w0_none
      subst hd_w0_none
      have hnone := v2hsh_branch_none_dec_9328_placed (F := F) hA (M.stepEvents evs1 st) s0 s3 out u.dk auth
        u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
        d_w8 d_w16 d_w24 d_w32 w8_e w16_e w24_e hi32 bs tail368 enc P_enc_heap RestRO
        (hsplit_all (fsp + 1392#64)) (hreloc_all (fsp + 1392#64))
        hu48 hu72 hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx23_3 hx26_3 hpstate3 htr3
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]))
        (SepWP.mono hnone fun sf Pf _ _ ⟨evs_f, hfree, hPf, hspf, hcsf, htrf⟩ => ?_)
      refine ⟨⟨evs1 ++ evs_f,
        headerSentSomeEncOptEnv_of_some henc
          (headerSentSomeEnc9036Env_append_freeOnly
            (encoderFromPbEnv_imp_headerSentSomeEnc9036Env hevs1) hfree),
        ?_⟩, hspf, hcsf, htrf⟩
      rw [M.stepEvents_append]
      exact Entails.trans hPf (Entails.of_eq (by dsimp only [RestRO]; sep_ac_rfl))
    | some pbDec =>
      dsimp only [Frame9100_ok]
      rw [hrec]
      dsimp only [Option.map]
      have hd_ext := v2hstop_optProtoDecoderHeap_some_extract A.repAlloc pbDec d_w0 d_w8 d_w16 d_w24 d_w32
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          v2hs_optProtoDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder pbDec)) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          (stackAt fsp encoderFromPbStack ∗
           memRegion (fsp + 1888#64) 400 ∗
           ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
           ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
           ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
           memRegion (fsp + 240#64) 24 ∗
           ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
           P_enc_heap ∗
           memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
           memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
           memRegion (fsp + 264#64) 712 ∗
           memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
           memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
           memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
           ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
           ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
           ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
           ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
           v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
           vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
           v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           memRegion (fsp + 1072#64) 192 ∗
           v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool lim (M.stepEvents evs1 st) s3 ∗ RestRO) by sep_ac_rfl))
          (sepConj_mono_left hd_ext)) ?_
      conv => arg 4; rw [sepConj_assoc]
      apply ProofLib.SepWP.pure_elim; rintro ⟨hd_w0_cap, _⟩
      have hd_w0_lt : d_w0.toNat < 2 ^ 63 := by omega
      have hdec_words :
          v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 =
          ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
          ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
          ((fsp + 1064#64) ↦₆₄ d_w32) := by
        dsimp only [v2hs_optProtoDecoderWordsAt]; simp only [arm64_norm]
      let Frame9328_some : SepProp :=
        v2hs_optProtoDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder pbDec)) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        ((fsp + 1032#64) ↦₆₄ d_w0) ∗
        stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
        ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (fsp + 1792#64) 56 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
        memRegion (fsp + 264#64) 712 ∗
        memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
        memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
        memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ RestRO
      have hpre9328_some :
          (v2hs_optProtoDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder pbDec)) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            (stackAt fsp encoderFromPbStack ∗
             memRegion (fsp + 1888#64) 400 ∗
             ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
             ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
             ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
             memRegion (fsp + 240#64) 24 ∗
             ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
             P_enc_heap ∗
             memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
             memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
             memRegion (fsp + 264#64) 712 ∗
             memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
             memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
             memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
             ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
             ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
             ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
             v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
             vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
             v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
             memRegion (fsp + 1072#64) 192 ∗
             v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             A.pool lim (M.stepEvents evs1 st) s3 ∗ RestRO)) =
          (((fsp + 1040#64) ↦₆₄ d_w8) ∗ ((fsp + 1048#64) ↦₆₄ d_w16) ∗
           ((fsp + 1056#64) ↦₆₄ d_w24) ∗ ((fsp + 1064#64) ↦₆₄ d_w32) ∗
           memRegion (fsp + 1848#64) 40 ∗
           A.pool lim (M.stepEvents evs1 st) s3 ∗ Frame9328_some) := by
        rw [hdec_words]; dsimp only [Frame9328_some]; sep_ac_rfl
      refine SepWP.weaken_pre (Entails.of_eq hpre9328_some) ?_
      refine seq_clean_lscl_st hcl3
        (mid := lsmpl.base 333 + 9384#64)
        (P_mid := fun s4 =>
          ((fsp + 1040#64) ↦₆₄ d_w8) ∗ ((fsp + 1048#64) ↦₆₄ d_w16) ∗
          ((fsp + 1056#64) ↦₆₄ d_w24) ∗ ((fsp + 1064#64) ↦₆₄ d_w32) ∗
          ((fsp + 1848#64) ↦₆₄ d_w0) ∗ ((fsp + 1856#64) ↦₆₄ d_w8) ∗
          ((fsp + 1864#64) ↦₆₄ d_w16) ∗ ((fsp + 1872#64) ↦₆₄ d_w24) ∗
          ((fsp + 1880#64) ↦₆₄ d_w32) ∗
          A.pool lim (M.stepEvents evs1 st) s4 ∗ Frame9328_some)
        (Q := fun s4 =>
          VmPreserved s3 s4 ∧
          s4.sp = fsp ∧ s4.readReg64 .x0 = fsp + 1888#64 ∧
          s4.readReg64 .x1 = fsp + 1848#64 ∧ s4.readReg64 .x19 = out ∧
          s4.readReg64 .x20 = (loByte (v1_wordAt bs.val 0)).zeroExtend 64 ∧
          s4.readReg64 .x21 = fsp + 1392#64 ∧ s4.readReg64 .x22 = fsp + 1888#64 ∧
          s4.readReg64 .x23 = fsp + 848#64 ∧ s4.readReg64 .x25 = fsp + 1792#64 ∧
          s4.readReg64 .x26 = u8 ∧ s4.readReg64 .x28 = u80 ∧ TraceCalleeSaved s4 s0)
        (v2hse3_copy_dec_9328_to_9384_placed_budget A lim (M.stepEvents evs1 st) (ext := ext)
          s0 s3 fsp out ((loByte (v1_wordAt bs.val 0)).zeroExtend 64) (fsp + 1392#64) u8 u80
          d_w0 d_w8 d_w16 d_w24 d_w32 Frame9328_some
          hfsp_align hd_w0_lt hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx25_3 hx26_3 hx28_3 hpstate3 htr3) ?_
      intro s4 hpc4 hrun4 hcl4 ⟨_hvm4, hsp4, hx0_4, hx1_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hx26_4, hx28_4, htr4⟩
      have hproto_dec := v2hsh_protoPolyDecoder_pack A.repAlloc (fsp + 1848#64)
        (pbToProtoPolyDecoder pbDec) d_w0 d_w8 d_w16 d_w24 d_w32
      simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hproto_dec
      let Rest9384 : SepProp :=
        ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
        ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
        ((fsp + 1064#64) ↦₆₄ d_w32) ∗
        ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
        ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 240#64) 24 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1344#64) 48 ∗
        memRegion (fsp + 2288#64) 16 ∗ memRegion (fsp + 264#64) 712 ∗
        memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
        memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
        memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ RestRO
      have hpre9384 :
          (((fsp + 1040#64) ↦₆₄ d_w8) ∗ ((fsp + 1048#64) ↦₆₄ d_w16) ∗
            ((fsp + 1056#64) ↦₆₄ d_w24) ∗ ((fsp + 1064#64) ↦₆₄ d_w32) ∗
            ((fsp + 1848#64) ↦₆₄ d_w0) ∗ ((fsp + 1856#64) ↦₆₄ d_w8) ∗
            ((fsp + 1864#64) ↦₆₄ d_w16) ∗ ((fsp + 1872#64) ↦₆₄ d_w24) ∗
            ((fsp + 1880#64) ↦₆₄ d_w32) ∗
            A.pool lim (M.stepEvents evs1 st) s4 ∗ Frame9328_some) ⊢
          stackAt fsp encoderFromPbStack ∗
            memRegion (fsp + 1888#64) polyDecoderSize ∗
            protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) (pbToProtoPolyDecoder pbDec) ∗
            A.pool lim (M.stepEvents evs1 st) s4 ∗ Rest9384 := by
        dsimp only [Frame9328_some, Rest9384, polyDecoderSize]
        refine Entails.trans (Entails.of_eq (show _ =
          ((((fsp + 1848#64) ↦₆₄ d_w0) ∗ ((fsp + 1856#64) ↦₆₄ d_w8) ∗
            ((fsp + 1864#64) ↦₆₄ d_w16) ∗ ((fsp + 1872#64) ↦₆₄ d_w24) ∗
            ((fsp + 1880#64) ↦₆₄ d_w32)) ∗
           v2hs_optProtoDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder pbDec)) d_w0 d_w8 d_w16 d_w24 d_w32) ∗
          (stackAt fsp encoderFromPbStack ∗
           memRegion (fsp + 1888#64) 400 ∗ A.pool lim (M.stepEvents evs1 st) s4 ∗
           (((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
            ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
            ((fsp + 1064#64) ↦₆₄ d_w32) ∗
            ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
            ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
            ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
            memRegion (fsp + 240#64) 24 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
            P_enc_heap ∗
            memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1344#64) 48 ∗
            memRegion (fsp + 2288#64) 16 ∗ memRegion (fsp + 264#64) 712 ∗
            memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
            memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
            memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
            ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
            ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
            ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
            v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
            vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
            v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (fsp + 1072#64) 192 ∗
            v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ RestRO)) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hproto_dec) (Entails.of_eq (by sep_ac_rfl))
      refine SepWP.weaken_pre hpre9384 ?_
      have hfits_dec : FitsEnv M lim (M.stepEvents evs1 st) (FromPbDecAllocEnv (pbToProtoPolyDecoder pbDec)) :=
        fitsEnv_decoderAlloc_of_headerSentSomeEnc9036Env henc_res hrec hfits hevs1
      refine v2hsh_decoder_call_9384_sepWP_placed hdec_ok_ext (M.stepEvents evs1 st)
        s0 s4 (s0.readReg64 .x30) fsp out
        ((loByte (v1_wordAt bs.val 0)).zeroExtend 64) (fsp + 1392#64) u8 u80
        (pbToProtoPolyDecoder pbDec) Rest9384 _ hcl4 hfsp_align hfits_dec
        hpc4 hrun4 hsp4 hx0_4 hx1_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4 hx26_4 hx28_4 htr4 ?_
      intro evs2 s5 hevs2 hpc5 hrun5 hcl5 ⟨hsp5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx25_5, hx26_5, hx28_5, htr5⟩
      cases hdec_res : decoderFromPbResult (pbToProtoPolyDecoder pbDec) with
      | error err =>
        have herr := v2hsh_branch_err_dec_9388_placed (F := F) hA (M.stepEvents evs2 (M.stepEvents evs1 st))
          s0 s5 out u auth
          u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
          d_w0 d_w8 d_w16 d_w24 d_w32 w8_e w16_e w24_e hi32 bs tail368
          enc err P_enc_heap RestRO
          (hsplit_all (fsp + 1392#64)) (hreloc_all (fsp + 1392#64))
          hdk_len hu24 hu48 hu72 hu80 hcl5 hsp0_align hpc5 hrun5 hsp5 hx19_5 htr5
        refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [Rest9384, fsp]))
          (SepWP.mono herr fun sf Pf _ _ ⟨evs_f, hfree, hPf, hspf, hcsf, htrf⟩ => ?_)
        refine ⟨⟨(evs1 ++ evs2) ++ evs_f,
          headerSentSomeEncOptEnv_of_some henc
            (headerSentSomeEnc9036Env_append_freeOnly
              (headerSentSomeEnc9036Env_of_some_dec henc_res hrec hevs1 hevs2) hfree),
          ?_⟩, hspf, hcsf, htrf⟩
        simp only [M.stepEvents_append]
        exact Entails.trans hPf (Entails.of_eq (by dsimp only [RestRO]; sep_ac_rfl))
      | ok dec =>
        rw [hu80] at hx28_5
        have hok := v2hsh_branch_ok_dec_9388_placed (F := F) hA (M.stepEvents evs2 (M.stepEvents evs1 st))
          s0 s5 out u auth
          u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
          d_w0 d_w8 d_w16 d_w24 d_w32 w8_e w16_e w24_e hi32 bs tail368
          enc dec P_enc_heap RestRO
          (hsplit_all (fsp + 1392#64)) (hreloc_all (out + 8#64))
          hdk_len hu24 hu48 hu72 hu80 hsp0_align hpc5 hrun5 hsp5
          hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx25_5 hx26_5 hx28_5 htr5
        refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [Rest9384, fsp]))
          (SepWP.mono hok fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf, _hvmf⟩ => ?_)
        refine ⟨⟨evs1 ++ evs2,
          headerSentSomeEncOptEnv_of_some henc
            (headerSentSomeEnc9036Env_of_some_dec henc_res hrec hevs1 hevs2),
          ?_⟩, hspf, hcsf, htrf⟩
        rw [M.stepEvents_append]
        exact Entails.trans hPf (Entails.of_eq (by dsimp only [RestRO]; sep_ac_rfl))

theorem v2hstop_some_enc_9036_to_ret_sepWP_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec_ok_ext : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    v2hstop_SomeEnc9036SepWPHypPlaced M A lim F ext s :=
  v2hstop_some_enc_9036_to_ret_sepWP_placed hA (encoder_from_pb_ok_of_alloc_placed hA) hdec_ok_ext s

/-- Proves `v2hstop_SomeEnc9036HypPlaced` (`SepWPp` interface): from `+9036`
    (`sendingEk = some pbEnc`) to `s0.x30` under `RustCliAllocBudget M`. -/
theorem v2hstop_some_enc_9036_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc_ok : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec_ok_ext : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    v2hstop_SomeEnc9036HypPlaced M A lim F ext s :=
  v2hstop_someEnc9036HypPlacedOfEnv_of_sepWP
    (v2hstop_some_enc_9036_to_ret_sepWP_placed hA henc_ok hdec_ok_ext s)

theorem v2hstop_some_enc_9036_to_ret_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec_ok_ext : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    v2hstop_SomeEnc9036HypPlaced M A lim F ext s :=
  v2hstop_someEnc9036HypPlacedOfEnv_of_sepWP
    (v2hstop_some_enc_9036_to_ret_sepWP_of_alloc_placed hA hdec_ok_ext s)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsjPlacedBudget
