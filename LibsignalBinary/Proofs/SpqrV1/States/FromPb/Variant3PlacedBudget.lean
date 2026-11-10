/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlacedBudgetAux
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 3 (`Ct1Received`, `+692`)

Total-correctness relocatable Block-`333` theorems and `subroutine_ok` contracts for
`InnerState.ct1Received` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsProg_333 lsmpl sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (pbToProtoPolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize protoChunkedCt1ReceivedAt protoInnerStateAt protoUnchunkedEkSentCt1ReceivedAt)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved cell0_2296_entails_memRegion_2304 optEncoderPtsBound resultChunkedStatesAt spqrErrorByte statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack v1StatePtsBound v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt v1_ucWordsAt v1_uc_and_enc_words_eq_pb128 v3_collapse_1392_ucWords_1496 v3_collapse_896_104_392_ucWords_1496 v3_collapse_pbA_112_224 v3_collapse_pbA_tag_ucWords_112 v3_optProtoUcHeap_some_cap_lt v3_split_1392_896 v3_split_2304_692 v3_split_752_1888 v3_stackAt_encoder_split_ekSent v3cr_bv_add_add_lit v3cr_chunkedCt1ReceivedAt_unpack v3cr_optProtoPolyEncoderAt_pack v3cr_optProtoUcHeap v3cr_protoUc_pack v3cr_states_from_pb_ct1Received_uc_none_eq)
open CryptoVerification.SpqrV1.Unchunked (ekSentCt1ReceivedFromPbStack ekSentCt1ReceivedResultAt extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget seq_clean_lscl_st)

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudget

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (encoder_from_pb_ok_of_alloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudgetAux
  (Ct1ReceivedFromPbAllocEnv Ct1ReceivedFromPbEnv Ct1ReceivedTailEnv Ct1ReceivedTailFits
   ct1ReceivedAllocEnv_imp_ct1ReceivedEnv ct1ReceivedEnv_of_tail ct1ReceivedEnv_sub_statesFromPbEnv
   ct1ReceivedTailFits_of_ct1ReceivedAllocEnv fitsEnv_alloc_of_ct1ReceivedEnv
   fitsEnv_alloc_of_statesFromPbEnv fitsEnv_ekPre_of_ct1ReceivedAllocEnv
   v3_ct1Received_post_uc_860_placed v3_ct1Received_post_uc_860_placed_sepWP
   v3_sepWP_call_lscl_cl v3cr_copy_pb_692_none_placed_budget
   v3cr_copy_pb_692_some_placed_budget v3cr_copy_uc_to_call_784_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
  (v3cr_states_from_pb_err_4176_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
  (EkSentCt1ReceivedFromPbPlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlacedBudgetAux
  (v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (EkSentCt1ReceivedFromPbPostEnv ekSentCt1ReceivedFromPb ekSentCt1ReceivedFromPbSpec)

export Variant3PlacedBudgetAux
  (Ct1ReceivedFromPbAllocEnv Ct1ReceivedFromPbEnv Ct1ReceivedTailEnv Ct1ReceivedTailFits
   ct1ReceivedAllocEnv_imp_ct1ReceivedEnv)
export Variant3PlacedBudgetAux
  (fitsEnv_alloc_of_ct1ReceivedEnv fitsEnv_alloc_of_statesFromPbEnv
   ct1ReceivedEnv_sub_statesFromPbEnv
   v3_ct1Received_post_uc_860_placed_sepWP v3_ct1Received_post_uc_860_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v3cr_bv_add_add_lit

/-! ## Entry-to-Exit Proof for Variant 3 (`Ct1Received`, `+692 -> s0.x30`, `SepWP` & `SepWPp`) -/

set_option maxHeartbeats 1200000 in
/-- Total-correctness (`SepWP`) entry-to-exit proof for Variant 3 (`Ct1Received`) from `+692`
    (`lsmpl.base 333 + 692`) to `s0.x30` under `RustCliAllocBudget M`. -/
theorem states_from_pb_ct1Received_692_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEk : Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt M A lim F ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hfits : FitsEnv M lim st (Ct1ReceivedFromPbAllocEnv F s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.ct1Received s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct1ReceivedFromPbEnv F s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases s with | mk uc sendingEk =>
  have hpts_fn : ∀ pbEnc, sendingEk = some pbEnc → ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555 := by
    intro pbEnc henc
    dsimp only at hpts
    rw [henc] at hpts
    exact hpts
  dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  refine SepWP.weaken_pre (Entails.trans
    (sepConj_mono_right (sepConj_mono (v3_split_2304_692 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_left
          (v3cr_chunkedCt1ReceivedAt_unpack A.repAlloc pbA ⟨uc, sendingEk⟩))))))))
    (Entails.of_eq (by sep_ac_rfl))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun e0 => SepWP.exists_elim fun e8 =>
    SepWP.exists_elim fun e16 => SepWP.exists_elim fun e24 =>
    SepWP.exists_elim fun e32 => SepWP.exists_elim fun e40 =>
    SepWP.exists_elim fun e48 =>
    SepWP.exists_elim fun d8 => SepWP.exists_elim fun d16 =>
    SepWP.exists_elim fun d24 => SepWP.exists_elim fun d32 =>
    SepWP.exists_elim fun d40 => SepWP.exists_elim fun d48 =>
    SepWP.exists_elim fun d56 => SepWP.exists_elim fun d64 =>
    SepWP.exists_elim fun d72 => SepWP.exists_elim fun d80 =>
    SepWP.exists_elim fun d88 => SepWP.exists_elim fun d96 =>
    SepWP.exists_elim fun d104 =>
    SepWP.exists_elim fun u8 => SepWP.exists_elim fun u16 =>
    SepWP.exists_elim fun u24 => SepWP.exists_elim fun u32 =>
    SepWP.exists_elim fun u40 => SepWP.exists_elim fun u48 =>
    SepWP.exists_elim fun u56 => SepWP.exists_elim fun u64 =>
    SepWP.exists_elim fun u72 => SepWP.exists_elim fun u80 =>
    SepWP.exists_elim fun u88 => SepWP.exists_elim fun u96 =>
    SepWP.exists_elim fun u104 =>
    SepWP.exists_elim fun w0 => SepWP.exists_elim fun w8 =>
    SepWP.exists_elim fun w16 => SepWP.exists_elim fun w24 =>
    SepWP.exists_elim fun w32 => SepWP.exists_elim fun w40 =>
    SepWP.exists_elim fun w48 => ?_
  rw [← v1_uc_and_enc_words_eq_pb128]
  cases uc with
  | none =>
    dsimp only [v3cr_optProtoUcHeap]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜u8 = noneCap⌝ ∗
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗
       A.pool lim st s1 ∗
       ((pbA ↦₆₄ 0x8000000000000003#64) ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun hu8 => ?_
    subst hu8
    have h692 := v3cr_copy_pb_692_none_placed_budget A lim st (ext := ext) s1
      (s0.sp - 2400#64) out pbA
      u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      w0 w8 w16 w24 w32 w40 w48
      d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
      e0 e8 e16 e24 e32 e40 e48
      ((pbA ↦₆₄ 0x8000000000000003#64) ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 1392 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt)
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx27_1
    refine seq_clean_lscl_st hcl1
      (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h692) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx19_2, hx22_2, htr2⟩
    have h1496 := v3_collapse_1392_ucWords_1496 (s0.sp - 2400#64)
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hpack_enc := v3cr_optProtoPolyEncoderAt_pack A.repAlloc (s0.sp - 2400#64 + 1496#64)
      (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
    have hpb112 := v3_collapse_pbA_tag_ucWords_112 pbA 0x8000000000000003#64
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hpb224 := Entails.trans (sepConj_mono_left hpb112)
      (v3_collapse_pbA_112_224 pbA w0 w8 w16 w24 w32 w40 w48)
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48) ∗
      (((pbA ↦₆₄ 0x8000000000000003#64) ∗
        v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s2) by sep_ac_rfl))
      (Entails.trans (sepConj_mono h1496 (sepConj_mono hpack_enc (sepConj_mono_left hpb224)))
        (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 1496 ∗
          optProtoPolynomialEncoderAt A.repAlloc (s0.sp - 2400#64 + 1496#64)
            (sendingEk.map pbToProtoPolyEncoder) ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool lim st s2 ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)))) ?_
    have hx22_byte : (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx22_2]; rfl
    have herr := Variant3bPlacedBudget.v3cr_states_from_pb_err_4176_placed (F := F) hA st s0 s2 hcl2 out .stateDecode
      sendingEk (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_byte (htr2.trans htr1)
    refine SepWP.mono herr fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
    refine ⟨⟨evs, hevs, Entails.trans hPf ?_⟩, hsp_f, hcs_f, htr_f⟩
    rw [v3cr_states_from_pb_ct1Received_uc_none_eq sendingEk]
    exact Entails.of_eq (by sep_ac_rfl)
  | some u =>
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v3cr_optProtoUcHeap A.repAlloc (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗
       A.pool lim st s1 ∗
       ((pbA ↦₆₄ 0x8000000000000003#64) ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt)) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (v3_optProtoUcHeap_some_cap_lt A.repAlloc u
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104))
        (Entails.of_eq (by sep_ac_rfl)))) ?_
    refine SepWP.pure_elim fun hu8_lt => ?_
    have h692 := v3cr_copy_pb_692_some_placed_budget A lim st (ext := ext) s1
      (s0.sp - 2400#64) out pbA
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      w0 w8 w16 w24 w32 w40 w48
      d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
      e0 e8 e16 e24 e32 e40 e48
      (v3cr_optProtoUcHeap A.repAlloc (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       (pbA ↦₆₄ 0x8000000000000003#64) ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 1392 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt)
      hfsp_align hu8_lt hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1
    refine seq_clean_lscl_st hcl1
      (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h692) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx8_2, hx19_2, hx23_2, hx25_2, hx27_2, _hx29_2, htr2⟩
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      memRegion (s0.sp - 2400#64) 1392 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v3cr_optProtoUcHeap A.repAlloc (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       (pbA ↦₆₄ 0x8000000000000003#64) ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s2) by sep_ac_rfl))
      (sepConj_mono (v3_split_1392_896 (s0.sp - 2400#64))
        (sepConj_mono_left (v3_split_752_1888 (s0.sp - 2400#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun c8 => SepWP.exists_elim fun c16 =>
      SepWP.exists_elim fun c24 => SepWP.exists_elim fun c32 =>
      SepWP.exists_elim fun c40 => SepWP.exists_elim fun c48 =>
      SepWP.exists_elim fun c56 => SepWP.exists_elim fun c64 =>
      SepWP.exists_elim fun c72 => SepWP.exists_elim fun c80 =>
      SepWP.exists_elim fun c88 => SepWP.exists_elim fun c96 =>
      SepWP.exists_elim fun c104 => ?_
    have huc1392_split :
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 =
          ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
           ((s0.sp - 2400#64 + 1408#64) ↦₆₄ u24) ∗
           ((s0.sp - 2400#64 + 1416#64) ↦₆₄ u32) ∗
           ((s0.sp - 2400#64 + 1424#64) ↦₆₄ u40) ∗
           ((s0.sp - 2400#64 + 1432#64) ↦₆₄ u48) ∗
           ((s0.sp - 2400#64 + 1440#64) ↦₆₄ u56) ∗
           ((s0.sp - 2400#64 + 1448#64) ↦₆₄ u64) ∗
           ((s0.sp - 2400#64 + 1456#64) ↦₆₄ u72) ∗
           ((s0.sp - 2400#64 + 1464#64) ↦₆₄ u80) ∗
           ((s0.sp - 2400#64 + 1472#64) ↦₆₄ u88) ∗
           ((s0.sp - 2400#64 + 1480#64) ↦₆₄ u96) ∗
           ((s0.sp - 2400#64 + 1488#64) ↦₆₄ u104)) := by
      unfold v1_ucWordsAt
      simp only [arm64_norm]
      sep_ac_rfl
    have h784 := v3cr_copy_uc_to_call_784_placed_budget A lim st (ext := ext) s2
      (s0.sp - 2400#64) out pbA
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104
      ((((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 1408#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 1416#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 1424#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 1432#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1440#64) ↦₆₄ u56) ∗
        ((s0.sp - 2400#64 + 1448#64) ↦₆₄ u64) ∗
        ((s0.sp - 2400#64 + 1456#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 1464#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1472#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 1480#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 1488#64) ↦₆₄ u104)) ∗
       memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
       memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
       memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
       (pbA ↦₆₄ 0x8000000000000003#64) ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v3cr_optProtoUcHeap A.repAlloc (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt)
      hfsp_align hpc2 hrun2 hsp2 hx8_2 hx19_2 hx23_2 hx25_2 hx27_2
    refine seq_clean_lscl_st hcl2
      (SepWP.weaken_pre (Entails.of_eq (by rw [huc1392_split]; sep_ac_rfl)) h784) ?_
    intro s3 hpc3 hrun3 hcl3 ⟨_hvm3, hsp3, hx0_3, hx1_3, hx19_3, hx23_3, hx25_3, hx27_3, _hx29_3, hx30_3, htr3⟩
    have hpack_uc := v3cr_protoUc_pack A.repAlloc (s0.sp - 2400#64 + 896#64) u
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hpb112 := v3_collapse_pbA_tag_ucWords_112 pbA 0x8000000000000003#64
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    rw [v3_stackAt_encoder_split_ekSent (s0.sp - 2400#64)]
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (v1_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v3cr_optProtoUcHeap A.repAlloc (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      ((pbA ↦₆₄ 0x8000000000000003#64) ∗
        v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      (((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
       (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 1408#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 1416#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 1424#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 1432#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1440#64) ↦₆₄ u56) ∗
        ((s0.sp - 2400#64 + 1448#64) ↦₆₄ u64) ∗
        ((s0.sp - 2400#64 + 1456#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 1464#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1472#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 1480#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 1488#64) ↦₆₄ u104))) ∗
      (memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
       A.pool lim st s3 ∗
       stackAt (s0.sp - 2400#64) ekSentCt1ReceivedFromPbStack ∗
       memRegion (s0.sp - 2400#64 - 5152#64) 848 ∗
       memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
       memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
      (Entails.trans (sepConj_mono hpack_uc (sepConj_mono_left hpb112))
        (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
           protoUnchunkedEkSentCt1ReceivedAt A.repAlloc (s0.sp - 2400#64 + 896#64) u ∗
           A.pool lim st s3 ∗
           stackAt s3.sp ekSentCt1ReceivedFromPbStack) ∗
          (memRegion (s0.sp - 2400#64 - 5152#64) 848 ∗
           memRegion (s0.sp - 2400#64) 896 ∗
           memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
           v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
           memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
           memRegion pbA 112 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 168#64) 56 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           statesFromPbJumpTablePlacedAt) by rw [hsp3, huc1392_split]; sep_ac_rfl)))) ?_
    have hs3_align : s3.spAligned = true := by
      simp only [State.spAligned, hsp3, hfsp_align]
    have htr3_0 : TraceCalleeSaved s3 s0 := htr3.trans (htr2.trans htr1)
    have hpre_ek :
        (memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
         protoUnchunkedEkSentCt1ReceivedAt A.repAlloc (s0.sp - 2400#64 + 896#64) u ∗
         A.pool lim st s3 ∗
         stackAt s3.sp ekSentCt1ReceivedFromPbStack) ⊢
        (LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPbSpec M A lim F).pre
          (⟨s0.sp - 2400#64 + 1888#64, s0.sp - 2400#64 + 896#64, u⟩, st) s3 := by
      dsimp only [LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPbSpec,
        LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPbSpecOfEnv]
      exact Entails.pure_right
        ⟨hx0_3, hx1_3, fitsEnv_ekPre_of_ct1ReceivedAllocEnv hfits,
          by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .x30); rw [show s3.readReg64 .x30 = _ from hx30_3]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩
        (Entails.refl _)
    refine v3_sepWP_call_lscl_cl hEk
      (x := (⟨s0.sp - 2400#64 + 1888#64, s0.sp - 2400#64 + 896#64, u⟩, st))
      hcl3 hpc3 hrun3 hs3_align hx30_3 hpre_ek (hnext := ?_)
    intro s4 hpc4 hrun4 hcl4 hsp4 hcs4
    dsimp only [LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPbSpec,
      LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPbSpecOfEnv]
    rw [hsp3] at hsp4 ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun evs_uc => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜s4.trace = s3.trace⌝ ∗
      (⌜EkSentCt1ReceivedFromPbPostEnv F u evs_uc⌝ ∗
       ((stackAt (s0.sp - 2400#64) ekSentCt1ReceivedFromPbStack ∗
         memRegion (s0.sp - 2400#64 - 5152#64) 848) ∗
        (memRegion (s0.sp - 2400#64) 896 ∗
         memRegion (s0.sp - 2400#64 + 896#64) 104 ∗
         memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
         v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
        ekSentCt1ReceivedResultAt A.repAlloc (F := F) (s0.sp - 2400#64 + 1888#64)
          (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
        memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingEk.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_uc st) s4)) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun htr4 => SepWP.pure_elim fun henv_uc => ?_
    rw [← v3_stackAt_encoder_split_ekSent (s0.sp - 2400#64)]
    have h1496 := v3_collapse_896_104_392_ucWords_1496 (s0.sp - 2400#64)
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left h1496)) ?_
    have hx19_4 : s4.readReg64 .x19 = out := (hcs4.1).trans hx19_3
    have hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 :=
      (hcs4.2.2.2.2.1).trans hx23_3
    have hx25_4 : s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 :=
      (hcs4.2.2.2.2.2.2.1).trans hx25_3
    have hx27_4 : s4.readReg64 .x27 = pbA :=
      (hcs4.2.2.2.2.2.2.2.2.1).trans hx27_3
    have hfits_tail : Ct1ReceivedTailFits M lim (M.stepEvents evs_uc st) F u sendingEk :=
      ct1ReceivedTailFits_of_ct1ReceivedAllocEnv hfits henv_uc
    have h860 := v3_ct1Received_post_uc_860_placed_sepWP hA hEnc (M.stepEvents evs_uc st)
      s0 s4 hcl4 out pbA u sendingEk
      w0 w8 w16 w24 w32 w40 w48 hpts_fn hfits_tail hsp0_align hpc4 hrun4 hsp4
      hx19_4 hx23_4 hx25_4 hx27_4 ⟨htr4.trans htr3_0.1, hcs4.2.2.2.2.2.2.2.2.2.2.2.trans htr3_0.2⟩
    refine SepWP.mono h860 fun sf Pf _ _ ⟨⟨evs_tail, htail, hPf⟩, hsp_f, hcs_f, htr_f⟩ => ?_
    rw [← M.stepEvents_append] at hPf
    exact ⟨⟨evs_uc ++ evs_tail, ct1ReceivedEnv_of_tail henv_uc htail, hPf⟩, hsp_f, hcs_f, htr_f⟩

theorem states_from_pb_ct1Received_692_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEk : Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt M A lim F ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received) (onPanic : State → SepProp → Prop)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hfits : FitsEnv M lim st (Ct1ReceivedFromPbAllocEnv F s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.ct1Received s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct1ReceivedFromPbEnv F s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)
      onPanic :=
  SepWPp.of_sepWP_ret
    (states_from_pb_ct1Received_692_placed_sepWP hA hEk hEnc st s0 s1 hcl1 out pbA s
      hpts hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1 htr1)

/-! ## `withLsCodeLoaded` Tagged-Variant Dispatch & `subroutine_ok` Contracts -/

/-- Lift a Variant-3 (`InnerState.ct1Received`, `+692`) `SepWP` step (receiving both `x23` and `x25`
    from `states_from_pb_dispatch_tagged_placed_budget`) to `subroutine_ok` for
    `withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpecOfEnv ...)`. -/
theorem sfpProof_ct1Received_ok_of_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received} {Env : List AllocEvent → Prop}
    (hstep : ∀ (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64),
      v1StatePtsBound { innerState := some (.ct1Received s) } →
      FitsEnv M lim st Env →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s0.sp &&& 15#64 == 0#64) = true →
      s1.pc = lsmpl.base 333 + 692#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 2400#64 →
      s1.readReg64 .x19 = out →
      s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
      s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 →
      s1.readReg64 .x27 = pbA →
      TraceCalleeSaved s1 s0 →
      SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          optProtoInnerStateAt A.repAlloc pbA (some (.ct1Received s)) ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim st s1)
        (fun sf Pf =>
          (∃ evs : List AllocEvent, Env evs ∧
            (Pf ⊢
              resultChunkedStatesAt A.repAlloc (F := F) out
                (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                  { innerState := some (.ct1Received s) }) ∗
              memRegion pbA optProtoInnerStateSize ∗
              statesFromPbJumpTablePlacedAt ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct1Received s) } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [DefsBudget.statesFromPbVariantPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.ct1Received s)) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  refine DefsBudget.sepWPp_of_states_exit_cl_placed st s0 s0 out pbA
    { innerState := some (.ct1Received s) } Env _ R ?_
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some (.ct1Received s)) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWP_seq_lscl hcl0
    (SepWP.mono hpro fun s1 P1 hpc1 hrun1 ⟨hP1, hsp1, _, hx8_1, hx0_1, htr1, _⟩ hcl1 => ?_)
  have htag_eq : optProtoInnerStateAt A.repAlloc pbA (some (.ct1Received s)) =
      (pbA ↦₆₄ 0x8000000000000003#64) ∗
      (protoChunkedCt1ReceivedAt A.repAlloc (pbA + 8#64) s ∗
       memRegion (pbA + 168#64) 56) := rfl
  have hP1' : P1 ⊢
      (pbA ↦₆₄ 0x8000000000000003#64) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (protoChunkedCt1ReceivedAt A.repAlloc (pbA + 8#64) s ∗
        memRegion (pbA + 168#64) 56)) ∗
      A.pool lim st s1 := by
    refine Entails.trans hP1 ?_
    rw [htag_eq]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hP1' ?_
  have hdisp := Variant1bPlacedBudgetAux.states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA 0x8000000000000003#64 692#64
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     (protoChunkedCt1ReceivedAt A.repAlloc (pbA + 8#64) s ∗
      memRegion (pbA + 168#64) 56))
    CryptoVerification.SpqrV1.States.FromPb.TaggedVariantDispatch.ct1Received hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWP_seq_lscl hcl1
    (SepWP.mono hdisp fun s2 P2 hpc2 hrun2
      ⟨hP2, hsp2, hx19_2, hx27_2, _, hx25_2, _, _, hx23_2, htr2, _⟩ hcl2 => ?_)
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hx25_2' : s2.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 := by
    rw [hx25_2]; bv_omega
  have hpre_join : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some (.ct1Received s)) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    refine Entails.trans hP2 ?_
    rw [htag_eq]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ 0x8000000000000003#64) ∗
        (protoChunkedCt1ReceivedAt A.repAlloc (pbA + 8#64) s ∗
         memRegion (pbA + 168#64) 56)) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  exact SepWP.weaken_pre hpre_join
    (hstep st s0 s2 out pbA hpts hfits hcl2 hsp0_align hpc2 hrun2 hsp2
      hx19_2 hx23_2' hx25_2' hx27_2 htr2)

/-- Envelope-parametric `subroutine_ok` for Variant 3 (`InnerState.ct1Received`) with
    `withLsCodeLoaded` under any `Env` with `Ct1ReceivedFromPbEnv F s ⊆ Env` and
    `FitsEnv Env → FitsEnv (Ct1ReceivedFromPbAllocEnv F s)`. -/
theorem states_from_pb_ct1Received_placed_ok_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEk : Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt M A lim F ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received)
    (halloc_fit : ∀ st : M.σ, FitsEnv M lim st Env →
      FitsEnv M lim st (Ct1ReceivedFromPbAllocEnv F s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → Ct1ReceivedFromPbEnv F s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct1Received s) } Env)) := by
  refine sfpProof_ct1Received_ok_of_step_cl_placed ?_
  intro st s0 s1 out pbA hpts hfits hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1 htr1
  dsimp only [v1StatePtsBound] at hpts
  have h692 := states_from_pb_ct1Received_692_placed_sepWP hA hEk hEnc st s0 s1 hcl1 out pbA s
    hpts (halloc_fit st hfits) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1 htr1
  exact SepWP.mono h692 fun sf Pf _ _ ⟨⟨evs, hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩ =>
    ⟨⟨evs, hsub st hfits hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩

/-- `subroutine_ok` for Variant 3 (`InnerState.ct1Received`) under its tight envelope
    `Ct1ReceivedFromPbEnv F s`. -/
theorem states_from_pb_ct1Received_placed_ok_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEk : Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt M A lim F ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct1Received s) } (Ct1ReceivedFromPbEnv F s))) :=
  states_from_pb_ct1Received_placed_ok_of_env hA hEk hEnc s
    (fun _ h => fitsEnv_alloc_of_ct1ReceivedEnv h)
    (fun _ _ _ h => h)

/-- `subroutine_ok` for Variant 3 (`InnerState.ct1Received`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`), parameterized by `hA` and `hEnc`. -/
theorem states_from_pb_ct1Received_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.ct1Received s) })) :=
  states_from_pb_ct1Received_placed_ok_of_env hA
    (Variant4cPlacedBudgetAux.v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok hA) hEnc s
    (fun _ h => fitsEnv_alloc_of_statesFromPbEnv s h)
    (fun _ _ hfits hevs => ct1ReceivedEnv_sub_statesFromPbEnv s hfits hevs)

/-- `subroutine_ok` for Variant 3 (`InnerState.ct1Received`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`), discharged from `FromPbAllocHooksBudget`
    alone via `v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok` and
    `encoder_from_pb_ok_of_alloc_placed`. -/
theorem states_from_pb_ct1Received_ok_ext_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.ct1Received s) })) :=
  states_from_pb_ct1Received_ok_ext_placed hA
    (Variant2aPlacedBudgetAux.encoder_from_pb_ok_of_alloc_placed hA) s

abbrev states_from_pb_variant2_placed := @states_from_pb_ct1Received_ok_ext_placed
abbrev states_from_pb_variant2_of_alloc_placed := @states_from_pb_ct1Received_ok_ext_of_alloc_placed

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudget
