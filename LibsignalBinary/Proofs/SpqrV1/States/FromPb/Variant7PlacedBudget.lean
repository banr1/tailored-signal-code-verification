/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7kPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7dPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7gPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, `+1056`, Block `333`)

Total-correctness (`SepWP`) relocatable stage compositions (`+3552`, `+3480`) and top-level
`subroutine_ok` contracts for Variant 7 (`InnerState.ct1Sampled`) of
`<spqr::v1::chunked::states::States>::from_pb` under `Ct1SampledFromPbEnv` and `StatesFromPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsProg_333 lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder States V1State pbToProtoPolyDecoder pbToProtoPolyEncoder spqrAuthApi
   spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1Sent)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize protoChunkedCt1SampledAt
   protoInnerStateAt protoUnchunkedCt1SentAt protoUnchunkedCt1SentSize)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialEncoderAt polyEncoderSize protoPolynomialEncoderAt
   protoPolynomialEncoderSize resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (EncoderFromPbGhost encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved cell0_2296_entails_memRegion_2304 collapse_step collapse_step0 collapse_top
   optEncoderPtsBound resultChunkedStatesAt sp_sub_2400_align split_step split_step0 split_top
   spqrErrorByte statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack
   v1StatePtsBound v7_ct1SentAt_unpack v7_ct1SentHeap v7_ct1SentWordsAt
   v7_ct1Sent_from_pb_error_eq v7_from_pb_ct1Sampled_bad_pts v7_from_pb_ct1Sampled_enc_none
   v7_from_pb_ct1Sampled_uc_err v7_from_pb_ct1Sampled_uc_none v7_memRegion_1888_128_272_to_400
   v7_memRegion_1888_288_split_encDec v7_memRegion_2304_split_uc v7_memRegion_2304_unsplit_uc
   v7_memRegion_uc_rest_to_1888 v7_optDecoderCapProp v7_optEncoderCapProp
   v7_optProtoPolyDecoderTail v7_optProtoPolyDecoder_expose_cap v7_optProtoPolyEncoderTail
   v7_optProtoPolyEncoder_expose_cap v7_optProtoUnchunkedCt1SentTail
   v7_optProtoUnchunkedCt1Sent_expose_w0 v7_optUcCapProp v7_optUcCapProp_imp_or
   v7_pbA_128_56_40_to_224 v7_receivingEkPtsOk
   v7_stackAt_ct1SentFromPbStack_to_encoderFromPbStack
   v7_stackAt_encoderFromPbStack_to_ct1SentFromPbStack v7_stackGapsEncDec)
open CryptoVerification.SpqrV1.Unchunked
  (Ct1SentFromPbGhost ct1SentAt ct1SentFromPbStack ct1SentResultAt)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (statesFromPbVariantPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget
  (Ct1SentFromPbPlacedOkExt ct1_sent_from_pb_ok_of_alloc_placed
   v7_sub_ok_ct1_sent_from_pb_placed v7_sub_ok_encoder_from_pb_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7dPlacedBudget
  (v7_dispatch_ct1Sampled_placed_budget v7_entry_1056_to_3480_placed_budget
   v7_entry_bad_pts_1056_to_4632_placed v7_uc_none_3480_to_4632_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlacedBudget
  (v7_bl_ct1_sent_3548_to_15272_placed_budget v7_copy_uc_3480_to_3548_placed_budget
   v7_uc_err_3552_to_4632_placed v7_uc_ok_spill_3552_to_3652_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7gPlacedBudget
  (v7_bl_encoder_3716_to_32996_placed_budget v7_copy_enc_3652_to_3716_placed_budget
   v7_uc_ok_none_enc_3552_to_4632_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7kPlacedBudget
  (V7Ok7404PropPlaced v7_after_enc_call_3720_placed v7_ok7404Prop_holds_placed
   v7_sepWPp_call_wpp_lscl v7_sepWPp_seq_clean_lscl v7_seq_err_4632_wpp_placed)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (Ct1SentFromPbPostEnv Ct1SentFromPbPreEnv ct1SentFromPb ct1SentFromPbSpec
   ct1SentFromPbSpecOfEnv)

export Variant7PlacedBudgetAux
  (Ct1SampledUcSomeEnv Ct1SampledFromPbEnv ct1SampledFromPbEnv_sub_statesFromPbEnv
   fitsEnv_ct1SampledFromPbEnv_of_statesFromPbEnv)

open Variant7PlacedBudgetAux
  (ct1SampledFromPbEnv_of_bad_pts ct1SampledFromPbEnv_of_ucSomeEnv
   ct1SampledFromPbEnv_of_uc_none ct1SampledUcSomeEnv_of_dec_err
   ct1SampledUcSomeEnv_of_dec_none ct1SampledUcSomeEnv_of_dec_ok
   ct1SampledUcSomeEnv_of_enc_err ct1SampledUcSomeEnv_of_enc_none
   ct1SampledUcSomeEnv_of_uc_err fitsEnv_ct1SentPre_of_ucSomeEnv
   fitsEnv_decAlloc_step_of_ucSomeEnv fitsEnv_encAlloc_step_of_ucSomeEnv
   fitsEnv_ucSomeEnv_of_ct1SampledFromPbEnv)

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-- Budget-threaded stage at `+3552` after `<Ct1Sent>::from_pb` returns at `fsp + 1888..2016`. -/
theorem v7_after_uc_call_3552_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st0 : M.σ) (evs_uc : List AllocEvent)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (h7404_ok : V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s)
    (huc_env : Ct1SentFromPbPostEnv F u evs_uc)
    (hfits_uc : FitsEnv M lim st0 (Ct1SampledUcSomeEnv F u s.sendingCt1 s.receivingEk))
    (hsub_uc : ∀ {evs : List AllocEvent},
      Ct1SampledUcSomeEnv F u s.sendingCt1 s.receivingEk evs → Env evs)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (hpts_enc : optEncoderPtsBound s.sendingCt1)
    (hcap_dec : v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder))
    (hs_uc : s.uc = some u)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64)
          (Ct1Sent.from_pb (spqrAuthApi F) u) ∗
        memRegion (s0.sp - 2400#64) 1888 ∗
        memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 128 ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_uc st0) s1)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).post
              ((out, pbA), st0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).onPanic
              ((out, pbA), st0) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  cases huc : Ct1Sent.from_pb (spqrAuthApi F) u with
  | error e =>
    have he := v7_ct1Sent_from_pb_error_eq F u huc
    subst he
    have hfrom_pb := v7_from_pb_ct1Sampled_uc_err F s u .stateDecode hpts hs_uc huc
    apply v7_seq_err_4632_wpp_placed st0 s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (v7_uc_err_3552_to_4632_placed (F := F) hA s0 s1 out pbA cap_dec (.err .stateDecode)
          (s.sendingCt1.map pbToProtoPolyEncoder) (s.receivingEk.map pbToProtoPolyDecoder)
          (M.stepEvents evs_uc st0)
          (memRegion (s0.sp - 2400#64) 1888 ∗ memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗ statesFromPbJumpTablePlacedAt)
          hcl1 hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1) ?_)
    intro sm Pm _ _ ⟨evs_free, hevs_free, hPm, hspm, hx19m, hx28m, htrm⟩
    rw [← M.stepEvents_append evs_uc evs_free st0] at hPm
    refine ⟨evs_uc ++ evs_free,
      hsub_uc (ct1SampledUcSomeEnv_of_uc_err huc huc_env hevs_free),
      Entails.trans hPm ?_, hspm, hx19m, hx28m, htrm⟩
    have hstack := v7_memRegion_2304_unsplit_uc (s0.sp - 2400#64)
    have h1888_split : memRegion (s0.sp - 2400#64) 1888 ⊢
        memRegion (s0.sp - 2400#64) 240 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 128 ∗
        memRegion ((s0.sp - 2400#64) + 368#64) 1520 := by
      exact split_top <|
        split_step0 (Entails.refl _) <|
        split_step (Entails.refl _) <|
        Entails.refl _
    have hpb224 := v7_pbA_128_56_40_to_224 pbA
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1888 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
       memRegion ((s0.sp - 2400#64) + 2016#64) 288) ∗
      (memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents (evs_uc ++ evs_free) st0) sm) by sep_ac_rfl)) ?_
    have h2304 :
        memRegion (s0.sp - 2400#64) 1888 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
        memRegion ((s0.sp - 2400#64) + 2016#64) 288 ⊢ memRegion (s0.sp - 2400#64) 2304 :=
      Entails.trans (sepConj_mono_left h1888_split)
        (Entails.trans (Entails.of_eq (by sep_ac_rfl)) hstack)
    exact Entails.trans (sepConj_mono h2304 (sepConj_mono_left hpb224)) (Entails.of_eq (by sep_ac_rfl))
  | ok uc =>
    dsimp only [ct1SentResultAt]
    cases hs_enc : s.sendingCt1 with
    | none =>
      have hfrom_pb := v7_from_pb_ct1Sampled_enc_none F s u uc hpts hs_uc huc hs_enc
      simp only [Option.map]
      have hopt_enc_none :
          optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) none =
          (((pbA + 128#64) ↦₆₄ noneCap) ∗ memRegion ((pbA + 128#64) + 8#64) 48) := rfl
      rw [hopt_enc_none]
      have h1888_split :
          memRegion (s0.sp - 2400#64) 1888 ⊢
          memRegion (s0.sp - 2400#64) 1264 ∗ memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 496 := by
        exact split_top <|
          split_step0 (Entails.refl _) <|
          split_step (Entails.refl _) <|
          Entails.refl _
      apply v7_seq_err_4632_wpp_placed st0 s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          memRegion (s0.sp - 2400#64) 1888 ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           ct1SentAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) uc ∗
           memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA 128 ∗
           (((pbA + 128#64) ↦₆₄ noneCap) ∗ memRegion ((pbA + 128#64) + 8#64) 48) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
           statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs_uc st0) s1) by sep_ac_rfl))
          (Entails.trans (sepConj_mono_left h1888_split) (Entails.of_eq (by sep_ac_rfl))))
        (SepWP.mono
          (v7_uc_ok_none_enc_3552_to_4632_placed hA s0 s1 out pbA cap_dec uc
            (s.receivingEk.map pbToProtoPolyDecoder) (M.stepEvents evs_uc st0)
            (memRegion (s0.sp - 2400#64) 1264 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 496 ∗
             memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
             memRegion ((pbA + 128#64) + 8#64) 48 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             memRegion pbA 128 ∗ statesFromPbJumpTablePlacedAt)
            hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1) ?_)
      intro sm Pm _ _ ⟨evs_free, hevs_free, hPm, hspm, hx19m, hx28m, htrm⟩
      rw [← M.stepEvents_append evs_uc evs_free st0] at hPm
      have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
        rw [hx28m]; rfl
      have henv_tot : Env (evs_uc ++ evs_free) := by
        apply hsub_uc
        rw [hs_enc]
        exact ct1SampledUcSomeEnv_of_enc_none huc huc_env hevs_free
      refine ⟨evs_uc ++ evs_free, henv_tot, Entails.trans hPm ?_, hspm, hx19m, hx28_b, htrm⟩
      have h2304 :
          memRegion (s0.sp - 2400#64) 1264 ∗ memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 496 ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
          memRegion ((s0.sp - 2400#64) + 2016#64) 288 ⊢ memRegion (s0.sp - 2400#64) 2304 := by
        exact collapse_top <|
          collapse_step0 (Entails.refl _) <|
          collapse_step (Entails.refl _) <|
          collapse_step (Entails.refl _) <|
          collapse_step (Entails.refl _) <|
          Entails.refl _
      have hm56 :
          ((pbA + 128#64) ↦₆₄ noneCap) ∗ memRegion ((pbA + 128#64) + 8#64) 48 ⊢
            memRegion (pbA + 128#64) 56 := by
        rw [ProofLib.memRegion_split (pbA + 128#64) 8 48 (by decide)]
        exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (pbA + 128#64) noneCap)
      have hpb224 := v7_pbA_128_56_40_to_224 pbA
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 1264 ∗ memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 496 ∗
         memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
         memRegion ((s0.sp - 2400#64) + 2016#64) 288) ∗
        (memRegion pbA 128 ∗
         (((pbA + 128#64) ↦₆₄ noneCap) ∗ memRegion ((pbA + 128#64) + 8#64) 48) ∗
         memRegion (pbA + 184#64) 40) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗
         A.pool lim (M.stepEvents (evs_uc ++ evs_free) st0) sm) by sep_ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono h2304
          (sepConj_mono_left (Entails.trans (sepConj_mono_right (sepConj_mono_left hm56)) hpb224))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    | some e =>
      have hpts_e : ∀ bs ∈ (pbToProtoPolyEncoder e).pts, bs.length ≤ 2 * 0x0555555555555555 := by
        rw [hs_enc] at hpts_enc; exact hpts_enc
      simp only [Option.map]
      refine SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          ct1SentAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) uc ∗
          (memRegion (s0.sp - 2400#64) 1888 ∗ memRegion ((s0.sp - 2400#64) + 2016#64) 288) ∗
          optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (some (pbToProtoPolyEncoder e)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
           statesFromPbJumpTablePlacedAt ∗
           A.pool lim (M.stepEvents evs_uc st0) s1) by sep_ac_rfl))
          (sepConj_mono
            (v7_ct1SentAt_unpack A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) uc)
            (sepConj_mono (v7_memRegion_1888_288_split_encDec (s0.sp - 2400#64))
              (sepConj_mono_left
                (v7_optProtoPolyEncoder_expose_cap A.repAlloc (pbA + 128#64) (some (pbToProtoPolyEncoder e))))))) ?_
      dsimp only [v7_optEncoderCapProp]
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro cap_enc; apply SepWPp.exists_elim; intro slot200
      apply SepWPp.exists_elim; intro slot24; apply SepWPp.exists_elim; intro slot16
      apply SepWPp.exists_elim; intro c1; apply SepWPp.exists_elim; intro p1; apply SepWPp.exists_elim; intro l1
      apply SepWPp.exists_elim; intro c2; apply SepWPp.exists_elim; intro p2; apply SepWPp.exists_elim; intro l2
      apply SepWPp.exists_elim; intro c3; apply SepWPp.exists_elim; intro p3; apply SepWPp.exists_elim; intro l3
      apply SepWPp.exists_elim; intro c4; apply SepWPp.exists_elim; intro p4; apply SepWPp.exists_elim; intro l4
      apply SepWPp.exists_elim; intro c5; apply SepWPp.exists_elim; intro p5; apply SepWPp.exists_elim; intro l5
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ⌜c1.toNat < 2 ^ 63⌝ ∗
        ⌜cap_enc.toNat < 2 ^ 63⌝ ∗
        (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
         memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
         ((pbA + 128#64) ↦₆₄ cap_enc) ∗
         (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
          (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ slot24) ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
          memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
          memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
          memRegion ((s0.sp - 2400#64) + 2016#64) 272 ∗
          v7_stackGapsEncDec (s0.sp - 2400#64) ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          memRegion pbA 128 ∗
          v7_optProtoPolyEncoderTail A.repAlloc (pbA + 128#64) cap_enc (some (pbToProtoPolyEncoder e)) ∗
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs_uc st0) s1)) by sep_ac_rfl)) ?_
      apply SepWPp.pure_elim; intro hc1
      apply SepWPp.pure_elim; intro hcap_enc
      refine v7_sepWPp_seq_clean_lscl hcl1
        (mid := lsmpl.base 374)
        (P_mid := fun sm =>
          (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
           protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1792#64) (pbToProtoPolyEncoder e) ∗
           A.pool lim (M.stepEvents evs_uc st0) sm ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
          (memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
           v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
           v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           memRegion (pbA + 128#64) 56 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
           statesFromPbJumpTablePlacedAt))
        (Q_regs := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
          sm.readReg64 .x1 = (s0.sp - 2400#64) + 1792#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = (s0.sp - 2400#64) + 1792#64 ∧ sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
          sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
          sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x25 = (s0.sp - 2400#64) + 1888#64 ∧
          sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = p1 ∧
          sm.readReg64 .x30 = lsmpl.base 333 + 3720#64 ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · refine seq_clean_st
          (mid := lsmpl.base 333 + 3652#64)
          (P_mid := fun sm =>
            ((pbA + 128#64) ↦₆₄ cap_enc) ∗
            v7_optProtoPolyEncoderTail A.repAlloc (pbA + 128#64) cap_enc (some (pbToProtoPolyEncoder e)) ∗
            memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
            (((s0.sp - 2400#64) + 24#64) ↦₆₄ slot24) ∗
            (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
             v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
             v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
             (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
             memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
             memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
             v7_stackGapsEncDec (s0.sp - 2400#64) ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             memRegion pbA 128 ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
             statesFromPbJumpTablePlacedAt) ∗
            A.pool lim (M.stepEvents evs_uc st0) sm)
          (Q := fun sm =>
            sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x1 = c1 ∧ sm.readReg64 .x8 = cap_enc ∧
            sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
            sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
            sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
            sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = p1 ∧
            TraceCalleeSaved sm s0)
          ?_ ?_
        · refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (SepWP.mono
              (v7_uc_ok_spill_3552_to_3652_placed_budget (ext := ext) A lim (M.stepEvents evs_uc st0)
                s0 s1 (s0.sp - 2400#64) out pbA cap_enc cap_dec
                ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64) ((s0.sp - 2400#64) + 1792#64)
                c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
                (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
                 (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
                 (((s0.sp - 2400#64) + 24#64) ↦₆₄ slot24) ∗
                 (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
                 memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
                 memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
                 memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
                 memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
                 memRegion ((s0.sp - 2400#64) + 2016#64) 272 ∗
                 v7_stackGapsEncDec (s0.sp - 2400#64) ∗
                 statesFromPbSavedCells s0 ∗
                 memRegion out chunkedStatesSize ∗
                 memRegion pbA 128 ∗
                 v7_optProtoPolyEncoderTail A.repAlloc (pbA + 128#64) cap_enc (some (pbToProtoPolyEncoder e)) ∗
                 (((pbA + 184#64) ↦₆₄ cap_dec) ∗
                  v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
                 statesFromPbJumpTablePlacedAt)
                hfsp_align hc1 hcap_enc hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1) ?_)
          intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
          refine ⟨Entails.trans hPm ?_, hq⟩
          have h400 := v7_memRegion_1888_128_272_to_400 (s0.sp - 2400#64)
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗ memRegion ((s0.sp - 2400#64) + 2016#64) 272) ∗
            (((pbA + 128#64) ↦₆₄ cap_enc) ∗
             v7_optProtoPolyEncoderTail A.repAlloc (pbA + 128#64) cap_enc (some (pbToProtoPolyEncoder e)) ∗
             memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
             (((s0.sp - 2400#64) + 24#64) ↦₆₄ slot24) ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
             v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
             v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
             (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
             memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
             memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
             v7_stackGapsEncDec (s0.sp - 2400#64) ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             memRegion pbA 128 ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
             statesFromPbJumpTablePlacedAt ∗
             A.pool lim (M.stepEvents evs_uc st0) sm) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left h400) (Entails.of_eq (by sep_ac_rfl))
        · intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx8_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
          refine seq_clean_st
            (mid := lsmpl.base 333 + 3716#64)
            (P_mid := fun sm =>
              (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
               protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1792#64) (pbToProtoPolyEncoder e) ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
               v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
               v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
               (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
               (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
               (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
               memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
               memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
               v7_stackGapsEncDec (s0.sp - 2400#64) ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               memRegion pbA 128 ∗
               memRegion (pbA + 128#64) 56 ∗
               (((pbA + 184#64) ↦₆₄ cap_dec) ∗
                v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
               statesFromPbJumpTablePlacedAt) ∗
              A.pool lim (M.stepEvents evs_uc st0) sm)
            (Q := fun sm =>
              sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
              sm.readReg64 .x1 = (s0.sp - 2400#64) + 1792#64 ∧ sm.readReg64 .x19 = out ∧
              sm.readReg64 .x20 = (s0.sp - 2400#64) + 1792#64 ∧ sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
              sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
              sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x25 = (s0.sp - 2400#64) + 1888#64 ∧
              sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = p1 ∧
              TraceCalleeSaved sm s0)
            ?_ ?_
          · refine SepWP.mono
              (v7_copy_enc_3652_to_3716_placed_budget A lim (M.stepEvents evs_uc st0)
                s0 s2 (s0.sp - 2400#64) out pbA cap_enc cap_dec c1 c2 l1 p1
                ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64) slot24
                (pbToProtoPolyEncoder e) _
                hfsp_align hpc2 hrun2 hsp2 hx1_2 hx8_2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2) ?_
            intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
            exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
          · intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx1_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
            refine SepWP.mono
              (v7_bl_encoder_3716_to_32996_placed_budget A lim (M.stepEvents evs_uc st0)
                s0 s3 (s0.sp - 2400#64) out pbA cap_dec c2 l1 p1
                ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64) _
                hpc3 hrun3 hsp3 hx0_3 hx1_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3) ?_
            intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
            exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
      · intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hx0_4, hx1_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx30_4, htr4⟩
        have halign4 : s4.spAligned = true := by
          unfold State.spAligned; rw [hsp4]; exact hfsp_align
        have hfits_enc :
            FitsEnv M lim (M.stepEvents evs_uc st0)
              (EncoderFromPbAllocEnv (pbToProtoPolyEncoder e)) := by
          apply fitsEnv_encAlloc_step_of_ucSomeEnv e huc huc_env
          rw [← hs_enc]
          exact hfits_uc
        refine v7_sepWPp_call_wpp_lscl (v7_sub_ok_encoder_from_pb_placed henc_sub)
          (x := (EncoderFromPbGhost.mk ((s0.sp - 2400#64) + 1888#64) ((s0.sp - 2400#64) + 1792#64)
                   (pbToProtoPolyEncoder e),
                 M.stepEvents evs_uc st0))
          hcl4 hpc4 hrun4 halign4 hx30_4
          (fun R' hm => by
            dsimp only [encoderFromPbSpec, polyEncoderSize]
            rw [sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hx0_4, hx1_4, hpts_e, hfits_enc,
              by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s4.readReg64 .x30); rw [show s4.readReg64 .x30 = _ from hx30_4]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩, ?_⟩
            rw [hsp4]
            exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
          (fun sf R' hm => by
            change sf.mem ⊨ (⌜False⌝ ∗ _) ∗ R' at hm
            rw [sepConj_assoc] at hm
            exact (not_satisfies_false_sepConj hm).elim)
          (fun _ _ => rfl)
          ?_
        intro s5 hpc5 hrun5 hcl5 hsp5 hcs5
        have hsp5' : s5.sp = s0.sp - 2400#64 := hsp5.trans hsp4
        have hx19_5 : s5.readReg64 .x19 = out := (hcs5.1).trans hx19_4
        have hx20_5 : s5.readReg64 .x20 = (s0.sp - 2400#64) + 1792#64 := (hcs5.2.1).trans hx20_4
        have hx21_5 : s5.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := (hcs5.2.2.1).trans hx21_4
        have hx22_5 : s5.readReg64 .x22 = cap_dec := (hcs5.2.2.2.1).trans hx22_4
        have hx23_5 : s5.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := (hcs5.2.2.2.2.1).trans hx23_4
        have hx24_5 : s5.readReg64 .x24 = c2 := (hcs5.2.2.2.2.2.1).trans hx24_4
        have hx25_5 : s5.readReg64 .x25 = (s0.sp - 2400#64) + 1888#64 := (hcs5.2.2.2.2.2.2.1).trans hx25_4
        have hx26_5 : s5.readReg64 .x26 = l1 := (hcs5.2.2.2.2.2.2.2.1).trans hx26_4
        have hx27_5 : s5.readReg64 .x27 = pbA := (hcs5.2.2.2.2.2.2.2.2.1).trans hx27_4
        have hx28_5 : s5.readReg64 .x28 = p1 := (hcs5.2.2.2.2.2.2.2.2.2.1).trans hx28_4
        dsimp only [encoderFromPbSpec, protoPolynomialEncoderSize]
        rw [hsp4, sepExists_sepConj_left]
        apply SepWPp.exists_elim; intro evs_enc
        rw [← M.stepEvents_append evs_uc evs_enc st0]
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ⌜s5.trace = s4.trace ∧ AllocCallPreserved s4 s5 ∧
           EncoderFromPbEnv (pbToProtoPolyEncoder e) evs_enc⌝ ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
             (fromPbResult (pbToProtoPolyEncoder e)) ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
           v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
           v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           memRegion (pbA + 128#64) 56 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
           statesFromPbJumpTablePlacedAt ∗
           A.pool lim (M.stepEvents (evs_uc ++ evs_enc) st0) s5) by sep_ac_rfl)) ?_
        apply SepWPp.pure_elim; rintro ⟨htr5, _hacp5, henc_env⟩
        exact v7_after_enc_call_3720_placed hA hdec_sub st0 (evs_uc ++ evs_enc)
          s0 s5 out pbA cap_dec slot16 slot200
          c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 s u uc e R
          hcl5 h7404_ok
          (fun err evs_free henc hfree => by
            apply hsub_uc
            rw [hs_enc]
            exact ct1SampledUcSomeEnv_of_enc_err huc henc huc_env henc_env hfree)
          (fun enc d henc hs_d => by
            apply fitsEnv_decAlloc_step_of_ucSomeEnv d huc henc huc_env henc_env
            rw [← hs_enc, ← hs_d]
            exact hfits_uc)
          (fun enc evs_free henc hs_none hfree => by
            apply hsub_uc
            rw [hs_enc, hs_none]
            exact ct1SampledUcSomeEnv_of_dec_none huc henc huc_env henc_env hfree)
          (fun enc d _dec evs_dec henc hs_d hdec_env _hdec_res => by
            apply hsub_uc
            rw [hs_enc, hs_d]
            exact ct1SampledUcSomeEnv_of_dec_ok huc henc huc_env henc_env hdec_env)
          (fun enc d _err evs_dec evs_free henc hs_d hdec_env _hdec_res hfree => by
            apply hsub_uc
            rw [hs_enc, hs_d]
            exact ct1SampledUcSomeEnv_of_dec_err huc henc huc_env henc_env hdec_env hfree)
          hpts hcap_dec hs_uc huc hs_enc hc1 hsp0_align
          hpc5 hrun5 hsp5' hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5
          ⟨htr5.trans htr4.1, hcs5.2.2.2.2.2.2.2.2.2.2.2.trans htr4.2⟩

/-- Budget-threaded stage at `+3480` after `<Ct1Sampled>` entry (`+1056 -> +3480`) has checked
    `receiving_ek.pts_needed`. -/
theorem v7_from_3480_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hct1_sub : Ct1SentFromPbPlacedOkExt M A lim F ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st0 : M.σ)
    (s0 s1 : State) (out pbA w0 cap_dec : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (h7404_ok : V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s)
    (hfits : FitsEnv M lim st0 (Ct1SampledFromPbEnv F s))
    (hsub : ∀ {evs : List AllocEvent}, Ct1SampledFromPbEnv F s evs → Env evs)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (hpts_enc : optEncoderPtsBound s.sendingCt1)
    (hcap_uc : v7_optUcCapProp w0 s.uc)
    (hcap_dec : v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc) ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st0 s1)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).post
              ((out, pbA), st0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).onPanic
              ((out, pbA), st0) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  cases hs_uc : s.uc with
  | none =>
    have hfrom_pb := v7_from_pb_ct1Sampled_uc_none F s hpts hs_uc
    rw [hs_uc] at hcap_uc
    dsimp only [v7_optUcCapProp] at hcap_uc
    subst hcap_uc
    apply v7_seq_err_4632_wpp_placed st0 s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (v7_uc_none_3480_to_4632_placed hA s0 s1 out pbA cap_dec s.sendingCt1 s.receivingEk st0
          (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
          hcl1 hcap_dec hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx22_1 hx27_1 htr1) ?_)
    intro sm Pm _ _ ⟨evs, hevs, hPm, hspm, hx19m, hx28m, htrm⟩
    have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx28m]; rfl
    exact ⟨evs, hsub (ct1SampledFromPbEnv_of_uc_none hs_uc hevs),
      Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hspm, hx19m, hx28_b, htrm⟩
  | some u =>
    rw [hs_uc] at hcap_uc
    dsimp only [v7_optUcCapProp] at hcap_uc
    have hfits_uc : FitsEnv M lim st0 (Ct1SampledUcSomeEnv F u s.sendingCt1 s.receivingEk) :=
      fitsEnv_ucSomeEnv_of_ct1SampledFromPbEnv hpts hs_uc hfits
    have hfits_ct1 : FitsEnv M lim st0 (Ct1SentFromPbPreEnv F u) :=
      fitsEnv_ct1SentPre_of_ucSomeEnv hfits_uc
    refine v7_sepWPp_seq_clean_lscl hcl1
      (mid := lsmpl.base 339)
      (P_mid := fun sm =>
        (memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
         protoUnchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 240#64) u ∗
         A.pool lim st0 sm ∗
         stackAt (s0.sp - 2400#64) ct1SentFromPbStack) ∗
        (memRegion ((s0.sp - 2400#64) - 5152#64) 816 ∗
         memRegion (s0.sp - 2400#64) 240 ∗
         memRegion ((s0.sp - 2400#64) + 368#64) 1520 ∗
         memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         memRegion pbA 128 ∗
         optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
         statesFromPbJumpTablePlacedAt))
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x1 = (s0.sp - 2400#64) + 240#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧ sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x30 = lsmpl.base 333 + 3552#64 ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · refine seq_clean_st
        (mid := lsmpl.base 333 + 3548#64)
        (P_mid := fun sm =>
          (memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
           protoUnchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 240#64) u ∗
           stackAt (s0.sp - 2400#64) ct1SentFromPbStack ∗
           memRegion ((s0.sp - 2400#64) - 5152#64) 816 ∗
           memRegion (s0.sp - 2400#64) 240 ∗
           memRegion ((s0.sp - 2400#64) + 368#64) 1520 ∗
           memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
           statesFromPbJumpTablePlacedAt) ∗
          A.pool lim st0 sm)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
          sm.readReg64 .x1 = (s0.sp - 2400#64) + 240#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧ sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
          sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · refine SepWP.weaken_pre
          (Entails.trans
            (sepConj_mono (v7_stackAt_encoderFromPbStack_to_ct1SentFromPbStack (s0.sp - 2400#64))
              (sepConj_mono_left (v7_memRegion_2304_split_uc (s0.sp - 2400#64))))
            (Entails.of_eq (by sep_ac_rfl)))
          (SepWP.mono
            (v7_copy_uc_3480_to_3548_placed_budget A lim st0 s0 s1 (s0.sp - 2400#64) out pbA w0 cap_dec
              ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64) ((s0.sp - 2400#64) + 1792#64)
              u
              (stackAt (s0.sp - 2400#64) ct1SentFromPbStack ∗
               memRegion ((s0.sp - 2400#64) - 5152#64) 816 ∗
               memRegion (s0.sp - 2400#64) 240 ∗
               memRegion ((s0.sp - 2400#64) + 368#64) 1520 ∗
               memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
               memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
               (((pbA + 184#64) ↦₆₄ cap_dec) ∗
                v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
               statesFromPbJumpTablePlacedAt)
              hcap_uc hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1) ?_)
        intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
        exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx27_2, htr2⟩
        refine SepWP.mono
          (v7_bl_ct1_sent_3548_to_15272_placed_budget A lim st0 s0 s2 (s0.sp - 2400#64) out pbA cap_dec
            ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64) ((s0.sp - 2400#64) + 1792#64) _
            hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx21_2 hx22_2 hx23_2 hx25_2 hx27_2 htr2) ?_
        intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
        exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
    · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx0_3, hx1_3, hx19_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx30_3, htr3⟩
      have halign3 : s3.spAligned = true := by
        unfold State.spAligned; rw [hsp3]; exact hfsp_align
      refine v7_sepWPp_call_wpp_lscl (v7_sub_ok_ct1_sent_from_pb_placed hct1_sub)
        (x := (Ct1SentFromPbGhost.mk ((s0.sp - 2400#64) + 1888#64) ((s0.sp - 2400#64) + 240#64) u,
               st0))
        hcl3 hpc3 hrun3 halign3 hx30_3
        (fun R' hm => by
          dsimp only [ct1SentFromPbSpec, ct1SentFromPbSpecOfEnv]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_3, hx1_3, hfits_ct1, by
            simp (config := { decide := true }) [show s3.readReg64 .lr = _ from hx30_3, wp_norm]⟩, ?_⟩
          rw [hsp3]
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
        (fun sf R' hm => by
          change sf.mem ⊨ (⌜False⌝ ∗ _) ∗ R' at hm
          rw [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim)
        (fun _ _ => rfl)
        ?_
      intro s4 hpc4 hrun4 hcl4 hsp4 hcs4
      have hsp4' : s4.sp = s0.sp - 2400#64 := hsp4.trans hsp3
      have hx19_4 : s4.readReg64 .x19 = out := (hcs4.1).trans hx19_3
      have hx21_4 : s4.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := (hcs4.2.2.1).trans hx21_3
      have hx22_4 : s4.readReg64 .x22 = cap_dec := (hcs4.2.2.2.1).trans hx22_3
      have hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := (hcs4.2.2.2.2.1).trans hx23_3
      have hx25_4 : s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 := (hcs4.2.2.2.2.2.2.1).trans hx25_3
      have hx27_4 : s4.readReg64 .x27 = pbA := (hcs4.2.2.2.2.2.2.2.2.1).trans hx27_3
      dsimp only [ct1SentFromPbSpec, ct1SentFromPbSpecOfEnv, ct1SentFromPb, protoUnchunkedCt1SentSize]
      rw [hsp3]
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro evs_uc
      have hstack_back := v7_stackAt_ct1SentFromPbStack_to_encoderFromPbStack (s0.sp - 2400#64)
      have h1888_back := v7_memRegion_uc_rest_to_1888 (s0.sp - 2400#64)
      refine SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) ct1SentFromPbStack ∗
           memRegion ((s0.sp - 2400#64) - 5152#64) 816) ∗
          (memRegion (s0.sp - 2400#64) 240 ∗
           memRegion ((s0.sp - 2400#64) + 240#64) 128 ∗
           memRegion ((s0.sp - 2400#64) + 368#64) 1520) ∗
          (⌜s4.trace = s3.trace⌝ ∗
           ⌜Ct1SentFromPbPostEnv F u evs_uc⌝ ∗
           (ct1SentResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64)
              (Ct1Sent.from_pb (spqrAuthApi F) u) ∗
            memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            memRegion pbA 128 ∗
            optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
            (((pbA + 184#64) ↦₆₄ cap_dec) ∗
             v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs_uc st0) s4)) by sep_ac_rfl))
          (Entails.trans (sepConj_mono hstack_back (sepConj_mono_left h1888_back))
            (Entails.of_eq (show _ =
              ⌜s4.trace = s3.trace⌝ ∗
              ⌜Ct1SentFromPbPostEnv F u evs_uc⌝ ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               ct1SentResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64)
                 (Ct1Sent.from_pb (spqrAuthApi F) u) ∗
               memRegion (s0.sp - 2400#64) 1888 ∗
               memRegion ((s0.sp - 2400#64) + 2016#64) 288 ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               memRegion pbA 128 ∗
               optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
               (((pbA + 184#64) ↦₆₄ cap_dec) ∗
                v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
               statesFromPbJumpTablePlacedAt ∗
               A.pool lim (M.stepEvents evs_uc st0) s4) by sep_ac_rfl)))) ?_
      apply SepWPp.pure_elim; intro htr4
      apply SepWPp.pure_elim; intro huc_env
      exact v7_after_uc_call_3552_placed hA henc_sub hdec_sub st0 evs_uc
        s0 s4 out pbA cap_dec s u R
        hcl4 h7404_ok huc_env hfits_uc
        (fun hevs => hsub (ct1SampledFromPbEnv_of_ucSomeEnv hpts hs_uc hevs))
        hpts hpts_enc hcap_dec hs_uc hsp0_align
        hpc4 hrun4 hsp4' hx19_4 hx21_4 hx22_4 hx23_4 hx25_4 hx27_4
        ⟨htr4.trans htr3.1, hcs4.2.2.2.2.2.2.2.2.2.2.2.trans htr3.2⟩

/-- Envelope-parametric `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) assuming
    `V7Ok7404PropPlaced` under any envelope `Env` subsuming `Ct1SampledFromPbEnv F s`. -/
theorem states_from_pb_ct1Sampled_ok_ext_of_ok7404_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hct1_sub : Ct1SentFromPbPlacedOkExt M A lim F ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct1Sampled)
    (h7404_ok : ∀ s0 out pbA, V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s)
    (hfits_imp : ∀ st : M.σ, FitsEnv M lim st Env →
      FitsEnv M lim st (Ct1SampledFromPbEnv F s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → Ct1SampledFromPbEnv F s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct1Sampled s) } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st0⟩ R s0 hpc0 hrun0 hpre0 hsp0_align
  obtain ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre0
  dsimp only [statesFromPbVariantPlacedSpecOfEnv] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8_0, hx0_0, hpts_enc, hfits0⟩, hmem0⟩
  dsimp only [v1StatePtsBound] at hpts_enc
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st0 s0,
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem0, ?_⟩
  have hexp :
      optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ⊢
        ∃∗ w0 : BitVec 64, ∃∗ cap_dec : BitVec 64,
          ⌜v7_optUcCapProp w0 s.uc ∧
           v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder)⌝ ∗
          ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc) ∗
          optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) := by
    dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt]
    refine Entails.trans
      (sepConj_mono (v7_optProtoUnchunkedCt1Sent_expose_w0 A.repAlloc pbA s.uc)
        (sepConj_mono_right
          (v7_optProtoPolyDecoder_expose_cap A.repAlloc (pbA + 184#64) (s.receivingEk.map pbToProtoPolyDecoder)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro cap_dec
    apply Entails.sepExists_elim; intro w0
    apply Entails.pure_left; intro hw0
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; intro hcap_dec
    refine Entails.sepExists_right w0 (Entails.sepExists_right cap_dec ?_)
    exact Entails.pure_right ⟨hw0, hcap_dec⟩ (Entails.of_eq (by sep_ac_rfl))
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hexp))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w0
  apply SepWPp.exists_elim; intro cap_dec
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    ⌜v7_optUcCapProp w0 s.uc ∧
     v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder)⌝ ∗
    (stackAt s0.sp statesFromPbStack ∗
     A.pool lim st0 s0 ∗
     (memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc) ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
      statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)) ?_
  apply SepWPp.pure_elim; rintro ⟨hcap_uc, hcap_dec⟩
  refine v7_sepWPp_seq_clean_lscl hcl0
    (mid := lsmpl.base 333 + 1056#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc) ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st0 sm)
    (Q_regs := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = w0 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x0 = pbA ∧ sm.readReg64 .x25 = s0.sp - 608#64 ∧
      sm.readReg64 .x21 = s0.sp - 1008#64 ∧ sm.readReg64 .x13 = s0.sp - 1136#64 ∧
      sm.readReg64 .x23 = s0.sp - 1552#64 ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · refine seq_clean_st
      (mid := lsmpl.base 333 + 36#64)
      (P_mid := fun sm =>
        (pbA ↦₆₄ w0) ∗
        statesFromPbJumpTablePlacedAt ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc ∗
         optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder))) ∗
        A.pool lim st0 sm)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x8 = out ∧
        sm.readReg64 .x0 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine SepWP.mono
        (DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st0 s0 out pbA
          (memRegion out chunkedStatesSize ∗
           ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc) ∗
           optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
           statesFromPbJumpTablePlacedAt)
          hsp0_align hpc0 hrun0 hx8_0 hx0_0) ?_
      intro sm Pm _ _ ⟨hPm, hsp_m, _, hx8_m, hx0_m, htr_m, _hvm_m⟩
      refine ⟨Entails.trans hPm ?_, hsp_m, hx8_m, hx0_m, htr_m⟩
      have hfsp := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
        ((pbA ↦₆₄ w0) ∗
         statesFromPbJumpTablePlacedAt ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc ∗
         optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
         A.pool lim st0 sm) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by sep_ac_rfl))
    · intro s1 hpc1 hrun1 ⟨hsp1, hx8_1, hx0_1, htr1⟩
      refine SepWP.mono
        (v7_dispatch_ct1Sampled_placed_budget A lim st0 s0 s1 out pbA w0 _
          (v7_optUcCapProp_imp_or hcap_uc)
          hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1) ?_
      intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
      exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx9_2, hx19_2, hx27_2, _, hx25_2, hx21_2, _, hx23_2, htr2⟩
    have hx21_2' : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by rw [hx21_2]; bv_omega
    have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by rw [hx23_2]; bv_omega
    have hx25_2' : s2.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 := by rw [hx25_2]; bv_omega
    by_cases hpts : v7_receivingEkPtsOk s.receivingEk
    · refine v7_sepWPp_seq_clean_lscl hcl2
        (mid := lsmpl.base 333 + 3480#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc) ∗
          optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim st0 sm)
        (Q_regs := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = w0 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧ sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
          sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (v7_entry_1056_to_3480_placed_budget A lim st0
              (s0 := s0.writeReg64 .x0 (s2.readReg64 .x26)) (s1 := s2)
              out pbA (s2.readReg64 .x1) w0 cap_dec
              ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64) ((s0.sp - 2400#64) + 1792#64)
              s.receivingEk
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               memRegion (s0.sp - 2400#64) 2304 ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 s.uc) ∗
               optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
               statesFromPbJumpTablePlacedAt)
              hcap_dec hpts hpc2 hrun2 hsp2 rfl hx9_2 hx19_2 hx21_2' hx23_2' hx25_2' rfl hx27_2 htr2) ?_)
        intro sm Pm _ _ ⟨hPm, _hvm_m, hsp_m, _, hx9_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, _, hx27_m, htr_m⟩
        exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)),
          hsp_m, hx9_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hx27_m, htr_m⟩
      · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx9_3, hx19_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, htr3⟩
        exact v7_from_3480_placed hA hct1_sub henc_sub hdec_sub st0 s0 s3 out pbA w0 cap_dec s R
          hcl3 (h7404_ok s0 out pbA) (hfits_imp st0 hfits0)
          (fun hevs => hsub st0 hfits0 hevs)
          hpts hpts_enc hcap_uc hcap_dec hsp0_align
          hpc3 hrun3 hsp3 hx9_3 hx19_3 hx21_3 hx22_3 hx23_3 hx25_3 hx27_3 htr3
    · cases hs_dec : s.receivingEk with
      | none =>
        exfalso
        apply hpts
        rw [hs_dec]
        trivial
      | some d =>
        have hpts_b : (d.ptsNeeded == 576#32) = false := by
          rw [hs_dec] at hpts
          exact Bool.eq_false_iff.mpr hpts
        have hfrom_pb := v7_from_pb_ct1Sampled_bad_pts F s d hs_dec hpts_b
        rw [hs_dec] at hcap_dec
        simp only [Option.map] at hcap_dec ⊢
        apply v7_seq_err_4632_wpp_placed st0 s0 s2 out pbA s .msgDecode _ R hfrom_pb hsp0_align
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (v7_entry_bad_pts_1056_to_4632_placed hA s0 s2 out pbA w0 cap_dec s.uc s.sendingCt1 d st0
              (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
              hcl2 hcap_uc hcap_dec hpts_b hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx27_2 htr2) ?_)
        intro sm Pm _ _ ⟨evs, hevs, hPm, hspm, hx19m, hx28m, htrm⟩
        have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .msgDecode := by
          rw [hx28m]; rfl
        exact ⟨evs, hsub st0 hfits0 (ct1SampledFromPbEnv_of_bad_pts hs_dec hpts_b hevs),
          Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hspm, hx19m, hx28_b, htrm⟩

/-- Top-level `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) assuming `V7Ok7404PropPlaced`
    under the canonical `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`). -/
theorem states_from_pb_ct1Sampled_ok_ext_of_ok7404_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (hct1_sub : Ct1SentFromPbPlacedOkExt M A lim F ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext) (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct1Sampled)
    (h7404_ok : ∀ s0 out pbA, V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.ct1Sampled s) })) :=
  states_from_pb_ct1Sampled_ok_ext_of_ok7404_placed_of_env hA hct1_sub henc_sub hdec_sub s h7404_ok
    (fun _ h => fitsEnv_ct1SampledFromPbEnv_of_statesFromPbEnv F s h)
    (fun _ _ hfits hevs => ct1SampledFromPbEnv_sub_statesFromPbEnv F s hfits hevs)

/-- Envelope-parametric `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) with explicit
    `Ct1SentFromPbPlacedOkExt` hypothesis under any envelope `Env` subsuming
    `Ct1SampledFromPbEnv F s`. -/
theorem states_from_pb_ct1Sampled_ok_ext_of_ct1_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext) (hct1_sub : Ct1SentFromPbPlacedOkExt M A lim F ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext) (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct1Sampled)
    (hfits_imp : ∀ st : M.σ, FitsEnv M lim st Env → FitsEnv M lim st (Ct1SampledFromPbEnv F s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → Ct1SampledFromPbEnv F s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env)) :=
  states_from_pb_ct1Sampled_ok_ext_of_ok7404_placed_of_env hA hct1_sub henc_sub hdec_sub s
    (fun s0 out pbA => v7_ok7404Prop_holds_placed hA s0 out pbA s) hfits_imp hsub

/-- Top-level `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) with arbitrary `ext` and
    explicit `Ct1SentFromPbPlacedOkExt` hypothesis under `StatesFromPbEnv`. -/
theorem states_from_pb_ct1Sampled_ok_ext_of_ct1_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (hct1_sub : Ct1SentFromPbPlacedOkExt M A lim F ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext) (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.ct1Sampled s) })) :=
  states_from_pb_ct1Sampled_ok_ext_of_ok7404_placed hA hct1_sub henc_sub hdec_sub s
    (fun s0 out pbA => v7_ok7404Prop_holds_placed hA s0 out pbA s)

/-- Envelope-parametric `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) under any
    envelope `Env` subsuming `Ct1SampledFromPbEnv F s`. -/
theorem states_from_pb_ct1Sampled_ok_ext_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext) (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct1Sampled)
    (hfits_imp : ∀ st : M.σ, FitsEnv M lim st Env → FitsEnv M lim st (Ct1SampledFromPbEnv F s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → Ct1SampledFromPbEnv F s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env)) :=
  states_from_pb_ct1Sampled_ok_ext_of_ct1_placed_of_env hA
    (ct1_sent_from_pb_ok_of_alloc_placed hA) henc_sub hdec_sub s hfits_imp hsub

/-- Tight-envelope `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) under its exact binary
    allocation envelope `Ct1SampledFromPbEnv F s`. -/
theorem states_from_pb_ct1Sampled_ok_ext_placed_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext) (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct1Sampled s) } (Ct1SampledFromPbEnv F s))) :=
  states_from_pb_ct1Sampled_ok_ext_placed_of_env hA henc_sub hdec_sub s
    (fun _ h => h) (fun _ _ _ h => h)

/-- Top-level `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) with arbitrary `ext` under
    the canonical `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`). -/
theorem states_from_pb_ct1Sampled_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc_sub : EncoderFromPbPlacedOkExt M A lim ext) (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.ct1Sampled s) })) :=
  states_from_pb_ct1Sampled_ok_ext_of_ct1_placed hA
    (ct1_sent_from_pb_ok_of_alloc_placed hA) henc_sub hdec_sub s

/-- Top-level `subroutine_ok` for Variant 7 (`InnerState.ct1Sampled s`) with `ext := fun _ => none`
    under the canonical `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`). -/
theorem states_from_pb_ct1Sampled_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (hA : FromPbAllocHooksBudget M A lim (fun _ => none))
    (henc_sub : EncoderFromPbPlacedOkExt M A lim (fun _ => none))
    (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim (fun _ => none))
    (s : V1State.Chunked.Ct1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics (fun _ => none))) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.ct1Sampled s) })) :=
  states_from_pb_ct1Sampled_ok_ext_placed hA henc_sub hdec_sub s

abbrev states_from_pb_variant6_placed := @states_from_pb_ct1Sampled_ok_ext_placed

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudget
