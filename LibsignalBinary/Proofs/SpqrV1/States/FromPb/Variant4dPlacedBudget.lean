/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecoderFromPbClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4d
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 4 (`EkSentCt1Received`) — Part D

Relocatable Block-`333` early `ptsNeeded ≠ 80` error path and `+2228` / `+2308 -> ret`
continuations for `InnerState.ekSentCt1Received` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudgetAux
  (v4b_step_248_none_to_2228_placed_budget
   v4b_step_2228_none_to_5264_placed_budget
   v4b_step_248_some_eq_to_2228_placed_budget
   v4b_step_248_some_ne_to_304_placed_budget)
export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudgetAux
  (v4b_step_2228_some_to_18368_placed_budget
   v4b_step_2308_err_to_5264_placed_budget
   v4b_step_2308_ok_none_to_6860_placed_budget
   v4d_dealloc_opt_dec_5264_to_ret_of_placedHooks_placed)
export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudgetAux
  (v4d_dealloc_opt_dec_5264_to_ret_placed
   v4d_drop_opt_uc_304_to_5276_of_placedHooks_placed
   v4d_drop_opt_uc_304_to_5276_placed)

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsProg_333 lsmpl sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoPolynomialDecoder States StatesError V1State pbToProtoPolyDecoder
   spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk (EkSentCt1Received)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved decoderFromPbResult decoderFromPbStack resultChunkedStatesAt spqrErrorByte
   statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack
   v4_stackAt_allocHook_to_encoderFromPbStack v4_stackAt_encoderFromPbStack_to_allocHook
   v4b_byte_region95_to_words v4b_ekSentCt1ReceivedAt_unpack
   v4b_ekSentCt1ReceivedHeap v4b_ekSentCt1ReceivedHeap_entails_dealloc
   v4b_optProtoPolyDecoderHeap v4b_optProtoPolyDecoderWordsAt v4b_optProtoUcHeap
   v4b_optProtoUcWordsAt v4b_pbA_all_words_entails_memRegion v4b_protoPolyDecoderAt_pack
   v4b_states_from_pb_ekSentCt1Received_ptsNeeded_ne v4c_memRegion_1652_split_896
   v4c_memRegion_224_to_ucSpillSlots v4c_memRegion_660_40_952_entails_1652
   v4c_polyDecoderAt_unpack v4c_ucSpillSlots v4c_ucWords_312_entails_400_16 v4c_wp_exists_left
   v4d_ekSentCt1ReceivedHeap_rk_lt v4d_fsp_aligned v4d_optProtoPolyDecoderHeap_some_d0_lt
   v4d_pull_pures v4d_rot3 v4d_rot4 v4d_sepWP_pure_left v4d_stack_2308_err_entails_2304
   v4d_stack_6860_entails_2304)
open CryptoVerification.SpqrV1.Unchunked (ekSentCt1ReceivedResultAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget decoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (seq_clean_evs seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (FromPbAllocHooksBudget)

/-! ## Envelope Composition, `withLsCodeLoaded` Sequencing, & Early `ptsNeeded ≠ 80#32` Error -/

theorem fromPbDecEnv_append_freeOnly {pb : ProtoPolynomialDecoder} {evs1 evs2 : List AllocEvent}
    (h1 : FromPbDecEnv pb evs1) (h2 : FreeOnlyEvs evs2) :
    FromPbDecEnv pb (evs1 ++ evs2) := by
  rcases h1 with ⟨evs_a, evs_f, rfl, ha, hf⟩
  exact ⟨evs_a, evs_f ++ evs2, List.append_assoc _ _ _, ha, hf.append h2⟩

private theorem v4d_sepWP_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P1' : SepProp} {P_mid : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P1' (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_regs sm))
    (hpre : P ⊢ P1')
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWP prog ret sm (P_mid sm) Q) :
    SepWP prog ret s P Q :=
  SepWP.weaken_pre hpre
    (sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpcm hrunm ⟨hPm, hQr⟩ hcl_m =>
      SepWP.weaken_pre hPm (h2 sm hpcm hrunm hcl_m hQr)))

/-- Complete `+248 -> ret` execution under `FreeOnlyEvs` when `s.receivingCt2 = some d`
    and `d.ptsNeeded ≠ 80#32`. -/
theorem v4d_ekSent_err_ptsNeeded_ne_248_of_placedHooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received)
    (d : PolynomialDecoder)
    (hne : d.ptsNeeded ≠ 80#32)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 248#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        (pbA ↦₆₄ 0x8000000000000004#64) ∗
        memRegion (pbA + 152#64) 72 ∗
        v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ekSentCt1Received { uc := optUc, receivingCt2 := some d }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    v4d_fsp_aligned s0.sp hsp0_align
  rw [v4b_states_from_pb_ekSentCt1Received_ptsNeeded_ne F optUc d hne]
  dsimp only [v4b_optProtoPolyDecoderHeap, pbToProtoPolyDecoder]
  rw [sepConj_assoc]
  apply v4d_sepWP_pure_left; rintro ⟨rfl, rfl, rfl, hle, hcap, _, _⟩
  have hd0_lt : d0.toNat < 2 ^ 63 := by omega
  let PtsBuf : SepProp :=
    if d0 = 0#64 then emp
    else A.live d8 (d0.toNat * 24) 8 ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 d8 d.pts ∗
      memRegion (d8 + BitVec.ofNat 64 (d.pts.length * 24)) ((d0.toNat - d.pts.length) * 24)
  change SepWP _ _ s1 (PtsBuf ∗ _) _
  have h248 := v4b_step_248_some_ne_to_304_placed_budget A lim st (ext := ext)
    s1 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
    d0 d8 (BitVec.ofNat 64 d.pts.length) d.ptsNeeded d.polys d32
    ((pbA ↦₆₄ 0x8000000000000004#64) ∗ memRegion (pbA + 152#64) 72 ∗
     v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
     PtsBuf ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
    hd0_lt hne hpc1 hrun1 hx27_1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_clean_st h248 ?_)
  intro s2 hpc2 hrun2 ⟨_hvm12, hsp2, hx0_2, hx1_2, _, _, _, hx11_2, hx12_2, _, _, _, hx19_2,
    hx20_2, hx21_2, hx22_2, _, hx24_2, hx25_2, hx26_2, _, hx28_2, htr2⟩
  rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; have htr2 := htr2.trans htr1
  have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
    d0 d8 (BitVec.ofNat 64 d.pts.length) d.ptsNeeded d.polys d32
  have hst := v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
  have h304 := v4d_drop_opt_uc_304_to_5276_of_placedHooks_placed hA st s0 s2
    (s0.sp - 2400#64) out d8 d0 (BitVec.ofNat 64 d.pts.length)
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 optUc
    (PtsBuf ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
     memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbJumpTablePlacedAt)
    hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx11_2 hx12_2 hx19_2 hx20_2
    hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2
  refine SepWP.weaken_pre ?_ (seq_clean_evs h304 ?_)
  · refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x8000000000000004#64) ∗
         v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 (BitVec.ofNat 64 d.pts.length) d.ptsNeeded d.polys d32 ∗
         memRegion (pbA + 152#64) 72) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         A.pool lim st s2 ∗ PtsBuf ∗ memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
      (Entails.trans (sepConj_mono hpb (sepConj_mono_left hst)) (Entails.of_eq (by sep_ac_rfl)))
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hpres3, hx20_3⟩
    have h5276 := Variant4aPlacedBudget.v4_states_from_pb_dealloc_proto_decoder_5276_placed
      hA s0 s3 (s0.sp - 2400#64) out d8 d0 2#64 d.pts (M.stepEvents evs1 st)
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt)
      hfsp_align hle hcap hpc3 hrun3 hpres3 hx20_3
    refine SepWP.weaken_pre (by dsimp only [PtsBuf]; exact Entails.of_eq (by sep_ac_rfl))
      (seq_clean_evs h5276 ?_)
    intro evs2 s4 hevs2 hpc4 hrun4 ⟨hsp4, hx19_4, _, _, hx26_4, htr4⟩
    have hx26_4' : (s4.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .msgDecode := by
      rw [hx26_4]; rfl
    have herr := Variant4aPlacedBudget.v4_states_from_pb_err_5348_placed_budget
      A lim (M.stepEvents evs2 (M.stepEvents evs1 st)) (F := F) (ext := ext) s0 s4 out .msgDecode
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx26_4' htr4
    refine SepWP.weaken_pre ?_ (SepWP.mono herr ?_)
    · refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
          (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗
           A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s4) by sep_ac_rfl))
        (sepConj_mono_left (v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)))
    · intro sf Pf _ _ ⟨hPf, _hvmf, hsp_f, hcs_f, htr_f⟩
      refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hsp_f, hcs_f, htr_f⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

theorem v4d_ekSent_err_ptsNeeded_ne_248_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received)
    (d : PolynomialDecoder)
    (hne : d.ptsNeeded ≠ 80#32)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 248#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        (pbA ↦₆₄ 0x8000000000000004#64) ∗
        memRegion (pbA + 152#64) 72 ∗
        v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ekSentCt1Received { uc := optUc, receivingCt2 := some d }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v4d_ekSent_err_ptsNeeded_ne_248_of_placedHooks_placed hA.toPlacedBudget st
    s0 s1 out pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
    d0 d8 d16 d24 d28 d32 optUc d hne
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-! ## `+2228 -> +5264 -> ret` (`s.uc = none`) and `+2308 -> ret` Post-Call Error Branches -/

/-- From `+2228`, when `s.uc = none` (`u0 = noneCap`), branches to `+5264`, deallocates `optDec`
    under `FreeOnlyEvs`, and exits with `.error (.err .stateDecode)`. -/
theorem v4d_ekSent_uc_none_2228_to_ret_of_placedHooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s2 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 2228#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out)
    (hx20_2 : s2.readReg64 .x20 = d16)
    (hx22_2 : s2.readReg64 .x22 = noneCap)
    (hx24_2 : s2.readReg64 .x24 = d8)
    (hx28_2 : s2.readReg64 .x28 = d0)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s2 ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have h2228 := v4b_step_2228_none_to_5264_placed_budget A lim st (ext := ext) s2
    (v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
    hpc2 hrun2 hx22_2
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_clean_st h2228 ?_)
  intro s3 hpc3 hrun3 ⟨_hvm23, hsp3, _, _, hx19_3, hx20_3, hx24_3, hx26_3, hx28_3, htr3⟩
  rw [hsp2] at hsp3; rw [hx19_2] at hx19_3; rw [hx20_2] at hx20_3
  rw [hx24_2] at hx24_3; rw [hx28_2] at hx28_3; have htr3 := htr3.trans htr2
  have hx26_3' : (s3.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx26_3]; rfl
  have hret := v4d_dealloc_opt_dec_5264_to_ret_of_placedHooks_placed (F := F) hA st
    s0 s3 out d0 d8 d16 d32 d24 d28 optDec .stateDecode
    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx24_3 hx28_3 hx26_3' htr3
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hret ?_)
  intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v4d_ekSent_uc_none_2228_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s2 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 2228#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out)
    (hx20_2 : s2.readReg64 .x20 = d16)
    (hx22_2 : s2.readReg64 .x22 = noneCap)
    (hx24_2 : s2.readReg64 .x24 = d8)
    (hx28_2 : s2.readReg64 .x28 = d0)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s2 ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v4d_ekSent_uc_none_2228_to_ret_of_placedHooks_placed hA.toPlacedBudget st
    s0 s2 out pbA d0 d8 d16 d32 d24 d28 optDec
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 hx24_2 hx28_2 htr2

/-- From `+2308`, when `EkSentCt1Received.from_pb` returned `.error e`:
    steps `+2308 -> +5264`, deallocates `optDec` under `FreeOnlyEvs`, and exits with
    `.error (.err .stateDecode)`. -/
theorem v4d_ekSent_2308_err_to_ret_of_placedHooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s3 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (e : StatesError)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = d16)
    (hx24_3 : s3.readReg64 .x24 = d8)
    (hx28_3 : s3.readReg64 .x28 = d0)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s3 ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  have h1896 :
      ekSentCt1ReceivedResultAt A.repAlloc (F := F) (fsp + 1888#64) (.error e) ⊢
      ∃∗ w1896 : BitVec 64, ∃∗ w1904 : BitVec 64, ∃∗ w1912 : BitVec 64,
        ⌜w1896.extractLsb' 0 8 = 0#8⌝ ∗
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
        memRegion (fsp + 1920#64) 72 := by
    dsimp only [ekSentCt1ReceivedResultAt]
    have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
    have ha1897 : (fsp + 1888#64) + 9#64 = (fsp + 1896#64) + 1#64 := by bv_omega
    rw [ha1896, ha1897]
    refine Entails.trans (sepConj_mono_right (v4b_byte_region95_to_words (fsp + 1896#64) 0#8)) ?_
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro w1896
    apply Entails.sepExists_elim; intro w1904
    apply Entails.sepExists_elim; intro w1912
    refine Entails.sepExists_right w1896
      (Entails.sepExists_right w1904 (Entails.sepExists_right w1912 (Entails.of_eq (by sep_ac_rfl))))
  refine SepWP.weaken_pre (sepConj_mono_left h1896) ?_
  wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w1896
  apply ProofLib.SepWP.exists_left; intro w1904
  apply ProofLib.SepWP.exists_left; intro w1912
  apply v4d_sepWP_pure_left; intro hw1896
  have h2308 := v4b_step_2308_err_to_5264_placed_budget A lim st (ext := ext)
    s3 fsp out d0 d8 d16 d28 w1896 w1904 w1912
    (memRegion fsp 224 ∗ ((fsp + 224#64) ↦₆₄ d32) ∗ memRegion (fsp + 236#64) 1652 ∗
     memRegion (fsp + 1920#64) 72 ∗ memRegion (fsp + 1992#64) 312 ∗
     v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx24_3 hx28_3
  refine SepWP.weaken_pre (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl))
    (seq_clean_st h2308 ?_)
  intro s4 hpc4 hrun4 ⟨_hvm34, hsp4, hx19_4, hx20_4, hx24_4, hx26_4, hx28_4, htr4⟩
  have htr4 := htr4.trans htr3
  have hx26_4' : (s4.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx26_4, hw1896]; rfl
  have h2304 := v4d_stack_2308_err_entails_2304 fsp d32 d28 w1896 w1904 w1912
  have hret := v4d_dealloc_opt_dec_5264_to_ret_of_placedHooks_placed (F := F) hA st
    s0 s4 out d0 d8 d16 d32 d24 d28 optDec .stateDecode
    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hsp0_align hpc4 hrun4 hsp4 hx19_4 hx20_4 hx24_4 hx28_4 hx26_4' htr4
  refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
  · refine Entails.trans
      (Entails.of_eq (show _ =
        (memRegion fsp 224 ∗ ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion (fsp + 236#64) 1652 ∗ ((fsp + 1888#64) ↦₆₄ noneCap) ∗
         ((fsp + 1896#64) ↦₆₄ w1896) ∗ ((fsp + 1904#64) ↦₆₄ w1904) ∗
         ((fsp + 1912#64) ↦₆₄ w1912) ∗ memRegion (fsp + 1920#64) 72 ∗
         memRegion (fsp + 1992#64) 312) ∗
        (v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
         stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool lim st s4 ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl)))
  · intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v4d_ekSent_2308_err_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s3 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (e : StatesError)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = d16)
    (hx24_3 : s3.readReg64 .x24 = d8)
    (hx28_3 : s3.readReg64 .x28 = d0)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s3 ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v4d_ekSent_2308_err_to_ret_of_placedHooks_placed hA.toPlacedBudget st
    s0 s3 out pbA d0 d8 d16 d32 d24 d28 optDec e
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx24_3 hx28_3 htr3

/-- From `+2308`, when `EkSentCt1Received.from_pb` returned `.ok uc` and `s.receivingCt2 = none`
    (`x28 = noneCap`): steps `+2308 -> +6860 -> +5348 -> ret` under `FreeOnlyEvs` with
    `.error (.err .stateDecode)`. -/
theorem v4d_ekSent_2308_ok_none_to_ret_of_placedHooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s3 : State) (out pbA d32 : BitVec 64) (d28 : BitVec 32)
    (uc : EkSentCt1Received (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx28_3 : s3.readReg64 .x28 = noneCap)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s3 ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  dsimp only [ekSentCt1ReceivedResultAt]
  refine SepWP.weaken_pre
    (sepConj_mono (v4b_ekSentCt1ReceivedAt_unpack A.repAlloc (fsp + 1888#64) uc)
      (sepConj_mono_left (v4c_memRegion_224_to_ucSpillSlots fsp))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v32; apply ProofLib.SepWP.exists_left; intro v40
  apply ProofLib.SepWP.exists_left; intro v48; apply ProofLib.SepWP.exists_left; intro v56
  apply ProofLib.SepWP.exists_left; intro v72; apply ProofLib.SepWP.exists_left; intro v80
  apply ProofLib.SepWP.exists_left; intro v128; apply ProofLib.SepWP.exists_left; intro v136
  apply ProofLib.SepWP.exists_left; intro v144; apply ProofLib.SepWP.exists_left; intro v216
  apply ProofLib.SepWP.exists_left; intro rkCap; apply ProofLib.SepWP.exists_left; intro rkPtr
  apply ProofLib.SepWP.exists_left; intro rkLen; apply ProofLib.SepWP.exists_left; intro mkCap
  apply ProofLib.SepWP.exists_left; intro mkPtr; apply ProofLib.SepWP.exists_left; intro mkLen
  apply ProofLib.SepWP.exists_left; intro dkCap; apply ProofLib.SepWP.exists_left; intro dkPtr
  apply ProofLib.SepWP.exists_left; intro dkLen; apply ProofLib.SepWP.exists_left; intro ct1Cap
  apply ProofLib.SepWP.exists_left; intro ct1Ptr; apply ProofLib.SepWP.exists_left; intro ct1Len
  have hdealloc := v4b_ekSentCt1ReceivedHeap_entails_dealloc A.repAlloc
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hdealloc)) ?_
  wp_simp_pre [sepConj_assoc]
  refine SepWP.weaken_pre (Entails.of_eq (sepConj_left_comm _ _ _)) ?_
  apply v4d_sepWP_pure_left; intro hrk_lt
  have h6860 := v4b_step_2308_ok_none_to_6860_placed_budget A lim st (ext := ext) s3 fsp out
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
    v72 v128 v144
    (vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗ vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
     vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗ vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
     ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
     ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
     ((fsp + 216#64) ↦₆₄ v216) ∗ memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
     memRegion (fsp + 88#64) 40 ∗ memRegion (fsp + 152#64) 64 ∗
     ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
     memRegion (fsp + 236#64) 1652 ∗ memRegion (fsp + 1992#64) 312 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hfsp_align hrk_lt hpc3 hrun3 hsp3 hx19_3 hx28_3
  refine SepWP.weaken_pre (by dsimp only [fsp, v4c_ucSpillSlots]; exact Entails.of_eq (by sep_ac_rfl))
    (seq_clean_st h6860 ?_)
  intro s4 hpc4 hrun4 ⟨_hvm34, hsp4, hx0_4, hx1_4, hx9_4, hx19_4, hx22_4, hx26_4, htr4⟩
  have htr4 := htr4.trans htr3
  have hst := v4_stackAt_encoderFromPbStack_to_allocHook fsp
  have hdrop := Variant4aPlacedBudget.v4_states_from_pb_drop_uc_6860_placed hA s0 s4 fsp out
    rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap st
    (memRegion (fsp - 5152#64) 1056 ∗
     v4b_optProtoUcWordsAt (fsp + 1888#64)
       rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
     ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
     ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
     ((fsp + 216#64) ↦₆₄ v216) ∗ memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
     memRegion (fsp + 88#64) 40 ∗ memRegion (fsp + 152#64) 64 ∗
     ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
     memRegion (fsp + 236#64) 1652 ∗ memRegion (fsp + 1992#64) 312 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hfsp_align hpc4 hrun4 hsp4 hx0_4 hx1_4 hx9_4 hx19_4 hx22_4 hx26_4 htr4
  refine SepWP.weaken_pre ?_ (seq_clean_evs hdrop ?_)
  · refine Entails.trans
      (Entails.of_eq (show _ =
        stackAt fsp encoderFromPbStack ∗
        (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗ ((fsp + 144#64) ↦₆₄ dkPtr) ∗
         vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗ vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
         vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗ vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
         A.pool lim st s4 ∗
         v4b_optProtoUcWordsAt (fsp + 1888#64)
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
         ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
         ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
         ((fsp + 216#64) ↦₆₄ v216) ∗ memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 88#64) 40 ∗ memRegion (fsp + 152#64) 64 ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion (fsp + 236#64) 1652 ∗ memRegion (fsp + 1992#64) 312 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl)))
  · intro evs s5 hevs hpc5 hrun5 ⟨hsp5, hx19_5, hx26_5, htr5⟩
    have hx26_5' : (s5.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx26_5]; rfl
    have hst_back := v4_stackAt_allocHook_to_encoderFromPbStack fsp
    have h2304 := v4d_stack_6860_entails_2304 fsp
      v32 v40 v48 v56 ct1Ptr v80 ct1Cap v136 dkPtr v216 d32 d28
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
    dsimp only [v4c_ucSpillSlots] at h2304
    have herr := Variant4aPlacedBudget.v4_states_from_pb_err_5348_placed_budget
      A lim (M.stepEvents evs st) (F := F) (ext := ext) s0 s5 out .stateDecode
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc5 hrun5 hsp5 hx19_5 hx26_5' htr5
    refine SepWP.weaken_pre ?_ (SepWP.mono herr ?_)
    · refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
           memRegion (fsp + 152#64) 64 ∗
           (((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
            ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
            ((fsp + 144#64) ↦₆₄ dkPtr) ∗ ((fsp + 216#64) ↦₆₄ v216)) ∗
           ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
           memRegion (fsp + 236#64) 1652 ∗
           v4b_optProtoUcWordsAt (fsp + 1888#64)
             rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
           memRegion (fsp + 1992#64) 312) ∗
          (statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗
           A.pool lim (M.stepEvents evs st) s5) by sep_ac_rfl))
        (sepConj_mono hst_back (sepConj_mono_left h2304))
    · intro sf Pf _ _ ⟨hPf, _hvmf, hsp_f, hcs_f, htr_f⟩
      exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v4d_ekSent_2308_ok_none_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s3 : State) (out pbA d32 : BitVec 64) (d28 : BitVec 32)
    (uc : EkSentCt1Received (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx28_3 : s3.readReg64 .x28 = noneCap)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s3 ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v4d_ekSent_2308_ok_none_to_ret_of_placedHooks_placed hA.toPlacedBudget st
    s0 s3 out pbA d32 d28 uc hsp0_align hpc3 hrun3 hsp3 hx19_3 hx28_3 htr3

/-! ## `+2308 -> lsmpl.base 376 -> +2472 -> +8180 / +8500 -> ret` (`Ok(uc)`, `receivingCt2 = some d`) -/

/-- Total-correctness (`SepWP`) execution from `+2308` when `EkSentCt1Received.from_pb` returned
    `.ok uc` and `s.receivingCt2 = some d`, under `FromPbAllocHooksPlacedBudget` and
    `FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder d))`, producing an event trace in
    `FromPbDecEnv (pbToProtoPolyDecoder d)`. -/
theorem v4d_ekSent_2308_ok_some_to_ret_of_placedHooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s0 s3 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (uc : EkSentCt1Received (spqrAuthApi F))
    (d : PolynomialDecoder)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder d)))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = d16)
    (hx23_3 : s3.readReg64 .x23 = d24.zeroExtend 64)
    (hx24_3 : s3.readReg64 .x24 = d8)
    (hx28_3 : s3.readReg64 .x28 = d0)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s3 ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv (pbToProtoPolyDecoder d) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (match decoderFromPbResult (pbToProtoPolyDecoder d) with
               | .error _ => .error (.err .stateDecode)
               | .ok dec => .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  dsimp only [ekSentCt1ReceivedResultAt]
  refine SepWP.weaken_pre (sepConj_mono_left (v4b_ekSentCt1ReceivedAt_unpack A.repAlloc (fsp + 1888#64) uc)) ?_
  apply v4c_wp_exists_left; intro rkCap; apply v4c_wp_exists_left; intro rkPtr
  apply v4c_wp_exists_left; intro rkLen; apply v4c_wp_exists_left; intro mkCap
  apply v4c_wp_exists_left; intro mkPtr; apply v4c_wp_exists_left; intro mkLen
  apply v4c_wp_exists_left; intro dkCap; apply v4c_wp_exists_left; intro dkPtr
  apply v4c_wp_exists_left; intro dkLen; apply v4c_wp_exists_left; intro ct1Cap
  apply v4c_wp_exists_left; intro ct1Ptr; apply v4c_wp_exists_left; intro ct1Len
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _))
    (Entails.trans (Entails.of_eq (v4d_rot3 _ _ _ _))
      (sepConj_mono_left (v4c_memRegion_224_to_ucSpillSlots fsp)))) ?_
  apply v4c_wp_exists_left; intro v32; apply v4c_wp_exists_left; intro v40
  apply v4c_wp_exists_left; intro v48; apply v4c_wp_exists_left; intro v56
  apply v4c_wp_exists_left; intro v72; apply v4c_wp_exists_left; intro v80
  apply v4c_wp_exists_left; intro v128; apply v4c_wp_exists_left; intro v136
  apply v4c_wp_exists_left; intro v144; apply v4c_wp_exists_left; intro v216
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (v4d_rot4 _ _ _ _ _))
      (sepConj_mono_left (v4c_memRegion_1652_split_896 fsp))) ?_
  apply v4c_wp_exists_left; intro s896; apply v4c_wp_exists_left; intro s904
  apply v4c_wp_exists_left; intro s912; apply v4c_wp_exists_left; intro s920
  apply v4c_wp_exists_left; intro s924; apply v4c_wp_exists_left; intro s928
  have hrk := v4d_ekSentCt1ReceivedHeap_rk_lt A.repAlloc
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc
  have hd0 := v4d_optProtoPolyDecoderHeap_some_d0_lt A.repAlloc (pbToProtoPolyDecoder d) d0 d8 d16 d24 d28 d32
  have h35448 := Variant4c0PlacedBudget.v4c_step_2308_ok_some_to_35448_placed_budget A lim st (ext := ext)
    s3 fsp out d0 d8 d16 d32 d24 d28
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
    v32 v40 v48 v56 v72 v80 v128 v136 v144 v216
    s896 s904 s912 s920 s924 s928
    (v4b_ekSentCt1ReceivedHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
     v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
     memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
     memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
     memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1992#64) 312 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hfsp_align
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        v4b_ekSentCt1ReceivedHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
        v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        (v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) s896 s904 s912 s920 s924 s928 ∗
         v4b_optProtoUcWordsAt (fsp + 1888#64)
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
         memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
         memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
         memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1992#64) 312 ∗
         stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool lim st s3 ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by dsimp only [fsp]; sep_ac_rfl))
      (Entails.trans (sepConj_mono hrk (sepConj_mono_left hd0)) (Entails.of_eq v4d_pull_pures))) ?_
  apply v4d_sepWP_pure_left; intro hrk_lt
  apply v4d_sepWP_pure_left; intro hd0_lt
  refine v4d_sepWP_seq_clean_lscl hcl3
    (h35448 hrk_lt hd0_lt hpc3 hrun3 hsp3 hx19_3 hx20_3 hx23_3 hx24_3 hx28_3)
    (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro sm hpcm hrunm hclm ⟨_hvm3m, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m,
    hx24_m, hx25_m, hx26_m, hx27_m, hx30_m, htr_m⟩
  have htr_m := htr_m.trans htr3
  have hsp_align_m : sm.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact hfsp_align
  have hpack_dec := v4b_protoPolyDecoderAt_pack A.repAlloc (fsp + 896#64)
    (pbToProtoPolyDecoder d) d0 d8 d16 d24 d28 d32
  have h1888_400 := v4c_ucWords_312_entails_400_16 fsp
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
  have hpre_ent :
      (memRegion (fsp + 1888#64) polyDecoderSize ∗
       protoPolynomialDecoderAt A.repAlloc (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
       A.pool lim st sm ∗ stackAt fsp decoderFromPbStack) ⊢
      (withLsCodeLoaded lsmpl (decoderFromPbSpec M A lim)).pre
        (⟨fsp + 1888#64, fsp + 896#64, pbToProtoPolyDecoder d⟩, st) sm := by
    dsimp only [withLsCodeLoaded, decoderFromPbSpec]
    rw [hsp_m, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl sm.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hclm (Entails.pure_right ⟨hx0_m, hx1_m, hfits,
      by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (sm.readReg64 .x30); rw [show sm.readReg64 .x30 = _ from hx30_m]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.weaken_pre ?_
    (SepWP.call_subroutine_frame hdec
      (x := (⟨fsp + 1888#64, fsp + 896#64, pbToProtoPolyDecoder d⟩, st))
      (F := v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
          mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
        ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
        memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
        memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗
        v4b_ekSentCt1ReceivedHeap A.repAlloc
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
        statesFromPbJumpTablePlacedAt)
      hpcm hrunm hsp_align_m hx30_m
      (fun R' hm => by
        rw [sepConj_assoc] at hm
        exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
      (fun _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      ?_
      (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm)))
  · dsimp only [polyDecoderSize, decoderFromPbStack]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (v4b_optProtoUcWordsAt (fsp + 1888#64)
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
         memRegion (fsp + 1992#64) 312) ∗
        (v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) d0 d8 d16 d24 d28 d32 ∗
         v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32) ∗
        (A.pool lim st sm ∗ stackAt fsp encoderFromPbStack ∗
         v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
           mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
         memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
         memRegion (fsp + 936#64) 952 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         v4b_ekSentCt1ReceivedHeap A.repAlloc
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
         statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
      (Entails.trans (sepConj_mono h1888_400 (sepConj_mono_left hpack_dec))
        (Entails.of_eq (by sep_ac_rfl)))
  · intro s4 hpc4 hrun4 hsp4 hcs4
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, _, hvregs_4⟩
    rw [hx19_m] at hx19_4; rw [hx20_m] at hx20_4; rw [hx21_m] at hx21_4
    rw [hx22_m] at hx22_4; rw [hx23_m] at hx23_4; rw [hx24_m] at hx24_4
    rw [hx25_m] at hx25_4; rw [hx26_m] at hx26_4; rw [hx27_m] at hx27_4
    rw [hsp_m] at hsp4
    dsimp only [withLsCodeLoaded, decoderFromPbSpec, protoPolynomialDecoderSize, decoderFromPbStack]
    rw [sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_elim; intro evs1
    rw [sepConj_assoc]
    apply ProofLib.SepWP.pure_elim; rintro ⟨htr4_m, _hacp4, henv1⟩
    have htr4 : TraceCalleeSaved s4 s0 := ⟨htr4_m.trans htr_m.1, hvregs_4.trans htr_m.2⟩
    have h1652 := v4c_memRegion_660_40_952_entails_1652 fsp
    have hpost_merge :
        (resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
          memRegion (fsp + 896#64) 40 ∗
          A.pool lim (M.stepEvents evs1 st) s4 ∗
          stackAt sm.sp encoderFromPbStack) ∗
        (v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
           mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
         memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
         memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         v4b_ekSentCt1ReceivedHeap A.repAlloc
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
         statesFromPbJumpTablePlacedAt) ⊢
        resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
          memRegion (fsp + 152#64) 64 ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
          memRegion (fsp + 236#64) 1652 ∗
          stackAt fsp encoderFromPbStack ∗
          memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
          memRegion (fsp + 88#64) 40 ∗
          v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
          v4b_ekSentCt1ReceivedHeap A.repAlloc
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs1 st) s4 := by
      rw [hsp_m]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (fsp + 236#64) 660 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952) ∗
          (resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
           memRegion (fsp + 152#64) 64 ∗
           ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
           stackAt fsp encoderFromPbStack ∗
           memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
           memRegion (fsp + 88#64) 40 ∗
           v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
             mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
           memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
           v4b_ekSentCt1ReceivedHeap A.repAlloc
             rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
           statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs1 st) s4) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left h1652) (Entails.of_eq (by sep_ac_rfl)))
    refine SepWP.weaken_pre hpost_merge ?_
    cases hres : decoderFromPbResult (pbToProtoPolyDecoder d) with
    | error e =>
      have herr := Variant4cPlacedBudget.v4c_step_2472_err_to_ret_of_placedHooks
        hA (M.stepEvents evs1 st) s0 s4 out pbA
        rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len
        uc e d32 d28 hsp0_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx26_4 htr4
      refine SepWP.mono herr fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
      refine ⟨evs1 ++ evs2, fromPbDecEnv_append_freeOnly henv1 hevs2, ?_, hsp_f, hcs_f, htr_f⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact hPf
    | ok dec =>
      dsimp only [resultPolyDecoderFromPbAt]
      refine SepWP.weaken_pre (sepConj_mono_left (v4c_polyDecoderAt_unpack A.repAlloc (fsp + 1888#64) dec)) ?_
      apply v4c_wp_exists_left; intro dw
      have hok := Variant4cPlacedBudget.v4c_step_2472_ok_to_ret_of_sub_placed
        A lim (M.stepEvents evs1 st) hA.memcpy_ok s0 s4 out pbA
        rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len
        uc dec dw d32 d28 hsp0_align hpc4 hrun4 hsp4
        hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 htr4
      refine SepWP.weaken_pre (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl))
        (SepWP.mono hok fun sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, _hvm4f⟩ => ?_)
      exact ⟨evs1, henv1, hPf, hsp_f, hcs_f, htr_f⟩

theorem v4d_ekSent_2308_ok_some_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s0 s3 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (uc : EkSentCt1Received (spqrAuthApi F))
    (d : PolynomialDecoder)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder d)))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = d16)
    (hx23_3 : s3.readReg64 .x23 = d24.zeroExtend 64)
    (hx24_3 : s3.readReg64 .x24 = d8)
    (hx28_3 : s3.readReg64 .x28 = d0)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s3 ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv (pbToProtoPolyDecoder d) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (match decoderFromPbResult (pbToProtoPolyDecoder d) with
               | .error _ => .error (.err .stateDecode)
               | .ok dec => .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v4d_ekSent_2308_ok_some_to_ret_of_placedHooks_placed hA.toPlacedBudget hdec st
    s0 s3 out pbA d0 d8 d16 d32 d24 d28 uc d hcl3 hfits
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx23_3 hx24_3 hx28_3 htr3

theorem v4d_ekSent_2308_ok_some_to_ret_sepWPp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s0 s3 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (uc : EkSentCt1Received (spqrAuthApi F))
    (d : PolynomialDecoder)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder d)))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = d16)
    (hx23_3 : s3.readReg64 .x23 = d24.zeroExtend 64)
    (hx24_3 : s3.readReg64 .x24 = d8)
    (hx28_3 : s3.readReg64 .x28 = d0)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s3 ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv (pbToProtoPolyDecoder d) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (match decoderFromPbResult (pbToProtoPolyDecoder d) with
               | .error _ => .error (.err .stateDecode)
               | .ok dec => .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      Qp :=
  SepWPp.of_sepWP_ret
    (v4d_ekSent_2308_ok_some_to_ret_of_placedHooks_placed hA hdec st
      s0 s3 out pbA d0 d8 d16 d32 d24 d28 uc d hcl3 hfits
      hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx23_3 hx24_3 hx28_3 htr3)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudget
