/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9d
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`)

Total-correctness (`SepWP`) relocatable continuations (`+2864`, `+2768`, `+444 -> s0.x30`) and
top-level `subroutine_ok` contracts for Variant 9 (`InnerState.ct1Acknowledged`) under
`Ct1AcknowledgedFromPbEnv` and `StatesFromPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsProg_333 lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder States V1State pbToProtoPolyDecoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize dropStack32 optProtoInnerStateAt optProtoInnerStateSize
   protoChunkedCt1AcknowledgedAt protoInnerStateAt protoUnchunkedCt1SentAt
   protoUnchunkedCt1SentSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize
   resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 decoderFromPbResult
   decoderFromPbStack resultChunkedStatesAt sp_sub_2400_align statesFromPbJumpTablePlacedAt
   statesFromPbSavedCells statesFromPbStack v9_Saved5368Preserved v9_byte_region119_to_words
   v9_ct1SentAt_unpack v9_ct1SentHeap v9_ct1SentHeap_rkCap_lt v9_ct1Sent_from_pb_err_eq
   v9_fsp_1888_err_entails_2304 v9_fsp_2864_none_collapse v9_memRegion_1392_1520_entails_1888
   v9_memRegion_1888_2016_eq_400_16 v9_memRegion_1888_split_none v9_memRegion_1888_split_some
   v9_memRegion_2304_split_2768 v9_optProtoPolyDecoderAt_unpack v9_optProtoPolyDecoderHeap
   v9_optProtoPolyDecoderHeap_some_cap_lt v9_optProtoPolyDecoderWordsAt v9_optProtoUcAt_unpack
   v9_optProtoUcHeap v9_optProtoUcHeap_some_cap_lt v9_optProtoUcWordsAt
   v9_optProtoUcWordsAt_entails_128 v9_pbA_128_entails_224 v9_pbA_entails_224 v9_protoUcAt_pack
   v9_stackAt_allocHook_to_drop32 v9_stackAt_allocHook_to_encoderFromPbStack
   v9_stackAt_drop32_to_allocHook v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb
   v9_stackAt_encoderFromPbStack_to_allocHook v9_states_from_pb_ct1Acknowledged_ptsNeeded_ne
   v9_states_from_pb_ct1Acknowledged_uc_none_dec_none
   v9_states_from_pb_ct1Acknowledged_uc_none_dec_some
   v9_states_from_pb_ct1Acknowledged_uc_some_dec_none
   v9_states_from_pb_ct1Acknowledged_uc_some_dec_some)
open CryptoVerification.SpqrV1.Unchunked
  (ct1SentFromPbStack ct1SentResultAt extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget (sepWPp_seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudget
  (v9_states_from_pb_drop_proto_uc_none_488_placed_budget
   v9_states_from_pb_drop_proto_uc_some_488_placed
   v9_states_from_pb_uc_none_2768_placed_budget v9_sub_ok_decoder_from_pb_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudget
  (v9_step_2864_ok_some_to_3040_placed_budget v9_tail_3044_to_ret_placed
   v9_tail_5360_to_ret_placed v9_tail_5368_to_ret_placed v9_tail_6904_to_ret_placed)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (Ct1SentFromPbPostEnv Ct1SentFromPbPreEnv ct1SentFromPb ct1SentFromPbSpec
   ct1SentFromPbSpecOfEnv)

export Variant9PlacedBudgetAux
  (v9_sub_ok_ct1_sent_from_pb_placed v9_seq_clean_lscl v9_call_ret_lscl v9_call_entails_lscl
   Ct1AcknowledgedUcSomeEnv Ct1AcknowledgedFromPbEnv
   ct1AcknowledgedFromPbEnv_sub_statesFromPbEnv
   fitsEnv_ct1AcknowledgedFromPbEnv_of_statesFromPbEnv)

open Variant9PlacedBudgetAux
  (ct1AcknowledgedUcSomeEnv_of_err ct1AcknowledgedUcSomeEnv_of_ok_none
   ct1AcknowledgedUcSomeEnv_of_ok_some fitsEnv_ct1SentPre_of_ucSomeEnv
   fitsEnv_decAlloc_step_of_ucSomeEnv v9_states_from_pb_copy_uc_to_call_2768_placed_budget
   v9_states_from_pb_step_444_to_2768_none_placed_budget
   v9_states_from_pb_step_444_to_2768_some_placed_budget
   v9_states_from_pb_step_444_to_488_err_placed_budget
   v9_step_2864_err_to_5360_placed_budget v9_step_2864_ok_none_to_6904_placed_budget)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem seq_st {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWP prog ret sm (P_mid sm) Q) :
    SepWP prog ret s P Q :=
  SepWP.seq h1 fun sm _ hpcm hrunm ⟨hPm, hQm⟩ =>
    SepWP.weaken_pre hPm (h2 sm hpcm hrunm hQm)

/-! ## 1. From `+2864` (Return of `<Ct1Sent>::from_pb`) to `s0.x30` -/

set_option maxHeartbeats 800000 in
/-- Total `SepWP` from `+2864` (after `ct1SentFromPb` returns with event prefix `evs1`) to `s0.x30`. -/
theorem v9_tail_2864_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (u : V1State.Unchunked.Ct1Sent) (optDec : Option PolynomialDecoder)
    {evs1 : List AllocEvent}
    (henv1 : Ct1SentFromPbPostEnv F u evs1)
    (hfits : FitsEnv M lim st (Ct1AcknowledgedUcSomeEnv F u optDec))
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 2864#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = w8) (hx21 : s.readReg64 .x21 = w0)
    (hx22 : s.readReg64 .x22 = w16) (hx23 : s.readReg64 .x23 = w32)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0)
    (hpts : ∀ d, optDec = some d → (d.ptsNeeded == 576#32) = true) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (ct1SentResultAt A.repAlloc (fsp + 1888#64) (ct1SentFromPb (spqrAuthApi F) u) ∗
        (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
        v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
        A.pool lim (M.stepEvents evs1 st) s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct1AcknowledgedUcSomeEnv F u optDec evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := optDec }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  let st1 : M.σ := M.stepEvents evs1 st
  cases hres : ct1SentFromPb (spqrAuthApi F) u with
  | error e =>
    have hres_raw : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb
        (spqrAuthApi F) u = .error e := hres
    have he : e = .err .stateDecode := v9_ct1Sent_from_pb_err_eq u hres_raw
    subst he
    have hmod : States.from_pb spqrPolyApi (spqrAuthApi F)
        { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := optDec }) } =
        .error (.err .stateDecode) := by
      cases optDec with
      | none => rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_none u, hres_raw]
      | some d => rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_some u d (hpts d rfl), hres_raw]
    rw [hmod]
    dsimp only [ct1SentResultAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hbw := v9_byte_region119_to_words (fsp + 1896#64) 0#8
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbw
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1896#64) ↦₈ 0#8) ∗ memRegion (fsp + 1897#64) 119) ∗
        (((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
         ((fsp + 1888#64) ↦₆₄ noneCap) ∗
         v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool lim st1 s ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by dsimp only [st1]; sep_ac_rfl))
      (sepConj_mono hbw (sepConj_mono_left (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32)))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w1896; apply ProofLib.SepWP.exists_left; intro w1904
    apply ProofLib.SepWP.exists_left; intro w1912; apply SepWP.pure_elim; intro hw1896
    let RestErr : SepProp :=
      memRegion (fsp + 1920#64) 96 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
      v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
      memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    refine seq_st (mid := lsmpl.base 333 + 5360#64)
      (P_mid := fun s1 =>
        v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st1 s1 ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (Q_regs := fun s1 => v9_Saved5368Preserved s0 s1 fsp out w8 w0 w1896 ∧ s1.readReg64 .x22 = w16) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
        RestErr ∗ A.pool lim st1 s by dsimp only [RestErr]; sep_ac_rfl)) ?_
      refine SepWP.mono
        (v9_step_2864_err_to_5360_placed_budget A lim st1 s0 s fsp out w8 w0 w16
          w1896 w1904 w1912 RestErr hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 htr) ?_
      rintro s1 P1 _ _ ⟨hP1, _, hpres1, hx22_1⟩
      refine ⟨Entails.trans hP1 ?_, hpres1, hx22_1⟩
      dsimp only [RestErr]
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion fsp 1888 ∗ (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ memRegion (fsp + 1920#64) 96) ∗
         memRegion (fsp + 2016#64) 288) ∗
        (v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool lim st1 s1 ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
      exact Entails.trans
        (sepConj_mono_left (v9_fsp_1888_err_entails_2304 fsp noneCap w1896 w1904 w1912))
        (Entails.of_eq (by sep_ac_rfl))
    · rintro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
      refine SepWP.mono
        (v9_tail_5360_to_ret_placed (F := F) hA st1 s0 s1 fsp out pbA w0 w8 w16 d24 d28 w32 w1896
          (optDec.map pbToProtoPolyDecoder) .stateDecode hsp0_align hfsp_eq hpc1 hrun1 hpres1 hx22_1 hw1896) ?_
      rintro sf Pf _ _ ⟨evs2, hfree2, hPf, hsp_f, hcs_f, htr_f⟩
      have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
        dsimp only [st1]; rw [M.stepEvents_append]
      rw [hst_eq] at hPf
      exact ⟨⟨evs1 ++ evs2, ct1AcknowledgedUcSomeEnv_of_err hres henv1 hfree2, hPf⟩,
        hsp_f, hcs_f, htr_f⟩
  | ok uc =>
    have hres_raw : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb
        (spqrAuthApi F) u = .ok uc := hres
    dsimp only [ct1SentResultAt]
    refine SepWP.weaken_pre (sepConj_mono_left (v9_ct1SentAt_unpack A.repAlloc (fsp + 1888#64) uc)) ?_
    simp only [sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro rkCap; apply ProofLib.SepWP.exists_left; intro rkPtr
    apply ProofLib.SepWP.exists_left; intro rkLen; apply ProofLib.SepWP.exists_left; intro mkCap
    apply ProofLib.SepWP.exists_left; intro mkPtr; apply ProofLib.SepWP.exists_left; intro mkLen
    apply ProofLib.SepWP.exists_left; intro hdrCap; apply ProofLib.SepWP.exists_left; intro hdrPtr
    apply ProofLib.SepWP.exists_left; intro hdrLen; apply ProofLib.SepWP.exists_left; intro esCap
    apply ProofLib.SepWP.exists_left; intro esPtr; apply ProofLib.SepWP.exists_left; intro esLen
    apply ProofLib.SepWP.exists_left; intro ct1Cap; apply ProofLib.SepWP.exists_left; intro ct1Ptr
    apply ProofLib.SepWP.exists_left; intro ct1Len
    refine SepWP.weaken_pre (Entails.trans (sepConj_mono_left (sepConj_mono_right
        (v9_ct1SentHeap_rkCap_lt A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc)))
      (Entails.of_eq (show _ = ⌜rkCap.toNat < 2 ^ 63⌝ ∗
        (v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
         v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool lim st1 s ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by dsimp only [st1]; sep_ac_rfl))) ?_
    apply SepWP.pure_elim; intro hrk_lt
    cases optDec with
    | none =>
      rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_none u, hres_raw]
      dsimp only [Option.map, v9_optProtoPolyDecoderHeap]
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = ⌜w0 = noneCap⌝ ∗
          (((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
            v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
           memRegion fsp 1888 ∗
           (v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
            v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
            memRegion (fsp + 2016#64) 288 ∗ A.pool lim st1 s ∗ stackAt fsp encoderFromPbStack ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by sep_ac_rfl))
        (sepConj_mono_right (sepConj_mono (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32)
          (sepConj_mono_left (v9_memRegion_1888_split_none fsp))))) ?_
      apply SepWP.pure_elim; rintro rfl
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro w248; apply ProofLib.SepWP.exists_left; intro w240
      apply ProofLib.SepWP.exists_left; intro w152; apply ProofLib.SepWP.exists_left; intro w144
      apply ProofLib.SepWP.exists_left; intro w128; apply ProofLib.SepWP.exists_left; intro d96
      apply ProofLib.SepWP.exists_left; intro w72
      let RestNone : SepProp :=
        memRegion fsp 72 ∗ memRegion (fsp + 80#64) 16 ∗ memRegion (fsp + 100#64) 28 ∗
        memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 80 ∗ memRegion (fsp + 255#64) 1633 ∗
        memRegion (fsp + 2016#64) 288 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
      refine seq_st (mid := lsmpl.base 333 + 6904#64)
        (P_mid := fun s1 =>
          memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
          v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool lim st1 s1 ∗ stackAt fsp encoderFromPbStack ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = mkPtr ∧ s1.readReg64 .x1 = mkCap ∧
          s1.readReg64 .x10 = rkCap ∧ s1.readReg64 .x13 = ct1Cap ∧ s1.readReg64 .x14 = ct1Ptr ∧
          s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ ((fsp + 128#64) ↦₆₄ w128) ∗
          ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
          ((fsp + 248#64) ↦ₛ loBytes7 w248) ∗
          v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
          RestNone ∗ A.pool lim st1 s by dsimp only [RestNone]; sep_ac_rfl)) ?_
        refine SepWP.mono
          (v9_step_2864_ok_none_to_6904_placed_budget A lim st1 s0 s fsp out
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
            w72 w128 w144 w152 w240 w248 d96 RestNone
            hfsp_align hrk_lt hpc hrun hsp hx19 hx21 hx25 htr) ?_
        rintro s1 P1 _ _ ⟨hP1, _, hregs1⟩
        refine ⟨Entails.trans hP1 ?_, hregs1⟩
        dsimp only [RestNone]
        have hcol := v9_fsp_2864_none_collapse fsp
          (unshiftWord ct1Len (loByte uc.epoch)) uc.epoch ((loByte ct1Len).zeroExtend 32)
        refine Entails.trans (Entails.of_eq (show _ =
          ((memRegion (fsp + 80#64) 16 ∗ ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
            memRegion (fsp + 100#64) 28) ∗
           (memRegion (fsp + 160#64) 80 ∗
            ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
            ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 1633 ∗
            memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288)) ∗
          (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗
           memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
           v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool lim st1 s1 ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hcol) (Entails.of_eq (by sep_ac_rfl))
      · rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx10_1, hx13_1, hx14_1, hx19_1, hx28_1, htr1⟩
        refine SepWP.mono
          (v9_tail_6904_to_ret_placed (F := F) hA st1 s0 s1 fsp out pbA
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
            hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx0_1 hx1_1 hx10_1 hx13_1 hx14_1 hx19_1 hx28_1 htr1) ?_
        rintro sf Pf _ _ ⟨evs2, hfree2, hPf, hsp_f, hcs_f, htr_f⟩
        have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
          dsimp only [st1]; rw [M.stepEvents_append]
        rw [hst_eq] at hPf
        exact ⟨⟨evs1 ++ evs2, ct1AcknowledgedUcSomeEnv_of_ok_none hres henv1 hfree2, hPf⟩,
          hsp_f, hcs_f, htr_f⟩
    | some d =>
      rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_some u d (hpts d rfl), hres_raw]
      dsimp only [Option.map]
      have hdec_fits : FitsEnv M lim st1 (FromPbDecAllocEnv (pbToProtoPolyDecoder d)) :=
        fitsEnv_decAlloc_step_of_ucSomeEnv d hres henv1 hfits
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
          v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
          memRegion fsp 1888 ∗
          (v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
           v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
           memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
           A.pool lim st1 s ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl))
        (sepConj_mono
          (v9_optProtoPolyDecoderHeap_some_cap_lt A.repAlloc (pbToProtoPolyDecoder d) w0 w8 w16 d24 d28 w32)
          (sepConj_mono_left (v9_memRegion_1888_split_some fsp)))) ?_
      rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hw0_lt, _⟩
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro w248; apply ProofLib.SepWP.exists_left; intro w240
      apply ProofLib.SepWP.exists_left; intro w216; apply ProofLib.SepWP.exists_left; intro w200
      apply ProofLib.SepWP.exists_left; intro w152; apply ProofLib.SepWP.exists_left; intro w144
      apply ProofLib.SepWP.exists_left; intro w136; apply ProofLib.SepWP.exists_left; intro w128
      apply ProofLib.SepWP.exists_left; intro d96; apply ProofLib.SepWP.exists_left; intro w80
      apply ProofLib.SepWP.exists_left; intro w72; apply ProofLib.SepWP.exists_left; intro w56
      apply ProofLib.SepWP.exists_left; intro w48; apply ProofLib.SepWP.exists_left; intro w40
      let RestSome : SepProp :=
        (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
        memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
        memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
        memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 936#64) 952 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
      let FrameDec : SepProp :=
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗
        memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗
        memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize
      refine v9_seq_clean_lscl hcl (mid := lsmpl.base 376)
        (P_mid := fun s1 =>
          (protoPolynomialDecoderAt A.repAlloc (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
            memRegion (fsp + 1888#64) 400 ∗ A.pool lim st1 s1 ∗ stackAt fsp decoderFromPbStack) ∗
          FrameDec)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧
          s1.readReg64 .x1 = fsp + 896#64 ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x21 = fsp + 848#64 ∧ s1.readReg64 .x24 = fsp + 1888#64 ∧
          s1.readReg64 .x25 = esLen ∧ s1.readReg64 .x26 = rkLen ∧ s1.readReg64 .x28 = rkPtr ∧
          s1.readReg64 .x30 = lsmpl.base 333 + 3044#64 ∧ TraceCalleeSaved s1 s0) ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
          ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗
          ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗ ((fsp + 144#64) ↦₆₄ w144) ∗
          ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
          ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ loBytes7 w248) ∗
          memRegion (fsp + 896#64) 40 ∗
          v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
          v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
          RestSome ∗ A.pool lim st1 s by dsimp only [RestSome]; sep_ac_rfl)) ?_
        refine SepWP.mono
          (v9_step_2864_ok_some_to_3040_placed_budget A lim st1 s0 s fsp out pbA
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
            w0 w8 w16 d24 d28 w32 d w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 d96
            RestSome hfsp_align hrk_lt hw0_lt hpc hrun hsp hx19 hx20 hx21 hx23 hx25 hx27 htr) ?_
        rintro s1 P1 _ _
          ⟨hP1, _, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        rw [hx24] at hx24_1
        refine ⟨Entails.trans hP1 ?_, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1,
          hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        dsimp only [RestSome, FrameDec]
        refine Entails.trans (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
          (memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288) ∗ stackAt fsp decoderFromPbStack ∗
          (protoPolynomialDecoderAt A.repAlloc (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
           A.pool lim st1 s1 ∗
           ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
           ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
           ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
           ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
           ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
           ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
           ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗
           memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗
           memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗
           memRegion (fsp + 936#64) 952 ∗
           v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
        rw [v9_memRegion_1888_2016_eq_400_16 fsp]
        exact Entails.trans
          (sepConj_mono_left (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32))
          (Entails.of_eq (by sep_ac_rfl))
      · rintro s1 hpc1 hrun1 hcl1
          ⟨hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        have hsp1_align : s1.spAligned = true := by
          unfold State.spAligned; rw [hsp1]; exact hfsp_align
        refine v9_call_entails_lscl (v9_sub_ok_decoder_from_pb_placed hDec)
          (x := (⟨fsp + 1888#64, fsp + 896#64, pbToProtoPolyDecoder d⟩, st1))
          (Frame := FrameDec) hcl1 hpc1 hrun1 hsp1_align hx30_1
          (by
            dsimp only [DefsBudget.decoderFromPbSpec, polyDecoderSize]
            rw [hsp1]
            exact Entails.pure_right ⟨hx0_1, hx1_1, hdec_fits, by rw [show s1.readReg64 .lr = _ from hx30_1]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.of_eq (by sep_ac_rfl))) ?_
        intro s2 hpc2 hrun2 _hcl2 hsp2 hcs2
        obtain ⟨hx19_2, _, hx21_2, _, _, hx24_2, hx25_2, hx26_2, _, hx28_2, _, hvregs_2⟩ := hcs2
        rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; rw [hx21_1] at hx21_2
        rw [hx24_1] at hx24_2; rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx28_1] at hx28_2
        dsimp only [DefsBudget.decoderFromPbSpec, protoPolynomialDecoderSize]
        rw [hsp1, sepExists_sepConj_left]
        apply ProofLib.SepWP.exists_left; intro evs2
        rw [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨htr2_eq, _, henv2⟩
        have htr2 : TraceCalleeSaved s2 s0 := ⟨htr2_eq.trans htr1.1, hvregs_2.trans htr1.2⟩
        refine SepWP.weaken_pre (Entails.of_eq (show _ =
          resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
          ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
          ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
          ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗
          memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗
          memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗
          memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
          v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs2 st1) s2 ∗
          stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize by dsimp only [FrameDec]; sep_ac_rfl)) ?_
        refine SepWP.mono
          (v9_tail_3044_to_ret_placed (F := F) hA (M.stepEvents evs2 st1) s0 s2 fsp out pbA
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc d
            hsp0_align hfsp_eq hpc2 hrun2 hsp2
            hx19_2 hx21_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2) ?_
        rintro sf Pf _ _ ⟨evs3, hfree3, _, hPf, hsp_f, hcs_f, htr_f⟩
        have hst_eq : M.stepEvents evs3 (M.stepEvents evs2 st1) =
            M.stepEvents (evs1 ++ evs2 ++ evs3) st := by
          dsimp only [st1]
          rw [List.append_assoc, M.stepEvents_append, M.stepEvents_append]
        rw [hst_eq] at hPf
        exact ⟨⟨evs1 ++ evs2 ++ evs3,
          ct1AcknowledgedUcSomeEnv_of_ok_some hres d henv1 henv2 hfree3, hPf⟩,
          hsp_f, hcs_f, htr_f⟩

/-! ## 2. From `+2768` (Check & Copy `uc`, Call `<Ct1Sent>::from_pb`) to `s0.x30` -/

set_option maxHeartbeats 800000 in
/-- Total `SepWP` from `+2768` (after validating `receivingEk`) to `s0.x30`. -/
theorem v9_tail_2768_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) (optDec : Option PolynomialDecoder)
    (hfits_uc : ∀ u, optUc = some u → FitsEnv M lim st (Ct1AcknowledgedUcSomeEnv F u optDec))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 2768#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = u0)
    (hx9 : s.readReg64 .x9 = ((loByte u8).zeroExtend 32).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = w8) (hx21 : s.readReg64 .x21 = w0)
    (hx22 : s.readReg64 .x22 = w16) (hx23 : s.readReg64 .x23 = w32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0)
    (hpts : ∀ d, optDec = some d → (d.ptsNeeded == 576#32) = true) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((pbA ↦₆₄ 0x8000000000000009#64) ∗
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
        v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ A.pool lim st s ∗
        stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct1AcknowledgedFromPbEnv F { uc := optUc, receivingEk := optDec } evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Acknowledged { uc := optUc, receivingEk := optDec }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases optUc with
  | none =>
    have hmod : States.from_pb spqrPolyApi (spqrAuthApi F)
        { innerState := some (.ct1Acknowledged { uc := none, receivingEk := optDec }) } =
        .error (.err .stateDecode) := by
      cases optDec with
      | none => exact v9_states_from_pb_ct1Acknowledged_uc_none_dec_none
      | some d => exact v9_states_from_pb_ct1Acknowledged_uc_none_dec_some d (hpts d rfl)
    rw [hmod]; dsimp only [v9_optProtoUcHeap]
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = ⌜u0 = noneCap⌝ ∗
        (((pbA ↦₆₄ 0x8000000000000009#64) ∗
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
         (v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
          A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left
        (v9_pbA_entails_224 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d24 d28 w32)))) ?_
    apply SepWP.pure_elim; rintro rfl
    let RestUcNone : SepProp :=
      v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
      memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
      memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    refine seq_st (mid := lsmpl.base 333 + 5360#64)
      (P_mid := fun s1 =>
        v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s1 ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (Q_regs := fun s1 => v9_Saved5368Preserved s0 s1 fsp out w8 w0 0#64 ∧ s1.readReg64 .x22 = w16) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (show _ = A.pool lim st s ∗ RestUcNone by
          dsimp only [RestUcNone]; sep_ac_rfl)) ?_
      refine SepWP.mono
        (v9_states_from_pb_uc_none_2768_placed_budget A lim st s0 s fsp out w8 w0 w16 RestUcNone
          hpc hrun hsp hx8 hx19 hx20 hx21 hx22 htr) ?_
      rintro s1 P1 _ _ ⟨hP1, _, hpres1, hx22_1⟩
      exact ⟨Entails.trans hP1 (Entails.of_eq (by dsimp only [RestUcNone]; sep_ac_rfl)), hpres1, hx22_1⟩
    · rintro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
      refine SepWP.mono
        (v9_tail_5360_to_ret_placed (F := F) hA st s0 s1 fsp out pbA w0 w8 w16 d24 d28 w32 0#64
          (optDec.map pbToProtoPolyDecoder) .stateDecode hsp0_align hfsp_eq hpc1 hrun1 hpres1 hx22_1 rfl) ?_
      rintro sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩
      have henv : Ct1AcknowledgedFromPbEnv F { uc := none, receivingEk := optDec } evs := by
        unfold Ct1AcknowledgedFromPbEnv
        cases optDec <;> exact hfree
      exact ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩
  | some u =>
    have hfits_u : FitsEnv M lim st (Ct1AcknowledgedUcSomeEnv F u optDec) := hfits_uc u rfl
    have hct1_fits : FitsEnv M lim st (Ct1SentFromPbPreEnv F u) :=
      fitsEnv_ct1SentPre_of_ucSomeEnv hfits_u
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v9_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        memRegion fsp 2304 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl))
      (sepConj_mono
        (v9_optProtoUcHeap_some_cap_lt A.repAlloc u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
        (sepConj_mono_left (v9_memRegion_2304_split_2768 fsp)))) ?_
    rw [sepConj_assoc]; apply SepWP.pure_elim; intro hu0_lt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro z1512; apply ProofLib.SepWP.exists_left; intro z1504
    apply ProofLib.SepWP.exists_left; intro z1496; apply ProofLib.SepWP.exists_left; intro z1488
    apply ProofLib.SepWP.exists_left; intro z1480; apply ProofLib.SepWP.exists_left; intro z1472
    apply ProofLib.SepWP.exists_left; intro z1464; apply ProofLib.SepWP.exists_left; intro z1456
    apply ProofLib.SepWP.exists_left; intro z1448; apply ProofLib.SepWP.exists_left; intro z1440
    apply ProofLib.SepWP.exists_left; intro z1432; apply ProofLib.SepWP.exists_left; intro z1424
    apply ProofLib.SepWP.exists_left; intro z1417; apply ProofLib.SepWP.exists_left; intro z1409
    apply ProofLib.SepWP.exists_left; intro z1401; apply ProofLib.SepWP.exists_left; intro b1400
    apply ProofLib.SepWP.exists_left; intro z1392
    let RestCopy : SepProp :=
      v9_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
      (pbA ↦₆₄ 0x8000000000000009#64) ∗
      v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
      v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
      memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗
      memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288 ∗
      stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    let FrameCt1 : SepProp :=
      memRegion (fsp - 5152#64) 816 ∗ (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
      v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
      v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
      memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗
      memRegion (fsp + 2016#64) 288 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    refine v9_seq_clean_lscl hcl (mid := lsmpl.base 339)
      (P_mid := fun s1 =>
        (protoUnchunkedCt1SentAt A.repAlloc (fsp + 1392#64) u ∗
          memRegion (fsp + 1888#64) 128 ∗ A.pool lim st s1 ∗ stackAt fsp ct1SentFromPbStack) ∗
        FrameCt1)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧
        s1.readReg64 .x1 = fsp + 1392#64 ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = w8 ∧ s1.readReg64 .x21 = w0 ∧ s1.readReg64 .x22 = w16 ∧
        s1.readReg64 .x23 = w32 ∧ s1.readReg64 .x24 = fsp + 1888#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x27 = pbA ∧
        s1.readReg64 .x30 = lsmpl.base 333 + 2864#64 ∧ TraceCalleeSaved s1 s0) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        ((fsp + 1392#64) ↦₆₄ z1392) ∗ ((fsp + 1400#64) ↦₈ b1400) ∗ ((fsp + 1401#64) ↦₆₄ z1401) ∗
        ((fsp + 1409#64) ↦₆₄ z1409) ∗ ((fsp + 1417#64) ↦ₛ loBytes7 z1417) ∗
        ((fsp + 1424#64) ↦₆₄ z1424) ∗ ((fsp + 1432#64) ↦₆₄ z1432) ∗ ((fsp + 1440#64) ↦₆₄ z1440) ∗
        ((fsp + 1448#64) ↦₆₄ z1448) ∗ ((fsp + 1456#64) ↦₆₄ z1456) ∗ ((fsp + 1464#64) ↦₆₄ z1464) ∗
        ((fsp + 1472#64) ↦₆₄ z1472) ∗ ((fsp + 1480#64) ↦₆₄ z1480) ∗ ((fsp + 1488#64) ↦₆₄ z1488) ∗
        ((fsp + 1496#64) ↦₆₄ z1496) ∗ ((fsp + 1504#64) ↦₆₄ z1504) ∗ ((fsp + 1512#64) ↦₆₄ z1512) ∗
        RestCopy ∗ A.pool lim st s by dsimp only [RestCopy]; sep_ac_rfl)) ?_
      refine SepWP.mono
        (v9_states_from_pb_copy_uc_to_call_2768_placed_budget A lim st s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 w0 w8 w16 w32
          z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472 z1480 z1488 z1496
          z1504 z1512 b1400 RestCopy
          hfsp_align hu0_lt hpc hrun hsp hx8 hx9 hx13 hx19 hx20 hx21 hx22 hx23 hx25 hx27 htr) ?_
      rintro s1 P1 _ _
        ⟨hP1, _, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
         hx27_1, _, hx30_1, htr1⟩
      refine ⟨Entails.trans hP1 ?_, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1,
        hx24_1, hx25_1, hx27_1, hx30_1, htr1⟩
      dsimp only [RestCopy, FrameCt1]
      rw [v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120) ∗
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        (memRegion (fsp + 1888#64) 128 ∗ A.pool lim st s1 ∗ stackAt fsp ct1SentFromPbStack ∗
         memRegion (fsp - 5152#64) 816 ∗ (pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗
         memRegion (fsp + 2016#64) 288 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono
        (v9_protoUcAt_pack A.repAlloc (fsp + 1392#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
        (sepConj_mono_left
          (v9_optProtoUcWordsAt_entails_128 (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)))
        (Entails.of_eq (by sep_ac_rfl))
    · rintro s1 hpc1 hrun1 hcl1
        ⟨hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx30_1, htr1⟩
      have hsp1_align : s1.spAligned = true := by
        unfold State.spAligned; rw [hsp1]; exact hfsp_align
      refine v9_call_entails_lscl (v9_sub_ok_ct1_sent_from_pb_placed (F := F) hA)
        (x := (⟨fsp + 1888#64, fsp + 1392#64, u⟩, st))
        (Frame := FrameCt1) hcl1 hpc1 hrun1 hsp1_align hx30_1
        (by
          dsimp only [ct1SentFromPbSpec, ct1SentFromPbSpecOfEnv, protoUnchunkedCt1SentSize]
          rw [hsp1]
          exact Entails.pure_right ⟨hx0_1, hx1_1, hct1_fits, by
            simp (config := { decide := true }) [show s1.readReg64 .lr = _ from hx30_1, wp_norm]⟩
            (Entails.of_eq (by sep_ac_rfl))) ?_
      intro s2 hpc2 hrun2 hcl2 hsp2 hcs2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, _, hx27_2, _, _, hvregs_2⟩ := hcs2
      rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2
      rw [hx21_1] at hx21_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
      rw [hx24_1] at hx24_2; rw [hx25_1] at hx25_2; rw [hx27_1] at hx27_2
      dsimp only [ct1SentFromPbSpec, ct1SentFromPbSpecOfEnv, protoUnchunkedCt1SentSize]
      rw [hsp1]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro evs1
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ⌜s2.trace = s1.trace⌝ ∗ ⌜Ct1SentFromPbPostEnv F u evs1⌝ ∗
        ((memRegion fsp 1392 ∗ memRegion (fsp + 1392#64) 128 ∗ memRegion (fsp + 1520#64) 368) ∗
         (stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816) ∗
         (ct1SentResultAt A.repAlloc (fsp + 1888#64) (ct1SentFromPb (spqrAuthApi F) u) ∗
          (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
          v9_optProtoPolyDecoderHeap A.repAlloc (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
          memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize))
        by dsimp only [FrameCt1]; sep_ac_rfl)) ?_
      apply SepWP.pure_elim; intro htr2_eq
      apply SepWP.pure_elim; intro henv1
      have htr2 : TraceCalleeSaved s2 s0 := ⟨htr2_eq.trans htr1.1, hvregs_2.trans htr1.2⟩
      refine SepWP.weaken_pre
        (Entails.trans (sepConj_mono_left (v9_memRegion_1392_1520_entails_1888 fsp)) ?_)
        (SepWP.mono
          (v9_tail_2864_to_ret_placed hA hDec st u optDec henv1 hfits_u s0 s2 hcl2 fsp out pbA
            w0 w8 w16 d24 d28 w32
            hsp0_align hfsp_eq hpc2 hrun2 hsp2
            hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 htr2 hpts) ?_)
      · rw [← v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb fsp]
        exact Entails.of_eq (by sep_ac_rfl)
      · rintro sf Pf _ _ ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩
        have henv_top : Ct1AcknowledgedFromPbEnv F { uc := some u, receivingEk := optDec } evs := by
          unfold Ct1AcknowledgedFromPbEnv
          cases optDec with
          | none => exact henv
          | some d =>
            dsimp only
            simp only [hpts d rfl, ↓reduceIte]
            exact henv
        exact ⟨⟨evs, henv_top, hPf⟩, hsp_f, hcs_f, htr_f⟩

/-! ## 3. Variant 9 (`Ct1Acknowledged`, `+444`) & Top-Level `subroutine_ok` Contracts -/

set_option maxHeartbeats 800000 in
/-- Total `SepWP` for Variant 9 (`Ct1Acknowledged`) from the switch target `+444` to `s0.x30`
    under its exact binary allocation envelope `Ct1AcknowledgedFromPbEnv F st_pb`. -/
theorem states_from_pb_ct1Acknowledged_444_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (fsp out pbA : BitVec 64)
    (st_pb : V1State.Chunked.Ct1Acknowledged)
    (hfits : FitsEnv M lim st (Ct1AcknowledgedFromPbEnv F st_pb))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64) (hx19 : s.readReg64 .x19 = out)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (optProtoInnerStateAt A.repAlloc pbA (some (.ct1Acknowledged st_pb)) ∗
        A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct1AcknowledgedFromPbEnv F st_pb evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Acknowledged st_pb) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  rcases st_pb with ⟨optUc, optDec⟩
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1AcknowledgedAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v9_optProtoUcAt_unpack A.repAlloc (pbA + 8#64) optUc)
      (sepConj_mono_left
        (v9_optProtoPolyDecoderAt_unpack A.repAlloc (pbA + 136#64) (optDec.map pbToProtoPolyDecoder))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0; apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16; apply ProofLib.SepWP.exists_left; intro d24
  apply ProofLib.SepWP.exists_left; intro d28; apply ProofLib.SepWP.exists_left; intro w32
  apply ProofLib.SepWP.exists_left; intro u0; apply ProofLib.SepWP.exists_left; intro u8
  apply ProofLib.SepWP.exists_left; intro u16; apply ProofLib.SepWP.exists_left; intro u24
  apply ProofLib.SepWP.exists_left; intro u32; apply ProofLib.SepWP.exists_left; intro u40
  apply ProofLib.SepWP.exists_left; intro u48; apply ProofLib.SepWP.exists_left; intro u56
  apply ProofLib.SepWP.exists_left; intro u64; apply ProofLib.SepWP.exists_left; intro u72
  apply ProofLib.SepWP.exists_left; intro u80; apply ProofLib.SepWP.exists_left; intro u88
  apply ProofLib.SepWP.exists_left; intro u96; apply ProofLib.SepWP.exists_left; intro u104
  apply ProofLib.SepWP.exists_left; intro u112; apply ProofLib.SepWP.exists_left; intro u120
  cases optDec with
  | none =>
    dsimp only [Option.map, v9_optProtoPolyDecoderHeap]
    let Rest444None : SepProp :=
      (pbA ↦₆₄ 0x8000000000000009#64) ∗
      v9_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
      memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ stackAt fsp encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    refine SepWP.weaken_pre (Entails.of_eq (show _ = ⌜w0 = noneCap⌝ ∗
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
       v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
       Rest444None ∗ A.pool lim st s) by dsimp only [Rest444None]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim; rintro rfl
    refine v9_seq_clean_lscl hcl
      (v9_states_from_pb_step_444_to_2768_none_placed_budget A lim st s0 s fsp out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
        w8 w16 d24 d28 w32 Rest444None hpc hrun hsp hx19 hx27 htr) ?_
    rintro s1 hpc1 hrun1 hcl1
      ⟨_, hsp1, _, hx8_1, hx9_1, hx13_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, _, htr1⟩
    rw [hx13] at hx13_1; rw [hx25] at hx25_1
    refine SepWP.weaken_pre
      (Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
        (Entails.of_eq (by dsimp only [Rest444None, Option.map, v9_optProtoPolyDecoderHeap]; sep_ac_rfl)))
      (v9_tail_2768_to_ret_placed hA hDec st s0 s1 hcl1 fsp out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
        noneCap w8 w16 d24 d28 w32 optUc none
        (fun u hu => by subst hu; exact hfits)
        hsp0_align hfsp_eq hpc1 hrun1 hsp1
        hx8_1 hx9_1 hx13_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
        (by intro d hd; cases hd))
  | some d =>
    dsimp only [Option.map]
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ A.pool lim st s ∗
         stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize) by sep_ac_rfl))
      (sepConj_mono_left
        (v9_optProtoPolyDecoderHeap_some_cap_lt A.repAlloc (pbToProtoPolyDecoder d) w0 w8 w16 d24 d28 w32))) ?_
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hw0_lt, hd24⟩
    change d24 = d.ptsNeeded at hd24; subst hd24
    let Rest444Some : SepProp :=
      (pbA ↦₆₄ 0x8000000000000009#64) ∗
      v9_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
      v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
      memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ stackAt fsp encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    cases hpts : d.ptsNeeded == 576#32
    · have hd24_ne : d.ptsNeeded ≠ 576#32 := by
        intro heq; rw [heq] at hpts; revert hpts; decide
      rw [v9_states_from_pb_ct1Acknowledged_ptsNeeded_ne optUc d hpts]
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
        Rest444Some ∗ A.pool lim st s by dsimp only [Rest444Some]; sep_ac_rfl)) ?_
      refine v9_seq_clean_lscl hcl
        (v9_states_from_pb_step_444_to_488_err_placed_budget A lim st s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d.ptsNeeded d28 w32 Rest444Some hw0_lt hd24_ne hpc hrun hsp hx19 hx27 htr) ?_
      rintro s1 hpc1 hrun1 hcl1
        ⟨_, hsp1, hx0_1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1, _, _, htr1⟩
      dsimp only [Rest444Some]
      cases optUc with
      | none =>
        dsimp only [v9_optProtoUcHeap]
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = ⌜u0 = noneCap⌝ ∗
            (((pbA ↦₆₄ 0x8000000000000009#64) ∗
              v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
              v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
             (v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              A.pool lim st s1 ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
              statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by sep_ac_rfl))
          (sepConj_mono_right (sepConj_mono_left
            (v9_pbA_entails_224 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
              w0 w8 w16 d.ptsNeeded d28 w32)))) ?_
        apply SepWP.pure_elim; rintro rfl
        let Rest488None : SepProp :=
          v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
          memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
          memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
        refine seq_st (mid := lsmpl.base 333 + 5368#64)
          (P_mid := fun s2 =>
            v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s2 ∗ stackAt fsp encoderFromPbStack ∗
            memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          (Q_regs := fun s2 => v9_Saved5368Preserved s0 s2 fsp out w8 w0 2#64 ∧ s2.readReg64 .x22 = w16) ?_ ?_
        · refine SepWP.weaken_pre (Entails.of_eq (show _ = A.pool lim st s1 ∗ Rest488None by
              dsimp only [Rest488None]; sep_ac_rfl)) ?_
          refine SepWP.mono
            (v9_states_from_pb_drop_proto_uc_none_488_placed_budget A lim st s0 s1 fsp out w8 w0 w16
              Rest488None hpc1 hrun1 hsp1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 htr1) ?_
          rintro s2 P2 _ _ ⟨hP2, _, hpres2, hx22_2⟩
          exact ⟨Entails.trans hP2 (Entails.of_eq (by dsimp only [Rest488None]; sep_ac_rfl)),
            hpres2, hx22_2⟩
        · rintro s2 hpc2 hrun2 ⟨hpres2, hx22_2⟩
          refine SepWP.mono
            (v9_tail_5368_to_ret_placed (F := F) hA st s0 s2 fsp out pbA
              w0 w8 w16 d.ptsNeeded d28 w32 2#64 (pbToProtoPolyDecoder d) .msgDecode
              hsp0_align hfsp_eq hpc2 hrun2 hpres2 hx22_2 rfl) ?_
          rintro sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩
          exact ⟨⟨evs, hfree, hPf⟩, hsp_f, hcs_f, htr_f⟩
      | some u =>
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
            v9_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
            (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
             stackAt fsp encoderFromPbStack ∗
             ((pbA ↦₆₄ 0x8000000000000009#64) ∗
              v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
              A.pool lim st s1 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by sep_ac_rfl))
          (sepConj_mono_left
            (v9_optProtoUcHeap_some_cap_lt A.repAlloc u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120))) ?_
        rw [sepConj_assoc]; apply SepWP.pure_elim; intro hu0_lt
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
            (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
             v9_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120) ∗
            stackAt fsp encoderFromPbStack ∗
            (A.pool lim st s1 ∗ (pbA ↦₆₄ 0x8000000000000009#64) ∗
             v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl))
          (sepConj_mono
            (v9_protoUcAt_pack A.repAlloc (pbA + 8#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
            (sepConj_mono_left (Entails.trans (v9_stackAt_encoderFromPbStack_to_allocHook fsp)
              (v9_stackAt_allocHook_to_drop32 fsp))))) ?_
        let Frame488 : SepProp :=
          memRegion (fsp - 5152#64) 1024 ∗ (pbA ↦₆₄ 0x8000000000000009#64) ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
          v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
          memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
        refine SepWP.weaken_pre (Entails.of_eq (show _ =
          protoUnchunkedCt1SentAt A.repAlloc (pbA + 8#64) u ∗
          A.pool lim st s1 ∗ stackAt fsp dropStack32 ∗ Frame488 by dsimp only [Frame488]; sep_ac_rfl)) ?_
        refine SepWP.seq
          (v9_states_from_pb_drop_proto_uc_some_488_placed hA st s0 s1 fsp out
            (pbA + 8#64) u0 w8 w0 w16 u Frame488
            hcl1 hfsp_align hu0_lt hpc1 hrun1 hsp1 hx0_1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 htr1) ?_
        rintro s2 P2 hpc2 hrun2 ⟨evs1, hfree1, hP2, hpres2, hx22_2⟩
        have hP2' : P2 ⊢
            v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp encoderFromPbStack ∗
            memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize := by
          refine Entails.trans hP2 ?_
          dsimp only [Frame488]
          refine Entails.trans (Entails.of_eq (show _ =
            ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
             v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
            (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
            (v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             A.pool lim (M.stepEvents evs1 st) s2 ∗ memRegion fsp 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono (v9_pbA_128_entails_224 pbA w0 w8 w16 d.ptsNeeded d28 w32)
              (sepConj_mono_left (Entails.trans (v9_stackAt_drop32_to_allocHook fsp)
                (v9_stackAt_allocHook_to_encoderFromPbStack fsp))))
            (Entails.of_eq (by sep_ac_rfl))
        refine SepWP.weaken_pre hP2' ?_
        refine SepWP.mono
          (v9_tail_5368_to_ret_placed (F := F) hA (M.stepEvents evs1 st) s0 s2 fsp out pbA
            w0 w8 w16 d.ptsNeeded d28 w32 2#64 (pbToProtoPolyDecoder d) .msgDecode
            hsp0_align hfsp_eq hpc2 hrun2 hpres2 hx22_2 rfl) ?_
        rintro sf Pf _ _ ⟨evs2, hfree2, hPf, hsp_f, hcs_f, htr_f⟩
        have hst_eq : M.stepEvents evs2 (M.stepEvents evs1 st) =
            M.stepEvents (evs1 ++ evs2) st := by
          rw [M.stepEvents_append]
        rw [hst_eq] at hPf
        have henv : Ct1AcknowledgedFromPbEnv F { uc := some u, receivingEk := some d } (evs1 ++ evs2) := by
          unfold Ct1AcknowledgedFromPbEnv
          dsimp only
          rw [hpts]
          exact hfree1.append hfree2
        exact ⟨⟨evs1 ++ evs2, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩
    · have hd24_eq : d.ptsNeeded = 576#32 := beq_iff_eq.mp hpts
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗
        Rest444Some ∗ A.pool lim st s by dsimp only [Rest444Some]; rw [hd24_eq]; sep_ac_rfl)) ?_
      refine v9_seq_clean_lscl hcl
        (v9_states_from_pb_step_444_to_2768_some_placed_budget A lim st s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d28 w32 Rest444Some hw0_lt hpc hrun hsp hx19 hx27 htr) ?_
      rintro s1 hpc1 hrun1 hcl1
        ⟨_, hsp1, _, hx8_1, hx9_1, _, hx13_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, _, htr1⟩
      rw [hx13] at hx13_1; rw [hx25] at hx25_1
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [Rest444Some]; rw [hd24_eq]; sep_ac_rfl))
        (v9_tail_2768_to_ret_placed hA hDec st s0 s1 hcl1 fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d.ptsNeeded d28 w32 optUc (some d)
          (fun u hu => by
            subst hu
            unfold Ct1AcknowledgedFromPbEnv at hfits
            dsimp only at hfits
            simp only [hpts, ↓reduceIte] at hfits
            exact hfits)
          hsp0_align hfsp_eq hpc1 hrun1 hsp1
          hx8_1 hx9_1 hx13_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
          (by intro d' hd'; cases hd'; exact hpts))

set_option allowUnsafeReducibility true in
private theorem sepWP_frame_evs {prog : Program} {target_pc : BitVec 64} {s : State}
    {P₀ F : SepProp} {Env : List AllocEvent → Prop}
    {P' : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target_pc s P₀
      (fun sf Pf => (∃ evs, Env evs ∧ (Pf ⊢ P' evs sf)) ∧ Q sf)) :
    SepWP prog target_pc s (P₀ ∗ F)
      (fun sf Pf => (∃ evs, Env evs ∧ (Pf ⊢ P' evs sf ∗ F)) ∧ Q sf) := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_mono (h (F ∗ R) hm) ?_ (fun _ _ ho => Satisfies.drop_mid ho)
  rintro sf _ _ ⟨Pf, hmf, ⟨evs, henv, hent⟩, hQ⟩
  exact ⟨Pf ∗ F, by rw [sepConj_assoc]; exact hmf, ⟨evs, henv, sepConj_mono_left hent⟩, hQ⟩

/-- Envelope-parametric `subroutine_ok` for Variant 9 (`some (.ct1Acknowledged st_pb)`) under any
    envelope `Env` subsuming `Ct1AcknowledgedFromPbEnv F st_pb`. -/
theorem states_from_pb_ct1Acknowledged_ok_ext_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st_pb : V1State.Chunked.Ct1Acknowledged)
    (hfits_imp : ∀ st : M.σ, FitsEnv M lim st Env →
      FitsEnv M lim st (Ct1AcknowledgedFromPbEnv F st_pb))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → Ct1AcknowledgedFromPbEnv F st_pb evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct1Acknowledged st_pb) } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [DefsBudget.statesFromPbVariantPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, _hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.ct1Acknowledged st_pb)) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some (.ct1Acknowledged st_pb)) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean_lscl_st hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1, _⟩
  dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  let RestDisp : SepProp :=
    protoChunkedCt1AcknowledgedAt A.repAlloc (pbA + 8#64) st_pb ∗ memRegion (pbA + 176#64) 48 ∗
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
  have hP1' :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
      memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗ A.pool lim st s1 ∗
      (memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ 0x8000000000000009#64) ∗
        protoChunkedCt1AcknowledgedAt A.repAlloc (pbA + 8#64) st_pb ∗ memRegion (pbA + 176#64) 48) ∗
       statesFromPbJumpTablePlacedAt) ⊢
      (pbA ↦₆₄ 0x8000000000000009#64) ∗ statesFromPbJumpTablePlacedAt ∗
      RestDisp ∗ A.pool lim st s1 := by
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      ((pbA ↦₆₄ 0x8000000000000009#64) ∗ statesFromPbJumpTablePlacedAt ∗
       protoChunkedCt1AcknowledgedAt A.repAlloc (pbA + 8#64) st_pb ∗ memRegion (pbA + 176#64) 48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304)
      (Entails.of_eq (by dsimp only [RestDisp]; sep_ac_rfl))
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA 0x8000000000000009#64 444#64 RestDisp
    TaggedVariantDispatch.ct1Acknowledged hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWPp_seq_clean_lscl_st hcl1 hdisp ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, hx25_2, _, hx13_2, _, htr2, _⟩
  have hx13_2' : s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64 := by rw [hx13_2]; bv_omega
  have hx25_2' : s2.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 := by rw [hx25_2]; bv_omega
  refine DefsBudget.sepWPp_of_states_exit_cl_placed st s0 s2 out pbA
    { innerState := some (.ct1Acknowledged st_pb) } Env _ R ?_
  have h444 := sepWP_frame_evs (F := statesFromPbJumpTablePlacedAt)
    (states_from_pb_ct1Acknowledged_444_placed (F := F) hA hDec st s0 s2 hcl2
      (s0.sp - 2400#64) out pbA st_pb (hfits_imp st hfits)
      hsp0_align rfl hpc2 hrun2 hsp2 hx13_2' hx19_2 hx25_2' hx27_2 htr2)
  refine SepWP.weaken_pre
    (by dsimp only [RestDisp, optProtoInnerStateAt, protoInnerStateAt]; exact Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono h444 ?_)
  rintro sf Pf _ _ ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩
  refine ⟨⟨evs, hsub st hfits henv, ?_⟩, hsp_f, hcs_f, htr_f⟩
  exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-- Tight-envelope `subroutine_ok` for Variant 9 (`some (.ct1Acknowledged st_pb)`) under its exact
    binary allocation envelope `Ct1AcknowledgedFromPbEnv F st_pb`. -/
theorem states_from_pb_ct1Acknowledged_ok_ext_placed_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st_pb : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct1Acknowledged st_pb) }
          (Ct1AcknowledgedFromPbEnv F st_pb))) :=
  states_from_pb_ct1Acknowledged_ok_ext_placed_of_env hA hDec st_pb
    (fun _ h => h) (fun _ _ _ h => h)

/-- Top-level `subroutine_ok` for Variant 9 (`some (.ct1Acknowledged st_pb)`) under the canonical
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`). -/
theorem states_from_pb_ct1Acknowledged_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st_pb : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.ct1Acknowledged st_pb) })) :=
  states_from_pb_ct1Acknowledged_ok_ext_placed_of_env hA hDec st_pb
    (fun _ h => fitsEnv_ct1AcknowledgedFromPbEnv_of_statesFromPbEnv F st_pb h)
    (fun _ _ hfits hevs => ct1AcknowledgedFromPbEnv_sub_statesFromPbEnv F st_pb hfits hevs)

abbrev states_from_pb_variant8_placed := @states_from_pb_ct1Acknowledged_ok_ext_placed

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudget
